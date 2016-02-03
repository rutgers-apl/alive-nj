'''
Translate expressions into SMT via Z3
'''

from language import *
from typing import TypeConstraints, TySort
from z3util import *
import z3, operator, logging


logger = logging.getLogger(__name__)

def is_const(term):
  return isinstance(term, Constant) or \
    (isinstance(term, Input) and term.name[0] == 'C')

def _mk_bop(op, defined = None, poisons = None):
  def bop(self, term):
    x,dx,px = self(term.x)
    y,dy,py = self(term.y)
    
    nonpoison = px+py
    if poisons:
      for f in term.flags:
        nonpoison.append(poisons[f](x,y))

    d = dx + dy + (defined(x,y) if defined else [])
  
    return op(x,y), d, nonpoison
  
  return bop

def _mk_must_analysis(op):
  def pred(self, term):
    x,dx,px = self(term._args[0])

    if is_const(x):
      return op(x),dx,px

    c = self.fresh_bool()
    return c, dx+[z3.Implies(c,op(x))], px

  return pred

def _mk_bin_must_analysis(op):
  def bop(self, term):
    x,dx,px = self(term._args[0])
    y,dy,py = self(term._args[1])

    if all(is_const(a) for a in term._args):
      return op(x,y),dx+dy,px+py

    c = self.fresh_bool()
    return c, dx+dy+[z3.Implies(c,op(x,y))], px+py

  return bop


class SMTTranslator(Visitor):
  def __init__(self, type_model):
    self.types = type_model
    self.terms = {}  # term -> SMT eval * defined * nonpoison
    self.fresh = 0

  def __call__(self, term):
    if term not in self.terms:
      self.terms[term] = term.accept(self)
    
    return self.terms[term]
  
  def bits(self, term):
    Ty = self.types[term]
    if Ty.decl().eq(TySort.integer):
      return Ty.arg(0).as_long()
    if Ty.eq(TySort.pointer):
      return 64
      # NOTE: assume 64-bit pointers, since we don't do anything with them

    assert False

  def fresh_bool(self):
    self.fresh += 1
    return z3.Bool('ana_' + str(self.fresh))

  def fresh_bv(self, size):
    self.fresh += 1
    return z3.BitVec('ana_' + str(self.fresh), size)

  def Input(self, term):
    # TODO: unique name check
    return z3.BitVec(term.name, self.bits(term)), [], []

  AddInst = _mk_bop(operator.add,
    poisons =
      {'nsw': lambda x,y: z3.SignExt(1,x)+z3.SignExt(1,y) == z3.SignExt(1,x+y),
       'nuw': lambda x,y: z3.ZeroExt(1,x)+z3.ZeroExt(1,y) == z3.ZeroExt(1,x+y)})

  SubInst = _mk_bop(operator.sub,
    poisons =
      {'nsw': lambda x,y: z3.SignExt(1,x)-z3.SignExt(1,y) == z3.SignExt(1,x-y),
       'nuw': lambda x,y: z3.ZeroExt(1,x)-z3.ZeroExt(1,y) == z3.ZeroExt(1,x-y)})

  MulInst = _mk_bop(operator.mul,
    poisons =
      {'nsw': lambda x,y: z3.SignExt(x.size(),x)*z3.SignExt(x.size(),y) == z3.SignExt(x.size(),x*y),
       'nuw': lambda x,y: z3.ZeroExt(x.size(),x)*z3.ZeroExt(x.size(),y) == z3.ZeroExt(x.size(),x*y)})

  SDivInst = _mk_bop(operator.div,
    defined = lambda x,y: [y != 0, z3.Or(x != (1 << x.size()-1), y != -1)],
    poisons = {'exact': lambda x,y: (x/y)*y == x})

  UDivInst = _mk_bop(z3.UDiv,
    defined = lambda x,y: [y != 0],
    poisons = {'exact': lambda x,y: z3.UDiv(x,y)*y == x})

  SRemInst = _mk_bop(z3.SRem,
    defined = lambda x,y: [y != 0, z3.Or(x != (1 << (x.size()-1)), y != -1)])

  URemInst = _mk_bop(z3.URem,
    defined = lambda x,y: [y != 0])
  
  ShlInst = _mk_bop(operator.lshift,
    defined = lambda x,y: [z3.ULT(y, y.size())],
    poisons =
      {'nsw': lambda x,y: (x << y) >> y == x,
       'nuw': lambda x,y: z3.LShR(x << y, y) == x})

  AShrInst = _mk_bop(operator.rshift,
    defined = lambda x,y: [z3.ULT(y, y.size())],
    poisons = {'exact': lambda x,y: (x >> y) << y == x})

  LShrInst = _mk_bop(z3.LShR,
    defined = lambda x,y: [z3.ULT(y, y.size())],
    poisons = {'exact': lambda x,y: z3.LShR(x, y) << y == x})

  AndInst = _mk_bop(operator.and_)
  OrInst = _mk_bop(operator.or_)
  XorInst = _mk_bop(operator.xor)
    


  def SExtInst(self, term):
    v,d,p = self(term.arg)
    src = self.bits(term.arg)
    tgt = self.bits(term)
    return z3.SignExt(tgt - src, v), d, p

  def ZExtInst(self, term):
    v,d,p = self(term.arg)
    src = self.bits(term.arg)
    tgt = self.bits(term)
    return z3.ZeroExt(tgt - src, v), d, p

  def TruncInst(self, term):
    v,d,p = self(term.arg)
    tgt = self.bits(term)
    return z3.Extract(tgt - 1, 0, v), d, p

  def IcmpInst(self, term):
    x,dx,px = self(term.x)
    y,dy,py = self(term.y)

    cmp = {
      'eq': operator.eq,
      'ne': operator.ne,
      'ugt': z3.UGT,
      'uge': z3.UGE,
      'ult': z3.ULT,
      'ule': z3.ULE,
      'sgt': operator.gt,
      'sge': operator.ge,
      'slt': operator.lt,
      'sle': operator.le}[term.pred](x,y)

    return bool_to_BitVec(cmp), dx+dy, px+py
  
  def SelectInst(self, term):
    c,dc,pc = self(term.sel)
    x,dx,px = self(term.arg1)
    y,dy,py = self(term.arg2)
    
    return z3.If(c == 1, x, y), dc+dx+dy, pc+px+py

  def Literal(self, term):
    return z3.BitVecVal(term.val, self.bits(term)), [], []

  # NOTE: constant expressions do no introduce poison or definedness constraints
  #       is this reasonable?
  AddCnxp = _mk_bop(operator.add)
  SubCnxp = _mk_bop(operator.sub)
  MulCnxp = _mk_bop(operator.mul)
  SDivCnxp = _mk_bop(operator.div)
  UDivCnxp = _mk_bop(z3.UDiv)
  SRemCnxp = _mk_bop(z3.SRem)
  URemCnxp = _mk_bop(z3.URem)
  ShlCnxp = _mk_bop(operator.lshift)
  AShrCnxp = _mk_bop(operator.rshift)
  LShrCnxp = _mk_bop(z3.LShR)
  AndCnxp = _mk_bop(operator.and_)
  OrCnxp = _mk_bop(operator.or_)
  XorCnxp = _mk_bop(operator.xor)

  def NotCnxp(self, term):
    x,dx,px = self(term.x)
    return ~x,dx,px

  def NegCnxp(self, term):
    x,dx,px = self(term.x)
    return -x,dx,px

  def AbsCnxp(self, term):
    x,dx,px = self(term._args[0])

    return z3.If(x >= 0, x, -x), dx, px

  def SignBitsCnxp(self, term):
    x,dx,px = self(term._args[0])
    size = self.bits(term)

    #b = ComputeNumSignBits(self.fresh_bv(size), size)
    b = self.fresh_bv(size)

    return b, dx + [z3.ULE(b, ComputeNumSignBits(x, size))], px

  def OneBitsCnxp(self, term):
    x,dx,px = self(term._args[0])
    b = self.fresh_bv(x.size())

    return b, dx+[b & ~x == 0], px

  def ZeroBitsCnxp(self, term):
    x,dx,px = self(term._args[0])
    b = self.fresh_bv(x.size())

    return b, dx+[b & x == 0], px

  def LeadingZerosCnxp(self, term):
    x,dx,px = self(term._args[0])

    return ctlz(x, self.bits(term)), dx, px

  def TrailingZerosCnxp(self, term):
    x,dx,px = self(term._args[0])
    
    return cttz(x, self.bits(term)), dx, px

  def Log2Cnxp(self, term):
    x,dx,px = self(term._args[0])

    return bv_log2(x, self.bits(term)), dx, px

  def LShrFunCnxp(self, term):
    x,dx,px = self(term._args[0])
    y,dy,py = self(term._args[1])

    return z3.LShR(x,y), dx+dy, px+py

  def SMaxCnxp(self, term):
    x,dx,px = self(term._args[0])
    y,dy,py = self(term._args[1])

    return z3.If(x > y, x, y), dx+dy, px+py

  def UMaxCnxp(self, term):
    x,dx,px = self(term._args[0])
    y,dy,py = self(term._args[1])

    return z3.If(z3.UGT(x,y), x, y), dx+dy, px+py

  def SExtCnxp(self, term):
    x,dx,px = self(term._args[0])

    bits = self.bits(term)
    return z3.SignExt(bits - x.size(), x), dx, px

  def ZExtCnxp(self, term):
    x,dx,px = self(term._args[0])

    bits = self.bits(term)
    return z3.ZeroExt(bits - x.size(), x), dx, px

  def TruncCnxp(self, term):
    x,dx,px = self(term._args[0])

    bits = self.bits(term)
    return z3.Extract(bits-1, 0, x), dx, px

  def WidthCnxp(self, term):
    return z3.BitVecVal(self.bits(term._args[0]), self.bits(term)), [], []
    # NOTE: nothing bad should happen if we don't evaluate the argument

  def AndPred(self, term):
    bs = []
    ds = []
    ps = []
    for cl in term.clauses:
      b,d,p = self(cl)
      bs.append(b)
      ds += d
      ps += p

    return z3.And(bs), ds, ps

  def OrPred(self, term):
    bs = []
    ds = []
    ps = []
    for cl in term.clauses:
      b,d,p = self(cl)
      bs.append(b)
      ds += d
      ps += p

    return z3.Or(bs), ds, ps

  def NotPred(self, term):
    p,dp,pp = self(term.p)
    return z3.Not(p),dp,pp

  def Comparison(self, term):
    cmp = {
      'eq': operator.eq,
      'ne': operator.ne,
      'ugt': z3.UGT,
      'uge': z3.UGE,
      'ult': z3.ULT,
      'ule': z3.ULE,
      'sgt': operator.gt,
      'sge': operator.ge,
      'slt': operator.lt,
      'sle': operator.le}[term.op]

    x,dx,px = self(term.x)
    y,dy,py = self(term.y)
    return cmp(x,y), dx+dy, px+py

  def IntMinPred(self, term):
    x,dx,px = self(term._args[0])

    return x == 1 << (x.size()-1), dx, []

  Power2Pred = _mk_must_analysis(lambda x: z3.And(x != 0, x & (x-1) == 0))
  Power2OrZPred = _mk_must_analysis(lambda x: x & (x-1) == 0)

  def ShiftedMaskPred(self, term):
    x,dx,px = self(term._args[0])

    v = (x - 1) | x
    return z3.And(v != 0, ((v+1) & v) == 0), dx, px

  MaskZeroPred = _mk_bin_must_analysis(lambda x,y: x & y == 0)

  NSWAddPred = _mk_bin_must_analysis(
    lambda x,y: z3.SignExt(1,x) + z3.SignExt(1,y) == z3.SignExt(1,x+y))

  NUWAddPred = _mk_bin_must_analysis(
    lambda x,y: z3.ZeroExt(1,x) + z3.ZeroExt(1,y) == z3.ZeroExt(1,x+y))

  NSWSubPred = _mk_bin_must_analysis(
    lambda x,y: z3.SignExt(1,x) - z3.SignExt(1,y) == z3.SignExt(1,x-y))

  NUWSubPred = _mk_bin_must_analysis(
    lambda x,y: z3.ZeroExt(1,x) - z3.ZeroExt(1,y) == z3.ZeroExt(1,x-y))

  def NSWMulPred(self, term):
    x,dx,px = self(term._args[0])
    y,dy,py = self(term._args[1])

    size = x.size()
    expr = z3.SignExt(size,x) * z3.SignExt(size,y) == z3.SignExt(size,x*y)

    return expr, dx+dy, px+py

  def NUWMulPred(self, term):
    x,dx,px = self(term._args[0])
    y,dy,py = self(term._args[1])

    size = x.size()
    expr = z3.ZeroExt(size,x) * z3.ZeroExt(size,y) == z3.ZeroExt(size,x*y)

    return expr, dx+dy, px+py

  def NUWShlPred(self, term):
    x,dx,px = self(term._args[0])
    y,dy,py = self(term._args[1])

    size = x.size()

    return z3.LShR(x << y, y) == x, dx+dy, px+py

  def OneUsePred(self, term):
    return z3.BoolVal(True), [], []
    # NOTE: should this have semantics?




def check_refinement_at(type_model, src, tgt, pre=None):
  smt = SMTTranslator(type_model)
  
  sv,sd,sp = smt(src)
  tv,td,tp = smt(tgt)
  if pre:
    pb,pd,pp = smt(pre)
    sd += [pb] + pd
    # NOTE: should we require sd => pd?
  
  sd = z3.And(sd)
  sp = z3.And(sp)
  td = z3.And(td)
  tp = z3.And(tp)
  
  s = z3.Solver()
  s.add(sd, z3.Not(td))
  logger.debug('undef check\n%s', s)
  if s.check() != z3.unsat:
    return 'undefined', s.model()
  
  s = z3.Solver()
  s.add(sd, sp, z3.Not(tp))
  logger.debug('poison check\n%s', s)
  if s.check() != z3.unsat:
    return 'poison', s.model()
  
  s = z3.Solver()
  s.add(sd, sp, sv != tv)
  logger.debug('equality check\n%s', s)
  if s.check() != z3.unsat:
    return 'unequal', s.model()
  
  return None


def check_refinement(e1, e2, pre=None):
  T = TypeConstraints()
  T.eq_types(e1,e2)
  pre.accept(T)
  
  for m in T.z3_models():
    logger.debug('using model %s', m)
    r = check_refinement_at(m, e1, e2, pre)
    if r:
      return r


  return None
  

def interp(e):
  T = TypeConstraints()
  T(e)
  
  m = T.z3_models().next()
  
  smt = SMTTranslator(m)
  return smt(e)


if __name__ == '__main__':
  logging.basicConfig() #level=logging.DEBUG)

  r = check_refinement(IcmpInst('ult', Input('x'), Literal(0)), Literal(0))
  print r if r else 'Okay'

# Pre: C1 < C2
# %Op0 = ashr exact %X, C1
# %r = shl i33 %Op0, C2
#   =>
# %r = shl %X, C2-C1

  C1 = Input('C1')
  C2 = Input('C2')
  x = Input('%X')

  op0 = AShrInst(x, C1, flags=['exact'])
  rs = ShlInst(op0, C2)
  rt = ShlInst(x, SubCnxp(C2,C1))
  pre = Comparison('slt',C1,C2)

  r = check_refinement(rs,rt,pre)
  print r if r else 'Okay'

  pre = IntMinPred(C1)
  src = AddInst(XorInst(x,C1),C2)
  tgt = AddInst(x, XorCnxp(C1,C2))
  r = check_refinement(src,tgt,pre)
  print r if r else 'Okay'
