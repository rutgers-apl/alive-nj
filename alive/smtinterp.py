'''
Translate expressions into SMT via Z3
'''

from .language import *
from .z3util import *
import z3, operator, logging
import types


logger = logging.getLogger(__name__)

class OpHandler(object):
  '''These essentially act as closures, where the arguments can be read.
  (And modified, so watch out.)

  To add to a class, use

    def MyClass(object):
      field = OpHandler(op)

  Then, MyClass.field returns the OpHandler, and my_obj.field returns a
  method.

  Subclasses must override __call__.
  '''
  def __init__(self, op):
    self.op = op

  def __call__(self, obj, term):
    args = (obj.eval(a) for a in term.args())

    return self.op(*args)

  def __get__(self, obj, cls=None):
    # return a method if invoked as obj.handler.
    if obj:
      return types.MethodType(self, obj, cls)

    return self

class SizedOpHandler(OpHandler):
  def __call__(self, obj, term):
    args = (obj.eval(a) for a in term.args())
    return self.op(obj.type(term).width, *args)

class BinOpHandler(OpHandler):
  _fields = ('op', 'defined', 'poisons')
  def __init__(self, op, defined = None, poisons = None):
    self.op = op
    self.poisons = poisons
    self.defined = defined

  def copy(self, **kws):
    dict = {f: kws.get(f, getattr(self, f)) for f in self._fields}
    return type(self)(**dict)

  def __call__(self, obj, term):
    return obj._binary_operator(term, self.op, self.defined, self.poisons)

class FBinOpHandler(OpHandler):
  def __call__(self, obj, term):
    return obj._float_binary_operator(term, self.op)

class MustAnalysis(OpHandler):
  def __call__(self, obj, term):
    return obj._must_analysis(term, self.op)


def _ty_sort(ty):
  'Translate a Type expression to a Z3 Sort'

  if isinstance(ty, IntType):
    return z3.BitVecSort(ty.width)

  return {
    PtrType: z3.BitVecSort(64),
    HalfType: z3.FloatHalf(),
    SingleType: z3.Float32(),
    DoubleType: z3.Float64()}[type(ty)]
    # NOTE: this assumes the global z3 context never changes

class MetaTranslator(MetaVisitor):
  def __init__(cls, name, bases, dict):
    if not hasattr(cls, 'registry'):
      cls.registry = {}

    cls.registry[name.lower()] = cls
    return super(MetaTranslator, cls).__init__(name, bases, dict)

class SMTTranslator(Visitor):
  __metaclass__ = MetaTranslator
  log = logger.getChild('SMTTranslator')

  def __init__(self, type_model):
    self.types = type_model
    self.fresh = 0
    self.defs = []  # current defined-ness conditions
    self.nops = []  # current non-poison conditions
    self.qvars = []

  def eval(self, term):
    '''smt.eval(term) -> Z3 expression

    Translate the term (and subterms), adding its definedness conditons,
    nonpoison conditions, and quantifier variables to the state.
    '''
    self.log.debug('eval %s', term)
    return term.accept(self)

  def __call__(self, term):
    '''smt(term) -> Z3 expression, def conds, nonpoison conds, qvars

    Clear the current state, translate the term (and subterms), and
    return the translation, definedness conditions, nonpoison conditions,
    and quantified variables.

    Quantified variables are guaranteed to be unique between different
    calls to the same SMTTranslator object.
    '''
    self.log.debug('call %s', term)
    self.defs = []
    self.nops = []
    self.qvars = []
    v = term.accept(self)
    return v, self.defs, self.nops, self.qvars

  def add_defs(self, *defs):
    self.defs += defs

  def add_nops(self, *nops):
    self.nops += nops
  
  def add_qvar(self, *qvars):
    self.qvars += qvars

  def type(self, term):
    return self.types[term]

  def fresh_bool(self):
    self.fresh += 1
    return z3.Bool('ana_' + str(self.fresh))

  def fresh_var(self, ty, prefix='undef_'):
    self.fresh += 1
    return z3.Const(prefix + str(self.fresh), _ty_sort(ty))

  def Input(self, term):
    # TODO: unique name check

    ty = self.types[term]
    return z3.Const(term.name, _ty_sort(ty))

  def _binary_operator(self, term, op, defined, poisons):
    x = self.eval(term.x)
    y = self.eval(term.y)

    if defined:
      self.add_defs(*defined(x,y))

    if poisons:
      for f in term.flags:
        self.add_nops(poisons[f](x,y))

    return op(x,y)

  AddInst = BinOpHandler(operator.add,
    poisons =
      {'nsw': lambda x,y: z3.SignExt(1,x)+z3.SignExt(1,y) == z3.SignExt(1,x+y),
       'nuw': lambda x,y: z3.ZeroExt(1,x)+z3.ZeroExt(1,y) == z3.ZeroExt(1,x+y)})

  SubInst = BinOpHandler(operator.sub,
    poisons =
      {'nsw': lambda x,y: z3.SignExt(1,x)-z3.SignExt(1,y) == z3.SignExt(1,x-y),
       'nuw': lambda x,y: z3.ZeroExt(1,x)-z3.ZeroExt(1,y) == z3.ZeroExt(1,x-y)})

  MulInst = BinOpHandler(operator.mul,
    poisons =
      {'nsw': lambda x,y: z3.SignExt(x.size(),x)*z3.SignExt(x.size(),y) == z3.SignExt(x.size(),x*y),
       'nuw': lambda x,y: z3.ZeroExt(x.size(),x)*z3.ZeroExt(x.size(),y) == z3.ZeroExt(x.size(),x*y)})

  SDivInst = BinOpHandler(operator.div,
    defined = lambda x,y: [y != 0, z3.Or(x != (1 << x.size()-1), y != -1)],
    poisons = {'exact': lambda x,y: (x/y)*y == x})

  UDivInst = BinOpHandler(z3.UDiv,
    defined = lambda x,y: [y != 0],
    poisons = {'exact': lambda x,y: z3.UDiv(x,y)*y == x})

  SRemInst = BinOpHandler(z3.SRem,
    defined = lambda x,y: [y != 0, z3.Or(x != (1 << (x.size()-1)), y != -1)])

  URemInst = BinOpHandler(z3.URem,
    defined = lambda x,y: [y != 0])
  
  ShlInst = BinOpHandler(operator.lshift,
    defined = lambda x,y: [z3.ULT(y, y.size())],
    poisons =
      {'nsw': lambda x,y: (x << y) >> y == x,
       'nuw': lambda x,y: z3.LShR(x << y, y) == x})

  AShrInst = BinOpHandler(operator.rshift,
    defined = lambda x,y: [z3.ULT(y, y.size())],
    poisons = {'exact': lambda x,y: (x >> y) << y == x})

  LShrInst = BinOpHandler(z3.LShR,
    defined = lambda x,y: [z3.ULT(y, y.size())],
    poisons = {'exact': lambda x,y: z3.LShR(x, y) << y == x})

  AndInst = BinOpHandler(operator.and_)
  OrInst = BinOpHandler(operator.or_)
  XorInst = BinOpHandler(operator.xor)



  def _float_binary_operator(self, term, op):
    x = self.eval(term.x)
    y = self.eval(term.y)

    if 'nnan' in term.flags:
      self.add_defs(z3.Not(z3.fpIsNaN(x)), z3.Not(z3.fpIsNaN(y)),
        z3.Not(z3.fpIsNaN(op(x,y))))

    if 'ninf' in term.flags:
      self.add_defs(z3.Not(z3.fpIsInfinite(x)), z3.Not(z3.fpIsInfinite(y)),
        z3.Not(z3.fpIsInfinite(op(x,y))))

    if 'nsz' in term.flags:
      # NOTE: this will return a different qvar for each (in)direct reference
      # to this term. Is this desirable?
      b = self.fresh_bool()
      self.add_qvar(b)
      z = op(x,y)
      nz = z3.fpMinusZero(_ty_sort(self.type(term)))
      return z3.If(z3.fpEQ(z,0), z3.If(b, 0, nz), z)

    return op(x,y)

  FAddInst = FBinOpHandler(operator.add)
  FSubInst = FBinOpHandler(operator.sub)
  FMulInst = FBinOpHandler(operator.mul)
  FDivInst = FBinOpHandler(lambda x,y: z3.fpDiv(z3._dflt_rm(), x, y))
  FRemInst = FBinOpHandler(z3.fpRem)

  # NOTE: SExt/ZExt/Trunc should all have IntType args
  SExtInst = SizedOpHandler(lambda size, x: z3.SignExt(size - x.size(), x))
  ZExtInst = SizedOpHandler(lambda size, x: z3.ZeroExt(size - x.size(), x))
  TruncInst = SizedOpHandler(lambda size, x: z3.Extract(size - 1, 0, x))

  def ZExtOrTruncInst(self, term):
    v = self.eval(term.arg)
    src = self.type(term.arg).width
    tgt = self.type(term).width
    
    if tgt == src:
      return v
    if tgt > src:
      return z3.ZeroExt(tgt - src, v)
    
    return z3.Extract(tgt-1, 0, v)

  def FPExtInst(self, term):
    v = self.eval(term.arg)
    rm = z3.get_default_rounding_mode()
    return z3.fpToFP(rm, v, _ty_sort(self.type(term)))
    # TODO: fpext range/rounding check
    # TODO: fptrunc range/rounding check

  FPTruncInst = FPExtInst

  def FPtoSIInst(self, term):
    v = self.eval(term.arg)
    src = self.type(term.arg)
    tgt = self.type(term)

    m = 2**(tgt.width-1)

    self.add_defs(v >= -m, v <= m-1)
    # this should be okay, because the bounds will round
    # towards zero if too large for the source type, only
    # excluding the infinities and NaN

    return z3.fpToSBV(z3.RTZ(), v, _ty_sort(tgt))
    # LLVM specifies RTZ

  def FPtoUIInst(self, term):
    v = self.eval(term.arg)
    src = self.type(term.arg)
    tgt = self.type(term)

    self.add_defs(v >= 0, v <= (2**tgt.width)-1)

    return z3.fpToUBV(z3.RTZ(), v, _ty_sort(tgt))
    # LLVM specifies RTZ

  # LLVM specifies: "If the value cannot fit in the floating point value,
  # the results are undefined."
  #
  # It is unclear what "cannot fit" means. Assume a value cannot fit if it
  # requires an exponent too large for the type. Assume "results are undefined"
  # means undefined behavior.
  def SItoFPInst(self, term):
    v = self.eval(term.arg)
    src = self.type(term.arg)
    tgt = self.type(term)

    w = 2**(tgt.exp-1) # 1 + maximum value of the exponent

    if src.width > w:
      m = (2**tgt.frac - 1) << (w-tgt.frac)
      self.add_defs(v >= -m, v <= m)

    return z3.fpToFP(z3.get_default_rounding_mode(), v, _ty_sort(tgt))

  def UItoFPInst(self, term):
    v = self.eval(term.arg)
    src = self.type(term.arg)
    tgt = self.type(term)

    w = 2**(tgt.exp-1)

    if src.width >= w:
      m = (2**tgt.frac-1) << (w - tgt.frac)
      self.add_defs(z3.UGE(v, 0), z3.ULE(v, m))

    return z3.fpToFPUnsigned(z3.get_default_rounding_mode(), v, _ty_sort(tgt))

  _icmp_ops = {
    'eq': operator.eq,
    'ne': operator.ne,
    'ugt': z3.UGT,
    'uge': z3.UGE,
    'ult': z3.ULT,
    'ule': z3.ULE,
    'sgt': operator.gt,
    'sge': operator.ge,
    'slt': operator.lt,
    'sle': operator.le,
  }

  def IcmpInst(self, term):
    x = self.eval(term.x)
    y = self.eval(term.y)

    cmp = self._icmp_ops[term.pred](x,y)

    return bool_to_BitVec(cmp)

  _fcmp_ops = {
    'false': lambda x,y: z3.BoolVal(False),
    'oeq': z3.fpEQ,
    'ogt': z3.fpGT,
    'oge': z3.fpGEQ,
    'olt': z3.fpLT,
    'ole': z3.fpLEQ,
    'one': lambda x,y: z3.Not(fpUEQ(x,y)),
    'ord': lambda x,y: z3.Not(z3.Or(z3.fpIsNaN(x), z3.fpIsNaN(y))),
    'ueq': fpUEQ,
    'ugt': lambda x,y: z3.Not(z3.fpLEQ(x,y)),
    'uge': lambda x,y: z3.Not(z3.fpLT(x,y)),
    'ult': lambda x,y: z3.Not(z3.fpGEQ(x,y)),
    'ule': lambda x,y: z3.Not(z3.fpGT(x,y)),
    'une': z3.fpNEQ,
    'uno': lambda x,y: z3.Or(z3.fpIsNaN(x), z3.fpIsNaN(y)),
    'true': lambda x,y: z3.BoolVal(True),
  }

  # TODO: fcmp flags
  def FcmpInst(self, term):
    x = self.eval(term.x)
    y = self.eval(term.y)

    cmp = self._fcmp_ops[term.pred](x,y)

    if 'nnan' in term.flags:
      self.add_defs(z3.Not(z3.fpIsNaN(x)), z3.Not(z3.fpIsNaN(y)))

    if 'ninf' in term.flags:
      self.add_defs(z3.Not(z3.fpIsInfinite(x)), z3.Not(z3.fpIsInfinite(y)))

    # no other flags are meaningful here?

    return bool_to_BitVec(cmp)

  SelectInst = OpHandler(lambda c,x,y: z3.If(c == 1, x, y))

  def Literal(self, term):
    ty = self.type(term)
    if isinstance(ty, FloatType):
      return z3.FPVal(term.val, _ty_sort(ty))

    return z3.BitVecVal(term.val, ty.width)

  def FLiteralVal(self, term):
    ty = self.type(term)
    assert isinstance(ty, FloatType)

    return z3.FPVal(term.val, _ty_sort(ty))

  def FLiteralNaN(self, term):
    return z3.fpNaN(_ty_sort(self.type(term)))

  def FLiteralPlusInf(self, term):
    return z3.fpPlusInfinity(_ty_sort(self.type(term)))

  def FLiteralMinusInf(self, term):
    return z3.fpMinusInfinity(_ty_sort(self.type(term)))

  def FLiteralMinusZero(self, term):
    return z3.fpMinusZero(_ty_sort(self.type(term)))

  def UndefValue(self, term):
    ty = self.type(term)
    x = self.fresh_var(ty)
    self.add_qvar(x)
    return x

  def PoisonValue(self, term):
    self.add_nops(z3.BoolVal(False))
    return self.fresh_var(self.type(term))

  # NOTE: constant expressions do no introduce poison or definedness constraints
  #       is this reasonable?
  # FIXME: cnxps need explicit undef checking
  # FIXME: div/rem by 0 is undef
  AddCnxp = BinOpHandler(operator.add)
  SubCnxp = BinOpHandler(operator.sub)
  MulCnxp = BinOpHandler(operator.mul)
  SDivCnxp = BinOpHandler(operator.div)
  UDivCnxp = BinOpHandler(z3.UDiv)
  SRemCnxp = BinOpHandler(operator.mod)
  URemCnxp = BinOpHandler(z3.URem)
  ShlCnxp = BinOpHandler(operator.lshift)
  AShrCnxp = BinOpHandler(operator.rshift)
  LShrCnxp = BinOpHandler(z3.LShR)
  AndCnxp = BinOpHandler(operator.and_)
  OrCnxp = BinOpHandler(operator.or_)
  XorCnxp = BinOpHandler(operator.xor)

  NotCnxp = OpHandler(operator.inv)

  def NegCnxp(self, term):
    if isinstance(self.type(term), FloatType):
      return z3.fpNeg(self.eval(term.x))

    return -self.eval(term.x)

  def AbsCnxp(self, term):
    x = self.eval(term._args[0])

    if isinstance(self.type(term), FloatType):
      return z3.fpAbs(x)

    return z3.If(x >= 0, x, -x)

  def SignBitsCnxp(self, term):
    x = self.eval(term._args[0])
    ty = self.type(term)

    #b = ComputeNumSignBits(self.fresh_bv(size), size)
    b = self.fresh_var(ty, 'ana_')

    self.add_defs(z3.ULE(b, ComputeNumSignBits(ty.width, x)))

    return b

  def OneBitsCnxp(self, term):
    x = self.eval(term._args[0])
    b = self.fresh_var(self.type(term), 'ana_')

    self.add_defs(b & ~x == 0)

    return b

  def ZeroBitsCnxp(self, term):
    x = self.eval(term._args[0])
    b = self.fresh_var(self.type(term), 'ana_')

    self.add_defs(b & x == 0)

    return b
  
  LeadingZerosCnxp = SizedOpHandler(ctlz)
  TrailingZerosCnxp = SizedOpHandler(cttz)
  Log2Cnxp = SizedOpHandler(bv_log2)
  LShrFunCnxp = OpHandler(z3.LShR)
  SMaxCnxp = OpHandler(lambda x,y: z3.If(x > y, x, y))
  UMaxCnxp = OpHandler(lambda x,y: z3.If(z3.UGT(x,y), x, y))

  SExtCnxp = SExtInst
  ZExtCnxp = ZExtInst
  TruncCnxp = TruncInst

  def FPExtCnxp(self, term):
    v = self.eval(term._args[0])
    return z3.fpToFP(z3.RNE(), v, _ty_sort(self.type(term)))
    # TODO: fpext() range/rounding check
    # TODO: fptrunc() range/rounding check

  FPTruncCnxp = FPExtCnxp

  def FPtoSICnxp(self, term): #FIXME
    x = self.eval(term._args[0])
    tgt = self.type(term)

    return z3.fpToSBV(z3.RTZ(), x, _ty_sort(tgt))

  def FPtoUICnxp(self, term): #FIXME
    x = self.eval(term._args[0])
    tgt = self.type(term)

    return z3.fpToUBV(z3.RTZ(), x, _ty_sort(tgt))

  def SItoFPCnxp(self, term): #FIXME
    x = self.eval(term._args[0])
    tgt = self.type(term)

    return z3.fpToFP(z3.RTZ(), x, _ty_sort(tgt))

  def UItoFPCnxp(self, term): #FIXME
    x = self.eval(term._args[0])
    tgt = self.type(term)

    return z3.fpToFPUnsigned(z3.RTZ(), x, _ty_sort(tgt))

  def WidthCnxp(self, term):
    return z3.BitVecVal(self.type(term._args[0]).width, self.type(term).width)
    # NOTE: nothing bad should happen if we don't evaluate the argument

  def AndPred(self, term):
    return mk_and([self.eval(cl) for cl in term.clauses])

  def OrPred(self, term):
    return mk_or([self.eval(cl) for cl in term.clauses])

  def NotPred(self, term):
    return z3.Not(self.eval(term.p))

  def Comparison(self, term):
    if term.op == 'eq' and isinstance(self.type(term.x), FloatType):
      cmp = z3.fpEQ
    else:
      cmp = self._icmp_ops[term.op]
      # only the signed ones can be FP, so this is safe

    return cmp(self.eval(term.x), self.eval(term.y))

  def _must_analysis(self, term, op):
    args = (self.eval(a) for a in term._args)

    if all(isinstance(a, Constant) for a in term._args):
      return op(*args)

    c = self.fresh_bool()
    self.add_defs(z3.Implies(c, op(*args)))
    return c

  CannotBeNegativeZeroPred = MustAnalysis(
    lambda x: z3.Not(x == z3.fpMinusZero(x.sort())))
    # or: z3.And(z3.Not(z3.fpIsNegative(x)), z3.Not(z3.fpIsZero(x)))

  def FPSamePred(self, term):
    return self.eval(term._args[0]) == self.eval(term._args[1])

  IntMinPred = OpHandler(lambda x: x == 1 << (x.size()-1))

  Power2Pred = MustAnalysis(lambda x: z3.And(x != 0, x & (x-1) == 0))
  Power2OrZPred = MustAnalysis(lambda x: x & (x-1) == 0)

  def ShiftedMaskPred(self, term):
    x = self.eval(term._args[0])

    v = (x - 1) | x
    return z3.And(v != 0, ((v+1) & v) == 0)

  MaskZeroPred = MustAnalysis(lambda x,y: x & y == 0)

  NSWAddPred = MustAnalysis(
    lambda x,y: z3.SignExt(1,x) + z3.SignExt(1,y) == z3.SignExt(1,x+y))

  NUWAddPred = MustAnalysis(
    lambda x,y: z3.ZeroExt(1,x) + z3.ZeroExt(1,y) == z3.ZeroExt(1,x+y))

  NSWSubPred = MustAnalysis(
    lambda x,y: z3.SignExt(1,x) - z3.SignExt(1,y) == z3.SignExt(1,x-y))

  NUWSubPred = MustAnalysis(
    lambda x,y: z3.ZeroExt(1,x) - z3.ZeroExt(1,y) == z3.ZeroExt(1,x-y))

  @OpHandler
  def NSWMulPred(x,y):
    size = x.size()
    return z3.SignExt(size,x) * z3.SignExt(size,y) == z3.SignExt(size,x*y)

  @OpHandler
  def NUWMulPred(x,y):
    size = x.size()
    return z3.ZeroExt(size,x) * z3.ZeroExt(size,y) == z3.ZeroExt(size,x*y)

  NUWShlPred = OpHandler(lambda x,y: z3.LShR(x << y, y) == x)

  def OneUsePred(self, term):
    return z3.BoolVal(True)
    # NOTE: should this have semantics?


class NewShlSemantics(SMTTranslator):
  ShlInst = SMTTranslator.ShlInst.copy(poisons = {
    'nsw': lambda a,b: z3.Or((a << b) >> b == a,
                             z3.And(a == 1, b == b.size() - 1)),
    'nuw': lambda a,b: z3.LShR(a << b, b) == a})

class FastMathUndef(SMTTranslator):
  def _float_binary_operator(self, term, op):
    x = self.eval(term.x)
    y = self.eval(term.y)

    conds = []
    z = op(x,y)
    if 'nnan' in term.flags:
      conds += [z3.Not(z3.fpIsNaN(x)), z3.Not(z3.fpIsNaN(y)),
        z3.Not(z3.fpIsNaN(op(x,y)))]

    if 'ninf' in term.flags:
      conds += [z3.Not(z3.fpIsInfinite(x)), z3.Not(z3.fpIsInfinite(y)),
        z3.Not(z3.fpIsInfinite(op(x,y)))]

    if 'nsz' in term.flags:
      # NOTE: this will return a different qvar for each (in)direct reference
      # to this term. Is this desirable?
      b = self.fresh_bool()
      self.add_qvar(b)
      z = op(x,y)
      nz = z3.fpMinusZero(_ty_sort(self.type(term)))
      z = z3.If(z3.fpEQ(z,0), z3.If(b, 0, nz), z)

    if conds:
      q = self.fresh_var(self.type(term))
      self.add_qvar(q)

      return z3.If(mk_and(conds), z, q)

    return z

class FPOverflowUndef(SMTTranslator):
  def SItoFPInst(self, term):
    v = self.eval(term.arg)
    src = self.type(term.arg)
    tgt = self.type(term)

    w = 2**(tgt.exp-1)
    z = z3.fpToFP(z3.get_default_rounding_mode(), v, _ty_sort(tgt))

    if src.width <= w:
      return z

    q = self.fresh_var(tgt)
    self.add_qvar(q)

    m = (2**tgt.frac - 1) << (w-tgt.frac)
    return z3.If(z3.And(v >= -m, v <= m), z, q)

  def UItoFPInst(self, term):
    v = self.eval(term.arg)
    src = self.type(term.arg)
    tgt = self.type(term)

    w = 2**(tgt.exp-1)

    z = z3.fpToFPUnsigned(z3.get_default_rounding_mode(), v, _ty_sort(tgt))

    if src.width < w:
      return z

    q = self.fresh_var(tgt)
    self.add_qvar(q)

    m = (2**tgt.frac-1) << (w - tgt.frac)
    return z3.If(z3.And(z3.UGE(v, 0), z3.ULE(v, m)), z, q)

  def FPTrunc(self, term):
    v = self.eval(term.arg)

    w = 2**(tgt.exp-1)
    m = (2**tgt.frac-1) << (w - tgt.frac)

    q = self.fresh_var(tgt)
    self.add_qvar(q)

    return z3.If(
      z3.Or(z3.fpIsNaN(v), z3.fpIsInfinite(v),
            z3.And(v >= -m, v <= m)),
      z3.fpToFP(z3.get_default_rounding_mode(), v, _ty_sort(tgt)),
      q)

class OldNSZ(SMTTranslator):
  def _float_binary_operator(self, term, op):
    x = self.eval(term.x)
    y = self.eval(term.y)

    if 'nnan' in term.flags:
      self.add_defs(z3.Not(z3.fpIsNaN(x)), z3.Not(z3.fpIsNaN(y)),
        z3.Not(z3.fpIsNaN(op(x,y))))

    if 'ninf' in term.flags:
      self.add_defs(z3.Not(z3.fpIsInfinite(x)), z3.Not(z3.fpIsInfinite(y)),
        z3.Not(z3.fpIsInfinite(op(x,y))))

    if 'nsz' in term.flags:
      # NOTE: this will return a different qvar for each (in)direct reference
      # to this term. Is this desirable?
      nz = z3.fpMinusZero(_ty_sort(self.type(term)))
      self.add_defs(z3.Not(x == nz), z3.Not(y == nz))
      return op(x,y)  # turns -0 to +0

    return op(x,y)

class BrokenNSZ(SMTTranslator):
  def _float_binary_operator(self, term, op):
    x = self.eval(term.x)
    y = self.eval(term.y)

    if 'nnan' in term.flags:
      self.add_defs(z3.Not(z3.fpIsNaN(x)), z3.Not(z3.fpIsNaN(y)),
        z3.Not(z3.fpIsNaN(op(x,y))))

    if 'ninf' in term.flags:
      self.add_defs(z3.Not(z3.fpIsInfinite(x)), z3.Not(z3.fpIsInfinite(y)),
        z3.Not(z3.fpIsInfinite(op(x,y))))

    if 'nsz' in term.flags:
      # NOTE: this will return a different qvar for each (in)direct reference
      # to this term. Is this desirable?
      q = self.fresh_var(self.type(term))
      self.add_qvar(q)  # FIXME
      self.add_defs(z3.fpEQ(q,0))
      z = op(x,y)
      return z3.If(z3.fpEQ(z,0), q, z)

    return op(x,y)
