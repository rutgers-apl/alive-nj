'''
Translate expressions into SMT via Z3
'''

from language import *
from typing import TypeConstraints
import z3, operator

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


class SMTTranslator(Visitor):
  def __init__(self, type_model):
    self.types = type_model
    self.terms = {}  # term -> SMT eval * defined * nonpoison

  def __call__(self, term):
    if term not in self.terms:
      self.terms[term] = term.accept(self)
    
    return self.terms[term]
  
  def bits(self, term):
    return self.types[term].arg(0).as_long()  # TODO: improve type -> bitwidth

  def Input(self, term):
    # TODO: unique name check
    return z3.BitVec(term.name, self.bits(term)), [], []


#   def AddInst(self, term):
#     x,dx,px = self(term.x)
#     y,dy,py = self(term.y)
#     
#     nonpoison = px+py
#     if 'nsw' in term.flags:
#       nonpoison.append(z3.SignExt(1,x)+z3.SignExt(1,y) == z3.SignExt(1,x+y))
#     if 'nuw' in term.flags:
#       nonpoison.append(z3.ZeroExt(1,x)+z3.ZeroExt(1,y) == z3.ZeroExt(1,x+y))
# 
#     return x+y, dx+dy, nonpoison
# 
#   def SubInst(self, term):
#     x,dx,px = self(term.x)
#     y,dy,py = self(term.y)
#     
#     nonpoison = px+py
#     if 'nsw' in term.flags:
#       nonpoison.append(z3.SignExt(1,x)-z3.SignExt(1,y) == z3.SignExt(1,x-y))
#     if 'nuw' in term.flags:
#       nonpoison.append(z3.ZeroExt(1,x)-z3.ZeroExt(1,y) == z3.ZeroExt(1,x-y))
# 
#     return x-y, dx+dy, nonpoison
# 
#   def MulInst(self, term):
#     x,dx,px = self(term.x)
#     y,dy,py = self(term.y)
#     
#     nonpoison = px+py
#     size = x.size()
#     if 'nsw' in term.flags:
#       nonpoison.append(z3.SignExt(size,x) * z3.SignExt(size,y) == z3.SignExt(size, x*y))
#     if 'nuw' in term.flags:
#       nonpoison.append(z3.ZeroExt(size,x) * z3.ZeroExt(size,y) == z3.ZeroExt(size, x*y))
#     
#     return x*y, dx+dy, nonpoison
# 
#   def SDivInst(self, term):
#     x,dx,px = self(term.x)
#     y,dy,py = self(term.y)
# 
#     nonpoison = px+py
#     if 'exact' in term.flags:
#       nonpoison.append((x/y)*y == x)
# 
#     bits = self.bits(term)
#     defined = dx + dy + [y != 0, z3.Or(x != (1 << (bits-1)), y != -1)]
#     
#     return x/y, defined, nonpoison
# 
#   def UDivInst(self, term):
#     x,dx,px = self(term.x)
#     y,dy,py = self(term.x)
#     
#     nonpoison = px+py
#     if 'exact' in term.flags:
#       nonpoison.append(z3.UDiv(x,y)*y == x)
#     
#     defined = dx + dy + [y != 0]
#     
#     return z3.UDiv(x,y), defined, nonpoison
# 
#   def SRemInst(self, term):
#     x,dx,px = self(term.x)
#     y,dy,py = self(term.x)
#     
#     bits = self.bits(term)
#     defined = dx + dy + [y != 0, z3.Or(x != (1 << (bits-1)), y != -1)]
#     
#     return z3.SRem(x,y), defined, px+py
# 
#   def URemInst(self, term):
#     x,dx,px = self(term.x)
#     y,dy,py = self(term.x)
#     
#     return z3.URem(x,y), dx+dy+[y != 0], px+py
# 
#   def ShlInst(self, term):
#     x,dx,px = self(term.x)
#     y,dy,py = self(term.x)
#     
#     nonpoison = px+py
#     if 'nsw' in term.flags:
#       nonpoison.append((x << y) >> y == x)
#     if 'nuw' in term.flags:
#       nonpoison.append(LShR(x << y, y) == x)
#     
#     defined = dx + dy + [ULT(y, self.bits(term))]
#     
#     return x << y, defined, nonpoison
# 
#   def AShrInst(self, term):
#     x,dx,px = self(term.x)
#     y,dy,py = self(term.x)
# 
#     nonpoison = dx+dy
#     if 'exact' in term.flags:
#       nonpoison.append((x >> y) << y == x)
#     
#     defined = dx + dy + [ULT(y, self.bits(term))]
#     
#     return x >> y, defined, nonpoison
# 
#   def LShrInst(self, term):
#     x,dx,px = self(term.x)
#     y,dy,py = self(term.x)
# 
#     nonpoison = dx+dy
#     if 'exact' in term.flags:
#       nonpoison.append(LShR(x, y) << y == x)
#     
#     defined = dx + dy + [ULT(y, self.bits(term))]
#     
#     return LShR(x, y), defined, nonpoison
# 
#   def AndInst(self, term):
#     x,dx,px = self(term.x)
#     y,dy,py = self(term.x)
# 
#     return a & b, dx+dy, px+py
# 
#   def OrInst(self, term):
#     x,dx,px = self(term.x)
#     y,dy,py = self(term.x)
# 
#     return a | b, dx+dy, px+py
# 
#   def XorInst(self, term):
#     x,dx,px = self(term.x)
#     y,dy,py = self(term.x)
# 
#     return a ^ b, dx+dy, px+py


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

  #def IcmpInst(self, term):
  
  def SelectInst(self, term):
    c,dc,pc = self(term.sel)
    x,dx,px = self(term.arg1)
    y,dy,py = self(term.arg2)
    
    return z3.If(c == 1, x, y), dc+dx+dy, pc+px+py

  def Literal(self, term):
    return z3.BitVecVal(term.val, self.bits(term)), [], []

def check_refinement_at(type_model, src, tgt):
  smt = SMTTranslator(type_model)
  
  sv,sd,sp = smt(src)
  tv,td,tp = smt(tgt)
  
  sd = z3.And(sd)
  sp = z3.And(sp)
  td = z3.And(td)
  tp = z3.And(tp)
  
  s = z3.Solver()
  s.add(sd, z3.Not(td))
  print s
  if s.check() != z3.unsat:
    return 'undefined', s.model()
  
  s = z3.Solver()
  s.add(sd, sp, z3.Not(tp))
  print s
  if s.check() != z3.unsat:
    return 'poison', s.model()
  
  s = z3.Solver()
  s.add(sd, sp, sv != tv)
  print s
  if s.check() != z3.unsat:
    return 'unequal', s.model()
  
  return None


def check_refinement(e1, e2):
  T = TypeConstraints()
  T.eq_types(e1,e2)
  
  for m in T.z3_models():
    r = check_refinement_at(m, e1, e2)
    if r:
      return r

  return None
  

def interp(e):
  T = TypeConstraints()
  T(e)
  
  m = T.z3_models().next()
  
  smt = SMTTranslator(m)
  return smt(e)
