'''
Extra functions for dealing with Z3 BitVecs.
'''

__all__ = ('mk_and', 'mk_or', 'mk_not', 'mk_forall', 'bool_to_BitVec',
           'bv_log2', 'ctlz', 'cttz', 'ComputeNumSignBits', 'fpUEQ',
           'zext_or_trunc')

import z3

def mk_and(clauses):
  'mk_and([p,q,r]) -> And(p,q,r)'
  if len(clauses) == 1:
    return clauses[0]
  if len(clauses) == 0:
    return z3.BoolVal(True)

  return z3.And(clauses)

def mk_or(clauses):
  'mk_or([p,q,r]) -> Or(p,q,r)'
  if len(clauses) == 1:
    return clauses[0]
  if len(clauses) == 0:
    return z3.BoolVal(False)

  return z3.Or(clauses)

def mk_not(clauses):
  'mk_not([p,q,r]) -> Not(And(p,q,r))'
  if len(clauses) == 1:
    return z3.Not(clauses[0])
  if len(clauses) == 0:
    return z3.BoolVal(False)

  return z3.Not(z3.And(clauses))

def mk_forall(qvars, clauses):
  'mk_forall(vs, [p,q,r]) -> ForAll(vs, And(p,q,r))'
  if len(qvars) == 0:
    return mk_and(clauses)

  return z3.ForAll(qvars, mk_and(clauses))


def bool_to_BitVec(b):
  return z3.If(b, z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

def bv_log2(bitwidth, v):
  def rec(h, l):
    if h <= l:
      return z3.BitVecVal(l, bitwidth)
    mid = l+int((h-l)/2)
    return z3.If(z3.Extract(h,mid+1,v) != 0, rec(h, mid+1), rec(mid, l))
  return rec(v.size()-1, 0)

def zext_or_trunc(v, src, tgt):
  if tgt == src:
    return v
  if tgt > src:
    return z3.ZeroExt(tgt - src, v)

  return z3.Extract(tgt-1, 0, v)

def ctlz(output_width, v):
  size = v.size()
  def rec(i):
    if i < 0:
      return z3.BitVecVal(size, output_width)
    return z3.If(z3.Extract(i,i,v) == z3.BitVecVal(1, 1),
              z3.BitVecVal(size-1-i, output_width),
              rec(i-1))
  return rec(size-1)


def cttz(output_width, v):
  size = v.size()
  def rec(i):
    if i == size:
      return z3.BitVecVal(size, output_width)
    return z3.If(z3.Extract(i,i,v) == z3.BitVecVal(1, 1),
              z3.BitVecVal(i, output_width),
              rec(i+1))
  return rec(0)


def ComputeNumSignBits(bitwidth, v):
  size = v.size()
  size1 = size - 1
  sign = z3.Extract(size1, size1, v)

  def rec(i):
    if i < 0:
      return z3.BitVecVal(size, bitwidth)
    return z3.If(z3.Extract(i,i,v) == sign,
              rec(i-1),
              z3.BitVecVal(size1-i, bitwidth))
  return rec(size - 2)


def fpUEQ(x, y):
  return z3.Or(z3.fpEQ(x,y), z3.fpIsNaN(x), z3.fpIsNaN(y))
