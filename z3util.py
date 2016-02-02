'''
Extra functions for dealing with Z3 BitVecs.
'''

import z3

def bool_to_BitVec(b):
  return z3.If(b, z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

def bv_log2(v, bitwidth):
  def rec(h, l):
    if h <= l:
      return z3.BitVecVal(l, bitwidth)
    mid = l+int((h-l)/2)
    return z3.If(z3.Extract(h,mid+1,v) != 0, rec(h, mid+1), rec(mid, l))
  return rec(v.size()-1, 0)


def ctlz(v, output_width):
  size = v.size()
  def rec(i):
    if i < 0:
      return z3.BitVecVal(size, output_width)
    return z3.If(z3.Extract(i,i,v) == z3.BitVecVal(1, 1),
              z3.BitVecVal(size-1-i, output_width),
              rec(i-1))
  return rec(size-1)


def cttz(v, output_width):
  size = v.size()
  def rec(i):
    if i == size:
      return z3.BitVecVal(size, output_width)
    return z3.If(z3.Extract(i,i,v) == z3.BitVecVal(1, 1),
              z3.BitVecVal(i, output_width),
              rec(i+1))
  return rec(0)


def ComputeNumSignBits(v, bitwidth):
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
