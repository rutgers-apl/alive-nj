'''
Defines the internal representation as nodes in a DAG.
'''

from . import pretty
import itertools
import operator

# Type system
# -----------

class Type(object):
  __slots__ = ()
  def __ne__(self, other):
    return not (self == other)

import operator


class Comparable(object):
  def __eq__(self, other): return self._cmp(operator.eq, other)
  def __ge__(self, other): return self._cmp(operator.ge, other)
  def __gt__(self, other): return self._cmp(operator.gt, other)
  def __le__(self, other): return self._cmp(operator.le, other)
  def __lt__(self, other): return self._cmp(operator.lt, other)
  def __ne__(self, other): return self._cmp(operator.ne, other)


class IntType(Type, Comparable):
  __slots__ = ('width',)
  def __init__(self, width):
    self.width = width
  
  def __repr__(self):
    return 'IntType({0!r})'.format(self.width)

  def __str__(self):
    return 'i' + str(self.width)

  def __hash__(self):
    return hash(type(self)) ^ hash(self.width)

  def _cmp(self, op, other):
    if isinstance(other, int):
      return op(self.width, other)
    if isinstance(other, IntType):
      return op(self.width, other.width)

    return NotImplemented

class PtrType(Type):
  __slots__ = ()

  # for now, assume a single pointer type
  def __eq__(self, other):
    return type(self) is type(other)

  def __ne__(self, other):
    return not(self == other)

  def __hash__(self):
    return hash(PtrType) * 2

  def __repr__(self):
    return 'PtrType()'

class FloatType(Type, Comparable):
  __slots__ = ()

  def __repr__(self):
    return type(self).__name__ + '()'

  def __hash__(self):
    return hash(type(self)) * 2

  def _cmp(self, op, other):
    if isinstance(other, int):
      return op(self.frac, other)
    if isinstance(other, FloatType):
      return op(self.frac, other.frac)

    return NotImplemented

class HalfType(FloatType):
  __slots__ = ()
  exp = 5
  frac = 11

  def __str__(self): return 'half'

class SingleType(FloatType):
  __slots__ = ()
  exp = 8
  frac = 24

  def __str__(self): return 'float'

class DoubleType(FloatType):
  __slots__ = ()
  exp = 11
  frac = 53

  def __str__(self): return 'double'


# DAG Nodes
# ---------

class MetaNode(type):
  'Automatically generate a superclass table for Node classes'

  def __new__(cls, name, bases, dict):
    if '__slots__' not in dict:
      dict['__slots__'] = ()

    return super(MetaNode, cls).__new__(cls, name, bases, dict)

  def __init__(cls, name, bases, dict):
    if not hasattr(cls, 'registry'):
      cls.registry = {}
    else:
      cls.registry[name] = bases[0].__name__

    if hasattr(cls, 'code'):
      assert cls.code not in cls.codes
      cls.codes[cls.code] = cls

    if '__slots__' in dict:
      cls._allslots = getattr(cls, '_allslots', ()) + tuple(dict['__slots__'])

    return super(MetaNode, cls).__init__(name, bases, dict)

class Node(pretty.PrettyRepr):
  __metaclass__ = MetaNode

  def accept(self, visitor, *args, **kws):
    return getattr(visitor, type(self).__name__)(self, *args, **kws)
    # makes the stack trace slightly ugly, but saves a bunch of typing

  def pretty(self):
    args = (getattr(self,s) for s in self._allslots)
    return pretty.pfun(type(self).__name__, args)

# NOTE: these are desirable, but shouldn't be activated until typing
# and smtinterp are thought through. In particular, two instances of
# "log2(C)" may not have the same type, so they shouldn't be conflated
# during type checking.
#
#   def __eq__(self, other):
#     return type(self) is type(other) and \
#       all(getattr(self,s) == getattr(other,s) for s in self.__slots__)
# 
#   def __hash__(self):
#     key = tuple(getattr(self,s) for s in self.__slots__)
#     h = hash(type(self)) ^ hash(key)
#     return h

  def args(self):
    return tuple(getattr(self,s) for s in self._allslots)

  def copy(self, **kws):
    args = tuple(kws[s] if s in kws else getattr(self,s)
                  for s in self._allslots)

    return type(self)(*args)

  def type_constraints(self, tcs):
    raise NotImplementedError(type(self).__name__ + \
      ' should override type_constraints')

class Value(Node):
  pass


class Input(Value):
  __slots__ = ('name',)
  def __init__(self, name):
    self.name = name
  
  def args(self):
    return ()

  def type_constraints(self, tcs):
    tcs.first_class(self)

class Instruction(Value):
  pass

class BinaryOperator(Instruction):
  __slots__ = ('x','y','ty','flags','name')
  codes = {}

  def __init__(self, x, y, ty = None, flags = (), name=''):
    self.ty = ty
    self.x = x
    self.y = y
    self.flags = tuple(flags)
    self.name = name

  def args(self):
    return (self.x, self.y)

class IntBinaryOperator(BinaryOperator):
  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.specific(self, self.ty)
    tcs.eq_types(self, self.x, self.y)

class WrappingBinaryOperator(IntBinaryOperator): pass
class InexactBinaryOperator(IntBinaryOperator): pass

class AddInst(WrappingBinaryOperator): code = 'add'
class SubInst(WrappingBinaryOperator): code = 'sub'
class MulInst(WrappingBinaryOperator): code = 'mul'
class SDivInst(InexactBinaryOperator): code = 'sdiv'
class UDivInst(InexactBinaryOperator): code = 'udiv'
class SRemInst(IntBinaryOperator):     code = 'srem'
class URemInst(IntBinaryOperator):     code = 'urem'
class ShlInst(WrappingBinaryOperator): code = 'shl'
class AShrInst(InexactBinaryOperator): code = 'ashr'
class LShrInst(InexactBinaryOperator): code = 'lshr'
class AndInst(IntBinaryOperator):      code = 'and'
class OrInst(IntBinaryOperator):       code = 'or'
class XorInst(IntBinaryOperator):      code = 'xor'


class FastMathInst(Instruction): pass

class FloatBinaryOperator(BinaryOperator, FastMathInst):
  def type_constraints(self, tcs):
    tcs.float(self)
    tcs.specific(self, self.ty)
    tcs.eq_types(self, self.x, self.y)


class FAddInst(FloatBinaryOperator): code = 'fadd'
class FSubInst(FloatBinaryOperator): code = 'fsub'
class FMulInst(FloatBinaryOperator): code = 'fmul'
class FDivInst(FloatBinaryOperator): code = 'fdiv'
class FRemInst(FloatBinaryOperator): code = 'frem'


class ConversionInst(Instruction):
  __slots__ = ('arg', 'src_ty', 'ty', 'name')
  codes = {}

  def __init__(self, arg, src_ty = None, dest_ty = None, name = ''):
    self.src_ty = src_ty
    self.arg = arg
    self.ty = dest_ty
    self.name = name

  def args(self):
    return (self.arg,)

class BitcastInst(ConversionInst):
  code = 'bitcast'

  def type_constraints(self, tcs):
    tcs.specific(self, self.ty)
    tcs.specific(self.arg, self.src_ty)
    tcs.width_equal(self.arg, self)

class SExtInst(ConversionInst):
  code = 'sext'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.integer(self.arg)
    tcs.specific(self, self.ty)
    tcs.specific(self.arg, self.src_ty)
    tcs.width_order(self.arg, self)

class ZExtInst(ConversionInst):
  code = 'zext'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.integer(self.arg)
    tcs.specific(self, self.ty)
    tcs.specific(self.arg, self.src_ty)
    tcs.width_order(self.arg, self)

class TruncInst(ConversionInst):
  code = 'trunc'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.integer(self.arg)
    tcs.specific(self, self.ty)
    tcs.specific(self.arg, self.src_ty)
    tcs.width_order(self, self.arg)

class ZExtOrTruncInst(ConversionInst):
  code = 'ZExtOrTrunc'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.integer(self.arg)
    tcs.specific(self, self.ty)
    tcs.specific(self.arg, self.src_ty)

class FPtoSIInst(ConversionInst):
  code = 'fptosi'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.float(self.arg)
    tcs.specific(self, self.ty)
    tcs.specific(self.arg, self.src_ty)

class FPtoUIInst(ConversionInst):
  code = 'fptoui'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.float(self.arg)
    tcs.specific(self, self.ty)
    tcs.specific(self.arg, self.src_ty)

class SItoFPInst(ConversionInst):
  code = 'sitofp'

  def type_constraints(self, tcs):
    tcs.float(self)
    tcs.integer(self.arg)
    tcs.specific(self, self.ty)
    tcs.specific(self.arg, self.src_ty)

class UItoFPInst(ConversionInst):
  code = 'uitofp'

  def type_constraints(self, tcs):
    tcs.float(self)
    tcs.integer(self.arg)
    tcs.specific(self, self.ty)
    tcs.specific(self.arg, self.src_ty)

class FPTruncInst(ConversionInst):
  code = 'fptrunc'

  def type_constraints(self, tcs):
    tcs.float(self)
    tcs.float(self.arg)
    tcs.specific(self, self.ty)
    tcs.specific(self.arg, self.src_ty)
    tcs.width_order(self, self.arg)

class FPExtInst(ConversionInst):
  code = 'fpext'

  def type_constraints(self, tcs):
    tcs.float(self)
    tcs.integer(self.arg)
    tcs.specific(self, self.ty)
    tcs.specific(self.arg, self.src_ty)
    tcs.width_order(self.arg, self)

class IcmpInst(Instruction):
  __slots__ = ('pred', 'x', 'y', 'ty', 'name')

  def __init__(self, pred, arg1, arg2, ty = None, name = ''):
    self.pred = pred # FIXME: handle comparison ops better somehow?
    self.ty   = ty
    self.x    = arg1
    self.y    = arg2
    self.name = name

  def args(self):
    return (self.x, self.y)

  def type_constraints(self, tcs):
    tcs.bool(self)
    tcs.int_ptr_vec(self.x)
    tcs.specific(self.x, self.ty)
    tcs.eq_types(self.x, self.y)

class FcmpInst(FastMathInst):
  __slots__ = ('pred','x','y','ty','flags','name')

  def __init__(self, pred, arg1, arg2, ty=None, flags=(), name=''):
    self.pred  = pred  #FIXME: validate ops
    self.ty    = ty
    self.flags = flags
    self.x     = arg1
    self.y     = arg2
    self.name  = name

  def args(self):
    return (self.x, self.y)

  def type_constraints(self, tcs):
    tcs.bool(self)
    tcs.float(self.x)
    tcs.specific(self.x, self.ty)
    tcs.eq_types(self.x, self.y)

class SelectInst(Instruction):
  __slots__ = ('sel', 'arg1', 'arg2', 'ty1', 'ty2', 'name')

  def __init__(self, sel, arg1, arg2, ty1 = None, ty2 = None, name = ''):
    self.sel  = sel
    self.ty1  = ty1
    self.arg1 = arg1
    self.ty2  = ty2
    self.arg2 = arg2
    self.name = name

  def args(self):
    return (self.sel, self.arg1, self.arg2)

  def type_constraints(self, tcs):
    tcs.bool(self.sel)
    tcs.first_class(self)
    tcs.specific(self.arg1, self.ty1)
    tcs.specific(self.arg2, self.ty2)
    tcs.eq_types(self, self.arg1, self.arg2)

# Constants
# ---------

class Constant(Value):
  pass

class Symbol(Input, Constant):
  '''Symbolic constants.
  '''
  
  def type_constraints(self, tcs):
    tcs.number(self)

# These behave like Inputs. In particular, Symbol defaults to Input in
# visitors. Having a separate class that inherits from both avoids the
# need for code like
#   isinstance(x, Constant) or (isinstance(x, Input) and x.name[0] == 'C')
# and is cleaner in general

class Literal(Constant):
  __slots__ = ('val',)

  def __init__(self, val):
    self.val = val
# TODO: need type for null?

  def args(self):
    return ()

  def type_constraints(self, tcs):
    tcs.number(self)

    x = self.val
    bl = x.bit_length() if x >= 0 else (-x-1).bit_length()+1
    if bl > 0:
      tcs.width_order(bl-1, self) # bl-1 because the ceiling is a hard limit

class FLiteral(Constant):
  def type_constraints(self, tcs):
    tcs.float(self)

class FLiteralNaN(FLiteral): val = 'nan'
class FLiteralPlusInf(FLiteral): val = 'inf'
class FLiteralMinusInf(FLiteral): val = '-inf'
class FLiteralMinusZero(FLiteral): val = '-0.0'

class FLiteralVal(FLiteral):
  __slots__ = ('val',)
  def __init__(self, val):
    self.val = val

  def __repr__(self):
    return 'FLiteral(' + repr(self.val) + ')'

  def args(self):
    return ()

class UndefValue(Constant):
  # not sure this is a constant, rather than an arbitrary value
  __slots__ = ('ty',)

  def __init__(self, ty = None):
    self.ty = ty

  def args(self):
    return ()

  def type_constraints(self, tcs):
    tcs.first_class(self)
    tcs.specific(self, self.ty)

class PoisonValue(Constant):
  def type_constraints(self, tcs):
    tcs.first_class(self)

class BinaryCnxp(Constant):
  __slots__ = ('x','y')
  codes = {}

  def __init__(self, x, y):
    self.x = x
    self.y = y

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.eq_types(self, self.x, self.y)

class NumBinaryCnxp(BinaryCnxp):
  def type_constraints(self, tcs):
    tcs.number(self)
    tcs.eq_types(self, self.x, self.y)

class AddCnxp(NumBinaryCnxp):  code = '+'
class SubCnxp(NumBinaryCnxp):  code = '-'
class MulCnxp(NumBinaryCnxp):  code = '*'
class SDivCnxp(NumBinaryCnxp): code = '/'
class UDivCnxp(BinaryCnxp): code = '/u'
class SRemCnxp(NumBinaryCnxp): code = '%'
class URemCnxp(BinaryCnxp): code = '%u'
class ShlCnxp(BinaryCnxp):  code = '<<'
class AShrCnxp(BinaryCnxp): code = '>>'
class LShrCnxp(BinaryCnxp): code = 'u>>'
class AndCnxp(BinaryCnxp):  code = '&'
class OrCnxp(BinaryCnxp):   code = '|'
class XorCnxp(BinaryCnxp):  code = '^'


# NOTE: do we need these?
class UnaryCnxp(Constant):
  __slots__ = ('x',)
  codes = {}

  def __init__(self, x):
    self.x = x

class NegCnxp(UnaryCnxp):
  code = '-'

  def type_constraints(self, tcs):
    tcs.number(self)
    tcs.eq_types(self, self.x)

class NotCnxp(UnaryCnxp):
  code = '~'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.eq_types(self, self.x)

class FunCnxp(Constant):
  __slots__ = ('_args',)
  codes = {}

  @classmethod
  def check_args(cls, args):
    if len(args) != len(cls.sig):
      raise BadArgumentCount(len(cls.sig), len(args))

    for i in xrange(len(args)):
      if not isinstance(args[i], cls.sig[i]):
        raise BadArgumentKind(i, cls.sig[i])

  def __init__(self, *args):
    self.check_args(args)
    self._args = args

  def pretty(self):
    return pretty.pfun_(type(self).__name__, self._args)

  def args(self):
    return self._args

class AbsCnxp(FunCnxp):
  sig  = (Constant,)
  code = 'abs'

  def type_constraints(self, tcs):
    tcs.number(self)
    tcs.eq_types(self, self._args[0])

class SignBitsCnxp(FunCnxp):
  sig  = (Value,)
  code = 'ComputeNumSignBits'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.integer(self._args[0])

class OneBitsCnxp(FunCnxp):
  sig  = (Value,)
  code = 'computeKnownOneBits'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.eq_types(self, self._args[0])

class ZeroBitsCnxp(FunCnxp):
  sig  = (Value,)
  code = 'computeKnownZeroBits'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.eq_types(self, self._args[0])

class LeadingZerosCnxp(FunCnxp):
  sig  = (Constant,)
  code = 'countLeadingZeros'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.integer(self._args[0])

class TrailingZerosCnxp(FunCnxp):
  sig  = (Constant,)
  code = 'countTrailingZeros'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.integer(self._args[0])

class FPMantissaWidthCnxp(FunCnxp):
  sig  = (Value,)
  code = 'fpMantissaWidth'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.float(self._args[0])

class LShrFunCnxp(FunCnxp):
  sig  = (Constant, Constant)
  code = 'lshr'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.eq_types(self, *self._args)

class Log2Cnxp(FunCnxp):
  sig  = (Constant,)
  code = 'log2'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.integer(self._args[0])

class SMaxCnxp(FunCnxp):
  sig  = (Constant, Constant)
  code = 'max'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.eq_types(self, *self._args)

class SMinCnxp(FunCnxp):
  sig  = (Constant, Constant)
  code = 'min'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.eq_types(self, *self._args)

class SExtCnxp(FunCnxp):
  sig  = (Constant,)
  code = 'sext'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.integer(self._args[0])
    tcs.width_order(self._args[0], self)

class TruncCnxp(FunCnxp):
  sig  = (Constant,)
  code = 'trunc'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.integer(self._args[0])
    tcs.width_order(self, self._args[0])

class UMaxCnxp(FunCnxp):
  sig  = (Constant, Constant)
  code = 'umax'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.eq_types(self, *self._args)

class UMinCnxp(FunCnxp):
  sig  = (Constant, Constant)
  code = 'umin'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.eq_types(self, *self._args)

class WidthCnxp(FunCnxp):
  sig  = (Value,)
  code = 'width'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.integer(self._args[0])

class ZExtCnxp(FunCnxp):
  sig  = (Constant,)
  code = 'zext'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.integer(self._args[0])
    tcs.width_order(self._args[0], self)

class FPExtCnxp(FunCnxp):
  sig  = (Constant,)
  code = 'fpext'

  def type_constraints(self, tcs):
    tcs.float(self)
    tcs.float(self._args[0])
    tcs.width_order(self, self._args[0])

class FPTruncCnxp(FunCnxp):
  sig  = (Constant,)
  code = 'fptrunc'

  def type_constraints(self, tcs):
    tcs.float(self)
    tcs.float(self._args[0])
    tcs.width_order(self._args[0], self)

class FPtoSICnxp(FunCnxp):
  sig  = (Constant,)
  code = 'fptosi'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.float(self._args[0])

class FPtoUICnxp(FunCnxp):
  sig   = (Constant,)
  code  = 'fptoui'

  def type_constraints(self, tcs):
    tcs.integer(self)
    tcs.float(self._args[0])

class SItoFPCnxp(FunCnxp):
  sig   = (Constant,)
  code  = 'sitofp'

  def type_constraints(self, tcs):
    tcs.float(self)
    tcs.integer(self._args[0])

class UItoFPCnxp(FunCnxp):
  sig   = (Constant,)
  code  = 'uitofp'

  def type_constraints(self, tcs):
    tcs.float(self)
    tcs.integer(self._args[0])

# Predicates
# ----------

class Predicate(Node):
  pass

class AndPred(Predicate):
  __slots__ = ('clauses',)

  def __init__(self, *clauses):
    self.clauses = clauses

  def pretty(self):
    return pretty.pfun('AndPred', self.clauses)

  def args(self):
    return self.clauses

  def type_constraints(self, tcs):
    for p in self.clauses:
      p.type_constraints(tcs)

TruePred = AndPred()

class OrPred(Predicate):
  __slots__ = ('clauses',)

  def __init__(self, *clauses):
    self.clauses = clauses

  def pretty(self):
    return pretty.pfun('OrPred', self.clauses)

  def args(self):
    return self.clauses

  def type_constraints(self, tcs):
    for p in self.clauses:
      p.type_constraints(tcs)

class NotPred(Predicate):
  __slots__ = ('p',)

  def __init__(self, p):
    self.p = p

  def args(self):
    return (self.p,)

  def type_constraints(self, tcs):
    self.p.type_constraints(tcs)

class Comparison(Predicate):
  __slots__ = ('op','x','y')

  def __init__(self, op, x, y):
    self.op = op
    self.x  = x
    self.y  = y
# Better ops as subclasses?

  def args(self):
    return (self.x, self.y)

  def type_constraints(self, tcs):
    # FIXME
    if self.op[0] == 'u':
      tcs.integer(self.x)
      # unsigned comparisons are integer-only
      # note that ugt could also be unordered greater-than
    else:
      tcs.number(self.x)
    tcs.eq_types(self.x, self.y)

class FunPred(Predicate):
  __slots__ = ('_args',)
  codes = {}

  @classmethod
  def check_args(cls, args):
    if len(args) != len(cls.sig):
      raise BadArgumentCount(len(cls.sig), len(args))

    for i in xrange(len(args)):
      if not isinstance(args[i], cls.sig[i]):
        raise BadArgumentKind(i, cls.sig[i])

  def __init__(self, *args):
    self.check_args(args)
    self._args = args

  def pretty(self):
    return pretty.pfun(type(self).__name__, self._args)

  def args(self):
    return self._args

def _none(term, tcs):
  pass

def _one_int(term, tcs):
  tcs.integer(term._args[0])

def _all_ints(term, tcs):
  tcs.integer(term._args[0])
  tcs.eq_types(*term._args)

def _one_float(term, tcs):
  tcs.float(term._args[0])

def _all_floats(term, tcs):
  tcs.float(term._args[0])
  tcs.eq_types(*term._args)

class CannotBeNegativeZeroPred(FunPred):
  sig  = (Value,)
  code = 'CannotBeNegativeZero'

  type_constraints = _one_float

class FPIdenticalPred(FunPred):
  sig  = (Constant, Constant)
  code = 'fpIdentical'

  type_constraints = _all_floats

class FPIntegerPred(FunPred):
  sig  = (Constant,)
  code = 'fpInteger'

  type_constraints = _one_float

class HasNInfPred(FunPred):
  sig  = (FastMathInst,)
  code = 'hasNoInf'

  type_constraints = _none

class HasNNaNPred(FunPred):
  sig  = (FastMathInst,)
  code = 'hasNoNaN'

  type_constraints = _none

class HasNSWPred(FunPred):
  sig  = (WrappingBinaryOperator,)
  code = 'hasNSW'

  type_constraints = _none

class HasNSZPred(FunPred):
  sig  = (FastMathInst,)
  code = 'hasNSZ'

  type_constraints = _none

class HasNUWPred(FunPred):
  sig  = (WrappingBinaryOperator,)
  code = 'hasNUW'

  type_constraints = _none

class IsExactPred(FunPred):
  sig  = (InexactBinaryOperator,)
  code = 'isExact'

  type_constraints = _none

class IntMinPred(FunPred): 
  sig  = (Constant,)
  code = 'isSignBit'

  type_constraints = _one_int

class Power2Pred(FunPred):
  sig   = (Value,)
  code  = 'isPowerOf2'

  type_constraints = _one_int

class Power2OrZPred(FunPred):
  sig   = (Value,)
  code  = 'isPowerOf2OrZero'

  type_constraints = _one_int

class ShiftedMaskPred(FunPred):
  sig   = (Constant,)
  code  = 'isShiftedMask'

  type_constraints = _one_int

class MaskZeroPred(FunPred):
  sig   = (Value, Constant)
  code  = 'MaskedValueIsZero'

  type_constraints = _all_ints

class NSWAddPred(FunPred):
  sig   = (Value, Value)
  code  = 'WillNotOverflowSignedAdd'

  type_constraints = _all_ints

class NUWAddPred(FunPred):
  sig   = (Value, Value)
  code  = 'WillNotOverflowUnsignedAdd'

  type_constraints = _all_ints

class NSWSubPred(FunPred):
  sig   = (Value, Value)
  code  = 'WillNotOverflowSignedSub'

  type_constraints = _all_ints

class NUWSubPred(FunPred):
  sig   = (Value, Value)
  code  = 'WillNotOverflowUnsignedSub'

  type_constraints = _all_ints

class NSWMulPred(FunPred):
  sig   = (Constant, Constant)
  code  = 'WillNotOverflowSignedMul'

  type_constraints = _all_ints

class NUWMulPred(FunPred):
  sig   = (Constant, Constant)
  code  = 'WillNotOverflowUnsignedMul'

  type_constraints = _all_ints

class NUWShlPred(FunPred):
  sig   = (Constant, Constant)
  code  = 'WillNotOverflowUnsignedShl'

  type_constraints = _all_ints

class OneUsePred(FunPred):
  sig   = ((Input, Instruction),)  # NOTE: one arg that is Input or Instruction
  code  = 'hasOneUse'

  type_constraints = _none

# Utilities
# ---------

def subterms(term, seen = None):
  '''Generate all subterms of the provided term.

  No subterm is generated twice. All terms appear after their subterms.
  '''

  if seen is None:
    seen = set()
  elif term in seen:
    return

  for a in term.args():
    for s in subterms(a, seen):
      yield s

  seen.add(term)
  yield term

def proper_subterms(term):
  seen = set()

  return itertools.chain.from_iterable(subterms(a, seen) for a in term.args())

# Visitor
# -------

class MetaVisitor(type):
  '''Fill out the visiting functions which aren't explicitly defined by a
  class or its bases.

  NOTE: it's better to subclass Visitor than use this directly.
  '''

  def __new__(cls, name, bases, dict):
    visiting = [f for f in dict if f in Node.registry or f == 'Node']

    # add explicit methods in the base classes
    for b in bases:
      if not hasattr(b, '_visiting'): continue
      for f in b._visiting:
        if f in dict: continue
        dict[f] = getattr(b, f)
        visiting.append(f)

    dict['_visiting'] = tuple(visiting)
    assert 'Node' in dict

    # direct all non-explicitly defined visiting methods to their parents
    for f,p in Node.registry.iteritems():
      if f in dict: continue
      while p not in dict: p = Node.registry[p]
      dict[f] = dict[p]

    return super(MetaVisitor, cls).__new__(cls, name, bases, dict)

class Visitor(object):
  __metaclass__ = MetaVisitor

  def Node(self, term, *args, **kws):
    raise UnmatchedCase('Visitor {0!r} cannot handle class {1!r}'.format(
      type(self).__name__, type(term).__name__))



# Errors
# ------

class UnmatchedCase(Exception):
  pass

class BadArgumentCount(Exception):
  def __init__(self, wanted, got):
    self.wanted = wanted
    self.got = got

  def __str__(self):
    return 'expected {} received {}'.format(self.wanted, self.got)

class BadArgumentKind(Exception):
  def __init__(self, idx, kind):
    self.idx = idx
    self.kind = kind

  kinds = {
    Value: 'any value',
    Constant: 'constant',
    (Input,Instruction): 'register',
    FastMathInst: 'floating-point inst',
    WrappingBinaryOperator: 'add, sub, mul, or shl',
    InexactBinaryOperator: 'sdiv, udiv, ashr, or lshr',
  }

  def __str__(self):
    return 'parameter {} expected {}'.format(self.idx+1, self.kinds[self.kind])
