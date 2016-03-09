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


class Value(Node):
  pass


class Input(Value):
  __slots__ = ('name',)
  def __init__(self, name):
    self.name = name
  
  def args(self):
    return ()

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

class IntBinaryOperator(BinaryOperator): pass

class AddInst(IntBinaryOperator):  code = 'add'
class SubInst(IntBinaryOperator):  code = 'sub'
class MulInst(IntBinaryOperator):  code = 'mul'
class SDivInst(IntBinaryOperator): code = 'sdiv'
class UDivInst(IntBinaryOperator): code = 'udiv'
class SRemInst(IntBinaryOperator): code = 'srem'
class URemInst(IntBinaryOperator): code = 'urem'
class ShlInst(IntBinaryOperator):  code = 'shl'
class AShrInst(IntBinaryOperator): code = 'ashr'
class LShrInst(IntBinaryOperator): code = 'lshr'
class AndInst(IntBinaryOperator):  code = 'and'
class OrInst(IntBinaryOperator):   code = 'or'
class XorInst(IntBinaryOperator):  code = 'xor'


class FloatBinaryOperator(BinaryOperator): pass

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

class SExtInst(ConversionInst):
  code = 'sext'

class ZExtInst(ConversionInst):
  code = 'zext'

class TruncInst(ConversionInst):
  code = 'trunc'

class ZExtOrTruncInst(ConversionInst): code = 'ZExtOrTrunc'
class FPtoSIInst(ConversionInst): code = 'fptosi'
class FPtoUIInst(ConversionInst): code = 'fptoui'
class SItoFPInst(ConversionInst): code = 'sitofp'
class UItoFPInst(ConversionInst): code = 'uitofp'
class FPTruncInst(ConversionInst): code = 'fptrunc'
class FPExtInst(ConversionInst): code = 'fpext'

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

class FcmpInst(Instruction):
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

# Constants
# ---------

class Constant(Value):
  pass

class Symbol(Input, Constant):
  '''Symbolic constants.
  '''
  pass
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

class FLiteral(Constant): pass

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

class PoisonValue(Constant):
  pass

class BinaryCnxp(Constant):
  __slots__ = ('x','y')
  codes = {}

  def __init__(self, x, y):
    self.x = x
    self.y = y

class AddCnxp(BinaryCnxp):  code = '+'
class SubCnxp(BinaryCnxp):  code = '-'
class MulCnxp(BinaryCnxp):  code = '*'
class SDivCnxp(BinaryCnxp): code = '/'
class UDivCnxp(BinaryCnxp): code = '/u'
class SRemCnxp(BinaryCnxp): code = '%'
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

class NegCnxp(UnaryCnxp): code = '-'
class NotCnxp(UnaryCnxp): code = '~'


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

class SignBitsCnxp(FunCnxp):
  sig  = (Value,)
  code = 'ComputeNumSignBits'

class OneBitsCnxp(FunCnxp):
  sig  = (Value,)
  code = 'computeKnownOneBits'

class ZeroBitsCnxp(FunCnxp):
  sig  = (Value,)
  code = 'computeKnownZeroBits'

class LeadingZerosCnxp(FunCnxp):
  sig  = (Constant,)
  code = 'countLeadingZeros'

class TrailingZerosCnxp(FunCnxp):
  sig  = (Constant,)
  code = 'countTrailingZeros'

class FPMantissaWidthCnxp(FunCnxp):
  sig  = (Value,)
  code = 'fpMantissaWidth'

class LShrFunCnxp(FunCnxp):
  sig  = (Constant, Constant)
  code = 'lshr'

class Log2Cnxp(FunCnxp):
  sig  = (Constant,)
  code = 'log2'

class SMaxCnxp(FunCnxp):
  sig  = (Constant, Constant)
  code = 'max'

class SMinCnxp(FunCnxp):
  sig  = (Constant, Constant)
  code = 'min'

class SExtCnxp(FunCnxp):
  sig  = (Constant,)
  code = 'sext'

class TruncCnxp(FunCnxp):
  sig  = (Constant,)
  code = 'trunc'

class UMaxCnxp(FunCnxp):
  sig  = (Constant, Constant)
  code = 'umax'

class UMinCnxp(FunCnxp):
  sig  = (Constant, Constant)
  code = 'umin'

class WidthCnxp(FunCnxp):
  sig  = (Value,)
  code = 'width'

class ZExtCnxp(FunCnxp):
  sig  = (Constant,)
  code = 'zext'

class FPExtCnxp(FunCnxp):
  sig  = (Constant,)
  code = 'fpext'

class FPTruncCnxp(FunCnxp):
  sig  = (Constant,)
  code = 'fptrunc'

class FPtoSICnxp(FunCnxp):
  sig  = (Constant,)
  code = 'fptosi'

class FPtoUICnxp(FunCnxp):
  sig   = (Constant,)
  code  = 'fptoui'

class SItoFPCnxp(FunCnxp):
  sig   = (Constant,)
  code  = 'sitofp'

class UItoFPCnxp(FunCnxp):
  sig   = (Constant,)
  code  = 'uitofp'

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

TruePred = AndPred()

class OrPred(Predicate):
  __slots__ = ('clauses',)

  def __init__(self, *clauses):
    self.clauses = clauses

  def pretty(self):
    return pretty.pfun('OrPred', self.clauses)

  def args(self):
    return self.clauses

class NotPred(Predicate):
  __slots__ = ('p',)

  def __init__(self, p):
    self.p = p

  def args(self):
    return (self.p,)

class Comparison(Predicate):
  __slots__ = ('op','x','y')

  def __init__(self, op, x, y):
    self.op = op
    self.x  = x
    self.y  = y
# Better ops as subclasses?

  def args(self):
    return (self.x, self.y)

class FunPred(Predicate):
  __slots__ = ('_args',)
  codes = {}

  @classmethod
  def check_args(cls, args):
    if len(args) != len(cls.sig):
      raise BadArgumentCount(len(cls.sig), len(args))

    for i in xrange(len(args)):
      if not isinstance(args[0], cls.sig[0]):
        raise BadArgumentKind(i, cls.sig[0])

  def __init__(self, *args):
    self.check_args(args)
    self._args = args

  def pretty(self):
    return pretty.pfun(type(self).__name__, self._args)

  def args(self):
    return self._args

class CannotBeNegativeZeroPred(FunPred):
  sig  = (Value,)
  code = 'CannotBeNegativeZero'

class FPIdenticalPred(FunPred):
  sig  = (Constant, Constant)
  code = 'fpIdentical'

class FPIntegerPred(FunPred):
  sig  = (Constant,)
  code = 'fpInteger'

class IntMinPred(FunPred): 
  sig  = (Constant,)
  code = 'isSignBit'

class Power2Pred(FunPred):
  sig   = (Value,)
  code  = 'isPowerOf2'

class Power2OrZPred(FunPred):
  sig   = (Value,)
  code  = 'isPowerOf2OrZero'

class ShiftedMaskPred(FunPred):
  sig   = (Constant,)
  code  = 'isShiftedMask'

class MaskZeroPred(FunPred):
  sig   = (Value, Constant)
  code  = 'MaskedValueIsZero'

class NSWAddPred(FunPred):
  sig   = (Value, Value)
  code  = 'WillNotOverflowSignedAdd'

class NUWAddPred(FunPred):
  sig   = (Value, Value)
  code  = 'WillNotOverflowUnsignedAdd'

class NSWSubPred(FunPred):
  sig   = (Value, Value)
  code  = 'WillNotOverflowSignedSub'

class NUWSubPred(FunPred):
  sig   = (Value, Value)
  code  = 'WillNotOverflowUnsignedSub'

class NSWMulPred(FunPred):
  sig   = (Constant, Constant)
  code  = 'WillNotOverflowSignedMul'

class NUWMulPred(FunPred):
  sig   = (Constant, Constant)
  code  = 'WillNotOverflowUnsignedMul'

class NUWShlPred(FunPred):
  sig   = (Constant, Constant)
  code  = 'WillNotOverflowUnsignedShl'

class OneUsePred(FunPred):
  sig   = ((Input, Instruction),)  # NOTE: one arg that is Input or Instruction
  code  = 'hasOneUse'

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


# Type constraints
# ----------------

def _int_monad(self, term):
  self.integer(term._args[0])

def _int_pred(self, term):
  self.integer(term._args[0])
  self.eq_types(*term._args)

class BaseTypeConstraints(Visitor):
  def Input(self, term):
    self.first_class(term)

  def Symbol(self, term):
    self.number(term)

  def IntBinaryOperator(self, term):
    self.specific(term, term.ty)
    self.eq_types(term, term.x, term.y)
    self.integer(term)

  def FloatBinaryOperator(self, term):
    self.float(term)
    self.specific(term, term.ty)
    self.eq_types(term, term.x, term.y)

  def SExtInst(self, term):
    self.ZExtInst(term)

  def ZExtInst(self, term):
    self.specific(term, term.ty)
    self.specific(term.arg, term.src_ty)
    self.integer(term)
    self.integer(term.arg)
    self.width_order(term.arg, term)

  def TruncInst(self, term):
    self.specific(term, term.ty)
    self.specific(term.arg, term.src_ty)
    self.integer(term)
    self.integer(term.arg)
    self.width_order(term, term.arg)

  def ZExtOrTruncInst(self, term):
    self.integer(term)
    self.integer(term.arg)
    self.specific(term, term.ty)
    self.specific(term.arg, term.src_ty)

  def FPtoSIInst(self, term):
    self.integer(term)
    self.float(term.arg)
    self.specific(term, term.ty)
    self.specific(term.arg, term.src_ty)

  def FPtoUIInst(self, term):
    self.integer(term)
    self.float(term.arg)
    self.specific(term, term.ty)
    self.specific(term.arg, term.src_ty)

  def SItoFPInst(self, term):
    self.float(term)
    self.integer(term.arg)
    self.specific(term, term.ty)
    self.specific(term.arg, term.src_ty)

  def FPExtInst(self, term):
    self.specific(term, term.ty)
    self.specific(term.arg, term.src_ty)
    self.float(term)
    self.float(term.arg)
    self.width_order(term.arg, term)

  def FPTruncInst(self, term):
    self.specific(term, term.ty)
    self.specific(term.arg, term.src_ty)
    self.float(term)
    self.float(term.arg)
    self.width_order(term, term.arg)

  def UItoFPInst(self, term):
    self.float(term)
    self.integer(term.arg)
    self.specific(term, term.ty)
    self.specific(term.arg, term.src_ty)

  def IcmpInst(self, term):
    self.bool(term)
    self.int_ptr_vec(term.x)
    self.specific(term.x, term.ty)
    self.eq_types(term.x, term.y)

  def FcmpInst(self, term):
    self.bool(term)
    self.float(term.x)
    self.specific(term.x, term.ty)
    self.eq_types(term.x, term.y)

  def SelectInst(self, term):
    self.bool(term.sel)
    self.first_class(term.arg1)
    self.specific(term.arg1, term.ty1)
    self.specific(term.arg2, term.ty2)
    self.eq_types(term, term.arg1, term.arg2)

  def Literal(self, term):
    self.number(term)

    x = term.val
    bl = x.bit_length() if x >= 0 else (-x-1).bit_length()+1
    if bl > 0:
      self.width_order(bl-1, term)  # bl-1 because the ceiling is a hard limit

  def FLiteral(self, term):
    self.float(term)
    # TODO: set minimum float size?

  def UndefValue(self, term):
    self.first_class(term)
    self.specific(term, term.ty)

  def PoisonValue(self, term):
    self.first_class(term)

  def BinaryCnxp(self, term):
    # FIXME
    if isinstance(term, (AddCnxp, SubCnxp, MulCnxp, SDivCnxp, SRemCnxp)):
      self.number(term)
    else:
      self.integer(term)
    self.eq_types(term, term.x, term.y)

  def NegCnxp(self, term):
    self.number(term)
    self.eq_types(term, term.x)

  def NotCnxp(self, term):
    self.integer(term)
    self.eq_types(term, term.x)

  def AbsCnxp(self, term):
    self.number(term)
    self.eq_types(term, term._args[0])

  def SignBitsCnxp(self, term):
    self.integer(term)
    self.integer(term._args[0])

  def OneBitsCnxp(self, term):
    self.integer(term)
    self.eq_types(term, term._args[0])

  def ZeroBitsCnxp(self, term):
    self.integer(term)
    self.eq_types(term, term._args[0])

  def LeadingZerosCnxp(self, term):
    self.integer(term)
    self.integer(term._args[0])

  def TrailingZerosCnxp(self, term):
    self.integer(term)
    self.integer(term._args[0])

  def FPMantissaWidthCnxp(self, term):
    self.float(term._args[0])
    self.integer(term)

  def LShrFunCnxp(self, term):
    self.integer(term)
    self.eq_types(term, *term._args)

  def Log2Cnxp(self, term):
    self.integer(term)
    self.integer(term)

  def SMaxCnxp(self, term):
    self.integer(term)
    self.eq_types(term, *term._args)

  SMinCnxp = SMaxCnxp

  def UMaxCnxp(self, term):
    self.integer(term)
    self.eq_types(term, *term._args)

  UMinCnxp = UMaxCnxp

  def SExtCnxp(self, term):
    self.integer(term)
    self.integer(term._args[0])
    self.width_order(term._args[0], term)

  def ZExtCnxp(self, term):
    self.integer(term)
    self.integer(term._args[0])
    self.width_order(term._args[0], term)

  def TruncCnxp(self, term):
    self.integer(term)
    self.integer(term._args[0])
    self.width_order(term, term._args[0])

  def FPtoSICnxp(self, term):
    self.float(term._args[0])
    self.integer(term)

  def FPtoUICnxp(self, term):
    self.float(term._args[0])
    self.integer(term)

  def SItoFPCnxp(self, term):
    self.integer(term._args[0])
    self.float(term)

  def UItoFPCnxp(self, term):
    self.integer(term._args[0])
    self.float(term)

  def FPExtCnxp(self, term):
    self.float(term)
    self.float(term._args[0])
    self.width_order(term, term._args[0])

  def FPTruncCnxp(self, term):
    self.float(term)
    self.float(term._args[0])
    self.width_order(term, term._args[0])

  def WidthCnxp(self, term):
    self.integer(term)
    self.integer(term._args[0])
    # NOTE: return type of width may be too small to hold value
    # NOTE: should we allow width of pointers?
    # NOTE: should we allow width() to return fp?

  def AndPred(self, term):
    for p in term.clauses:
      p.accept(self)

  def OrPred(self, term):
    for p in term.clauses:
      p.accept(self)

  def NotPred(self, term):
    term.p.accept(self)

  def Comparison(self, term):
    # FIXME
    if term.op[0] == 'u':
      self.integer(term.x)
      # unsigned comparisons are integer-only
      # note that ugt could also be unordered greater-than
    else:
      self.number(term.x)
    self.eq_types(term.x, term.y)

  def CannotBeNegativeZeroPred(self, term):
    self.float(term._args[0])

  def FPIdenticalPred(self, term):
    self.float(term._args[0])
    self.eq_types(*term._args)

  def FPIntegerPred(self, term):
    self.float(term._args[0])

  IntMinPred = _int_monad
  Power2Pred = _int_monad
  Power2OrZPred = _int_monad
  ShiftedMaskPred = _int_monad
  MaskZeroPred = _int_pred
  NSWAddPred = _int_pred
  NUWAddPred = _int_pred
  NSWSubPred = _int_pred
  NUWSubPred = _int_pred
  NSWMulPred = _int_pred
  NUWMulPred = _int_pred
  NUWShlPred = _int_pred
  
  def OneUsePred(self, term):
    pass


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
  }

  def __str__(self):
    return 'parameter {} expected {}'.format(self.idx+1, self.kinds[self.kind])
