'''
Defines the internal representation as nodes in a DAG.
'''


# Type system
# -----------

class Type(object):
  pass

class IntType(Type):
  def __init__(self, width):
    self.width = width
  
  def __repr__(self):
    return 'IntType({0!r})'.format(self.width)
  
  def __eq__(self, other):
    return type(other) is IntType and self.width == other.width

class FloatType(Type):
  def __repr__(self):
    return type(self).__name__ + '()'

  def __eq__(self, other):
    return type(other) is type(self)

class HalfType(FloatType):
  exp = 5
  frac = 11

class SingleType(FloatType):
  exp = 8
  frac = 24

class DoubleType(FloatType):
  exp = 11
  frac = 53



# DAG Nodes
# ---------

class MetaNode(type):
  'Automatically generate a superclass table for Node classes'
  def __init__(cls, name, bases, dict):
    if not hasattr(cls, 'registry'):
      cls.registry = {}
    else:
      cls.registry[name] = bases[0].__name__

    if hasattr(cls, 'code'):
      assert cls.code not in cls.codes
      cls.codes[cls.code] = cls

    return super(MetaNode, cls).__init__(cls, bases, dict)

class Node(object):
  __metaclass__ = MetaNode

#   def __repr__(self):
#     return type(self).__name__ + '()'
  
  def accept(self, visitor, *args, **kws):
    return getattr(visitor, type(self).__name__)(self, *args, **kws)
    # makes the stack trace slightly ugly, but saves a bunch of typing

class Value(Node):
  pass


class Input(Value):
  def __init__(self, name):
    self.name = name
    self.type = None
  
  def __repr__(self):
    return 'Input({0.name!r})'.format(self)
  
  def args(self):
    return ()

class Instruction(Value):
  pass

class BinaryOperator(Instruction):
  codes = {}

  def __init__(self, x, y, ty = None, flags = (), name=''):
    self.ty = ty
    self.x = x
    self.y = y
    self.flags = tuple(flags)
    self.name = name
  
  def __repr__(self):
    return '{0.__name__}({1.x!r}, {1.y!r}, {1.ty!r}, {1.flags!r})'.format(type(self), self)

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


class ConversionInst(Instruction):
  codes = {}

  def __init__(self, arg, src_ty = None, dest_ty = None, name = ''):
    self.src_ty = src_ty
    self.arg = arg
    self.ty = dest_ty
    self.name = name

  def __repr__(self):
    return '{0.__name__}({1.arg!r}, {1.src_ty!r}, {1.ty!r})'.format(type(self), self)

  def args(self):
    return (self.arg,)

class SExtInst(ConversionInst):
  code = 'sext'

class ZExtInst(ConversionInst):
  code = 'zext'

class TruncInst(ConversionInst):
  code = 'trunc'

class ZExtOrTruncInst(ConversionInst): code = 'ZExtOrTrunc'

class IcmpInst(Instruction):
  def __init__(self, pred, arg1, arg2, ty = None, name = ''):
    self.pred = pred # FIXME: handle comparison ops better somehow?
    self.ty   = ty
    self.x    = arg1
    self.y    = arg2
    self.name = name

  def __repr__(self):
    return 'IcmpInst({0.pred!r}, {0.x!r}, {0.y!r}, {0.ty!r})'.format(self)

  def args(self):
    return (self.x, self.y)

class SelectInst(Instruction):
  def __init__(self, sel, arg1, arg2, ty1 = None, ty2 = None, name = ''):
    self.sel  = sel
    self.ty1  = ty1
    self.arg1 = arg1
    self.ty2  = ty2
    self.arg2 = arg2
    self.name = name

  def __repr__(self):
    return 'SelectInst({0.sel!r}, {0.arg1!r}, {0.arg2!r}, {0.ty1!r}, {0.ty2!r})'.format(self)

  def args(self):
    return (self.sel, self.arg1, self.arg2)

# Constants
# ---------

class Constant(Value):
  pass

class Literal(Constant):
  def __init__(self, val):
    self.val = val
# TODO: need type for null?

  def __repr__(self):
    return 'Literal({0!r})'.format(self.val)

  def args(self):
    return ()

class FLiteral(Constant):
  def __init__(self, val):
    self.val = val

  def __repr__(self):
    return 'FLiteral(' + repr(self.val) + ')'

  def args(self):
    return ()

class UndefValue(Constant):
  # not sure this is a constant, rather than an arbitrary value
  def __init__(self, ty = None):
    self.ty = ty

  def args(self):
    return ()

class BinaryCnxp(Constant):
  codes = {}

  def __init__(self, x, y):
    self.x = x
    self.y = y

  def __repr__(self):
    return '{0.__name__}({1.x!r}, {1.y!r})'.format(type(self), self)

  def args(self):
    return (self.x, self.y)

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
  codes = {}

  def __init__(self, x):
    self.x = x

  def __repr__(self):
    return '{0.__name__}({1.x!r})'.format(type(self), self)

  def args(self):
    return (self.x,)

class NegCnxp(UnaryCnxp): code = '-'
class NotCnxp(UnaryCnxp): code = '~'


class FunCnxp(Constant):
  codes = {}

  def __init__(self, *args):
    self._args = args
    assert len(args) == self.arity
  
  def __repr__(self):
    return type(self).__name__ + '(' + ', '.join(repr(a) for a in self._args) + ')'

  def args(self):
    return self._args

class AbsCnxp(FunCnxp):
  arity = 1
  code = 'abs'

class SignBitsCnxp(FunCnxp):
  arity = 1
  code  = 'ComputeNumSignBits'

class OneBitsCnxp(FunCnxp):
  arity = 1
  code  = 'computeKnownOneBits'

class ZeroBitsCnxp(FunCnxp):
  arity = 1
  code  = 'computeKnownZeroBits'

class LeadingZerosCnxp(FunCnxp):
  arity = 1
  code  = 'countLeadingZeros'

class TrailingZerosCnxp(FunCnxp):
  arity = 1
  code  = 'countTrailingZeros'

class LShrFunCnxp(FunCnxp):
  arity = 2
  code  = 'lshr'

class Log2Cnxp(FunCnxp):
  arity = 1
  code  = 'log2'

class SMaxCnxp(FunCnxp):
  arity = 2
  code  = 'max'

class SExtCnxp(FunCnxp):
  arity = 1
  code  = 'sext'

class TruncCnxp(FunCnxp):
  arity = 1
  code  = 'trunc'

class UMaxCnxp(FunCnxp):
  arity = 2
  code  = 'umax'

class WidthCnxp(FunCnxp):
  arity = 1
  code = 'width'

class ZExtCnxp(FunCnxp):
  arity = 1
  code = 'zext'

# Predicates
# ----------

class Predicate(Node):
  pass

class AndPred(Predicate):
  def __init__(self, *clauses):
    self.clauses = clauses

  def __repr__(self):
    return 'AndPred(' + ', '.join(repr(a) for a in self.clauses) + ')'

  def args(self):
    return self.clauses

TruePred = AndPred()

class OrPred(Predicate):
  def __init__(self, *clauses):
    self.clauses = clauses

  def __repr__(self):
    return 'OrPred(' + ', '.join(repr(a) for a in self.clauses) + ')'

  def args(self):
    return self.clauses

class NotPred(Predicate):
  def __init__(self, p):
    self.p = p

  def __repr__(self):
    return 'NotPred(' + repr(self.p) + ')'

  def args(self):
    return (self.p,)

class Comparison(Predicate):
  def __init__(self, op, x, y):
    self.op = op
    self.x  = x
    self.y  = y
# Better ops as subclasses?

  def __repr__(self):
    return 'Comparison({0.op!r}, {0.x!r}, {0.y!r})'.format(self)

  def args(self):
    return (self.x, self.y)

class FunPred(Predicate):
  codes = {}

  def __init__(self, *args):
    self._args = args
    assert len(args) == self.arity

  def __repr__(self):
    return type(self).__name__ + '(' + ', '.join(repr(a) for a in self._args) + ')'

  def args(self):
    return self._args

class IntMinPred(FunPred): 
  arity = 1
  code = 'isSignBit'

class Power2Pred(FunPred):
  arity = 1
  code  = 'isPowerOf2'

class Power2OrZPred(FunPred):
  arity = 1
  code  = 'isPowerOf2OrZero'

class ShiftedMaskPred(FunPred):
  arity = 1
  code  = 'isShiftedMask'

class MaskZeroPred(FunPred):
  arity = 2
  code  = 'MaskedValueIsZero'

class NSWAddPred(FunPred):
  arity = 2
  code  = 'WillNotOverflowSignedAdd'

class NUWAddPred(FunPred):
  arity = 2
  code  = 'WillNotOverflowUnsignedAdd'

class NSWSubPred(FunPred):
  arity = 2
  code  = 'WillNotOverflowSignedSub'

class NUWSubPred(FunPred):
  arity = 2
  code  = 'WillNotOverflowUnsignedSub'

class NSWMulPred(FunPred):
  arity = 2
  code  = 'WillNotOverflowSignedMul'

class NUWMulPred(FunPred):
  arity = 2
  code  = 'WillNotOverflowUnsignedMul'

class NUWShlPred(FunPred):
  arity = 2
  code  = 'WillNotOverflowUnsignedShl'

class OneUsePred(FunPred):
  arity = 1
  code  = 'hasOneUse'


# Visitor
# -------

class UnmatchedCase(Exception):
  pass


def _int_monad(self, term):
  self.integer(term._args[0])

def _int_pred(self, term):
  self.integer(term._args[0])
  self.eq_types(*term._args)

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
  
  
class BaseTypeConstraints(Visitor):
  def Input(self, term):
    if term.name[0] == 'C':
      self.integer(term)
    else:
      self.first_class(term)

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
    self.integer(term) # TODO: should width_ceiling imply integer?
    self.integer(term.arg)
    self.width_ceiling(term.arg, term)

  def TruncInst(self, term):
    self.specific(term, term.ty)
    self.specific(term.arg, term.src_ty)
    self.integer(term)
    self.integer(term.arg)
    self.width_ceiling(term, term.arg)

  def ZExtOrTruncInst(self, term):
    self.integer(term)
    self.integer(term.arg)
    self.specific(term, term.ty)
    self.specific(term.arg, term.src_ty)

  def IcmpInst(self, term):
    self.bool(term)
    self.int_ptr_vec(term.x)
    self.specific(term.x, term.ty)
    self.eq_types(term.x, term.y)

  def SelectInst(self, term):
    self.bool(term.sel)
    self.first_class(term.arg1)
    self.specific(term.arg1, term.ty1)
    self.specific(term.arg2, term.ty2)
    self.eq_types(term, term.arg1, term.arg2)

  def Literal(self, term):
    self.integer(term)

    x = term.val
    bl = x.bit_length() if x >= 0 else (-x-1).bit_length()+1
    self.width_ceiling(x-1, term)  # -1 because the ceiling is a hard limit

  def FLiteral(self, term):
    self.float(term)
    # TODO: set minimum float size?

  def UndefValue(self, term):
    self.first_class(term)
    self.specific(term, term.ty)

  def BinaryCnxp(self, term):
    self.integer(term)
    self.eq_types(term, term.x, term.y)
  
  def UnaryCnxp(self, term):
    self.integer(term)
    self.eq_types(term, term.x)

  def AbsCnxp(self, term):
    self.integer(term)
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

  def LShrFunCnxp(self, term):
    self.integer(term)
    self.eq_types(term, *term._args)

  def Log2Cnxp(self, term):
    self.integer(term)
    self.integer(term)

  def SMaxCnxp(self, term):
    self.integer(term)
    self.eq_types(term, *term._args)

  def UMaxCnxp(self, term):
    self.integer(term)
    self.eq_types(term, *term._args)
  
  def SExtCnxp(self, term):
    self.width_ceiling(term._args[0], term)

  def ZExtCnxp(self, term):
    self.width_ceiling(term._args[0], term)

  def TruncCnxp(self, term):
    self.width_ceiling(term, term._args[0])

  def WidthCnxp(self, term):
    self.integer(term)
    self.integer(term._args[0])
    # NOTE: return type of width may be too small to hold value

  def AndPred(self, term):
    for p in term.clauses:
      p.accept(self)

  def OrPred(self, term):
    for p in term.clauses:
      p.accept(self)

  def NotPred(self, term):
    term.p.accept(self)

  def Comparison(self, term):
    self.integer(term.x)
    self.eq_types(term.x, term.y)

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