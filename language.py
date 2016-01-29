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

# TODO: class PtrType; class ArrayType





# DAG Nodes
# ---------

class MetaNode(type):
  'Automatically generate a superclass table for Node classes'
  def __init__(cls, name, bases, dict):
    if not hasattr(cls, 'registry'):
      cls.registry = {}
    else:
      cls.registry[name] = bases[0].__name__

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

class Instruction(Value):
  pass

class BinaryOperator(Instruction):
  def __init__(self, x, y, ty = None, flags = ()):
    self.ty = ty
    self.x = x
    self.y = y
    self.flags = tuple(flags)
  
  def __repr__(self):
    return '{0.__name__}({1.x!r}, {1.y!r}, {1.ty!r}, {1.flags!r})'.format(type(self), self)

class AddInst(BinaryOperator):
  pass

class SubInst(BinaryOperator):
  pass

class MulInst(BinaryOperator):
  pass

class SDivInst(BinaryOperator):
  pass

class UDivInst(BinaryOperator):
  pass

class SRemInst(BinaryOperator):
  pass

class URemInst(BinaryOperator):
  pass

class ShlInst(BinaryOperator):
  pass

class AShrInst(BinaryOperator):
  pass

class LShrInst(BinaryOperator):
  pass

class AndInst(BinaryOperator):
  pass

class OrInst(BinaryOperator):
  pass

class XorInst(BinaryOperator):
  pass



class ConversionInst(Instruction):
  def __init__(self, arg, src_ty = None, dest_ty = None):
    self.src_ty = src_ty
    self.arg = arg
    self.ty = dest_ty

  def __repr__(self):
    return '{0.__name__}({1.arg!r}, {1.src_ty!r}, {1.ty!r})'.format(type(self), self)

class SExtInst(ConversionInst):
  pass

class ZExtInst(ConversionInst):
  pass

class TruncInst(ConversionInst):
  pass


class IcmpInst(Instruction):
  def __init__(self, pred, arg1, arg2, ty = None):
    self.pred = pred # FIXME -- something better
    self.ty   = ty
    self.x    = arg1
    self.y    = arg2

  def __repr__(self):
    return 'IcmpInst({0.pred!r}, {0.x!r}, {0.y!r}, {0.ty!r})'.format(self)

class SelectInst(Instruction):
  def __init__(self, sel, arg1, arg2, ty1 = None, ty2 = None):
    self.sel  = sel
    self.ty1  = ty1
    self.arg1 = arg1
    self.ty2  = ty2
    self.arg2 = arg2

  def __repr__(self):
    return 'SelectInst({0.sel!r}, {0.arg1!r}, {0.arg2!r}, {0.ty1!r}, {0.ty2!r})'.format(self)


# Constants
# ---------

class Constant(Value):
  pass

class Literal(Constant):
  def __init__(self, val):
    self.val = val
# TODO: need type for null?

class BinaryCnxp(Constant):
  def __init__(self, x, y):
    self.x = x
    self.y = y

class UnaryCnxp(Constant):
  def __init__(self, x):
    self.x = x



# Visitor
# -------

class UnmatchedCase(Exception):
  pass

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
    return

  def BinaryOperator(self, term):
    self.specific(term, term.ty)
    self.eq_types(term, term.x, term.y)
    self.integer(term)

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

  def IcmpInst(self, term):
    self.bool(term)
    self.first_class(term.x)
    self.specific(term.x, term.ty)
    self.eq_types(term.x, term.y)

  def SelectInst(self, term):
    self.bool(term.sel)
    self.specific(term.arg1, term.ty1)
    self.specific(term.arg2, term.ty2)
    self.eq_types(term, term.arg1, term.arg2)

  def Literal(self, term):
    self.integer(term)
    self.width_ceiling(term.val.bit_length()-1, term)
      # FIXME: bit_length() is nonsensical for negative numbers

  def BinaryCnxp(self, term):
    self.eq_types(term.x, term.y)
  
  def UnaryCnxp(self, term):
    self.eq_types(term.x)
