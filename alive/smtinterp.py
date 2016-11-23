'''
Translate expressions into SMT via Z3
'''

from .language import *
from .z3util import *
from .util.dispatch import doubledispatch
from . import typing
from functools import partial
import z3, operator, logging
import types
import collections
from contextlib import contextmanager

# Z3 changed the API slightly after 4.4.1. This patches the old API
# to look like the new one.
# TODO: remove once we can drop support for 4.4.1
if hasattr(z3, 'fpIsInfinite'):
  _fpFP = z3.fpFP
  z3.fpFP = lambda sgn,exp,sig: _fpFP(sgn, sig, exp)
  z3.fpIsInf = z3.fpIsInfinite

logger = logging.getLogger(__name__)

# FIXME: assumes 64-bit pointers
# TODO: move into BaseSMTTranslator
def _ty_sort(ty):
  'Translate a Type expression to a Z3 Sort'

  if isinstance(ty, IntType):
    return z3.BitVecSort(ty.width)

  return {
    PtrType: z3.BitVecSort(64),
    HalfType: z3.FloatHalf(),
    SingleType: z3.Float32(),
    DoubleType: z3.Float64(),
    FP128Type: z3.Float128(),
    X86FP80Type: z3.FPSort(15, 64),
    }[type(ty)]
    # NOTE: this assumes the global z3 context never changes

Interp = collections.namedtuple('Interp',
  'value defined nonpoison safe aux qvars')

class MetaTranslator(type):
  def __init__(cls, name, bases, dict):
    if not hasattr(cls, 'registry'):
      cls.registry = {}

    cls.registry[name.lower()] = cls
    return super(MetaTranslator, cls).__init__(name, bases, dict)

class BaseSMTTranslator():
  __metaclass__ = MetaTranslator

  def __init__(self, type_model):
    self.types = type_model
    self.fresh = 0
    self.reset()
    self.attrs = collections.defaultdict(dict)
      # term -> attr -> var

  def reset(self):
    self.defs = []  # current defined-ness conditions
    self.nops = []  # current non-poison conditions
    self._safe = [] # current safety conditions
    self._aux  = [] # current auxiliary conditions
    self.qvars = []

  def eval(self, term):
    """Return the SMT translation of the term. Any side conditions are added
    to the translator context.
    """
    logger.debug('eval %s', term)
    return eval(term, self)

  def __call__(self, term):
    """Interpret the term in a fresh translator context.

    Quantified variables are guaranteed to be unique between different
    calls to the same SMTTranslator object.
    """
    # WARNING: calling eval after __call__ will modify the Interp
    # returned by __call__. Maybe better to clear everything after calling
    # eval? Perhaps best to clear both, but that wastes effort.
    logger.debug('call %s', term)
    self.reset()
    v = eval(term, self)
    return Interp(
      value = v,
      defined = self.defs,
      nonpoison = self.nops,
      safe = self._safe,
      aux = self._aux,
      qvars = self.qvars,
    )

  def add_defs(self, *defs):
    """Add well-defined conditions to the current translator context.
    """
    self.defs += defs

  def add_nonpoison(self, *nonpoisons):
    """Add non-poison conditions to current translator context.
    """
    self.nops += nonpoisons

  add_nops = add_nonpoison

  @contextmanager
  def local_nonpoison(self):
    """Create a context with nonpoison conditions independent from any prior
    conditions.

    Returns the list of safety conditions associated with the operations in
    the context.

    Usage:
      with smt.local_nonpoison() as s:
        <operations>
    """
    old = self.nops
    try:
      new = []
      self.nops = new
      yield new
    finally:
      self.nops = old

  def add_safe(self, *safe):
    """Add safety conditions to the current translator context.
    """
    self._safe += safe

  @contextmanager
  def local_safe(self):
    """Create a context with safety conditions independent from any prior
    conditions.

    Returns the list of safety conditions associated with the operations in
    the context.

    Usage:
      with smt.local_safe() as s:
        <operations>
    """
    old = self._safe
    try:
      new = []
      self._safe = new
      yield new
    finally:
      self._safe = old

  def add_aux(self, *auxs):
    """Add auxiliary conditions to the current translator context.
    """
    self._aux += auxs

  def add_qvar(self, *qvars):
    """Add quantified variables to the current translator context.
    """
    self.qvars += qvars

  def type(self, term):
    return self.types[typing.context[term]]

  def fresh_bool(self):
    self.fresh += 1
    return z3.Bool('ana_' + str(self.fresh))

  def fresh_var(self, ty, prefix='undef_'):
    self.fresh += 1
    return z3.Const(prefix + str(self.fresh), _ty_sort(ty))

  def _conditional_value(self, conds, v, name=''):
    raise NotImplementedError

  def _conditional_conv_value(self, conds, v, name=''):
    raise NotImplementedError

  def _binary_operator(self, term, op, defined, poisons):
    x = self.eval(term.x)
    y = self.eval(term.y)

    if defined:
      self.add_defs(*defined(x,y))

    if poisons:
      for f in poisons:
        if f in self.attrs[term]:
          self.add_nops(z3.Implies(self.attrs[term][f], poisons[f](x,y)))
        elif f in term.flags:
          self.add_nops(poisons[f](x,y))

    return op(x,y)

  def _float_binary_operator(self, term, op):
    logger.debug('_fbo: %s\n%s', term, self.attrs[term])
    x = self.eval(term.x)
    y = self.eval(term.y)
    z = op(x,y)

    conds = []
    if 'nnan' in self.attrs[term]:
      df = z3.And(z3.Not(z3.fpIsNaN(x)), z3.Not(z3.fpIsNaN(y)),
        z3.Not(z3.fpIsNaN(z)))
      conds.append(z3.Implies(self.attrs[term]['nnan'], df))

    elif 'nnan' in term.flags:
      conds += [z3.Not(z3.fpIsNaN(x)), z3.Not(z3.fpIsNaN(y)),
        z3.Not(z3.fpIsNaN(z))]

    if 'ninf' in self.attrs[term]:
      df = z3.And(z3.Not(z3.fpIsInf(x)), z3.Not(z3.fpIsInf(y)),
        z3.Not(z3.fpIsInf(z)))
      conds.append(z3.Implies(self.attrs[term]['ninf'], df))

    elif 'ninf' in term.flags:
      conds += [z3.Not(z3.fpIsInf(x)), z3.Not(z3.fpIsInf(y)),
        z3.Not(z3.fpIsInf(z))]

    if 'nsz' in self.attrs[term] or 'nsz' in term.flags:
      # NOTE: this will return a different qvar for each (in)direct reference
      # to this term. Is this desirable?
      b = self.fresh_bool()
      self.add_qvar(b)
      z = op(x,y)

      c = z3.fpIsZero(z)
      if 'nsz' in self.attrs[term]:
        c = z3.And(self.attrs[term]['nsz'], c)

      s = _ty_sort(self.type(term))
      z = z3.If(c, z3.If(b, 0, z3.fpMinusZero(s)), z)

      if isinstance(term, FDivInst):
        c = [z3.Not(z3.fpIsZero(x)), z3.fpIsZero(y)]
        if 'nsz' in self.attrs[term]:
          c.append(self.attrs[term]['nsz'])

        z = z3.If(z3.And(c),
          z3.If(b, z3.fpPlusInfinity(s), z3.fpMinusInfinity(s)),
          z)

    return self._conditional_value(conds, z, term.name)


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

  def _must_analysis(self, term, op):
    args = (self.eval(a) for a in term._args)

    if all(isinstance(a, Constant) for a in term._args):
      return op(*args)

    c = self.fresh_bool()
    self.add_aux(z3.Implies(c, op(*args)))
    return c

  def _has_attr(self, attr, term):
    if attr in term.flags:
      return z3.BoolVal(True)

    return self._get_attr_var(attr, term)

  def _get_attr_var(self, attr, term):
    if attr in self.attrs[term]:
      return self.attrs[term][attr]

    # TODO: pick name better
    b = self.fresh_bool()
    logger.debug('Creating attr var %s for %s:%s', b, term, attr)
    self.attrs[term][attr] = b
    return b


# generic function Eval
# =====================

@doubledispatch
def eval(term, smt):
  """
  Return an SMT translation of term, using smt for subterms.
  """

  raise NotImplementedError("cannot eval {} with {}".format(
    type(term).__name__, type(smt).__name__))

def _handler(op):
  return lambda term,smt: op(*(smt.eval(a) for a in term.args()))

@eval.register(Node, BaseSMTTranslator)
def _(term, smt):
  raise NotImplementedError("Can't eval {} for {}".format(
    type(term).__name__, type(smt).__name__))

@eval.register(Input, BaseSMTTranslator)
def _(term, smt):
  ty = smt.type(term)
  return z3.Const(term.name, _ty_sort(ty))

def binop(op, defined=None, poisons=None):
  return lambda term, smt: smt._binary_operator(term, op, defined, poisons)

eval.register(AddInst, BaseSMTTranslator,
  binop(operator.add,
    poisons = {
      'nsw': lambda x,y: z3.SignExt(1,x)+z3.SignExt(1,y) == z3.SignExt(1,x+y),
      'nuw': lambda x,y: z3.ZeroExt(1,x)+z3.ZeroExt(1,y) == z3.ZeroExt(1,x+y)
    }))

eval.register(SubInst, BaseSMTTranslator,
  binop(operator.sub,
    poisons = {
      'nsw': lambda x,y: z3.SignExt(1,x)-z3.SignExt(1,y) == z3.SignExt(1,x-y),
      'nuw': lambda x,y: z3.ZeroExt(1,x)-z3.ZeroExt(1,y) == z3.ZeroExt(1,x-y)
    }))

eval.register(MulInst, BaseSMTTranslator,
  binop(operator.mul,
    poisons = {
      'nsw': lambda x,y: z3.SignExt(x.size(),x)*z3.SignExt(x.size(),y)
                  == z3.SignExt(x.size(),x*y),
      'nuw': lambda x,y: z3.ZeroExt(x.size(),x)*z3.ZeroExt(x.size(),y)
                  == z3.ZeroExt(x.size(),x*y)
    }))

eval.register(SDivInst, BaseSMTTranslator,
  binop(operator.div,
    defined = lambda x,y: [y != 0, z3.Or(x != (1 << x.size()-1), y != -1)],
    poisons = {'exact': lambda x,y: (x/y)*y == x}))

eval.register(UDivInst, BaseSMTTranslator,
  binop(z3.UDiv,
    defined = lambda x,y: [y != 0],
    poisons = {'exact': lambda x,y: z3.UDiv(x,y)*y == x}))

eval.register(SRemInst, BaseSMTTranslator,
  binop(z3.SRem,
    defined = lambda x,y: [y != 0, z3.Or(x != (1 << x.size()-1), y != -1)]))

eval.register(URemInst, BaseSMTTranslator,
  binop(z3.URem,
    defined = lambda x,y: [y != 0]))

eval.register(ShlInst, BaseSMTTranslator,
  binop(operator.lshift,
    defined = lambda x,y: [z3.ULT(y, y.size())],
    poisons = {
      'nsw': lambda x,y: (x << y) >> y == x,
      'nuw': lambda x,y: z3.LShR(x << y, y) == x}))

eval.register(AShrInst, BaseSMTTranslator,
  binop(operator.rshift,
    defined = lambda x,y: [z3.ULT(y, y.size())],
    poisons = {'exact': lambda x,y: (x >> y) << y == x}))

eval.register(LShrInst, BaseSMTTranslator,
  binop(z3.LShR,
    defined = lambda x,y: [z3.ULT(y, y.size())],
    poisons = {'exact': lambda x,y: z3.LShR(x, y) << y == x}))

eval.register(AndInst, BaseSMTTranslator, binop(operator.and_))
eval.register(OrInst, BaseSMTTranslator, binop(operator.or_))
eval.register(XorInst, BaseSMTTranslator, binop(operator.xor))


def fbinop(op):
  return lambda term,smt: smt._float_binary_operator(term, op)

eval.register(FAddInst, BaseSMTTranslator, fbinop(operator.add))
eval.register(FSubInst, BaseSMTTranslator, fbinop(operator.sub))
eval.register(FMulInst, BaseSMTTranslator, fbinop(operator.mul))
eval.register(FDivInst, BaseSMTTranslator, fbinop(
  lambda x,y: z3.fpDiv(z3.get_default_rounding_mode(), x, y)))
eval.register(FRemInst, BaseSMTTranslator, fbinop(z3.fpRem))


@doubledispatch
def _eval_bitcast(src, tgt, v):
  """
  Return SMT expression converting v from src to tgt.

  Assumes src and tgt have the same bit width.
  """
  raise NotImplementedError

@_eval_bitcast.register(IntType, IntType)
@_eval_bitcast.register(IntType, PtrType)
@_eval_bitcast.register(PtrType, IntType)
@_eval_bitcast.register(PtrType, PtrType)
@_eval_bitcast.register(FloatType, FloatType)
def _(src, tgt, v):
  return v


@_eval_bitcast.register(IntType, FloatType)
@_eval_bitcast.register(PtrType, FloatType)
def _(src, tgt, v):
  return z3.fpToFP(v, _ty_sort(tgt))

@_eval_bitcast.register(FloatType, IntType)
@_eval_bitcast.register(FloatType, PtrType)
def _(src, tgt, v):
  return z3.fpToIEEEBV(v)

@_eval_bitcast.register(IntType, X86FP80Type)
@_eval_bitcast.register(PtrType, X86FP80Type)
def _(src, tgt, v):
  return z3.fpFP(z3.Extract(79,79,v),
    z3.Extract(78,64,v),
    z3.Extract(62,0,v))

@_eval_bitcast.register(X86FP80Type, IntType)
@_eval_bitcast.register(X86FP80Type, PtrType)
def _(src, tgt, v):
  w = z3.fpToIEEEBV(v)
  i = z3.If(z3.Or(z3.fpIsZero(v), z3.fpIsSubnormal(v)),
    z3.BitVecVal(0,1),
    z3.BitVecVal(1,1))

  return z3.Concat(z3.Extract(78,63,w), i, z3.Extract(62,0,w))


def _convert(op):
  return lambda term, smt: \
    op(smt.type(term.arg), smt.type(term), smt.eval(term.arg))

eval.register(BitcastInst, BaseSMTTranslator, _convert(_eval_bitcast))

eval.register(SExtInst, BaseSMTTranslator, _convert(
  lambda s,t,v: z3.SignExt(t.width - s.width, v)))

eval.register(ZExtInst, BaseSMTTranslator, _convert(
  lambda s,t,v: z3.ZeroExt(t.width - s.width, v)))

eval.register(TruncInst, BaseSMTTranslator, _convert(
  lambda s,t,v: z3.Extract(t.width-1, 0, v)))

eval.register(ZExtOrTruncInst, BaseSMTTranslator, _convert(
  lambda s,t,v: zext_or_trunc(v, s.width, t.width)))

# FIXME: don't assume 64-bit pointers
eval.register(PtrtointInst, BaseSMTTranslator, _convert(
  lambda s,t,v: zext_or_trunc(v, 64, t.width)))

eval.register(InttoptrInst, BaseSMTTranslator, _convert(
  lambda s,t,v: zext_or_trunc(v, s.width, 64)))

eval.register(FPExtInst, BaseSMTTranslator, _convert(
  lambda s,t,v: z3.fpToFP(z3.get_default_rounding_mode(), v, _ty_sort(t))))

@eval.register(FPTruncInst, BaseSMTTranslator)
def _fptrunc(term, smt):
  v = smt.eval(term.arg)
  tgt = smt.type(term)
  e = 2**(tgt.exp-1) # max exponent + 1
  m = 2**e

  rm = z3.get_default_rounding_mode()
  return smt._conditional_conv_value(
    [v > -m, v < m],
    z3.fpTpFP(rm, v, _ty_sort(tgt)),
    term.name)

@eval.register(FPtoSIInst, BaseSMTTranslator)
def _fptosi(term, smt):
  v = smt.eval(term.arg)
  src = smt.type(term.arg)
  tgt = smt.type(term)

  m = 2**(tgt.width-1)

  # TODO: don't generate trivial conds
  return smt._conditional_conv_value(
    [v >= -m, v <= m-1],
    z3.fpToSBV(z3.RTZ(), v, _ty_sort(tgt)),
    term.name)

@eval.register(FPtoUIInst, BaseSMTTranslator)
def _fptoui(term, smt):
  v = smt.eval(term.arg)
  src = smt.type(term.arg)
  tgt = smt.type(term)

  # TODO: don't generate trivial conds
  return smt._conditional_conv_value(
    [0 <= v, v <= (2**tgt.width)-1],
    z3.fpToUBV(z3.RTZ(), v, _ty_sort(tgt)),
    term.name)

@eval.register(SItoFPInst, BaseSMTTranslator)
def _sitofp(term, smt):
  v = smt.eval(term.arg)
  src = smt.type(term.arg)
  tgt = smt.type(term)

  w = 2**(tgt.exp-1) # 1 + maximum value of the exponent

  if src.width - 1 > w:
    m = 2**w
    conds = [-m < v, v < m]
  else:
    conds = []

  return smt._conditional_conv_value(conds,
    z3.fpToFP(z3.get_default_rounding_mode(), v, _ty_sort(tgt)),
    term.name)

@eval.register(UItoFPInst, BaseSMTTranslator)
def _uitofp(term, smt):
  v = smt.eval(term.arg)
  src = smt.type(term.arg)
  tgt = smt.type(term)

  w = 2**(tgt.exp-1)

  if src.width >= w:
    m = 2**w
    conds = [z3.ULE(v, m)]
  else:
    conds = []

  return smt._conditional_conv_value(conds,
    z3.fpToFPUnsigned(z3.get_default_rounding_mode(), v, _ty_sort(tgt)),
    term.name)

@eval.register(IcmpInst, BaseSMTTranslator)
def _icmp(term, smt):
  x = smt.eval(term.x)
  y = smt.eval(term.y)

  cmp = smt._icmp_ops[term.pred](x,y)

  return bool_to_BitVec(cmp)

@eval.register(FcmpInst, BaseSMTTranslator)
def _fcmp(term, smt):
  x = smt.eval(term.x)
  y = smt.eval(term.y)

  if term.pred == '':
    var = z3.BitVec('fcmp_' + term.name, 4)
    ops = smt._fcmp_ops.itervalues()
    # since _fcmp_ops should never change, this should be stable

    cmp = ops.next()(x,y)
    i = 1
    for op in ops:
      cmp = z3.If(var == i, op(x,y), cmp)
      i += 1

  else:
    cmp = smt._fcmp_ops[term.pred](x,y)

  conds = []
  if 'nnan' in term.flags:
    conds += [z3.Not(z3.fpIsNaN(x)), z3.Not(z3.fpIsNaN(y))]

  if 'ninf' in term.flags:
    conds += [z3.Not(z3.fpIsInf(x)), z3.Not(z3.fpIsInf(y))]

  return smt._conditional_value(
    conds,
    bool_to_BitVec(cmp),
    term.name)

eval.register(SelectInst, BaseSMTTranslator,
  _handler(lambda c,x,y: z3.If(c == 1, x, y)))


# Constants
# ---------

@eval.register(Literal, BaseSMTTranslator)
def _literal(term, smt):
  ty = smt.type(term)
  if isinstance(ty, FloatType):
    return z3.FPVal(term.val, _ty_sort(ty))

  return z3.BitVecVal(term.val, ty.width)

eval.register(FLiteralVal, BaseSMTTranslator,
  lambda term, smt: z3.FPVal(term.val, _ty_sort(smt.type(term))))

eval.register(FLiteralNaN, BaseSMTTranslator,
  lambda term, smt: z3.fpNaN(_ty_sort(smt.type(term))))

eval.register(FLiteralPlusInf, BaseSMTTranslator,
  lambda term, smt: z3.fpPlusInfinity(_ty_sort(smt.type(term))))

eval.register(FLiteralMinusInf, BaseSMTTranslator,
  lambda term, smt: z3.fpMinusInfinity(_ty_sort(smt.type(term))))

eval.register(FLiteralMinusZero, BaseSMTTranslator,
  lambda term, smt: z3.fpMinusZero(_ty_sort(smt.type(term))))

@eval.register(UndefValue, BaseSMTTranslator)
def _undef(term, smt):
  ty = smt.type(term)
  x = smt.fresh_var(ty)
  smt.add_qvar(x)
  return x

@eval.register(PoisonValue, BaseSMTTranslator)
def _poison(term, smt):
  smt.add_nops(z3.BoolVal(False))
  return smt.fresh_var(smt.type(term))

# NOTE: constant expressions do not introduce poison or definedness constraints
#       is this reasonable?
# FIXME: div/rem by 0 is undef
# NOTE: better to use _handler here instead binop?

def _cbinop(op, safe):
  def handler(term, smt):
    x = smt.eval(term.x)
    y = smt.eval(term.y)

    smt.add_safe(safe(x,y))

    return op(x,y)

  return handler

eval.register(AddCnxp, BaseSMTTranslator, binop(operator.add))
eval.register(SubCnxp, BaseSMTTranslator, binop(operator.sub))
eval.register(MulCnxp, BaseSMTTranslator, binop(operator.mul))
eval.register(UDivCnxp, BaseSMTTranslator, _cbinop(z3.UDiv, lambda x,y: y != 0))

# LLVM 3.8.0 APInt srem implemented via urem
# SMT-LIB does not appear to define srem
eval.register(SRemCnxp, BaseSMTTranslator,
  _cbinop(operator.mod, lambda x,y: y != 0))
eval.register(URemCnxp, BaseSMTTranslator,
  _cbinop(z3.URem, lambda x,y: y != 0))

# LLVM 3.8.0 APInt specifically checks for too-large shifts and
# returns 0. SMT-LIB also defines out-of-range shifts to be 0.
eval.register(ShlCnxp, BaseSMTTranslator, binop(operator.lshift))
eval.register(AShrCnxp, BaseSMTTranslator, binop(operator.rshift))
eval.register(LShrCnxp, BaseSMTTranslator, binop(z3.LShR))

eval.register(AndCnxp, BaseSMTTranslator, binop(operator.and_))
eval.register(OrCnxp, BaseSMTTranslator, binop(operator.or_))
eval.register(XorCnxp, BaseSMTTranslator, binop(operator.xor))

# special case because Z3 4.4.1 doesn't do FP div correctly
# LLVM 3.8.0 sdiv implemented via udiv
# SMT-LIB does not appear to define sdiv
@eval.register(SDivCnxp, BaseSMTTranslator)
def _sdiv(term, smt):
  if isinstance(smt.type(term), FloatType):
    return z3.fpDiv(z3.get_current_rounding_mode(),
      smt.eval(term.x), smt.eval(term.y))

  x = smt.eval(term.x)
  y = smt.eval(term.y)
  smt.add_safe(y != 0)

  return x / y

eval.register(NotCnxp, BaseSMTTranslator,
  lambda term, smt: ~smt.eval(term.x))

@eval.register(NegCnxp, BaseSMTTranslator)
def _neg(term, smt):
  if isinstance(smt.type(term), FloatType):
    return z3.fpNeg(smt.eval(term.x))

  return -smt.eval(term.x)

@eval.register(AbsCnxp, BaseSMTTranslator)
def _abs(term, smt):
  x = smt.eval(term._args[0])

  if isinstance(smt.type(term), FloatType):
    return z3.fpAbs(x)

  return z3.If(x >= 0, x, -x)

@eval.register(SignBitsCnxp, BaseSMTTranslator)
def _signbits(term, smt):
  x = smt.eval(term._args[0])
  ty = smt.type(term)

  #b = ComputeNumSignBits(smt.fresh_bv(size), size)
  b = smt.fresh_var(ty, 'ana_')

  smt.add_aux(z3.ULE(b, ComputeNumSignBits(ty.width, x)))

  return b

@eval.register(OneBitsCnxp, BaseSMTTranslator)
def _ones(term, smt):
  x = smt.eval(term._args[0])
  b = smt.fresh_var(smt.type(term), 'ana_')

  smt.add_aux(b & ~x == 0)

  return b

@eval.register(ZeroBitsCnxp, BaseSMTTranslator)
def _zeros(term, smt):
  x = smt.eval(term._args[0])
  b = smt.fresh_var(smt.type(term), 'ana_')
  # FIXME: make sure each reference to this analysis is the same

  smt.add_aux(b & x == 0)

  return b

eval.register(LeadingZerosCnxp, BaseSMTTranslator,
  lambda term,smt: ctlz(smt.type(term).width,
    smt.eval(term._args[0])))

eval.register(TrailingZerosCnxp, BaseSMTTranslator,
  lambda term,smt: cttz(smt.type(term).width,
    smt.eval(term._args[0])))

eval.register(Log2Cnxp, BaseSMTTranslator,
  lambda term,smt: bv_log2(smt.type(term).width,
    smt.eval(term._args[0])))

eval.register(LShrFunCnxp, BaseSMTTranslator, _handler(z3.LShR))
eval.register(SMaxCnxp, BaseSMTTranslator,
  _handler(lambda x,y: z3.If(x > y, x, y)))
eval.register(SMinCnxp, BaseSMTTranslator,
  _handler(lambda x,y: z3.If(x > y, y, x)))
eval.register(UMaxCnxp, BaseSMTTranslator,
  _handler(lambda x,y: z3.If(z3.UGT(x, y), x, y)))
eval.register(UMinCnxp, BaseSMTTranslator,
  _handler(lambda x,y: z3.If(z3.UGT(x, y), y, x)))


@eval.register(SExtCnxp, BaseSMTTranslator)
def _(term, smt):
  v = smt.eval(term._args[0])
  src = smt.type(term._args[0])
  tgt = smt.type(term)

  return z3.SignExt(tgt.width - src.width, v)

@eval.register(ZExtCnxp, BaseSMTTranslator)
def _(term, smt):
  v = smt.eval(term._args[0])
  src = smt.type(term._args[0])
  tgt = smt.type(term)

  return z3.ZeroExt(tgt.width - src.width, v)

@eval.register(TruncCnxp, BaseSMTTranslator)
def _(term, smt):
  v = smt.eval(term._args[0])
  tgt = smt.type(term)

  return z3.Extract(tgt.width - 1, 0, v)

@eval.register(FPExtCnxp, BaseSMTTranslator)
@eval.register(FPTruncCnxp, BaseSMTTranslator)
def _(term, smt):
  v = smt.eval(term._args[0])
  return z3.fpToFP(z3.RNE(), v, _ty_sort(smt.type(term)))

@eval.register(FPMantissaWidthCnxp, BaseSMTTranslator)
def _mantissa(term, smt):
  ty = smt.type(term._args[0])
  return z3.BitVecVal(ty.frac, smt.type(term).width)

@eval.register(FPtoSICnxp, BaseSMTTranslator) #FIXME
def _fptosi(term, smt):
  x = smt.eval(term._args[0])
  tgt = smt.type(term)

  return z3.fpToSBV(z3.RTZ(), x, _ty_sort(tgt))

@eval.register(FPtoUICnxp, BaseSMTTranslator) #FIXME
def _fptoui(term, smt):
  x = smt.eval(term._args[0])
  tgt = smt.type(term)

  return z3.fpToUBV(z3.RTZ(), x, _ty_sort(tgt))

@eval.register(SItoFPCnxp, BaseSMTTranslator) #FIXME
def _sitofp(term, smt):
  x = smt.eval(term._args[0])
  tgt = smt.type(term)

  return z3.fpToFP(z3.RTZ(), x, _ty_sort(tgt))

@eval.register(UItoFPCnxp, BaseSMTTranslator) #FIXME
def _uitofp(term, smt):
  x = smt.eval(term._args[0])
  tgt = smt.type(term)

  return z3.fpToFPUnsigned(z3.RTZ(), x, _ty_sort(tgt))

@eval.register(WidthCnxp, BaseSMTTranslator)
def _width(term, smt):
  return z3.BitVecVal(smt.type(term._args[0]).width, smt.type(term).width)
  # NOTE: nothing bad should happen if we don't evaluate the argument



# Predicates
# ----------

# FIXME: move mk_implies to z3util
def mk_implies(premises, consequents):
  if not consequents:
    return []

  if premises:
    return [z3.Implies(mk_and(premises), mk_and(consequents))]

  return consequents

@eval.register(AndPred, BaseSMTTranslator)
def _(term, smt):
  context = []

  for c in term.clauses:
    with smt.local_safe() as s:
      p = smt.eval(c)

    smt.add_safe(*mk_implies(context, s))
    context.append(p)

  return mk_and(context)

@eval.register(OrPred, BaseSMTTranslator)
def _(term, smt):
  context = []

  for c in term.clauses:
    with smt.local_safe() as s:
      p = smt.eval(c)

    smt.add_safe(*mk_implies(map(z3.Not, context), s))
    context.append(p)

  return mk_or(context)

eval.register(NotPred, BaseSMTTranslator,
  lambda term, smt: z3.Not(smt.eval(term.p)))

@eval.register(Comparison, BaseSMTTranslator)
def _comparison(term, smt):
  if term.op == 'eq' and isinstance(smt.type(term.x), FloatType):
    cmp = z3.fpEQ
  else:
    cmp = smt._icmp_ops[term.op]
    # only the signed ones can be FP, so this is safe

  return cmp(smt.eval(term.x), smt.eval(term.y))

def _must(op):
  return lambda t,s: s._must_analysis(t, op)

eval.register(CannotBeNegativeZeroPred, BaseSMTTranslator,
  _must(lambda x: z3.Not(x == z3.fpMinusZero(x.sort()))))

eval.register(FPIdenticalPred, BaseSMTTranslator, _handler(operator.eq))

eval.register(FPIntegerPred, BaseSMTTranslator,
  _handler(lambda x: x == z3.fpRoundToIntegral(z3.RTZ(), x)))


def _has_attr(attr):
  return lambda t,s: s._has_attr(attr, t._args[0])

eval.register(HasNInfPred, BaseSMTTranslator, _has_attr('ninf'))
eval.register(HasNNaNPred, BaseSMTTranslator, _has_attr('nnan'))
eval.register(HasNSWPred, BaseSMTTranslator, _has_attr('nsw'))
eval.register(HasNSZPred, BaseSMTTranslator, _has_attr('nsz'))
eval.register(HasNUWPred, BaseSMTTranslator, _has_attr('nuw'))
eval.register(IsExactPred, BaseSMTTranslator, _has_attr('exact'))

@eval.register(IsConstantPred, BaseSMTTranslator)
def _(term, smt):
  arg = term._args[0]
  if isinstance(arg, Constant):
    return z3.BoolVal(True)

  if isinstance(arg, Instruction):
    return z3.BoolVal(False)

  assert isinstance(arg, Input)

  # if this is in input, we can return true or false, but we
  # need to do so consistently
  return smt._get_attr_var('is_const', arg)

eval.register(IntMinPred, BaseSMTTranslator,
  _handler(lambda x: x == 1 << (x.size()-1)))

eval.register(Power2Pred, BaseSMTTranslator,
  _must(lambda x: z3.And(x != 0, x & (x-1) == 0)))

eval.register(Power2OrZPred, BaseSMTTranslator,
  _must(lambda x: x & (x-1) == 0))

@eval.register(ShiftedMaskPred, BaseSMTTranslator)
def _(term, smt):
  x = smt.eval(term._args[0])
  v = (x-1) | x
  return z3.And(v != 0, ((v+1) & v) == 0)

eval.register(MaskZeroPred, BaseSMTTranslator,
  _must(lambda x,y: x & y == 0))

eval.register(NSWAddPred, BaseSMTTranslator,
  _must(lambda x,y: z3.SignExt(1,x) + z3.SignExt(1,y) == z3.SignExt(1,x+y)))

eval.register(NUWAddPred, BaseSMTTranslator,
  _must(lambda x,y: z3.ZeroExt(1,x) + z3.ZeroExt(1,y) == z3.ZeroExt(1,x+y)))

eval.register(NSWSubPred, BaseSMTTranslator,
  _must(lambda x,y: z3.SignExt(1,x) - z3.SignExt(1,y) == z3.SignExt(1,x-y)))

eval.register(NUWSubPred, BaseSMTTranslator,
  _must(lambda x,y: z3.ZeroExt(1,x) - z3.ZeroExt(1,y) == z3.ZeroExt(1,x-y)))

@eval.register(NSWMulPred, BaseSMTTranslator)
@_handler
def _(x,y):
  size = x.size()
  return z3.SignExt(size,x) * z3.SignExt(size,y) == z3.SignExt(size,x*y)

@eval.register(NUWMulPred, BaseSMTTranslator)
@_handler
def _(x,y):
  size = x.size()
  return z3.ZeroExt(size,x) * z3.ZeroExt(size,y) == z3.ZeroExt(size,x*y)

eval.register(NUWShlPred, BaseSMTTranslator,
  _handler(lambda x,y: z3.LShR(x << y, y) == x))

# NOTE: should this have semantics?
eval.register(OneUsePred, BaseSMTTranslator, lambda t,s: z3.BoolVal(True))


# SMT Translators
# ===============

class SMTTranslator(BaseSMTTranslator):
  """Just for use elsewhere"""
  pass

class SMTPoison(BaseSMTTranslator):
  def _conditional_value(self, conds, v, name=''):
    self.add_nops(*conds)
    return v

  _conditional_conv_value = _conditional_value

class SMTUndef(BaseSMTTranslator):
  def _conditional_value(self, conds, v, name=''):
    if not conds:
      return v

    self.fresh += 1
    name = 'undef_{}_{}'.format(name, self.fresh) if name else \
      'undef_' + str(self.fresh)

    u = z3.Const(name, v.sort())
    self.add_qvar(u)
    return z3.If(z3.And(conds), v, u)

  _conditional_conv_value = _conditional_value


class NewShlSemantics(BaseSMTTranslator):
  pass

eval.register(ShlInst, NewShlSemantics,
  binop(operator.lshift,
    defined = lambda x,y: [z3.ULT(y, y.size())],
    poisons = {
    'nsw': lambda a,b: z3.Or((a << b) >> b == a,
                             z3.And(a == 1, b == b.size() - 1)),
    'nuw': lambda a,b: z3.LShR(a << b, b) == a}))


class SMTPoisonNewShl(NewShlSemantics, SMTPoison):
  pass

class SMTUndefNewShl(NewShlSemantics, SMTUndef):
  pass


class FPImpreciseUndef(SMTUndef):
  pass

@eval.register(SItoFPInst, FPImpreciseUndef)
def _(term, smt):
  v = smt.eval(term.arg)
  src = smt.type(term.arg)
  tgt = smt.type(term)

  w = 2**(tgt.exp)-1

  if src.width > w:
    m = (2**tgt.frac-1) << (w - tgt.frac)
    conds = [v >= -m, v <= m]
  else:
    conds = []

  b = smt.fresh_bool()
  smt.add_qvar(b)
  sort = _ty_sort(tgt)
  return smt._conditional_conv_value(
    conds,
    z3.If(b, z3.fpToFP(z3.RTN(), v, sort), z3.fpToFP(z3.RTP(),v,sort)),
    term.name)


class OldNSZ(BaseSMTTranslator):
  def _float_binary_operator(self, term, op):
    x = self.eval(term.x)
    y = self.eval(term.y)

    if 'nnan' in term.flags:
      self.add_defs(z3.Not(z3.fpIsNaN(x)), z3.Not(z3.fpIsNaN(y)),
        z3.Not(z3.fpIsNaN(op(x,y))))

    if 'ninf' in term.flags:
      self.add_defs(z3.Not(z3.fpIsInf(x)), z3.Not(z3.fpIsInf(y)),
        z3.Not(z3.fpIsInf(op(x,y))))

    if 'nsz' in term.flags:
      # NOTE: this will return a different qvar for each (in)direct reference
      # to this term. Is this desirable?
      nz = z3.fpMinusZero(_ty_sort(self.type(term)))
      self.add_defs(z3.Not(x == nz), z3.Not(y == nz))
      return op(x,y)  # turns -0 to +0

    return op(x,y)

class BrokenNSZ(BaseSMTTranslator):
  def _float_binary_operator(self, term, op):
    x = self.eval(term.x)
    y = self.eval(term.y)

    if 'nnan' in term.flags:
      self.add_defs(z3.Not(z3.fpIsNaN(x)), z3.Not(z3.fpIsNaN(y)),
        z3.Not(z3.fpIsNaN(op(x,y))))

    if 'ninf' in term.flags:
      self.add_defs(z3.Not(z3.fpIsInf(x)), z3.Not(z3.fpIsInf(y)),
        z3.Not(z3.fpIsInf(op(x,y))))

    if 'nsz' in term.flags:
      # NOTE: this will return a different qvar for each (in)direct reference
      # to this term. Is this desirable?
      q = self.fresh_var(self.type(term))
      self.add_qvar(q)  # FIXME
      self.add_defs(z3.fpEQ(q,0))
      z = op(x,y)
      return z3.If(z3.fpEQ(z,0), q, z)

    return op(x,y)
