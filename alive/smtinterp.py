'''
Translate expressions into SMT via Z3
'''

from .language import *
from .z3util import *
from .util.dispatch import doubledispatch
from . import typing
from . import error
from functools import partial
import z3, operator, logging
import types
import collections
from contextlib import contextmanager
import warnings

# Z3 changed the API slightly after 4.4.1. This patches the old API
# to look like the new one.
# TODO: remove once we can drop support for 4.4.1
if hasattr(z3, 'fpIsInfinite'):
  _fpFP = z3.fpFP
  z3.fpFP = lambda sgn,exp,sig: _fpFP(sgn, sig, exp)
  z3.fpIsInf = z3.fpIsInfinite

logger = logging.getLogger(__name__)

# FIXME: assumes 64-bit pointers
# TODO: move into BaseSMTEncoder
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

class MetaEncoder(type):
  def __init__(cls, name, bases, dict):
    if not hasattr(cls, 'registry'):
      cls.registry = {}

    if not (name.startswith('Base') or name.endswith('Mixin')):
      reg_name = name
      if cls.__module__ != __name__ and cls.__module__ != '__main__':
        reg_name = cls.__module__ + '.' + name

      reg_name = reg_name.lower()

      if reg_name in cls.registry:
        raise ValueError('Duplicate encoder key: {0}\n{1}\n{2}'.format(
          reg_name, cls, cls.registry[reg_name]))

      cls.registry[reg_name] = cls

    return super(MetaEncoder, cls).__init__(name, bases, dict)

class BaseSMTEncoder():
  __metaclass__ = MetaEncoder

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

  def _conjunction(self, clauses):
    context = []

    for c in clauses:
      with self.local_safe() as s:
        p = self.eval(c)

      self.add_safe(*mk_implies(context, s))
      context.append(p)

    return context

  def conjunction(self, clauses):
    """Interpret a list of predicates in a fresh context.

    The Interp.value returned will be a list of SMT expressions.
    """
    self.reset()
    ps = self._conjunction(clauses)
    return Interp(
      value = ps,
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

  @contextmanager
  def local_defined(self):
    """Create a context with well-defined conditions independent from any prior
    conditions.

    Returns the list of well-defined conditions associated with the operations
    in the context.

    Usage:
      with smt.local_defined() as s:
        <operations>
    """
    old = self.defs
    try:
      new = []
      self.defs = new
      yield new
    finally:
      self.defs = old

  def add_nonpoison(self, *nonpoisons):
    """Add non-poison conditions to current translator context.
    """
    self.nops += nonpoisons

  add_nops = add_nonpoison # TODO: deprecate

  @contextmanager
  def local_nonpoison(self):
    """Create a context with nonpoison conditions independent from any prior
    conditions.

    Returns the list of nonpoison conditions associated with the operations in
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
    raise NotImplementedError('{} does not support floating-point'.format(
      type(self).__name__.lower()))

  def _conditional_conv_value(self, conds, v, name=''):
    raise NotImplementedError(
      '{} does not support floating-point conversion'.format(
      type(self).__name__.lower()))

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
    with self.local_nonpoison(), self.local_defined():
      args = [self.eval(a) for a in term._args]

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


def lookup(encoder):
  """Return an SMT encoder with this name (case-insensitive).

  If passed a subclass of BaseSMTEncoder, return it unchanged.
  """
  logger.debug('Looking up encoder %s', encoder)

  if isinstance(encoder, str):
    try:
      return BaseSMTEncoder.registry[encoder.lower()]
    except KeyError:
      raise error.Error('Unknown SMT encoder: ' + encoder)

  if isinstance(encoder, type) and issubclass(encoder, BaseSMTEncoder):
    return encoder

  raise ValueError('Argument to lookup must be string or class')

def encoders():
  """Return an iterator of name,class pairs for all known encoders.
  """
  return BaseSMTEncoder.registry.iteritems()

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

@eval.register(Node, BaseSMTEncoder)
def _(term, smt):
  raise NotImplementedError("Can't eval {} for {}".format(
    type(term).__name__, type(smt).__name__))

@eval.register(Input, BaseSMTEncoder)
def _(term, smt):
  ty = smt.type(term)
  smt.add_nonpoison(z3.Bool('np_' + term.name))
  return z3.Const(term.name, _ty_sort(ty))

@eval.register(Symbol, BaseSMTEncoder)
def _(term, smt):
  ty = smt.type(term)
  return z3.Const(term.name, _ty_sort(ty))

# TODO: since none of the clients use defined (aside from PLDI2015), maybe
# better to move it out
def binop(op, defined=None, poisons=None):
  return lambda term, smt: smt._binary_operator(term, op, defined, poisons)

eval.register(AddInst, BaseSMTEncoder,
  binop(operator.add,
    poisons = {
      'nsw': lambda x,y: z3.SignExt(1,x)+z3.SignExt(1,y) == z3.SignExt(1,x+y),
      'nuw': lambda x,y: z3.ZeroExt(1,x)+z3.ZeroExt(1,y) == z3.ZeroExt(1,x+y)
    }))

eval.register(SubInst, BaseSMTEncoder,
  binop(operator.sub,
    poisons = {
      'nsw': lambda x,y: z3.SignExt(1,x)-z3.SignExt(1,y) == z3.SignExt(1,x-y),
      'nuw': lambda x,y: z3.ZeroExt(1,x)-z3.ZeroExt(1,y) == z3.ZeroExt(1,x-y)
    }))

eval.register(MulInst, BaseSMTEncoder,
  binop(operator.mul,
    poisons = {
      'nsw': lambda x,y: z3.SignExt(x.size(),x)*z3.SignExt(x.size(),y)
                  == z3.SignExt(x.size(),x*y),
      'nuw': lambda x,y: z3.ZeroExt(x.size(),x)*z3.ZeroExt(x.size(),y)
                  == z3.ZeroExt(x.size(),x*y)
    }))

@eval.register(SDivInst, BaseSMTEncoder)
def _(term, smt):
  with smt.local_nonpoison() as nx:
    x = smt.eval(term.x)

  with smt.local_nonpoison() as ny:
    y = smt.eval(term.y)

  smt.add_nonpoison(*nx)

  smt.add_defs(y != 0, *ny)
  smt.add_defs(z3.Or(mk_and(nx + [x != 1 << (x.size()-1)]), y != -1))

  if 'exact' in term.flags:
    smt.add_nonpoison((x/y)*y == x)

  return x/y

@eval.register(UDivInst, BaseSMTEncoder)
def _(term, smt):
  x = smt.eval(term.x)

  with smt.local_nonpoison() as ny:
    y = smt.eval(term.y)

  smt.add_defs(y != 0, *ny)

  if 'exact' in term.flags:
    smt.add_nonpoison(z3.UDiv(x,y)*y == x)

  return z3.UDiv(x,y)

@eval.register(SRemInst, BaseSMTEncoder)
def _(term, smt):
  with smt.local_nonpoison() as nx:
    x = smt.eval(term.x)

  with smt.local_nonpoison() as ny:
    y = smt.eval(term.y)

  smt.add_nonpoison(*nx)

  smt.add_defs(y != 0, *ny)
  smt.add_defs(z3.Or(mk_and(nx + [x != 1 << (x.size()-1)]), y != -1))

  return z3.SRem(x,y)

@eval.register(URemInst, BaseSMTEncoder)
def _(term, smt):
  x = smt.eval(term.x)

  with smt.local_nonpoison() as ny:
    y = smt.eval(term.y)

  smt.add_defs(y != 0, *ny)

  return z3.URem(x,y)

def shift_op(op, poisons):
  def _(term, smt):
    x = smt.eval(term.x)
    y = smt.eval(term.y)
    z = smt._conditional_value([z3.ULT(y, y.size())], op(x,y), term.name)

    for f in poisons:
      if f in smt.attrs[term]:
        smt.add_nonpoison(z3.Implies(self.attrs[term][f], poisons[f](x,y,z)))
      elif f in term.flags:
        smt.add_nonpoison(poisons[f](x,y,z))

    cond = [z3.ULT(y, y.size())]
    return z

  return _

eval.register(ShlInst, BaseSMTEncoder,
  shift_op(operator.lshift,
    poisons = {
      'nsw': lambda x,y,z: z >> y == x,
      'nuw': lambda x,y,z: z3.LShR(z, y) == x}))


eval.register(AShrInst, BaseSMTEncoder,
  shift_op(operator.rshift,
    poisons = {'exact': lambda x,y,z: z << y == x}))


eval.register(LShrInst, BaseSMTEncoder,
  shift_op(z3.LShR,
    poisons = {'exact': lambda x,y,z: z << y == x}))


eval.register(AndInst, BaseSMTEncoder, binop(operator.and_))
eval.register(OrInst, BaseSMTEncoder, binop(operator.or_))
eval.register(XorInst, BaseSMTEncoder, binop(operator.xor))


def fbinop(op):
  return lambda term,smt: smt._float_binary_operator(term, op)

eval.register(FAddInst, BaseSMTEncoder, fbinop(operator.add))
eval.register(FSubInst, BaseSMTEncoder, fbinop(operator.sub))
eval.register(FMulInst, BaseSMTEncoder, fbinop(operator.mul))
eval.register(FDivInst, BaseSMTEncoder, fbinop(
  lambda x,y: z3.fpDiv(z3.get_default_rounding_mode(), x, y)))
eval.register(FRemInst, BaseSMTEncoder, fbinop(fpMod))


@doubledispatch
def _eval_bitcast(src, tgt, v):
  """
  Return SMT expression converting v from src to tgt.

  Assumes src and tgt have the same bit width.
  """
  raise NotImplementedError('Unexpected bitcast: {} -> {}'.format(src, tgt))

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

eval.register(BitcastInst, BaseSMTEncoder, _convert(_eval_bitcast))

eval.register(SExtInst, BaseSMTEncoder, _convert(
  lambda s,t,v: z3.SignExt(t.width - s.width, v)))

eval.register(ZExtInst, BaseSMTEncoder, _convert(
  lambda s,t,v: z3.ZeroExt(t.width - s.width, v)))

eval.register(TruncInst, BaseSMTEncoder, _convert(
  lambda s,t,v: z3.Extract(t.width-1, 0, v)))

eval.register(ZExtOrTruncInst, BaseSMTEncoder, _convert(
  lambda s,t,v: zext_or_trunc(v, s.width, t.width)))

# FIXME: don't assume 64-bit pointers
eval.register(PtrtointInst, BaseSMTEncoder, _convert(
  lambda s,t,v: zext_or_trunc(v, 64, t.width)))

eval.register(InttoptrInst, BaseSMTEncoder, _convert(
  lambda s,t,v: zext_or_trunc(v, s.width, 64)))

eval.register(FPExtInst, BaseSMTEncoder, _convert(
  lambda s,t,v: z3.fpToFP(z3.get_default_rounding_mode(), v, _ty_sort(t))))

@eval.register(FPTruncInst, BaseSMTEncoder)
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

@eval.register(FPtoSIInst, BaseSMTEncoder)
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

@eval.register(FPtoUIInst, BaseSMTEncoder)
def _fptoui(term, smt):
  v = smt.eval(term.arg)
  src = smt.type(term.arg)
  tgt = smt.type(term)

  # TODO: don't generate trivial conds
  return smt._conditional_conv_value(
    [0 <= v, v <= (2**tgt.width)-1],
    z3.fpToUBV(z3.RTZ(), v, _ty_sort(tgt)),
    term.name)

@eval.register(SItoFPInst, BaseSMTEncoder)
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

@eval.register(UItoFPInst, BaseSMTEncoder)
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

@eval.register(IcmpInst, BaseSMTEncoder)
def _icmp(term, smt):
  x = smt.eval(term.x)
  y = smt.eval(term.y)

  cmp = smt._icmp_ops[term.pred](x,y)

  return bool_to_BitVec(cmp)

@eval.register(FcmpInst, BaseSMTEncoder)
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

eval.register(SelectInst, BaseSMTEncoder,
  _handler(lambda c,x,y: z3.If(c == 1, x, y)))

@eval.register(FreezeInst, BaseSMTEncoder)
def _(term, smt):
  warnings.warn("Ignoring freeze")

  return smt.eval(term.x)

# Constants
# ---------

@eval.register(Literal, BaseSMTEncoder)
def _literal(term, smt):
  ty = smt.type(term)
  if isinstance(ty, FloatType):
    return z3.FPVal(term.val, _ty_sort(ty))

  return z3.BitVecVal(term.val, ty.width)

eval.register(FLiteralVal, BaseSMTEncoder,
  lambda term, smt: z3.FPVal(term.val, _ty_sort(smt.type(term))))

eval.register(FLiteralNaN, BaseSMTEncoder,
  lambda term, smt: z3.fpNaN(_ty_sort(smt.type(term))))

eval.register(FLiteralPlusInf, BaseSMTEncoder,
  lambda term, smt: z3.fpPlusInfinity(_ty_sort(smt.type(term))))

eval.register(FLiteralMinusInf, BaseSMTEncoder,
  lambda term, smt: z3.fpMinusInfinity(_ty_sort(smt.type(term))))

eval.register(FLiteralMinusZero, BaseSMTEncoder,
  lambda term, smt: z3.fpMinusZero(_ty_sort(smt.type(term))))

@eval.register(UndefValue, BaseSMTEncoder)
def _undef(term, smt):
  ty = smt.type(term)
  x = smt.fresh_var(ty)
  smt.add_qvar(x)
  return x

@eval.register(PoisonValue, BaseSMTEncoder)
def _poison(term, smt):
  smt.add_nops(z3.BoolVal(False))
  return smt.fresh_var(smt.type(term))


def _cbinop(op, safe):
  def handler(term, smt):
    x = smt.eval(term.x)
    y = smt.eval(term.y)

    smt.add_safe(safe(x,y))

    return op(x,y)

  return handler

# NOTE: better to use _handler here instead binop?
eval.register(AddCnxp, BaseSMTEncoder, binop(operator.add))
eval.register(SubCnxp, BaseSMTEncoder, binop(operator.sub))
eval.register(MulCnxp, BaseSMTEncoder, binop(operator.mul))
eval.register(UDivCnxp, BaseSMTEncoder, _cbinop(z3.UDiv, lambda x,y: y != 0))

# LLVM 3.8.0 APInt srem implemented via urem
# SMT-LIB does not appear to define srem
eval.register(SRemCnxp, BaseSMTEncoder,
  _cbinop(operator.mod, lambda x,y: y != 0))
eval.register(URemCnxp, BaseSMTEncoder,
  _cbinop(z3.URem, lambda x,y: y != 0))

# LLVM 3.8.0 APInt specifically checks for too-large shifts and
# returns 0. SMT-LIB also defines out-of-range shifts to be 0.
eval.register(ShlCnxp, BaseSMTEncoder, binop(operator.lshift))
eval.register(AShrCnxp, BaseSMTEncoder, binop(operator.rshift))
eval.register(LShrCnxp, BaseSMTEncoder, binop(z3.LShR))

eval.register(AndCnxp, BaseSMTEncoder, binop(operator.and_))
eval.register(OrCnxp, BaseSMTEncoder, binop(operator.or_))
eval.register(XorCnxp, BaseSMTEncoder, binop(operator.xor))

# special case because Z3 4.4.1 doesn't do FP div correctly
# LLVM 3.8.0 sdiv implemented via udiv
# SMT-LIB does not appear to define sdiv
@eval.register(SDivCnxp, BaseSMTEncoder)
def _sdiv(term, smt):
  if isinstance(smt.type(term), FloatType):
    return z3.fpDiv(z3.get_current_rounding_mode(),
      smt.eval(term.x), smt.eval(term.y))

  x = smt.eval(term.x)
  y = smt.eval(term.y)
  smt.add_safe(y != 0)

  return x / y

eval.register(NotCnxp, BaseSMTEncoder,
  lambda term, smt: ~smt.eval(term.x))

@eval.register(NegCnxp, BaseSMTEncoder)
def _neg(term, smt):
  if isinstance(smt.type(term), FloatType):
    return z3.fpNeg(smt.eval(term.x))

  return -smt.eval(term.x)

@eval.register(AbsCnxp, BaseSMTEncoder)
def _abs(term, smt):
  x = smt.eval(term._args[0])

  if isinstance(smt.type(term), FloatType):
    return z3.fpAbs(x)

  return z3.If(x >= 0, x, -x)

@eval.register(SignBitsCnxp, BaseSMTEncoder)
def _signbits(term, smt):
  with smt.local_defined(), smt.local_nonpoison():
    x = smt.eval(term._args[0])
  ty = smt.type(term)

  #b = ComputeNumSignBits(smt.fresh_bv(size), size)
  b = smt.fresh_var(ty, 'ana_')

  smt.add_aux(z3.ULE(b, ComputeNumSignBits(ty.width, x)))
  # FIXME: exact results for constants

  return b

@eval.register(OneBitsCnxp, BaseSMTEncoder)
def _ones(term, smt):
  with smt.local_defined(), smt.local_nonpoison():
    x = smt.eval(term._args[0])
  b = smt.fresh_var(smt.type(term), 'ana_')

  smt.add_aux(b & ~x == 0)

  return b

@eval.register(ZeroBitsCnxp, BaseSMTEncoder)
def _zeros(term, smt):
  with smt.local_defined(), smt.local_nonpoison():
    x = smt.eval(term._args[0])

  b = smt.fresh_var(smt.type(term), 'ana_')
  # FIXME: make sure each reference to this analysis is the same

  smt.add_aux(b & x == 0)

  return b

eval.register(LeadingZerosCnxp, BaseSMTEncoder,
  lambda term,smt: ctlz(smt.type(term).width,
    smt.eval(term._args[0])))

eval.register(TrailingZerosCnxp, BaseSMTEncoder,
  lambda term,smt: cttz(smt.type(term).width,
    smt.eval(term._args[0])))

eval.register(Log2Cnxp, BaseSMTEncoder,
  lambda term,smt: bv_log2(smt.type(term).width,
    smt.eval(term._args[0])))

eval.register(LShrFunCnxp, BaseSMTEncoder, _handler(z3.LShR))
eval.register(SMaxCnxp, BaseSMTEncoder,
  _handler(lambda x,y: z3.If(x > y, x, y)))
eval.register(SMinCnxp, BaseSMTEncoder,
  _handler(lambda x,y: z3.If(x > y, y, x)))
eval.register(UMaxCnxp, BaseSMTEncoder,
  _handler(lambda x,y: z3.If(z3.UGT(x, y), x, y)))
eval.register(UMinCnxp, BaseSMTEncoder,
  _handler(lambda x,y: z3.If(z3.UGT(x, y), y, x)))


@eval.register(SExtCnxp, BaseSMTEncoder)
def _(term, smt):
  v = smt.eval(term._args[0])
  src = smt.type(term._args[0])
  tgt = smt.type(term)

  return z3.SignExt(tgt.width - src.width, v)

@eval.register(ZExtCnxp, BaseSMTEncoder)
def _(term, smt):
  v = smt.eval(term._args[0])
  src = smt.type(term._args[0])
  tgt = smt.type(term)

  return z3.ZeroExt(tgt.width - src.width, v)

@eval.register(TruncCnxp, BaseSMTEncoder)
def _(term, smt):
  v = smt.eval(term._args[0])
  tgt = smt.type(term)

  return z3.Extract(tgt.width - 1, 0, v)

@eval.register(FPExtCnxp, BaseSMTEncoder)
@eval.register(FPTruncCnxp, BaseSMTEncoder)
def _(term, smt):
  v = smt.eval(term._args[0])
  return z3.fpToFP(z3.RNE(), v, _ty_sort(smt.type(term)))

@eval.register(FPMantissaWidthCnxp, BaseSMTEncoder)
def _mantissa(term, smt):
  ty = smt.type(term._args[0])
  return z3.BitVecVal(ty.frac, smt.type(term).width)

@eval.register(FPtoSICnxp, BaseSMTEncoder) #FIXME
def _fptosi(term, smt):
  x = smt.eval(term._args[0])
  tgt = smt.type(term)

  return z3.fpToSBV(z3.RTZ(), x, _ty_sort(tgt))

@eval.register(FPtoUICnxp, BaseSMTEncoder) #FIXME
def _fptoui(term, smt):
  x = smt.eval(term._args[0])
  tgt = smt.type(term)

  return z3.fpToUBV(z3.RTZ(), x, _ty_sort(tgt))

@eval.register(SItoFPCnxp, BaseSMTEncoder) #FIXME
def _sitofp(term, smt):
  x = smt.eval(term._args[0])
  tgt = smt.type(term)

  return z3.fpToFP(z3.RTZ(), x, _ty_sort(tgt))

@eval.register(UItoFPCnxp, BaseSMTEncoder) #FIXME
def _uitofp(term, smt):
  x = smt.eval(term._args[0])
  tgt = smt.type(term)

  return z3.fpToFPUnsigned(z3.RTZ(), x, _ty_sort(tgt))

@eval.register(WidthCnxp, BaseSMTEncoder)
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

@eval.register(AndPred, BaseSMTEncoder)
def _(term, smt):
  return mk_and(smt._conjunction(term.clauses))

@eval.register(OrPred, BaseSMTEncoder)
def _(term, smt):
  context = []

  for c in term.clauses:
    with smt.local_safe() as s:
      p = smt.eval(c)

    smt.add_safe(*mk_implies(map(z3.Not, context), s))
    context.append(p)

  return mk_or(context)

eval.register(NotPred, BaseSMTEncoder,
  lambda term, smt: z3.Not(smt.eval(term.p)))

@eval.register(Comparison, BaseSMTEncoder)
def _comparison(term, smt):
  if term.op == 'eq' and isinstance(smt.type(term.x), FloatType):
    cmp = z3.fpEQ
  else:
    cmp = smt._icmp_ops[term.op]
    # only the signed ones can be FP, so this is safe

  return cmp(smt.eval(term.x), smt.eval(term.y))

def _must(op):
  return lambda t,s: s._must_analysis(t, op)

eval.register(CannotBeNegativeZeroPred, BaseSMTEncoder,
  _must(lambda x: z3.Not(x == z3.fpMinusZero(x.sort()))))

eval.register(FPIdenticalPred, BaseSMTEncoder, _handler(operator.eq))

eval.register(FPIntegerPred, BaseSMTEncoder,
  _handler(lambda x: x == z3.fpRoundToIntegral(z3.RTZ(), x)))


def _has_attr(attr):
  return lambda t,s: s._has_attr(attr, t._args[0])

eval.register(HasNInfPred, BaseSMTEncoder, _has_attr('ninf'))
eval.register(HasNNaNPred, BaseSMTEncoder, _has_attr('nnan'))
eval.register(HasNSWPred, BaseSMTEncoder, _has_attr('nsw'))
eval.register(HasNSZPred, BaseSMTEncoder, _has_attr('nsz'))
eval.register(HasNUWPred, BaseSMTEncoder, _has_attr('nuw'))
eval.register(IsExactPred, BaseSMTEncoder, _has_attr('exact'))

@eval.register(IsConstantPred, BaseSMTEncoder)
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

eval.register(IntMinPred, BaseSMTEncoder,
  _handler(lambda x: x == 1 << (x.size()-1)))

eval.register(Power2Pred, BaseSMTEncoder,
  _must(lambda x: z3.And(x != 0, x & (x-1) == 0)))

eval.register(Power2OrZPred, BaseSMTEncoder,
  _must(lambda x: x & (x-1) == 0))

@eval.register(ShiftedMaskPred, BaseSMTEncoder)
def _(term, smt):
  x = smt.eval(term._args[0])
  v = (x-1) | x
  return z3.And(v != 0, ((v+1) & v) == 0)

eval.register(MaskZeroPred, BaseSMTEncoder,
  _must(lambda x,y: x & y == 0))

eval.register(NSWAddPred, BaseSMTEncoder,
  _must(lambda x,y: z3.SignExt(1,x) + z3.SignExt(1,y) == z3.SignExt(1,x+y)))

eval.register(NUWAddPred, BaseSMTEncoder,
  _must(lambda x,y: z3.ZeroExt(1,x) + z3.ZeroExt(1,y) == z3.ZeroExt(1,x+y)))

eval.register(NSWSubPred, BaseSMTEncoder,
  _must(lambda x,y: z3.SignExt(1,x) - z3.SignExt(1,y) == z3.SignExt(1,x-y)))

eval.register(NUWSubPred, BaseSMTEncoder,
  _must(lambda x,y: z3.ZeroExt(1,x) - z3.ZeroExt(1,y) == z3.ZeroExt(1,x-y)))

@eval.register(NSWMulPred, BaseSMTEncoder)
@_handler
def _(x,y):
  size = x.size()
  return z3.SignExt(size,x) * z3.SignExt(size,y) == z3.SignExt(size,x*y)

@eval.register(NUWMulPred, BaseSMTEncoder)
@_handler
def _(x,y):
  size = x.size()
  return z3.ZeroExt(size,x) * z3.ZeroExt(size,y) == z3.ZeroExt(size,x*y)

eval.register(NUWShlPred, BaseSMTEncoder,
  _handler(lambda x,y: z3.LShR(x << y, y) == x))

# NOTE: should this have semantics?
eval.register(OneUsePred, BaseSMTEncoder, lambda t,s: z3.BoolVal(True))


# SMT Encoders
# ===============

class SMTPoison(BaseSMTEncoder):
  def _conditional_value(self, conds, v, name=''):
    self.add_nops(*conds)
    return v

  _conditional_conv_value = _conditional_value

class SMTUndef(BaseSMTEncoder):
  def _conditional_value(self, conds, v, name=''):
    if not conds:
      return v

    self.fresh += 1
    name = 'undef_{}_{}'.format(name, self.fresh) if name else \
      'undef_' + str(self.fresh)

    u = z3.Const(name, v.sort())
    self.add_qvar(u)
    return z3.If(mk_and(conds), v, u)

  _conditional_conv_value = _conditional_value



class UBCPSelectMixin(BaseSMTEncoder):
  """Undefined behavior for poisoned choice, conditional poison
  """
  pass

@eval.register(SelectInst, UBCPSelectMixin)
def _(term, smt):
  with smt.local_nonpoison() as nc:
    c = smt.eval(term.sel)

  smt.add_defs(*nc)

  with smt.local_nonpoison() as nx:
    x = smt.eval(term.arg1)

  with smt.local_nonpoison() as ny:
    y = smt.eval(term.arg2)

  if nx or ny:
    smt.add_nonpoison(z3.If(c == 1, mk_and(nx), mk_and(ny)))

  return z3.If(c == 1, x, y)

class UBCPSelect(UBCPSelectMixin, SMTUndef):
  pass

class UBSelectMixin(BaseSMTEncoder):
  """Undefined behavior for poisoned choice, poion if either choice is poison
  """
  pass

@eval.register(SelectInst, UBSelectMixin)
def _(term, smt):
  with smt.local_nonpoison() as nc:
    c = smt.eval(term.sel)

  smt.add_defs(*nc)

  x = smt.eval(term.arg1)
  y = smt.eval(term.arg2)

  return z3.If(c == 1, x, y)

class UBSelect(UBSelectMixin, SMTUndef):
  pass

class NCCPSelectMixin(BaseSMTEncoder):
  """Nondeterministic choice, conditional poison
  """

@eval.register(SelectInst, NCCPSelectMixin)
def _(term, smt):
  with smt.local_nonpoison() as nc:
    c = smt.eval(term.sel)

  if nc:
    u = smt.fresh_var(smt.type(term.sel))
    smt.add_qvar(u)
    c = z3.If(mk_and(nc), c, u)

  with smt.local_nonpoison() as nx:
    x = smt.eval(term.arg1)

  with smt.local_nonpoison() as ny:
    y = smt.eval(term.arg2)

  if nx or ny:
    smt.add_nonpoison(z3.If(c == 1, mk_and(nx), mk_and(ny)))

  return z3.If(c == 1, x, y)

class NCCPSelect(NCCPSelectMixin, SMTUndef):
  pass

class CPSelectMixin(BaseSMTEncoder):
  """Conditional poison
  """

@eval.register(SelectInst, CPSelectMixin)
def _(term, smt):
  c = smt.eval(term.sel)

  with smt.local_nonpoison() as nx:
    x = smt.eval(term.arg1)

  with smt.local_nonpoison() as ny:
    y = smt.eval(term.arg2)

  if nx or ny:
    smt.add_nonpoison(z3.If(c == 1, mk_and(nx), mk_and(ny)))

  return z3.If(c == 1, x, y)

class CPSelect(CPSelectMixin, SMTUndef):
  pass



class PoisonOnly(CPSelectMixin, SMTPoison):
  pass

@eval.register(FreezeInst, PoisonOnly)
def _(term, smt):
  with smt.local_nonpoison() as n:
    x = smt.eval(term.x)

  # if term is never poison, return it's interp directly
  if not n:
    return x

  ty = smt.type(term)
  u  = z3.Const('frozen_' + term.name, _ty_sort(ty))
  # TODO: don't assume unique names

  return z3.If(mk_and(n), x, u)

@eval.register(UndefValue, PoisonOnly)
def _(term, smt):
  warnings.warn('Use of undef with poison-only semantics')
  return eval.dispatch(UndefValue, BaseBranchSelect)(term, smt)




# ----
# Historical encoders

class PLDI2015(BaseSMTEncoder):
  """Preserve the encoding of Alive as of the original Alive paper.
  """
  pass

@eval.register(Input, PLDI2015)
@eval.register(Symbol, PLDI2015)  # make sure these are the same
def _(term, smt):
  ty = smt.type(term)
  return z3.Const(term.name, _ty_sort(ty))


eval.register(SDivInst, PLDI2015,
  binop(operator.div,
    defined = lambda x,y: [y != 0, z3.Or(x != (1 << x.size()-1), y != -1)],
    poisons = {'exact': lambda x,y: (x/y)*y == x}))

eval.register(UDivInst, PLDI2015,
  binop(z3.UDiv,
    defined = lambda x,y: [y != 0],
    poisons = {'exact': lambda x,y: z3.UDiv(x,y)*y == x}))

eval.register(SRemInst, PLDI2015,
  binop(z3.SRem,
    defined = lambda x,y: [y != 0, z3.Or(x != (1 << x.size()-1), y != -1)]))

eval.register(URemInst, PLDI2015,
  binop(z3.URem,
    defined = lambda x,y: [y != 0]))

eval.register(ShlInst, PLDI2015,
  binop(operator.lshift,
    defined = lambda x,y: [z3.ULT(y, y.size())],
    poisons = {
      'nsw': lambda x,y: (x << y) >> y == x,
      'nuw': lambda x,y: z3.LShR(x << y, y) == x}))

eval.register(AShrInst, PLDI2015,
  binop(operator.rshift,
    defined = lambda x,y: [z3.ULT(y, y.size())],
    poisons = {'exact': lambda x,y: (x >> y) << y == x}))

eval.register(LShrInst, PLDI2015,
  binop(z3.LShR,
    defined = lambda x,y: [z3.ULT(y, y.size())],
    poisons = {'exact': lambda x,y: z3.LShR(x, y) << y == x}))



# -----
# Miscellaneous encoders


class NewShlMixin(BaseSMTEncoder):
  pass

eval.register(ShlInst, NewShlMixin,
  shift_op(operator.lshift,
    poisons = {
    'nsw': lambda a,b: z3.Or((a << b) >> b == a,
                             z3.And(a == 1, b == b.size() - 1)),
    'nuw': lambda a,b: z3.LShR(a << b, b) == a}))


class SMTPoisonNewShl(NewShlMixin, SMTPoison):
  pass

class SMTUndefNewShl(NewShlMixin, SMTUndef):
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


class OldNSZ(BaseSMTEncoder):
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

class BrokenNSZ(BaseSMTEncoder):
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
