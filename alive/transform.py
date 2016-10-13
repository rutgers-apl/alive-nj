'''
General object representing transformations (optimizations).
'''

from .language import *
from . import typing
from .util import pretty
from .util.dispatch import singledispatch
import logging
import collections
import itertools

logger = logging.getLogger(__name__)


class Transform(pretty.PrettyRepr):
  def __init__(self, src, tgt, pre=None, name=''):
    self.name = name
    self.pre = pre
    self.src = src
    self.tgt = tgt

  def pretty(self):
    return pretty.pfun(type(self).__name__,
      (self.src, self.tgt, self.pre, self.name))

  def subterms(self):
    """Generate all terms in the transform, without repeats.
    """
    seen = set()

    return itertools.chain(
      subterms(self.src, seen),
      subterms(self.tgt, seen),
      () if self.pre is None else subterms(self.pre, seen)
    )

  def type_constraints(self):
    logger.debug('%s: Gathering type constraints', self.name)

    t = typing.TypeConstraints()
    seen = set()

    # find type variables from the source
    for term in subterms(self.src, seen):
      term.type_constraints(t)

    # note the type variables fixed by the source
    src_reps = tuple(t.sets.reps())

    defaultable = []
    if self.pre:
      for term in subterms(self.pre, seen):
        term.type_constraints(t)

        # note the immediate arguments to Comparisons and predicates,
        # in case they need to be defaulted later
        if isinstance(term, (Comparison, FunPred)):
          defaultable.extend(term.args())

    for term in subterms(self.tgt, seen):
      term.type_constraints(t)

    t.eq_types(self.src, self.tgt)

    # find any type variables not unified with a variable from the source
    # (ie. which are newly introduced by the target or precondition)
    reps = set(r for r in t.sets.reps()
      if r not in t.specifics and t.constraints[r] != typing.BOOL)
    for r in src_reps:
      reps.discard(t.sets.rep(r))

    # if any of the new variables are defaultable, then default them
    if reps:
      for term in defaultable:
        r = t.sets.rep(term)
        if r in reps:
          t.default(r)
          reps.discard(r)

    # if any new type variables cannot be defaulted, then the transformation
    # is ambiguously typed
    if reps:
      fmt = Formatter()
      raise typing.Error('Ambiguous type for ' + ', '.join(
          fmt.operand(term) for term in reps))

    return t

  def abstract_type_model(self):
    if not hasattr(self, '_model'):
      self._model = self.type_constraints().get_type_model()

    return self._model

  def type_models(self):
    return self.abstract_type_model().type_vectors()

  def validate_model(self, type_vector):
    """Return whether the type vector meets this opt's constraints.
    """

    model = self.abstract_type_model()
    V = typing.Validator(model, type_vector)
    seen = set()

    try:
      V.eq_types(self.src, self.tgt)

      for t in self.subterms():
        logger.debug('checking %s', t)
        t.type_constraints(V)

      return True

    except typing.Error:
      return False

  def constant_defs(self):
    """Generate shared constant terms from the target and precondition.

    Terms are generated before any terms that reference them.
    """

    return constant_defs(self.tgt, [self.pre] if self.pre else [])

  def format(self):
    return format_parts(
      self.name,
      [('Pre:', self.pre)] if self.pre else [],
      self.src,
      self.tgt)

def get_insts(v):
  def walk(v, insts, seen):
    if v in seen or not isinstance(v, Instruction):
      return

    seen.add(v)

    for a in v.args():
      walk(a, insts, seen)

    insts.append(v)

  seen = set()
  insts = []
  walk(v, insts, seen)
  return insts

def count_uses(dag, uses=None):
  if uses is None:
    uses = collections.Counter()

  def walk(v):
    for a in v.args():
      if a not in uses:
        walk(a)
      uses[a] += 1

  walk(dag)
  return uses

def constant_defs(tgt, terms=[]):
  """Generate shared constant terms from the target and precondition.

  Terms are generated before any terms that reference them.
  """
  uses = count_uses(tgt)
  for t in terms:
    count_uses(t, uses)

  for t in subterms(tgt):
    if uses[t] > 1 and isinstance(t, Constant) and not isinstance(t, Symbol):
      yield t

def format_parts(name, headers, src, tgt):
  """Return a printable string for an optimization.

  Usage:
    print format_parts('spam', ('Pre:', eggs), bacon, spam)
  """
  lines = []
  if name:
    lines.append('Name: ' + name)

  fmt = Formatter()
  srci = get_insts(src)
  src_lines = [format(i, fmt) for i in srci]

  tgt_lines = ['{} = {}'.format(fmt.name(v), format(v, fmt))
                for v in constant_defs(tgt, map(lambda h: h[1], headers))]


  for h,t in headers:
    lines.append(h + ' ' + format(t, fmt))

  lines.extend(src_lines)
  lines.append('=>')
  lines.extend(tgt_lines)

  if isinstance(tgt, Instruction):
    fmt.ids[tgt] = src.name

  tgti = get_insts(tgt)
  lines.extend(format(i, fmt) for i in tgti if i not in fmt.ids)

  if not isinstance(tgt, Instruction):
    lines.append(src.name + ' = ' + format(tgt, fmt))
  else:
    lines.append(format(tgt, fmt))

  return '\n'.join(lines)

class Formatter(object):
  def __init__(self):
    self.ids = {}
    self.names = set()
    self.fresh = 0

  def name(self, term):
    if term in self.ids: return self.ids[term]

    prefix = 'C' if isinstance(term, Constant) else '%'

    if isinstance(term, (Input, Instruction)) and term.name:
      name = term.name
    else:
      name = prefix + str(self.fresh)
      self.fresh += 1

    while name in self.names:
      name = prefix + str(self.fresh)
      self.fresh += 1

    self.ids[term] = name
    self.names.add(name)
    return name

  def operand(self, term, ty = None):
    ty = str(ty) + ' ' if ty else ''

    if term in self.ids or isinstance(term, Instruction):
      return ty + self.name(term)

    return ty + format(term, self)

@singledispatch
def format(term, fmt):
  """
  format(term, fmt)
  Return Node formatted in Alive syntax.

  fmt must be a Formatter object, which handles operand references
  """

  raise NotImplementedError("Can't format " + type(term).__name__)

@format.register(Input)
def _(term, fmt):
 return fmt.name(term)

@format.register(BinaryOperator)
def _(term, fmt):
  return fmt.name(term) + ' = ' + term.code + ' ' + \
    (' '.join(term.flags) + ' ' if term.flags else '') +\
    fmt.operand(term.x, term.ty) + ', ' + fmt.operand(term.y)

@format.register(ConversionInst)
def _(term, fmt):
  return fmt.name(term) + ' = ' + term.code + ' ' + \
    fmt.operand(term.arg, term.src_ty) + \
    (' to ' + str(term.ty) if term.ty else '')

@format.register(IcmpInst)
def _(term, fmt):
  return fmt.name(term) + ' = ' + 'icmp ' + term.pred + ' ' + \
    fmt.operand(term.x, term.ty) + ', ' + fmt.operand(term.y)

@format.register(FcmpInst)
def _(term, fmt):
  return fmt.name(term) + ' = ' + 'fcmp ' + \
    (' '.join(term.flags) + ' ' if term.flags else '') + \
    term.pred + ' ' + fmt.operand(term.x, term.ty) + ', ' + \
    fmt.operand(term.y)

@format.register(SelectInst)
def _(term, fmt):
  return fmt.name(term) + ' = ' + 'select ' + fmt.operand(term.sel) + \
    ', ' + fmt.operand(term.arg1, term.ty1) + \
    ', ' + fmt.operand(term.arg2, term.ty2)

@format.register(Literal)
def _(term, fmt):
  return str(term.val)

@format.register(FLiteral)
def _(term, fmt):
  return str(term.val)

@format.register(UndefValue)
def _(term, fmt):
  return 'undef'

@format.register(PoisonValue)
def _(term, fmt):
  return 'poison'

@format.register(BinaryCnxp)
def _(term, fmt):
  return '(' + \
    ' '.join((fmt.operand(term.x), term.code, fmt.operand(term.y))) + \
    ')'

@format.register(UnaryCnxp)
def _(term, fmt):
  return term.code + fmt.operand(term.x)

@format.register(FunCnxp)
def _(term, fmt):
  return term.code + '(' + \
    ', '.join(fmt.operand(a) for a in term._args) + ')'


@format.register(AndPred)
def _(term, fmt):
  if len(term.clauses) == 0:
    return 'true'

  return '(' + ' && '.join(format(cl,fmt) for cl in term.clauses) + ')'

@format.register(OrPred)
def _(term, fmt):
  if len(term.clauses) == 0:
    return '!true'

  return '(' + ' || '.join(format(cl, fmt) for cl in term.clauses) + ')'

@format.register(NotPred)
def _(term, fmt):
  return '!' + format(term.p, fmt)

@format.register(Comparison)
def _(term, fmt):
  code = {
    'eq':  '==',
    'ne':  '!=',
    'slt': '<',
    'sle': '<=',
    'sgt': '>',
    'sge': '>=',
    'ult': 'u<',
    'ule': 'u<=',
    'ugt': 'u>',
    'uge': 'u>=',
    }[term.op]

  return ' '.join((fmt.operand(term.x), code, fmt.operand(term.y)))

@format.register(FunPred)
def _(term, fmt):
  return term.code + '(' + ', '.join(fmt.operand(a) for a in term._args) + ')'
