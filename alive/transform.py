'''
General object representing transformations (optimizations).
'''

from .language import *
from . import typing
from . import pretty
import logging
import collections

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

  def type_constraints(self):
    logger.debug('%s: Gathering type constraints', self.name)
    t = typing.TypeConstraints()

    # find type variables from the source
    t(self.src)
#     try:
#       t.type_models().next()
#       # FIXME: this triggers warnings for variables constrained to NUMBER
#       # which will later be constrained by the target
#     except StopIteration:
#       raise typing.Error('Unsatisfiable type constraints in source')

    src_reps = tuple(t.sets.reps())

    t.eq_types(self.src, self.tgt)
    if self.pre:
      self.pre.accept(t)

    reps = set(t.sets.reps())
    for r in src_reps:
      reps.discard(t.sets.rep(r))

    # TODO: warning for defaulted terms
    # FIXME: defaulted terms in the target are almost certainly bad
    for r in reps:
      if t.constraints.get(r) == typing.BOOL: continue

      logger.debug('%s: Defaulting term %r', self.name, r)
      t.specific(r, IntType(64))
      # move this into TypeConstraints?

    return t

  def type_models(self):
    return self.type_constraints().type_models()

  def constant_defs(self):
    """Generate shared constant terms from the target and precondition.

    Terms are generated before any terms that reference them.
    """

    uses = count_uses(self.tgt)
    if self.pre:
      count_uses(self.pre, uses)

    for t in subterms(self.tgt):
      if uses[t] > 1 and isinstance(t, Constant) and not isinstance(t, Symbol):
        yield t

  def format(self):
    s = ''
    if self.name:
      s += 'Name: ' + self.name + '\n'
      
    f = Formatter()
    srci = get_insts(self.src)
    
    src_lines = [i.accept(f) for i in srci]
    
    if logger.isEnabledFor(logging.DEBUG):
      logger.debug('Generated source\n%s\n  %s',
        '\n'.join(src_lines), pretty.pformat(f.ids, indent=2))

    tgt_lines = ['{} = {}'.format(f.name(v), v.accept(f))
                  for v in self.constant_defs()]

    if tgt_lines and logger.isEnabledFor(logging.DEBUG):
      logger.debug('Generated constant definitions\n%s\n  %s',
        '\n'.join(tgt_lines), pretty.pformat(f.ids, indent=2))

    if self.pre:
      s += 'Pre: ' + self.pre.accept(f) + '\n'

    s += '\n'.join(src_lines) + '\n=>\n'

    if isinstance(self.tgt, Instruction):
      f.ids[self.tgt] = self.src.name

    tgti = get_insts(self.tgt)
    tgt_lines.extend(i.accept(f) for i in tgti if i not in f.ids)

    if not isinstance(self.tgt, Instruction):
      tgt_lines.append(self.src.name + ' = ' + self.tgt.accept(f))
    else:
      tgt_lines.append(self.tgt.accept(f))

    s += '\n'.join(tgt_lines)

    return s

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

class Formatter(Visitor):
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

    if term in self.ids:
      return ty + self.name(term)

    assert not isinstance(term, Instruction)

    return ty + term.accept(self)

  def Node(self, term):
    return '<>'

  def Input(self, term):
    return self.name(term)

  def BinaryOperator(self, term):
    return self.name(term) + ' = ' + term.code + ' ' + \
      (' '.join(term.flags) + ' ' if term.flags else '') +\
      self.operand(term.x, term.ty) + ', ' + self.operand(term.y)

  def ConversionInst(self, term):
    return self.name(term) + ' = ' + term.code + ' ' + \
      self.operand(term.arg, term.src_ty) + \
      (' to ' + str(term.ty) if term.ty else '')

  def IcmpInst(self, term):
    return self.name(term) + ' = ' + 'icmp ' + term.pred + ' ' + \
      self.operand(term.x, term.ty) + ', ' + self.operand(term.y)

  def FcmpInst(self, term):
    return self.name(term) + ' = ' + 'fcmp ' + \
      (' '.join(term.flags) + ' ' if term.flags else '') + \
      term.pred + ' ' + self.operand(term.x, term.ty) + ', ' + \
      self.operand(term.y)

  def SelectInst(self, term):
    return self.name(term) + ' = ' + 'select ' + self.operand(term.sel) + \
      ', ' + self.operand(term.arg1, term.ty1) + \
      ', ' + self.operand(term.arg2, term.ty2)

  def Literal(self, term):
    return str(term.val)

  def FLiteral(self, term):
    return str(term.val)

  def UndefValue(self, term):
    return 'undef'

  def PoisonValue(self, term):
    return 'poison'

  def BinaryCnxp(self, term):
    return '(' + \
      ' '.join((self.operand(term.x), term.code, self.operand(term.y))) + \
      ')'

  def UnaryCnxp(self, term):
    return term.code + self.operand(term.x)

  def FunCnxp(self, term):
    return term.code + '(' + \
      ', '.join(self.operand(a) for a in term._args) + ')'


  def AndPred(self, term):
    if len(term.clauses) == 0:
      return 'true'

    return '(' + ' && '.join(cl.accept(self) for cl in term.clauses) + ')'

  def OrPred(self, term):
    if len(term.clauses) == 0:
      return '!true'

    return '(' + ' || '.join(cl.accept(self) for cl in term.clauses) + ')'

  def NotPred(self, term):
    return '!' + term.p.accept(self)

  def Comparison(self, term):
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
    
    return ' '.join((self.operand(term.x), code, self.operand(term.y)))

  def FunPred(self, term):
    return term.code + '(' + ', '.join(self.operand(a) for a in term._args) + ')'