from .. import language as L
from .. import smtinterp
from ..z3util import mk_and, mk_or
import z3
import operator
import logging
import collections

logger = logging.getLogger(__name__)

def mk_implies(premises, consequents):
  if not consequents:
    return []

  if premises:
    return [z3.Implies(mk_and(premises), mk_and(consequents))]

  return consequents


SMT = collections.namedtuple('SMT', 'value defined nonpoison safe qvars')


class Translator(smtinterp.BaseSMTTranslator):
  def __init__(self, type_model, **kws):
    super(Translator, self).__init__(type_model, **kws)
    self._safe = []

  def __call__(self, term):
    self._safe = []
    v,d,p,q = super(Translator, self).__call__(term)
    s = self._safe

    return SMT(value=v, defined=d, nonpoison=p, safe=s, qvars=q)

  def add_safe(self, conds):
    self._safe.extend(conds)

  def reset_safe(self, safe=None):
    if safe is None: safe = []

    self._safe, safe = safe, self._safe

    return safe

  def eval_with_safe(self, term):
    safe, self._safe = self._safe, []
    logger.debug('Context saved: %s', safe)

    v = smtinterp.eval(term, self)

    safe, self._safe = self._safe, safe
    logger.debug('Returning safe condition: %s', safe)

    return v, safe

def binop(op, safe):
  def _(term, smt):
    x = smt.eval(term.x)
    y = smt.eval(term.y)

    smt.add_safe(safe(x,y))

    return op(x,y)

  return _

smtinterp.eval.register(L.SDivCnxp, Translator,
  binop(operator.div,
    lambda x,y: [y != 0, z3.Or(x != (1 << x.size()-1), y != -1)]))

smtinterp.eval.register(L.UDivCnxp, Translator,
  binop(z3.UDiv, lambda x,y: [y != 0]))

smtinterp.eval.register(L.SRemCnxp, Translator,
  binop(operator.mod,
    lambda x,y: [y != 0, z3.Or(x != (1 << x.size()-1), y != -1)]))

smtinterp.eval.register(L.URemCnxp, Translator,
  binop(z3.URem, lambda x,y: [y != 0]))

smtinterp.eval.register(L.ShlCnxp, Translator,
  binop(operator.lshift, lambda x,y: [z3.ULT(y, y.size())]))

smtinterp.eval.register(L.AShrCnxp, Translator,
  binop(operator.rshift, lambda x,y: [z3.ULT(y, y.size())]))

smtinterp.eval.register(L.LShrCnxp, Translator,
  binop(z3.LShR, lambda x,y: [z3.ULT(y, y.size())]))

@smtinterp.eval.register(L.LShrFunCnxp, Translator)
def _(term, smt):
  x = smt.eval(term._args[0])
  y = smt.eval(term._args[1])

  smt.add_safe([z3.ULT(y, y.size())])

  return z3.LShR(x,y)

@smtinterp.eval.register(L.AndPred, Translator)
def _(term, smt):
  context = []

  for c in term.clauses:
    p, safe = smt.eval_with_safe(c)
    smt.add_safe(mk_implies(context, safe))
    context.append(p)

  return mk_and(context)

@smtinterp.eval.register(L.OrPred, Translator)
def _(term, smt):
  context = []

  for c in term.clauses:
    p, safe = smt.eval_with_safe(c)
    smt.add_safe(mk_implies(map(z3.Not, context), safe))
    context.append(p)

  return mk_or(context)


def check_safety(opt, type_model=None):
  if type_model is None:
    type_model = opt.type_models().next()

  logger.info('Checking safety of opt %r', opt.name)

  smt = Translator(type_model)

  if opt.pre:
    pre = smt(opt.pre)
    pd = pre.defined + pre.nonpoison
    pd.append(pre.value)
    ps = pre.safe
  else:
    pd = []
    ps = []

  src = smt(opt.src)
  assert not src.safe

  tgt = smt(opt.tgt)

  e = mk_and(ps + mk_implies(pd, tgt.safe))
  logger.debug('expr:\n%s', e)

  s = z3.Solver()
  s.add(z3.Not(e))
  res = s.check()

  if res == z3.unsat:
    return None

  if res == z3.unknown:
    raise Exception('Sover returned unknown: ' + s.reason_unknown())

  model  = s.model()
  logger.info('Found counterexample: %s', model)

  s.add(src.defined)
  s.add(src.nonpoison)
  logger.debug('Second check:\n%s', s)

  res = s.check()
  if res == z3.sat:
    model = s.model()
    logger.info('Found "well-defined" counter-example: %s', model)

  return model



def main():
  import sys, logging.config
  from alive import parser, config

  logging.config.dictConfig(config.logs)
  #logger.setLevel(logging.DEBUG)

  if sys.stdin.isatty():
    sys.stderr.write('[Reading from terminal...]\n')

  opts = parser.parse_opt_file(sys.stdin.read())

  bads = 0
  for opt in opts:
    print 'Checking', repr(opt.name)

    m = check_safety(opt)

    if m is not None:
      print '* Found counter-example', m
      bads += 1

  print 'Unsafe opts:', bads

if __name__ == '__main__':
  main()
