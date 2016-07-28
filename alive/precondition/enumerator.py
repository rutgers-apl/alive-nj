from .. import language as L
from .. import typing
import itertools
import collections

Config = collections.namedtuple('Config', 'symbols type_reps model')

def set_type(term, tyvar):
  assert term not in typing.context
  typing.context[term] = tyvar
  return term

binops = L.BinaryCnxp.codes.values()
unops = L.UnaryCnxp.codes.values()

def expressions(size, tyvar, config):
  """Generate pairs (expr, bool) containing expressions of a particular size
  using the given symbols.
  
  The bool is True if the expression contains a symbol.
  """

  if size < 1:
    return

  if size == 1:
    for s in config.symbols:
      if typing.context[s] == tyvar:
        yield s, True
    return

  if size == 2:
    yield set_type(L.Literal(0), tyvar), False
    yield set_type(L.Literal(1), tyvar), False
    yield set_type(L.Literal(-1), tyvar), False
    for r in config.type_reps:
      yield set_type(L.WidthCnxp(r), tyvar), tyvar == config.model.default_id

  size -= 1
  for lsize in xrange(1,size):
    for op in binops:
      for l,s1 in expressions(lsize, tyvar, config):
        for r,s2 in expressions(size-lsize, tyvar, config):
          yield set_type(op(l,r), tyvar), s1 or s2

  for op in unops:
    for e,s in expressions(size, tyvar, config):
      if not s: continue
      yield set_type(op(e), tyvar), s

  # TODO: functions

def positive_predicates(size, config):
  tyvars = { typing.context[s] for s in config.symbols }
  tyvars.add(config.model.default_id)

  # enumerate comparisons
  for lsize in xrange(1, (size-1)/2+1):
    for tyvar in tyvars:
      for l,s1 in expressions(lsize, tyvar, config):
        for r,s2 in expressions(size-lsize-1, tyvar, config):
          if not (s1 or s2): continue

          # TODO: avoid ult if tyvar is floating
          for cmp in ['eq', 'slt', 'ult']: # sufficient?
            yield L.Comparison(cmp, l, r)

  # enumerate unary predicates
  for tyvar in tyvars:
    for e,s in expressions(size-2, tyvar, config):
      if not s: continue

      yield L.IntMinPred(e)
      yield L.Power2Pred(e)
      yield L.Power2OrZPred(e)

def predicates(size, config):
  return itertools.chain(
    positive_predicates(size, config),
    itertools.imap(L.NotPred, positive_predicates(size-1, config)))
