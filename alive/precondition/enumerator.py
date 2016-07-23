from .. import language as L
from .. import typing
import itertools


def set_type(term, tyvar):
  assert term not in typing.context
  typing.context[term] = tyvar
  return term

binops = L.BinaryCnxp.codes.values()
unops = L.UnaryCnxp.codes.values()

def expressions(size, symbols, tyvar, type_model):
  """Generate pairs (expr, bool) containing expressions of a particular size
  using the given symbols.
  
  The bool is True if the expression contains a symbol.
  """

  if size < 1:
    return

  if size == 1:
    for s in symbols:
      if typing.context[s] == tyvar:
        yield s, True
    return

  if size == 2:
    yield set_type(L.Literal(0), tyvar), False
    yield set_type(L.Literal(1), tyvar), False
    yield set_type(L.Literal(-1), tyvar), False
    # TODO: width()

  size -= 1
  for lsize in xrange(1,size):
    for op in binops:
      for l,s1 in expressions(lsize, symbols, tyvar, type_model):
        for r,s2 in expressions(size-lsize, symbols, tyvar, type_model):
          yield set_type(op(l,r), tyvar), s1 or s2

  for op in unops:
    for e,s in expressions(size, symbols, tyvar, type_model):
      if not s: continue
      yield set_type(op(e), tyvar), s

  # TODO: functions

def positive_predicates(size, symbols, type_model):
  tyvars = { typing.context[s] for s in symbols }

  # enumerate comparisons
  for lsize in xrange(1, (size-1)/2+1):
    for tyvar in tyvars:
      for l,s1 in expressions(lsize, symbols, tyvar, type_model):
        for r,s2 in expressions(size-lsize-1, symbols, tyvar, type_model):
          if not (s1 or s2): continue

          # TODO: avoid ult if tyvar is floating
          for cmp in ['eq', 'slt', 'ult']: # sufficient?
            yield L.Comparison(cmp, l, r)

  # enumerate unary predicates
  for tyvar in tyvars:
    for e,s in expressions(size-2, symbols, tyvar, type_model):
      if not s: continue

      yield L.IntMinPred(e)
      yield L.Power2Pred(e)
      yield L.Power2OrZPred(e)

def predicates(size, symbols, type_model):
  return itertools.chain(
    positive_predicates(size, symbols, type_model),
    itertools.imap(L.NotPred, positive_predicates(size-1, symbols, type_model)))
