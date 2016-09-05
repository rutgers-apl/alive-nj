from .. import language as L
from .. import typing
import itertools
import collections

Config = collections.namedtuple('Config', 'symbols type_reps model')
# symbols:   maps tyvars to terms
# type_reps: list of terms to use for width()
# model:     the AbstractTypeModel

def set_type(term, tyvar):
  assert term not in typing.context
  typing.context[term] = tyvar
  return term

#binops = L.BinaryCnxp.codes.values()
binops = (L.AddCnxp, L.SubCnxp, L.AndCnxp, L.OrCnxp, L.XorCnxp, L.MulCnxp,
          L.ShlCnxp, L.SDivCnxp, L.UDivCnxp, L.SRemCnxp, L.URemCnxp, L.LShrCnxp,
          L.AShrCnxp)
unops = L.UnaryCnxp.codes.values()


def expressions(size, tyvar, config):
  """Generate pairs (expr, bool) containing expressions of a particular size
  using the given symbols.

  The bool is True if the expression contains a symbol.
  """

  if size < 1:
    return

  if size == 1:
    for s in config.symbols.get(tyvar, []):
      yield s, True

    yield set_type(L.Literal(0), tyvar), False
    yield set_type(L.Literal(1), tyvar), False
    yield set_type(L.Literal(-1), tyvar), False
      # TODO: figure out a way to produce C == -1 but not C + -1

    for r in config.type_reps:
      yield set_type(L.WidthCnxp(r), tyvar), tyvar == config.model.default_id

    return

  size -= 1
  for lsize in xrange(1,size):
    for op in binops:
      for l,s1 in expressions(lsize, tyvar, config):
        for r,s2 in expressions(size-lsize, tyvar, config):
          yield set_type(op(l,r), tyvar), s1 or s2

  for op in unops:
    for e,s in expressions(size, tyvar, config):
      if not s: continue
      if isinstance(e, L.UnaryCnxp): continue
      yield set_type(op(e), tyvar), s

  # TODO: functions
  size -= 1
  for e,s in expressions(size, tyvar, config):
    if not s: continue
    yield set_type(L.AbsCnxp(e), tyvar), s

  for t2 in config.symbols.iterkeys():
    for e,s in expressions(size, t2, config):
      if not s: continue
      yield set_type(L.Log2Cnxp(e), tyvar), tyvar == config.model.default_id

def predicates(size, config):
  tyvars = config.symbols.keys()
  tyvars.append(config.model.default_id)

  # enumerate comparisons
  for lsize in xrange(1, (size-1)/2+1):
    for tyvar in tyvars:
      for l,s1 in expressions(lsize, tyvar, config):
        for r,s2 in expressions(size-lsize-1, tyvar, config):
          if not (s1 or s2): continue

          # TODO: avoid ult if tyvar is floating
          for cmp in ['eq', 'ult', 'ugt', 'slt', 'sgt']: # sufficient?
            yield L.Comparison(cmp, l, r)

  # enumerate unary predicates
  for tyvar in tyvars:
    for e,s in expressions(size-3, tyvar, config):
      if not s: continue

      yield L.IntMinPred(e)
      yield L.Power2Pred(e)
      yield L.Power2OrZPred(e)
