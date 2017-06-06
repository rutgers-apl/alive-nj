from .. import language as L
from .. import typing
import itertools
import collections
import logging

logger = logging.getLogger(__name__)

Config = collections.namedtuple('Config', 'symbols type_reps environment')
# symbols:     maps tyvars to terms
# type_reps:   list of terms to use for width()
# environment: the TypeEnvironment

def set_type(config, term, tyvar):
  assert term not in config.environment.vars
  config.environment.vars[term] = tyvar
  return term

#binops = L.BinaryCnxp.codes.values()
binops = (L.AddCnxp, L.SubCnxp, L.AndCnxp, L.OrCnxp, L.XorCnxp, L.MulCnxp,
          L.ShlCnxp, L.SDivCnxp, L.UDivCnxp, L.SRemCnxp, L.URemCnxp, L.LShrCnxp,
          L.AShrCnxp)
unops = L.UnaryCnxp.codes.values()


def _flatten(tlist):
  list = []
  while tlist is not None:
    tlist,x = tlist
    list.append(x)

  return list

_neg_icmp_ops = {
  'eq':  'ne',
  'ne':  'eq',
  'slt': 'sge',
  'sle': 'sgt',
  'sgt': 'sle',
  'sge': 'slt',
  'ult': 'uge',
  'ule': 'ugt',
  'ugt': 'ule',
  'uge': 'ult',
}

def negate_pred(pred):
  if isinstance(pred, L.Comparison):
    return pred.copy(op=_neg_icmp_ops[pred.op])

  return L.NotPred(pred)

def preconditions(config):
  for size in itertools.count(2):
    logger.info('Generating size %s', size)
    for p in sized_preconditions(config, size):
      yield p

def sized_preconditions(config, size):
  def combine(l, r, neg):
    if neg: r = negate_pred(r)
    return (l, r)

  def predicates(size):
    return sized_predicates(config, size)

  def disjunctions(size):
    for t in assocs(size, combine, 2, neg_subexprs=predicates):
      yield L.OrPred(_flatten(t))

  for t in assocs(size,combine, 2, subexprs=disjunctions, neg_subexprs=predicates):
    yield L.AndPred(_flatten(t))

  for t in disjunctions(size):
    yield t

  for t in predicates(size):
    yield t
    yield negate_pred(t)


def predicates(config):
  for size in itertools.count(2):
    logger.info('Generating size %s', size)
    for p in sized_predicates(config, size):
      yield p

def sized_predicates(config, size):
  tys = config.symbols.keys()
  tys.append(config.environment.default_id)  # shouldn't already be there

  # comparisons
  for ty in tys:
    zero = set_type(config, L.Literal(0), ty)

    # E == 0, E < 0, E > 0
    for t,b in expressions(config, ty, size-1):
      if b: continue
      for cmp in ['eq', 'slt', 'sgt']:
        yield L.Comparison(cmp, t, zero)

    # E1 < E2, E1 u< E2
    for rsize in xrange(1, (size+1)/2):
      for l,bl in expressions(config, ty, size-rsize):
        for r,br in expressions(config, ty, rsize, one=True):
          if bl and br: continue
          yield L.Comparison('slt', l, r)
          yield L.Comparison('sgt', l, r)
          yield L.Comparison('ult', l, r)
          yield L.Comparison('ugt', l, r)

    if size % 2 == 0:
      for n,(l,bl) in enumerate(expressions(config, ty, size/2, one=True)):
        for r,br in itertools.islice(expressions(config,ty,size/2,one=True), n):
          if bl and br: continue
          yield L.Comparison('slt', l, r)
          yield L.Comparison('sgt', l, r)
          yield L.Comparison('ult', l, r)
          yield L.Comparison('ugt', l, r)


  # unary predicate functions
  for ty in tys:
    for t,b in expressions(config, ty, size-1):
      if b: continue
      yield L.IntMinPred(t)
      yield L.Power2Pred(t)
      yield L.Power2OrZPred(t)


def expressions(config, ty, size, **kws):
  return itertools.chain(
    [(set_type(config, L.Literal(1), ty), True)]
                               if size == 1 and kws.get('one',False) else [],
    atoms(config, ty, size)    if kws.get('atoms',True) else [],
    sums(config, ty, size)     if kws.get('sums',True) else [],
    products(config, ty, size) if kws.get('products',True) else [],
    logic(config, ty, size)    if kws.get('logic',True) else [],
    xors(config, ty, size)     if kws.get('xors',True) else [],
    nonassoc(config, ty, size) if kws.get('nonassoc',True) else [],
    funcs(config, ty, size)    if kws.get('funcs',True) else [],
  )

def neg_expressions(config, ty, size, **kws):
  for t,b in expressions(config, ty, size, **kws):
    yield set_type(config, L.NegCnxp(t), ty), b

def atoms(config, ty, size):
  if size != 1: return

  for s in config.symbols.get(ty,[]):
    yield (s, False)

  for r in config.type_reps:
    yield set_type(config, L.WidthCnxp(r), ty), \
      ty != config.environment.default_id

def sums(config, ty, size):
  def combine(x, (y,by), neg):
    if x is None:
      if neg:
        return set_type(config, L.NegCnxp(y), ty), by
      return (y,by)

    x,bx = x
    if neg:
      return set_type(config, L.SubCnxp(x,y), ty), bx and by
    return set_type(config, L.AddCnxp(x,y), ty), bx and by

  return assocs(size, combine,
    neg_subexprs=lambda s: expressions(config, ty, s, one=True, sums=False))

def products(config, ty, size):
  def combine(x, y, neg):
    assert not neg
    if x is None: return y

    x,bx = x
    y,by = y
    return set_type(config, L.MulCnxp(x,y), ty), bx and by

  return assocs(size, combine,
    subexprs=lambda s: expressions(config, ty, s, sums=False, products=False))

def logic(config, ty, size):
  def Or(x, (y,by), neg):
    if neg:
      y = set_type(config, L.NotCnxp(y), ty)
    if x is None:
      return y,by

    x,bx = x
    return set_type(config, L.OrCnxp(x,y), ty), bx and by

  def And(x, (y,by), neg):
    if neg:
      y = set_type(config, L.NotCnxp(y), ty)
    if x is None:
      return y,by

    x,bx = x
    return set_type(config, L.AndCnxp(x,y), ty), bx and by

  def subexprs(size):
    return expressions(config, ty, size, logic=False)

  def disjunctions(size):
    return assocs(size, Or, neg_subexprs=subexprs)

  return itertools.chain(
    assocs(size, And, subexprs=disjunctions, neg_subexprs=subexprs),
    disjunctions(size),
  )

def xors(config, ty, size):
  def Xor(x, (y,by), neg):
    assert not neg
    if x is None:
      return y,by

    x,bx = x
    return set_type(config, L.XorCnxp(x,y), ty), bx and by

  return assocs(size, Xor,
    subexprs=lambda s: itertools.chain(
      expressions(config, ty, s, xors=False, one=True),
      neg_expressions(config, ty, s, xors=False, sums=False, logic=False)))

_div_ops = [L.SDivCnxp, L.UDivCnxp, L.SRemCnxp, L.URemCnxp]
_shift_ops = [L.ShlCnxp, L.LShrCnxp, L.AShrCnxp]

def nonassoc(config, ty, size):
  def div_subexprs(size):
    return itertools.chain(
      expressions(config, ty, size),
      neg_expressions(config, ty, size, sums=False))

  # allow 1, -1 in left of shift
  def shift_lexpr(size):
    return itertools.chain(
      expressions(config, ty, size, one=True),
      neg_expressions(config, ty, size, sums=False, one=True))

  for lsize in xrange(1,size):
    rsize = size - lsize
    for r,br in div_subexprs(rsize):
      for l,bl in div_subexprs(lsize):
        for op in _div_ops:
          yield set_type(config, op(l,r),ty), br and bl

      for l,bl in shift_lexpr(lsize):
        for op in _shift_ops:
          yield set_type(config, op(l,r),ty), br and bl



def funcs(config, ty, size):
  if size < 2: return

  for t,b in expressions(config, ty, size-1):
    if b: continue
    yield set_type(config, L.AbsCnxp(t), ty), b

  var_ty = ty != config.environment.default_id

  for argty in config.symbols.iterkeys():
    for t,b in expressions(config, argty, size-1):
      if b: continue
      yield set_type(config, L.Log2Cnxp(t), ty), var_ty

  for argty in config.environment.lower_bounds.get(ty, ()):
    for t,b in expressions(config, argty, size-1):
      if b: continue
      yield set_type(config, L.ZExtCnxp(t), ty), var_ty
      yield set_type(config, L.SExtCnxp(t), ty), var_ty

  for argty in config.environment.upper_bounds.get(ty, ()):
    for t,b in expressions(config, argty, size-1):
      if b: continue
      yield set_type(config, L.TruncCnxp(t), ty), var_ty




def noexprs(size):
  return []

def assocs(size, combine, start=1, subexprs=noexprs, neg_subexprs=noexprs):
  """Generate unique expressions of a commutative, associative, idempotent
  operator.

  Creates 2 or more subexpressions whose sizes add up to the size, with the
  property that each subexpression is no larger than the previous one. E.g.,
  4 becomes 1+1+1+1, 2+1+1, 3+1, and 2+2.

  If two subexpressions have the same size, the left one always comes earlier
  in the sequence of subexpressions. E.g., we will produce A+B, but not B+A.

  combine(exp, subexp, negate):
    Should return exp+subexp, or exp+(-subexp) if negate

  Only subexpressions produced by neg_subexprs will be negated. These will
  produce A-B, but not A-A.
  """
  def push(size, threshold):
    if size < threshold: return
    if size == threshold:
      n = 0
      for c in neg_subexprs(size):
        yield n, combine(None, c, False)
        yield n, combine(None, c, True)
        n += 1
      for c in subexprs(size):
        yield n, combine(None, c, False)
        n += 1
      return

    lsize = size - threshold

    for pos,l in push(lsize, threshold):
      if pos == 0: continue
      n = 0
      for c in neg_subexprs(threshold):
        yield n, combine(l, c, False)
        yield n, combine(l, c, True)
        n += 1
        if n >= pos: break

      if n >= pos: continue
      for c in subexprs(threshold):
        yield n, combine(l, c, False)
        n += 1
        if n >= pos: break

    for l in increase(lsize, threshold):
      n = 0
      for c in neg_subexprs(threshold):
        yield n, combine(l, c, False)
        yield n, combine(l, c, True)
        n += 1
      for c in subexprs(threshold):
        yield n, combine(l, c, False)
        n += 1

  def increase(size, threshold, singles=True):
    if size <= threshold: return

    for rsize in xrange(threshold+1, size/2 + 1):
      lsize = size - rsize
      for pos,l in push(lsize, rsize):
        if pos == 0: continue
        n = 0
        for c in neg_subexprs(rsize):
          yield combine(l, c, False)
          yield combine(l, c, True)
          n += 1
          if n >= pos: break
        if n >= pos: continue
        for c in subexprs(rsize):
          yield combine(l, c, False)
          n += 1
          if n >= pos: break

      for l in increase(lsize, rsize):
        for c in neg_subexprs(rsize):
          yield combine(l, c, False)
          yield combine(l, c, True)
        for c in subexprs(rsize):
          yield combine(l, c, False)

    if singles:
      for c in neg_subexprs(size):
        yield combine(None, c, False)
        yield combine(None, c, True)
      for c in subexprs(size):
        yield combine(None, c, False)

  return increase(size, start-1, singles=False)
