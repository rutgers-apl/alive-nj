from .. import language as L
from .. import typing
import itertools
import collections
import logging

logger = logging.getLogger(__name__)

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


def old_expressions(size, tyvar, config):
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
      for l,s1 in old_expressions(lsize, tyvar, config):
        for r,s2 in old_expressions(size-lsize, tyvar, config):
          yield set_type(op(l,r), tyvar), s1 or s2

  for op in unops:
    for e,s in old_expressions(size, tyvar, config):
      if not s: continue
      if isinstance(e, L.UnaryCnxp): continue
      yield set_type(op(e), tyvar), s

  # TODO: functions
  size -= 1
  for e,s in old_expressions(size, tyvar, config):
    if not s: continue
    yield set_type(L.AbsCnxp(e), tyvar), s

  for t2 in config.symbols.iterkeys():
    for e,s in old_expressions(size, t2, config):
      if not s: continue
      yield set_type(L.Log2Cnxp(e), tyvar), tyvar == config.model.default_id

def old_predicates(config):
  tyvars = config.symbols.keys()
  tyvars.append(config.model.default_id)

  # enumerate comparisons
  #for size in itertools.count(3):
  for size in xrange(3,8):
    logger.info('Generating size %s', size)

    for lsize in xrange(1, (size-1)/2+1):
      for tyvar in tyvars:
        for l,s1 in old_expressions(lsize, tyvar, config):
          for r,s2 in old_expressions(size-lsize-1, tyvar, config):
            if not (s1 or s2): continue

            # TODO: avoid ult if tyvar is floating
            for cmp in ['eq', 'ult', 'ugt', 'slt', 'sgt']: # sufficient?
              yield L.Comparison(cmp, l, r)

    # enumerate unary predicates
    for tyvar in tyvars:
      for e,s in old_expressions(size-3, tyvar, config):
        if not s: continue

        yield L.IntMinPred(e)
        yield L.Power2Pred(e)
        yield L.Power2OrZPred(e)


def old_sums(config, size, tyvar, allones=True):
  """Generate pairs e,b, where e is a constant expression, and
  b is true unless e contains a symbol or tyvar is default_id.
  """
  # TODO: consider literals other than one
  if size == 1:
    yield set_type(L.Literal(1), tyvar), True

    if allones:
      yield set_type(L.Literal(-1), tyvar), True

  # sums with no final literal
  for tb in _sums_2(config, size, tyvar, 0):
    yield tb

  # sums with a final literal
  l = set_type(L.Literal(1), tyvar)
  for t,b in _sums_2(config, size-2, tyvar, 0):
    yield set_type(L.AddCnxp(t,l), tyvar), b
    yield set_type(L.SubCnxp(t,l), tyvar), b

def _sums_2(config, size, tyvar, place):
  """Generate width() terms
  """
  if size < 1: return

  if place >= len(config.type_reps):
    for tb in _sums_3(config, size, tyvar, 0):
      yield tb
    return

  for tb in _sums_2(config, size, tyvar, place+1):
    yield tb

  wb = tyvar != config.model.default_id
  w = set_type(L.WidthCnxp(config.type_reps[place]), tyvar)

  if size == 1:
    yield w, wb
    return

  if size == 2:
    yield set_type(L.NegCnxp(w), tyvar), wb
    return

  for t,b in _sums_2(config, size-2, tyvar, place+1):
    yield set_type(L.AddCnxp(t,w), tyvar), b or wb
    yield set_type(L.SubCnxp(t,w), tyvar), b or wb

def _sums_3(config, size, tyvar, place):
  """Generate symbol terms
  """
  if size < 1: return

  vars = config.symbols.get(tyvar, [])
  if place >= len(vars):
    for tb in _sums_4(config, size, tyvar):
      yield tb
    return

  for tb in _sums_3(config, size, tyvar, place+1):
    yield tb

  if size == 1:
    yield vars[place], False
    return

  if size == 2:
    yield set_type(L.NegCnxp(vars[place]), tyvar), False
    return

  for t,_ in _sums_3(config, size-2, tyvar, place+1):
    yield set_type(L.AddCnxp(t, vars[place]), tyvar), False
    yield set_type(L.SubCnxp(t, vars[place]), tyvar), False

commutative_ops = [L.MulCnxp, L.AndCnxp, L.OrCnxp, L.XorCnxp]
noncommutative_ops = [L.SDivCnxp, L.UDivCnxp, L.SRemCnxp, L.URemCnxp,
  L.ShlCnxp, L.LShrCnxp, L.AShrCnxp]

def _sums_4(config, size, tyvar):
  """Generate all non-addition terms.
  """
  if size < 2:
    return

  for t,b in sums(config, size-1, tyvar):
    if isinstance(t, (L.Literal, L.UnaryCnxp)): continue
    yield set_type(L.NotCnxp(t), tyvar), b

  # for commutative operators, bias size to the left
  # TODO: some way to exclude multiplying by 1
  for lsize in xrange(1, (size-1)/2+1):
    for l,lb in sums(config, lsize, tyvar, allones=False):
      for r,rb in sums(config, size-lsize-1, tyvar, allones=False):
        for op in commutative_ops:
          yield set_type(op(l,r), tyvar), lb and rb

  # noncommutative operators
  for lsize in xrange(1, size-1):
    for l,lb in sums(config, lsize, tyvar):
      for r,rb in sums(config, size-lsize-1, tyvar):
        for op in noncommutative_ops:
          yield set_type(op(l,r), tyvar), lb and rb

  # TODO: functions
  for t,b in sums(config, size-2, tyvar):
    if b: continue
    # avoid generating abs(1), but still abs(width(%x)) for default type

    yield set_type(L.AbsCnxp(t), tyvar), b

  # type-variable functions
  for argtyvar in config.symbols.iterkeys():
    for t,b in sums(config, size-2, argtyvar):
      if b: continue
      # never generate log2(1) or log2(width(%x))
      yield set_type(L.Log2Cnxp(t), tyvar), tyvar == config.model.default_id

  # sums of nonsums (e.g, ~C1 + ~C2)
  for lsize in xrange(2, size-2):
    for l,lb in _sums_4(config, lsize, tyvar):
      for r,rb in _sums_4(config, size-lsize-1, tyvar):
        yield set_type(L.AddCnxp(l,r), tyvar), lb and rb
        yield set_type(L.SubCnxp(l,r), tyvar), lb and rb


def old_predicates_2(config):
  tyvars = config.symbols.keys()
  tyvars.append(config.model.default_id)
  # is there any chance of duplication?
  logger.debug('tyvars %s', tyvars)

  #for size in itertools.count(3):
  for size in xrange(3,8):
    logger.info('Generating size %s', size)

    # comparisons
    for tyvar in tyvars:
      logger.debug('comparisons for %s', tyvar)
      zero = set_type(L.Literal(0), tyvar)

      # expr == 0, expr > 0, expr < 0
      for t,b in old_sums(config, size-2, tyvar):
        if b: continue
        for cmp in ['eq', 'slt', 'sgt']:
          yield L.Comparison(cmp, t, zero)

      # expr1 < expr2, expr1 u< expr2 (nb. expr is never 0)
      for lsize in xrange(1, size-1):
        for l,bl in old_sums(config, lsize, tyvar):
          for r,br in old_sums(config, size-lsize-1, tyvar):
            if bl and br: continue
            yield L.Comparison('slt', l, r)
            yield L.Comparison('ult', l, r)

    # unary predicate functions
    for tyvar in tyvars:
      for t,b in old_sums(config, size-3, tyvar):
        if b: continue
        yield L.IntMinPred(t)
        yield L.Power2Pred(t)
        yield L.Power2OrZPred(t)

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
      yield L.OrPred(*_flatten(t))

  for t in assocs(size,combine, 2, subexprs=disjunctions, neg_subexprs=predicates):
    yield L.AndPred(*_flatten(t))

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
  tys.append(config.model.default_id)  # shouldn't already be there

  # comparisons
  for ty in tys:
    zero = set_type(L.Literal(0), ty)

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
    [(set_type(L.Literal(1), ty), True)]
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
    yield set_type(L.NegCnxp(t), ty), b

def atoms(config, ty, size):
  if size != 1: return

  for s in config.symbols.get(ty,[]):
    yield (s, False)

  for r in config.type_reps:
    yield set_type(L.WidthCnxp(r), ty), ty != config.model.default_id

def sums(config, ty, size):
  def combine(x, (y,by), neg):
    if x is None:
      if neg:
        return set_type(L.NegCnxp(y), ty), by
      return (y,by)

    x,bx = x
    if neg:
      return set_type(L.SubCnxp(x,y), ty), bx and by
    return set_type(L.AddCnxp(x,y), ty), bx and by

  return assocs(size, combine,
    neg_subexprs=lambda s: expressions(config, ty, s, one=True, sums=False))

def products(config, ty, size):
  def combine(x, y, neg):
    assert not neg
    if x is None: return y

    x,bx = x
    y,by = y
    return set_type(L.MulCnxp(x,y), ty), bx and by

  return assocs(size, combine,
    subexprs=lambda s: expressions(config, ty, s, sums=False, products=False))

def logic(config, ty, size):
  def Or(x, (y,by), neg):
    if neg:
      y = set_type(L.NotCnxp(y), ty)
    if x is None:
      return y,by

    x,bx = x
    return set_type(L.OrCnxp(x,y), ty), bx and by

  def And(x, (y,by), neg):
    if neg:
      y = set_type(L.NotCnxp(y), ty)
    if x is None:
      return y,by

    x,bx = x
    return set_type(L.AndCnxp(x,y), ty), bx and by

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
    return set_type(L.XorCnxp(x,y), ty), bx and by

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
          yield set_type(op(l,r),ty), br and bl

      for l,bl in shift_lexpr(lsize):
        for op in _shift_ops:
          yield set_type(op(l,r),ty), br and bl



def funcs(config, ty, size):
  if size < 2: return

  for t,b in expressions(config, ty, size-1):
    if b: continue
    yield set_type(L.AbsCnxp(t), ty), b

  for argty in config.symbols.iterkeys():
    for t,b in expressions(config, argty, size-1):
      if b: continue
      yield set_type(L.Log2Cnxp(t), ty), ty != config.model.default_id



cfg = Config({0: [L.Symbol('C1'), L.Symbol('C2')]},
  [L.Input('%x')],
  typing.AbstractTypeModel([],[],[],[],[],1),
)



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
