from . import enumerator
from .. import language as L
from .. import typing
from .. import smtinterp
from ..analysis import safety
from ..util.pretty import pformat
from ..z3util import mk_and, mk_or, mk_not, mk_forall
import collections
import itertools
import logging
import random
import z3

logger = logging.getLogger(__name__)

CONFLICT_SET_CUTOFF = 16
SAMPLES = 5

def mk_implies(premises, consequent):
  if premises:
    return z3.Implies(mk_and(premises), consequent)

  return consequent


TestCase = collections.namedtuple('TestCase', ['type_vector', 'values'])

REJECT, ACCEPT, UNSAFE = range(3)

def test_feature(pred, test_case, cache):
  try:
    pred_smt = cache[test_case.type_vector]
  except KeyError:
    smt = safety.Translator(test_case.type_vector)
    pre = smt(pred)
    assert not (pre.defined or pre.nonpoison or pre.qvars)
    pred_smt = (pre.safe, pre.value)
    cache[test_case.type_vector] = pred_smt

  if pred_smt[0]:
    safe = z3.simplify(z3.substitute(mk_and(pred_smt[0]), *test_case.values))
    assert z3.is_bool(safe)
    if z3.is_false(safe):
      return UNSAFE

  e = z3.simplify(z3.substitute(pred_smt[1], *test_case.values))
  assert z3.is_bool(e)
  if z3.is_true(e):
    return ACCEPT

  return REJECT

def dividing_features(samples, features):
  """Examine features in the provided iterable and yield those which divide the
  good and bad instances.
  """
  log = logger.getChild('dividing_features')

  for pred in features:
    reporter.consider_feature()
    for good, bad in samples:
      cache = {}
      good_results = [0]*3
      for g in good:
        good_results[test_feature(pred, g, cache)] += 1

      log.debug('Good Results: %s', good_results)

      if good_results[UNSAFE] or \
          (good_results[ACCEPT] and good_results[REJECT]):
        continue

      bad_results = [0]*3
      for b in bad:
        bad_results[test_feature(pred, b, cache)] += 1

      log.debug('Bad Results: %s', bad_results)

      if (good_results[ACCEPT] and not bad_results[ACCEPT]) or \
          (good_results[REJECT] and not bad_results[REJECT]):
        yield pred, cache
        break

def find_conflict_set(vectors, key):
  best = 0
  chosen = None

  for _,g,b in vectors:
    if not g or not b: continue

    val = key(len(g),len(b))
    if val > best or chosen is None:
      best = val
      chosen = (g,b)

  return chosen

find_largest_conflict_set = lambda v: find_conflict_set(v, lambda g,b: g+b)
find_smallest_conflict_set = lambda v: find_conflict_set(v, lambda g,b: -g-b)
find_most_positive_conflict_set = lambda v: find_conflict_set(v, lambda g,b: g)
find_least_negative_conflict_set = lambda v: find_conflict_set(v,lambda g,b: -b)


def sample_conflict_set(good, bad):
  if len(good) + len(bad) <= CONFLICT_SET_CUTOFF:
    return good, bad

  x = random.randrange(
    max(1, CONFLICT_SET_CUTOFF - len(bad)),
    min(CONFLICT_SET_CUTOFF, len(good)+1)
  )

  g = random.sample(good, x)
  b = random.sample(bad, CONFLICT_SET_CUTOFF - x)
  assert len(g) + len(b) == CONFLICT_SET_CUTOFF

  return g,b


def partition(feature, cache, cases):
  partitions = [[],[],[]]

  for tc in cases:
    result = test_feature(feature, tc, cache)
    partitions[result].append(tc)

  return partitions

def extend_feature_vectors(vectors, feature, cache=None):
  if cache is None:
    cache = {}

  new_vectors = []
  for vector, good, bad in vectors:
    good_p = partition(feature, cache, good)
    bad_p = partition(feature, cache, bad)

    # abort if the feature is unsafe for any good instance
    if good_p[UNSAFE]:
      return None
    # NOTE: this is a conservative method to ensure the boolean learner can
    #       find an expression

    for result in xrange(3):
      if good_p[result] or bad_p[result]:
        new_vectors.append((vector + (result,), good_p[result], bad_p[result]))

  return new_vectors

def score_features(vectors):
  """For each feature, calculate the number of examples it isolates.

  A feature isolates an example if the example would be moved into
  a conflict set if the feature were removed.
  """

  features = len(vectors[0][0])
  pos_count = collections.defaultdict(
    lambda: collections.defaultdict(collections.Counter))
  neg_count = collections.defaultdict(
    lambda: collections.defaultdict(collections.Counter))

  for v,pos,neg in vectors:
    for f in xrange(features):
      pos_count[f][v[0:f]+v[f+1:]][v[f]] += len(pos)
      neg_count[f][v[0:f]+v[f+1:]][v[f]] += len(neg)

  score  = [0] * features
  pscore = [0] * features

  for f in xrange(features):
    for k,pc in pos_count[f].iteritems():
      nc = neg_count[f][k]
      # check whether pc and nc include both pos and neg examples and isolated examples
      has_pos = any(pc.itervalues())
      has_neg = any(nc.itervalues())
      if not (has_pos and has_neg):
        continue

      pos_isolated = sum(pc[r] for r in xrange(3) if not nc[r])
      neg_isolated = sum(nc[r] for r in xrange(3) if not pc[r])
      score[f] += pos_isolated + neg_isolated
      pscore[f] += pos_isolated


  return score, pscore

def clause_accepts(clause, vector):
  return any(vector[l] == REJECT if l < 0 else vector[l] == ACCEPT
              for l in clause)

def consistent_clause(clause, vectors):
  return all(clause_accepts(clause, v) for v in vectors)

def all_clauses(lits, size):
  for c in itertools.combinations(xrange(lits), size):
    for p in itertools.product([True,False], repeat=size):
      yield tuple(i if s else i-lits for (i,s) in itertools.izip(c,p))

def learn_boolean(feature_count, goods, bads):
  log = logger.getChild('learn_bool')
  log.debug('called with %s features; vectors: %s good, %s bad', feature_count,
    len(goods), len(bads))

  clauses = []
  excluded_by = [] # for each clause, the bad vector ids it excludes
  excluding = collections.defaultdict(set) # n -> set of clauses excluding n vectors
  excludes = collections.defaultdict(list) # vector id -> list of clauses

  k = 0

  # generate clauses until all bad vectors are excluded
  while len(excludes) < len(bads):
    k += 1
    assert k <= feature_count # FIXME
    reporter.increase_clause_size()
    clauses.extend(c for c in all_clauses(feature_count, k)
      if consistent_clause(c, goods))

    log.debug('size %s; %s consistent clauses', k, len(clauses))

    # note the vectors excluded by each new clause
    for c in xrange(len(excluded_by), len(clauses)):
      exc = set()
      for v,vector in enumerate(bads):
        if not clause_accepts(clauses[c], vector):
          exc.add(v)
          excludes[v].append(c)
      excluded_by.append(exc)
      excluding[len(exc)].add(c)

    log.debug('%s of %s bad vectors excluded', len(excludes), len(bads))

  cover = []

  # repeatedly select the clause which excludes the most bad vectors
  for s in xrange(max(excluding), 0, -1):
    if s not in excluding: continue

    cs = excluding[s]
    log.debug('%s vectors to exclude', len(excludes))

    while cs:
      log.debug('%s clauses excluding %s', len(cs), s)

      # select arbitrary clause
      # (pick the earliest one, as it will be simplest)
      #c = cs.pop()
      c = min(cs)
      cs.remove(c)

      cover.append(clauses[c])
      reporter.add_clause()

      # remove all vectors excluded by clauses[c]
      for v in excluded_by[c]:
        for xc in excludes.pop(v):
          if xc == c: continue

          #log.debug('deleting vector %s from clause %s', v, xc)
          exc = excluded_by[xc]
          excluding[len(exc)].remove(xc)
          exc.remove(v)
          excluding[len(exc)].add(xc)

  return cover

def learn_incomplete_boolean(feature_count, weighted_positive_vectors,
    negative_vectors, weight_threshold, max_size=1):
  """Find an expression which rejects all negative vectors, accepts more than
  a threshold of positive examples.
  """
  log = logger.getChild('learn_bool')

  clauses = []

  # generate all clauses up to the maximum size
  for k in xrange(1,max_size+1):
    clauses.extend(all_clauses(feature_count, k))
    log.debug('size %s, clauses %s', k, len(clauses))

  clauses_accepting_weight = collections.defaultdict(set)
  clauses_accepting_vector = collections.defaultdict(list)
  weight_accepted_by_clause = {}
  vectors_rejected_by_clause = []

  for c,clause in enumerate(clauses):
    exc = set()
    clause_weight = 0
    for v,(vector,weight) in enumerate(weighted_positive_vectors):
      if clause_accepts(clause, vector):
        clause_weight += weight
        clauses_accepting_vector[v].append(c)
      else:
        exc.add(v)

    clauses_accepting_weight[clause_weight].add(c)
    vectors_rejected_by_clause.append(exc)
    weight_accepted_by_clause[c] = clause_weight

  builder = reject_negative_vectors(negative_vectors)
  builder.next()
  for w in xrange(max(clauses_accepting_weight), weight_threshold, -1):
    if w not in clauses_accepting_weight: continue

    cs = clauses_accepting_weight[w]
    clauses_to_add = []

    while cs:
      log.debug('%s clauses accepting weight %s', len(cs), w)

      # choose arbitrary clause
      #c = cs.pop()
      c = min(cs)
      cs.remove(c)
      log.debug('adding clause %s %s', c, clauses[c])

      # now that we've chosen this clause, we don't need to track its weight
      del weight_accepted_by_clause[c]

      clauses_to_add.append(clauses[c])

      for v in vectors_rejected_by_clause[c]:
        vw = weighted_positive_vectors[v][1]

        # adjust the weight of any clauses accepting this vector
        # (if it has already been removed, do nothing)
        for xc in clauses_accepting_vector.pop(v, []):
          if xc not in weight_accepted_by_clause: continue

          xw = weight_accepted_by_clause[xc]

          if xw > w:
            continue
          clauses_accepting_weight[xw].remove(xc)
          weight_accepted_by_clause[xc] -= vw
          clauses_accepting_weight[weight_accepted_by_clause[xc]].add(xc)


    log.debug('sending clauses %s', clauses_to_add)
    pre = builder.send(clauses_to_add)
    if pre:
      return pre


  # if we got this far, then nothing was enough to exclude the negative vectors
  return None
# FIXME: either remove, or replace learn_incomplete_boolean
def learn_incomplete_boolean_tryhard(feature_count, weighted_positive_vectors,
    negative_vectors, weight_threshold, max_size=1):
  """Find an expression which rejects all negative vectors, accepts more than
  a threshold of positive examples.
  """
  log = logger.getChild('learn_bool.tryhard')

  clauses = []

  max_weight = sum(v[1] for v in weighted_positive_vectors)

  # generate all clauses up to the maximum size
  for k in xrange(1,max_size+1):
    clauses.extend(all_clauses(feature_count, k))
    log.debug('size %s, clauses %s', k, len(clauses))

  nonselected = set(xrange(len(clauses)))
  best_coverage = 0
  best_pre = None

  while nonselected:
    clauses_accepting_weight = collections.defaultdict(set)
    clauses_accepting_vector = collections.defaultdict(list)
    weight_accepted_by_clause = {}
    vectors_rejected_by_clause = []

    initial_weight = {}
    for c,clause in enumerate(clauses):
      exc = set()
      clause_weight = 0
      for v,(vector,weight) in enumerate(weighted_positive_vectors):
        if clause_accepts(clause, vector):
          clause_weight += weight
          clauses_accepting_vector[v].append(c)
        else:
          exc.add(v)

      clauses_accepting_weight[clause_weight].add(c)
      vectors_rejected_by_clause.append(exc)
      weight_accepted_by_clause[c] = clause_weight

      initial_weight[c] = clause_weight

    # get the heaviest nonselected clause
    heaviest_nonselected = max(
      itertools.ifilter(lambda c: c in nonselected, xrange(len(clauses))),
      key=initial_weight.get
    )
    log.debug('heaviest: %s %s', heaviest_nonselected, clauses[heaviest_nonselected])

    w = weight_accepted_by_clause[heaviest_nonselected]
    if w < best_coverage:
      break

    weight_accepted_by_clause[heaviest_nonselected] = max_weight
    clauses_accepting_weight[w].remove(heaviest_nonselected)
    clauses_accepting_weight[max_weight].add(heaviest_nonselected)

    builder = reject_negative_vectors(negative_vectors)
    builder.next()
    for w in xrange(max(clauses_accepting_weight), weight_threshold, -1):

      cs = clauses_accepting_weight.get(w)
      if not cs: continue

      clauses_to_add = []

      while cs:
        log.debug('%s clauses accepting weight %s', len(cs), w)

        # choose arbitrary clause
        #c = cs.pop()
        c = min(cs)
        cs.remove(c)
        log.debug('adding clause %s %s', c, clauses[c])

        # now that we've chosen this clause, we don't need to track its weight
        del weight_accepted_by_clause[c]

        del initial_weight[c]
        nonselected.discard(c)

        clauses_to_add.append(clauses[c])

        for v in vectors_rejected_by_clause[c]:
          vw = weighted_positive_vectors[v][1]

          # adjust the weight of any clauses accepting this vector
          # (if it has already been removed, do nothing)
          for xc in clauses_accepting_vector.pop(v, []):
            if xc not in weight_accepted_by_clause: continue

            xw = weight_accepted_by_clause[xc]

            if xw > w:
              continue
            clauses_accepting_weight[xw].remove(xc)
            weight_accepted_by_clause[xc] -= vw
            clauses_accepting_weight[weight_accepted_by_clause[xc]].add(xc)


      log.debug('sending clauses %s', clauses_to_add)
      pre = builder.send(clauses_to_add)
      if pre:
        log.debug('Got back: %s', pre)
        cv = sum(v[1] for v in weighted_positive_vectors
                  if all(clause_accepts(c, v[0]) for c in pre))
        # TODO: use min of initial_weights?
        log.debug('Coverage: %s (best %s)', cv, best_coverage)
        if cv > best_coverage or (cv == best_coverage and len(pre) < len(best_pre)):
          # TODO: remove log msg once status of tryhard is deterimined
          if best_coverage > 0:
            log.info('Trying hard paid off %s -> %s', best_coverage, cv)
          best_coverage = cv
          best_pre = pre

        break

  # if we got this far, then nothing was enough to exclude the negative vectors
  return best_pre


# TODO: rewrite learn_boolean to use this
def reject_negative_vectors(vectors):
  """Find an expression which rejects all the provided vectors, using the
  clauses sent to the generator.

  Yield None if more clauses are needed.
  """
  log = logger.getChild('learn_bool')
  clauses = []
  excluded_by = [] # for each clause, the bad vector ids it excludes
  excluding = collections.defaultdict(set) # n -> set of clauses excluding n vectors
  excludes = collections.defaultdict(list) # vector id -> list of clauses

  while len(excludes) < len(vectors):
    new_clauses = yield
    clauses.extend(new_clauses)

    for c in xrange(len(excluded_by), len(clauses)):
      exc = set()
      for v,vector in enumerate(vectors):
        if not clause_accepts(clauses[c], vector):
          exc.add(v)
          excludes[v].append(c)
      excluded_by.append(exc)
      excluding[len(exc)].add(c)

    log.debug('%s of %s negative vectors excluded', len(excludes), len(vectors))

  # everything is covered
  cover = []

  # repeatedly select the clause which excludes the most bad vectors
  for s in xrange(max(excluding), 0, -1):
    if s not in excluding: continue

    cs = excluding[s]

    while cs:
      log.debug('%s to exclude, %s excluding %s', len(excludes), len(cs), s)

      # select arbitrary clause
      # (pick the earliest one, as it will be simplest)
      #c = cs.pop()
      c = min(cs)
      cs.remove(c)

      cover.append(clauses[c])
      reporter.add_clause()

      # remove all vectors excluded by clauses[c]
      for v in excluded_by[c]:
        for xc in excludes.pop(v):
          if xc == c: continue

          #log.debug('deleting vector %s from clause %s', v, xc)
          exc = excluded_by[xc]
          excluding[len(exc)].remove(xc)
          exc.remove(v)
          excluding[len(exc)].add(xc)

  yield cover


def mk_AndPred(clauses):
  clauses = tuple(clauses)
  if len(clauses) == 1:
    return clauses[0]

  return L.AndPred(*clauses)

def mk_OrPred(clauses):
  clauses = tuple(clauses)
  if len(clauses) == 1:
    return clauses[0]

  return L.OrPred(*clauses)

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


def make_precondition(features, feature_vectors, incomplete):
  """Return an expression which is true for the positive feature vectors.

  incomplete - require success only for the most positive vector
  """
  log = logger.getChild('pie')

  if incomplete:
    pos_vecs = filter(lambda v: not v[2], feature_vectors)
    best_vec = max(pos_vecs, key=lambda v: len(v[1]))
    pos_vecs = [best_vec[0]]
  else:
    pos_vecs = [v[0] for v in feature_vectors if not v[2]]

  neg_vecs = [v[0] for v in feature_vectors if v[2]]

#   log.debug('make_precondition\n+ %s\n- %s', pos_vecs, neg_vecs)

  clauses = learn_boolean(len(features), pos_vecs, neg_vecs)

  log.debug('clauses: %s', clauses)

  # only useful when doing an incomplete precondition, but it's cheap
  coverage = sum(len(v[1]) for v in feature_vectors if not v[2] and
    all(clause_accepts(c, v[0]) for c in clauses))

  log.debug('coverage: %s', coverage)

  pre = mk_AndPred(
          mk_OrPred(
            negate_pred(features[l]) if l < 0 else features[l] for l in c)
          for c in clauses)

  return pre, coverage, features


def infer_preconditions_by_examples(config, positive, negative,
    features = (),
    incompletes = False,
    conflict_set = find_largest_conflict_set):
  """Synthesize preconditions which accepts the positive instances and rejects
  the negative ones. This is a generator, but will only yield one result if
  incompletes is False.

  features - an optional list of features to start with
  incompletes - if true, yield intermediate preconditions which accept some
    but not all positive instances
  conflict_set - a strategy for selecting conflict sets
  """
  log = logger.getChild('pie')
  features = list(features)

  log.info('Inferring: examples %s/%s, features %s', len(positive),
    len(negative), len(features))

  feature_vectors = [((), positive, negative)]
  for f in features:
    new_vectors = extend_feature_vectors(feature_vectors, f)

    if new_vectors is None:
      log.info('Skipping feature %s', f)
      continue

    feature_vectors = new_vectors

    reporter.accept_feature()
    if log.isEnabledFor(logging.DEBUG):
      log.debug('Feature Vectors\n  ' +
        pformat([(v,len(g),len(b)) for (v,g,b) in feature_vectors],
          indent=2))

  incomplete_coverage = 0
  while True:

    # if we are yielding intermediate results, then see if any positive
    # instances have moved out of a conflict set, and then return a precondition
    # which covers at least the largest positive vector
    if incompletes:
      # ----
      # FIXME: move scoring somewhere appropriate
      if log.isEnabledFor(logging.DEBUG):
        from .. import transform
        score, pscore = score_features(feature_vectors)
        fmt = transform.Formatter()
        log.debug('Feature scores:\n' + '\n'.join(
          '  {:5,} {:5,} : {}'.format(score[f], pscore[f],
                                transform.format(features[f], fmt))
            for f in xrange(len(features))))
      # ----

      available_positives = sum(len(v[1]) for v in feature_vectors if not v[2])
      log.debug('available positives: %s', available_positives)
      if available_positives > incomplete_coverage:
        incomplete_coverage = available_positives
        yield make_precondition(features, feature_vectors, incompletes)

        # -----
        # FIXME: use only one method for finding incomplete preconditions
        # FIXME: none of these check for None results
        wpos = [(v[0], len(v[1])) for v in feature_vectors if not v[2]]
        neg = [v[0] for v in feature_vectors if v[2]]
        cl = learn_incomplete_boolean_tryhard(len(features), wpos, neg, 0)
        log.debug('clauses: %s', cl)
        p = mk_AndPred(
              mk_OrPred(
                negate_pred(features[l]) if l < 0 else features[l] for l in c)
              for c in cl)

        cv = sum(len(v[1]) for v in feature_vectors if not v[2] and
          all(clause_accepts(c, v[0]) for c in cl))

        log.debug('coverage: %s', cv)

        yield p, cv, features
#
#         # do the same with k <= 2
#         cl = learn_incomplete_boolean_tryhard(len(features), wpos, neg, 0, 2)
#         log.debug('clauses: %s', cl)
#         cv = sum(len(v[1]) for v in feature_vectors if not v[2] and
#           all(clause_accepts(c, v[0]) for c in cl))
#         log.debug('coverage: %s', cv)
#
#         p = mk_AndPred(
#               mk_OrPred(
#                 negate_pred(features[l]) if l < 0 else features[l] for l in c)
#               for c in cl)
#
#         yield p, cv, features
        # ----

    conflict = conflict_set(feature_vectors)
    if conflict is None:
      break

    # prepare to learn a new feature
    if len(conflict[0]) + len(conflict[1]) > CONFLICT_SET_CUTOFF:
      samples = [sample_conflict_set(*conflict) for _ in xrange(SAMPLES)]
    else:
      samples = [conflict]

#     if log.isEnabledFor(logging.DEBUG):
#       log.debug('samples\n' + pformat(samples, prefix='  '))

    # find a feature which divides a sample and is safe for all positives
    generated_features = dividing_features(
      samples, enumerator.predicates(config))
    new_vectors = None
    while new_vectors is None:
      f, cache = generated_features.next()
      log.debug('Candidate feature\n%s', f)
      new_vectors = extend_feature_vectors(feature_vectors, f, cache)

    # add the new feature
    features.append(f)
    feature_vectors = new_vectors

    reporter.accept_feature()
    log.info('Feature %s: %s', len(features), f)
    if log.isEnabledFor(logging.DEBUG):
      log.debug('Feature Vectors\n  ' +
        pformat([(v,len(g),len(b)) for (v,g,b) in feature_vectors],
          indent=2))

  # no conflict sets left
  yield make_precondition(features, feature_vectors, False)

def satisfiable(expr, substitutes):
  """Return whether expr can be satisfied, given the substitutions.
  """
  s = z3.Solver()
  s.add(z3.substitute(expr, *substitutes))
  res = s.check()

  if res == z3.unknown:
    logging.warn('Unknown result:\n%s', s)

  return res == z3.sat

def get_models(expr, vars):
  """Generate tuples satisfying the expression.
  """

  s = z3.Solver()
  s.add(expr)
  res = s.check()

  while res == z3.sat:
    model = s.model()
    yield tuple((v,model[v]) for v in vars)

    s.add(z3.Or([v != model[v] for v in vars]))
    res = s.check()

  if res == z3.unknown:
    raise Exception('Solver returned unknown: ' + s.reason_unknown())

def interpret_opt(smt, opt, strengthen=False):
  """Translate opt to form mk_and(S + P) => Q and return S, P, Q.
  """

  if strengthen:
    assert opt.pre
    pre = smt(opt.pre)
    safe = pre.safe + pre.defined + pre.nonpoison + [pre.value]
  else:
    safe = []

  src = smt(opt.src)
  if src.qvars:
    raise Exception('quantified variables in opt {!r}'.format(opt.name))

  assert not src.safe

  sd = src.defined + src.nonpoison

  tgt = smt(opt.tgt)
  safe.extend(tgt.safe)

  td = tgt.defined + tgt.nonpoison + [src.value == tgt.value]

  return safe, sd, mk_and(td)

def random_cases(types):
  """Generate infinitely many possible values for the given list of types.
  """
  assert all(isinstance(ty, L.IntType) for ty in types)

  while True:
    yield tuple(random.randrange(0, 2**ty.width) for ty in types)

def get_corner_cases(types):
  """Generate every combination of 0,1,-1, and INT_MIN.
  """
  def corners(ty):
    if ty == L.IntType(1):
      return [0,1]
    elif isinstance(ty, L.IntType):
      return [0,1,2**ty.width-1,2**(ty.width-1)]
    else:
      return []

  return itertools.product(*map(corners, types))

def make_test_cases(opt, symbols, inputs, type_vectors,
    num_random, num_good, num_bad, assumptions=(), strengthen=False):
  log = logger.getChild('make_test_cases')


  goods = []
  bads = []

  assert num_bad > 0
  num_random = max(0, num_random)

  for type_vector in type_vectors:
    log.debug('Making cases for %s', type_vector)

    smt = safety.Translator(type_vector)

    symbol_smts = [smt.eval(t) for t in symbols]

    safe, premises, consequent = interpret_opt(smt, opt, strengthen)
    assumptions_smt = [smt.eval(t) for t in assumptions]

    e = mk_and(safe + [mk_implies(premises, consequent)])

    query = mk_and(assumptions_smt + [z3.Not(e)])
    log.debug('Negative Query:\n%s', query)

    solver_bads = [tc
      for tc in itertools.islice(get_models(query, symbol_smts), num_bad)
      if not any(v is None for (_,v) in tc)]
      # NOTE: getting None as a value means we can't use it as a test-case,
      # but discarding them may lead to false positives

    log.debug('%s counter-examples', len(solver_bads))

    bads.extend(TestCase(type_vector, tc) for tc in solver_bads)
    reporter.test_cases(goods, bads)

    skip = set(tuple(v.as_long() for (_,v) in tc) for tc in solver_bads)


    if num_good > 0:
      input_smts = [smt.eval(t) for t in inputs]

      query = mk_and(assumptions_smt + premises + [mk_forall(input_smts, [e])])
      log.debug('Positive Query\n%s', query)
      solver_goods = [tc for
        tc in itertools.islice(get_models(query, symbol_smts), num_good)
        if not any(v is None for (_,v) in tc)]

      log.debug('%s pro-examples', len(solver_goods))

      goods.extend(TestCase(type_vector, tc) for tc in solver_goods)
      skip.update(tuple(v.as_long() for (_,v) in tc) for tc in solver_goods)
      reporter.test_cases(goods, bads)

    filter = mk_and(assumptions_smt + premises) \
      if assumptions_smt or premises else None

    symbol_types = [type_vector[typing.context[s]] for s in symbols]
    corner_tcs = get_corner_cases(symbol_types)
    random_tcs = itertools.islice(random_cases(symbol_types), num_random)

    for tc_vals in itertools.chain(corner_tcs, random_tcs):
      if tc_vals in skip: continue

      skip.add(tc_vals)

      tc = TestCase(type_vector,
        tuple(itertools.imap(lambda s,v,ty: (s, z3.BitVecVal(v, ty.width)),
          symbol_smts, tc_vals, symbol_types)))

      if filter and not satisfiable(filter, tc.values):
        continue

      if satisfiable(z3.Not(e), tc.values):
        bads.append(tc)
      else:
        goods.append(tc)

      reporter.test_cases(goods, bads)


  return goods, bads

def exponential_sample(iterable):
  """Yield iter[0], iter[1], iter[2], iter[4], ...
  """
  it = iter(iterable)

  yield it.next()
  yield it.next()

  skip = 1
  while True:
    for _ in xrange(skip):
      x = it.next()

    yield x
    skip *= 2

def check_refinement(opt, assumptions, pre, symbols, solver_bad):
  """Return counter-examples
  """
  # TODO: add support for weakening
  log = logger.getChild('check_refinement')

  for type_vector in opt.type_models():
    reporter.test_precondition()
    smt = safety.Translator(type_vector)

    tgt_safe, premises, consequent = interpret_opt(smt, opt)  # cache this?

    log.debug('\ntgt_safe %s\npremises %s\nconsequent %s',
      tgt_safe, premises, consequent)

    meta_premise = []
    for t in assumptions:
      t_smt = smt(t)
      meta_premise.extend(t_smt.safe)
      meta_premise.extend(t_smt.defined)
      meta_premise.extend(t_smt.nonpoison)
      meta_premise.append(t_smt.value)

    pre_smt = smt(pre)
    meta_premise.extend(pre_smt.safe)
    meta_premise.extend(pre_smt.defined)
    meta_premise.extend(pre_smt.nonpoison)
    meta_premise.append(pre_smt.value)

    log.debug('meta_premise\n%s', meta_premise)

    e = mk_implies(meta_premise,
                   mk_and(tgt_safe + [mk_implies(premises, consequent)]))
    log.debug('Validity check\n%s', e)

    symbol_smts = [smt.eval(t) for t in symbols]
    counter_examples = list(TestCase(type_vector, tc)
      for tc in itertools.islice(
        get_models(z3.Not(e), symbol_smts), solver_bad)
    )

    if counter_examples:
      return counter_examples

  return []

def check_completeness(opt, assumptions, pre, symbols, inputs, solver_good):
  """Return positive examples which the precondition excludes.
  """

  log = logger.getChild('check_completeness')
  log.debug('Checking completeness')

  for type_vector in opt.type_models():
    log.debug('checking types %s', type_vector)
    reporter.test_precondition() # make more specific?
    smt = safety.Translator(type_vector)

    tgt_safe, premises, consequent = interpret_opt(smt, opt)

    meta_premise = []
    for t in assumptions:
      t_smt = smt(t)
      meta_premise.extend(t_smt.safe)
      meta_premise.append(t_smt.value)
      assert not t_smt.defined or t_smt.value
      # TODO: add these to premises?

    pre_smt = smt(pre)
    meta_premise.append(mk_not(pre_smt.safe + [pre_smt.value]))
    assert not pre_smt.defined or pre_smt.value
    # TODO: add these to premises?

    log.debug('meta_premise\n%s', meta_premise)

    input_smts = [smt.eval(t) for t in inputs]

    e = mk_and(meta_premise +
         [mk_forall(input_smts, tgt_safe + [mk_implies(premises, consequent)])])

    log.debug('Validity check\n%s', e)
    symbol_smts = [smt.eval(t) for t in symbols]

    false_negatives = list(TestCase(type_vector, tc)
      for tc in itertools.islice(get_models(e, symbol_smts), solver_good)
    )

    if false_negatives:
      return false_negatives

  return []

def infer_precondition(opt,
    features=(),
    assumptions=(),
    random_cases=100,
    solver_good=10,
    solver_bad=10,
    strengthen=False,
    incompletes=False,
    weakest=False,
    conflict_set=find_largest_conflict_set):
  log = logger.getChild('infer')

  if log.isEnabledFor(logging.INFO):
    log.info('infer_precondtion invoked on %r (%s features,'
      '%s randoms, %s +solver, %s -solver',
      opt.name, 'No' if features is None else len(features),
      random_cases, solver_good, solver_bad)

  type_model = opt.abstract_type_model()
  type_vectors = list(exponential_sample(type_model.type_vectors()))

  for t in assumptions:
    type_model.extend(t)

  for t in features:
    type_model.extend(t)

  symbols = []
  ty_symbols = collections.defaultdict(list)
  inputs = []
  reps = [None] * type_model.tyvars
  for t in L.subterms(opt.src):
    if isinstance(t, (L.Input, L.Instruction)):
      reps[typing.context[t]] = t
    if isinstance(t, L.Symbol):
      symbols.append(t)
      ty_symbols[typing.context[t]].append(t)
    elif isinstance(t, L.Input):
      inputs.append(t)

  reps = [r for r in reps if r is not None]
  assert all(isinstance(t, (L.Input, L.Instruction)) for t in reps)

  goods, bads = make_test_cases(opt, symbols, inputs, type_vectors,
    random_cases, solver_good, solver_bad, assumptions, strengthen)

  log.info('Initial test cases: %s good, %s bad', len(goods), len(bads))

  # ----
  # FIXME: remove or formalize test of given precondition
  if opt.pre:
    cache = {}
    prepos = sum(1 for e in goods if test_feature(opt.pre, e, cache) == ACCEPT)
    preneg = sum(1 for e in bads if test_feature(opt.pre, e, cache) != ACCEPT)
    msg = 'Accepts {}/{} positive; rejects {}/{} negative'.format(
      prepos, len(goods), preneg, len(bads))
    reporter.clear_message()
    log.info('Given precondition: %s', msg)
    print ';', msg
  # ----

  valid = not bads
  pre = None

  config = enumerator.Config(ty_symbols, reps, type_model)

  while not valid:
    reporter.begin_round()

    pres = infer_preconditions_by_examples(config, goods, bads,
      features=features, incompletes=incompletes, conflict_set=conflict_set)

    valid = True

    for pre, coverage, ifeatures in pres:
      if log.isEnabledFor(logging.INFO):
        log.info('Inferred precondition\n' + pformat(pre, prefix='  '))

      counter_examples = check_refinement(opt, assumptions, pre, symbols, solver_bad)

      if counter_examples:
        valid = False
        features = ifeatures
        bads.extend(counter_examples)
        reporter.test_cases(goods, bads)
        log.info('%s false positives', len(counter_examples))
        break

      if weakest and coverage == len(goods):
        false_negatives = check_completeness(
          opt, assumptions, pre, symbols, inputs, solver_good
        )

        if false_negatives:
          valid = False
          features = ifeatures
          goods.extend(false_negatives)
          reporter.test_cases(goods, bads)
          log.info('%s false negatives', len(false_negatives))
          break

      yield pre, coverage, ifeatures


# ----

import sys, os

class SilentReporter(object):
  def test_cases(self, good, bad): pass
  def consider_feature(self): pass
  def accept_feature(self): pass
  def test_precondition(self): pass
  def begin_round(self): pass
  def increase_clause_size(self): pass
  def add_clause(self): pass

class Reporter(object):
  _fmt_cases = 'Round {0.round} Adding test cases: {0.num_good_cases:,}/{0.num_bad_cases:,}'
  _fmt_features = 'Round {0.round} Considered {0.generated_features:5,} Accepted {0.features:2}'
  _fmt_cnf = 'Round {0.round} Adding {0.k}-CNF clauses of {0.features} features'
  _fmt_clauses = 'Round {0.round} Selected {0.clauses} clauses of {0.features} features'
  _fmt_proofs = 'Round {0.round} Testing: {0.proofs:2} proofs'

  def __init__(self):
    self.num_good_cases = 0
    self.num_bad_cases = 0
    self.generated_features = 0
    self.features = 0
    self.k = 0
    self.clauses = 0
    self.proofs = 0
    self.round = 0
    self.width = int(os.environ.get('COLUMNS', 80))

    if sys.stdout.isatty():
      self.status = sys.stdout
    elif sys.stderr.isatty():
      self.status = sys.stderr
    else:
      self.status = None

  def write_message(self, msg):
    self.status.write('\r')
    self.status.write(msg[0:self.width])
    self.status.write(' ' * (self.width - len(msg)))
    self.status.flush()

  def clear_message(self):
    if self.status:
      self.status.write('\r')
      self.status.write(' ' * self.width)
      self.status.write('\r')
      self.status.flush()

  def test_cases(self, good, bad):
    self.num_good_cases = len(good)
    self.num_bad_cases = len(bad)
    if self.status:
      self.write_message(self._fmt_cases.format(self))

  def consider_feature(self):
    self.generated_features += 1
    if self.status:
      self.write_message(self._fmt_features.format(self))

  def accept_feature(self):
    self.features += 1
    if self.status:
      self.write_message(self._fmt_features.format(self))

  def increase_clause_size(self):
    self.k += 1
    if self.status:
      self.write_message(self._fmt_cnf.format(self))

  def add_clause(self):
    self.clauses += 1
    if self.status:
      self.write_message(self._fmt_clauses.format(self))

  def begin_round(self):
    self.round += 1
    #self.generated_features = 0
    self.features = 0
    self.k = 0
    self.clauses = 0
    self.proofs = 0

  def test_precondition(self):
    if self.status:
      self.write_message(self._fmt_proofs.format(self))

    self.proofs += 1

reporter = SilentReporter()

def set_reporter(rep):
  global reporter
  reporter = rep

cs_strategies = {
  'largest': find_largest_conflict_set,
  'smallest': find_smallest_conflict_set,
  'maxpos': find_most_positive_conflict_set,
  'minneg': find_least_negative_conflict_set,
}

default_strengthen = False
default_weakest = False
default_assume_pre = False
default_pre_features = False
default_incompletes = True
default_assumptions = True
default_features = True
default_echo = True
default_strategy = 'largest'

def main():
  import argparse, sys, logging.config
  from alive import config, transform
  from alive.parser import read_opt_files
  from alive.util.args import NegatableFlag
  logging.config.dictConfig(config.logs)

  parser = argparse.ArgumentParser()
  parser.add_argument('--strengthen', action=NegatableFlag,
    default=default_strengthen,
    help='Find a stronger precondition')
  parser.add_argument('--weakest', action=NegatableFlag,
    default=default_weakest,
    help='Ensure precondition accepts all valid instances')
  parser.add_argument('--assume-pre', action=NegatableFlag,
    default=default_assume_pre,
    help='Treat precondition as an assumption')
  parser.add_argument('--pre-features', action=NegatableFlag,
    default=default_pre_features,
    help='Take clauses from precondition as initial features')
  parser.add_argument('--incompletes', action=NegatableFlag,
    default=default_incompletes,
    help='Report too-strong preconditions during inference')
  parser.add_argument('--assumptions', action=NegatableFlag,
    default=default_assumptions,
    help='Use assumptions in Assume: headers')
  parser.add_argument('--features', action=NegatableFlag,
    default=default_features,
    help='Use features provided in Feature: headers')
  parser.add_argument('--echo', action=NegatableFlag,
    default=default_echo,
    help='Print the input optimizations before inferring')
  parser.add_argument('--strategy', action='store',
    default=default_strategy,
    choices=cs_strategies,
    help='Method for choosing conflict set')
  parser.add_argument('file', type=argparse.FileType('r'), nargs='*',
    default=[sys.stdin])

  args = parser.parse_args()

  for opt,features,assumes in read_opt_files(args.file, extended_results=True):
    print '-----'

    if not args.assumptions:
      assumes = []
    if args.assume_pre:
      assumes.append(opt.pre)

    if not args.features:
      features = []
    if args.pre_features and opt.pre:
      features.extend(t for t in L.subterms(opt.pre)
                        if isinstance(t, (L.Comparison, L.FunPred)))

    if args.echo:
      hds = [('Assume:', t) for t in assumes]
      if opt.pre:
        hds.append(('Pre:', opt.pre))
      hds.extend(('Feature:', t) for t in features)
      print transform.format_parts(opt.name, hds, opt.src, opt.tgt)

    set_reporter(Reporter())

    pres = infer_precondition(opt, strengthen=args.strengthen,
      weakest=args.weakest,
      features=features,
      assumptions=assumes,
      random_cases=500,
      incompletes=args.incompletes,
      conflict_set=cs_strategies[args.strategy])

    for pre, coverage, ifeatures in pres:
      reporter.clear_message()

      hds = [('Feature:', t) for t in ifeatures] + \
        [('Assume:', t) for t in assumes] + [('Pre:', pre)]

      print
      print transform.format_parts(opt.name, hds, opt.src, opt.tgt)
      print '''; positive instances {1:,} of {0.num_good_cases:,}
; negative instances {0.num_bad_cases:,}
; rounds {0.round:,}
; features in final round {0.features:,}
; total features generated {0.generated_features:,}'''.format(reporter,coverage)
      sys.stdout.flush()

if __name__ == '__main__':
  main()
