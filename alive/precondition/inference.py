from . import enumerator
from .. import language as L
from .. import typing
from .. import smtinterp
from ..analysis import safety
from ..util.pretty import pformat
from ..z3util import mk_and, mk_or, mk_forall
import collections
import itertools
import logging
import random
import z3

logger = logging.getLogger(__name__)

CONFLICT_SET_CUTOFF = 16

def mk_implies(premises, consequent):
  if premises:
    return z3.Implies(mk_and(premises), consequent)

  return consequent


TestCase = collections.namedtuple('TestCase', ['type_vector', 'values'])

def test_feature(pred, test_case, cache):
  try:
    pred_smt = cache[test_case.type_vector]
  except KeyError:
    smt = safety.Translator(test_case.type_vector)
    pre = smt(pred)
    assert not (pre.defined or pre.nonpoison or pre.qvars)
    pred_smt = mk_and(pre.safe + [pre.value])
    cache[test_case.type_vector] = pred_smt

  e = z3.simplify(z3.substitute(pred_smt, *test_case.values))
  assert z3.is_bool(e)
  return z3.is_true(e)

def learn_feature(config, good, bad):
  log = logger.getChild('learn_feature')
  for size in itertools.count(3):
    log.info('Checking size %s', size)
    for pred in enumerator.predicates(size, config):
      log.debug('Checking %s', pred)
      reporter.consider_feature()

      cache = {}
      good_accept = sum(1 for g in good if test_feature(pred, g, cache))
      bad_accept  = sum(1 for b in bad if test_feature(pred, b, cache))

      log.debug('Accepted: %s good, %s bad', good_accept, bad_accept)

      if (good_accept == len(good) and bad_accept == 0) or \
          (good_accept == 0 and bad_accept == len(bad)):
        return pred, cache
#       if all(test_feature(pred, g, cache) for g in good) and \
#           all(not test_feature(pred, b, cache) for b in bad):
#         return pred, cache

def learn_feature_1(config, good, bad):
  log = logger.getChild('learn_feature')
  threshold = min(CONFLICT_SET_CUTOFF, len(good)+len(bad))
  for size in itertools.count(3):
    log.info('Checking size %s', size)
    for pred in enumerator.predicates(size, config):
      log.debug('Checking %s', pred)
      reporter.consider_feature()

      cache = {}
      good_accept = sum(1 for g in good if test_feature(pred, g, cache))
      good_reject = len(good) - good_accept
      bad_accept  = sum(1 for b in bad if test_feature(pred, b, cache))
      bad_reject  = len(bad) - bad_accept

      log.debug('Accepted: %s good, %s bad', good_accept, bad_accept)

      if (good_accept + bad_reject >= threshold and
            min(good_accept, bad_reject) > 0) or \
          (good_reject + bad_accept >= threshold and
            min(good_reject, bad_accept) > 0):
        return pred, cache


def find_largest_conflict_set(vectors):
  largest = 0
  chosen = None

  for _,g,b in vectors:
    if not g or not b: continue

    size = len(g) + len(b)
    if size > largest:
      largest = size
      chosen = (g,b)

  log = logger.getChild('find_largest_conflict_set')
  if chosen and log.isEnabledFor(logging.DEBUG):
    log.debug('\n  good: ' + pformat(chosen[0], indent=8, start_at=8) +
              '\n  bad:  ' + pformat(chosen[1], indent=8, start_at=8))

  return chosen

def sample_largest_conflict_set(vectors):
  chosen = find_largest_conflict_set(vectors)

  if chosen:
    g,b = chosen
    if len(g) + len(b) > CONFLICT_SET_CUTOFF:
      x = random.randrange(
            max(1, CONFLICT_SET_CUTOFF - len(b)),
            min(CONFLICT_SET_CUTOFF, len(g)+1))

      g = random.sample(g, x)
      b = random.sample(b, CONFLICT_SET_CUTOFF - x)
      assert len(g) + len(b) == CONFLICT_SET_CUTOFF
      chosen = (g,b)

    log = logger.getChild('sample_largest_conflict_set')
    if log.isEnabledFor(logging.DEBUG):
      log.debug('\n  good: ' + pformat(g, indent=8, start_at=8) +
                '\n  bad:  ' + pformat(b, indent=8, start_at=8))

  return chosen

find_conflict_set = sample_largest_conflict_set

def partition(feature, cache, cases):
  sats = []
  unsats = []

  for tc in cases:
    if test_feature(feature, tc, cache):
      sats.append(tc)
    else:
      unsats.append(tc)

  return sats, unsats

def extend_feature_vectors(vectors, feature, cache=None):
  if cache is None:
    cache = {}

  new_vectors = []
  for vector, good, bad in vectors:
    good_t, good_f = partition(feature, cache, good)
    bad_t, bad_f = partition(feature, cache, bad)

    if good_t or bad_t:
      new_vectors.append((vector + (True,), good_t, bad_t))
    if good_f or bad_f:
      new_vectors.append((vector + (False,), good_f, bad_f))

  return new_vectors

def clause_accepts(clause, vector):
  return any((l < 0 and not vector[l]) or (l >= 0 and vector[l]) for l in clause)

def consistent_clause(clause, vectors):
  return all(clause_accepts(clause, v) for v in vectors)

def learn_boolean(feature_count, goods, bads):
  log = logger.getChild('learn_bool')
  log.debug('called with %s features; vectors: %s good, %s bad', feature_count,
    len(goods), len(bads))

  clauses = []
  excluded_by = [] # for each clause, the bad vector ids it excludes
  excluding = collections.defaultdict(set) # n -> set of clauses excluding n vectors
  excludes = collections.defaultdict(list) # vector id -> list of clauses

  lits = range(-feature_count, feature_count)
  k = 0

  # generate clauses until all bad vectors are excluded
  while len(excludes) < len(bads):
    k += 1
    reporter.increase_clause_size()
    clauses.extend(c for c in itertools.combinations(lits, k)
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

def infer_precondition_by_examples(config, goods, bads,
    features=()):
  """Synthesize a precondition which accepts the good examples and
  rejects the bad examples.

  features is None or an initial list of features; additional features
  will be appended to this list.
  """
  log = logger.getChild('pie')

  features = list(features)

  log.info('Inferring: %s good, %s bad, %s features', len(goods),
    len(bads), len(features))

  feature_vectors = [((),goods,bads)]
  for f in features:
    feature_vectors = extend_feature_vectors(feature_vectors, f)

    reporter.accept_feature()
    if log.isEnabledFor(logging.DEBUG):
      log.debug('Feature Vectors\n  ' +
        pformat([(v,len(g),len(b)) for (v,g,b) in feature_vectors],
          indent=2))

  while True:
    # find a conflict set
    conflict = find_conflict_set(feature_vectors)
    if conflict is None:
      break

    f, cache = learn_feature(config, conflict[0], conflict[1])
    log.info('Feature %s: %s', len(features), f)

    features.append(f)

    feature_vectors = extend_feature_vectors(feature_vectors, f, cache)

    reporter.accept_feature()
    if log.isEnabledFor(logging.DEBUG):
      log.debug('Feature Vectors\n  ' +
        pformat([(v,len(g),len(b)) for (v,g,b) in feature_vectors],
          indent=2))

  good_vectors = []
  bad_vectors = []

  for vector, g, b in feature_vectors:
    assert not g or not b
    if g:
      good_vectors.append(vector)
    else:
      bad_vectors.append(vector)

  clauses = learn_boolean(len(features), good_vectors, bad_vectors)

  pre = mk_AndPred(
          mk_OrPred(
            negate_pred(features[l]) if l < 0 else features[l] for l in c)
          for c in clauses)

  return pre

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
    num_random, num_good, num_bad, strengthen=False):
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

    e = mk_and(safe + [mk_implies(premises, consequent)])
    log.debug('Query:\n%s', e)

    solver_bads = [tc
      for tc in itertools.islice(get_models(z3.Not(e), symbol_smts), num_bad)
      if not any(v is None for (_,v) in tc)]
      # NOTE: getting None as a value means we can't use it as a test-case,
      # but discarding them may lead to false positives

    log.debug('%s counter-examples', len(solver_bads))

    bads.extend(TestCase(type_vector, tc) for tc in solver_bads)
    reporter.test_cases(goods, bads)

    skip = set(tuple(v.as_long() for (_,v) in tc) for tc in solver_bads)


    if num_good > 0:
      input_smts = [smt.eval(t) for t in inputs]

      query = mk_and(premises + [mk_forall(input_smts, [e])])
      log.debug('Query\n%s', query)
      solver_goods = [tc for
        tc in itertools.islice(get_models(query, symbol_smts), num_good)
        if not any(v is None for (_,v) in tc)]

      log.debug('%s pro-examples', len(solver_goods))

      goods.extend(TestCase(type_vector, tc) for tc in solver_goods)
      skip.update(tuple(v.as_long() for (_,v) in tc) for tc in solver_goods)
      reporter.test_cases(goods, bads)

    filter = mk_and(premises) if premises else None

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

def infer_precondition(opt,
    features=(),
    random_cases=100,
    solver_good=10,
    solver_bad=10,
    strengthen=False,
    use_features=False):
  log = logger.getChild('infer')

  if log.isEnabledFor(logging.INFO):
    log.info('infer_precondtion invoked on %r (%s features,'
      '%s randoms, %s +solver, %s -solver',
      opt.name, 'No' if features is None else len(features),
      random_cases, solver_good, solver_bad)

  type_model = opt.abstract_type_model()
  type_vectors = list(exponential_sample(type_model.type_vectors()))

  symbols = []
  inputs = []
  reps = [None] * type_model.tyvars
  for t in L.subterms(opt.src):
    if isinstance(t, (L.Input, L.Instruction)):
      reps[typing.context[t]] = t
    if isinstance(t, L.Symbol):
      symbols.append(t)
    elif isinstance(t, L.Input):
      inputs.append(t)

  reps = [r for r in reps if r is not None]
  assert all(isinstance(t, (L.Input, L.Instruction)) for t in reps)

  goods, bads = make_test_cases(opt, symbols, inputs, type_vectors,
    random_cases, solver_good, solver_bad, strengthen)

  log.info('Initial test cases: %s good, %s bad', len(goods), len(bads))

  valid = not bads
  pre = None

  config = enumerator.Config(symbols, reps, type_model)

  if use_features:
    features = [t for t in L.subterms(opt.pre)
                    if isinstance(t, (L.Comparison, L.FunPred))]

  while not valid:
    reporter.begin_round()
    pre = infer_precondition_by_examples(config, goods, bads, features)

    if log.isEnabledFor(logging.INFO):
      log.info('Inferred precondition:\n  ' + pformat(pre, indent=2))

    valid = True

    for type_vector in type_model.type_vectors():
      reporter.test_precondition()
      smt = safety.Translator(type_vector)

      tgt_safe, premises, consequent = interpret_opt(smt, opt)  # cache this?

      log.debug('\ntgt_safe %s\npremises %s\nconsequent %s',
        tgt_safe, premises, consequent)


      pre_smt = smt(pre)
      pre_safe = pre_smt.safe
      pd = pre_smt.defined + pre_smt.nonpoison
      pd.append(pre_smt.value)

      log.debug('\npre_safe %s\npd %s', pre_safe, pd)

      if tgt_safe:
        pre_safe.append(mk_implies(pd, mk_and(tgt_safe)))

      premises.extend(pd)

      e = mk_implies(pre_safe + premises, consequent)
      log.debug('Validity check: %s', e)

      symbol_smts = [smt.eval(t) for t in symbols]
      counter_examples = list(itertools.islice(
        get_models(z3.Not(e), symbol_smts), solver_bad))

      log.info('counter-examples: %s', len(counter_examples))

      if counter_examples:
        valid = False
        bads.extend(TestCase(type_vector, tc) for tc in counter_examples)
        break

  return pre


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
    self.status.write('\r')
    self.status.write(' ' * self.width)
    self.status.write('\r')
    self.status.flush()

  def test_cases(self, good, bad):
    self.num_good_cases = len(good)
    self.num_bad_cases = len(bad)
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


def main():
  import argparse, sys, logging.config
  from alive import config, transform
  from alive.main import read_opt_files
  logging.config.dictConfig(config.logs)

  parser = argparse.ArgumentParser()
  parser.add_argument('--strengthen', action='store_true',
    help='Find a stronger precondition')
  parser.add_argument('--features', action='store_true',
    help='Take clauses from precondition as initial features')
  parser.add_argument('file', type=argparse.FileType('r'), nargs='*',
    default=[sys.stdin])

  args = parser.parse_args()

  for opt in read_opt_files(args.file):
    print '-----'
    print opt.format()
    set_reporter(Reporter())

    pre = infer_precondition(opt, strengthen=args.strengthen,
      use_features=args.features,
      random_cases=500)
    reporter.clear_message()

    opt.pre = pre
    print
    print opt.format()
    print '; rounds {0.round:,}\n; features in final round {0.features:,}\n' \
      '; total features generated {0.generated_features:,}'.format(reporter)

if __name__ == '__main__':
  main()
