import alive.language as L
from alive.parser import parse_transform, parse_opt_file
from alive import smtinterp
from alive import typing
from alive.z3util import mk_and, mk_or
from alive.util.pretty import pformat
import random
import itertools
import collections
import z3
import logging
import operator


def mk_implies(premises, consequent):
  if premises:
    return z3.Implies(mk_and(premises), consequent)

  return consequent

def incremental_check(vars, types, term):
  t = typing.TypeConstraints()
  
  for v in vars:
    t.specific(v, types[v])
  
  term.type_constraints(t)
  return t.type_models().next()  # Does it matter if there's more than one?


class Translator(smtinterp.SMTPoison):
  """Extension of SMTPoison noting undefined behavior in constant expressions.

  Note: presently, this will intermingle well-defined conditions for
  constant expressions with the definitional aspects of analysis predicates
  and expressions. Should we begin using those here, we will probably want to
  separate them.

  Note: SMTPoison is chosen arbitrarily.
  """
  pass

  # The long-term evolution here is probably to fold this stuff into
  # BaseSMTTranslator, possibly separating the constraints used for
  # must analysis from the well-defined conditions.
  #
  # In general, it is still unclear how to handle undefined behavior in
  # the precondition.
  
  # TODO: replace this with safety.Translator

smtinterp.eval.register(L.SDivCnxp, Translator,
  smtinterp.binop(operator.div,
    defined = lambda x,y: [y != 0, z3.Or(x != (1 << x.size()-1), y != -1)]))

smtinterp.eval.register(L.UDivCnxp, Translator,
  smtinterp.binop(z3.UDiv,
    defined = lambda x,y: [y != 0]))

smtinterp.eval.register(L.SRemCnxp, Translator,
  smtinterp.binop(operator.mod,
    defined = lambda x,y: [y != 0, z3.Or(x != (1 << x.size()-1), y != -1)]))

smtinterp.eval.register(L.URemCnxp, Translator,
  smtinterp.binop(z3.URem,
    defined = lambda x,y: [y != 0]))

smtinterp.eval.register(L.ShlCnxp, Translator,
  smtinterp.binop(operator.lshift,
    defined = lambda x,y: [z3.ULT(y, y.size())]))

smtinterp.eval.register(L.AShrCnxp, Translator,
  smtinterp.binop(operator.rshift,
    defined = lambda x,y: [z3.ULT(y, y.size())]))

smtinterp.eval.register(L.LShrCnxp, Translator,
  smtinterp.binop(z3.LShR,
    defined = lambda x,y: [z3.ULT(y, y.size())]))

@smtinterp.eval.register(L.LShrFunCnxp, Translator)
def _(term, smt):
  x = smt.eval(term._args[0])
  y = smt.eval(term._args[1])

  smt.add_defs(z3.ULT(y, y.size()))

  return z3.LShR(x,y)


binops = L.BinaryCnxp.codes.values()
#binops = [L.AddCnxp, L.SubCnxp, L.MulCnxp, L.ShlCnxp, L.LShrCnxp, L.AShrCnxp, L.AndCnxp, L.OrCnxp, L.XorCnxp]
unops = L.UnaryCnxp.codes.values()

# TODO: more expression forms
# TODO: filter by return type?
def enum_expr(size, symbols):
  """Generate pairs (expr, bool) containing expressions of a particular size
  using the given symbols.
  
  The bool is True if the expression contains a symbol.
  """
  if size < 1:
    return

  if size == 1:
    for s in symbols:
      yield s, True
    return

  if size == 2:
    yield L.Literal(0), False
    yield L.Literal(1), False

  size -= 1

  for lsize in xrange(1,size):
    for op in binops:
      for l,s1 in enum_expr(lsize, symbols):
        for r,s2 in enum_expr(size-lsize, symbols):
          yield op(l,r), s1 or s2

  # arguably redundant, since we will eventually generate 0-X and (0-1)^X
  for op in unops:
    for l,s in enum_expr(size, symbols):
      yield op(l),s


def enum_positive_predicates(size, symbols):
  lsize_max = (size-1)/2
  for lsize in xrange(1,lsize_max+1):
    for l,s1 in enum_expr(lsize, symbols):
      for r,s2 in enum_expr(size-lsize-1, symbols):
        if not (s1 or s2): continue

        for cmp in ['eq', 'slt', 'ult']: # sufficient?
          yield L.Comparison(cmp, l, r)

  for e,s in enum_expr(size-2, symbols):
    if not s: continue

    yield L.IntMinPred(e)

def enum_predicates(size, symbols):
  return itertools.chain(enum_positive_predicates(size, symbols),
    itertools.imap(L.NotPred, enum_positive_predicates(size-1, symbols)))

def get_vars(opt):
  return tuple(v for v in L.subterms(opt.src) if isinstance(v, L.Input))

def get_symbols(opt):
  return tuple(v for v in L.subterms(opt.src) if isinstance(v, L.Symbol))

def random_value(ty):
  """Return a random value for an Alive type."""
  
  assert isinstance(ty, L.IntType)
  
  return z3.BitVecVal(random.randrange(0, 2**ty.width), ty.width)


def random_test_case(types):
  """Return random Z3 values for a given tuple of Z3 variable/Alive type pairs."""

  return tuple(random_value(ty) for ty in types)


def make_test_cases(n, e, var_types, var_smts, filter=None):
  goods = []
  bads = []
  for _ in xrange(n):
    tc = tuple(itertools.izip(var_smts, random_test_case(var_types)))
    if filter:
      s = z3.Solver()
      s.add(z3.substitute(filter, *tc))
      res = s.check()
      if res == z3.unsat:
        continue
      if res == z3.unknown:
        logging.warn('Unknown result for filter %s', tc)
        continue

    s = z3.Solver()
    s.add(z3.Not(z3.substitute(e, *tc)))
    res = s.check()
    if res == z3.unsat:
      goods.append(tc)
    elif res == z3.sat:
      bads.append(tc)
    else:
      logging.warn('Unknown result for tc %s', tc)

  return goods, bads


def test_feature(pred, test_case):
  e = z3.simplify(z3.substitute(pred, *test_case))
  assert z3.is_bool(e)
  return z3.is_true(e)

def learn_feature(symbols, types, good, bad):
  log = logging.getLogger('infer.learn_feature')
  for size in itertools.count(3):
    log.info('Checking size %s', size)
    for pred in enum_predicates(size, symbols):
      log.debug('Checking %s', pred)
      
      pred_types = incremental_check(symbols, types, pred)
      #smt = smtinterp.SMTPoison(pred_types)
      #pred_smt = smt.eval(pred)
      smt = Translator(pred_types)
      pv,pd,_,_ = smt(pred)
      pd.append(pv)
      pred_smt = mk_and(pd)
      log.debug('SMT translation %s', pred_smt)

      if all(test_feature(pred_smt, g) for g in good) and \
          all(not test_feature(pred_smt, b) for b in bad):
        return pred, pred_smt

CONFLICT_SET_CUTOFF = 16

def find_conflict_set(vectors):
  """Return a set of good and bad test inputs with the same feature vector.
  
  Return None if no such set exists.
  """
  
  largest = 0
  chosen = None
  
  for (g,b) in vectors.itervalues():
    size = min(len(g), len(b))
    if size > largest:
      largest = size
      chosen = (g,b)

  if chosen:
    # This may need to be rethought. The paper recommends a conflict size of 16,
    # but doesn't specify how it should be divided between good and bad inputs.
    g,b = chosen
    if len(g) + len(b) > CONFLICT_SET_CUTOFF:
      x = random.randrange(max(1, CONFLICT_SET_CUTOFF - len(b)), min(CONFLICT_SET_CUTOFF, len(g)+1))
      
      g = random.sample(g, x)
      b = random.sample(b, CONFLICT_SET_CUTOFF - x)
      assert len(g) + len(b) == CONFLICT_SET_CUTOFF
      chosen = (g,b)

  return chosen

def partition(feature, cases):
  sats = []
  unsats = []

  for tc in cases:
    if test_feature(feature, tc):
      sats.append(tc)
    else:
      unsats.append(tc)
  
  return sats, unsats

def extend_feature_vectors(vectors, feature):
  new_vectors = {}
  for vector, (good,bad) in vectors.iteritems():
    good_t, good_f = partition(feature, good)
    bad_t, bad_f = partition(feature, bad)

    if good_t or bad_t:
      new_vectors[vector + (True,)] = (good_t, bad_t)
    if good_f or bad_f:
      new_vectors[vector + (False,)] = (good_f, bad_f)

  return new_vectors

def extend_feature_vectors_with_ast(vectors, feature, symbols, types):
  assert isinstance(feature, L.Predicate)
  types = incremental_check(symbols, types, feature)
  smt = smtinterp.SMTPoison(types)
  f_smt = smt.eval(feature)

  return extend_feature_vectors(vectors, f_smt)

def generate_clauses(literals, k):
  """Generate disjunctions of literals up to size k"""

  for n in xrange(k):
    for lits in itertools.combinations(xrange(-literals, literals), n+1):
      yield lits

def clause_accepts(clause, vector):
  return any((l < 0 and not vector[l]) or (l >= 0 and vector[l]) for l in clause)

def consistent_clause(clause, vectors):
  return all(clause_accepts(clause, v) for v in vectors)

def learn_boolean(feature_count, goods, bads):
  log = logging.getLogger('infer.learn_bool')
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
    log.debug('excluding %s: %s', s, cs)

    while cs:
      log.debug('%s clauses excluding %s', len(cs), s)
      
      # select arbitrary clause
      # (better to select the smallest clause?)
      c = cs.pop()
      
      cover.append(clauses[c])

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

def check_expr(expr, vars):
  s = z3.Solver()
  s.add(expr)
  res = s.check()

  if res == z3.sat:
    model = s.model()
    return tuple((v, model[v]) for v in vars)

  if res == z3.unknown:
    raise Exception('Solver returned unknown: ' + s.reason_unknown())

  return None

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

def infer_precondition(opt, type_model=None,
    features=None,
    random_cases=100,
    solver_good=10,
    solver_bad=10):
  log = logging.getLogger('infer.infer')

  if type_model is None:
    type_model = opt.type_models().next()

  symbols = tuple(t for t in L.subterms(opt.src) if isinstance(t, L.Symbol))
  symbol_types = tuple(type_model[t] for t in symbols)

  smt = smtinterp.SMTPoison(type_model)
  
  symbol_smts = tuple(smt.eval(t) for t in symbols)
  
  sv,sd,sp,sq = smt(opt.src)
  if sq:
    raise Exception('quantified variables in opt {!r}'.format(opt.name))

  tv,td,tp,_ = smt(opt.tgt)

  e = mk_implies(sd+sp, mk_and(td+tp+[sv==tv]))

#   bad = check_expr(z3.Not(e), symbol_smts)
#   if bad is None: return None
#   
#   log.debug('basic counter-example: %s', bad)

  solver_bad = max(solver_bad, 1)

  solver_bads = list(itertools.islice(
    get_models(z3.Not(e), symbol_smts),
    solver_bad))
  if not solver_bads: return None

  log.debug('initial counter-examples: %s', solver_bads)

  if solver_good > 0:
    inputs = tuple(smt.eval(t) for t in L.subterms(opt.src) 
      if isinstance(t, L.Input) and not isinstance(t, L.Symbol))

    query = mk_and(sd+sp+[z3.ForAll(inputs, e)])
    log.debug('query for goods: %s', query)

    solver_goods = list(itertools.islice(
      get_models(query, symbol_smts), solver_good))

    log.debug('initial examples: %s', solver_goods)
  else:
    solver_goods = []

  psi = z3.And(sd+sp) if sd or sp else None
  goods, bads = make_test_cases(random_cases, e, symbol_types, symbol_smts,
    filter=psi)

  goods.extend(solver_goods)
  bads.extend(solver_bads)

  assert goods

  log.debug('Test inputs: %s good, %s bad', len(goods), len(bads))

  while True:
    pre = infer_precondition_by_examples(symbols, type_model, goods, bads, features)
    log.info('Inferred precondition %s', pre)

    types = incremental_check(symbols, type_model, pre)
    smt2 = smtinterp.SMTPoison(types)
    pb,pd,_,_ = smt2(pre)
    # Should this use Translator?
    # Currently, we don't generate any terms which populate pd
    # (although they may be provided as initial features)

    # TODO: check whether precondition is satisfiable

    e = mk_implies(sd+sp+pd+[pb], mk_and(td+tp+[sv==tv]))
    log.debug('Checking expression %s', e)

    solver_bads = list(itertools.islice(
      get_models(z3.Not(e), symbol_smts), solver_bad))
    if not solver_bads:
      return pre

    log.debug('Adding counter-examples %s', solver_bads)
    bads.extend(solver_bads)
    
    # TODO: check for too-strong precondition?


def infer_precondition_by_examples(symbols, type_model, goods, bads,
    features=None):
  """Synthesize a precondition which accepts the good examples and
  rejects the bad examples.
  
  features is None or an initial list of features; additional features
  will be appended to this list.
  """
  log = logging.getLogger('infer.pie')
  if features is None:
    features = []

  feature_vectors = {(): (goods, bads)}
  for f in features:
    feature_vectors = extend_feature_vectors_with_ast(feature_vectors, f, symbols, type_model)
    if log.isEnabledFor(logging.DEBUG):
      log.debug('Feature Vectors\n  ' + 
        pformat([(v,len(g),len(b)) for (v,(g,b)) in feature_vectors.iteritems()]
        , indent=2))

  while True:
    # find a conflict set
    conflicts = find_conflict_set(feature_vectors)
    if conflicts is None:
      break
    log.debug('Conflict sets\n  GOOD %s\n  BAD %s', conflicts[0], conflicts[1])

    f, f_smt = learn_feature(symbols, type_model, conflicts[0], conflicts[1])
    log.info('Learned feature: %s', f)

    features.append(f)
    
    feature_vectors = extend_feature_vectors(feature_vectors, f_smt)

    if log.isEnabledFor(logging.DEBUG):
      log.debug('Feature Vectors\n  ' + 
        pformat([(v,len(g),len(b)) for (v,(g,b)) in feature_vectors.iteritems()]
        , indent=2))

  # partition feature vectors
  good_vectors = []
  bad_vectors = []
  for vector, (g,b) in feature_vectors.iteritems():
    assert not g or not b
    if g:
      good_vectors.append(vector)
    else:
      bad_vectors.append(vector)

  clauses = learn_boolean(len(features), good_vectors, bad_vectors)

  pre = L.AndPred(*(L.OrPred(*(L.NotPred(features[l]) if l < 0 else features[l] for l in c))
                        for c in clauses))

  return pre

MINIMUM_CONFLICT_SET = 16

def alt_learn_feature(symbols, types, good, bad):
  """Return a feature which separates a subset of the test inputs.
  """
  log = logging.getLogger('infer.learn_feature')
  for size in itertools.count(3):
    log.info('Checking size %s', size)
    for pred in enum_predicates(size, symbols):
      log.debug('Checking %s', pred)
      
      pred_types = incremental_check(symbols, types, pred)
      smt = smtinterp.SMTPoison(pred_types)
      pred_smt = smt.eval(pred)
      
      accepts = sum(1 for g in good if test_feature(pred_smt, g))
      rejects = sum(1 for b in bad if not test_feature(pred_smt, b))

      if (accepts + rejects >= MINIMUM_CONFLICT_SET and min(accepts,rejects) > 0) or \
          (accepts == len(good) and rejects == len(bad)):
        return pred, pred_smt

def alt_find_conflict_set(vectors):
  """Return a set of good and bad test inputs with the same feature vector.
  
  Return None if no such set exists.
  """
  
  largest = 0
  chosen = None
  
  for (g,b) in vectors.itervalues():
    size = min(len(g), len(b))
    if size > largest:
      largest = size
      chosen = (g,b)

  return chosen


def alt_infer_precondition_by_examples(symbols, type_model, goods, bads,
    features=None):
  log = logging.getLogger('infer.pie')
  if features is None:
    features = []

  feature_vectors = {(): (goods, bads)}
  for f in features:
    feature_vectors = extend_feature_vectors_with_ast(feature_vectors, f, symbols, type_model)
    if log.isEnabledFor(logging.DEBUG):
      log.debug('Feature Vectors\n  ' +
        pformat([(v,len(g),len(b)) for (v,(g,b)) in feature_vectors.iteritems()]
        , indent=2))

  while True:
    # find a conflict set
    conflicts = alt_find_conflict_set(feature_vectors)
    if conflicts is None:
      break
    log.debug('Conflict sets\n  GOOD %s\n  BAD %s', conflicts[0], conflicts[1])

    f, f_smt = alt_learn_feature(symbols, type_model, conflicts[0], conflicts[1])
    log.info('Learned feature: %s', f)

    features.append(f)
    
    feature_vectors = extend_feature_vectors(feature_vectors, f_smt)

    if log.isEnabledFor(logging.DEBUG):
      log.debug('Feature Vectors\n  ' + pformat(feature_vectors, indent=2))

  # partition feature vectors
  good_vectors = []
  bad_vectors = []
  for vector, (g,b) in feature_vectors.iteritems():
    assert not g or not b
    if g:
      good_vectors.append(vector)
    else:
      bad_vectors.append(vector)

  clauses = learn_boolean(len(features), good_vectors, bad_vectors)

  pre = L.AndPred(*(L.OrPred(*(L.NotPred(features[l]) if l < 0 else features[l] for l in c))
                        for c in clauses))

  return pre


# 
# # C1 == C2+C3
# test = '''Pre: C1 == C2+C3
# %add = add %X, C3
# %cmp1 = icmp ult %add, C1
# %cmp2 = icmp eq %X, C2
# %r = or %cmp1, %cmp2
#   =>
# %r = icmp ule %add, C1'''
# 
# opt = parse_transform(test)
# types = opt.type_models().next()
# 

def main():
  import sys, alive.config, logging.config
  logging.config.dictConfig(alive.config.logs)
  logging.getLogger('infer').setLevel(logging.INFO)
  
  if sys.stdin.isatty():
    print '[Reading from keyboard...]'
  
  # TODO: provide an actual interface
  opts = parse_opt_file(sys.stdin.read())

  for opt in opts:
    print '-------\nChecking', opt.name
    
    pre = infer_precondition(opt)
    
    opt.pre = pre
    print opt.format()

if __name__ == '__main__':
  main()