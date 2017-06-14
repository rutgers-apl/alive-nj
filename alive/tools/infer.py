import argparse, sys, os, logging, logging.config
import alive.precondition.inference as I
import alive.language as L
from alive import config, error
from alive.formatter import Formatted, format_parts
from alive.tools.common import read_opt_files, match_name, all_of
from alive.util.args import NegatableFlag


def main(
    incompletes = True,
    assume_pre = False,
    pre_features = False,
    strengthen = False,
    weakest = True,
    first_only = False,
    use_assumptions = True,
    use_features = True,
    echo = True,
    strategy = 'largest',
    encoding = config.encoding,
    random_examples = 50,
    solver_positives = 10,
    solver_negatives = 10,
    filter = None,
  ):
  logging.config.dictConfig(config.logs)

  parser = argparse.ArgumentParser(
    description='Infer preconditions for each provided optimization'
  )

  interp_group = parser.add_argument_group('input interpetation')
  interp_group.add_argument('-a', '--assume-pre', action=NegatableFlag,
    default=assume_pre,
    help='Treat precondition as an assumption')
  interp_group.add_argument('-f', '--pre-features', action=NegatableFlag,
    default=pre_features,
    help='Take clauses from precondition as initial features')
  interp_group.add_argument('--assumptions', action=NegatableFlag,
    default=use_assumptions,
    help='Use assumptions in Assume: headers')
  interp_group.add_argument('--features', action=NegatableFlag,
    default=use_features,
    help='Use features provided in Feature: headers')
  interp_group.add_argument('--encoding', action='store',
    default=encoding,
    help='Specify variant of Alive/LLVM semantics')

  example_group = parser.add_argument_group('example generation')
  example_group.add_argument('-p', '--positives', type=int, metavar='N',
    default=solver_positives,
    help='Number of positive examples to obtain with queries')
  example_group.add_argument('-n', '--negatives', type=int, metavar='N',
    default=solver_negatives,
    help='Number of negative examples to obtain with queries')
  example_group.add_argument('-r', '--randoms', type=int, metavar='N',
    default=random_examples,
    help='Number of randomly-chosen examples, per type assignment')

  infer_group = parser.add_argument_group('inference methodology')
  infer_group.add_argument('-i', '--incompletes', action=NegatableFlag,
    default=incompletes,
    help='Report too-strong preconditions during inference')
  infer_group.add_argument('--strengthen', action=NegatableFlag,
    default=strengthen,
    help='Find a stronger precondition')
  infer_group.add_argument('--weakest', action=NegatableFlag,
    default=weakest,
    help='Ensure precondition accepts all valid instances')
  infer_group.add_argument('--first-only', action=NegatableFlag,
    default=first_only,
    help='Stop after the first valid precondition')
  infer_group.add_argument('--strategy', action='store',
    default=strategy,
    choices=cs_strategies,
    help='Method for choosing conflict set')

  parser.add_argument('--echo', action=NegatableFlag,
    default=echo,
    help='Print the input optimizations before inferring')

  parser.add_argument('-m', '--match', action='store', metavar='PATTERN',
    help='Ignore optimizations which do not match this regular expression')
  parser.add_argument('file', type=argparse.FileType('r'), nargs='*',
    default=[sys.stdin])

  args = parser.parse_args()

  try:
    I.set_encoding(args.encoding)


    for opt,features in read_opt_files(args.file,
        filter = all_of(match_name(args.match), filter),
        extended_results=True):
      print '; -----'

      assumes = []
      if args.assumptions:
        assumes += opt.asm
      if args.assume_pre:
        assumes += opt.pre

      if not args.features:
        features = []
      if args.pre_features and opt.pre:
        features.extend(t for p in opt.pre for t in L.subterms(p)
                          if isinstance(t, (L.Comparison, L.FunPred)))

      if args.echo:
        hds = [('Assume:', t) for t in assumes]
        hds.extend(('Pre:', t) for t in opt.pre)
        hds.extend(('Feature:', t) for t in features)
        print Formatted(format_parts(opt.name, hds, opt.src, opt.tgt))

      I.set_reporter(Reporter())

      pres = I.infer_precondition(opt,
        strengthen = args.strengthen,
        weakest = args.weakest,
        features = features,
        assumptions = assumes,
        random_cases = args.randoms,
        solver_good = args.positives,
        solver_bad = args.negatives,
        incompletes = args.incompletes,
        conflict_set = cs_strategies[args.strategy])

      if args.first_only:
        pres = itertools.islice(pres, 1)

      try:
        for pre, coverage, ifeatures in pres:
          I.reporter.clear_message()

          hds = [('Feature:', t) for t in ifeatures] + \
            [('Assume:', t) for t in assumes] + \
            [('Pre:', pre)] if pre else []

          print
          print Formatted(format_parts(opt.name,hds,opt.src,opt.tgt))
          print '''; positive examples {1:,} of {0.num_good_cases:,}
; negative examples {0.num_bad_cases:,}
; accepted features {0.features:,}
; total features tested {0.generated_features:,}'''.format(I.reporter,coverage)
          sys.stdout.flush()

        if args.weakest:
          I.reporter.clear_message()
          print '; precondition is complete'

      except I.Failure as e:
        I.reporter.clear_message()
        print '; FAILURE:', e

  except KeyboardInterrupt:
    sys.stderr.write('\n[Keyboard interrupt]\n')
    exit(130)
  except error.Error as e:
    print 'ERROR:', e
    exit(1)
  except Exception as e:
    logging.exception('Uncaught exception: %s', e)
    sys.stderr.write('\nERROR: {}\n'.format(e))
    exit(1)
  finally:
    logging.shutdown()


cs_strategies = {
  'largest': I.find_largest_conflict_set,
  'smallest': I.find_smallest_conflict_set,
  'maxpos': I.find_most_positive_conflict_set,
  'minneg': I.find_least_negative_conflict_set,
}


class Reporter(object):
  _fmt_cases = 'Adding test cases: {0.num_good_cases:,}/{0.num_bad_cases:,}'
  _fmt_features = 'Considered {0.generated_features:5,} Accepted {0.features:2}'
  _fmt_cnf = 'Adding {0.k}-CNF clauses of {0.features} features'
  _fmt_clauses = 'Selected {0.clauses} clauses of {0.features} features'
  _fmt_proofs = 'Testing: {0.proofs:2} proofs'

  def __init__(self):
    self.num_good_cases = 0
    self.num_bad_cases = 0
    self.generated_features = 0
    self.features = 0
    self.k = 0
    self.clauses = 0
    self.proofs = 0
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

  def enter_boolean_learner(self):
    self.k = 0
    self.clauses = 0

  def increase_clause_size(self):
    self.k += 1
    if self.status:
      self.write_message(self._fmt_cnf.format(self))

  def add_clause(self):
    self.clauses += 1
    if self.status:
      self.write_message(self._fmt_clauses.format(self))

  def begin_solving(self):
    self.proofs = 0

  def test_precondition(self):
    if self.status:
      self.write_message(self._fmt_proofs.format(self))

    self.proofs += 1



if __name__ == '__main__':
  main()
