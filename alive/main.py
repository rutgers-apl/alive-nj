#! /usr/bin/env python

import logging, logging.config, argparse, sys
import os
import os.path
import itertools
import z3
from . import config
from . import error
from . import typing
from . import refinement
from . import smtinterp
from .parser import read_opt_files

class StatusReporter(object):
  _fmt         = '{0.tested} Tested. Done {0.checks:2} for {0.opt.name!r}'
  _fmt_persist = '{0.tested} Tested. {0.failed} Failed. Done {0.checks:2} for {0.opt.name!r}'
  _fmt_final   = '{0.tested} Tested. {0.failed} Failed.'

  def __init__(self, quiet, persist):
    self.quiet = quiet
    self.persist = persist
    self.tested = 0
    self.failed = 0
    self.failures = []
    self.width = int(os.environ.get('COLUMNS', 80))
    self.fmt = self._fmt_persist if persist else self._fmt

    if sys.stdout.isatty():
      self.status = sys.stdout
      self.stdstatus = True
    elif sys.stderr.isatty():
      self.status = sys.stderr
      self.stdstatus = False
    else:
      self.status = None
      self.stdstatus = False

  def begin_opt(self, opt):
    logging.info('Checking opt %s', opt.name)
    self.opt = opt
    self.checks = 0

    if not self.quiet:
      self.clear()
      print '----------'
      #print opt.format()
      opt.format().write_to(sys.stdout, width=self.width)
      print

    self.write_status()

  def add_proof(self):
    self.checks += 1
    self.write_status()

  def end_opt(self):
    if self.checks == 0:
      raise typing.Error('Unsatisfiable type constraints')

    logging.info('Passed %s checks', self.checks)
    self.tested += 1
    if not self.quiet:
      self.clear()
      print 'Done:', self.checks
      print 'Optimization is correct'

  def fail_opt(self, error):
    logging.info('Verification failed: %s', error)
    self.tested += 1
    self.failed += 1
    self.failures.append(self.opt.name)

    # report error
    self.clear()
    if self.quiet:
      print '----------'
      self.opt.format().write_to(sys.stdout, width=self.width)
      print

    print 'ERROR:', error
    sys.stdout.flush()
    print

    if not self.persist:
      self.final_status()
      exit(1)

  def clear(self):
    if self.stdstatus:
      self.status.write('\r')
      self.status.write(' ' * self.width)
      self.status.write('\r')

  def write_status(self):
    if self.status:
      status = self.fmt.format(self)
      self.status.write('\r')
      self.status.write(status[0:self.width])
      self.status.write(' ' * (self.width-len(status)))
      self.status.flush()

  def final_status(self):
    if not self.status:
      return

    if not self.persist and self.stdstatus and (not self.quiet or self.failed):
      self.clear()
      return

    status = self._fmt_final.format(self)
    self.status.write('\r')
    self.status.write(status[0:self.width])
    self.status.write(' ' * (self.width - len(status)))
    self.status.flush()

    if self.persist and self.failed:
      self.status.write('\n\nFailed:\n')
      for n in self.failures:
        self.status.write('  ')
        self.status.write(n)
        self.status.write('\n')


rounding_modes = {
  'rne': z3.RNE,
  'rna': z3.RNA,
  'rtp': z3.RTP,
  'rtz': z3.RTZ,
  'rtn': z3.RTN,
}

def verify_opts(opts, quiet=config.quiet, persist=config.persist,
    translator=config.translator):
  """Check refinement of each opt in iterable."""

  status_reporter = StatusReporter(quiet, persist)

  for opt in opts:
    try:
      status_reporter.begin_opt(opt)

      for m in opt.type_models():
        refinement.check(opt, m, translator)
        status_reporter.add_proof()

      status_reporter.end_opt()

    except (refinement.Error, typing.Error) as e:
      status_reporter.fail_opt(e)

  status_reporter.final_status()

def main():
  logging.config.dictConfig(config.logs)

  parser = argparse.ArgumentParser()
  parser.add_argument('--persist', action='store_true',
    default=config.persist,
    help='continue processing opts after verification failures')
  parser.add_argument('--quiet', action='store_true',
    default=config.quiet,
    help='only print number of tested and unverified opts')
  parser.add_argument('--translator', action='store',
    default=config.translator,
    # choices=smtinterp.SMTTranslator.registry,
    help='(advanced) pick class for SMT translation')
  parser.add_argument('-r', '--rounding-mode', action='store',
    choices=rounding_modes,
    help='rounding mode for arithmetic')
  parser.add_argument('--bench-dir', action='store',
    help='generate SMT2 benchmarks in this directory')
  parser.add_argument('--bench-threshold', action='store', type=float,
    help='minimum solve time (s) needed to trigger benchmark generation')
  parser.add_argument('file', type=argparse.FileType('r'), nargs='*',
    default=[sys.stdin],
    help='file(s) containing Alive optimizations (stdin by default)')

  args = parser.parse_args()

  if args.bench_dir:
    config.bench_dir = args.bench_dir

  if args.bench_threshold:
    config.bench_threshold = args.bench_threshold

  if config.bench_dir:
    if not os.path.isdir(config.bench_dir):
      print 'ERROR: Benchmark directory', config.bench_dir, 'does not exist'
      exit(1)

  if args.translator not in smtinterp.SMTTranslator.registry:
    print 'ERROR: Unknown translator:', args.translator
    exit(1)

  if args.rounding_mode:
    z3.set_default_rounding_mode(rounding_modes[args.rounding_mode]())

  try:
    verify_opts(read_opt_files(args.file), args.quiet, args.persist,
      args.translator)
  except error.Error as e:
    print 'ERROR:', e
    exit(1)
  except KeyboardInterrupt:
    sys.stderr.write('\n[Keyboard interrupt]\n')
    exit(130)
  except Exception as e:
    logging.exception('Uncaught exception: %s', e)
    sys.stderr.write('\nERROR: {}\n'.format(e))
    exit(1)
  finally:
    logging.shutdown()
