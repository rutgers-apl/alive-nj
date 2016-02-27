#! /usr/bin/env python

import logging, logging.config, argparse, sys
import os
import os.path
import itertools
from . import config
from . import typing
from . import refinement
from . import smtinterp
from .parser import parse_opt_file

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
    self.opt = opt
    self.checks = 0

    if not self.quiet:
      self.clear()
      print '----------'
      print opt.format()
      print
    
    self.write_status()

  def add_proof(self):
    self.checks += 1
    self.write_status()

  def end_opt(self):
    if self.checks == 0:
      raise typing.Error('Unsatisfiable type constraints')

    self.tested += 1
    if not self.quiet:
      self.clear()
      print 'Done:', self.checks
      print 'Optimization is correct'

  def fail_opt(self, error):
    self.tested += 1
    self.failed += 1
    self.failures.append(self.opt.name)

    # report error
    self.clear()
    if self.quiet:
      print '----------'
      print self.opt.format()
      print

    if isinstance(error, refinement.Error):
      error.write()
    else:
      print 'ERROR:', error

    print

    if not self.persist:
      self.final_status()
      exit(-1)

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


def read_opt_files(files):
  for f in files:
    if f.isatty():
      sys.stderr.write('[Reading from terminal...]\n')

    for n,opt in itertools.izip(itertools.count(1), parse_opt_file(f.read())):
      if opt.name:
        opt.name = '{}#{}:{}'.format(f.name, n, opt.name)
      else:
        opt.name = '{}#{}'.format(f.name, n, opt.name)
      yield opt


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
    help='(advanced) pick class for SMT translation')
  parser.add_argument('file', type=argparse.FileType('r'), nargs='*',
    default=[sys.stdin],
    help='file(s) containing Alive optimizations (stdin by default)')

  args = parser.parse_args()

  if config.bench_dir:
    if not os.path.isdir(config.bench_dir):
      print 'ERROR: Benchmark directory', config.bench_dir, 'does not exist'
      exit(-1)

  if args.translator not in smtinterp.SMTTranslator.registry:
    print 'ERROR: Unknown translator:', args.translator
    exit(-1)

  status_reporter = StatusReporter(args.quiet, args.persist)

  for opt in read_opt_files(args.file):
    try:
      status_reporter.begin_opt(opt)

      for m in opt.type_models():
        refinement.check(opt, m, args.translator)
        status_reporter.add_proof()

      status_reporter.end_opt()

    except (refinement.Error, typing.Error) as e:
      status_reporter.fail_opt(e)

  status_reporter.final_status()
