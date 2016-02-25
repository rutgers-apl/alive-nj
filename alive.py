#! /usr/bin/env python

import logging, logging.config, argparse, sys
import os.path
import config
import typing
from refinement import check_refinement
from parser import parse_opt_file

def check_opt(opt, chatty=True, trns=config.translator):
  if chatty:
    print '----------'
    print opt.format()
    print
  
  proofs = 0
  for m in opt.type_models():
    r = check_refinement(opt,m,trns)
    if r:
      if chatty:
        print
        r.write()
        print '\nOptimization is incorrect'
      return False
    
    proofs += 1
    if chatty and sys.stdout.isatty():
      sys.stdout.write('\rDone: ' + str(proofs))
      sys.stdout.flush()
  
  if proofs == 0:
    raise typing.Error('Unsatisfiable type constraints')

  if chatty:
    print '\nOptimization is correct'

  return True

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

  chatty = not args.quiet
  tested = 0
  failed = 0

  if config.bench_dir:
    if not os.path.isdir(config.bench_dir):
      print 'Benchmark directory', config.bench_dir, 'does not exist'
      exit(-1)

  for f in args.file:
    if f.isatty():
      sys.stderr.write('[Reading from terminal...]\n')

    opts = parse_opt_file(f.read())
    
    for opt in opts:
      tested += 1
      try:
        valid = check_opt(opt, chatty, args.translator)
      except typing.Error, e:
        print 'ERROR:', e
        if args.persist:
          valid = False
        else:
          exit(-1)

      if not valid:
        failed += 1
        if not args.persist:
          exit(-1)
      if not chatty and sys.stdout.isatty():
        sys.stdout.write('\rOpts tested: {}; Failures: {}'.format(
          tested, failed))
        sys.stdout.flush()

  if chatty or not sys.stdout.isatty():
    print 'Opts tested: {}; Failures: {}'.format(tested, failed)
  else:
    print

if __name__ == '__main__':
  try:
    main()
  except KeyboardInterrupt:
    sys.stderr.write('\n[Keyboard interrupt]\n')
  except Exception, e:
    logging.exception(e)
    raise
