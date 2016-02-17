#! /usr/bin/env python

import logging, logging.config, argparse, sys
import config
from parser import parse_opt_file

def check_opt(opt, chatty=True):
  if chatty:
    print '----------'
    print opt.format()
    print
  
  proofs = 0
  for m in opt.type_models():
    r = opt.check_refinement(m)
    if r:
#       logging.warning('Optimization %r incorrect: %s', opt.name, r)
      if chatty:
        print
        r.write()
        print '\nOptimization is incorrect'
      return False
    
    proofs += 1
    if chatty and sys.stdout.isatty():
      sys.stdout.write('\rDone: ' + str(proofs))
      sys.stdout.flush()
  
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
  parser.add_argument('file', type=argparse.FileType('r'), nargs='*',
    default=[sys.stdin],
    help='file(s) containing Alive optimizations (stdin by default')

  args = parser.parse_args()

  chatty = not args.quiet
  tested = 0
  failed = 0

  for f in args.file:
    if f.isatty():
      sys.stderr.write('[Reading from terminal...]\n')

    opts = parse_opt_file(f.read())
    
    for opt in opts:
      tested += 1
      if not check_opt(opt, chatty):
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
