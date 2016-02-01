#! /usr/bin/env python

from parser import parse_opt_file
import logging, argparse, sys

def check_opt(opt):
  print '----------'
  print opt.format()
  print
  
  proofs = 0
  for m in opt.z3_models():
    r = opt.check_refinement(m)
    if r:
      print r
      exit(-1)
    
    proofs += 1
    sys.stdout.write('\rProofs: ' + str(proofs))
    sys.stdout.flush()
  
  print

def main():
  parser = argparse.ArgumentParser()
  parser.add_argument('file', type=argparse.FileType('r'), nargs='*',
    default=[sys.stdin],
    help='file(s) containing Alive optimizations (stdin by default')

  args = parser.parse_args()
  
  for f in args.file:
    if f.isatty():
      sys.stderr.write('[Reading from terminal...]\n')

    opts = parse_opt_file(f.read())
    
    for opt in opts:
      check_opt(opt)

if __name__ == '__main__':
  logging.basicConfig()
  try:
    main()
  except KeyboardInterrupt:
    print '\nExiting\n'
