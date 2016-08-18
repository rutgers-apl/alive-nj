#!/usr/bin/env python

from alive.precondition.inference import main
import logging, sys

try:
  main()
except KeyboardInterrupt:
  sys.stderr.write('\n[Keyboard interrupt]\n')
except Exception, e:
  logging.exception(e)
  raise
