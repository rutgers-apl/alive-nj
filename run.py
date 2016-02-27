#!/usr/bin/env python

from alive.main import main
import logging

try:
  main()
except KeyboardInterrupt:
  sys.stderr.write('\n[Keyboard interrupt]\n')
except Exception, e:
  logging.exception(e)
  raise
