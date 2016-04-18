'''
Central location for global configuration parameters.
'''
import sys

# continue after failure
persist = False

# minimal output
quiet = False

# allow poison->undefined behavior
poison_undef = True

# benchmark directory (if None, no benchmarks will be printed)
bench_dir = None

# output benchmark if solve time exceeds this threshold (in seconds)
bench_threshold = 0.0

# timeout for Z3, in ms. None for no timeout
timeout = 5*60*1000

# which class to use for translation to SMT (by lowercased name)
translator = 'smtundef'

# logging configuration. see logging.config docs for schema
logs = {
  'version': 1,
  'disable_existing_loggers': False,
  
  'formatters': {
    'default': {
      'format': '%(asctime)s %(levelname)-8s %(name)s - %(message)s',
    },
    
    'brief': {
      'format': '%(message)s'
    }
  },
  
  'handlers': {
    'default': {
      'class': 'logging.handlers.RotatingFileHandler',
      'formatter': 'default',
      'filename': 'log/alive.log',
      'maxBytes': 1024000,
      'backupCount': 5,
    },
    
    'warnings': {
      'class': 'logging.StreamHandler',
      'formatter': 'brief',
      'level': 'WARNING',
      'stream': sys.stderr,
    }
  },
  
  'root': {
    'level': 'WARNING',
    'handlers': ['default', 'warnings']
  },
  
  'loggers': {
#     'alive.typing': { 'level': 'DEBUG' },
#     'alive.transform': { 'level': 'DEBUG' },
#     'alive.smtinterp': { 'level': 'DEBUG'},
#     'alive.refinement': { 'level': 'DEBUG'},
  }
}
