'''
Central location for global configuration parameters.
'''
import sys

# continue after failure
persist = False

# minimal output
quiet = False

# logging configuration. see logging.config docs for schema
logs = {
  'version': 1,
  'disable_existing_loggers': False,
  
  'formatters': {
    'default': {
      'format': '%(asctime)s - %(levelname)-8s - %(name)s - %(message)s',
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
    'handlers': ['default']
  },
  
  'loggers': {
#     'smtinterp': {
#       'level': 'WARNING',
#     }
  }
}
