import itertools
import re
from .. import parser
from ..error import Error

__all__ = ('read_opt_files', 'all_of', 'any_of', 'match_name', 'contains_node')

def read_opt_files(files, filter=None, extended_results=False):
  """Parse and iterate optimizations given in files.

  files  - iterable of open files or strings
  filter - selects which optimizations to return, None means return all
  extended_results
         - if True, returns any features provided with the optimization
  """

  opts = itertools.chain.from_iterable(
            parser.parse_opt_file(f, extended_results) for f in files)

  if filter:
    if extended_results:
      return itertools.ifilter(lambda x: filter(x[0]), opts)

    return itertools.ifilter(filter, opts)

  return opts

def all_of(*preds):
  preds = filter(None,preds)

  if len(preds) == 0: return None
  if len(preds) == 1: return preds[0]

  return lambda opt: all(p(opt) for p in preds)

def any_of(*preds):
  preds = filter(None,preds)

  if len(preds) == 1: return preds[0]

  return lambda opt: any(p(opt) for p in preds)

def contains_node(cls):
  return lambda opt: any(isinstance(t, cls) for t in opt.subterms())

def match_name(pattern):
  if pattern is None:
    return None

  try:
    regex = re.compile(pattern)
    return lambda opt: regex.search(opt.name)
  except re.error as e:
    raise Error('Invalid pattern: {}'.format(e))
