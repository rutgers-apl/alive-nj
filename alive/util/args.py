"""
Simple extensions to argparse for common cases.
"""

import argparse

class NegatableFlag(argparse.Action):
  """Action type for paired Boolean flags, e.g., '--spam'/'--no-spam'.

  This is an alternative to specifying two separate options with a common
  dest and opposite storage actions. If --spam and --no-spam occur in the
  argument list, the last one wins.

  Usage:
    parser.add_argument('--spam', action=NegatableFlag)

  Usable keywords: dest, default, required, help
  """
  def __init__(self,
               option_strings,
               dest,
               default=False,
               required=False,
               help=None):

    neg_options = []
    for opt in option_strings:
      if opt.startswith('--no-'):
        raise ValueError('Flags cannot begin with "--no-"')
      if opt.startswith('--'):
        neg_options.append('--no-' + opt[2:])

    option_strings.extend(neg_options)

    if help:
      help += ' (default {})'.format('yes' if default else 'no')

    super(NegatableFlag, self).__init__(
      option_strings=option_strings,
      dest=dest,
      nargs=0,
      default=default,
      required=required,
      help=help)

  def __call__(self, parser, namespace, values, option_string=None):
    setattr(namespace, self.dest,
      not (isinstance(option_string,str) and option_string.startswith('--no-')))
