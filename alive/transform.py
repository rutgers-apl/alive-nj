'''
General object representing transformations (optimizations).
'''

from . import language as L
from . import typing
from .formatter import *
from .util import pretty
import logging
import collections
import itertools

logger = logging.getLogger(__name__)


class Transform(pretty.PrettyRepr):
  def __init__(self, src, tgt, pre=None, name=''):
    self.name = name
    self.pre = pre
    self.src = src
    self.tgt = tgt

  def pretty(self):
    return pretty.pfun(type(self).__name__,
      (self.src, self.tgt, self.pre, self.name))

  def subterms(self):
    """Generate all terms in the transform, without repeats.
    """
    seen = set()

    return itertools.chain(
      L.subterms(self.src, seen),
      L.subterms(self.tgt, seen),
      () if self.pre is None else L.subterms(self.pre, seen)
    )

  def type_constraints(self):
    logger.debug('%s: Gathering type constraints', self.name)

    t = typing.TypeConstraints()
    seen = set()

    # find type variables from the source
    t.collect(self.src, seen)

    # note the type variables fixed by the source
    t.bind_reps()

    if self.pre:
      t.collect(self.pre, seen)

    t.collect(self.tgt, seen)
    t.eq_types(self.src, self.tgt)

    # ensure no ambiguously-typed values
    t.set_defaultables()

    return t

  def abstract_type_model(self):
    if not hasattr(self, '_model'):
      self._model = self.type_constraints().get_type_model()

    return self._model

  def type_models(self):
    return self.abstract_type_model().type_vectors()

  def validate_model(self, type_vector):
    """Return whether the type vector meets this opt's constraints.
    """

    model = self.abstract_type_model()
    V = typing.Validator(model, type_vector)
    seen = set()

    try:
      V.eq_types(self.src, self.tgt)

      for t in self.subterms():
        logger.debug('checking %s', t)
        t.type_constraints(V)

      return True

    except typing.Error:
      return False

  def constant_defs(self):
    """Generate shared constant terms from the target and precondition.

    Terms are generated before any terms that reference them.
    """

    return constant_defs(self.tgt, [self.pre] if self.pre else [])

  def format(self):
    return Formatted(self)


@format_doc.register(Transform)
def _(opt, fmt, prec):
  return format_parts(
    opt.name,
    [('Pre:', opt.pre)] if opt.pre else [],
    opt.src,
    opt.tgt,
    fmt)


