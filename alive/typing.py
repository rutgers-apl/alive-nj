'''
Apply typing constraints to the IR.
'''

from .language import *
from .util import disjoint, pretty
import logging, itertools
import collections
import weakref

logger = logging.getLogger(__name__)

FIRST_CLASS, NUMBER, FLOAT, INT_PTR, PTR, INT, BOOL, Last = range(8)

context = weakref.WeakKeyDictionary()
  # Maps nodes to type ids
  # Uses weak refs, to enable creating many typed terms without having to worry
  # about garbage collection (useful when enumerating possible preconditions)
  #
  # Presently, nodes are stored by their hash (ie, by pointer). This means:
  # 1. the same node cannot have two different type ids, so sharing nodes between
  #    transformations is dangerous
  # 2. any switch to structural equality for nodes will require changing how this
  #    works (eg, log2(C) may have different types in different contexts, presently
  #    they are different objects)
  #
  # It is possible to avoid using a global here by including context in the
  # TypeModel, but this would possibly complicate things elsewhere.

def most_specific(c1,c2):
  if c1 > c2:
    c1,c2 = c2,c1

  if c1 == NUMBER:
    if c2 == PTR:
      return None

    if c2 == INT_PTR:
      return INT

  if c1 == FLOAT and c2 != FLOAT:
    return None

  if c1 == PTR and c2 != PTR:
    return None

  return c2


_constraint_name = {
  FIRST_CLASS: 'first class',
  NUMBER:      'integer or floating-point',
  FLOAT:       'floating-point',
  INT_PTR:     'integer or pointer',
  PTR:         'pointer',
  INT:         'integer',
  BOOL:        'i1',
}

_constraint_class = {
  FIRST_CLASS: (IntType, FloatType, PtrType),
  NUMBER:      (IntType, FloatType),
  FLOAT:       FloatType,
  INT_PTR:     (IntType, PtrType),
  PTR:         PtrType,
  INT:         IntType,
}

def meets_constraint(con, ty):
  if con == BOOL:
    return ty == IntType(1)
  
  return isinstance(ty, _constraint_class[con])



class TypeConstraints(object):
  logger = logger.getChild('TypeConstraints')
  def __init__(self, maxwidth=64):
    self.sets = disjoint.DisjointSubsets()
    self.specifics = {}
    self.constraints = collections.defaultdict(lambda: FIRST_CLASS)
    self.ordering = set() # pairs (x,y) where width(x) < width(y)
    self.width_equalities = set() # pairs (x,y) where width(x) == width(y)
    self.widthlimit = maxwidth+1

  def __call__(self, term):
    self.ensure(term)
  
  def ensure(self, term):
    if term in self.sets:
      return

    assert isinstance(term, Value)
    self.logger.debug('adding term %s', term)
    self.sets.add_key(term)
    term.type_constraints(self)

  def _merge(self, t1, t2):
    self.logger.debug('unifying %s and %s', t1, t2)

    if t2 in self.specifics:
      self.specific(t1, self.specifics.pop(t2))

    if t2 in self.constraints:
      self.constrain(t1, self.constraints.pop(t2))

  def eq_types(self, *terms):
    for t in terms:
      self.ensure(t)
    
    it = iter(terms)
    t1 = self.sets.rep(it.next())
    for t2 in it:
      self.sets.unify(t1, t2, self._merge)



  def specific(self, term, ty):
    self.ensure(term)
    if ty is None:
      return

    self.logger.debug('specifying %s : %s', term, ty)
    r = self.sets.rep(term)
    if r not in self.specifics:
      self.specifics[r] = ty
    if self.specifics[r] != ty:
      raise Error('Incompatible types for {}: {} and {}'.format(
        term.name if hasattr(term, 'name') else str(term),
        ty,
        self.specifics[term]))
  
  def constrain(self, term, con):
    self.ensure(term)
    r = self.sets.rep(term)
    con0 = self.constraints[r]

    self.logger.debug('Refining constraint for %s: %s & %s', term, con, con0)
    c = most_specific(con0, con)
    if c is None:
      raise Error('Incompatible constraints for {}: {} and {}'.format(
        term.name if hasattr(term, 'name') else str(term),
        _constraint_name[con],
        _constraint_name[con0]))

    self.constraints[r] = c

  def integer(self, term):
    self.constrain(term, INT)

  def bool(self, term):
    self.constrain(term, BOOL)
  
  def pointer(self, term):
    self.constrain(term, PTR)
  
  def int_ptr_vec(self, term):
    self.constrain(term, INT_PTR)

  def float(self, term):
    self.constrain(term, FLOAT)

  def number(self, term):
    self.constrain(term, NUMBER)

  def first_class(self, term):
    self.constrain(term, FIRST_CLASS)

  def width_order(self, lo, hi):
    if isinstance(lo, Value):
      self.ensure(lo)
    self.ensure(hi)
    self.ordering.add((lo,hi))

  def width_equal(self, a, b):
    self.ensure(a)
    self.ensure(b)
    self.width_equalities.add((a,b))

  def validate(self):
    '''Make sure specific types meet constraints'''
    
    for r in self.specifics:
      if r not in self.constraints:
        continue

      if not meets_constraint(self.constraints[r], self.specifics[r]):
        raise Error('Incompatible constraints for {}: {} is not {}'.format(
          r.name if hasattr(term, 'name') else str(r),
          self.specifics[r],
          _constraint_name[self.constraints[r]]))

  def simplify_orderings(self):
    if self.logger.isEnabledFor(logging.DEBUG):
      self.logger.debug('simplifying ordering:\n  ' + 
        pretty.pformat(self.ordering, indent=2) +
        '\n  equalities:\n' + pretty.pformat(self.width_equalities, indent=2))

    ords = { (lo if isinstance(lo, int) else self.sets.rep(lo), self.sets.rep(hi))
              for (lo,hi) in self.ordering }

    eqs = { (self.sets.rep(a), self.sets.rep(b))
      for (a,b) in self.width_equalities if a != b }
    eqs = { (a,b) if id(a) < id(b) else (b,a) for (a,b) in eqs}

    if self.logger.isEnabledFor(logging.DEBUG):
      self.logger.debug('simplified ordering:\n  ' + 
        pretty.pformat(ords, indent=2) +
        '\n  equalities:\n' + pretty.pformat(eqs, indent=2))

    assert all(isinstance(lo, int) or
      most_specific(self.constraints[lo], self.constraints[hi]) is not None
      for (lo, hi) in ords)

    self.ordering = ords
    self.width_equalities = eqs

  def get_type_model(self):
    """Return an AbstractTypeModel expressing the constraints gathered so far,
    and sets the type variable for each term.
    """

    self.simplify_orderings()
    # TODO: this can be folded into the next loop

    # find predecessors and lower bounds
    lower_bounds = collections.defaultdict(list)
    min_width = {}
    for lo,hi in self.ordering:
      if isinstance(lo, int):
        min_width[hi] = max(lo, min_width.get(hi,0))
      else:
        lower_bounds[hi].append(lo)

    if logger.isEnabledFor(logging.DEBUG):
      logger.debug('get_type_model:\n  min_width: ' +
        pretty.pformat(min_width, indent=13) +
        '\n  lower_bounds: ' + pretty.pformat(lower_bounds, indent=16))

    # recursively walk DAG
    # TODO: handle all specific constraints first?
    finished = {}
    order = []
    def visit(rep):
      if rep in finished:
        if finished[rep]:
          return

        # if rep is in finished, but we haven't set it to true, then
        # we must have found a loop
        raise Error('Incompatible constraints for {}: circular ordering'.format(
          rep.name if hasattr(rep, 'name') else str(rep)
          ))

      finished[rep] = False
      for p in lower_bounds[rep]:
        visit(p)

      order.append(rep)
      finished[rep] = True

    for r in self.sets.reps():
      visit(r)

    tyvars = dict(itertools.izip(order, itertools.count()))
    if logger.isEnabledFor(logging.DEBUG):
      logger.debug('get_type_model:\n  tyvars: ' +
        pretty.pformat(tyvars, indent=10))

    min_width = { tyvars[rep]: w for (rep,w) in min_width.iteritems() }
    lower_bounds = { tyvars[rep]: tuple(tyvars[t] for t in ts)
                      for (rep,ts) in lower_bounds.iteritems() if ts }

    # recreate specific and constraint in terms of tyvars
    specific = {}
    constraint = []
    for tyvar,rep in enumerate(order):
      if rep in self.specifics:
        specific[tyvar] = self.specifics[rep]
        if not meets_constraint(self.constraints[rep], self.specifics[rep]):
          raise Error('Incompatible constraints for {}: {} is not {}'.format(
            rep.name if hasattr(rep, 'name') else str(r),
            self.specifics[rep],
            _constraint_name[self.constraints[rep]]))

      constraint.append(self.constraints[rep])

      for t in self.sets.subset(rep):
        assert t not in context
        context[t] = tyvar

    # note equal widths
    width_equality = {}
    for (a,b) in self.width_equalities:
      assert a != b
      va = tyvars[a]
      vb = tyvars[b]
      if va > vb: va,vb = vb,va

      if vb in width_equality:
        width_equality[va] = width_equality[vb]

      width_equality[vb] = va

    return AbstractTypeModel(constraint, specific, min_width, lower_bounds,
      width_equality)

class AbstractTypeModel(object):
  """Contains the constraints gathered during type checking.
  """

  pointer_width = 64
    # in principle, this could be a parameter to the model, or even vary during
    # enumeration, but right now pointer width doesn't affect anything

  max_int = 65 # one more than the largest int type permitted
  float_tys = (HalfType(), SingleType(), DoubleType())

  def __init__(self, constraint, specific, min_width, lower_bounds, width_equality):
    self.constraint = constraint
    self.specific = specific
    self.min_width = min_width
    self.lower_bounds = lower_bounds
    self.width_equality = width_equality
    self.tyvars = len(constraint)

  # TODO: we probably need some way to determine which types are larger/smaller than

  @staticmethod
  def int_types(min_width, max_width):
    """Generate IntTypes in the range min_width to max_width-1.
    """

    if min_width <= 4 < max_width:
      yield IntType(4)
    if min_width <= 8 < max_width:
      yield IntType(8)
    for w in xrange(min_width, min(max_width, 4)):
      yield IntType(w)
    for w in xrange(max(min_width, 5), min(max_width, 8)):
      yield IntType(w)
    for w in xrange(max(min_width, 9), max_width):
      yield IntType(w)

  def floor(self, vid, vector):
    if vid in self.lower_bounds:
      floor = max(vector[v].width for v in self.lower_bounds[vid])
    else:
      floor = 0
    floor = max(floor, self.min_width.get(vid, 0))
    return floor

  def bits(self, ty):
    """Return the size of the type in bits.
    """

    if isinstance(ty, IntType):
      return ty.width
    if isinstance(ty, X86FP80Type):
      return 80
    if isinstance(ty, FloatType):
      return ty.exp + ty.frac
      # true for all current floats: the sign bit and the implicit fraction
      # bit cancel out
    if isinstance(ty, PtrType):
      return self.pointer_width

    assert False


  # this could be done as a stack, instead of as nested generators
  def _enum_vectors(self, vid, vector):
    if vid >= self.tyvars:
      yield tuple(vector)
      return

    if vid in self.specific:
      # TODO: better to put an upper bound on variables less than a fixed type
      if vector[vid] <= self.floor(vid, vector):
        return

      # this check could be avoided if fixed types occurred before variables
      if vid in self.width_equality and \
          self.bits(vector[vid]) != self.bits(vector[self.width_equality[vid]]):
        return

      for v in self._enum_vectors(vid+1, vector):
        yield v

      return

    con = self.constraint[vid]
    if con == FIRST_CLASS:
      tys = itertools.chain(self.int_types(1, self.max_int), (PtrType(),), self.float_tys)
    elif con == NUMBER:
      tys = itertools.chain(self.int_types(1, self.max_int), self.float_tys)
    elif con == FLOAT:
      tys = (t for t in self.float_tys if t > self.floor(vid, vector))
    elif con == INT_PTR:
      tys = itertools.chain(self.int_types(1, self.max_int), (PtrType(),))
    elif con == INT:
      floor = self.floor(vid, vector)
      if isinstance(floor, IntType): floor = floor.width
      tys = self.int_types(floor + 1, self.max_int)
    elif con == BOOL:
      tys = (IntType(1),)
    else:
      assert False

    if vid in self.width_equality:
      bits = self.bits(vector[self.width_equality[vid]])
      tys = (t for t in tys if self.bits(t) == bits)
      # NOTE: this wastes a lot of effort, but it's only used for bitcast
      # NOTE: this will permit bitcasting between equal types (eg. i64 -> i64)

    for t in tys:
      vector[vid] = t
      for v in self._enum_vectors(vid+1, vector):
        yield v

  def type_vectors(self):
    """Generate type vectors consistent with this model."""

    vector = [None] * self.tyvars

    for vid,ty in self.specific.iteritems():
      vector[vid] = ty

    return self._enum_vectors(0, vector)

class Error(Exception):
  pass
