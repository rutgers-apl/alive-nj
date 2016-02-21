'''
Apply typing constraints to the IR.
'''

from language import *
import disjoint, pretty
import logging, itertools

logger = logging.getLogger(__name__)

FIRST_CLASS, NUMBER, FLOAT, INT_PTR, PTR, INT, BOOL, Last = range(8)


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



class TypeConstraints(BaseTypeConstraints):
  def __init__(self, maxwidth=64):
    self.sets = disjoint.DisjointSubsets()
    self.specifics = {}
    self.constraints = {}
    self.ordering = set() # pairs (x,y) where width(x) < width(y)
    self.widthlimit = maxwidth+1

  def __call__(self, term):
    self.ensure(term)
  
  def ensure(self, term):
    if term in self.sets:
      return

    assert isinstance(term, Value)
    logger.debug('adding term %s', term)
    self.sets.add_key(term)
    term.accept(self)

  def eq_types(self, *terms):
    for t in terms:
      self.ensure(t)
    
    it = iter(terms)
    t1 = self.sets.rep(it.next())
    for t2 in it:
      if self.sets.unified(t1,t2):
        continue

      logger.debug('unifying %s and %s',t1,t2)
      t2 = self.sets.rep(t2)
      self.sets.unify(t1,t2)
      if t2 == self.sets.rep(t1):
        t1,t2 = t2,t1
      
      if t2 in self.specifics:
        self.specific(t1, self.specifics.pop(t2))
      if t2 in self.constraints:
        self.constrain(t1, self.constraints.pop(t2))

  def specific(self, term, ty):
    self.ensure(term)
    if ty is None:
      return

    logger.debug('specifying %s : %s', term, ty)
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
    con0 = self.constraints.get(r, FIRST_CLASS)

    logger.debug('Refining constraint for %s: %s & %s', term, con, con0)
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

  def width_ceiling(self, lo, hi):
    if isinstance(lo, Value):
      self.ensure(lo)
    self.ensure(hi)
    self.ordering.add((lo,hi))

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
    if logger.isEnabledFor(logging.DEBUG):
      logger.debug('simplifying ordering:\n  ' + 
        pretty.pformat(self.ordering, indent=2))

    ords = { (lo if isinstance(lo, int) else self.sets.rep(lo), self.sets.rep(hi))
              for (lo,hi) in self.ordering }

    if logger.isEnabledFor(logging.DEBUG):
      logger.debug('simplified ordering:\n  ' + 
        pretty.pformat(ords, indent=2))

    self.ordering = ords

  def type_models(self):
    logger.debug('generating models')
    self.simplify_orderings()
    
    numbers = [r for (r,con) in self.constraints.iteritems() if con == NUMBER]
    if numbers:
      logger.warning('NUMBER constraint(s) survived unification\n  %s',
        pretty.pformat(numbers, indent=2))

    model = {}

    # collect sets with fixed types
    for r,ty in self.specifics.iteritems():
      if r in self.constraints and not \
          meets_constraint(self.constraints[r], ty):
        raise Error('Incompatible constraints for {}: {} is not {}'.format(
          r.name if hasattr(r, 'name') else str(r),
          self.specifics[r],
          _constraint_name[self.constraints[r]]))

      model[r] = ty

    for lo,hi in self.ordering:
      if lo == hi:
        raise Error('Incompatible constraints for {}: circular ordering'.format(
          lo.name if hasattr(lo, 'name') else str(lo)))
      if lo in model and hi in model and model[lo].width >= model[hi].width:
        raise Error('Incompatible constraints for {} and {}: {} < {}'.format(
          lo.name if hasattr(lo, 'name') else str(lo),
          hi.name if hasattr(hi, 'name') else str(hi),
          model[lo],
          model[hi]))
      if isinstance(lo, int) and hi in model and lo >= model[hi].width:
        raise Error('Incompatible constraints for {}: {} < {}'.format(
          hi.name if hasattr(hi, 'name') else str(hi),
          IntType(lo),
          model[hi]))

    vars = tuple(r for r in self.sets.reps() if r not in self.specifics)
    if logger.isEnabledFor(logging.DEBUG):
      logger.debug('variables:\n  ' + pretty.pformat(vars, indent=2))
      logger.debug('initial model:\n  ' + pretty.pformat(model, indent=2))

    return self._iter_models(0, vars, model)

  float_tys = (HalfType(), SingleType(), DoubleType())

  def _iter_models(self, n, vars, model):
    if n == len(vars):
      if logger.isEnabledFor(logging.DEBUG):
        logger.debug('emitting model\n  ' + pretty.pformat(model, indent=2))

      yield TypeModel(self.sets, dict(model))
      return

    v = vars[n]
    con = self.constraints.get(v, FIRST_CLASS)
    if con == FIRST_CLASS:
      tys = itertools.chain(self._ints(1, self.widthlimit), (PtrType(),), self.float_tys)
    elif con == NUMBER:
      tys = itertools.chain(self._ints(1, self.widthlimit), self.float_tys)
    elif con == FLOAT:
      tys = self.float_tys
    elif con == INT_PTR:
      tys = itertools.chain(self._ints(1, self.widthlimit), (PtrType(),))
    elif con == PTR:
      tys = (PtrType(),)
    elif con == INT:
      # this is the only case where we can have an ordering constraint
      wmin = 1
      wmax = self.widthlimit
      for lo,hi in self.ordering:
        if lo == v and hi in model and model[hi].width < wmax:
          wmax = model[hi].width
        elif hi == v and lo in model and model[lo].width > wmin:
          wmin = model[lo].width
        elif hi == v and isinstance(lo, int) and lo >= wmin:
          wmin = lo+1

      logger.debug('Int range [%s,%s) for %s', wmin, wmax, v)
      tys = self._ints(wmin,wmax)

    elif con == BOOL:
      tys = (IntType(1),)
    else:
      assert False

    for ty in tys:
      model[v] = ty
      for m in self._iter_models(n+1, vars, model):
        yield m

  def _ints(self, wmin, wmax):
    if wmin <= 4 < wmax:
      yield IntType(4)
    if wmin <= 8 < wmax:
      yield IntType(8)
    for w in xrange(wmin, min(wmax,4)):
      yield IntType(w)
    for w in xrange(max(wmin,5),min(wmax,8)):
      yield IntType(w)
    for w in xrange(max(wmin,9), wmax):
      yield IntType(w)

class TypeModel(object):
  '''Map terms to types.
  '''

  def __init__(self, sets, model):
    self.sets = sets
    self.model = model

  def __getitem__(self, key):
    return self.model[self.sets.rep(key)]

class Error(Exception):
  pass
