'''
Apply typing constraints to the IR.
'''

from language import *
import disjoint, logging, collections, z3, pretty
import itertools

logger = logging.getLogger(__name__)

FIRST_CLASS, NUMBER, FLOAT, INT_PTR, PTR, INT, BOOL, Last = range(8)

class IncompatibleConstraints(Exception):
  pass


def most_specific(c1,c2):
  if c1 > c2:
    c1,c2 = c2,c1

  if c1 == NUMBER:
    if c2 == PTR:
      raise IncompatibleConstraints 

    if c2 == INT_PTR:
      return INT

  if c1 == FLOAT and c2 != FLOAT:
    raise IncompatibleConstraints

  if c1 == PTR and c2 != PTR:
    raise IncompatibleConstraints
  
  return c2


def meets_constraint(con, ty):
  if con == FIRST_CLASS:
    return isinstance(ty, (IntType, FloatType, PtrType))
  if con == NUMBER:
    return isinstance(ty, (IntType, FloatType))
  if con == FLOAT:
    return isinstance(ty, FloatType)
  if con == INT_PTR:
    return isinstance(ty, (IntType, PtrType))
  if con == PTR:
    return isinstance(ty, PtrType)
  if con == INT:
    return isinstance(ty, IntType)
  if con == BOOL:
    return ty == IntType(1)

  assert False

FloatTy = z3.Datatype('FloatTy')
FloatTy.declare('half')
FloatTy.declare('single')
FloatTy.declare('double')
FloatTy = FloatTy.create()

TySort = z3.Datatype('Ty')
TySort.declare('integer', ('width', z3.IntSort()))
TySort.declare('pointer')
TySort.declare('float', ('float_ty', FloatTy))
TySort = TySort.create()


def translate_ty(ty):
  'Translate an internal type to Z3'
  
  if isinstance(ty, IntType):
    return TySort.integer(ty.width)

  if isinstance(ty, HalfType):
    return TySort.float(FloatTy.half)

  if isinstance(ty, SingleType):
    return TySort.float(FloatTy.single)

  if isinstance(ty, DoubleType):
    return TySort.float(FloatTy.double)

  if isinstance(ty, PtrType):
    return TySort.pointer
  
  assert False # TODO: raise something here

def ty_from_z3(z3_ty):
  'Translate a Z3 TySort into an Alive Type'

  if z3_ty.decl().eq(TySort.integer):
    return IntType(z3_ty.arg(0).as_long())

  if z3_ty.decl().eq(TySort.float):
    fty = z3_ty.arg(0)
    if fty.eq(FloatTy.half):
      return HalfType()
    if fty.eq(FloatTy.single):
      return SingleType()
    if fty.eq(FloatTy.double):
      return DoubleType()

  if z3_ty.eq(TySort.pointer):
    return PtrType()
  assert False

def z3_constraints(con, var, maxwidth=64, depth=1):
  if con == FIRST_CLASS:
    return z3.Or(
      z3_constraints(PTR, var, maxwidth, depth),
      z3_constraints(INT, var, maxwidth, depth),
      z3_constraints(FLOAT, var, maxwidth, depth),
    )

  if con == FLOAT:
    return TySort.is_float(var)

  if con == INT_PTR:
    return z3.Or(
      z3_constraints(PTR, var, maxwidth, depth),
      z3_constraints(INT, var, maxwidth, depth),
    )

  if con == PTR:
    return TySort.is_pointer(var)

  if con == INT:
    return z3.And(
      TySort.is_integer(var),
      TySort.width(var) > 0,
      TySort.width(var) <= maxwidth
    )

  if con == BOOL:
    return var == TySort.integer(1)
    


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
      logger.error('Specified %s and %s for %s', ty, self.specifics[r], term)
      raise IncompatibleConstraints
  
  def constrain(self, term, con):
    self.ensure(term)
    r = self.sets.rep(term)
    con0 = self.constraints.get(r,FIRST_CLASS)

    logger.debug('Refining constraint for %s: %s & %s', term, con, con0)
    self.constraints[r] = most_specific(con0, con)

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
        raise IncompatibleConstraints

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


  def z3_solver(self, maxwidth=64, depth=0):
    self.simplify_orderings()
    s = z3.Solver()
    # this stops working if we use SolverFor('QF_LIA') for unclear reasons
    
    vars = {}
    var = 0
    for r in self.sets.reps():
      var += 1
      vars[r] = z3.Const('v_' + str(var), TySort)
      
      if r in self.constraints:
        s.add(z3_constraints(self.constraints[r], vars[r], maxwidth, depth))
      
      if r in self.specifics:
        s.add(vars[r] == translate_ty(self.specifics[r]))

    for (lo,hi) in self.ordering:
      if isinstance(lo, int):
        s.add(lo < TySort.width(vars[hi]))
      else:
        s.add(TySort.width(vars[lo]) < TySort.width(vars[hi]))
    
    return s, vars

  def z3_models(self, maxwidth=64, depth=0):
    s, vars = self.z3_solver(maxwidth, depth)
    
    if logger.isEnabledFor(logging.DEBUG):
      logger.debug('solver\n%s', s)
      logger.debug('vars\n  %s', pretty.pformat(vars, indent=2))

    if s.check() != z3.sat:
      raise IncompatibleConstraints

    nonfixed = [v for r,v in vars.iteritems()
                  if r not in self.specifics and
                     self.constraints.get(r, FIRST_CLASS) != BOOL]

    while s.check() == z3.sat:
      model = s.model()
      logger.debug('solution\n%s', model)

      ty_model = { r: ty_from_z3(model[v]) for (r,v) in vars.iteritems() }
      yield TypeModel(self.sets, ty_model)

      s.add(z3.Or([v != model[v] for v in nonfixed]))
      logger.debug('solver %s', s)

    logger.debug('No solution')

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
        raise IncompatibleConstraints
      model[r] = ty

    for lo,hi in self.ordering:
      if lo in model and hi in model and model[lo].width >= model[hi].width:
        raise IncompatibleConstraints
      if isinstance(lo, int) and hi in model and lo >= model[hi].width:
        raise IncompatibleConstraints

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
