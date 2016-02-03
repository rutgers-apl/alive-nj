'''
Apply typing constraints to the IR.
'''

from language import *
import disjoint, logging, collections, z3

logger = logging.getLogger(__name__)

FIRST_CLASS, PTR, INT, BOOL, Last = range(5)

class IncompatibleConstraints(Exception):
  pass


def most_specific(c1,c2):
  if c1 > c2:
    c1,c2 = c2,c1
  
  if c1 == PTR and c2 != PTR:
    raise IncompatibleConstraints
  
  return c2


def meets_constraint(con, ty):
  if con == FIRST_CLASS:
    return isinstance(ty, IntType) # TODO: PtrType
  if con == PTR:
    return False # TODO: PtrType
  if con == INT:
    return isinstance(ty, IntType)
  if con == BOOL:
    return ty == IntType(1)

  assert False

TySort = z3.Datatype('Ty')
TySort.declare('integer', ('width', z3.IntSort()))
TySort.declare('pointer')
TySort = TySort.create()


def translate_ty(ty):
  'Translate an internal type to Z3'
  
  if isinstance(ty, IntType):
    return TySort.integer(ty.width)
  
  assert False # TODO: raise something here

def z3_constraints(con, var, maxwidth=64, depth=1):
  if con == FIRST_CLASS:
    return z3.Or(
      z3_constraints(PTR, var, maxwidth, depth),
      z3_constraints(INT, var, maxwidth, depth)
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
  def __init__(self):
    self.sets = disjoint.DisjointSubsets()
    self.specifics = {}
    self.constraints = {}
    self.ordering = set() # pairs (x,y) where width(x) < width(y)

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
    self.constrain(term, FIRST_CLASS)

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
    logger.debug('simplifying ordering: %s', self.ordering)
    ords = { (lo if isinstance(lo, int) else self.sets.rep(lo), self.sets.rep(hi))
              for (lo,hi) in self.ordering }
    logger.debug('simplifed ordering: %s', ords)
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
    
    logger.debug('solver %s', s)
    logger.debug('vars %s', vars)
    
    if s.check() != z3.sat:
      raise IncompatibleConstraints

    nonfixed = [v for r,v in vars.iteritems()
                  if r not in self.specifics and
                     self.constraints.get(r, FIRST_CLASS) != BOOL]

    while s.check() == z3.sat:
      model = s.model()
      logger.debug('solution\n%s', model)
      yield { k: model[vars[r]] for k,r in self.sets.key_reps() }
      
      s.add(z3.Or([v != model[v] for v in nonfixed]))
      
      logger.debug('solver %s', s)


if __name__ == '__main__':
  logging.basicConfig(level=logging.DEBUG)
  
#   x = Input('x')
#   y = AddInst(Input('w'), SExtInst(x), IntType(8))
#   z = IcmpInst('sle',x,y)

  x = Input('x')
  y = Input('y')
  z = AddInst(SExtInst(x), SExtInst(y), IntType(8))
  w = SExtInst(AddInst(x,y))
  
  T = TypeConstraints()
  T(z)

#   from pprint import pprint
#   pprint(T.constraints)
#   pprint(T.specifics)
# 
#   for m in T.z3_models():
#     print
#     pprint(m)
#     break
  
  T(w)
  T.eq_types(w,z)

  from pprint import pprint
  pprint(T.constraints)
  pprint(T.specifics)

  for m in T.z3_models():
    print
    pprint(m)
