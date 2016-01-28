'''
Implements a disjoint subset structure.
'''

class DisjointSubsets(object):
  '''
  Stores values in one or more subsets. Each value exists in only one
  subset at a time. Subsets may be unified.
  '''
  def __init__(self):
    self._parent = {}
    # the parent is another element of the subset, or None for the
    # representative. Each subset has exactly one representative.
    # Must form a path from every element of the subset to the
    # representative
    self._subset = {}
    # the subset, represented as a set

  def __contains__(self, key):
    return key in self._parent

  def key_reps(self):
    'Generate pairs consisting of an element and its representative.'
    for key in self._parent:
      rep = self.rep(key)
      yield (key,rep)

  def subset_items(self):
    'Generate pairs consisting of a representative and its subset.'
    return self._subset.iteritems()

  def reps(self):
    'Generate all representatives.'
    return self._subset.iterkeys()

  def add_key(self, key):
    if key in self._parent:
      return
    
    self._parent[key] = None
    self._subset[key] = frozenset([key])

  def rep(self, key):
    if key not in self._parent:
      raise KeyError

    while self._parent[key] is not None:
      key = self._parent[key]
    
    return key

  def subset(self, key):
    rep = self.rep(key)
    return self._subset[rep]

  def unify(self, key1, key2):
    rep1 = self.rep(key1)
    rep2 = self.rep(key2)

    if rep1 == rep2:
      return

    self._parent[rep2] = rep1
    subset1 = self._subset[rep1]
    subset2 = self._subset.pop(rep2)
    self._subset[rep1] = subset1.union(subset2)

  def unified(self, key1, key2):
    return self.rep(key1) == self.rep(key2)

# ----

class Tag(object):
  '''Subclasses of Tag may be used to label objects, so that they
  may be added to sets or DisjointSubsets multiple times.'''

  def __init__(self, value):
    self.val = value

  def __eq__(self, other):
    return type(self) == type(other) and self.val == other.val

  def __ne__(self, other):
    return not (self == other)

  def __hash__(self):
    return hash(type(self)) ^ hash(self.val)

  def __repr__(self):
    return '{}({!r})'.format(type(self).__name__, self.val)
