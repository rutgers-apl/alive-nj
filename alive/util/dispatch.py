"""
Decorators for creating single- and double-dispatch functions.

Usage:

  @singledispatch
  def spam(x,y,z=None):
    ...

  @spam.register(Eggs)
  def _(x, y, z=None):
    ...


  # the undecorated method is returned
  @spam.register(Bacon)
  @spam.register(Spam)
  def _(x, y, z=None):
    ...

  # use as a function to register an existing function
  spam.register(BakedBeans, spam_baked_beans)
  
  # obtain specific implementations
  spam.dispatch(BakedBeans) is spam_baked_beans
"""

__all__ = ('singledispatch', 'doubledispatch')

import functools

def singledispatch(default):
  registry = {object: default}

  def dispatch(cls):
    for k in cls.mro():
      if k in registry:
        return registry[k]

    raise NotImplementedError

  def register(cls, fun=None):
    if fun is None:
      return lambda f: register(cls, f)

    registry[cls] = fun
    return fun

  def wrapper(arg, *args, **kws):
    return dispatch(type(arg))(arg, *args, **kws)

  functools.update_wrapper(wrapper, default)
  wrapper.dispatch = dispatch
  wrapper.register = register
  wrapper.registry = registry

  return wrapper


def _lookup2(cls1, cls2, registry):
  """
  Find the most specific implementation for (cls1,cls2) in registry.
  
  A more specific superclass of cls1 beats a more specific superclass
  of cls2.
  """

  for k1 in cls1.mro():
    for k2 in cls2.mro():
      if (k1,k2) in registry:
        return registry[(k1,k2)]

  raise NotImplementedError

def doubledispatch(default):
  """
  Create a multimethod which dispatches on the first two arguments.
  """
  
  registry = {(object,object): default}
  cache = {}

  def dispatch(cls1, cls2):
    try:
      return cache[(cls1, cls2)]
    except KeyError:
      fun = _lookup2(cls1, cls2, registry)
      cache[(cls1,cls2)] = fun
      return fun

  def register(cls1, cls2, fun=None):
    if fun is None:
      return lambda f: register(cls1, cls2, f)

    cache.clear()
    registry[(cls1,cls2)] = fun
    return fun

  def wrapper(arg1, arg2, *args, **kws):
    return dispatch(type(arg1), type(arg2))(arg1, arg2, *args, **kws)

  functools.update_wrapper(wrapper, default)
  wrapper.dispatch = dispatch
  wrapper.register = register
  wrapper.registry = registry
  
  return wrapper
