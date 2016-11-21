'''
Simple pretty printer.

Based on "Lazy v. Yield: Incremental, Linear Pretty-Printing", by Kiselyov,
Peyton-Jones, and Sabry.

Simple documents can be created using 'text', 'line', and 'seq'.

  >>> pprint(seq(text('hello'), line, text('world')))
  hello
  world

'group' will replace line breaks by spaces, as long as doing so will
not exceed the output width (default 80).

  >>> pprint(group(text('hello'), line, text('world')))
  hello world
  >>> pprint(group(text('hello'), line, text('world')), width=10)
  hello
  world

If 'doc' prints on multiple lines, 'nest(i, doc)' will indent the second and
following lines by i spaces. This can also be written "doc.nest(i)".

'text' and 'pprint' convert strings to documents. 'prepr(obj)' calls
'obj.pretty()', if defined, and otherwise uses 'repr(obj)' except for some
built-in Python collections.

  >>> pprint('spam')
  spam
  >>> pprint(prepr('spam'))
  'spam'
  >>> pprint(['spam','eggs','bacon','spam'], width=30)
  ['spam',
   'eggs',
   'bacon',
   'spam']

Non-document arguments to 'seq', 'group', and 'join' are passed through 'text'.
'softline' breaks if the text following it is too long to fit. This can be
combined with join to do word wrapping.

  >>> pprint(softline.join(['spam']*5 + ['baked', 'beans']), width=30)
  spam spam spam spam spam baked
  beans
  >>> pprint(softline.join(['spam']*5 + ['baked', 'beans']), width=20)
  spam spam spam spam
  spam baked beans

'''

__author__ = 'David Menendez <davemm@cs.rutgers.edu>'
__version__ = '2.0'

from collections import deque
from itertools import chain
import sys, StringIO

__all__ = ('text', 'prepr', 'line', 'lbreak', 'softline', 'commaline',
  'group', 'seq', 'iter_seq', 'nest',
  'pprint', 'pformat', 'PrettyRepr')

def iter_seq(doc_it):
  docs = tuple(doc_it)
  return text(docs[0]) if len(docs) == 1 else _Seq(docs)

def seq(*docs):
  return iter_seq(docs)

def group(*docs):
  doc = text(docs[0]) if len(docs) == 1 else iter_seq(docs)

  # maintain the rule that groups cannot be empty, and
  # nested groups must be strictly smaller than their enclosing
  # group
  # NOTE: break can violate this rule
  if isinstance(doc, _Group) or not bool(doc):
    return doc

  return _Group(doc)

def text(string):
  '''Converts a string to a Doc.

  Docs are passed through unchanged. Other objects are passed to prepr.
  '''
  if isinstance(string, Doc): return string
  if isinstance(string, str): return _Text(string)
  return prepr(string)

def prepr(obj):
  '''Converts an object to a Doc, similar to repr.

  prepr(obj) -> obj.pretty(), if obj has a member pretty.
  prepr(obj) special-cases tuples, lists, dicts, sets, and frozensets.
  prepr(obj) -> text(repr(obj)) for all other objects
  '''
  if hasattr(obj, 'pretty'):
    return _Pretty(obj)

  if isinstance(obj, tuple): return ptuple(obj)
  if isinstance(obj, list): return plist(obj)
  if isinstance(obj, dict): return pdict(obj)
  if isinstance(obj, (set,frozenset)): return pset(obj)

  return _Text(repr(obj))



def pprint(*objs, **kws):
  """Pretty-print specified objects.

  pprint(*objs, file=sys.stdout, sep=line, end='\n', grouped=True, first=True,
         indent=0, prefix='', **kws)

  Keywords:
    file    - where to write the objects
    sep     - a Doc output between objects
    end     - a string written after any objs have been written
    grouped - whether to attempt to write on one line
    first   - if False, apply prefix and indent to first line
    indent  - indentation level (following first line)
    prefix  - written before all lines following the first, before any indent
    width   - desired maximum width
  """
  file    = kws.pop('file', sys.stdout)
  sep     = kws.pop('sep', line)
  end     = kws.pop('end', '\n')
  grouped = kws.pop('grouped', True)
  first   = kws.pop('first', True)
  indent  = kws.pop('indent', 0)
  prefix  = kws.pop('prefix', '')

  doc = sep.join(objs)
  if grouped:
    doc = group(doc)
  if not first:
    file.write(prefix)
    file.write(' ' * indent)
    kws['start_at'] = len(prefix) + indent

  doc.write_to(file, indent=indent, prefix=prefix, **kws)
  if end:
    file.write(end)

def pformat(*objs, **kws):
  """Return a string containing the pretty-printed objects.

  pformat(*objs, sep=line, end='', **kws)

  Keywords:
    sep     - a Doc output between objects
    end     - a string written after any objs have been written
    width   - desired maximum width
    indent  - indentation level (following first line)
    prefix  - written before all lines following the first, before any indent
  """
  sep = kws.pop('sep', line)
  end = kws.pop('end', '')

  sbuf = StringIO.StringIO()
  group(sep.join(objs)).write_to(sbuf, **kws)
  if end:
    sbuf.write(end)

  return sbuf.getvalue()


class PrettyRepr(object):
  '''Mixin class for objects which can pretty-print their representation.
  '''

  def pretty(self):
    'Return a Doc representing the object.'
    return text(super(PrettyRepr, self).__repr__())

  def __repr__(self):
    return self.pretty().oneline()

  def pprint(self, stream=None, end='\n', **kws):
    if stream is None:
      stream = sys.stdout

    self.pretty().write_to(stream, **kws)
    if end:
      stream.write(end)

  def pformat(self, **kws):
    sbuf = StringIO.StringIO()
    self.pretty().write_to(sbuf, **kws)
    return sbuf.getvalue()



class Doc(PrettyRepr):
  '''The intermediate formatting tree generated during pretty printing.

  Use text, prepr, group, seq, line, lbreak, and others to create Docs.

  Combine Docs with +, or use | to put a line between them.
  '''
  __slots__ = ()
  Text, Line, Break, GBegin, GEnd = range(5)

  def __add__(self, other):
    return seq(self, other)

  def __radd__(self, other):
    return seq(other, self)

  def __or__(self, other):
    'doc | obj -> seq(doc, line, obj)'
    return seq(self, line, other)

  def __ror__(self, other):
    return seq(other, line, self)

  def nest(self, indent):
    """Increase indentation level.

    doc.nest(x) == nest(x, doc)
    """
    return _Nest(indent, self)

  def join(self, docs):
    """Concatenate the docs, separated by this Doc."""
    return iter_seq(joinit(docs, self))

  def __str__(self):
    """Convert this Doc to a string.

    This returns the content of the Doc. Use __repr__ to return the
    structure of the Doc."""
    sbuf = StringIO.StringIO()
    self.write_to(sbuf)
    return sbuf.getvalue()

  def write_to(self, file, width=80, indent=0, **kws):
    """Write this doc to the specified file."""
    out = grow_groups(add_hp(
      find_group_ends(width, text_events(width, file.write, **kws))))

    out.next()
    self.send_to(out, indent)
    out.close()

  def oneline(self):
    """Convert this Doc to a one-line string."""
    sbuf = StringIO.StringIO()
    def dump():
      while True:
        event = yield
        if event[0] == Doc.Text:
          sbuf.write(event[1])
        elif event[0] == Doc.Line:
          sbuf.write(' ')

    out = dump()
    out.next()
    self.send_to(out, 0)
    return sbuf.getvalue()

  def pretty(self):
    """Return the structure of this Doc as a Doc."""
    return pfun(type(self).__name__, (getattr(self,s) for s in self.__slots__))


class _Text(Doc):
  __slots__ = ('text',)
  def __init__(self, text):
    assert '\n' not in text
    self.text = text

  def send_to(self, out, indent):
    out.send((Doc.Text, self.text))

  def __nonzero__(self):
    return bool(self.text)

class _Line(Doc):
  __slots__ = ()
  def send_to(self, out, indent):
    out.send((Doc.Line, indent))

  def __repr__(self):
    return '_Line()'

class _Break(Doc):
  __slots__ = ()
  def send_to(self, out, indent):
    out.send((Doc.Break, indent))

  def __repr__(self):
    return '_Break()'

  def __nonzero__(self):
    return False

class _Group(Doc):
  __slots__ = ('doc',)
  def __init__(self, doc):
    assert bool(doc)
    self.doc = doc # need to normalize this. maybe before construction?

  def send_to(self, out, indent):
    out.send((Doc.GBegin,))
    self.doc.send_to(out, indent)
    out.send((Doc.GEnd,))

class _Seq(Doc):
  __slots__ = ('docs',)
  def __init__(self, docs):
    self.docs = docs

  def send_to(self, out, indent):
    for doc in self.docs:
      text(doc).send_to(out, indent)

  def __nonzero__(self):
    return any(bool(doc) for doc in self.docs)


class _Nest(Doc):
  __slots__ = ('indent', 'doc')
  def __init__(self, indent, doc):
    self.indent = indent
    self.doc = doc

  def send_to(self, out, indent):
    self.doc.send_to(out, indent + self.indent)

  def __nonzero__(self):
    return bool(self.doc)

class _Pretty(Doc):
  __slots__ = ('obj',)
  def __init__(self, obj):
    self.obj = obj

  def send_to(self, out, indent):
    self.obj.pretty().send_to(out, indent)



def joinit(iterable, delimiter):
  it = iter(iterable)
  yield next(it)
  for x in it:
    yield delimiter
    yield x

def grow_groups(next):
  """Delays GEnd event until the next Line or Break.

  If a group is immediately followed by trailing text, we should take it
  into account when choosing whether to break the group. This stream
  transformer pushes GEnds past any trailing text.

  Furthermore, since GBegin can always be moved past text, grow_groups also
  pushes them to the right as far as possible. This will eliminate some
  groups if they contain only text.

  This avoids the problem where a group is just short enough to fit on a line,
  but is immediately followed by text, such as a comma, which will then go
  past the right margin.

  Be sure to call close() to send any suspended GEnds downstream.
  """
  next.next()
  pushing = 0
  pushing_b = 0

  try:
    while True:
      event = yield
      if event[0] == Doc.Text:
        next.send(event)
      elif event[0] == Doc.GBegin:
        if pushing:
          pushing_b += 1
        else:
          next.send(event)
      elif event[0] == Doc.GEnd:
        if pushing_b:
          pushing_b -= 1
        else:
          pushing += 1
      else:
        while pushing:
          next.send((Doc.GEnd,))
          pushing -= 1
        while pushing_b:
          next.send((Doc.GBegin,))
          pushing_b -= 1
        next.send(event)
  finally:
    while pushing:
      next.send((Doc.GEnd,))
      pushing -= 1
    while pushing_b:
      next.send((Doc.GBegin,))
      pushing_b -= 1


def add_hp(next):
  """Annotate events with their horizontal position.

  Assuming an infinitely-wide canvas, how many characters to the right is the
  _end_ of this event.
  """
  next.next()
  pos = 0

  while True:
    event = yield

    if event[0] == Doc.Text:
      pos += len(event[1])
      next.send((Doc.Text, pos, event[1]))

    elif event[0] == Doc.Line:
      pos += 1
      next.send((Doc.Line, pos, event[1]))

    elif event[0] == Doc.Break:
      next.send((Doc.Break, pos, event[1]))

    else:
      next.send((event[0], pos))


class Buf(object):
  """Sequence type providing O(1) insert at either end, and O(1) concatenation.
  """

  def __init__(self):
    self.head = []
    self.tail = self.head

  def append_left(self, item):
    self.head = [item, self.head]

  def append(self, item):
    last = self.tail
    self.tail = []
    last.append(item)
    last.append(self.tail)

  def extend(self, other):
    last = self.tail
    last.extend(other.head)
    self.tail = other.tail

  def __iter__(self):
    crnt = self.head

    while crnt:
      yield crnt[0]
      crnt = crnt[1]

def add_GBegin_pos(next):
  """Annotate GBegin events with the horizontal position of the end of the
  group.

  Because this waits until the entire group has been seen, so its latency and
  memory use are unbounded.
  """
  next.next()
  bufs = []

  while True:
    event = yield

    if event[0] == Doc.GBegin:
      bufs.append(Buf())

    elif bufs and event[0] == Doc.GEnd:
      pos = event[1]
      buf = bufs.pop()
      buf.append_left((Doc.GBegin, pos))
      buf.append(event)

      if bufs:
        buf[-1].extend(buf)
      else:
        for event in buf:
          next.send(event)

    elif bufs:
      bufs[-1].append(event)

    else:
      next.send(event)


def find_group_ends(width, next):
  """Annotate GBegin events with the horizontal position of the end of the
  group.

  GBegins corresponding to groups larger than the width will be annotated with
  'None'. This keeps memory usage and latency bounded, at the cost of some
  potential inaccuracy. (Zero-width groups may cause FindGroupEnds to declare
  a group too long, even if it is not.) Assumes that all groups have non-zero
  widths.
  """
  next.next()
  bufs = deque()
    # each entry in the queue corresponds to an incomplete group and contains
    # (1) the rightmost horizontal position this group can contain while staying
    #     on a line
    # (2) a Buf() containing the events of this group so far

  while True:
    event = yield
    if bufs:
      if event[0] == Doc.GEnd:
        _, buf = bufs.pop()
        buf.append_left((Doc.GBegin, event[1]))
        buf.append((Doc.GEnd, event[1]))
        if bufs:
          bufs[-1][1].extend(buf)
        else:
          for e in buf:
            next.send(e)

      else:
        if event[0] == Doc.GBegin:
          bufs.append((event[1] + width, Buf()))
        else:
          bufs[-1][1].append(event)

        while bufs[0][0] < event[1] or len(bufs) > width:
          next.send((Doc.GBegin, None))
          _, buf = bufs.popleft()
          for e in buf:
            next.send(e)

          if not bufs:
            break

    elif event[0] == Doc.GBegin:
      bufs.append((event[1] + width, Buf()))

    else:
      next.send(event)

def text_events(width, out, prefix='', start_at=0):
  """Write an annotated event stream to some method.

  Arguments:
    width - Desired maximum width for printing
    out   - A function which accepts strings (e.g. sys.stdout.write)
  Keywords:
    prefix - A string to put the start of each subsequent line. This counts
             against the given width.
    start_at - Assume this many characters have been printed on the first line
  """
  width -= len(prefix)
  newline = '\n' + prefix
  fits = 0
  hpl = width - start_at

  while True:
    event = yield

    if event[0] == Doc.Text:
      out(event[2])
    elif event[0] == Doc.Line:
      if fits:
        out(' ')
      else:
        out(newline)
        out(' ' * event[2])
        hpl = event[1] + width - event[2]
    elif event[0] == Doc.Break:
      if not fits:
        out(newline)
        out(' ' * event[2])
        hpl = event[1] + width - event[2]
    elif event[0] == Doc.GBegin:
      if fits:
        fits += 1
      elif event[1] != None and event[1] <= hpl:
        fits = 1
    else:
      if fits:
        fits -= 1


line = _Line()
lbreak = _Break()
softline = _Group(line)
commaline = seq(',', line)

def nest(indent, doc):
  return _Nest(indent, doc)

def pfun(name, args, indent=2):
  args = tuple(prepr(a) for a in args)
  if len(args) == 0:
    return seq(name, '()')
  return group(name, '(', lbreak, commaline.join(args), ')').nest(indent)

def pfun_(name, args):
  if len(args) == 0:
    return seq(name, '()')
  return group(name, '(', commaline.join(args), ')').nest(len(name)+1)

def pdict(dict):
  return group('{',
    commaline.join(group(prepr(k), ':', line, prepr(v)).nest(2)
      for (k,v) in dict.iteritems()), '}').nest(1)

def plist(list):
  return group('[', commaline.join(prepr(v) for v in list), ']').nest(1)

def ptuple(tup):
  if len(tup) == 0:
    return text('()')
  if len(tup) == 1:
    return group('(', prepr(tup[0]), ',)').nest(1)
  return group('(', commaline.join(prepr(v) for v in tup), ')').nest(1)

def pset(set):
  nm = type(set).__name__
  return seq(nm, '(', plist(sorted(set)), ')').nest(len(nm)+1)




def block_print(obj, width=80):
  def blk(next):
    next.next()
    try:
      while True:
        event = yield
        if event[0] == Doc.Line or event[0] == Doc.Break:
          next.send((Doc.GBegin,))
          next.send((event[0],0))
          next.send((Doc.GEnd,))

        elif event[0] == Doc.Text:
          next.send(event)
    finally:
      next.close()

  it = blk(grow_groups(add_hp(find_group_ends(width,
    text_events(width, sys.stdout.write)))))

  it.next()
  text(obj).send_to(it, 0)
  it.close()
  sys.stdout.write('\n')
