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

__all__ = ('text', 'prepr', 'line', 'lbreak', 'softline',
  'group', 'seq', 'iter_seq', 'nest',
  'pprint', 'pformat')

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

class Doc(object):
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
    '''doc.nest(i) -> doc
    
    Indents lines after the first by i spaces.
    '''
    return _Nest(indent, self)
  
  def join(self, docs):
    '''d.join(iterable) -> doc
    
    Concatenate the documents in iterable, separated by d.
    '''
    return iter_seq(joinit(docs, self))

  def _stream_to(self, width, indent, stream):
    out = GrowGroups(AddHP(
      FindGroupEnds(width, TextEvents(width, stream.write))))
    self.send(out, indent)
    out.flush()

  def pprint(self, width=80, indent=0, stream=None):
    if stream is None: stream = sys.stdout
    self._stream_to(width, indent, stream)
    stream.write('\n')

  def pformat(self, width=80, indent=0):
    sbuf = StringIO.StringIO()
    self._stream_to(width, indent, sbuf)
    return sbuf.getvalue()

  def oneline(self):
    sbuf = StringIO.StringIO()
    def out(event):
      if event[0] == Doc.Text:
        sbuf.write(event[1])
      elif event[0] == Doc.Line:
        sbuf.write(' ')
    
    self.send(out, 0)
    return sbuf.getvalue()

  def pretty(self):
    return group(type(self).__name__, '(', lbreak,
      (',' + line).join(prepr(getattr(self,s)) for s in self.__slots__),
      ')').nest(2)

  def __repr__(self):
    return self.pretty().oneline()

class _Text(Doc):
  __slots__ = ('text',)
  def __init__(self, text):
    assert '\n' not in text
    self.text = text
  
  def send(self, out, indent):
    out((Doc.Text, self.text))

  def __nonzero__(self):
    return bool(self.text)

class _Line(Doc):
  __slots__ = ()
  def send(self, out, indent):
    out((Doc.Line, indent))

  def __repr__(self):
    return '_Line()'

class _Break(Doc):
  __slots__ = ()
  def send(self, out, indent):
    out((Doc.Break, indent))

  def __repr__(self):
    return '_Break()'

  def __nonzero__(self):
    return False

class _Group(Doc):
  __slots__ = ('doc',)
  def __init__(self, doc):
    assert bool(doc)
    self.doc = doc # need to normalize this. maybe before construction?

  def send(self, out, indent):
    out((Doc.GBegin,))
    self.doc.send(out, indent)
    out((Doc.GEnd,))

class _Seq(Doc):
  __slots__ = ('docs',)
  def __init__(self, docs):
    self.docs = docs

  def send(self, out, indent):
    for doc in self.docs:
      text(doc).send(out, indent)

  def __nonzero__(self):
    return any(bool(doc) for doc in self.docs)


class _Nest(Doc):
  __slots__ = ('indent', 'doc')
  def __init__(self, indent, doc):
    self.indent = indent
    self.doc = doc

  def send(self, out, indent):
    self.doc.send(out, indent + self.indent)

  def __nonzero__(self):
    return bool(self.doc)

class _Pretty(Doc):
  __slots__ = ('obj',)
  def __init__(self, obj):
    self.obj = obj
    
  def send(self, out, indent):
    self.obj.pretty().send(out, indent)



def joinit(iterable, delimiter):
  it = iter(iterable)
  yield next(it)
  for x in it:
    yield delimiter
    yield x


class GrowGroups(object):
  '''Delays GEnd event until the next Line or Break.

  If a group is immediately followed by trailing text, we should take it
  into account when choosing whether to break the group. This stream
  transformer pushes GEnds past any trailing text.
  
  Furthermore, since GBegin can always be moved past text, GrowGroups also
  pushes them to the right as far as possible. This will eliminate some
  groups if they contain only text.
  '''
  def __init__(self, next):
    self.next = next
    self.pushing = 0    # number of GEnds being delayed
    self.pushing_b = 0  # number of GBegins being delayed

  def __call__(self, event):
    if event[0] == Doc.Text:
      self.next(event)
    elif event[0] == Doc.GBegin:
      if self.pushing:
        self.pushing_b += 1
      else:
        self.next(event)
    elif event[0] == Doc.GEnd:
      if self.pushing_b:
        self.pushing_b -= 1
      else:
        self.pushing += 1
    else:
      self.flush()
      self.next(event)

  def flush(self):
    '''Stream any delayed GEnds and GBegins.

    Unless the stream terminates with a line break, or contains no groups,
    GrowGroups will hang on to the final GEnd(s) unless they are flushed out.
    '''
    while self.pushing:
      self.next((Doc.GEnd,))
      self.pushing -= 1
    while self.pushing_b:
      self.next((Doc.GBegin,))
      self.pushing_b -= 1

class AddHP(object):
  '''Annotate events with their horizontal position.
  
  Assuming an infinitely-wide canvas, how many characters to the right is the
  _end_ of this event.
  '''

  def __init__(self, next):
    self.next = next
    self.pos = 0

  def __call__(self, event):
    if event[0] == Doc.Text:
      self.pos += len(event[1])
      self.next((Doc.Text, self.pos, event[1]))
    
    elif event[0] == Doc.Line:
      self.pos += 1
      self.next((Doc.Line, self.pos, event[1]))
    
    elif event[0] == Doc.Break:
      self.next((Doc.Break, self.pos, event[1]))
    
    else:
      self.next((event[0], self.pos))


class Buf(object):
  'Sequence type providing O(1) insert at either end, and O(1) concatenation.'
  
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


class AddGBeginPos(object):
  '''
  Annotate GBegin events with the horizontal position of the end of the group.
  
  Because this waits until the entire group has been seen, so its latency and
  memory use are unbounded.
  '''
  def __init__(self, next):
    self.next = next
    self.bufs = []

  def __call__(self, event):
    if event[0] == Doc.GBegin:
      self.bufs.append(Buf())
    
    elif self.bufs and event[0] == Doc.GEnd:
      pos = event[1]
      buf = self.bufs.pop()
      buf.append_left((Doc.GBegin, pos))
      buf.append(event)
      if bufs:
        bufs[-1].extend(buf)
      else:
        for event in buf:
          self.next(event)

    elif self.bufs:
      bufs[-1].append(event)

    else:
      self.next(event)

class FindGroupEnds(object):
  '''
  Annotate GBegin events with the horizontal position of the end of the group.
  
  GBegins corresponding to groups larger than the width will be annotated with
  'None'. This keeps memory usage and latency bounded, at the cost of some
  potential inaccuracy. (Zero-width groups may cause FindGroupEnds to declare
  a group too long, even if it is not.)
  '''
  def __init__(self, width, next):
    self.next = next
    self.width = width
    self.bufs = deque()

  def __call__(self, event):
    if self.bufs:
      if event[0] == Doc.GEnd:
        _, buf = self.bufs.pop()
        buf.append_left((Doc.GBegin, event[1]))
        buf.append((Doc.GEnd, event[1]))
        if self.bufs:
          self.bufs[-1][1].extend(buf)
        else:
          for event in buf:
            self.next(event)
      
      else:
        if event[0] == Doc.GBegin:
          self.bufs.append((event[1] + self.width, Buf()))
        else:
          self.bufs[-1][1].append(event)
        
        while self.bufs[0][0] < event[1] or len(self.bufs) > self.width:
          self.next((Doc.GBegin, None))
          _, buf = self.bufs.popleft()
          for e in buf:
            self.next(e)

          if not self.bufs:
            break

    elif event[0] == Doc.GBegin:
      self.bufs.append((event[1] + self.width, Buf()))
    else:
      self.next(event)

class TextEvents(object):
  '''Write an annotated event stream to some method.
  
  This will typically be called with sys.stdout.write or something similar.
  '''

  def __init__(self, width, out):
    self.width = width
    self.out = out
    self.fits = 0
    self.hpl = width

  def __call__(self, event):
    if event[0] == Doc.Text:
      self.out(event[2])
    elif event[0] == Doc.Line:
      if self.fits:
        self.out(' ')
      else:
        self.out('\n' + ' ' * event[2])
        self.hpl = event[1] + self.width - event[2]
    elif event[0] == Doc.Break:
      if not self.fits:
        self.out('\n' + ' ' * event[2])
        self.hpl = event[1] + self.width - event[2]
    elif event[0] == Doc.GBegin:
      if self.fits:
        self.fits += 1
      elif event[1] != None and event[1] <= self.hpl:
        self.fits = 1
    else:
      if self.fits:
        self.fits -= 1


line = _Line()
lbreak = _Break()
softline = _Group(line)

def nest(indent, doc):
  return _Nest(indent, doc)
  

def pdict(dict):
  return group('{',
    (',' + line).join(group(prepr(k), ':', line, prepr(v)).nest(2)
      for (k,v) in dict.iteritems()), '}').nest(1)

def plist(list):
  return group('[', (',' + line).join(prepr(v) for v in list), ']').nest(1)

def ptuple(tup):
  if len(tup) == 0:
    return text('()')
  if len(tup) == 1:
    return group('(', prepr(tup[0]), ',)').nest(1)
  return group('(', (',' + line).join(prepr(v) for v in tup), ')').nest(1)

def pset(set):
  nm = type(set).__name__
  return seq(nm, '(', plist(sorted(set)), ')').nest(len(nm)+1)

def pprint(obj, width=80, indent=0, stream=None):
  text(obj).pprint(width, indent, stream)

def pformat(obj, width=80, indent=0):
  return text(obj).pformat(width, indent)




def block_print(obj, width=80):
  next = GrowGroups(AddHP(FindGroupEnds(width, TextEvents(width, sys.stdout.write))))

  def blk(event):
    if event[0] == Doc.Line or event[0] == Doc.Break:
      next((Doc.GBegin,))
      next((event[0],0))
      next((Doc.GEnd,))

    elif event[0] == Doc.Text:
      next(event)
  
  text(obj).send(blk, 0)
  next.flush()
  sys.stdout.write('\n')
