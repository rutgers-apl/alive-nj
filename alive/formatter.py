"""Transform an Alive internal representation into Alive syntax.
"""

from . import language as L
from .util import pretty
from .util.dispatch import singledispatch
import collections
import itertools

def get_insts(v):
  def walk(v, insts, seen):
    if v in seen or not isinstance(v, L.Instruction):
      return

    seen.add(v)

    for a in v.args():
      walk(a, insts, seen)

    insts.append(v)

  seen = set()
  insts = []
  walk(v, insts, seen)
  return insts

def format_parts(name, headers, src, tgt, fmt = None):
  """Return a printable Doc for an optimization.

  Usage:
    print format_parts('spam', [('Pre:', eggs)], bacon, spam)
  """

  fmt = fmt or Formatter()

  srci = [(fmt.name(i), format_doc(i, fmt, 0)) for i in get_insts(src)]
  cdefs = [(fmt.name(v), format_doc(v, fmt, 0))
              for v in L.constant_defs(tgt, map(lambda h: h[1], headers))]

  heads = pretty.iter_seq(
    pretty.seq(h, ' ', format_doc(t, fmt, 0).nest(len(h)+1), pretty.line)
    for h,t in headers)

  if isinstance(tgt, L.Instruction):
    fmt.ids[tgt] = fmt.name(src)

  tgti = [(fmt.name(i), format_doc(i, fmt, 0))
          for i in get_insts(tgt) if i not in fmt.ids]

  tgti.append((fmt.name(src), format_doc(tgt, fmt, 0)))

  # now, find the longest instruction or cdef name
  name_width = max(map(lambda d: len(d[0]), itertools.chain(srci, cdefs, tgti)))
  nest = name_width + 3

  def fmt_decl((id,decl)):
    return pretty.seq(id, ' ' * (name_width - len(id)), ' = ', decl).nest(nest)

  return pretty.seq(
    pretty.seq('Name: ', name, pretty.line) if name else pretty.seq(),
    heads,
    '  ',
    pretty.line.join(map(fmt_decl, srci)).nest(2),
    pretty.line,
    '=>',
    pretty.line,
    '  ',
    pretty.line.join(map(fmt_decl, itertools.chain(cdefs, tgti))).nest(2),
    pretty.line
  )

class Formatted(pretty.Doc):
  """Suspends formatting of a Transform or Alive term.

  Formats using line continuations, so should not generally be combined with
  other Docs or used with the functions from pretty, e.g., pprint.

  Usage:
    Formatted(opt).write_to(sys.stdout)
    log.debug('expression: %s', Formatted(expr, indent=2))
  """
  __slots__ = ('term', 'fmt', 'prec', 'kws')
  def __init__(self, term, formatter = None, prec = 0, **kws):
    self.term = term
    self.fmt = formatter or Formatter()
    self.prec = prec
    self.kws = kws

  def send_to(self, out, indent):
    format_doc(self.term, self.fmt, self.prec).send_to(out, indent)

  def __str__(self):
    import StringIO
    sbuf = StringIO.StringIO()
    self.write_to(sbuf, **self.kws)
    return sbuf.getvalue()

  def write_to(self, file, width=80, indent=0, **kws):
    """Write this doc to the specified file."""
    it = pretty.grow_groups(pretty.add_hp(pretty.find_group_ends(width,
      text_events_line_continue(width, file.write, **kws))))
    it.next()
    self.send_to(it, indent)
    it.close()


class Formatter(object):
  def __init__(self):
    self.ids = {}
    self.names = set()
    self.fresh = 0

  def name(self, term):
    """Generates a fresh name for this term, or returns the previously-generated
    name.
    """
    if term in self.ids: return self.ids[term]

    prefix = 'C' if isinstance(term, L.Constant) else '%'

    if isinstance(term, (L.Input, L.Instruction)) and term.name:
      name = term.name
    else:
      name = prefix + str(self.fresh)
      self.fresh += 1

    while name in self.names:
      name = prefix + str(self.fresh)
      self.fresh += 1

    self.ids[term] = name
    self.names.add(name)
    return name

  def operand(self, term, prec = 0, ty = None):
    """Use the name for this term, if any, or format it.
    """

    if term in self.ids or isinstance(term, L.Instruction):
      term = pretty.text(self.name(term))
    else:
      term = Formatted(term, self, prec)

    if ty is None:
      return term

    return pretty.seq(str(ty), ' ', term)

@singledispatch
def format_doc(term, formatter, precedence):
  """format_doc(term, formatter, precedence) -> Doc
  """
  raise NotImplementedError("Can't format " + type(term).__name__)

@format_doc.register(pretty.Doc)
def _(doc, fmt, prec):
  return doc

@format_doc.register(L.Input)
def _(term, fmt, prec):
  return pretty.text(fmt.name(term))

@format_doc.register(L.BinaryOperator)
def _(term, fmt, prec):
  return pretty.group(
    term.code,
    ' ',
    pretty.seq(
      pretty.text(' ').join(term.flags),
      ' ') if term.flags else pretty.seq(),
    fmt.operand(term.x, 0, term.ty),
    ',',
    pretty.line,
    fmt.operand(term.y, 0)).nest(len(term.code) + 1)

@format_doc.register(L.ConversionInst)
def _(term, fmt, prec):
  name = fmt.name(term)
  body = pretty.seq(
    term.code,
    ' ',
    fmt.operand(term.arg, 0, term.src_ty))

  if term.ty:
    body = pretty.seq(body, pretty.line, 'to ', str(term.ty))

  return pretty.group(body).nest(len(term.code) + 1)

@format_doc.register(L.IcmpInst)
def _(term, fmt, prec):
  return pretty.group(
    'icmp ',
    term.pred,
    pretty.line,
    fmt.operand(term.x, 0, term.ty),
    ',',
    pretty.line,
    fmt.operand(term.y, 0)).nest(5)

@format_doc.register(L.FcmpInst)
def _(term, fmt, prec):
  return pretty.group(
    'fcmp',
    pretty.iter_seq(pretty.seq(' ', f) for f in term.flags),
    pretty.seq(' ', term.pred) if term.pred else '',
    pretty.line if term.flags or term.pred else ' ',
    fmt.operand(term.x, 0, term.ty),
    ',',
    pretty.line,
    fmt.operand(term.y, 0)).nest(5)

@format_doc.register(L.SelectInst)
def _(term, fmt, prec):
  name = fmt.name(term)
  return pretty.group(
    'select ',
    fmt.operand(term.sel, 0),
    ',',
    pretty.line,
    fmt.operand(term.arg1, 0, term.ty1),
    ',',
    pretty.line,
    fmt.operand(term.arg2, 0, term.ty2)).nest(7)

@format_doc.register(L.FreezeInst)
def _(term, fmt, prec):
  name = fmt.name(term)
  return pretty.group('freeze ', fmt.operand(term.x, 0)).nest(7)

@format_doc.register(L.Literal)
@format_doc.register(L.FLiteral)
def _(term, fmt, prec):
  return pretty.text(str(term.val))

@format_doc.register(L.UndefValue)
def _(term, fmt, prec):
  return pretty.text('undef')

@format_doc.register(L.PoisonValue)
def _(term, fmt, prec):
  return pretty.text('poison')

_bin_cnxp_prec = {
  '*': 9, '/': 9, '/u': 9, '%': 9, '%u': 9,
  '+': 8, '-': 8,
  '>>': 7, '<<': 7, 'u>>': 7,
  '&': 6,
  '^': 5,
  '|': 4,
  '&&': 2,
  '||': 1,
}
_bin_cnxp_lassoc = {'-', '/', '/u', '%', '%u', '<<', '>>', 'u>>'}

def _gather(term, prec, peers):
  if not isinstance(term, L.BinaryCnxp) or prec != _bin_cnxp_prec[term]:
    peers.append(term)
    return

  gather(term.x, prec, peers)


@format_doc.register(L.BinaryCnxp)
def _(term, fmt, prec):
  peers = []

  op_prec = _bin_cnxp_prec[term.code]

  def gather(term):
    if not isinstance(term, L.BinaryCnxp) or \
        op_prec != _bin_cnxp_prec[term.code]:
      return fmt.operand(term, op_prec)

    return pretty.seq(
      gather(term.x),
      pretty.line,
      term.code,
      ' ',
      fmt.operand(term.y, op_prec)
        if term.code in _bin_cnxp_lassoc
        else gather(term.y))

  body = gather(term)

  if prec >= op_prec or 3 < prec < 8:
    body = pretty.seq('(', body, ')')

  return pretty.group(body).nest(2)

@format_doc.register(L.UnaryCnxp)
def _(term, fmt, prec):
  return pretty.seq(term.code, fmt.operand(term.x, 10))

@format_doc.register(L.FunCnxp)
@format_doc.register(L.FunPred)
def _(term, fmt, prec):
  return pretty.group(
    term.code,
    '(',
    pretty.lbreak if term._args else pretty.seq(),
    pretty.seq(',', pretty.line).join(fmt.operand(a, 0) for a in term._args),
    ')').nest(2)

@format_doc.register(L.AndPred)
def _(term, fmt, prec):
  if not term.clauses:
    return pretty.text('true')

  body = pretty.seq(pretty.line, '&& ').join(fmt.operand(a, 2).nest(3)
    for a in term.clauses)

  if prec > 2:
    body = pretty.seq('(', body, ')')

  return pretty.group(body)

@format_doc.register(L.OrPred)
def _(term, fmt, prec):
  if not term.clauses:
    return pretty.text('!true')

  body = pretty.seq(pretty.line, '|| ').join(fmt.operand(a, 1).nest(3)
    for a in term.clauses)

  if prec > 1:
    body = pretty.seq('(', body, ')')

  return pretty.group(body)

@format_doc.register(L.NotPred)
def _(term, fmt, prec):
  return pretty.seq('!', fmt.operand(term.p, 10))

_cmp_codes = {
  'eq':  '==',
  'ne':  '!=',
  'slt': '<',
  'sle': '<=',
  'sgt': '>',
  'sge': '>=',
  'ult': 'u<',
  'ule': 'u<=',
  'ugt': 'u>',
  'uge': 'u>=',
}

@format_doc.register(L.Comparison)
def _(term, fmt, prec):
  body = pretty.seq(
    fmt.operand(term.x, 3).nest(3),
    pretty.line,
    _cmp_codes[term.op],
    ' ',
    fmt.operand(term.y, 3).nest(3)
  )

  if prec > 3:
    body = pretty.seq('(', body, ')')

  return pretty.group(body)

def text_events_line_continue(width, out, prefix='', suffix=' \\', start_at=0):
  width -= len(prefix)
  newline = '\n' + prefix
  fits = 0
  broken = 0
  hp_eol = width - start_at

  while True:
    event = yield

    if event[0] == pretty.Doc.Text:
      out(event[2])

    elif event[0] == pretty.Doc.Line and fits:
      out(' ')

    elif event[0] == pretty.Doc.Line or \
        (event[0] == pretty.Doc.Break and not fits):
      hp_eol = event[1] + width - event[2]
      if broken:
        out(suffix)
        hp_eol -= len(suffix)
      out(newline)
      out(' ' * event[2])

    elif event[0] == pretty.Doc.GBegin:
      if fits:
        fits += 1
      elif event[1] != None and event[1] <= hp_eol:
        fits = 1
      elif broken:
        broken += 1
      else:
        broken = 1
        hp_eol -= len(suffix)

    elif event[0] == pretty.Doc.GEnd:
      if fits:
        fits -= 1
      else:
        broken -= 1
