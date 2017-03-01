import collections, sys
from . import language as L
from .transform import Transform, Formatter
from pyparsing.pyparsing import *

ParserElement.enablePackrat()
ParserElement.setDefaultWhitespaceChars(' \t')

class Phase:
  Source, Target, Pre = range(3);

  names = {
    Source: "Source",
    Target: "Target",
    Pre: "Precondition",
  }

class Ast(object):
  def __init__(self, pstr, loc, toks):
    self.str = pstr
    self.loc = loc
    self.toks = toks

  def __repr__(self):
    return "%s('', %s, %s)" % (self.__class__.__name__, self.loc, self.toks)

  def _fatal(self, msg):
    if isinstance(msg, list):
      msg = '\n'.join(msg)
    raise ParseFatalException(self.str, self.loc, msg)


class TypeAst(Ast):
  pass

class IntTypeAst(TypeAst):
  def eval(self, ids, phase):
    return L.IntType(self.toks[1])

class FloatTypeAst(TypeAst):
  codes = {
    'half': L.HalfType(),
    'float': L.SingleType(),
    'double': L.DoubleType(),
    'fp128': L.FP128Type(),
    'x86_fp80': L.X86FP80Type(),
  }

  def eval(self, ids, phase):
    return self.codes[self.toks[0]]

class OptionalTypeAst(TypeAst):
  def eval(self, ids, phase):
    if self.toks:
      self.loc = self.toks[0].loc  # is this ever needed?
      return self.toks[0].eval(ids, phase)

    return None




class ValAst(Ast):
  pass

class LiteralAst(ValAst):
  def value(self, ty, ids, phase):
    # NOTE: do anything with the type?
    tok = self.toks[0]
    if '.' in tok:
      x = float(tok)
      if x == 0.0 and tok[0] == '-':
        return L.FLiteralMinusZero()
      return L.FLiteralVal(x)
    return L.Literal(int(tok))

class LitWordAst(ValAst):
  def value(self, ty, ids, phase):
    v = self.toks[0]

    if v == 'true':
      return L.Literal(1)
    if v == 'false':
      return L.Literal(0)
    if v == 'undef':
      return L.UndefValue(ty)
    if v == 'poison':
      return L.PoisonValue()
    if v == 'nan':
      return L.FLiteralNaN()
    if v == 'inf':
      return L.FLiteralPlusInf()
    if v == '-inf':
      return L.FLiteralMinusInf()

    self._fatal('Unrecognized literal {0!r}'.format(v))

class Name(ValAst):
  def __init__(self, pstr, loc, tok):
    self.id = tok[0]
    self.loc = loc
    self.str = pstr

  def __str__(self): return self.id

  def __repr__(self):
    return "%s(%s,%d)" % (self.__class__.__name__, self.id, self.loc)

  def value(self, ty, ids, phase):
    if self.id in ids:
      return ids[self.id]

    if phase == Phase.Source:
      ids[self.id] = self.cls(self.id)
      return ids[self.id]

    self._fatal('Input {} not in source'.format(self.id))

class Register(Name):  cls = L.Input
class ConstName(Name): cls = L.Symbol

def yieldPairs(toks):
  it = iter(toks)
  while True:
    try:
      a = it.next()
      b = it.next()
      yield a,b
    except StopIteration:
      break


class UnaryExpr(ValAst):
  def value(self, ty, ids, phase):
    if phase == Phase.Source:
      self._fatal('Expressions not permitted in source')

    op = L.UnaryCnxp.codes[self.toks[0][0]]
    x = self.toks[0][1].value(ty, ids, phase)
    return op(x)

class BinaryExpr(ValAst):
  def value(self, ty, ids, phase):
    if phase == Phase.Source:
      self._fatal('Expressions not permitted in source')

    x = self.toks[0][0].value(ty, ids, phase)
    for op, v in yieldPairs(self.toks[0][1:]):
      y = v.value(ty, ids, phase)
      x = L.BinaryCnxp.codes[op](x, y)

    return x


class PreconditionAst(Ast):
  pass

class TrueAst(PreconditionAst):
  def condition(self, ids):
    return L.TruePred


comparators = {
  '==': 'eq',
  '!=': 'ne',
  '<': 'slt',
  '<=': 'sle',
  '>': 'sgt',
  '>=': 'sge',
  'u<': 'ult',
  'u<=': 'ule',
  'u>': 'ugt',
  'u>=': 'uge',
  }


class CmpAst(PreconditionAst):
  def condition(self, ids):
    x = self.toks[0].value(None, ids, Phase.Pre)
    conds = []
    for opname,rhs in yieldPairs(self.toks[1:]):
      op = comparators[opname]
      y = rhs.value(None, ids, Phase.Pre)
      conds.append(L.Comparison(op,x,y))
      x = y
    if len(conds) == 1:
      return conds[0]
    else:
      return L.AndPred(*conds)

class NotAst(PreconditionAst):
  def condition(self, ids):
    return L.NotPred(self.toks[0][0].condition(ids))

class AndAst(PreconditionAst):
  def condition(self, ids):
    return L.AndPred(*(p.condition(ids) for p in self.toks[0]))

class OrAst(PreconditionAst):
  def condition(self, ids):
    return L.OrPred(*(p.condition(ids) for p in self.toks[0]))



class FunAst(ValAst, PreconditionAst):
  'Common expression type for <name>(<args>). Supports value and condition.'

  def condition(self, ids):
    name = self.toks[0]

    if name not in L.FunPred.codes:
      self._fatal('Unknown predicate: ' + name)

    pred = L.FunPred.codes[name]

    args = tuple(a.value(None, ids, Phase.Pre) for a in self.toks[1:])

    try:
      return pred(*args)
    except L.BadArgumentCount, e:
      self._fatal('Wrong number of arguments to {0}: {1}'.format(name, e))
    except L.BadArgumentKind, e:
      self.toks[e.idx+1]._fatal('{} {}'.format(name, e))

  def value(self, ty, ids, phase):
    if phase == Phase.Source:
      self._fatal('Expressions not permitted in source')

    # determine if this is a valid function
    name = self.toks[0]

    if name not in L.FunCnxp.codes:
      self._fatal('Unknown function: ' + name)

    fun = L.FunCnxp.codes[name]

    args = tuple(a.value(None, ids, phase) for a in self.toks[1:])

    try:
      return fun(*args)
    except L.BadArgumentCount, e:
      self._fatal('Wrong number of arguments to {0}: {1}'.format(name, e))
    except L.BadArgumentKind, e:
      self.toks[e.idx+1]._fatal('{} {}'.format(name, e))


class CDefAst(Ast):
  """Represents <cname> = <cexpr>."""

  def eval(self, ids, phase):
    if phase != Phase.Target:
      self._fatal('Constant definitions only permitted in target')

    c = self.toks.lhs.id

    if c in ids:
      self._fatal('Redefinition of ' + r)

    val = self.toks.rhs.value(None, ids, phase)

    ids[c] = val

class OpInstAst(Ast):
  'Represents <reg> = <instr>'

  def eval(self, ids, phase):
    r = self.toks.lhs.id

    inst = self.toks.op.inst(r, ids, phase)

    if r in ids:
      self._fatal('Redefinition of ' + r)

    ids[r] = inst

  def name(self):
    return self.toks.lhs.id

class InstAst(Ast):
  pass

class CopyOpAst(InstAst):
  def inst(self, name, ids, phase):
    ty = self.toks.ty.eval(ids, phase)
    return self.toks.x.value(ty, ids, phase)

  # TODO: replace this entirely


class BinOpAst(InstAst):
  def inst(self, name, ids, phase):
    op = self.toks.code
    ty = self.toks.ty.eval(ids, phase)

    v1 = self.toks.x.value(ty, ids, phase)
    v2 = self.toks.y.value(ty, ids, phase)
    flags = [tok.value for tok in self.toks.flags]

    return op(v1,v2,ty=ty,flags=flags,name=name)
    # FIXME: validate flags


class ConvOpAst(InstAst):
  def inst(self, name, ids, phase):
    op  = self.toks.code
    sty = self.toks.sty.eval(ids, phase)
    rty = self.toks.rty.eval(ids, phase)
    x   = self.toks.x.value(sty, ids, phase)

    return op(x, src_ty=sty, dest_ty=rty, name=name)


class ICmpAst(InstAst):
  def inst(self, name, ids, phase):
    ty = self.toks.ty.eval(ids, phase)
    x  = self.toks.x.value(ty, ids, phase)
    y  = self.toks.y.value(ty, ids, phase)

    return L.IcmpInst(self.toks.cmp[0], x, y, ty, name)
    # FIXME: validate cmp?

class FCmpAst(InstAst):
  def inst(self, name, ids, phase):
    ty = self.toks.ty.eval(ids, phase)
    x  = self.toks.x.value(ty, ids, phase)
    y  = self.toks.y.value(ty, ids, phase)
    flags = tuple(tok.value for tok in self.toks.flags)

    return L.FcmpInst(self.toks.cmp[0], x, y, ty, flags, name)


class SelectAst(InstAst):
  def inst(self, name, ids, phase):
    toks = self.toks

    pty = toks.ty.eval(ids, phase)
    if pty is not None and pty != L.IntType(1):
      toks.ty._fatal('Only i1 permitted')

    tty = toks.tty.eval(ids, phase)
    fty = toks.fty.eval(ids, phase)

    sel = toks.pred.value(pty, ids, phase)
    tval = toks.tval.value(tty, ids, phase)
    fval = toks.fval.value(fty, ids, phase)

    return L.SelectInst(sel, tval, fval, tty, fty, name)

class FreezeAst(InstAst):
  def inst(self, name, ids, phase):
    toks = self.toks
    ty = self.toks.ty.eval(ids, phase)
    x  = self.toks.x.value(ty, ids, phase)

    return L.FreezeInst(x, ty, name)

# class AllocaExpr(InstAst):
#   def getOp(self, name, ids, phase):
# #     print 'AllocaExpr.getOp', self.toks.dump()
#     if 'num' in self.toks:
#       num_ty = self.toks.num_ty.evalInt(ids, phase)
#       num = self.toks.num.getValue(num_ty, ids, phase)
#     else:
#       num_ty = IntType()
#       num = ConstantVal(1, num_ty)
#       ids[num.getUniqueName()] = num
#
#     align = self.toks.align if 'align' in self.toks else 0
#     ty = self.toks.ty.eval(ids, phase)
#
#     try:
#       return Alloca(self.toks.ty.eval(ids, phase), num_ty, num, align)
#     except AssertionError, e:
#       self._fatal(str(e))
#
# class GEPExpr(InstAst):
#   def getOp(self, name, ids, phase):
#     ty = self.toks.ptr_t.evalPtr(ids,phase)
#     ptr = self.toks.ptr.getValue(ty, ids, phase)
#     flds = []
#     for te, ve in yieldPairs(self.toks.flds):
#       t = te.evalInt(ids,phase)
#       v = ve.getValue(ty,ids,phase)
#       flds += [t,v]
#
#     return GEP(ty, ptr, flds, 'inbounds' in self.toks)
#
# class LoadExpr(InstAst):
#   def getOp(self, name, ids, phase):
#     ty = self.toks.ty.evalPtr(ids, phase)
#     x = self.toks.x.getValue(ty, ids, phase)
#     align = self.toks.get('align', defaultValue = 0)
#
#     return Load(ty, x, align)
#
# class StoreExpr(InstAst):
#   def eval(self, ids, phase):
#     val_t = self.toks.val_t.eval(ids, phase)
#     val   = self.toks.val.getValue(val_t, ids, phase)
#     ptr_t = self.toks.ptr_t.evalPtr(ids, phase)
#     ptr   = self.toks.ptr.getValue(ptr_t, ids, phase)
#     align = self.toks.get('align', defaultValue = 0)
#
#     s = Store(val_t, val, ptr_t, ptr, align)
#     ids[s.getUniqueName()] = s
#

posnum = Word(nums).setParseAction(lambda s,l,t: int(t[0]))

ty = ('i' + posnum).setParseAction(IntTypeAst) \
  | oneOf('half float double fp128 x86_fp80').setParseAction(FloatTypeAst)
ty.setName('type')

opt_ty = Optional(ty).setParseAction(OptionalTypeAst)


lit = Regex("-?\d+(?:.\d+)?").setName("Literal").setParseAction(LiteralAst)

reg = Word('%', srange('[a-zA-Z0-9_.]')).setParseAction(Register)
reg.setName('Register')

cname = Word('C', srange('[0-9]'), asKeyword=True).setParseAction(ConstName)
cname.setName('ConstName')

ident = ~ty + ~cname + \
  Word(srange("[a-zA-Z]"), srange(r"[a-zA-Z0-9_.]"), asKeyword=True)
ident.setName("Identifier")

cexpr = Forward()

special_arg = oneOf('true false null nan inf -inf').setParseAction(LitWordAst)
arg = reg | special_arg | cexpr

args = delimitedList(arg)


cfunc = ident + Suppress('(') + args + Suppress(')')
cfunc.setParseAction(FunAst)

catom = cname | lit | cfunc
catom.setName('const, literal, or function')


cexpr << infixNotation(catom,
      [(Regex(r'~|-(?!\s*\d)'), 1, opAssoc.RIGHT, UnaryExpr),
       (Regex(r'\*|/u?|%(?= )|%u'), 2, opAssoc.LEFT, BinaryExpr),  # require space after % to avoid matching registers
       (oneOf('+ -'), 2, opAssoc.LEFT, BinaryExpr),
       (oneOf('<< >> u>>'), 2, opAssoc.LEFT, BinaryExpr),
       (Literal('&'), 2, opAssoc.LEFT, BinaryExpr),
       (Literal('^'), 2, opAssoc.LEFT, BinaryExpr),
       (Literal('|'), 2, opAssoc.LEFT, BinaryExpr),
      ])
cexpr.setName('ConstExpr')

pre_comp_op = oneOf('== != < <= > >= u< u<= u> u>=').setName('comparison operator')

pre_lit = Literal("true").setParseAction(TrueAst)
pre_comp = (cexpr + OneOrMore(pre_comp_op - cexpr)).setParseAction(CmpAst)
pre_comp.setName('comparison')

pre_atom = pre_lit | pre_comp | cfunc

pre = infixNotation(pre_atom,
      [(Suppress('!'), 1, opAssoc.RIGHT, NotAst),
       (Suppress('&&'), 2, opAssoc.LEFT, AndAst),
       (Suppress('||'), 2, opAssoc.LEFT, OrAst),
      ])
pre.setName('precondition')

special_lit = oneOf('true false undef poison null nan inf -inf').setParseAction(LitWordAst)
operand = (reg | special_lit | cexpr).setName("Operand")

comma = Suppress(',')
equals = Suppress('=')

copyOp = opt_ty('ty') + operand('x')
copyOp.setParseAction(CopyOpAst)

def opCode(codes):
  def pa(s,l,t):
    if t[0] in codes:
      return codes[t[0]]
    else:
      raise ParseException(s,l,"Not an appropriate code")

#   return oneOf(' '.join(codes))('code').setParseAction(traceParseAction(pa)).setDebug()
  return ident('code').setParseAction(pa, callDuringTry=True)

flags = Group(ZeroOrMore(locatedExpr(oneOf('nsw nuw exact nnan ninf nsz arcp fast'))))

binOp = (opCode(L.BinaryOperator.codes) - flags('flags') - opt_ty('ty')
      - operand('x') - comma - operand('y')).setParseAction(BinOpAst)

opt_rty = (Suppress('to') - ty | FollowedBy(LineEnd())).setParseAction(OptionalTypeAst)

convOp = (opCode(L.ConversionInst.codes) - opt_ty('sty') - operand('x')
          - opt_rty('rty')).setParseAction(ConvOpAst)

cmpOp = Optional(ident, '')

# NOTE: are anonymous predicates actually necessary?
icmp = Literal('icmp') - cmpOp('cmp') - opt_ty('ty') - operand('x') - comma - operand('y')
icmp.setParseAction(ICmpAst)

fcmp = Literal('fcmp') - flags('flags') - cmpOp('cmp') - opt_ty('ty') - operand('x') - comma - operand('y')
fcmp.setParseAction(FCmpAst)

select = Literal('select') - opt_ty('ty') + operand('pred') \
  + comma + opt_ty('tty') + operand('tval') + comma + opt_ty('fty') + operand('fval')
select.setParseAction(SelectAst)

# # Ending with an optional segment consumes the newline
# alloca = Suppress('alloca') - (ty | FollowedBy(comma|LineEnd()))('ty').setParseAction(OptionalTypeAst) \
#   + (comma + opt_ty('num_ty') + operand('num') | FollowedBy(comma|LineEnd())) \
#   + (comma + Suppress('align') + posnum('align') | FollowedBy(LineEnd()))
# alloca.setName('alloca')
# alloca.setParseAction(AllocaExpr)
#
# # alloca = Suppress('alloca') + opt_ty('ty') + Optional(comma + opt_ty('num_ty') + operand('num')) \
# #     + comma + Suppress('align') + posnum('align') \
# #   | Suppress('alloca') + opt_ty('ty') + comma + opt_ty('num_ty') + operand('num') \
# #   | Suppress('alloca') + (ty | FollowedBy(LineEnd()))('ty').setParseAction(OptionalTypeExpr)
#
#
# gep = Suppress('getelementptr') + Optional('inbounds') + opt_ty('ptr_t') + operand('ptr') + Group(
#   comma + ZeroOrMore(opt_ty + operand + comma) + opt_ty + operand
#   | FollowedBy(LineEnd()))('flds')
#
# gep.setParseAction(GEPExpr)
#
# load = Suppress('load') + opt_ty('ty') + operand('x') + (comma + Suppress('align') + posnum('align')|FollowedBy(LineEnd()))
# load.setParseAction(LoadExpr)
#
freeze = Literal('freeze') - opt_ty('ty') + operand('x')
freeze.setParseAction(FreezeAst)

op = binOp | convOp | icmp | fcmp | select | copyOp | freeze
op.setName('operator')


opInst = reg('lhs') + Suppress('=') + op('op')
opInst.setParseAction(OpInstAst)
#
# store = Suppress('store') - opt_ty('val_t') - operand('val') - comma - opt_ty('ptr_t') - operand('ptr') - \
#   (comma - Suppress('align') - posnum('align') | FollowedBy(LineEnd()))
# store.setParseAction(StoreExpr)
#
# instr = opInstr | store
# instr.setName('Instruction')

cdef = cname('lhs') + Suppress('=') + cexpr('rhs')
cdef.setParseAction(CDefAst)

instr = opInst | cdef
instr.setName('Instruction')

#instrs = OneOrMore(instr - LineEnd().suppress())

class TransformAST(Ast):
  def eval(self, extended_results=False):
    t = self.toks
    name = t.name[0] if t.name else ''
    root = t.src[-1].name()

    if t.tgt[-1].name() != root:
      t.tgt[-1]._fatal('Target root must redefine source ({0})'.format(root))

    ids = {}
    for i in t.src: i.eval(ids, Phase.Source)

    for i in t.tgt:
      if isinstance(i, CDefAst):
        i.eval(ids, Phase.Target)

    preconditions = []
    assumptions = []
    features = []

    headers = {'Pre:': preconditions,
      'Assume:': assumptions,
      'Feature:': features}

    for h in t.headers:
      headers[h[0]].append(h[1].condition(ids))

    src = ids.pop(root)
    for i in t.tgt:
      if not isinstance(i, CDefAst):
        i.eval(ids, Phase.Target)

    transform = Transform(src, ids[root], preconditions, assumptions, name)

    if extended_results:
      return transform, features

    return transform


comment = Literal(';') + restOfLine()
continuation = '\\' + LineEnd()

EOL = Suppress(OneOrMore(LineEnd()))

header = Group(oneOf('Pre: Assume:') - pre - EOL) | \
  Group('Feature:' - pre_atom - EOL)

transform = (Optional(Suppress("Name:") - SkipTo(LineEnd()) - EOL).setResultsName("name") \
  + Group(ZeroOrMore(header))('headers') \
  + Group(OneOrMore(instr - EOL)).setResultsName("src") \
  - Suppress("=>") - EOL \
  - Group(OneOrMore(instr - EOL)).setResultsName("tgt"))
transform.setName('transform')
transform.setParseAction(TransformAST)

transforms = Optional(EOL) + ZeroOrMore(transform)
transforms.ignore(comment)
transforms.ignore(continuation)

str1 = """
Name: Test1
Pre: width(%a) == -C

%a = mul %x, C
%r = add %a, %x
=>
%r = mul %x, C+1
"""

str2 = '''Name: InstCombineShift: 366-1
%TrOp = shl %X, C1
%Op0 = trunc %TrOp
%r = shl i17 %Op0, C2
  =>
%s1 = shl %TrOp, zext(C2)
%and = and %s1, ((1<<width(C2))-1) << zext(C2)
%r = trunc %and
'''

str3 = '''Name: test
Assume: C1 != 0
Feature: C1 ^ C2 == 0
Feature: isPowerOf2(C1)
Pre: C2 != 0
%x = add %a, C1
%y = add %x, C2
=>
%y = add %a, (C1+C2)
'''

str4 = '''%x = add %a, %b
=>
%x = add %a, %b
'''

# comma.setDebug()
# cfunc.setDebug()
# arg.setDebug()
# reg.setDebug()
# ty.setDebug()
# opt_ty.setDebug()
# cexpr.setDebug()
# pre.setDebug()
# pre_atom.setDebug()
# pre_pred.setDebug()
# pre_comp.setDebug()
# pre_lit.setDebug()
# binOp.setDebug()
# convOp.setDebug()
# select.setDebug()
# alloca.setDebug()
# op.setDebug(True)
# instr.setDebug()
# instrs.setDebug()
# cexpr.setDebug()
# reg.setDebug()
# operand.setDebug()
# transform.setDebug()

def test(s = '%a = add i8 %b, %c', t = None):
  try:
    op = instr.parseString(s)[0]
    src = collections.OrderedDict()
    op.eval(src, Phase.Source)

    if t:
      top = instr.parseString(t)[0]
      tgt = collections.OrderedDict([(k,v) for k,v in src.iteritems() if isinstance(v,Input)])

      #for x in src:
      # if isinstance(src[x], Input):
      #   tgt[x] = src[x]
      top.eval(tgt, Phase.Target)
    else: tgt = {}
    return src, tgt
  except ParseBaseException, e:
    print e.msg, '(line %d, col %d)' % (e.lineno, e.col)
    if e.pstr:
      print e.line
      print ' ' * (e.col-1) + '^'

def parse_transform(s, extended_results=False):
  try:
    return transform.parseString(s, True)[0].eval(extended_results)
  except ParseBaseException, e:
    print 'ERROR:', e.msg, '(line %d, col %d)' % (e.lineno, e.col)
    if e.pstr:
      print e.line
      print ' ' * (e.col-1) + '^'
    raise

def parse_opt_file(s, extended_results=False):
  'Wrapper for transforms.parseString which exits program on exceptions.'
  try:
    return [t.eval(extended_results)
            for t in transforms.parseString(s, True)]
  except ParseBaseException, e:
    print 'ERROR:', e.msg, '(line %d, col %d)' % (e.lineno, e.col)
    if e.pstr:
      print e.line
      print ' ' * (e.col-1) + '^'
    exit(-1)

def read_opt_files(files, extended_results=False):
  for f in files:
    if f.isatty():
      sys.stderr.write('[Reading from terminal...]\n')

    for opt in parse_opt_file(f.read(), extended_results):
      yield opt


def parse_opts(s):
  # transforms.setDebug()
  try:
    for t in transforms.parseString(s, True):
      print '---------'
      print t.format()
      print

  except ParseBaseException, e:
    print e.msg, '(line %d, col %d)' % (e.lineno, e.col)
    if e.pstr:
      print e.line
      print ' ' * (e.col-1) + '^'

if __name__ == "__main__":
  opts = parse_opts(sys.stdin.read())
#   import logging
#   logging.basicConfig()
#   logging.getLogger('transform').setLevel(logging.DEBUG)
#   parse_opts(str2)
