import collections, sys
import language as L
from transform import Transform, Formatter
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
    return L.Literal(int(self.toks[0]))

class LitWordAst(ValAst):
  def value(self, ty, ids, phase):
    v = self.toks[0]

    if v == 'true':
      return L.Literal(1)
    if v == 'false':
      return L.Literal(0)
    
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
      ids[self.id] = L.Input(self.id)
      return ids[self.id]

    self._fatal('Input {} not in source'.format(self.id))

class Register(Name): pass
class ConstName(Name): pass

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



predicates = L.FunPred.codes
functions = L.FunCnxp.codes


class FunAst(ValAst, PreconditionAst):
  'Common expression type for <name>(<args>). Supports value and condition.'

  def condition(self, ids):
    name = self.toks[0]

    if name not in predicates:
      self._fatal('Unknown predicate: ' + name)

    pred = predicates[name]
    
    # check arity
    if len(self.toks)-1 != pred.arity:
      self._fatal('Wrong number of arguments to {0}: expected {1} received {2}'.format(
        name, pred.arity, len(self.toks)-1))

    args = tuple(a.value(None, ids, Phase.Pre) for a in self.toks[1:])
    
    return pred(*args)


  def value(self, ty, ids, phase):
    if phase == Phase.Source:
      self._fatal('Expressions not permitted in source')

    # determine if this is a valid function
    name = self.toks[0]
    
    if name not in functions:
      self._fatal('Unknown function: ' + name)
    
    fun = functions[name]
    
    # check arity
    if len(self.toks)-1 != fun.arity:
      self._fatal('Wrong number of arugments to {0}: expected {1} received {2}'.format(
        name, fun.arity, len(self.toks)-1))

    args = tuple(a.value(None, ids, phase) for a in self.toks[1:])
    
    return fun(*args)


class OpInstAst(Ast):
  'Represents <reg> = <instr>'

  def eval(self, ids, phase):
    r = self.toks.lhs.id

    if r in ids:
      self._fatal('Redefinition of ' + r)

    ids[r] = self.toks.op.inst(r, ids, phase)

  def name(self):
    return self.toks.lhs.id

class InstAst(Ast):
  pass

class CopyOpAst(InstAst):
  def inst(self, name, ids, phase):
    ty = self.toks.ty.eval(ids, phase)
    return self.toks.x.value(ty, ids, phase)

  # TODO: replace this entirely

# bin_insts = {
#   'add':  L.AddInst,
#   'sub':  L.SubInst,
#   'mul':  L.MulInst,
#   'sdiv': L.SDivInst,
#   'udiv': L.UDivInst,
#   'srem': L.SRemInst,
#   'urem': L.URemInst,
#   'shl':  L.ShlInst,
#   'ashr': L.AShrInst,
#   'lshr': L.LShrInst,
#   'and':  L.AndInst,
#   'or':   L.OrInst,
#   'xor':  L.XorInst,
#   }

bin_insts = L.BinaryOperator.codes

class BinOpAst(InstAst):
  def inst(self, name, ids, phase):
    op = self.toks.code
    ty = self.toks.ty.eval(ids, phase)

    v1 = self.toks.x.value(ty, ids, phase)
    v2 = self.toks.y.value(ty, ids, phase)
    flags = [tok.value for tok in self.toks.flags]

    return op(v1,v2,ty=ty,flags=flags,name=name)
    # FIXME: validate flags

# conv_insts = {
#   'sext': L.SExtInst,
#   'zext': L.ZExtInst,
#   'trunc': L.TruncInst,
#   }

conv_insts = L.ConversionInst.codes

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
    
    return L.IcmpInst(self.toks.cmp, x, y, ty, name)
    # FIXME: validate cmp?


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

ty = ('i' + posnum).setName('type').setParseAction(IntTypeAst)

opt_ty = Optional(ty).setParseAction(OptionalTypeAst)


lit = Regex("(?:-\s*)?\d+").setName("Literal").setParseAction(LiteralAst)

ident = Word(srange("[a-zA-Z]"), srange(r"[a-zA-Z0-9_.]")).setName("Identifier")

reg = Regex(r"%[a-zA-Z0-9_.]+").setName("Register").setParseAction(Register)

cname = Regex(r"C\d*(?![a-zA-Z_.])").setName("ConstName").setParseAction(ConstName)


cexpr = Forward()


arg = reg | cexpr

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

# pre_pred = (ident + Suppress('(') + args + Suppress(')')).setParseAction(FunAst)
# pre_pred.setName('predicate')

pre_atom = pre_lit | pre_comp | cfunc

pre = infixNotation(pre_atom,
      [(Suppress('!'), 1, opAssoc.RIGHT, NotAst),
       (Suppress('&&'), 2, opAssoc.LEFT, AndAst),
       (Suppress('||'), 2, opAssoc.LEFT, OrAst),
      ])
pre.setName('precondition')

special_lit = oneOf('true false undef null').setParseAction(LitWordAst)
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

flags = Group(ZeroOrMore(locatedExpr(oneOf('nsw nuw exact'))))

binOp = (opCode(bin_insts) - flags('flags') - opt_ty('ty') - operand('x') - comma
      - operand('y')).setParseAction(BinOpAst)

opt_rty = (Suppress('to') - ty | FollowedBy(LineEnd())).setParseAction(OptionalTypeAst)

convOp = (opCode(conv_insts) - opt_ty('sty') - operand('x') - opt_rty('rty')).setParseAction(ConvOpAst)

cmpOp = Optional(ident, '')

## FIXME: "icmp i8 %x, %y" parses the "i8" as the comparison operator
icmp = Literal('icmp') - cmpOp('cmp') - opt_ty('ty') - operand('x') - comma - operand('y')
icmp.setParseAction(ICmpAst)

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
op = binOp | convOp | icmp | select | copyOp # | alloca | gep | load | copyOp
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

instr = opInst
instr.setName('Instruction')

#instrs = OneOrMore(instr - LineEnd().suppress())

def parseTransform(s,l,t):
  name = t.name[0] if t.name else ''

  src = collections.OrderedDict()
  for i in t.src: i.eval(src, Phase.Source)
  
  root = t.src[-1].name()

  if t.pre[0]:
    pre = t.pre[0].condition(src)
  else:
    pre = None
  
  if t.tgt[-1].name() != root:
    t.tgt[-1]._fatal('Target root must redefine source (' + root + ')')

  # copy inputs to target, excluding root
  tgt = src.copy()
  tgt.pop(root)

  for i in t.tgt: i.eval(tgt, Phase.Target)

  return Transform(src[root], tgt[root], pre, name)

comment = Literal(';') + restOfLine()
continuation = '\\' + LineEnd()

EOL = Suppress(OneOrMore(LineEnd()))

transform = (Optional(Suppress("Name:") - SkipTo(LineEnd()) - EOL).setResultsName("name") \
  + Optional(Suppress("Pre:") - pre - EOL, None).setResultsName("pre") \
  + Group(OneOrMore(instr - EOL)).setResultsName("src") \
  - Suppress("=>") - EOL \
  - Group(OneOrMore(instr - EOL)).setResultsName("tgt"))
transform.setName('transform')
transform.setParseAction(parseTransform)

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

def parse_transform(s):
  try:
    return transform.parseString(s, True)[0]
  except ParseBaseException, e:
    print 'ERROR:', e.msg, '(line %d, col %d)' % (e.lineno, e.col)
    if e.pstr:
      print e.line
      print ' ' * (e.col-1) + '^'
    raise

def parse_opt_file(s):
  'Wrapper for transforms.parseString which exits program on exceptions.'
  try:
    return transforms.parseString(s, True)
  except ParseBaseException, e:
    print 'ERROR:', e.msg, '(line %d, col %d)' % (e.lineno, e.col)
    if e.pstr:
      print e.line
      print ' ' * (e.col-1) + '^'
    exit(-1)


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
