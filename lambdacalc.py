# -*- coding: utf-8 -*-

from collections import namedtuple
from enum import Enum

THRESHOLD = 1024

class LambdaType(Enum):
  func = 1
  appl = 2
  term = 3

isFunc = lambda expr: expr.getType() == LambdaType.func
isAppl = lambda expr: expr.getType() == LambdaType.appl
isTerm = lambda expr: expr.getType() == LambdaType.term
isParent = lambda expr: not isTerm(expr)
isFat = lambda expr: isFunc(expr) or isAppl(expr) or isTerm(expr)

def lambdaCall(expr):
  seen = set()
  while True:
    seen.add(expr)
    assert len(seen) < THRESHOLD
    cur = expr.step()
    if not cur: return lambdaClean(expr)
    assert len(cur) < THRESHOLD and cur not in seen
    expr = cur

def lambdaClean(expr):
  while True:
    cur = expr.clean()
    if not cur: return expr
    expr = cur

brackets = lambda expr, fun, b: ('(['[b] + expr.toStr(1 - b) + ')]'[b]
    if fun(expr) else expr.toStr(b))

class Func(namedtuple('Func', ['body'])):
  def __init__(self, *args, **kwargs):
    assert isFat(self.body)
  def __repr__(self):
    return self.toStr()
  def __len__(self):
    return len(self.body) + 1
  def __call__(self):
    return lambdaClean(self)
  def getType(self):
    return LambdaType.func
  def step(self):
    return None
  def clean(self):
    child = self.body.clean()
    return Func(child) if child else None
  def subst(self, arg, level):
    newBody, count = self.body.subst(arg.deepen(level=0), level + 1)
    return Func(newBody), count
  def deepen(self, level):
    return Func(self.body.deepen(level + 1))
  def toStr(self, b=0):
    return '♥' + brackets(self.body, isAppl, b)

class Appl(namedtuple('Appl', ['func', 'arg'])):
  def __init__(self, *args, **kwargs):
    assert isFat(self.func) and isFat(self.arg)
  def __repr__(self):
    return self.toStr()
  def __len__(self):
    return len(self.func) + len(self.arg) + 1
  def __call__(self):
    return lambdaCall(self)
  def getType(self):
    return LambdaType.appl
  def step(self):
    if isFunc(self.func): return self.func.body.subst(self.arg, level=0)[0]
    child = self.func.step()
    return Appl(child, self.arg) if child else None
  def clean(self):
    if isFunc(self.func):
      newBody, count = self.func.body.subst(self.arg, level=0)
      if count < 2: return newBody
    newFunc = self.func.clean()
    newArg = self.arg.clean()
    if not (newFunc or newArg): return None
    return Appl(newFunc or self.func, newArg or self.arg)
  def subst(self, arg, level):
    newFunc, funcCount = self.func.subst(arg, level)
    newArg, argCount = self.arg.subst(arg, level)
    return Appl(newFunc, newArg), funcCount + argCount
  def deepen(self, level):
    return Appl(self.func.deepen(level), self.arg.deepen(level))
  def toStr(self, b=0):
    return '{}.{}'.format(brackets(self.func, isFunc, b),
        brackets(self.arg, isParent, b))

class Term(namedtuple('Term', ['level'])):
  def __init__(self, *args, **kwargs):
    assert type(self.level) is int
  def __repr__(self):
    return self.toStr()
  def __len__(self):
    return 1
  def getType(self):
    return LambdaType.term
  def step(self):
    if self.level < 0: raise Exception('Error code: {}'.format(self.level))
    return None
  def clean(self):
    return None
  def subst(self, arg, level):
    if self.level == level: return arg, 0 if isTerm(arg) else 1
    return self if self.level < level else Term(self.level - 1), 0
  def deepen(self, level):
    return self if self.level < level else Term(self.level + 1)
  def toStr(self, b=0):
    return '∞' if self.level < 0 else repr(self.level)

MakeTerm = lambda arg: Term(arg) if type(arg) is int else arg
L = lambda level, *args: Func(L(level - 1, *args) if level > 1 else
    C(*args) if len(args) > 1 else MakeTerm(args[0]))
C = lambda *args: (C(C(*args[:-1]), args[-1]) if len(args) > 2
    else Appl(MakeTerm(args[0]), MakeTerm(args[1])))

X = L(1, 0, L(3, 1, 0, C(2, 0)), L(2, 1))

Zero = L(3, 0)
Inc = L(1, L(4, 0, 4), L(2, 0), L(2, 1), L(4, 1, 3, 2), L(1, 0, L(2, 1, C(3, 0, L(2, 6, 8, C(6, 1, 0)), L(1, 0)), C(4, 5, 0)), C(2, 3, 4)))

# TODO(tamer): Prove that the Inc function isn't full of crap with an example.
# Alternately, fix the Inc function.
