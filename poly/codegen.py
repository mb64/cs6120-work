# Codegen
# ~~~~~~~
#
# This is mostly just helper functions reifying ISL conditions as code.

from util import *
import bril
from bril import Instr

import islpy as isl

# Global counter
# This is ugly but makes my life easier
counter = 0
def fresh() -> str:
    global counter
    counter += 1
    return f'__tmp{counter}'


class Codegen:
    instrs: list[Instr]

    def __init__(self):
        self.instrs = []

    def take_instrs(self) -> list[Instr]:
        result = self.instrs
        self.instrs = []
        return result

    def const(self, value: int) -> str:
        dest = fresh()
        self.instrs.append({ 'op': 'const', 'dest': dest, 'type': 'int', 'value': value })
        return dest

    def true(self) -> str:
        dest = fresh()
        self.instrs.append({ 'op': 'const', 'dest': dest, 'type': 'bool', 'value': True })
        return dest

    def false(self) -> str:
        dest = fresh()
        self.instrs.append({ 'op': 'const', 'dest': dest, 'type': 'bool', 'value': False })
        return dest

    def and_(self, *args) -> str:
        if len(args) == 0:
            return self.true()
        result = args[0]
        for arg in args[1:]:
            result = self.op('and', result, arg, type='bool')
        return result

    def or_(self, *args) -> str:
        if len(args) == 0:
            return self.false()
        result = args[0]
        for arg in args[1:]:
            result = self.op('or', result, arg, type='bool')
        return result

    def op(self, op: str, *args, type='int') -> str:
        dest = fresh()
        self.instrs.append({ 'op': op, 'dest': dest, 'type': type, 'args': list(args) })
        return dest

    def add(self, x: str, y: str) -> str:
        return self.op('add', x, y)

    def mul(self, x: str, y: str) -> str:
        return self.op('mul', x, y)

    def lt(self, x: str, y: str) -> str:
        return self.op('lt', x, y, type='bool')

    def aff(self, aff: isl.Aff) -> str:
        aff = aff.drop_unused_params().as_aff()
        space = aff.space
        n = space.dim(isl.dim_type.param)
        result = self.const(aff.get_constant_val().to_python())
        for i in range(n):
            v: str = space.get_dim_name(isl.dim_type.param, i)
            coeff: int = aff.get_coefficient_val(isl.dim_type.param, i).to_python()
            result = self.add(result, self.mul(v, self.const(coeff)))
        return result

    def set(self, s: isl.Set) -> str:
        return self.or_(self.basic_set(bs) for bs in s.get_basic_sets())

    def basic_set(self, bs: isl.BasicSet) -> str:
        return self.and_(self.constraint(c) for c in bs.get_constraints())

    def constraint(self, c: isl.Constraint) -> str:
        value = self.aff(c.get_aff())
        op = 'eq' if c.is_equality() else 'ge'
        return self.op(op, value, self.const(0), type='bool')

def isl_set(s: isl.Set) -> tuple[list[Instr], str]:
    c = Codegen()
    val = c.set(s)
    return c.take_instrs(), val

def isl_aff(a: isl.Aff) -> tuple[list[Instr], str]:
    c = Codegen()
    val = c.aff(a)
    return c.take_instrs(), val


