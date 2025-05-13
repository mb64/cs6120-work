# Static control flow
# ~~~~~~~~~~~~~~~~~~~
#
# A function with _static control flow_ has its variables partitioned in two groups:
#  1. Control-flow-relevant "affine variables" i,j,k
#  2. Control-flow-irrelevant "data variables" x,y,z
#
# s ::= for (i \in affine domain) { ss }       (single-variable for loop)
#    |  if (affine condition) { ss }
#    |  instr_1; ...; instr_N
#
# ss ::= s_1; ...; s_N
#
# Affine conditions and domains can only be in terms of affine variables.
# Instructions can only modify data variables.
#
# As an implementation trick, rather than try to eliminate all uses of
# control-flow variables, I simply add new control-flow variables. A later dead
# code pass can remove dead uses of the old ones, or keep them around if
# they're used for other things too.
#
# This is a representation that's quite close to polyhedral form. Using this as
# the primary IR for polyhedral transformations is inspired by MLIR's
# simplified polyhedral form:
#   https://mlir.llvm.org/docs/Rationale/RationaleSimplifiedPolyhedralForm/
# In particular, the classical scheduling problem for polyhedral IRs is very
# tricky, but here, everything is already in some schedule by default.
#
# Here are some of the sources I've found on scheduling and codegen for a
# classical polyhedral representation:
# - https://link.springer.com/article/10.1023/A:1007554627716 (IJPP'00)
# - https://icps.u-strasbg.fr/~bastoul/research/papers/Bas04-PACT.pdf (PACT'04) -- CLooG
# - https://lirias.kuleuven.be/retrieve/319112 (TOPLAS'15)
#
# What's an affine domain / affine condition?
# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#
# These are conjuncts of (in)equalities \sum coeff*i + const >= 0. They are
# represented using the ISL library.
#
# The only difference is that iteration domains are about _new_ variables, and
# affine conditions are about _existing_ variables.
#

from util import *
import bril
import graph
import relooper
from relooper import Command, BBCmd, Block, Loop, If, Return, Jump
import codegen

import islpy as isl
isl_ctx = isl.Context()

RET_VAR = '__ret'

class Static:
    def debug(self, indent=''):
        raise Exception(f'{type(self)} is supposed to implement this virtual method')

    def to_structured(self, cont: Command) -> Command:
        raise Exception(f'{type(self)} is supposed to implement this virtual method')

def debug_all(ss: list[Static], indent=''):
    for s in ss:
        s.debug(indent)

def to_structured_all(ss: list[Static], cont: Command) -> Command:
    for s in reversed(ss):
        cont = s.to_structured(cont)
    return cont

@dataclasses.dataclass
class BBStatic(Static):
    instrs: list[bril.Instr]  # they do not affect control flow, or affine variables

    def debug(self, indent=''):
        for i in self.instrs:
            print(indent + str(i))

    def to_structured(self, cont: Command) -> Command:
        return BBCmd(self.instrs, cont)

@dataclasses.dataclass
class For(Static):
    var: str
    domain: isl.Set  # 0-dimensional; but with params = all the control flow vars, including var
    body: list[Static]

    def debug(self, indent=''):
        print(indent + f'for {self.var} in {self.domain} {{')
        debug_all(self.body, indent + '  ')
        print(indent + f'}}')

    def bounds(self) -> tuple[isl.Aff, isl.Aff]:
        # Lowest element in the range, one past the biggest element in the range
        space = self.domain.space

        # wrangle it so the loop var is a set var, not a param
        dim = space.find_dim_by_name(isl.dim_type.param, self.var)
        dim_id = space.get_dim_id(isl.dim_type.param, dim)
        idlist = isl.IdList.from_id(dim_id)
        the_set = self.domain.params().unbind_params(space.add_unnamed_tuple_ui(1).multi_id(idlist))

        lo = the_set.dim_min(0).get_pieces()
        hi = the_set.dim_max(0).get_pieces()
        if len(lo) != 1 or len(hi) != 1:
            raise Unhandled(f'Piecewise bounds: {self.domain}')
        (s, lo_aff), = lo
        (s, hi_aff), = hi
        return (lo_aff, hi_aff + 1)

    def to_structured(self, cont: Command) -> Command:
        cg = codegen.Codegen()

        # i = lower_bound
        # loop .l {
        #   if (i < upper_bound) { body; i += 1; jmp .l; } else { cont }
        # }

        lo, hi = self.bounds()

        lower_bound = cg.aff(lo)
        one = cg.const(1)
        preheader_insts = cg.take_instrs()
        preheader: list[bril.Instr] = [
                *preheader_insts,
                { 'op': 'id', 'dest': self.var, 'type': 'int', 'args': [lower_bound] },
            ]

        increment = BBCmd(
                [{ 'op': 'add', 'dest': self.var, 'type': 'int', 'args': [self.var, one] }],
                Jump(self.var),
            )

        upper_bound = cg.aff(hi)
        cond = cg.lt(self.var, upper_bound)
        body = BBCmd(cg.take_instrs(), If(cond, to_structured_all(self.body, increment), cont))

        loop = Loop(label = self.var, contents = body)
        return BBCmd(instrs = preheader, cont = loop)

@dataclasses.dataclass
class Cond(Static):
    condition: isl.Set  # 0-dimensional; but with params = all the control flow vars
    body: list[Static]

    def debug(self, indent=''):
        print(indent + f'if {self.condition} {{')
        debug_all(self.body, indent + '  ')
        print(indent + f'}}')

    def to_structured(self, cont: Command) -> Command:
        cond_instrs, cond = codegen.isl_set(self.condition)
        return Block(
                "else",
                BBCmd(cond_instrs, If(cond, to_structured_all(self.body, Jump('else')), Jump('else'))),
                cont)

@dataclasses.dataclass
class StaticFunction:
    name: str
    args: list[bril.Param]
    type: bril.Typ | None
    code: list[Static]

    def debug(self, indent=''):
        args = ', '.join(f'{param["name"]}: {param["type"]}' for param in self.args)
        print(indent + f'func @{self.name}({args}) {{')
        debug_all(self.code, indent + '  ')
        if self.type is not None:
            print(indent + f'  return {RET_VAR}')
        print(indent + f'}}')

    def to_structured(self) -> relooper.StructuredFunction:
        if self.type is None:
            cont = Return(None)
        else:
            cont = Return(RET_VAR)
        code = to_structured_all(self.code, cont)
        return relooper.StructuredFunction(
                name = self.name,
                args = self.args,
                type = self.type,
                code = code,
            )


# Information flow analysis: which variables are used in control flow
#
# It's a super simple flow-insensitive analysis
def control_flow_vars(func: relooper.StructuredFunction) -> set[str]:
    roots: set[str] = set()  # these are used in control flow
    edges: set[tuple[str, str]] = set()  # (a,b) means b helps determine the value of a
    bad: set[str] = set()

    def go(c: Command):
        match c:
            case BBCmd(instrs, cont):
                edges.update({ (inst['dest'], arg)
                    for inst in instrs
                    if bril.is_pure(inst) and 'dest' in inst and 'args' in inst
                    for arg in inst['args']
                })
                bad.update({ inst['dest'] for inst in instrs if not bril.is_pure(inst) and 'dest' in inst })
                go(cont)
            case Block(label, contents, cont):
                go(contents)
                go(cont)
            case Loop(label, contents):
                go(contents)
            case If(b, true, false):
                roots.add(b)
                go(true)
                go(false)
            case Return(): pass
            case Jump(): pass
            case _: assert False  # unhandled case

    go(func.code)
    result: set[str] = graph.reachable(edges, roots)

    for v in result & bad:
        raise Unhandled(f'non-static control flow from variable {v}')

    return result


def compute_live_vars(func: relooper.StructuredFunction) -> tuple[dict[str, set[str]], set[str]]:
    live_vars: dict[str, set[str]] = defaultdict(set)
    changed = True

    def go(cmd: Command) -> set[str]:
        nonlocal live_vars, changed
        match cmd:
            case BBCmd(instrs, cont):
                live = go(cont)
                for i in reversed(instrs):
                    live |= set(bril.uses(i))
                    live -= set(bril.writes(i))
                return live
            case Block(label, contents, cont):
                live = go(cont)
                if live != live_vars[label]:
                    live_vars[label] = live.copy()
                    changed = True
                return go(contents)
            case Loop(label, contents):
                live = go(contents)
                if live != live_vars[label]:
                    live_vars[label] = live.copy()
                    changed = True
                return live
            case If(condition, true, false):
                return go(true) | go(false)
            case Return(value):
                return {value} if value is not None else set()
            case Jump(label):
                return live_vars[label].copy()
            case _:
                assert False  # missing case

    while changed:
        changed = False
        func_live = go(func.code)

    return live_vars, func_live

def is_changing_in_loop(var: str, loop: Loop) -> bool:
    # If the variable can change between iterations of the loop

    changed_in: dict[str, bool] = defaultdict(lambda: False)
    def go(cmd: Command, changed: bool):
        nonlocal changed_in
        match cmd:
            case BBCmd(instrs, cont):
                changed = changed or any(('dest' in i and i['dest'] == var) for i in instrs)
                go(cont, changed)
            case Jump(label):
                changed_in[label] |= changed
            case Block(label, contents, cont):
                go(contents, changed)
                go(cont, changed_in[label])
            case Loop(label, contents):
                changed_in[label] = changed
                go(contents, changed)
                if changed_in[label] and not changed:
                    go(contents, True)
            case If(condition, true, false):
                go(true, changed)
                go(false, changed)
            case Return(value):
                pass
            case _:
                assert False  # missing case

    go(loop, False)
    return changed_in[loop.label]

# For turning commands into static control flow.
#
# StaticCommands.
#  sc ::= s; ret
#      |  s; jmp l[env]
#      |  s; if cond { s; jmp l[env] } else { sc }
#
# Invariant: the same label occurs at most once, AND they occur in the order of
# the branch stack.

# Type alias: environment (for control flow variables)
#  - if it's unknown, it gets None
#  - if it's an affine number, it's a (valid) isl.Aff
#  - if it's an affine condition, it's a (valid) isl.Set
#
# ISL convention: N params, no other vars.
Env = dict[str, isl.Aff | isl.Set | None]

class StaticCommand:
    def can_reach(self, lbl: str) -> bool:
        raise Exception(f'{type(self)} needs to implement this abstract method')


@dataclasses.dataclass
class Simple(StaticCommand):
    body: list[Static]
    dest: str
    env: Env  # N params

    def can_reach(self, lbl: str) -> bool:
        return lbl == self.dest

@dataclasses.dataclass
class SimpleRet(StaticCommand):
    body: list[Static]

    def can_reach(self, lbl: str) -> bool:
        return False

@dataclasses.dataclass
class Compound(StaticCommand):
    init: list[Static]
    condition: isl.Set
    true: Simple
    false: StaticCommand

    def can_reach(self, lbl: str) -> bool:
        return self.true.can_reach(lbl) or self.false.can_reach(lbl)

def prepend_basic_block(init: list[Static], cont: StaticCommand) -> StaticCommand:
    match cont:
        case SimpleRet(body):
            return SimpleRet(init + body)
        case Simple(body, dest, env):
            return Simple(init + body, dest, env)
        case Compound(init_, condition, true, false):
            return Compound(init + init_, condition, true, false)
        case _:
            assert False  # missing case

def more_recent(l1: str, l2: str, stack: list[str]) -> bool:
    # true if l1 is higher on the branch stack than l2
    for l in reversed(stack):
        if l == l1:
            return True
        if l == l2:
            return False
    assert False  # internal error

def make_branch_simple(condition: isl.Set, true: Simple, false: Simple) -> Simple:
    # Merge two simple things with the same destination
    assert true.dest == false.dest

    env: Env = {}
    for k in set(true.env.keys()) & set(false.env.keys()):
        # There's probably a more precise way of doing this
        l, r = true.env[k], false.env[k]
        if l is None or r is None or l != r:
            env[k] = None
        else:
            env[k] = l

    return Simple(
            body = [Cond(condition, true.body), Cond(condition.complement(), false.body)],
            dest = true.dest,
            env = env,
        )

def make_branch(condition: isl.Set, true: StaticCommand, false: StaticCommand, stack: list[str]) -> StaticCommand:
    # In theory, this function can be implemented for every case.
    # In practice, only few arise. In particular, I'm not implementing any of
    # the recursive cases.
    match (true, false):
        case (Simple(body1, dest1, env1), Compound(init2, condition2, true2, false2)):
            if dest1 == true2.dest:
                return Compound(
                        init = [Cond(condition.complement(), init2)],
                        condition = condition | condition2,
                        true = make_branch_simple(condition, true, true2),
                        false = false2,
                    )
            elif more_recent(dest1, true2.dest, stack):
                return Compound([], condition, true, false)
            else:
                raise Unhandled('Merging complex control flow')

        case (Compound(), Simple()):
            return make_branch(condition.complement(), false, true, stack)

        case (Simple(body1, dest1, env1), Simple(body2, dest2, env2)):
            if dest1 == dest2:
                return make_branch_simple(condition, true, false)
            elif more_recent(dest1, dest2, stack):
                return Compound([], condition, true, false)
            else:
                return Compound([], condition.complement(), false, true)

        case (SimpleRet(body1), SimpleRet(body2)):
            return SimpleRet([Cond(condition, body1), Cond(condition.complement(), body2)])

        case (Simple(body1, dest, env), SimpleRet(body2)):
            return Compound([], condition, true, false)

        case (SimpleRet(body1), Simple(body2, dest, env)):
            return Compound([], condition.complement(), false, true)

        case _:
              raise Unhandled('Merging complex control flow')

def isl_aff_to_const(aff: isl.Aff) -> int | None:
    return aff.get_constant_val().to_python() if aff.is_cst() else None

def isl_space_get_params(space: isl.Space) -> list[str]:
    n = space.dim(isl.dim_type.param)
    return [space.get_dim_name(isl.dim_type.param, i) for i in range(n)]

def eval_instr(instr: bril.Instr, env: Env, space: isl.Space, aff_vars: set[str]):
    # Evaluate the instr in the env, **modifying the env**.
    if 'dest' not in instr or instr['dest'] not in aff_vars:
        return
    dest = instr['dest']
    if not bril.is_pure(instr):
        env[dest] = None
        return
    if instr['op'] == 'const':
        if instr['type'] == 'int':
            env[dest] = isl.Aff.val_on_domain_space(space, instr['value'])
        else:
            env[dest] = isl.Set.universe(space) if instr['value'] else isl.Set.empty(space)
        return

    args: list[isl.Aff | isl.Set] = []
    for arg in instr['args']:
        if arg not in env or env[arg] is None:
            # print(f'Calculating {dest}: {arg} is no good; {env=}')
            env[dest] = None
            return
        args.append(env[arg])

    match instr['op']:
        case 'id':
            x, = args
            env[dest] = x

        case 'add':
            l, r = args
            env[dest] = l + r
        case 'sub':
            l, r = args
            env[dest] = l - r
        case 'mul':
            l, r = args
            l_const = isl_aff_to_const(l)
            r_const = isl_aff_to_const(r)
            if l_const is not None:
                env[dest] = l_const * r
            elif r_const is not None:
                env[dest] = l * r_const
            else:
                env[dest] = None

        case 'eq':
            l, r = args
            env[dest] = l.eq_set(r)
        case 'gt':
            l, r = args
            env[dest] = l.gt_set(r)
        case 'ge':
            l, r = args
            env[dest] = l.ge_set(r)
        case 'lt':
            l, r = args
            env[dest] = l.lt_set(r)
        case 'le':
            l, r = args
            env[dest] = l.le_set(r)

        # TODO: boolean operations

        case _:
            env[dest] = None

def isl_var_in_space(space: isl.Space, name: str) -> isl.Aff:
    dim = space.find_dim_by_name(isl.dim_type.param, name)
    return isl.Aff.var_on_domain(isl.LocalSpace(space), isl.dim_type.param, dim)

def isl_downcast_to_space(space: isl.Space, val: isl.Aff | isl.Set | None) -> isl.Aff | isl.Set | None:
    if val is None:
        return None
    # Align it to the new parameter space and check if it uses any extra dims
    if isinstance(val, isl.Aff):

        val = val.drop_unused_params().as_aff().align_params(space)
        return val if val.space.params() == space.params() else None
    else:
        val = val.drop_unused_params().align_params(space)
        return val if val.space.params() == space.params() else None

def get_loop_domain(new_space: isl.Space, start_of_loop: isl.Aff, loop_var: str, symbolic_loop_var: isl.Aff, condition: isl.Set) -> isl.Set:
    # loop ends when condition is false: find the least loop_var in
    #   { loop_var | start_of_loop <= loop_var and !condition }

    dim = new_space.find_dim_by_name(isl.dim_type.param, loop_var)
    dim_id = new_space.get_dim_id(isl.dim_type.param, dim)
    idlist = isl.IdList.from_id(dim_id)

    the_set = start_of_loop.le_set(symbolic_loop_var) & condition.complement()
    end_of_loop = the_set.params().unbind_params(the_set.space.add_unnamed_tuple_ui(1).multi_id(idlist)).dim_min(0)

    return start_of_loop.le_set(symbolic_loop_var) & symbolic_loop_var.lt_set(end_of_loop)

def command_to_static(func: relooper.StructuredFunction) -> StaticFunction:
    aff_vars = control_flow_vars(func)
    live_vars, initial_live_vars = compute_live_vars(func)
    # print(f'{aff_vars=}')
    # print(f'{live_vars=}')

    all_vars = relooper.all_vars(func)
    for p in func.args:
        v = p['name']
        if v in all_vars and v in aff_vars:
            raise Unhandled(f'Control-relevant parameter {v} is modified in the function')
        all_vars.add(v)

    var_counter = 0
    def fresh() -> str:  # Fresh loop counter variable
        nonlocal var_counter
        var_counter += 1
        while f'i{var_counter}' in all_vars:
            var_counter += 1
        return f'i{var_counter}'

    def recurse(
            cmd: Command,
            env: Env,
            stack: list[str],
            space: isl.Space,
            space_list: dict[str, isl.Space],
    ) -> StaticCommand:
        # print(f'Processing in {env=} and {stack=}')
        # cmd.debug('  ')
        match cmd:
            case BBCmd(instrs, cont):
                env = env.copy()
                for i in instrs:
                    eval_instr(i, env, space, aff_vars)
                return prepend_basic_block(
                        [BBStatic(instrs)],
                        recurse(cont, env, stack, space, space_list))

            case Block(label, contents, cont):
                contents_ = recurse(contents, env, stack + [label], space, space_list | { label: space })
                if isinstance(contents_, Simple) and contents_.dest == label:
                    # It doesn't go anywhere but the label. (Just a merge point.)
                    return prepend_basic_block(
                            contents_.body,
                            recurse(cont, contents_.env, stack, space, space_list))
                if not isinstance(contents_, Compound) or contents_.true.dest != label:
                    # It doesn't actually use the label?
                    assert not contents_.can_reach(label)
                    return contents_
                # Final case: contents_ is a Compound thing branching on label
                cont_ = prepend_basic_block(
                        contents_.true.body,
                        recurse(cont, contents_.true.env, stack, space, space_list))
                return prepend_basic_block(
                        contents_.init,
                        make_branch(contents_.condition, cont_, contents_.false, stack))

            case Loop(label, contents):
                # There should ideally only be one control-flow-relevant
                # variable that is live at the start of the loop and changes
                # every iteration
                iter_var_candidates = [ v for v in live_vars[label] & aff_vars if is_changing_in_loop(v, cmd) ]
                if len(iter_var_candidates) != 1:
                    raise Unhandled(f'No single good loop var: {iter_var_candidates=}')
                iter_var, = iter_var_candidates
                # print(f'Loop {label}: trying iteration variable {iter_var}')
                # TODO: think about nested loops that accidentally use the same
                # iteration variable (I think we're ok here actually)
                # If any var in env is changing in the loop, it must be dead
                # So we can safely ignore it (?)

                # Extend the space with the iter var
                loop_var = fresh()
                new_space = isl.Space.create_from_names(isl_ctx, set=[], params = isl_space_get_params(space)+[loop_var])

                # Extend the Env using align_params
                symbolic_loop_var = isl_var_in_space(new_space, loop_var)
                new_env: Env = { iter_var: symbolic_loop_var }
                for k, val in env.items():
                    if val is None:
                        new_env[k] = None
                    elif isinstance(val, isl.Aff):
                        new_env[k] = val.align_params(new_space)
                    else: 
                        new_env[k] = val.align_params(new_space)
                new_env[iter_var] = symbolic_loop_var

                # Recurse + find the loop structure
                contents_ = recurse(contents, new_env, stack + [label], new_space, space_list | { label: new_space })
                if not isinstance(contents_, Compound):
                    raise Unhandled(f'inside of loop {label} is not a compound thing')
                if contents_.true.dest != label:
                    raise Unhandled(f'inside of loop {label} does not branch back to the loop')

                # find the loop domain
                if contents_.true.env[iter_var] is None:
                    raise Unhandled(f'Loop {label} does not have affine control (at least, not with {iter_var})')
                stride = isl_aff_to_const(contents_.true.env[iter_var] - symbolic_loop_var)
                if stride is None:
                    raise Unhandled(f'no constant loop stride for {label}: {contents_.true.env[iter_var]}')
                if stride != 1:
                    # TODO: would be nice to support other strides
                    raise Unhandled(f'can\'t deal with strides other than 1 yet for {label}')
                start_aff = env[iter_var]
                if start_aff is None:
                    raise Unhandled(f'Starting value for loop {label} is not affine')
                start_of_loop = start_aff.align_params(new_space)
                domain = get_loop_domain(new_space, start_of_loop, loop_var, symbolic_loop_var, contents_.condition)

                # construct the loop
                instr: bril.Instr = { 'op': 'id', 'dest': iter_var, 'type': 'int', 'args': [loop_var] }
                loop = For(loop_var, domain, [BBStatic([instr])] + contents_.init + contents_.true.body)
                return prepend_basic_block([loop] + contents_.init, contents_.false)

            case If(condition, true, false):
                condition_ = env[condition]
                if condition_ is None:
                    raise Unhandled(f'condition {condition} is not affine')
                assert isinstance(condition_, isl.Set), f'{condition=} {env=}'
                true_ = recurse(true, env, stack, space, space_list)
                false_ = recurse(false, env, stack, space, space_list)
                return make_branch(condition_, true_, false_, stack)

            case Return(value):
                if value is not None:
                    assert func.type is not None
                    return SimpleRet([BBStatic([{ 'op': 'id', 'dest': RET_VAR, 'type': func.type, 'args': [value] }])])
                else:
                    return SimpleRet([])

            case Jump(label):
                old_space = space_list[label]
                env_ = {k: isl_downcast_to_space(old_space, v) for k, v in env.items()}
                return Simple(
                        body = [],
                        dest = label,
                        env = env_,
                    )

            case _:
                assert False  # missing case

    param_types = { p['name']: p['type'] for p in func.args }
    initial_vars = [ p['name'] for p in func.args if p['name'] in aff_vars ]
    initial_space = isl.Space.create_from_names(isl_ctx, set=[], params=initial_vars)
    initial_env: Env = {}
    for v in initial_vars:
        if param_types[v] == 'bool':
            # TODO: this could totally be handled
            raise Unhandled(f'Boolean control-flow parameter {v} in {func.name}')
        else:
            initial_env[v] = isl_var_in_space(initial_space, v)
    match recurse(func.code, initial_env, [], initial_space, {}):
        case SimpleRet(body):
            return StaticFunction(
                    name = func.name,
                    args = func.args,
                    type = func.type,
                    code = body,
                )
        case x:
            assert False  # internal error



