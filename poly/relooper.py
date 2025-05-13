# Structured control flow
# ~~~~~~~~~~~~~~~~~~~~~~~
#
# Control flow is structured when it's of the form
#
# c ::= block .l { c1 } c2            (l is in scope for c1 but not c2)
#    |  loop .l { c }                 (l is in scope for c)
#    |  instr_1; ...; instr_N; c
#    |  if b then cs else c
#    |  jmp l
#    |  ret v
#
# Blocks create a scoped "break" label for the _end_ of the block, while loops
# create a scoped "continue" label for the _start_ of the loop.
#
# I mostly follow the algorithm from "Beyond relooper":
#
# Norman Ramsey. 2022. Beyond Relooper: recursive translation of unstructured
# control flow to structured control flow (functional pearl). Proc. ACM
# Program. Lang. 6, ICFP, Article 90 (August 2022), 22 pages.
# https://doi.org/10.1145/3547621
#
# However, my IR differs somewhat in how it's nested: I don't have an implicit
# "fallthru" continuation; all code must end in an explicit terminator.

from util import *
import bril
import graph

class Command:
    def debug(self, indent = ''):
        raise Exception(f'{type(self)} should have implemented this virtual method')

    def codegen(self, fresh_label: Callable[[str], str], label_env: dict[str, str]) -> list[bril.Instr | bril.Label]:
        raise Exception(f'{type(self)} should have implemented this virtual method')

@dataclasses.dataclass
class StructuredFunction:
    name: str
    args: list[bril.Param]
    type: bril.Typ | None
    code: Command

    def debug(self, indent = ''):
        args = ', '.join(f'{param["name"]}: {param["type"]}' for param in self.args)
        print(indent + f'func @{self.name}({args}) {{')
        self.code.debug(indent + '  ')
        print(indent + f'}}')

    def codegen(self) -> bril.Function:
        labels = set()
        def fresh_label(stem: str) -> str:
            nonlocal labels
            if stem not in labels:
                labels.add(stem)
                return stem
            for i in itertools.count():
                if stem + str(i) not in labels:
                    labels.add(stem + str(i))
                    return stem + str(i)
            assert False  # unreachable

        result: bril.Function = {
                'name': self.name,
                'args': self.args,
                'instrs': self.code.codegen(fresh_label, {}),
            }
        if self.type is not None:
            result['type'] = self.type
        return result

@dataclasses.dataclass
class BBCmd(Command):
    instrs: list[bril.Instr]  # Invariant: not control instructions
    cont: Command

    def debug(self, indent = ''):
        print(indent + '{ // basic block')
        for instr in self.instrs:
            print(indent + '  ' + str(instr))
        print(indent + '}')
        self.cont.debug(indent)

    def codegen(self, fresh_label: Callable[[str], str], label_env: dict[str, str]) -> list[bril.Instr | bril.Label]:
        return list[bril.Instr | bril.Label](self.instrs) + self.cont.codegen(fresh_label, label_env)

@dataclasses.dataclass
class Block(Command):
    label: str
    contents: Command
    cont: Command

    def debug(self, indent = ''):
        print(indent + f'block .{self.label} {{')
        self.contents.debug(indent + '  ')
        print(indent + f'}} // .{self.label}:')
        self.cont.debug(indent)

    def codegen(self, fresh_label: Callable[[str], str], label_env: dict[str, str]) -> list[bril.Instr | bril.Label]:
        label = fresh_label(self.label)
        return self.contents.codegen(fresh_label, label_env | { self.label: label }) \
                + [bril.Label({'label': label})] \
                + self.cont.codegen(fresh_label, label_env)

@dataclasses.dataclass
class Loop(Command):
    label: str
    contents: Command

    def debug(self, indent = ''):
        print(indent + f'loop .{self.label} {{ // .{self.label}:')
        self.contents.debug(indent + '  ')
        print(indent + f'}}')

    def codegen(self, fresh_label: Callable[[str], str], label_env: dict[str, str]) -> list[bril.Instr | bril.Label]:
        label = fresh_label(self.label)
        result: list[bril.Instr | bril.Label] = []
        return result \
                + [bril.Label({'label': label})] \
                + self.contents.codegen(fresh_label, label_env | { self.label: label })

@dataclasses.dataclass
class If(Command):
    condition: str  # variable name
    true: Command
    false: Command

    def debug(self, indent = ''):
        print(indent + f'if {self.condition} {{')
        self.true.debug(indent + '  ')
        print(indent + f'}} else {{')
        self.false.debug(indent + '  ')
        print(indent + f'}}')

    def codegen(self, fresh_label: Callable[[str], str], label_env: dict[str, str]) -> list[bril.Instr | bril.Label]:
        then_, else_ = fresh_label('then'), fresh_label('else')
        result: list[bril.Instr | bril.Label] = []
        return result \
                + [bril.Instr({'op': 'br', 'args': [self.condition], 'labels': [then_, else_]})] \
                + [bril.Label({'label': then_})] \
                + self.true.codegen(fresh_label, label_env) \
                + [bril.Label({'label': else_})] \
                + self.false.codegen(fresh_label, label_env)

@dataclasses.dataclass
class Return(Command):
    value: Optional[str]  # variable name

    def debug(self, indent = ''):
        print(indent + f'return {self.value}')

    def codegen(self, fresh_label: Callable[[str], str], label_env: dict[str, str]) -> list[bril.Instr | bril.Label]:
        if self.value is None:
            return [bril.Instr({'op': 'ret'})]
        else:
            return [bril.Instr({'op': 'ret', 'args': [self.value]})]

@dataclasses.dataclass
class Jump(Command):
    label: str  # must be in scope

    def debug(self, indent = ''):
        print(indent + f'jump .{self.label}')

    def codegen(self, fresh_label: Callable[[str], str], label_env: dict[str, str]) -> list[bril.Instr | bril.Label]:
        return [{'op': 'jmp', 'labels': [label_env[self.label]]}]

def check_well_scoped(cmd: Command, scope = set()):
    match cmd:
        case Return(): pass
        case BBCmd(instrs, cont):
            check_well_scoped(cont, scope)
        case Jump(l):
            assert l in scope
        case If(condition, true, false):
            check_well_scoped(true, scope)
            check_well_scoped(false, scope)
        case Loop(label, contents):
            check_well_scoped(contents, scope | {label})
        case Block(label, contents, cont):
            check_well_scoped(contents, scope | {label})
            check_well_scoped(cont, scope)
        case _: assert False  # unhandled case

def all_vars(func: StructuredFunction) -> set[str]:
    result: set[str] = set()

    def go(c: Command):
        match c:
            case BBCmd(instrs, cont):
                result.update({ inst['dest'] for inst in instrs if 'dest' in inst })
                go(cont)
            case Block(label, contents, cont):
                go(contents)
                go(cont)
            case Loop(label, contents):
                go(contents)
            case If(b, true, false):
                go(true)
                go(false)
            case Return(): pass
            case Jump(): pass
            case _: assert False  # unhandled case

    go(func.code)
    return result


def to_structured_control_flow(cfg: bril.CFGFunction) -> StructuredFunction:
    # It's relooping time!
    #
    # Raises `Unhandled` if the CFG is irreducible.
    #
    # Two ingredients: dom tree, and reverse postorder numbering
    dom = cfg.dom_tree()
    preds = graph.pairs_to_dict([(b,a) for (a,b) in cfg.edges()])
    numbering = graph.reverse_postorder_number(cfg.edges(), bril.START)

    headers: set[str] = set()
    for s, t in cfg.edges():
        if numbering[t] <= numbering[s]: # back-edge
            if not dom.dominates(t, s): # that's not a loop header
                raise Unhandled(f'Irreducible control flow: {cfg.name}: edge from {s} to {t}')
            headers.add(t)

    def recurse(node: str) -> Command:
        bb = cfg.bbs[node]
        successors = bb.successors()

        # terminator. include code directly if it's also a dom tree child, and
        # is not a merge node
        do_inline = lambda l: len(preds[l]) == 1
        def successor(s) -> Command:
            return recurse(s) if do_inline(s) else Jump(s)

        if bb.term['op'] == 'ret':
            value = None
            if 'args' in bb.term:
                value, = bb.term['args']
            result: Command = Return(value = value)
        elif bb.term['op'] == 'jmp':
            lbl, = bb.term['labels']
            result = successor(lbl)
        elif bb.term['op'] == 'br':
            true, false = bb.term['labels']
            condition, = bb.term['args']
            result = If(condition, successor(true), successor(false))
        else:
            assert False  # bad terminator

        # instructions
        if len(bb.instrs) != 0:
            result = BBCmd(instrs = bb.instrs, cont = result)

        # dom tree children: add labels for the blocks we don't inline
        blocks = [ch for ch in dom.children[node] if ch != bril.END and not do_inline(ch)]
        blocks.sort(key = lambda ch: numbering[ch])
        for ch in blocks:
            result = Block(label = ch, contents = result, cont = recurse(ch))

        # loop header
        if node in headers:
            result = Loop(label = node, contents = result)

        return result

    code = recurse(bril.START)
    check_well_scoped(code)  # debug assertion
    return StructuredFunction(
            name = cfg.name,
            args = cfg.args,
            type = cfg.type,
            code = code,
        )

