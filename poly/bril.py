# Bril basics
# ~~~~~~~~~~~
#
# Both the simple JSON stuff, and also CFGs and dominator trees.
#
# For example use, see main.py

from util import *
import graph
import json

Typ: TypeAlias = str | dict[str, 'Typ']

class Param(TypedDict):
    name: str
    type: Typ

class Label(TypedDict):
    label: str

class Instr(TypedDict, total=False):
    op: Required[str]
    dest: str
    type: Typ
    args: list[str]
    funcs: list[str]
    labels: list[str]
    value: int | bool

def uses(l: Instr) -> list[str]:
    return l['args'] if 'args' in l else []
def writes(l: Instr) -> list[str]:
    return [l['dest']] if 'dest' in l else []

def is_pure(l: Instr) -> bool:
    return not is_terminator(l) and l['op'] not in ['print', 'call', 'alloc', 'free', 'store', 'load', 'nop']

def is_label(l: Instr | Label) -> TypeGuard[Label]:
    return 'label' in l
def is_instr(l: Instr | Label) -> TypeGuard[Instr]:
    return 'op' in l
def is_terminator(l: Instr | Label) -> bool:
    return is_instr(l) and l['op'] in {'ret', 'br', 'jmp'}

class Function(TypedDict, total=False):
    name: Required[str]
    args: list[Param]
    type: Typ
    instrs: Required[list[Label | Instr]]

class Program(TypedDict):
    functions: list[Function]

def load(fp: Any) -> Program:
    # Load from a file, such as sys.stdin or open('foo.json')
    #
    # FIXME: does not validate the json
    result: Any = json.load(fp)
    return result


# CFG
# ~~~

START = '__START'
END = '__END'

@dataclasses.dataclass
class BB:
    label: str
    instrs: list[Instr]
    term: Instr

    def successors(self) -> set[str]:
        return {END} if self.term['op'] == 'ret' else set(self.term['labels'])

    def debug(self, indent = ''):
        print(indent + f'.{self.label}:')
        for instr in self.instrs:
            print(indent + '  ' + str(instr))
        print(indent + '  ' + str(self.term))

@dataclasses.dataclass
class CFGFunction:
    name: str
    args: list[Param]
    type: Typ | None
    bbs: dict[str, BB]

    def debug(self, indent = ''):
        args = ', '.join(f'{param["name"]}: {param["type"]}' for param in self.args)
        print(indent + f'func @{self.name}({args}) {{')
        for bb in self.bbs.values():
            bb.debug(indent)
        print(f'}}')

    def edges(self) -> list[tuple[str, str]]:
        result = []
        for bb in self.bbs.values():
            for target in bb.successors():
                result.append((bb.label, target))
        return result

    def dom_tree(self) -> graph.DomTree:
        # Please do DCE first
        return graph.dom_tree(self.edges(), START)

    def reverse_dom_tree(self) -> graph.DomTree:
        # Please do DCE first
        return graph.dom_tree([(b, a) for (a, b) in self.edges()], END)

    def dce(self):
        reachable = graph.reachable(self.edges(), [START])
        self.bbs = { l: bb for l, bb in self.bbs.items() if l in reachable }

        # check for non-reverse-reachable blocks
        backwards_reachable = graph.reachable([(b,a) for (a,b) in self.edges()], [END])
        for l in reachable - backwards_reachable:
            raise Unhandled(f'static infinite loop at {self.name} in label {l}')


def function_to_cfg(func: Function) -> CFGFunction:
    name = func['name']
    args = func['args'] if 'args' in func else []
    type = func['type'] if 'type' in func else None

    instrs = func['instrs'] + [{'op': 'ret'}]

    bbs: list[BB] = []
    cur_label: Optional[str] = START
    cur: list[Instr] = []
    for instr in instrs:
        if cur_label is None:
            if not is_label(instr):
                # dead code (no label to reach it, not in a BB)
                continue
            cur_label = instr['label']
        elif is_terminator(instr):
            assert is_instr(instr)
            bbs.append(BB(cur_label, cur, instr))
            cur_label = None
            cur = []
        elif is_label(instr):
            bbs.append(BB(cur_label, cur, { 'op': 'jmp', 'labels': [instr['label']] }))
            cur_label = instr['label']
            cur = []
        else:
            assert is_instr(instr)
            cur.append(instr)

    assert cur == []
    bbs_dict: dict[str, BB] = { bb.label: bb for bb in bbs }

    result = CFGFunction(
            name = name,
            args = args,
            type = type,
            bbs = bbs_dict,
        )
    result.dce()  # dom_tree and friends depend on dce
    return result

