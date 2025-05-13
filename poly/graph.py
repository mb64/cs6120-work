# Some graph operations
# ~~~~~~~~~~~~~~~~~~~~~

from util import *


def pairs_to_dict[A,B](pairs: Iterable[tuple[A, B]]) -> dict[A, set[B]]:
    result = defaultdict(set)
    for a, b in pairs:
        result[a].add(b)
    return result

def reachable[A](pairs: Iterable[tuple[A, A]], start: Iterable[A]) -> set[A]:
    edges = pairs_to_dict(pairs)
    reachable = set()
    def go(v):
        if v in reachable: return
        reachable.add(v)
        for t in edges[v]: go(t)
    for v in start: go(v)
    return reachable

def postorder_number[A](pairs: Iterable[tuple[A, A]], start: A) -> dict[A, int]:
    edges = pairs_to_dict(pairs)
    counter = 0
    numbers: dict[A, int] = {}
    def go(v):
        if v in numbers: return
        numbers[v] = -1
        for t in edges[v]: go(t)
        nonlocal counter
        numbers[v] = counter
        counter += 1
    go(start)
    return numbers

def reverse_postorder_number[A](pairs: Iterable[tuple[A, A]], start: A) -> dict[A, int]:
    numbers = postorder_number(pairs, start)
    for l in numbers:
        numbers[l] = len(numbers) - numbers[l]
    return numbers

def dominators[A](pairs: list[tuple[A, A]], start: A) -> set[tuple[A, A]]:
    # REQUIREMENT: all nodes should be reachable from start
    # RETURNS: the tuple X, Y means all paths from start to Y must pass thru X
    succs = pairs_to_dict(pairs)
    preds = pairs_to_dict([(b,a) for (a,b) in pairs])
    doms: dict[A, set[A]] = dict()
    wl = [start]
    while len(wl) != 0:
        l = wl.pop()
        new = {start} if l == start else {l} | set.intersection(*[doms[p] for p in preds[l] if p in doms])
        if l not in doms or doms[l] != new:
            doms[l] = new
            wl += list(succs[l])

    return {(x, y) for y in doms for x in doms[y]}

@dataclasses.dataclass
class DomTree:
    root: str
    children: dict[str, set[str]]
    parents: dict[str, str]
    doms: set[tuple[str, str]]

    def dominates(self, x: str, y: str) -> bool:
        # Does x dominate y?
        return (x, y) in self.doms

def dom_tree(pairs: list[tuple[str, str]], start: str) -> DomTree:
    doms = dominators(pairs, start)

    def lowest(x: str, y: str) -> str:
        if (x, y) in doms:
            return y
        elif (y, x) in doms:
            return x
        assert False  # internal error

    parents: dict[str, str] = {}
    for x, y in doms:
        if x != y:
            parents[y] = lowest(parents[y], x) if y in parents else x
    children = pairs_to_dict([(p, c) for c, p in parents.items()])

    return DomTree(
            root = start,
            children = children,
            parents = parents,
            doms = doms,
        )

