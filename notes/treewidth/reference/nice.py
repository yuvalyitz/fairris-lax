"""Nice tree decompositions (rooted trees, kinds leaf / introduce / forget / join), brute-force treewidth,
and a checker for tree decompositions.  Graphs are dicts  vertex -> set(neighbours)."""
import itertools, random


class Nice:
    __slots__ = ("kind", "v", "kids", "bag")

    def __init__(self, kind, bag, v=None, kids=()):
        self.kind, self.bag, self.v, self.kids = kind, frozenset(bag), v, list(kids)

    def width(self):
        return max([len(self.bag) - 1] + [k.width() for k in self.kids])

    def nodes(self):
        for k in self.kids:
            yield from k.nodes()
        yield self


def leaf():
    return Nice("leaf", ())


def intro(v, t):
    return Nice("intro", t.bag | {v}, v, [t])


def forget(v, t):
    return Nice("forget", t.bag - {v}, v, [t])


def join(a, b):
    assert a.bag == b.bag
    return Nice("join", a.bag, None, [a, b])


def elimination_tree(adj, order):
    pos = {v: i for i, v in enumerate(order)}
    g = {v: set(adj[v]) for v in adj}
    bag, parent = {}, {}
    for v in order:
        later = {w for w in g[v] if pos[w] > pos[v]}
        bag[v] = frozenset(later | {v})
        for a in later:
            for b in later:
                if a != b:
                    g[a].add(b)
        parent[v] = min(later, key=lambda w: pos[w]) if later else None
    return bag, parent


def nice_from_order(adj, order):
    bag, parent = elimination_tree(adj, order)
    kids = {v: [] for v in adj}
    roots = []
    for v in order:
        (roots if parent[v] is None else kids[parent[v]]).append(v)

    def build(v):
        ts = []
        for c in kids[v]:
            t = build(c)
            for x in sorted(bag[c] - bag[v]):
                t = forget(x, t)
            for x in sorted(bag[v] - t.bag):
                t = intro(x, t)
            ts.append(t)
        if not ts:
            t = leaf()
            for x in sorted(bag[v]):
                t = intro(x, t)
            return t
        t = ts[0]
        for u in ts[1:]:
            t = join(t, u)
        return t

    trees = []
    for r in roots:
        t = build(r)
        for x in sorted(t.bag):
            t = forget(x, t)
        trees.append(t)
    if not trees:
        return leaf()
    t = trees[0]
    for u in trees[1:]:
        t = join(t, u)
    return t


def is_nice_td(adj, t, width_bound=None):
    """Checks: shapes of the four kinds, and that the bags form a tree decomposition of adj."""
    bags = []
    edges = []

    def rec(n):
        i = len(bags)
        bags.append(n.bag)
        if n.kind == "leaf":
            assert not n.kids and not n.bag
        elif n.kind == "intro":
            (c,) = n.kids
            assert n.v not in c.bag and n.bag == c.bag | {n.v}
        elif n.kind == "forget":
            (c,) = n.kids
            assert n.v in c.bag and n.bag == c.bag - {n.v}
        else:
            a, b = n.kids
            assert n.bag == a.bag == b.bag
        for c in n.kids:
            j = rec(c)
            edges.append((i, j))
        return i

    rec(t)
    return is_td(adj, bags, edges, width_bound)


def is_td(adj, bags, edges, width_bound=None):
    n = len(bags)
    if width_bound is not None and any(len(b) > width_bound + 1 for b in bags):
        return False
    if any(v not in set().union(*bags) for v in adj) if bags else bool(adj):
        return False
    for v in adj:
        for w in adj[v]:
            if not any(v in b and w in b for b in bags):
                return False
    # tree
    if len(edges) != n - 1:
        return False
    nb = {i: [] for i in range(n)}
    for a, b in edges:
        nb[a].append(b)
        nb[b].append(a)
    seen = {0}
    st = [0]
    while st:
        x = st.pop()
        for y in nb[x]:
            if y not in seen:
                seen.add(y)
                st.append(y)
    if len(seen) != n:
        return False
    for v in adj:
        occ = [i for i in range(n) if v in bags[i]]
        if not occ:
            return False
        seen = {occ[0]}
        st = [occ[0]]
        while st:
            x = st.pop()
            for y in nb[x]:
                if v in bags[y] and y not in seen:
                    seen.add(y)
                    st.append(y)
        if len(seen) != len(occ):
            return False
    return True


def treewidth(adj):
    """Exact treewidth by DP over vertex subsets (n <= ~12)."""
    vs = sorted(adj)
    n = len(vs)
    if n == 0:
        return -1
    idx = {v: i for i, v in enumerate(vs)}
    nbm = [0] * n
    for v in vs:
        for w in adj[v]:
            nbm[idx[v]] |= 1 << idx[w]
    full = (1 << n) - 1

    def q(S, v):
        # vertices outside S+{v} reachable from v through S
        seen = 1 << v
        frontier = 1 << v
        res = 0
        while frontier:
            u = (frontier & -frontier).bit_length() - 1
            frontier &= frontier - 1
            nxt = nbm[u] & ~seen
            seen |= nxt
            res |= nxt & ~S
            frontier |= nxt & S
        return bin(res & ~(1 << v)).count("1")

    tw = {0: -1}
    for S in range(1, full + 1):
        best = n
        T = S
        while T:
            v = (T & -T).bit_length() - 1
            T &= T - 1
            S2 = S & ~(1 << v)
            val = max(tw[S2], q(S2, v))
            if val < best:
                best = val
        tw[S] = best
    return tw[full]
