"""Phase A: the decision tables FS(p) over a nice tree decomposition."""
import chars as C


def neighbours_in_bag(adj, v, bag):
    return frozenset(w for w in adj[v] if w in bag)


def tables(adj, nice, kmax, prune=False):
    """Returns a dict id(node) -> set of characteristics (FS)."""
    FS = {}

    def rec(n):
        if id(n) in FS:
            return FS[id(n)]
        if n.kind == "leaf":
            res = {C.LEAF}
        elif n.kind == "forget":
            res = {C.forget(c, n.v) for c in rec(n.kids[0])}
        elif n.kind == "intro":
            child = n.kids[0]
            N = neighbours_in_bag(adj, n.v, child.bag)
            res = set()
            for c in rec(child):
                res |= C.introduce(c, n.v, N, kmax)
        else:
            A, B = rec(n.kids[0]), rec(n.kids[1])
            res = set()
            byshape = {}
            for b in B:
                byshape.setdefault(C_shape(b), []).append(b)
            for a in A:
                for b in byshape.get(C_shape(a), []):
                    res.update(C.join(a, b, kmax))
        if prune:
            res = prune_dominated(res)
        FS[id(n)] = res
        return res

    rec(nice)
    return FS


def C_shape(t):
    S, y, K = t
    return (S, tuple(C_shape(k) for k in K))


def prune_dominated(res):
    """Keep only the minimal characteristics (Definition 4.6 / 5.11: a full set may be thinned by dominance)."""
    by = {}
    for c in res:
        by.setdefault(C_shape(c), []).append(c)
    out = set()
    for group in by.values():
        for c in group:
            if not any(d != c and C.dom_char(d, c) for d in group):
                out.add(c)
    return out
