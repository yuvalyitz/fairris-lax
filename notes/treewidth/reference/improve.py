"""T1 (improveDecomposition) and T2 (vertex-by-vertex wrapper), reference implementation."""
import chars as C, dp, real as R, nice as N


def improve(adj, nice, k, check=False, prune=True):
    """Given a nice decomposition of G, return a nice decomposition of width <= k, or None (tw > k)."""
    kmax = k + 1
    FS = dp.tables(adj, nice, kmax, prune=prune)
    root = FS[id(nice)]
    if not root:
        return None
    c = sorted(root, key=repr)[0]
    Y = R.realize(adj, nice, FS, kmax, nice, c)
    if check:
        a = R.analyze(Y, nice.bag)
        assert C.dom_char(R.run_char(a), c), "root realizer not dominated"
    return R.niceify(Y)


def insert_everywhere(t, v):
    if t.kind == "leaf":
        return N.intro(v, N.leaf())
    kids = [insert_everywhere(c, v) for c in t.kids]
    return N.Nice(t.kind, t.bag | {v}, t.v, kids)


def decompose(adj, k, check=False):
    """T2: nice decomposition of G of width <= k, or None."""
    cur = N.leaf()
    cur_adj = {}
    for v in sorted(adj):
        cur_adj = {u: set(nb) for u, nb in cur_adj.items()}
        cur_adj[v] = {w for w in adj[v] if w in cur_adj}
        for w in cur_adj[v]:
            cur_adj[w].add(v)
        t = insert_everywhere(cur, v)
        cur = improve(cur_adj, t, k, check)
        if cur is None:
            return None
        if check:
            assert N.is_nice_td(cur_adj, cur, k), "output is not a nice TD of width <= k"
    return cur
