"""Completeness oracle: restrict a real global tree decomposition Z to every nice node p and check that
FS(p) contains an entry dominated-by... i.e. an entry c with  c <= char(Z|p)."""
import itertools
import nice as N, dp, chars as C, real as R


def real_from_elimination(adj, order, root_choice=0):
    bag, parent = N.elimination_tree(adj, order)
    r = R.Real()
    ids = {}
    roots = [v for v in order if parent[v] is None]
    # connect forest roots under the first root
    def build(v, par):
        i = r.new(bag[v], par)
        ids[v] = i
        for w in order:
            if parent[w] == v:
                build(w, i)
    build(roots[0], None)
    for x in roots[1:]:
        build(x, ids[roots[0]])
    # rerooting is not needed: any node can be the origin in the DP (all restrictions share the tree)
    return r


def reroot(real, new_root):
    r = R.Real()
    order = []
    adjl = {i: set(real.kids[i]) | ({real.par[i]} if real.par[i] is not None else set()) for i in real.bag}
    m = {}
    def go(i, p, par):
        j = r.new(real.bag[i], par)
        m[i] = j
        for c in adjl[i]:
            if c != p:
                go(c, i, j)
    go(new_root, None, None)
    return r


def restrict(real, U):
    r = real.copy()
    for i in r.bag:
        r.bag[i] &= U
    return r


def check(adj, nice, FS, Z, kmax, verbose=False):
    """Returns the first nice node (post-order) whose restriction is not dominated by any table entry."""
    def under(n):
        s = set(n.bag)
        for c in n.kids:
            s |= under(c)
        return s
    for n in nice.nodes():
        U = under(n)
        Y = restrict(Z, U)
        ch = R.run_char(R.analyze(Y, n.bag))
        if not any(C.dom_char(c, ch) for c in FS[id(n)]):
            return n, ch
    return None
