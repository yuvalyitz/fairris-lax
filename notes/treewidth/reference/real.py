"""Phase B: realising characteristics by explicit rooted tree decompositions ("realizers").

A realizer of a table entry c at a nice node p is a rooted tree decomposition Y of G^+_p (bags = Finset of
vertices) whose actual characteristic is *dominated by* c (char(Y) <= c).  It is built bottom-up along a derivation
of c; every step is a local surgery on the realizer, guided by the typical-level plan and by witnesses of the
typical sequences inside the exact chains:

  forget   : the tree is unchanged
  introduce: pick a typical-level plan whose result is dominated by the target; cut chains at witnesses, add v
  join     : per run a monotone lattice path over the two exact size sequences whose tau-sum is dominated
"""
from itertools import product
import chars as C
from typical import tau, dom


class Real:
    def __init__(self):
        self.bag, self.kids, self.par = {}, {}, {}
        self.root, self.nxt = None, 0

    def new(self, bag, parent=None):
        i = self.nxt
        self.nxt += 1
        self.bag[i], self.kids[i], self.par[i] = set(bag), [], parent
        if parent is None:
            self.root = i
        else:
            self.kids[parent].append(i)
        return i

    def copy(self):
        r = Real()
        r.bag = {i: set(b) for i, b in self.bag.items()}
        r.kids = {i: list(k) for i, k in self.kids.items()}
        r.par = dict(self.par)
        r.root, r.nxt = self.root, self.nxt
        return r

    def as_td(self):
        ids = sorted(self.bag)
        idx = {i: j for j, i in enumerate(ids)}
        bags = [frozenset(self.bag[i]) for i in ids]
        edges = [(idx[p], idx[c]) for p in ids for c in self.kids[p]]
        return bags, edges

    def width(self):
        return max(len(b) for b in self.bag.values()) - 1


# ------------------------------------------------------------------ analysis (the actual characteristic)
class Run:
    __slots__ = ("S", "nodes", "sizes", "kids")

    def __init__(self, S, nodes, sizes, kids):
        self.S, self.nodes, self.sizes, self.kids = S, nodes, sizes, kids


def run_char(r):
    return (r.S, tau(tuple(r.sizes)), tuple(run_char(k) for k in r.kids))


def analyze(real, B):
    B = frozenset(B)

    def go(n):
        return Run(frozenset(real.bag[n]) & B, [n], [len(real.bag[n])], [go(c) for c in real.kids[n]])

    def normrun(r):
        kids = [normrun(k) for k in r.kids]
        kids = [k for k in kids if not (not k.kids and k.S <= r.S)]
        if len(kids) == 1 and kids[0].S == r.S:
            k = kids[0]
            r.nodes, r.sizes, r.kids = r.nodes + k.nodes, r.sizes + k.sizes, k.kids
        else:
            r.kids = sorted(kids, key=lambda k: C._key(run_char(k), r.S))
        return r

    return normrun(go(real.root))


def witnesses(a):
    """Indices w_1 < ... < w_s into the exact sequence `a` of the entries of tau(a) (stack algorithm)."""
    st = []
    for j, y in enumerate(a):
        cut = None
        for i, (x, _) in enumerate(st):
            if all(min(x, y) <= z <= max(x, y) for z, _ in st[i + 1:]):
                cut = i
                break
        if cut is None:
            st.append((y, j))
        else:
            if cut == len(st) - 1 and st[cut][0] == y:
                continue
            del st[cut + 1:]
            st.append((y, j))
    return [j for _, j in st]


# ------------------------------------------------------------------ chain surgery
def core_child_roots(run):
    return [k.nodes[0] for k in run.kids]


def dup_after(real, run, nodes, i):
    """Insert a copy of nodes[i] (same bag) as its chain successor; returns nothing, updates `nodes`."""
    n = nodes[i]
    if i < len(nodes) - 1:
        succ = [nodes[i + 1]]
    else:
        succ = core_child_roots(run)
    d = real.new(real.bag[n], n)              # appended to kids[n]
    real.kids[n] = [c for c in real.kids[n] if c not in succ]
    for c in succ:
        real.par[c] = d
        real.kids[d].append(c)
    nodes.insert(i + 1, d)


def do_cut(real, run, nodes, sizes, wpos, y, cut):
    """Cut the exact chain at the typical split `cut` = (typ, f) (absolute index into y).
    Returns c such that the left piece is nodes[:c+1] (and, for typ 1, a duplicate has been inserted at c+1)."""
    typ, f = cut
    if typ == 1:
        c = wpos[f]
        dup_after(real, run, nodes, c)
        sizes.insert(c + 1, sizes[c])
        return c
    rising = y[f] < y[f + 1]
    return wpos[f] if rising else wpos[f + 1] - 1


def add_v(real, ids, v):
    for n in ids:
        real.bag[n].add(v)


def apply_win(real, run, plan, v, lo_cut=None):
    """Apply a win-plan on the run `run` whose first tree node is in W (after an optional pre-cut done by caller)."""
    raise NotImplementedError


def apply_plan(real, root_run, path, plan, v, N):
    run = root_run
    for i in path:
        run = run.kids[i]
    nodes, sizes = list(run.nodes), list(run.sizes)
    y = tau(tuple(sizes))
    wpos = witnesses(sizes)
    kind = plan[0]
    if kind == "att":
        cut = plan[1]
        if cut is None:
            x = nodes[-1]
        else:
            c = do_cut(real, run, nodes, sizes, wpos, y, cut)
            x = nodes[c]
        _, _, chain, M = plan
        parent = x
        for X in chain:
            parent = real.new(set(X), parent)
        real.new(set(M) | {v}, parent)
        return
    # kind == "top": ("top", pre, wplan)
    _, pre, wplan = plan

    def process(run, nodes, sizes, wpos, y, pre, wplan):
        """W starts at chain position after the optional pre-cut; wplan = ('end', cut) | ('whole', kidplans)."""
        end_idx = None
        if wplan[0] == "end":
            c2 = do_cut(real, run, nodes, sizes, wpos, y, wplan[1])
            end_idx = c2
        # pre cut (to the left of c2, computed on the same witness positions)
        if pre is None:
            start = 0
        else:
            c1 = do_cut(real, run, nodes, sizes, wpos, y, pre)
            start = c1 + 1
            if pre[0] == 1 and end_idx is not None:
                end_idx += 1
        if end_idx is None:
            mid = nodes[start:]
        else:
            mid = nodes[start:end_idx + 1]
        add_v(real, mid, v)
        if wplan[0] == "whole":
            for kr, kp in zip(run.kids, wplan[1]):
                if kp is not None:
                    apply_kid(kr, kp)

    def apply_kid(kr, kp):
        # kid plan is ('end', cut) or ('whole', ...) with lo = 0, W contains the first node
        knodes, ksizes = list(kr.nodes), list(kr.sizes)
        ky = tau(tuple(ksizes))
        kw = witnesses(ksizes)
        process(kr, knodes, ksizes, kw, ky, None, kp)

    process(run, nodes, sizes, wpos, y, pre, wplan)


def realize_introduce(real, B, v, N, target, kmax):
    """New realizer for the introduce node; its actual characteristic is dominated by `target`."""
    ra = analyze(real, B)
    ca = run_char(ra)
    for path, plan, rep in C.intro_plans(ca, v, frozenset(N)):
        t = C.norm(rep)
        if C.max_entry(t) > kmax or not C.dom_char(t, target):
            continue
        new = real.copy()
        rnew = analyze(new, B)      # same structure as ra (deterministic)
        apply_plan(new, rnew, path, plan, v, N)
        return new
    raise AssertionError("no plan dominated by the target: monotonicity failure")


# ------------------------------------------------------------------ join
def find_path(a, b, S, want):
    """Monotone lattice path over exact sequences a, b with tau(sums) - |S| dominated by `want`."""
    n, m = len(a), len(b)
    c = len(S)
    st = [[dict() for _ in range(m)] for _ in range(n)]
    st[0][0][tau((a[0] + b[0],))] = None
    for i in range(n):
        for j in range(m):
            for pre in list(st[i][j]):
                for di, dj in ((1, 0), (0, 1), (1, 1)):
                    i2, j2 = i + di, j + dj
                    if i2 < n and j2 < m:
                        q = tau(pre + (a[i2] + b[j2],))
                        if q not in st[i2][j2]:
                            st[i2][j2][q] = (i, j, pre)
    for e in st[n - 1][m - 1]:
        if dom(tuple(z - c for z in e), want):
            path = []
            i, j, pre = n - 1, m - 1, e
            while True:
                path.append((i, j))
                pr = st[i][j][pre]
                if pr is None:
                    break
                i, j, pre = pr
            path.reverse()
            return path
    return None


def junk_children(real, run, idx):
    n = run.nodes[idx]
    if idx < len(run.nodes) - 1:
        core = {run.nodes[idx + 1]}
    else:
        core = set(core_child_roots(run))
    return [c for c in real.kids[n] if c not in core]


def copy_subtree(src, n, dst, parent):
    m = dst.new(src.bag[n], parent)
    for c in src.kids[n]:
        copy_subtree(src, c, dst, m)
    return m


def merge_runs(RA, ra, RB, rb, target, new, parent):
    path = find_path(ra.sizes, rb.sizes, ra.S, target[1])
    assert path is not None, "no dominated path"
    chain = []
    seenA, seenB = set(), set()
    for t, (i, j) in enumerate(path):
        bag = RA.bag[ra.nodes[i]] | RB.bag[rb.nodes[j]]
        n = new.new(bag, parent if t == 0 else chain[-1])
        chain.append(n)
        if i not in seenA:
            seenA.add(i)
            for c in junk_children(RA, ra, i):
                copy_subtree(RA, c, new, n)
        if j not in seenB:
            seenB.add(j)
            for c in junk_children(RB, rb, j):
                copy_subtree(RB, c, new, n)
    for ka, kb, kt in zip(ra.kids, rb.kids, target[2]):
        merge_runs(RA, ka, RB, kb, kt, new, chain[-1])


def realize_join(RA, BA, RB, BB, target, kmax):
    aA, aB = analyze(RA, BA), analyze(RB, BB)
    cA, cB = run_char(aA), run_char(aB)
    for d in C.join(cA, cB, kmax):
        if C.dom_char(d, target):
            new = Real()
            merge_runs(RA, aA, RB, aB, d, new, None)
            return new
    raise AssertionError("no dominated join option: monotonicity failure")


# ------------------------------------------------------------------ the extraction driver
def realize(adj, nice, FS, kmax, node, c):
    """Real tree decomposition of G^+_node whose actual characteristic is dominated by c (c in FS[node])."""
    if node.kind == "leaf":
        r = Real()
        r.new(set())
        return r
    if node.kind == "forget":
        ch = node.kids[0]
        for cq in FS[id(ch)]:
            if C.forget(cq, node.v) == c:
                return realize(adj, nice, FS, kmax, ch, cq)
        raise AssertionError("no predecessor")
    if node.kind == "intro":
        ch = node.kids[0]
        N = frozenset(w for w in adj[node.v] if w in ch.bag)
        for cq in FS[id(ch)]:
            if c in C.introduce(cq, node.v, N, kmax):
                Y = realize(adj, nice, FS, kmax, ch, cq)
                return realize_introduce(Y, ch.bag, node.v, N, c, kmax)
        raise AssertionError("no predecessor")
    a, b = node.kids
    for ca in FS[id(a)]:
        for cb in FS[id(b)]:
            if ca[0] == cb[0] and c in C.join(ca, cb, kmax):
                YA = realize(adj, nice, FS, kmax, a, ca)
                YB = realize(adj, nice, FS, kmax, b, cb)
                return realize_join(YA, a.bag, YB, b.bag, c, kmax)
    raise AssertionError("no predecessor")


# ------------------------------------------------------------------ Kloks: rooted decomposition -> nice
def niceify(real, keep_root=True):
    import nice as N

    def build(n):
        X = frozenset(real.bag[n])
        ts = []
        for c in real.kids[n]:
            t = build(c)
            for x in sorted(t.bag - X):
                t = N.forget(x, t)
            for x in sorted(X - t.bag):
                t = N.intro(x, t)
            ts.append(t)
        if not ts:
            t = N.leaf()
            for x in sorted(X):
                t = N.intro(x, t)
            return t
        t = ts[0]
        for u in ts[1:]:
            t = N.join(t, u)
        return t

    return build(real.root)
