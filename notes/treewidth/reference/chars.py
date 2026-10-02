"""Characteristics of partial tree decompositions: rooted *run trees*.

A characteristic (relative to a boundary B) is a rooted tree; a node is a triple (S, y, kids):
  S     frozenset  subset of B                       (the restricted bag, shared by the whole run)
  y     tuple      typical sequence of bag sizes      (along the run: a chain of same-S tree nodes)
  kids  tuple      sorted canonical order              (children of the LAST tree node of the run)
The root run starts at the *origin* of the partial decomposition, which is never pruned.

normal form (`norm`): (i) a leaf run whose S is contained in its parent's S is junk and is dropped;
(ii) a run with exactly one kid of the same S is merged with it (sequences concatenated, then tau);
(iii) a run without kids keeps only its first entry (the further nodes of the chain are junk leaves).
"""
from itertools import product
from functools import lru_cache
from typical import tau, ring, splits

Char = tuple


@lru_cache(maxsize=None)
def verts(t):
    S, y, K = t
    r = set(S)
    for k in K:
        r |= verts(k)
    return frozenset(r)


def _key(kid, S):
    return tuple(sorted(verts(kid) - S))


def sort_kids(kids, S):
    return tuple(sorted(kids, key=lambda k: _key(k, S)))


@lru_cache(maxsize=None)
def norm(t):
    S, y, K = t
    K2 = []
    for k in K:
        k = norm(k)
        if not k[2] and k[0] <= S:
            continue                       # (i) prunable leaf run
        K2.append(k)
    if not K2:                             # (iii) a leaf run keeps only its first node: the others are junk
        return (S, y[:1], ())
    if len(K2) == 1 and K2[0][0] == S:     # (ii) merge with the single same-S kid
        k = K2[0]
        return (S, tau(y + k[1]), k[2])
    return (S, y, sort_kids(K2, S))


def relabel(t, f):
    S, y, K = t
    return (f(S), y, tuple(relabel(k, f) for k in K))


LEAF = (frozenset(), (0,), ())


def forget(t, x):
    return norm(relabel(t, lambda S: S - {x}))


def max_entry(t):
    S, y, K = t
    return max([max(y)] + [max_entry(k) for k in K])


def join(A, B, kmax):
    """All characteristics of joins of a partial decomposition of char. A with one of char. B."""
    SA, yA, KA = A
    SB, yB, KB = B
    if SA != SB or len(KA) != len(KB):
        return []
    c = len(SA)
    ys = sorted({tuple(z - c for z in t) for t in ring(yA, yB)})
    ys = [t for t in ys if max(t) <= kmax]
    if not ys:
        return []
    kid_opts = []
    for a, b in zip(KA, KB):
        o = join(a, b, kmax)
        if not o:
            return []
        kid_opts.append(o)
    out = []
    for y in ys:
        for combo in product(*kid_opts):
            out.append((SA, y, tuple(combo)))
    return out


# ---------------------------------------------------------------- introduce
def plus1(y):
    return tuple(z + 1 for z in y)


def win(t, v):
    """W contains the first tree node of run t.  Yields (replacement subtree, covered vertex set)."""
    S, y, K = t
    S1 = S | {v}
    out = []
    for (M, R) in splits(y):                       # W ends inside the run
        out.append(((S1, plus1(M), ((S, R, K),)), frozenset(S)))
    kid_choice = []
    for k in K:                                    # W contains the whole run and continues into kids
        kid_choice.append([(k, frozenset())] + win(k, v))
    for combo in product(*kid_choice):
        kids = tuple(c[0] for c in combo)
        cov = set(S)
        for c in combo:
            cov |= c[1]
        out.append(((S1, plus1(y), kids), frozenset(cov)))
    return out


def wtop(t, v):
    """W has its topmost tree node inside run t."""
    S, y, K = t
    out = list(win(t, v))
    for (P, R) in splits(y):
        for (X, cov) in win((S, R, K), v):
            out.append(((S, P, (X,)), cov))
    return out


def all_chains(S, N):
    """The shapes of a new branch hanging at a tree node whose run has label S (needs N <= S): a strictly
    decreasing chain  M_1 > M_2 > ... > M_r  (r >= 0) of subsets of S containing N, followed by a leaf whose label is
    M + {v} with  N <= M <= M_r  (M <= S when r = 0).  Yields (chain, M)."""
    from itertools import combinations
    S, N = frozenset(S), frozenset(N)
    extra = sorted(S - N)
    cands = [N | frozenset(c) for r in range(len(extra) + 1) for c in combinations(extra, r)]
    out = []

    def rec(chain):
        bound = chain[-1] if chain else S
        for M in cands:
            if M <= bound:
                out.append((tuple(chain), M))
        for X in cands:
            if X <= bound and (not chain or X < bound):
                rec(chain + [X])

    rec([])
    return out


def path_subtree(chain, M, v):
    node = (frozenset(M) | {v}, (len(M) + 1,), ())
    for X in reversed(chain):
        node = (frozenset(X), (len(X),), (node,))
    return node


def attach_leaf(t, v, N):
    """v's bag is a new leaf branch (see `new_paths`) hanging at a tree node of run t (needs N <= S)."""
    S, y, K = t
    out = []
    for chain, M in all_chains(S, N):
        br = path_subtree(chain, M, v)
        out.append((S, y, K + (br,)))
        for (P, R) in splits(y):
            out.append((S, P, (br, (S, R, K))))
    return out


def _variants(t, v, N):
    S, y, K = t
    vs = []
    for rep, cov in wtop(t, v):
        if N <= cov:
            vs.append(rep)
    if N <= S:
        vs += attach_leaf(t, v, N)
    for i, k in enumerate(K):
        for kv in _variants(k, v, N):
            vs.append((S, y, K[:i] + (kv,) + K[i + 1:]))
    return vs


def introduce(c, v, N, kmax):
    N = frozenset(N)
    out = set()
    for t in _variants(c, v, N):
        t = norm(t)
        if max_entry(t) <= kmax:
            out.add(t)
    return out


# ------------------------------------------------------------ dominance
def dom_char(a, b):
    """a <= b (a at least as good): same shape, run-wise sequence domination."""
    from typical import dom
    Sa, ya, Ka = a
    Sb, yb, Kb = b
    if Sa != Sb or len(Ka) != len(Kb) or not dom(ya, yb):
        return False
    return all(dom_char(x, y) for x, y in zip(Ka, Kb))


def size(t):
    return 1 + sum(size(k) for k in t[2])


# ------------------------------------------------- introduce with explicit plans (used by extraction)
def win_plans(t, v, lo=0):
    """Like `win`, but the run is entered at typical index `lo`; returns (plan, replacement, covered)."""
    S, y, K = t
    s = len(y)
    S1 = S | {v}
    out = []
    for f in range(lo, s):
        out.append((("end", (1, f)), (S1, plus1(y[lo:f + 1]), ((S, y[f:], K),)), frozenset(S)))
    for f in range(lo, s - 1):
        out.append((("end", (2, f)), (S1, plus1(y[lo:f + 1]), ((S, y[f + 1:], K),)), frozenset(S)))
    kid_choice = [[(None, k, frozenset())] + win_plans(k, v) for k in K]
    for combo in product(*kid_choice):
        cov = set(S)
        for c in combo:
            cov |= c[2]
        out.append((("whole", tuple(c[0] for c in combo)), (S1, plus1(y[lo:]), tuple(c[1] for c in combo)),
                    frozenset(cov)))
    return out


def wtop_plans(t, v):
    S, y, K = t
    s = len(y)
    out = [(("top", None, p), rep, cov) for p, rep, cov in win_plans(t, v, 0)]
    for f in range(s):
        for p, X, cov in win_plans(t, v, f):
            out.append((("top", (1, f), p), (S, y[:f + 1], (X,)), cov))
    for f in range(s - 1):
        for p, X, cov in win_plans(t, v, f + 1):
            out.append((("top", (2, f), p), (S, y[:f + 1], (X,)), cov))
    return out


def attach_plans(t, v, N):
    S, y, K = t
    out = []
    for chain, M in all_chains(S, N):
        br = path_subtree(chain, M, v)
        out.append((("att", None, chain, M), (S, y, K + (br,))))
        for f in range(len(y)):
            out.append((("att", (1, f), chain, M), (S, y[:f + 1], (br, (S, y[f:], K)))))
        for f in range(len(y) - 1):
            out.append((("att", (2, f), chain, M), (S, y[:f + 1], (br, (S, y[f + 1:], K)))))
    return out


def intro_plans(t, v, N, path=()):
    """All (path, plan, unnormalised result) — the same option set as `introduce`."""
    S, y, K = t
    out = []
    for p, rep, cov in wtop_plans(t, v):
        if N <= cov:
            out.append((path, p, rep))
    if N <= S:
        for p, rep in attach_plans(t, v, N):
            out.append((path, p, rep))
    for i, k in enumerate(K):
        for pth, p, rep in intro_plans(k, v, N, path + (i,)):
            out.append((pth, p, (S, y, K[:i] + (rep,) + K[i + 1:])))
    return out
