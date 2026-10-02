"""Typical sequences (Bodlaender-Kloks, Section 3) on tuples of naturals.

tau            : Def. 3.5 (stack algorithm; same result as any order of operations, Lemma 3.2)
dom(a, b)      : a < b of Def. 3.7 (exists extensions a* <= b* of equal length)
ring(a, b)     : { tau(a* + b*) : a* in E(a), b* in E(b), |a*| = |b*| }   (Def. 3.8, via Lemma 3.17)
splits(y)      : the splits of a typical sequence (Def. 3.10), both types
"""
from functools import lru_cache


def _in_range(z, x, y):
    return min(x, y) <= z <= max(x, y)


@lru_cache(maxsize=None)
def tau(a):
    """Typical sequence of the tuple `a` (stack algorithm)."""
    st = []
    for y in a:
        # cut the stack back to the leftmost index i whose entry sees everything above it
        # inside the interval spanned by t_i and y
        cut = None
        for i, x in enumerate(st):
            if all(_in_range(z, x, y) for z in st[i + 1:]):
                cut = i
                break
        if cut is None:
            st.append(y)
        else:
            x = st[cut]
            if cut == len(st) - 1 and x == y:
                # y repeats the last kept entry
                continue
            del st[cut + 1:]
            st.append(y)
    return tuple(st)


def tau_slow(a):
    """Direct implementation of Def. 3.5 (used only to test `tau`)."""
    a = list(a)
    changed = True
    while changed:
        changed = False
        for i in range(len(a) - 1):
            if a[i] == a[i + 1]:
                del a[i + 1]
                changed = True
                break
        if changed:
            continue
        n = len(a)
        for i in range(n):
            for j in range(i + 2, n):
                if all(_in_range(a[t], a[i], a[j]) for t in range(i + 1, j)):
                    del a[i + 1:j]
                    changed = True
                    break
            if changed:
                break
    return tuple(a)


def dom(a, b):
    """a < b : there are extensions a* of a and b* of b, of the same length, with a* <= b*."""
    n, m = len(a), len(b)
    if n == 0 or m == 0:
        return False
    if a[0] > b[0]:
        return False
    reach = [[False] * m for _ in range(n)]
    reach[0][0] = True
    for i in range(n):
        for j in range(m):
            if not reach[i][j]:
                continue
            for di, dj in ((1, 0), (0, 1), (1, 1)):
                i2, j2 = i + di, j + dj
                if i2 < n and j2 < m and a[i2] <= b[j2]:
                    reach[i2][j2] = True
    return reach[n - 1][m - 1]


@lru_cache(maxsize=None)
def ring(a, b):
    """{ tau(a* + b*) } over extensions of equal length (each a tuple)."""
    n, m = len(a), len(b)
    states = [[set() for _ in range(m)] for _ in range(n)]
    states[0][0].add(tau((a[0] + b[0],)))
    for i in range(n):
        for j in range(m):
            cur = states[i][j]
            if not cur:
                continue
            for di, dj in ((1, 0), (0, 1), (1, 1)):
                i2, j2 = i + di, j + dj
                if i2 < n and j2 < m:
                    z = a[i2] + b[j2]
                    for pre in cur:
                        states[i2][j2].add(tau(pre + (z,)))
    return frozenset(states[n - 1][m - 1])


def ring_path(a, b, want):
    """A monotone lattice path over (a, b) whose sum sequence has tau equal `want`; list of (i, j)."""
    n, m = len(a), len(b)
    # states[i][j] : dict prefix -> predecessor (i', j', prefix')
    states = [[dict() for _ in range(m)] for _ in range(n)]
    states[0][0][tau((a[0] + b[0],))] = None
    for i in range(n):
        for j in range(m):
            for pre in list(states[i][j].keys()):
                for di, dj in ((1, 0), (0, 1), (1, 1)):
                    i2, j2 = i + di, j + dj
                    if i2 < n and j2 < m:
                        np_ = tau(pre + (a[i2] + b[j2],))
                        if np_ not in states[i2][j2]:
                            states[i2][j2][np_] = (i, j, pre)
    if want not in states[n - 1][m - 1]:
        return None
    path = []
    i, j, pre = n - 1, m - 1, want
    while True:
        path.append((i, j))
        pred = states[i][j][pre]
        if pred is None:
            break
        i, j, pre = pred
    path.reverse()
    return path


def splits(y):
    """All splits (d1, d2), both nonempty, of a typical sequence (Def. 3.10):
       type 1 : d1 = y[0..f], d2 = y[f..]      (f = 0 .. s-1)
       type 2 : d1 = y[0..f], d2 = y[f+1..]    (f = 0 .. s-2)"""
    s = len(y)
    out = []
    for f in range(s):
        out.append((y[:f + 1], y[f:]))
    for f in range(s - 1):
        out.append((y[:f + 1], y[f + 1:]))
    return out
