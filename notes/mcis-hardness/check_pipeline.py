import itertools, random

def alpha(n, adj):
    best = 0
    # simple branch and bound MIS
    order = list(range(n))
    def rec(cands, size):
        nonlocal best
        if size + len(cands) <= best: return
        if not cands:
            best = max(best, size); return
        v = cands[0]
        rec([u for u in cands[1:] if u not in adj[v]], size+1)
        rec(cands[1:], size)
    rec(order, 0)
    return best

def gadget(r):
    # K_{r+2} minus path b-a-c and a perfect matching on the other r-1 vertices; a = vertex 0
    assert r % 2 == 1 and r >= 3
    m = r + 2
    a, b, c = 0, 1, 2
    rest = list(range(3, m))
    assert len(rest) % 2 == 0
    removed = {frozenset((a,b)), frozenset((a,c))}
    for i in range(0, len(rest), 2): removed.add(frozenset((rest[i], rest[i+1])))
    edges = {frozenset(p) for p in itertools.combinations(range(m), 2)} - removed
    return m, edges

def regularise(n, edges, r):
    edges = set(map(frozenset, edges))
    deg = [sum(1 for e in edges if v in e) for v in range(n)]
    assert max(deg, default=0) <= r
    N = n; gadgets = 0
    for v in range(n):
        for _ in range(r - deg[v]):
            m, ge = gadget(r)
            base = N
            for e in ge: edges.add(frozenset(x + base for x in e))
            edges.add(frozenset((v, base + 0)))   # attach a
            N += m; gadgets += 1
    return N, edges, gadgets

def to_adj(n, edges):
    adj = [set() for _ in range(n)]
    for e in edges:
        u, v = tuple(e); adj[u].add(v); adj[v].add(u)
    return adj

def mcis_instance(n, edges, k):
    # k classes, each a copy of V; (i,u)~(j,v) for i!=j iff u==v or uv in E
    E = {frozenset(e) for e in edges}
    verts = [(i, u) for i in range(k) for u in range(n)]
    def adjf(x, y):
        (i, u), (j, v) = x, y
        return i != j and (u == v or frozenset((u, v)) in E)
    return verts, adjf

def has_indep_transversal(n, k, adjf):
    for f in itertools.product(range(n), repeat=k):
        if all(not adjf((i, f[i]), (j, f[j])) for i in range(k) for j in range(i+1, k)):
            return True
    return False

random.seed(1)
# 1. gadget properties
for r in (3, 5, 7):
    m, ge = gadget(r); adj = to_adj(m, ge)
    degs = [len(adj[v]) for v in range(m)]
    assert degs[0] == r - 1 and all(d == r for d in degs[1:]), degs
    a1 = alpha(m, adj)
    adj2 = [set(x for x in adj[v] if x != 0) for v in range(m)]
    # alpha(X - a)
    sub = [v for v in range(1, m)]
    idx = {v: i for i, v in enumerate(sub)}
    adjs = [set(idx[u] for u in adj[v] if u != 0) for v in sub]
    a2 = alpha(len(sub), adjs)
    assert a1 == 2 and a2 == 2, (r, a1, a2)
print("gadget ok for r=3,5,7 (deg, alpha=2 with and without a)")

# 2. regularisation preserves alpha up to +2*gadgets, gives r-regular
tested = 0
for trial in range(60):
    n = random.randint(1, 6)
    edges = [e for e in itertools.combinations(range(n), 2) if random.random() < 0.4]
    Delta = max([sum(1 for e in edges if v in e) for v in range(n)] + [0])
    r = Delta if Delta % 2 == 1 else Delta + 1
    r = max(r, 3)
    N, E2, g = regularise(n, edges, r)
    adj2 = to_adj(N, E2)
    assert all(len(adj2[v]) == r for v in range(N)), "not regular"
    a0 = alpha(n, to_adj(n, edges))
    if N <= 40:
        a1 = alpha(N, adj2)
        assert a1 == a0 + 2 * g, (n, edges, r, a0, a1, g)
        tested += 1
print("regularisation ok on", tested, "random graphs (alpha shift = 2 per gadget, r-regular)")

# 3. copy reduction to MCIS and Normal form
tested = 0
for trial in range(40):
    n = random.randint(2, 5)
    edges = [e for e in itertools.combinations(range(n), 2) if random.random() < 0.4]
    Delta = max([sum(1 for e in edges if v in e) for v in range(n)] + [0])
    r = max(3, Delta if Delta % 2 == 1 else Delta + 1)
    N, E2, g = regularise(n, edges, r)
    alph = alpha(n, to_adj(n, edges))
    for k in range(2, 4):
        kk = k + 2 * g          # IS target on the regularised graph
        # MCIS instance with kk classes over N vertices: too big to brute force for large kk; check structure only
        verts, adjf = mcis_instance(N, E2, kk)
        # regular of degree (kk-1)*(r+1)
        deg = {x: sum(1 for y in verts if adjf(x, y)) for x in verts[:N]}
        assert all(d == (kk - 1) * (r + 1) for d in deg.values())
        ecount = sum(1 for x in verts for y in verts if x < y and adjf(x, y))
        assert ecount % 2 == 0 and N >= 4
        tested += 1
print("MCIS structure ok:", tested, "cases: regular degree (k-1)(r+1), even edges, size>=4")

# 4. equivalence of the copy reduction on tiny graphs (brute force transversals)
for trial in range(40):
    n = random.randint(2, 5)
    edges = [e for e in itertools.combinations(range(n), 2) if random.random() < 0.4]
    E = {frozenset(e) for e in edges}
    alph = alpha(n, to_adj(n, edges))
    for k in range(2, 5):
        verts, adjf = mcis_instance(n, edges, k)
        assert has_indep_transversal(n, k, adjf) == (alph >= k), (n, edges, k, alph)
print("copy reduction equivalence ok (MCIS yes iff alpha >= k)")
