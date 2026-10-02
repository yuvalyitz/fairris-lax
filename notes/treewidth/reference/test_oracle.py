"""Completeness oracle (tables_complete) and the exact-layer equations (char_forget) on random instances:
random graph, random *nice* decomposition (width l), random *global* decomposition Z of width <= k (from a random
elimination order), random origin (root); for every nice node p, the restriction Z|p must be dominated by a table
entry, and  char(Z|p, B\\x) = forget(char(Z|p, B))  at forget nodes."""
import sys, random, time, signal
from multiprocessing import Pool
import nice as N, dp, oracle as O, chars as C, real as R
from test_all import Timeout, _alarm


def task(seed):
    rnd = random.Random(seed)
    n = rnd.randint(3, 7)
    p = rnd.choice([0.25, 0.4, 0.6])
    edges = [(a, b) for a in range(n) for b in range(a + 1, n) if rnd.random() < p]
    adj = {v: set() for v in range(n)}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    tw = N.treewidth(adj)
    k = tw + rnd.choice([0, 0, 1])
    # global decomposition of width <= k
    for _ in range(200):
        order = list(range(n))
        rnd.shuffle(order)
        bag, par = N.elimination_tree(adj, order)
        if max(len(b) for b in bag.values()) - 1 <= k:
            break
    else:
        return ("skip", seed)
    # nice decomposition of width <= k+2
    for _ in range(200):
        o2 = list(range(n))
        rnd.shuffle(o2)
        t = N.nice_from_order(adj, o2)
        if t.width() <= k + 2:
            break
    else:
        return ("skip", seed)
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(120)
    try:
        FS = dp.tables(adj, t, k + 1, prune=True)
        Z0 = O.real_from_elimination(adj, order)
        root = rnd.choice(sorted(Z0.bag))
        Z = O.reroot(Z0, root)
        res = O.check(adj, t, FS, Z, k + 1)
        if res:
            return ("INCOMPLETE", seed, n, edges, k, order, o2)
        # forget equation
        def under(nd):
            s = set(nd.bag)
            for c in nd.kids:
                s |= under(c)
            return s
        for nd in t.nodes():
            if nd.kind == "forget":
                child = nd.kids[0]
                Y = O.restrict(Z, under(nd))
                a = R.run_char(R.analyze(Y, child.bag))
                b = R.run_char(R.analyze(Y, nd.bag))
                if C.forget(a, nd.v) != b:
                    return ("FORGET-EQ", seed, n, edges, k, order, o2)
        # exact-layer statements: char_join_dom and char_intro_dom on the ACTUAL characteristics
        for nd in t.nodes():
            Y = O.restrict(Z, under(nd))
            if nd.kind == "join":
                A, Bn = nd.kids
                ca = R.run_char(R.analyze(O.restrict(Z, under(A)), nd.bag))
                cb = R.run_char(R.analyze(O.restrict(Z, under(Bn)), nd.bag))
                cp = R.run_char(R.analyze(Y, nd.bag))
                if not any(C.dom_char(c, cp) for c in C.join(ca, cb, k + 1)):
                    return ("JOIN-DOM", seed, n, edges, k, order, o2)
            if nd.kind == "intro":
                child = nd.kids[0]
                cq = R.run_char(R.analyze(O.restrict(Z, under(child)), child.bag))
                cp = R.run_char(R.analyze(Y, nd.bag))
                Nn = dp.neighbours_in_bag(adj, nd.v, child.bag)
                if not any(C.dom_char(c, cp) for c in C.introduce(cq, nd.v, Nn, k + 1)):
                    return ("INTRO-DOM", seed, n, edges, k, order, o2)
        return ("ok", seed)
    except Timeout:
        return ("timeout", seed)
    finally:
        signal.alarm(0)


if __name__ == "__main__":
    cnt = int(sys.argv[1])
    stats = {}
    t0 = time.time()
    with Pool(5) as pool:
        for r in pool.imap_unordered(task, range(cnt)):
            stats[r[0]] = stats.get(r[0], 0) + 1
            if r[0] not in ("ok", "skip", "timeout"):
                print(r, flush=True)
    print("FINISHED", stats, round(time.time() - t0))
