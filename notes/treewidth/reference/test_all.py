"""Test harness: compares the reference algorithm with brute-force treewidth.

  python3 test_all.py decide  NMAX KMAX EXTRA PER   # Phase A only (decision), all atlas graphs with <= NMAX vertices
  python3 test_all.py improve NMAX KMAX EXTRA PER   # T1 with extraction, output validated (l <= k+1+EXTRA)
  python3 test_all.py wrapper NMAX KMAX             # T2 (vertex-by-vertex), output validated
  python3 test_all.py random  N P KMAX EXTRA COUNT  # random G(N,P) graphs (any N)
"""
import sys, random, time, signal, itertools
from multiprocessing import Pool
import nice as N, dp, improve as I, real as R, chars as C


class Timeout(Exception):
    pass


def _alarm(sig, frm):
    raise Timeout()


def one(task):
    mode, edges, n, k, order, budget = task
    adj = {v: set() for v in range(n)}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    tw = N.treewidth(adj)
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(budget)
    t0 = time.time()
    try:
        if mode == "decide":
            t = N.nice_from_order(adj, order)
            FS = dp.tables(adj, t, k + 1, prune=True)
            got = bool(FS[id(t)])
            ok = got == (tw <= k)
            return ("ok" if ok else "MISMATCH", edges, n, k, tw, t.width(), order, time.time() - t0)
        if mode == "improve":
            t = N.nice_from_order(adj, order)
            out = I.improve(adj, t, k, check=True)
            if out is None:
                ok = tw > k
            else:
                ok = tw <= k and N.is_nice_td(adj, out, k)
            return ("ok" if ok else "MISMATCH", edges, n, k, tw, t.width(), order, time.time() - t0)
        if mode == "wrapper":
            out = I.decompose(adj, k, check=True)
            if out is None:
                ok = tw > k
            else:
                ok = tw <= k and N.is_nice_td(adj, out, k)
            return ("ok" if ok else "MISMATCH", edges, n, k, tw, -1, order, time.time() - t0)
    except Timeout:
        return ("timeout", edges, n, k, tw, -1, order, budget)
    except AssertionError as e:
        return ("ASSERT " + str(e), edges, n, k, tw, -1, order, time.time() - t0)
    finally:
        signal.alarm(0)


def tasks_atlas(mode, nmax, kmax, extra, per, budget, seed=11):
    from networkx.generators.atlas import graph_atlas_g
    rnd = random.Random(seed)
    for g in graph_atlas_g():
        n = g.number_of_nodes()
        if not 1 <= n <= nmax:
            continue
        edges = sorted(g.edges())
        adj = {v: set(g[v]) for v in g}
        for k in range(0, kmax + 1):
            got = 0
            tries = 0
            while got < per and tries < 80:
                tries += 1
                order = list(range(n))
                rnd.shuffle(order)
                if mode == "wrapper":
                    yield (mode, edges, n, k, order, budget)
                    got = per
                    continue
                t = N.nice_from_order(adj, order)
                if t.width() > k + 1 + extra:
                    continue
                got += 1
                yield (mode, edges, n, k, order, budget)


if __name__ == "__main__":
    mode = sys.argv[1]
    budget = 60
    if mode == "random":
        n, p, kmax, extra, count = int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
        rnd = random.Random(3)
        tasks = []
        for _ in range(count):
            edges = [(a, b) for a in range(n) for b in range(a + 1, n) if rnd.random() < p]
            adj = {v: set() for v in range(n)}
            for a, b in edges:
                adj[a].add(b)
                adj[b].add(a)
            for k in range(1, kmax + 1):
                for _ in range(20):
                    order = list(range(n))
                    rnd.shuffle(order)
                    if N.nice_from_order(adj, order).width() <= k + 1 + extra:
                        tasks.append(("improve", edges, n, k, order, budget))
                        break
    else:
        nmax, kmax = int(sys.argv[2]), int(sys.argv[3])
        extra = int(sys.argv[4]) if len(sys.argv) > 4 else 1
        per = int(sys.argv[5]) if len(sys.argv) > 5 else 1
        tasks = list(tasks_atlas(mode, nmax, kmax, extra, per, budget))
    print(len(tasks), "tasks", flush=True)
    t0 = time.time()
    stats = {}
    with Pool(6) as pool:
        for i, r in enumerate(pool.imap_unordered(one, tasks, chunksize=1)):
            stats[r[0]] = stats.get(r[0], 0) + 1
            if r[0] not in ("ok", "timeout"):
                print(r, flush=True)
            if i % 200 == 0:
                print(i, stats, round(time.time() - t0), flush=True)
    print("FINISHED", stats, round(time.time() - t0))
