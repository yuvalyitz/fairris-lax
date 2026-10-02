"""Structured graphs (cycles, grids, complete bipartite, wheels, Petersen, trees): T1 with a min-degree TD and
T2 (wrapper), against brute-force treewidth."""
import sys, time, random
from multiprocessing import Pool
import networkx as nx
import nice as N, improve as I, test_all as T


def named():
    out = {}
    for n in (4, 5, 6, 7, 8):
        out[f"C{n}"] = nx.cycle_graph(n)
    out["grid2x3"] = nx.grid_2d_graph(2, 3)
    out["grid2x4"] = nx.grid_2d_graph(2, 4)
    out["grid3x3"] = nx.grid_2d_graph(3, 3)
    out["K23"] = nx.complete_bipartite_graph(2, 3)
    out["K33"] = nx.complete_bipartite_graph(3, 3)
    out["K44"] = nx.complete_graph(4)
    out["K5"] = nx.complete_graph(5)
    out["wheel6"] = nx.wheel_graph(6)
    out["wheel7"] = nx.wheel_graph(7)
    out["petersen"] = nx.petersen_graph()
    out["tree8"] = nx.random_labeled_tree(8, seed=1)
    out["cube"] = nx.hypercube_graph(3)
    out["prism"] = nx.circular_ladder_graph(4)
    out["2K4"] = nx.disjoint_union(nx.complete_graph(4), nx.complete_graph(4))
    return out


def tasks():
    rnd = random.Random(1)
    for name, g in named().items():
        g = nx.convert_node_labels_to_integers(g)
        edges = sorted(g.edges())
        n = g.number_of_nodes()
        adj = {v: set(g[v]) for v in g}
        tw = N.treewidth(adj)
        for k in sorted({max(1, tw - 1), tw, tw + 1}):
            for mode in ("improve", "wrapper"):
                # min-degree-ish ordering: greedy
                order, rem = [], {v: set(adj[v]) for v in adj}
                while rem:
                    v = min(rem, key=lambda x: (len(rem[x]), x))
                    for a in rem[v]:
                        rem[a] |= rem[v] - {a}
                        rem[a].discard(v)
                    del rem[v]
                    order.append(v)
                yield (mode, edges, n, k, order, 240, name)


def run(task):
    mode, edges, n, k, order, budget, name = task
    r = T.one((mode, edges, n, k, order, budget))
    return (name,) + r


if __name__ == "__main__":
    ts = list(tasks())
    print(len(ts), "tasks", flush=True)
    with Pool(6) as p:
        for r in p.imap_unordered(run, ts):
            print(r[0], r[1], "k=", r[4], "tw=", r[5], "l=", r[6], "t=%.1f" % r[8], flush=True)
