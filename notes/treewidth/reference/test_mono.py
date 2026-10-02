"""Typical-layer monotonicity (forgetC_mono, joinC_mono, introC_mono) on pairs of table entries a' <= a."""
import random, sys, itertools
from networkx.generators.atlas import graph_atlas_g
import nice as N, dp, chars as C
random.seed(5)
graphs = [g for g in graph_atlas_g() if g.number_of_nodes() in (4,)]
checked = {"forget": 0, "intro": 0, "join": 0}
for g in graphs:
    adj = {v: set(g[v]) for v in g}
    order = list(adj); random.shuffle(order)
    t = N.nice_from_order(adj, order)
    for k in (1, 2):
        if t.width() > k + 1:
            continue
        FS = dp.tables(adj, t, k + 1, prune=False)
        for n in t.nodes():
            if n.kind == "leaf":
                continue
            ch = n.kids[0]
            src = sorted(FS[id(ch)], key=repr)
            pairs = [(a1, a) for a in src for a1 in src if a1 != a and C.dom_char(a1, a)]
            random.shuffle(pairs)
            for a1, a in pairs[:6]:
                if n.kind == "forget":
                    assert C.dom_char(C.forget(a1, n.v), C.forget(a, n.v)); checked["forget"] += 1
                elif n.kind == "intro":
                    Nn = dp.neighbours_in_bag(adj, n.v, ch.bag)
                    ra = C.introduce(a, n.v, Nn, k + 1)
                    r1 = C.introduce(a1, n.v, Nn, k + 1)
                    for c in ra:
                        assert any(C.dom_char(d, c) for d in r1), ("introC_mono fails", a1, a, c)
                    checked["intro"] += 1
                else:
                    other = sorted(FS[id(n.kids[1])], key=repr)
                    bs = [b for b in other if C_shape(b) == C_shape(a)] if False else other
                    for b in bs[:6]:
                        for b1 in [b] + [x for x in bs if x != b and C.dom_char(x, b)][:2]:
                            ja = C.join(a, b, k + 1)
                            j1 = C.join(a1, b1, k + 1)
                            for c in ja:
                                assert any(C.dom_char(d, c) for d in j1), ("joinC_mono fails", a1, a, b1, b, c)
                            checked["join"] += 1
print("monotonicity ok", checked)
