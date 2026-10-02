# Wrap/ notes (package C8a)

## Files
* `Analyze.lean`   analyze_char, conn_of_conn_toRT_analyze, analyze_toRT_isTD, analyze_toRT_width, analyze_toRT_char (B' = B)
* `NiceMany.lean`  forgetMany_spec, introMany_spec, conv_spec, fold_spec, fold_nconn
* `Nice.lean`      niceOf_facts, niceOf_spec
* `NiceSize.lean`  niceOf_size_le_uncond (`2*(|V|+1)*size`, no hypothesis)
* `NiceSizeConn.lean` niceOf_size_le (original bound, hypothesis `t.Conn`)
* `Decompose.lean` hasTW_mono, ImproveSpec, decompose_correct, decompose_words, symmOn_of_encodes

## Statement repairs (relative to proofs-todo/Statements.lean)
1. `niceOf_size_le (t : RT)` is FALSE without `t.Conn`: t = node ∅ [4 x node {1,2,3,4} []] has
   size 5, |V| = 4, `(niceOf t).size = 39 > (4+2)*(5+1) = 36`.  Repaired: `niceOf_size_le {t} (hc : t.Conn)`,
   same bound; plus the hypothesis-free `niceOf_size_le_uncond : size ≤ 2*(|V|+1)*size t`.
2. `analyze_toRT_char (B B')` is FALSE for `B' ≠ B` (reassembling sorts the kids by their `B`-keys; the `B'`
   normal form sorts stably, so `B'`-key ties expose the order).  Counterexample (checked with `decide`):
   t = node {1,2} [node {1,4} [node {2} []], node {2,3} [node {1} []]], B = {3,4}, B' = {1,2}.
   Repaired to `B' = B` (= `char_toRT_analyze`); all downstream uses (`mergeReal_spec`) only need `B' = B`.
3. `improve_correct` / `decompose_correct` / `decompose_words` need SYMMETRIC adjacency on the vertices involved
   (see below).  They are proved here with `ImproveSpec adj W` (the conclusion of `improve_correct` for all
   `U ⊆ W`) as an explicit hypothesis; `decompose_correct adj W himp k i` needs `range i ⊆ W`.

## The asymmetric-adjacency issue (`Adj.SymmOn`)
`nbrs adj v B = B.filter (adj v ·)` and the intro clause of `NT.Good` look only at `adj v u` while `adj.graph`
is `fromRel`, i.e. `u ≠ v ∧ (adj u v ∨ adj v u)`.  If `adj 0 1 = false`, `adj 1 0 = true` then
`improve adj 0 (intro 0 (intro 1 leaf))` returns `some _` (checked by `#eval`) although the graph is an edge with
treewidth 1: so `improve_correct`, `tables_sound/complete`, `realize_intro`, `char_intro_dom`, `decompose_*`
are all false for arbitrary `adj`.  (`good_of_isNiceTD`, `PTD.restrict_*`, the join clause do not need symmetry.)

**Minimal hypothesis:** `adj.SymmOn W` where `Adj.SymmOn adj W := ∀ u ∈ W, ∀ v ∈ W, adj u v = adj v u`,
with `W ⊇ nt.under ∪ {vertices introduced}` (for `decompose adj k n`: `W = range n`).  Downstream statements
should take `(hs : adj.SymmOn W)` and `nt.under ⊆ W`; with it `hs.graph_adj_iff : adj.graph.Adj u v ↔ u ≠ v ∧ adj u v = true`
on `W`, which is all that is used.

**The word encoding satisfies it:** `symmOn_of_encodes`: if `hadj : ∀ u v : Fin n, adj u v = true ↔ G.Adj u v ∨ G.Adj v u`
(the hypothesis of `decompose_words`) then `adj.SymmOn (range n)` (proved; and `graph_adj_of_encodes` shows
`adj.graph.Adj u v ↔ (liftGraph G).Adj u v` for `u, v < n`).  Outside `range n` `adj` is unconstrained, which is
harmless since `decompose adj k n` only touches vertices `< n`.
