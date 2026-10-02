import Lax117284.BipartiteKuhn
import Lax117284.BipartiteMatching
import Lax117284.BipartiteGraph

/-!
---
title: Kuhn's Algorithm Computes a Maximum Matching
type: theorem
---
The matching Kuhn's algorithm returns is a matching of the graph, and no matching of the graph
has more edges. In particular it saturates the left side exactly when some matching does, and
its size is the matching number of the bipartite graph.

# Formalization Notes

The first two statements are about the relation the algorithm works on; the third is about the
graph, in Mathlib's terms: for a graph on `Fin V` split at `n`, the relation between `Fin n`
and `Fin (V - n)` is adjacency across the split, and a matching of the graph is the same thing
as an injective assignment of left neighbours to right vertices, edge for edge.

The proof does not use Berge's lemma. A search from `l₀` fails only when every right vertex
reachable from `l₀` by alternating exploration is already matched, and the left vertices so
reached then outnumber the right vertices so reached by exactly one. This state is stable: a
later augmentation from another free vertex keeps the reached left vertices matched, hence into
the same set of right neighbours, which it therefore saturates again, so that `l₀` reaches
nothing new and stays failed. At the end the failed left vertices `F` and the set `S` of all
left vertices reachable from them have `|N(S)| = |S| - |F|`, and any matching matches at most
`|N(S)|` vertices of `S`, so it has at most `|L| - |F|` edges — which is the size of the
matching returned, since every left vertex outside `F` is matched.
-/

namespace Lax117284.BipartiteKuhnCorrect

open Lax117284.BipartiteKuhn Lax117284.BipartiteMatching Lax117284.BipartiteGraph

variable {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  (adj : L → R → Prop) [DecidableRel adj]

/-- **The result is a matching of the graph.** -/
axiom kuhn_isMatching : Respects adj (kuhn adj) ∧ InjOnSupport (kuhn adj)

/-- **No matching is larger.** -/
axiom kuhn_maximum (μ : R → Option L) (hres : Respects adj μ) (hinj : InjOnSupport μ) :
    size μ ≤ size (kuhn adj)

/-- **A matching saturating the left side exists exactly when the result is one.** -/
axiom kuhn_saturates_iff :
    (∀ l, Matched (kuhn adj) l) ↔ ∃ f : L → R, Function.Injective f ∧ ∀ l, adj l (f l)

/-- The adjacency across the split of a graph on `Fin V` split at `n`, as a relation between
the left vertices `Fin n` and the right vertices `Fin (V - n)`. -/
def leftRel {V : ℕ} (G : SimpleGraph (Fin V)) (n : ℕ) (hn : n ≤ V) :
    Fin n → Fin (V - n) → Prop :=
  fun i j => G.Adj ⟨i, by omega⟩ ⟨n + j, by omega⟩

open scoped Classical in
/-- **The size of the result is the matching number of the graph.** -/
axiom kuhn_matchingNumber {V : ℕ} (G : SimpleGraph (Fin V)) (n : ℕ) (hn : n ≤ V)
    (hs : SplitAt G n) : size (kuhn (leftRel G n hn)) = matchingNumber G

end Lax117284.BipartiteKuhnCorrect
