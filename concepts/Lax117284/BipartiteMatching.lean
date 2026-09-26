import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Set.Card

/-!
---
title: Matchings, the matching number, and saturation
type: definition
---
A matching of a graph is a set of edges no two of which share a vertex; the matching number is
the largest number of edges in a matching; a matching saturates a set of vertices when it covers
every one of them, and it is perfect when it covers every vertex of the graph.

# Formalization notes

Matchings are Mathlib's: a subgraph `M` of `G` is a matching, `M.IsMatching`, when every vertex
of `M` has exactly one neighbour in `M`; its edges are `M.edgeSet`. Perfect matchings are
Mathlib's `IsPerfectMatching`. Only the size, the matching number, saturation and maximality are
named here.

The matching number is the supremum of the sizes of the matchings. For a finite graph the set of
sizes is bounded by the number of edges and contains `0`, so the supremum is a maximum, attained
by some matching; a maximum matching is one that attains it.
-/

namespace Lax117284.BipartiteMatching

variable {V : Type*} (G : SimpleGraph V)

/-- The size of a subgraph: the number of its edges. -/
noncomputable def size (M : G.Subgraph) : ℕ := M.edgeSet.ncard

/-- **The matching number**: the largest size of a matching. -/
noncomputable def matchingNumber : ℕ :=
  sSup {k | ∃ M : G.Subgraph, M.IsMatching ∧ size G M = k}

/-- **A maximum matching**: a matching no matching outnumbers. -/
def IsMaximumMatching (M : G.Subgraph) : Prop :=
  M.IsMatching ∧ ∀ M' : G.Subgraph, M'.IsMatching → size G M' ≤ size G M

/-- **A subgraph saturates a set of vertices** when it contains every one of them. -/
def Saturates (M : G.Subgraph) (S : Set V) : Prop := S ⊆ M.verts

end Lax117284.BipartiteMatching
