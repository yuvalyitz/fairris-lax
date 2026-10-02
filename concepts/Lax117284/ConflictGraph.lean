import Lax117284.Scheduling
import Lax228581.Treewidth
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
---
title: The Conflict Graphs of an Instance
type: definition
---
Let $I$ be an instance with $n$ clients and $m$ days. The *day $i$ conflict graph* of $I$
is the graph on the $n$ clients in which two clients are adjacent if their jobs of day $i$
conflict. The *overall conflict graph* of $I$ is the graph on the $n$ clients in which two
clients are adjacent if their jobs conflict on at least one day; its edge set is the union
of the edge sets of the $m$ daily graphs.

A day's conflict graph is the intersection graph of that day's $n$ intervals, so it is an
interval graph. The observation the results of the source rest on is that a set of clients
can be served on day $i$ exactly when it is an independent set of the day $i$ conflict
graph: a schedule is feasible if and only if each of its days is independent in that day's
graph.

The treewidth $\tau$ of the overall conflict graph is the structural parameter measured in
the last section of the source, and it is the archive's treewidth.

# Formalization Notes

Both graphs are irreflexive by construction, the adjacency conjoining distinctness of the
two clients: a job always conflicts with itself, which carries no information about the
instance.

Interval graphs are not defined here. A day's conflict graph is an interval graph by
construction, and the only property of interval graphs that is used is that such a graph
can be coloured with as many colours as its largest clique has vertices, which is a
statement about these graphs and is proved as one.
-/

namespace Lax117284.ConflictGraph

open Lax117284.Scheduling

/-- Conflict is a symmetric relation: the two jobs share a time point either way. -/
theorem conflict_symm {I : Instance} {i : Fin I.days} {j j' : Fin I.clients}
    (h : I.Conflict i j j') : I.Conflict i j' j :=
  let ⟨t, ht⟩ := h; ⟨t, ht.2, ht.1⟩

variable (I : Instance)

/-- **The day `i` conflict graph** of `I`: two distinct clients are adjacent when their
jobs of day `i` conflict. -/
def dayGraph (i : Fin I.days) : SimpleGraph (Fin I.clients) where
  Adj j j' := j ≠ j' ∧ I.Conflict i j j'
  symm := ⟨fun _ _ h => ⟨h.1.symm, conflict_symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **The overall conflict graph** of `I`: two distinct clients are adjacent when their
jobs conflict on some day. -/
def overallGraph : SimpleGraph (Fin I.clients) where
  Adj j j' := j ≠ j' ∧ ∃ i, I.Conflict i j j'
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp fun _ => conflict_symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The treewidth `τ` of the overall conflict graph of `I`. -/
noncomputable def treewidth : ℕ := Lax228581.Treewidth.treewidth (overallGraph I)

/-- **A schedule is feasible exactly when every day's set of clients is an independent set
of that day's conflict graph.** -/
axiom feasible_iff_isIndepSet {I : Instance} (σ : I.Schedule) :
    Instance.Feasible σ ↔ ∀ i, (dayGraph I i).IsIndepSet (σ i : Set (Fin I.clients))

end Lax117284.ConflictGraph
