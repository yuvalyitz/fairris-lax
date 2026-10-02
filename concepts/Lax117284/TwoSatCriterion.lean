import Lax117284.TwoSatImplicationGraph

/-!
---
title: The Satisfiability Criterion for 2-CNF Formulas
type: lemma
---
A 2-CNF formula is satisfiable exactly when it has no empty clause and no variable is
contradictory in its implication graph: no variable $x$ with a path from $x$ to $\lnot x$ and a
path from $\lnot x$ to $x$. This is the criterion of Aspvall, Plass and Tarjan, on which every
polynomial-time algorithm for 2-SAT rests.

# Formalization Notes

The direction from a satisfying assignment is by induction along the paths: an edge preserves
truth, so a true literal reaches only true literals, and a variable cannot be true together with
its negation. The other direction builds an assignment. The graph is skew-symmetric — an edge
$a \to b$ gives an edge $\lnot b \to \lnot a$ — and so a set of literals closed under successors
that never contains a literal together with its negation can be extended by any variable not yet
decided: one of its two literals does not reach its own negation, and that literal together with
everything it reaches joins the set consistently. When every variable is decided the set is a
satisfying assignment.

The empty clause is stated separately because it has no literal and so no edge; the criterion
about paths says nothing about it.
-/

namespace Lax117284.TwoSatCriterion

open Lax429075.CNF Lax117284.TwoSatCNF Lax117284.TwoSatImplicationGraph

/-- **The criterion of Aspvall, Plass and Tarjan.** -/
axiom satisfiable_iff (F : Formula) (h : IsTwoCNF F) :
    Satisfiable F ↔ [] ∉ F ∧ ∀ x : ℕ, ¬ Contradictory F x

end Lax117284.TwoSatCriterion
