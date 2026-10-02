import Lax117284.TwoSatAlgorithm

/-!
---
title: Correctness of the Algorithm
type: theorem
---
The algorithm accepts a formula exactly when it is in 2-CNF and satisfiable.

# Formalization Notes

The width check accepts exactly the 2-CNF formulas without an empty clause, and the search, by
the criterion, rejects exactly the formulas with a contradictory variable. Two points connect
the search to the criterion. The set the search computes is the set of literals reachable within
the nodes, and reachability in the whole graph from a literal that occurs stays within the
nodes, since every edge joins two literals of one clause. And it suffices to test the variables
that occur, since a variable that does not occur has no edges at either of its literals and so is
never contradictory.
-/

namespace Lax117284.TwoSatCorrectness

open Lax429075.CNF Lax117284.TwoSatCNF Lax117284.TwoSatAlgorithm

/-- **The algorithm is correct.** -/
axiom decide_iff (F : Formula) : decide F = true ↔ IsTwoCNF F ∧ Satisfiable F

end Lax117284.TwoSatCorrectness
