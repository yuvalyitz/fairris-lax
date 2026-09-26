import Lax117284Proofs.Theorem7Bridge

/-!
Theorem 7's correctness. The development's construction takes the formula together with a
rank for each position — which of the at most two occurrences of its literal it is — and
the construction of the concepts computes that rank from the formula, so it is that
construction at that choice.
-/

namespace Lax117284Proofs.Theorem7

open Lax117284.BoundedSat Lax117284.Theorem7 Lax117284Proofs.Theorem7Bridge

/--
---
conclusion: Lax117284.Theorem7.correct
---
The three dummies conflict with each other on all three days, so exactly one of them runs
on each day; the first day then admits one client of every group, which is the assignment
and one client of every clause, the second day is a dead end for everything but a client of
a clause of three literals, and on the third day a client of an occurrence conflicts with
exactly the variable client that falsifies its literal.
-/
theorem correct (φ : Formula) : φ.Satisfiable ↔ (inst φ).HasKFairSchedule 1 := by
  rw [← satisfiable_iff φ, (bnd φ).satisfiable_iff_hasOneFairSchedule]
  exact (numbering φ).hasKFairSchedule_iff 1

end Lax117284Proofs.Theorem7
