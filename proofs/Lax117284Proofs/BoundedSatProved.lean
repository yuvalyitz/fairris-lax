import Lax117284.BoundedSat
import Lax345332Proofs.BFinal

/-!
The NP-hardness of [2,3]-bounded 3-SAT, from the proof of the same theorem in lax-345332.

The two submissions carry the same definitions: a formula is the same structure with the same
fields and occurrence bound, satisfaction and the number of positions are the same terms, the
binary code of a number is the same function, and a formula is written as the same word. The
language of this submission is therefore the language `SAT23` of lax-345332, as sets of words,
and a polynomial-time many-one reduction to one is a reduction to the other.
-/

namespace Lax117284Proofs.BoundedSatProved

open Lax117284.BoundedSat

/-- A formula of lax-345332 is a formula of this submission. -/
def toFormula (φ : Lax345332.TwoThreeSat.Formula) : Formula :=
  ⟨φ.vars, φ.twoClauses, φ.threeClauses, φ.aLit, φ.bLit, φ.occ_le_two⟩

/-- A formula of this submission is a formula of lax-345332. -/
def ofFormula (φ : Formula) : Lax345332.TwoThreeSat.Formula :=
  ⟨φ.vars, φ.twoClauses, φ.threeClauses, φ.aLit, φ.bLit, φ.occ_le_two⟩

/-- The two languages are equal. -/
theorem language_eq : Lax345332.TwoThreeSat.SAT23 = BoundedSat := by
  ext w
  constructor
  · rintro ⟨φ, rfl, hv, hs⟩
    exact ⟨toFormula φ, rfl, hv, hs⟩
  · rintro ⟨φ, rfl, hv, hs⟩
    exact ⟨ofFormula φ, rfl, hv, hs⟩

/--
---
conclusion: Lax117284.BoundedSat.boundedSat_npHard
---
[2,3]-bounded 3-SAT is NP-hard: the theorem `Lax345332.TwoThreeSat.npHard`, proved in lax-345332
by the reduction from satisfiability through (3,4)-SAT and composed with the Cook–Levin
theorem, for the language `SAT23`, which is this submission's `BoundedSat`.
-/
theorem boundedSat_npHard_proved :
    type_of% @Lax117284.BoundedSat.boundedSat_npHard := by
  intro A hA
  rw [← language_eq]
  exact Lax345332Proofs.BFinal.npHard A hA

end Lax117284Proofs.BoundedSatProved

example : type_of% @Lax117284.BoundedSat.boundedSat_npHard :=
  Lax117284Proofs.BoundedSatProved.boundedSat_npHard_proved
