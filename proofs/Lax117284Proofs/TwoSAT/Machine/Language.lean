import Lax117284Proofs.TwoSAT.Machine.Scan
import Lax117284.TwoSatRunningTime

/-!
Membership in 2-SAT, in the terms of the machine: the scan accepts the bits, every clause has
one or two literals, and no occurring variable is contradictory.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Language

open Lax429075.CNF Lax429075.Encoding Lax434930.PolynomialTime Lax117284.TwoSatCNF
open Lax391470Proofs.CnfScan Lax117284Proofs.TwoSAT.Machine.Scan Lax117284Proofs.TwoSAT.Machine.Model

/-- The concept's bits are the scanner's. -/
theorem bitsOf_eq (x : List ℕ) :
    Lax117284.TwoSatRunningTime.bitsOf x = Lax391470Proofs.Bits.bitsOf x := rfl

/-- **The bits of a word are in 2-SAT** exactly when the scan accepts them as a satisfiable
2-CNF formula. -/
theorem mem_twoSAT_iff (y : List ℕ) :
    Lax391470Proofs.Bits.bitsOf y ∈ TwoSAT ↔
      Accepted y ∧ IsTwoCNF (formulaOf y) ∧ Satisfiable (formulaOf y) := by
  constructor
  · rintro ⟨F, hF, h2, hs⟩
    have h := accept_complete F
    rw [hF] at h
    have hF' : formulaOf y = F := h.2
    exact ⟨h.1, hF' ▸ h2, hF' ▸ hs⟩
  · rintro ⟨hacc, h2, hs⟩
    exact ⟨formulaOf y, accept_sound hacc, h2, hs⟩

/-- The same, in the machine's terms. -/
theorem mem_twoSAT_iff' (y : List ℕ) :
    Lax391470Proofs.Bits.bitsOf y ∈ TwoSAT ↔
      Accepted y ∧ WidthOk (formulaOf y) ∧ ∀ x ∈ vars (formulaOf y), ¬ Bad (formulaOf y) x := by
  rw [mem_twoSAT_iff, ← answer_iff]

/-- The concept's count of variables is the scanned formula's. -/
theorem wordVarCount_eq (y : List ℕ) (h : Accepted y) :
    Lax117284.TwoSatRunningTime.wordVarCount y = varCount (formulaOf y) := by
  unfold Lax117284.TwoSatRunningTime.wordVarCount
  have h' : (run init (Lax391470Proofs.Bits.bitsOf y)).ph = 4 := h
  rw [bitsOf_eq, decodeCNF_eq, if_pos h']; rfl

theorem wordVarCount_eq_zero (y : List ℕ) (h : ¬ Accepted y) :
    Lax117284.TwoSatRunningTime.wordVarCount y = 0 := by
  unfold Lax117284.TwoSatRunningTime.wordVarCount
  have h' : ¬ (run init (Lax391470Proofs.Bits.bitsOf y)).ph = 4 := h
  rw [bitsOf_eq, decodeCNF_eq, if_neg h']; rfl

end Lax117284Proofs.TwoSAT.Machine.Language
