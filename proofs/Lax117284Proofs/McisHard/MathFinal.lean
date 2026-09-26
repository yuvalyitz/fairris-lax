import Lax117284Proofs.McisHard.HinstProofs
import Lax117284Proofs.McisHard.BridgeProofs

/-!
# The math layer, assembled: `reduceMcis_correct` from the proved lemmas (no stubs)
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Proved

open Lax117284.MulticolouredIndepSet Lax434930.PolynomialTime
open Lax117284.Problems (encodeNat)
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284.BoundedSat

theorem reduceMcis_correct (w : Word) :
    w ∈ BoundedSat ↔ Lax117284Proofs.McisHard.reduceMcis w ∈ NormalMulticolouredIndepSet := by
  classical
  by_cases h : ∃ φ : Formula, encodeFormula φ = w ∧ φ.vars ≤ slots φ
  · unfold Lax117284Proofs.McisHard.reduceMcis
    rw [dif_pos h]
    obtain ⟨hφ, hle⟩ := h.choose_spec
    generalize h.choose = φ at hφ hle ⊢
    have hs := shape_valsOf φ
    have hc := condN_valsOf φ hle
    have hsat : (formulaOf (valsOf φ) hc hs).Satisfiable ↔ φ.Satisfiable := by
      rw [Proved.formulaOf_valsOf φ hs hc]
    have hN : (Lax117284Proofs.McisHard.Hfin (valsOf φ)).Normal ∧
        ((Lax117284Proofs.McisHard.Hfin (valsOf φ)).HasIndepSet ↔ φ.Satisfiable) := by
      unfold Lax117284Proofs.McisHard.Hfin
      by_cases h0 : SlotsN (valsOf φ) = 0
      · rw [if_pos h0]
        exact ⟨Proved.H0_normal, ⟨fun _ => Lax117284Proofs.McisHard.sat_of_slots_zero φ
          (by rw [← valsOf_slots φ]; exact h0), fun _ => Proved.H0_hasIndepSet⟩⟩
      · rw [if_neg h0]
        exact ⟨Proved.Hinst_normal _ hs hc h0, (Proved.Hinst_hasIndepSet_iff _ hs hc).trans hsat⟩
    constructor
    · rintro ⟨φ', hφ', -, hS⟩
      have : φ' = φ := SourceInjectivity.boundedSat_encode_inj (hφ'.trans hφ.symm)
      subst this
      exact ⟨_, rfl, hN.1, hN.2.2 hS⟩
    · rintro ⟨G, hG, hNG, hI⟩
      have : G = Lax117284Proofs.McisHard.Hfin (valsOf φ) := SourceInjectivity.mis_encode_inj hG
      subst this
      exact ⟨φ, hφ, hle, hN.2.1 hI⟩
  · unfold Lax117284Proofs.McisHard.reduceMcis
    rw [dif_neg h]
    constructor
    · rintro ⟨φ, hφ, hle, -⟩
      exact absurd ⟨φ, hφ, hle⟩ h
    · rintro ⟨G, hG, -⟩
      exfalso
      have := congrArg List.length hG
      simp [encodeInstance, encodeNat] at this

end Lax117284Proofs.McisHard.Proved
