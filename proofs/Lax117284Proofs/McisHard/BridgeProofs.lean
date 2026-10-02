import Lax117284Proofs.McisHard.Defs

/-!
# WP5 (Word-Level Part): `formulaOf_valsOf`, `reduceMcis_code`, `reduceMcis_rej`
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Proved

open Lax117284.MulticolouredIndepSet Lax434930.PolynomialTime
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284Proofs.Machine.TokModel
open Lax117284.BoundedSat
open Lax117284Proofs.McisHard

theorem formulaOf_valsOf (φ : Formula) (hs : ShapeF (valsOf φ)) (hc : CondN (valsOf φ)) :
    formulaOf (valsOf φ) hc hs = φ := by
  apply Lax117284Proofs.SourceInjectivity.boundedSat_encode_inj
  rw [← code_toksF (formulaOf (valsOf φ) hc hs) , valsOf_formulaOf, code_toksF]

open Classical in
/-- **The reduction on the code of an admissible stream.** -/
theorem reduceMcis_code (ts : List Tok)
    (hconf : Conforms EF ts)
    (hcond : CondN (ts.map Lax117284Proofs.Machine.TokProg.Tok.val)) :
    reduceMcis (code ts) = encodeInstance (Hfin (ts.map Lax117284Proofs.Machine.TokProg.Tok.val)) := by
  obtain ⟨hshape, hts⟩ := shape_of_conforms hconf
  have hg := (sat_gate (code ts)).2 ⟨ts, rfl, hconf, hcond⟩
  unfold reduceMcis
  rw [dif_pos hg]
  have hφ : formulaOf _ hcond hshape = hg.choose := by
    apply Lax117284Proofs.SourceInjectivity.boundedSat_encode_inj
    have h1 := code_toksF (formulaOf _ hcond hshape)
    rw [valsOf_formulaOf] at h1
    rw [hg.choose_spec.1, ← h1, ← hts]
  rw [← hφ, valsOf_formulaOf]

open Classical in
/-- **A word that is not the code of an admissible stream is rejected.** -/
theorem reduceMcis_rej (w : Word)
    (h : ¬ ∃ ts : List Tok, w = code ts ∧ Conforms EF ts ∧
      CondN (ts.map Lax117284Proofs.Machine.TokProg.Tok.val)) :
    reduceMcis w = [] := by
  unfold reduceMcis
  rw [dif_neg (fun hg => h ((sat_gate w).1 hg))]

end Lax117284Proofs.McisHard.Proved
