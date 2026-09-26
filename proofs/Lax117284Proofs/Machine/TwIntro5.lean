import Lax117284Proofs.Machine.TwIntro4

/-!
The fill of the table of an introduce node.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- The context survives a fill that keeps the other arrays and the constants. -/
lemma NC.of_agrA {S : List String} {arr : String} {σ0 σ : Env} (h : NC P B σ0)
    (hA : AgrA S arr σ0 σ) (hl : (σ.arrs arr).length = (σ0.arrs arr).length)
    (hS : ∀ y ∈ S, y ∈ SN) (harr : arr = "SZ" ∨ arr = "BG" ∨ arr = "TB") : NC P B σ := by
  have hx : ∀ a, a ≠ arr → σ.arrs a = σ0.arrs a := hA.2
  refine h.transfer (fun y hy => hA.1 y (fun hyS => ?_)) (hx _ ?_) (hx _ ?_) ?_ ?_ ?_
  · have := hS y hyS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [SN, SV, Stt, St2, SD] at this
  · rcases harr with rfl | rfl | rfl <;> decide
  · rcases harr with rfl | rfl | rfl <;> decide
  · rcases harr with rfl | rfl | rfl
    · exact hl
    · rw [hx _ (by decide)]
    · rw [hx _ (by decide)]
  · rcases harr with rfl | rfl | rfl
    · rw [hx _ (by decide)]
    · exact hl
    · rw [hx _ (by decide)]
  · rcases harr with rfl | rfl | rfl
    · rw [hx _ (by decide)]
    · rw [hx _ (by decide)]
    · exact hl

theorem introTB_run {i0 : ℕ} (hT : TC P B i0 σ) (hbs : σ.vars "bs" = (i0 + 1) * P.tabs)
    (hfn : σ.vars "fn" = 2 ^ (P.m * (bagL P.D (i0 + 1)).length)) :
    ∃ σ', Run B (fillLoop "TB" introCell) σ σ'
        ((vcost P.m (bagL P.D (i0 + 1)).length + 60 + 20 + 4) *
          2 ^ (P.m * (bagL P.D (i0 + 1)).length) + 6) ∧
      AgrA ("fc" :: SI) "TB" σ σ' ∧ σ'.out = σ.out ∧
      (σ'.arrs "TB").length = (σ.arrs "TB").length ∧
      RowDesc "TB" ((i0 + 1) * P.tabs) ((2 ^ P.I.days) ^ (bagL P.D (i0 + 1)).length)
        (fun e => tbv P.I P.kk P.D (i0 + 1) e) σ σ' := by
  have hC := hT.C
  have hiN := hT.iN
  have hl1 := bagL_intro_len P hT.k_
  have hle1 := bagL_len_le P (j := i0 + 1) hiN
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  have hb1 := hC.b1
  have hlenTB := hC.lenTB
  have hpt : 2 ^ (P.m * (bagL P.D (i0 + 1)).length) ≤ P.tabs := pow_le_tabs P hle1
  have hpt0 : (2 ^ P.m) ^ (bagL P.D i0).length ≤ P.tabs := by
    rw [bpow']; exact pow_le_tabs P hlen0
  have hNt : (i0 + 2) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ hiN
  have hi2t : (i0 + 2) * P.tabs = (i0 + 1) * P.tabs + P.tabs := by ring
  have hi1t : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
  have hres := fillLoop_run (B := B) "TB" introCell (fun e => tbv P.I P.kk P.D (i0 + 1) e)
    ("fc" :: SI) (vcost P.m (bagL P.D (i0 + 1)).length + 60) (2 ^ (P.m * (bagL P.D (i0 + 1)).length))
    σ hfn (by omega) (by rw [hbs]; omega)
    (fun k => lt_of_le_of_lt tbv_le_one (by omega)) (by simp [SI, SV, Stt, St2, SD])
    (by rw [hbs]; omega) (by
      intro σ' hF hA hlt
      have hC' : NC P B σ' := hC.of_agrA hA hF.1 SI_sub (Or.inr (Or.inr rfl))
      have hS : ∀ y, y ∈ ["off", "vs", "Pp", "shp1", "cbase"] → σ'.vars y = σ.vars y :=
        fun y hy => hA.1 y (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp [SI, SV, Stt, St2, SD])
      have hT' : TC P B i0 σ' :=
        ⟨hC', hiN, hT.k_, fun t ht => by rw [hA.2 "BG" (by decide)]; exact hT.bg t ht,
          fun e he => by
            rw [hF.2, if_neg (by rw [hbs]; omega)]; exact hT.tb e he,
          by rw [hS "off" (by simp)]; exact hT.off_, by rw [hS "vs" (by simp)]; exact hT.vs_,
          by rw [hS "Pp" (by simp)]; exact hT.Pp_, by rw [hS "shp1" (by simp)]; exact hT.shp1_,
          by rw [hS "cbase" (by simp)]; exact hT.cbase_⟩
      obtain ⟨σ'', r, hv, ha, hfr, ho⟩ := introCell_run hT' hlt
      exact ⟨σ'', r, hv, ha, fun y hy => hfr y (fun h => hy (List.mem_cons_of_mem _ h)),
        hfr "fc" (by simp [SI, SV, Stt, St2, SD]), ho⟩)
  obtain ⟨σ', r, hl, hg, hA, ho⟩ := hres
  refine ⟨σ', r, hA, ho, hl, fun k => ?_⟩
  rw [hg k, hbs, bpow]

end Lax117284Proofs.Machine.TwNode
