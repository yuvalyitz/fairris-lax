import Lax117284Proofs.Machine.TwIntro3

/-!
The cell of the table of an introduce node: the count of the violations, then the lookup.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

lemma bpow' (P : Params) (s : ℕ) : (2 ^ P.m) ^ s = 2 ^ (P.m * s) := by rw [← pow_mul]

/-- The cell of the table of an introduce node. -/
def introCell : Com := .seq (.assign "e" (V "fc")) (.seq violCom introTail)

/-- The scalars a cell writes. -/
def SI : List String := ["e", "lo", "hi", "rm", "val"] ++ SV

lemma SI_sub : ∀ y ∈ "fc" :: SI, y ∈ SN := by
  intro y hy
  simp only [SI, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | h
  · simp [SN]
  · simp [SN]
  · simp [SN]
  · simp [SN]
  · simp [SN]
  · simp [SN]
  · simp only [SN, List.mem_append]; right; simpa using h

/-- **The context of a cell of the table of an introduce node.** -/
structure TC (P : Params) (B : ℕ) (i0 : ℕ) (σ : Env) : Prop where
  C : NC P B σ
  iN : i0 + 1 < P.N
  k_ : kind P.D (i0 + 1) = 1
  bg : ∀ t < (bagL P.D (i0 + 1)).length,
    (σ.arrs "BG").getD ((i0 + 1) * P.wid + t) 0 = (bagL P.D (i0 + 1))[t]!
  tb : ∀ e < (2 ^ P.m) ^ (bagL P.D i0).length,
    (σ.arrs "TB").getD (i0 * P.tabs + e) 0 = tbv P.I P.kk P.D i0 e
  off_ : σ.vars "off" = (i0 + 1) * P.wid
  vs_ : σ.vars "vs" = (bagL P.D (i0 + 1)).length
  Pp_ : σ.vars "Pp" = 2 ^ (P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1)))
  shp1_ : σ.vars "shp1" = P.m * (pos (bagL P.D i0) (vertex P.D (i0 + 1)) + 1)
  cbase_ : σ.vars "cbase" = i0 * P.tabs

theorem introCell_run {i0 : ℕ} (hT : TC P B i0 σ)
    (hfc : σ.vars "fc" < 2 ^ (P.m * (bagL P.D (i0 + 1)).length)) :
    ∃ σ', Run B introCell σ σ' (vcost P.m (bagL P.D (i0 + 1)).length + 60) ∧
      σ'.vars "val" = tbv P.I P.kk P.D (i0 + 1) (σ.vars "fc") ∧ σ'.arrs = σ.arrs ∧
      (∀ y, y ∉ SI → σ'.vars y = σ.vars y) ∧ σ'.out = σ.out := by
  have hC := hT.C
  have hiN := hT.iN
  have hl1 := bagL_intro_len P hT.k_
  have hle1 := bagL_len_le P (j := i0 + 1) hiN
  have hb1 := hC.b1
  have hb2 := hC.b2
  have hb5 := hC.b5
  have hb6 := hC.b6
  have hb8 := hC.b8
  have hb10 := hC.b10
  have hlenBG := hC.lenBG
  have hlenTB := hC.lenTB
  have hyl : P.y.length = 2 + 2 * (P.m * P.n) := by
    rw [P.hy.length_eq]; unfold Params.m Params.n; ring
  have hlX := hC.lenX
  have hNw : (i0 + 2) * P.wid ≤ P.N * P.wid := Nat.mul_le_mul_right _ hiN
  have hi2' : (i0 + 2) * P.wid = i0 * P.wid + P.wid + P.wid := by ring
  have hi1' : (i0 + 1) * P.wid = i0 * P.wid + P.wid := by ring
  have hNt : (i0 + 1) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ (by omega)
  have hi1t : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
  have hpt : 2 ^ (P.m * (bagL P.D (i0 + 1)).length) ≤ P.tabs := pow_le_tabs P hle1
  have hfcB : σ.vars "fc" < B := by omega
  have hbl1 : ∀ t < (bagL P.D (i0 + 1)).length, (bagL P.D (i0 + 1))[t]! < P.n :=
    fun t ht => bagL_get_lt P hiN ht
  have r1 : Run B (.assign "e" (V "fc")) σ (σ.setVar "e" (σ.vars "fc")) 2 :=
    (Run.assign (evalB_var hfcB)).mono (by simp [Expr.size])
  have h1 : (bagL P.D (i0 + 1)).length * ((bagL P.D (i0 + 1)).length * P.m + 1) ≤
      P.wid * (P.wid * P.m + 1) :=
    Nat.mul_le_mul hle1 (by have := Nat.mul_le_mul_right P.m hle1; omega)
  have h2 : (bagL P.D (i0 + 1)).length * P.m ≤ P.wid * P.m := Nat.mul_le_mul_right _ hle1
  have hV : VC (σ.arrs "X") P.n P.m P.kk (bagL P.D (i0 + 1)) B (σ.setVar "e" (σ.vars "fc")) := by
    refine ⟨by simp, by simp [hC.n_], by simp [hC.m_], by simp [hC.kk_], by simp [hC.mn_],
      by simp [hC.mask_], by omega, by simpa using hC.XB,
      by omega, by omega, by omega, by omega, ?_, ?_, hbl1, ?_, ?_,
      by omega, by omega, by omega⟩
    · intro t ht
      simpa [hT.off_] using hT.bg t ht
    · simp only [vars_setVar, arrs_setVar, String.reduceEq, if_false]
      rw [hT.off_]; omega
    · simp only [vars_setVar, String.reduceEq, if_false]
      rw [hT.off_]; omega
    · simp [hT.vs_]
  obtain ⟨σ2, r2, hv2, A2, o2⟩ := violCom_run hV (by simp; exact hfcB)
  have hfr : ∀ y, y ∉ SV → y ≠ "e" → σ2.vars y = σ.vars y := by
    intro y hy hne
    rw [A2.2 y hy]
    simp [Env.setVar, hne]
  have he2 : σ2.vars "e" = σ.vars "fc" := by
    rw [A2.2 "e" (by simp [SV, Stt, St2, SD])]; simp [Env.setVar]
  have har : σ2.arrs = σ.arrs := by rw [A2.1]; simp
  have hvi : σ2.vars "vi" = violE P.I P.kk (bagL P.D (i0 + 1)) (σ.vars "fc") := by
    rw [hv2]
    simp only [vars_setVar, if_true]
    exact violN_eq_violE P.hy hC.Xy P.kk _ (fun t ht => hbl1 t ht) _
  have hpl : pos (bagL P.D i0) (vertex P.D (i0 + 1)) ≤ (bagL P.D i0).length := pos_le_length
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  have hfc' : σ.vars "fc" < (2 ^ P.m) ^ ((bagL P.D i0).length + 1) := by
    rw [bpow', ← hl1]; exact hfc
  have hrmlt : rmN (2 ^ P.m) (pos (bagL P.D i0) (vertex P.D (i0 + 1))) (σ.vars "fc") <
      (2 ^ P.m) ^ (bagL P.D i0).length := rmN_lt (by positivity) hfc' hpl
  have hpt0 : (2 ^ P.m) ^ (bagL P.D i0).length ≤ P.tabs := by
    rw [bpow']; exact pow_le_tabs P hlen0
  have hct : i0 * P.tabs + P.tabs ≤ P.N * P.tabs := by
    have : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
    have := Nat.mul_le_mul_right P.tabs (show i0 + 1 ≤ P.N by omega)
    omega
  have hTBv := hT.tb _ hrmlt
  have hTBB : (σ2.arrs "TB").getD (i0 * P.tabs + rmN (2 ^ P.m)
      (pos (bagL P.D i0) (vertex P.D (i0 + 1))) (σ.vars "fc")) 0 < B := by
    rw [har, hTBv]; have := tbv_le_one (I := P.I) (kk := P.kk) (D := P.D)
      (j := i0) (e := rmN (2 ^ P.m) (pos (bagL P.D i0) (vertex P.D (i0 + 1))) (σ.vars "fc"))
    omega
  obtain ⟨σ3, r3, hv3, ha3, hf3, o3⟩ := introTail_run (B := B) σ2 P.m
    (pos (bagL P.D i0) (vertex P.D (i0 + 1))) (σ.vars "fc") (i0 * P.tabs)
    ((hfr "Pp" (by simp [SV, Stt, St2, SD]) (by decide)).trans hT.Pp_)
    ((hfr "shp1" (by simp [SV, Stt, St2, SD]) (by decide)).trans hT.shp1_)
    he2 ((hfr "cbase" (by simp [SV, Stt, St2, SD]) (by decide)).trans hT.cbase_)
    (by rw [har]; omega) hTBB (by omega) (by omega)
    (by have := pow_le_tabs P (s := pos (bagL P.D i0) (vertex P.D (i0 + 1))) (by omega); omega)
    (by
      have h1 := Nat.mul_le_mul_left P.m
        (show pos (bagL P.D i0) (vertex P.D (i0 + 1)) + 1 ≤ P.wid by omega)
      have h2 := Nat.mul_le_mul_left P.m (show P.wid ≤ P.wid + 1 by omega)
      have hb9 := hC.b9
      omega) hfcB (by omega)
    (by rw [hv2]; exact lt_of_le_of_lt (violN_le _ _ _ _ _ _) (by omega))
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by unfold vcost; omega), ?_, ha3.trans har, ?_,
    by rw [o3, o2]; simp⟩
  · rw [hv3, hvi, har, hTBv, tbv_intro hT.k_]
    rfl
  · intro y hy
    have hyS : y ∉ SV := fun h => hy (by simp [SI, h])
    have hye : y ≠ "e" := fun h => hy (by simp [SI, h])
    rw [hf3 y (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> exact hy (by simp [SI, h])), hfr y hyS hye]

end Lax117284Proofs.Machine.TwNode
