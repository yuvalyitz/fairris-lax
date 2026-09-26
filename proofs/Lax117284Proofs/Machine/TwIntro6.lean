import Lax117284Proofs.Machine.TwIntro5

/-!
The whole program of an introduce node, and its correctness.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- **The program of an introduce node.** -/
def introCom : Com :=
  .seq introHead (.seq (fillLoop "BG" bgPreIntro) (.seq introMid (fillLoop "TB" introCell)))

/-- What an introduce node costs. -/
def introCost (P : Params) : ℕ :=
  (34 * P.wid + 130) + ((20 + 20 + 4) * P.wid + 6) + 100 +
    ((vcost P.m P.wid + 60 + 20 + 4) * P.tabs + 6)

lemma midState_arrs (P : Params) (i0 : ℕ) (σ : Env) {a : String} (ha : a ≠ "SZ") :
    (midState P i0 σ).arrs a = σ.arrs a := by
  simp [midState, ha]

theorem introCom_run {i0 : ℕ} (hC : NC P B σ) (hN : NI P.I P.kk P.D P.wid P.tabs (i0 + 1) σ)
    (hi : σ.vars "i" = i0 + 1) (hiN : i0 + 1 < P.N) (hk : kind P.D (i0 + 1) = 1) :
    ∃ σ', Run B introCom σ σ' (introCost P) ∧ Keep σ σ' ∧
      NI P.I P.kk P.D P.wid P.tabs (i0 + 1 + 1) σ' ∧ σ'.out = σ.out := by
  have hl1 := bagL_intro_len P hk
  have hle1 := bagL_len_le P (j := i0 + 1) hiN
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  obtain ⟨σ3, r3, k3, har3, hc3, hs3, hvx3, hot3, hp3, hcw3, hs13, hiw3, hbs3, hfn3⟩ :=
    introHead_run hC hN hi hiN
  have hQ3 : HQ P B i0 σ3 :=
    ⟨k3.nc hC, hiN, (k3.vars "i" (by simp [SN, SV, Stt, St2, SD])).trans hi, hc3, hs3, hvx3, hp3,
      hcw3, hs13, hiw3, hbs3, hfn3, hk⟩
  have hP3 : HP P B i0 σ3 := ⟨hQ3, hN.of_arrs har3⟩
  obtain ⟨σ4, r4, hA4, o4, hl4, hrow4⟩ := introBG_run hP3
  have k4 : Keep σ3 σ4 := Keep.of_agrA hA4 hl4
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> simp [SN]) (Or.inr (Or.inl rfl)) o4
  have hQ4 : HQ P B i0 σ4 := hQ3.transfer k4 (fun y hy => hA4.1 y (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  obtain ⟨σ5, r5, e5⟩ := introMid_run hQ4
  have k5 : Keep σ4 σ5 := by
    rw [e5]; unfold midState
    exact (((((((Keep.refl σ4).setArr (Or.inl rfl) _ _).setVar (by simp [SN]) _).setVar
      (by simp [SN]) _).setVar (by simp [SN]) _).setVar (by simp [SN]) _).setVar
      (by simp [SN]) _).setVar (by simp [SN]) _ |>.setVar (by simp [SN]) _
  have hBG5 : σ5.arrs "BG" = σ4.arrs "BG" := by rw [e5]; exact midState_arrs P i0 σ4 (by decide)
  have hTB5 : σ5.arrs "TB" = σ.arrs "TB" := by
    rw [e5, midState_arrs P i0 σ4 (by decide), hA4.2 "TB" (by decide), har3]
  have hSZ5 : σ5.arrs "SZ" = (σ.arrs "SZ").set (i0 + 1) ((bagL P.D i0).length + 1) := by
    rw [e5]; simp [midState, hA4.2 "SZ" (by decide), har3]
  have hT5 : TC P B i0 σ5 := by
    refine ⟨k5.nc hQ4.C, hiN, hk, fun t ht => ?_, fun e he => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hBG5, hrow4, if_pos (by omega)]
      simp
    · rw [hTB5]; exact hN.tb i0 (by omega) e he
    · rw [e5]; simp [midState]
    · rw [e5]; simp [midState, hl1]
    · rw [e5]; simp [midState]
    · rw [e5]; simp [midState]
    · rw [e5]; simp [midState]
  have hbs5 : σ5.vars "bs" = (i0 + 1) * P.tabs := by rw [e5]; simp [midState]
  have hfn5 : σ5.vars "fn" = 2 ^ (P.m * (bagL P.D (i0 + 1)).length) := by
    rw [e5, hl1]; simp [midState]
  obtain ⟨σ6, r6, hA6, o6, hl6, hrow6⟩ := introTB_run hT5 hbs5 hfn5
  have k6 : Keep σ5 σ6 := Keep.of_agrA hA6 hl6 SI_sub (Or.inr (Or.inr rfl)) o6
  have hpt : 2 ^ (P.m * (bagL P.D (i0 + 1)).length) ≤ P.tabs := pow_le_tabs P hle1
  have hK : (vcost P.m (bagL P.D (i0 + 1)).length + 60 + 20 + 4) *
      2 ^ (P.m * (bagL P.D (i0 + 1)).length) ≤ (vcost P.m P.wid + 60 + 20 + 4) * P.tabs :=
    Nat.mul_le_mul (by have := vcost_mono P.m hle1; omega) hpt
  refine ⟨σ6, (r3.seq (r4.seq (r5.seq r6))).mono (by unfold introCost; omega),
    k3.trans (k4.trans (k5.trans k6)), ?_, by rw [o6, e5]; simp [midState, o4, k3.out]⟩
  refine NI_next (i := i0 + 1) (σ0 := σ) hN (fun j hj => bagL_len_le P (by omega))
    (fun s hs => by rw [bpow]; exact pow_le_tabs P hs) ?_ ?_ ?_
  · intro k
    rw [hA6.2 "SZ" (by decide), hSZ5, getD_set']
    by_cases hk1 : k = i0 + 1
    · subst hk1
      rw [if_pos ⟨rfl, by have := hC.lenSZ; omega⟩, if_pos (by omega), hl1]
    · rw [if_neg (by omega), if_neg (by omega)]
  · intro k
    rw [hA6.2 "BG" (by decide), hBG5, hrow4, har3]
  · intro k
    rw [hrow6, hTB5]

end Lax117284Proofs.Machine.TwNode
