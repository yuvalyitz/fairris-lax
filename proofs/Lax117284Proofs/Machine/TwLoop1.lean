import Lax117284Proofs.Machine.TwJoin3

/-!
The program of a node of any kind: the leaf, and the dispatch on the kind.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

lemma bagL_leaf' (P : Params) {i : ℕ} (hk : i = 0 ∨ kind P.D i = 0) : bagL P.D i = [] := by
  rcases hk with rfl | hk
  · simp [bagL]
  · cases i with
    | zero => simp [bagL]
    | succ j => exact bagL_leaf hk

lemma tbv_leaf0 {I : Lax117284.Scheduling.Instance} {kk : ℕ} {D : List ℕ} {i : ℕ}
    (hk : i = 0 ∨ kind D i = 0) : tbv I kk D i 0 = 1 := by
  rcases hk with rfl | hk
  · exact tbv_one (by simp [TB])
  · cases i with
    | zero => exact tbv_one (by simp [TB])
    | succ j => exact tbv_one ((TB_leaf hk).2 rfl)

theorem leafCom_ok {i : ℕ} (hC : NC P B σ) (hN : NI P.I P.kk P.D P.wid P.tabs i σ)
    (hi : σ.vars "i" = i) (hiN : i < P.N) (hk : i = 0 ∨ kind P.D i = 0) :
    ∃ σ', Run B leafCom σ σ' 40 ∧ Keep σ σ' ∧ NI P.I P.kk P.D P.wid P.tabs (i + 1) σ' ∧
      σ'.out = σ.out := by
  have hb1 := hC.b1
  have htab : 0 < P.tabs := by unfold Params.tabs Params.bs; positivity
  have hNt : (i + 1) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ hiN
  have hi1 : (i + 1) * P.tabs = i * P.tabs + P.tabs := by ring
  obtain ⟨σ', r, e⟩ := leafCom_run (B := B) (Tm := P.tabs) hi hC.Tm_
    (by have := hC.lenSZ; omega) (by have := hC.lenTB; omega)
    (by omega) (by have := hC.b3; omega)
  have hl0 := bagL_leaf' P hk
  have hleaf := tbv_leaf0 (I := P.I) (kk := P.kk) (D := P.D) hk
  have hSZ : σ'.arrs "SZ" = (σ.arrs "SZ").set i 0 := by rw [e]; simp
  have hBG : σ'.arrs "BG" = σ.arrs "BG" := by rw [e]; simp
  have hTB : σ'.arrs "TB" = (σ.arrs "TB").set (i * P.tabs) 1 := by rw [e]; simp
  refine ⟨σ', r, ?_, ?_, by rw [e]; simp⟩
  · rw [e]
    exact (((Keep.refl σ).setArr (Or.inl rfl) _ _).setVar (by simp [SN]) _).setArr
      (Or.inr (Or.inr rfl)) _ _
  · refine NI_next (i := i) (σ0 := σ) hN (fun j hj => ?_)
      (fun s hs => by rw [bpow]; exact pow_le_tabs P hs) ?_ ?_ ?_
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · exact bagL_len_le P (by omega)
      · subst h; rw [hl0]; simp
    · intro k
      rw [hSZ, getD_set']
      by_cases hk1 : k = i
      · subst hk1
        rw [if_pos ⟨rfl, by have := hC.lenSZ; omega⟩]
        simp [hl0]
      · rw [if_neg (by omega), if_neg (by omega)]
    · intro k
      simp [hBG, hl0]
    · intro k
      rw [hTB, getD_set']
      simp only [hl0, List.length_nil, pow_zero]
      by_cases hk1 : k = i * P.tabs
      · subst hk1
        rw [if_pos ⟨rfl, by have := hC.lenTB; omega⟩]
        simp [hleaf]
      · rw [if_neg (by omega), if_neg (by omega)]

end Lax117284Proofs.Machine.TwNode
