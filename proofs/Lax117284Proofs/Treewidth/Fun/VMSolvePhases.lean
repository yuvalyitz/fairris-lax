import Lax117284Proofs.Treewidth.Fun.VMSolveDefs

/-!
# WP V3 (9): the phases of `solveCom` on the input `x`, with frames

`read_phase`, and the numeric facts about `Bimp` that all phases share.
-/

namespace Lax117284Proofs.Treewidth.Fun.Load

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax117284Proofs.Treewidth.Fun.VM Lax117284Proofs.Treewidth.Fun.VM.Ram ToVal

/-! ## Numeric facts -/

theorem N_le_progLen (Δ : ℕ → Option Tm) (N main : ℕ) : N ≤ progLen Δ N main := by
  have h : progLen Δ N main = offset Δ N := by
    simp [progLen, codeL, progCode, stub, offset_eq]; ring
  rw [h]; exact le_offset Δ N

theorem le_wordMax_of_mem {l : List ℕ} {v : ℕ} (hv : v ∈ l) : v ≤ wordMax l := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have : l.getD j 0 = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  rw [← this]; exact wordMax_getD_le l j

theorem bexp_gt_M (M K : ℕ) : M < bexp M K := by unfold bexp; nlinarith [Nat.zero_le (M + K + 2)]
theorem bexp_gt_K (M K : ℕ) : K < bexp M K := by unfold bexp; nlinarith [Nat.zero_le (M + K + 2)]
theorem bexp_ge_two (M K : ℕ) : 2 ≤ bexp M K := by unfold bexp; nlinarith [Nat.zero_le (M + K + 2)]

theorem entry_lt_Bx (p : KP) (fmt : Fmt) (x : List ℕ) : ∀ v ∈ x, v < Bx p fmt x := by
  intro v hv
  have h1 : v ≤ wordMax x := by
    have : ∃ j, x.getD j 0 = v ∨ v = 0 := by
      obtain ⟨j, hj⟩ := List.getElem_of_mem hv
      exact ⟨j, Or.inl (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj.1]; simp [hj.2])⟩
    obtain ⟨j, hj | hj⟩ := this
    · rw [← hj]; exact wordMax_getD_le x j
    · omega
  exact lt_of_le_of_lt h1 (bexp_gt_M _ _)

theorem Bx_gt_K (p : KP) (fmt : Fmt) (x : List ℕ) : Kx p fmt x < Bx p fmt x := bexp_gt_K _ _

/-! ## The read phase -/

theorem read_phase (fmt : Fmt) {x : List ℕ} {A Bi : ℕ} (hx : x ≠ []) (hA : x.length ≤ A)
    (hxB : ∀ v ∈ x, v < Bi) (hL : x.length + 1 < Bi) (hfmt : fmtLen fmt x = x.length) {σ : IEnv}
    (hinp : σ.inp = x) (hha : σ.arrs "HA" = arrOf A (fun _ => 0)) :
    ∃ σ', Run Bi fmt.loadCom σ σ' (52 * x.length + 60) ∧ Read x A σ' ∧
      (∀ y, y ∉ ["v", "M", "i", "tot"] → σ'.vars y = σ.vars y) ∧
      (∀ a, a ≠ "HA" → σ'.arrs a = σ.arrs a) ∧ σ'.out = σ.out := by
  cases fmt with
  | graphK =>
    have hlen : x.getD 0 0 * x.getD 0 0 + 2 = x.length := hfmt
    obtain ⟨σ', hr, hq⟩ := (loadK_spec hx hA hxB hL hlen).run (σ := σ) ⟨hinp, hha⟩
    refine ⟨σ', hr.mono (by omega), hq, ?_, ?_, ?_⟩
    · intro y hy; exact hr.frame_var y (by simp [loadK, hdrCom, rdLoop, rdOne, Com.wvars] at hy ⊢; tauto)
    · intro a ha; exact hr.frame_arr a (by simp [loadK, hdrCom, rdLoop, rdOne, Com.warrs]; exact ha)
    · exact hr.out_eq (by simp [loadK, hdrCom, rdLoop, rdOne, Com.NoWrite])
  | graphKLD =>
    have hlen : x.getD 0 0 * x.getD 0 0 + 4 + 3 * x.getD (x.getD 0 0 * x.getD 0 0 + 3) 0 = x.length := by
      have e : 1 + x.getD 0 0 * x.getD 0 0 + 2 = x.getD 0 0 * x.getD 0 0 + 3 := by omega
      have hfmt' : 1 + x.getD 0 0 * x.getD 0 0 + 2 + 1 + 3 * x.getD (1 + x.getD 0 0 * x.getD 0 0 + 2) 0
          = x.length := hfmt
      rw [e] at hfmt'
      omega
    obtain ⟨σ', hr, hq⟩ := (loadKLD_spec hx hA hxB hL hlen).run (σ := σ) ⟨hinp, hha⟩
    refine ⟨σ', hr.mono (by omega), hq, ?_, ?_, ?_⟩
    · intro y hy; exact hr.frame_var y (by simp [loadKLD, hdrCom, rdLoop, rdOne, bump, Com.wvars] at hy ⊢; tauto)
    · intro a ha; exact hr.frame_arr a (by simp [loadKLD, hdrCom, rdLoop, rdOne, bump, Com.warrs]; exact ha)
    · exact hr.out_eq (by simp [loadKLD, hdrCom, rdLoop, rdOne, bump, Com.NoWrite])

theorem idx_lt (fmt : Fmt) (x : List ℕ) (hfmt : fmtLen fmt x = x.length) :
    x.getD 0 0 * x.getD 0 0 + fmt.off < x.length := by
  cases fmt with
  | graphK =>
    have : x.getD 0 0 * x.getD 0 0 + 2 = x.length := hfmt
    show x.getD 0 0 * x.getD 0 0 + 1 < x.length
    omega
  | graphKLD =>
    have hh : 1 + x.getD 0 0 * x.getD 0 0 + 2 + 1 + 3 * x.getD (1 + x.getD 0 0 * x.getD 0 0 + 2) 0 = x.length :=
      hfmt
    show x.getD 0 0 * x.getD 0 0 + 2 < x.length
    omega

theorem two_le_len (fmt : Fmt) (x : List ℕ) (hfmt : fmtLen fmt x = x.length) : 2 ≤ x.length := by
  cases fmt with
  | graphK =>
    have : x.getD 0 0 * x.getD 0 0 + 2 = x.length := hfmt
    omega
  | graphKLD =>
    have hh : 1 + x.getD 0 0 * x.getD 0 0 + 2 + 1 + 3 * x.getD (1 + x.getD 0 0 * x.getD 0 0 + 2) 0 = x.length :=
      hfmt
    omega

/-! ## Cost and word arithmetic (isolated) -/

theorem cost_total_le (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) (fmt : Fmt) (x y : List ℕ)
    (hy : y.length ≤ Kx p fmt x) :
    (52 * x.length + 60) + ((kE p).size + 40) + (12 + (16 * x.length + 6)) + 12 +
      (3 * progLen Δ N main + 1) + (3 * progLen Δ N main + 1) + (3 * N + 1) +
      124 * (3 * Kx p fmt x + 4) + (16 * y.length + 12) ≤ Cimp Δ N main p fmt x := by
  unfold Cimp kappa kS
  set kk := progLen Δ N main + N + wordMax (opasL Δ N main) + wordMax (ftL Δ N) + p.c0 + p.c1 + p.c2 +
    (kE p).size + 1 with hkk
  set K := Kx p fmt x with hK
  set n := x.length with hn
  have h1 : 1000 * K ≤ 1000 * kk * K := Nat.mul_le_mul_right _ (by omega)
  have h2 : 1000 * n ≤ 1000 * kk * n := Nat.mul_le_mul_right _ (by omega)
  have e : 1000 * kk * (K + n + 1) = 1000 * kk * K + 1000 * kk * n + 1000 * kk := by ring
  rw [e]
  omega

end Lax117284Proofs.Treewidth.Fun.Load
