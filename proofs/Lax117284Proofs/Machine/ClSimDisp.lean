import Lax117284Proofs.Machine.ClSimBlk

/-!
The ladder of tests on the opcode reaches the block of the instruction at hand, and the block's
specification is the instruction's.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

variable {B wp v : ℕ} {s : State} {P : Program} {z : List ℕ}

theorem cond_op_eval (σ : Env) (k : ℕ) (h1 : σ.vars "op" < B) (h2 : k < B) :
    (Cond.eq (V "op") (lit k)).evalB B σ = some (decide (σ.vars "op" = k)) := by
  rw [evalB_condEq (m := σ.vars "op") (n := k) (evalB_var h1) (evalB_lit h2)]
  by_cases h : σ.vars "op" = k <;> simp [h]

/-- The ladder: from `k`, with `n` rungs, reaches the block of `o`. -/
theorem dispN_spec {Pr : Env → Prop} {Q : Env → Env → Prop} {K : ℕ} (o : ℕ)
    (hop : ∀ σ, Pr σ → σ.vars "op" = o) (hB : 20 < B) :
    ∀ (n k : ℕ), k ≤ o → o < k + n → k + n ≤ 18 → Spec B Pr (blk o) Q K →
      Spec B Pr (dispN n k) Q (4 * (o - k + 1) + K) := by
  intro n
  induction n with
  | zero => intro k hk1 hk2; omega
  | succ n ih =>
    intro k hk1 hk2 hk3 hblk
    have hdef : ∀ σ, Pr σ → ∃ b, (Cond.eq (V "op") (lit k)).evalB B σ = some b := fun σ hσ =>
      ⟨_, cond_op_eval σ k (by rw [hop σ hσ]; omega) (by omega)⟩
    have hev : ∀ σ, Pr σ → (Cond.eq (V "op") (lit k)).evalB B σ = some (decide (o = k)) := by
      intro σ hσ
      rw [cond_op_eval σ k (by rw [hop σ hσ]; omega) (by omega), hop σ hσ]
    have main : Spec B Pr (dispN (n + 1) k) Q (1 + (Cond.eq (V "op") (lit k)).size +
        (4 * (o - k) + K)) := by
      refine Spec.ite hdef ?_ ?_
      · by_cases hko : k = o
        · subst hko
          exact (Spec.pre hblk (fun σ h => h.1)).mono (by omega)
        · intro σ ⟨hσ, hc⟩
          rw [hev σ hσ] at hc
          simp at hc
          omega
      · by_cases hko : k = o
        · intro σ ⟨hσ, hc⟩
          rw [hev σ hσ] at hc
          subst hko
          simp at hc
        · have := ih (k + 1) (by omega) (by omega) (by omega) hblk
          refine (Spec.pre this (fun σ h => h.1)).mono ?_
          omega
    refine Spec.mono main ?_
    simp only [Cond.size, Expr.size]
    omega

/-- What the blocks assume of the world. -/
structure Hyp (B wp : ℕ) (s : State) (P : Program) (z : List ℕ) : Prop where
  hB : Bnd B wp
  hw : ∀ x, s.mem x < 2 ^ wp
  hzB : z.length < B
  hzE : ∀ i, z.getD i 0 < B
  hzE' : ∀ i (h : i < z.length), z[i] < B
  hpl : P.length < B
  hpc : s.pc < P.length

theorem dispatch_of_blk {Q : Env → Env → Prop} {K : ℕ} (o a b c : ℕ) (hB : 20 < B) (ho : o < 18)
    (hblk : Spec B (Pre P z wp v s o a b c) (blk o) Q K) :
    Spec B (Pre P z wp v s o a b c) dispatch Q (4 * (o + 1) + K) := by
  have := dispN_spec (B := B) (Pr := Pre P z wp v s o a b c) (Q := Q) (K := K) o
    (fun σ h => h.1.op) hB 18 0 (by omega) (by omega) (by omega) hblk
  simpa [dispatch] using this

theorem dispatch_spec (i : Instr) (H : Hyp B wp s P z)
    (hL : (code i).2.1 < B ∧ (code i).2.2.1 < B ∧ (code i).2.2.2 < B) :
    Spec B (Pre P z wp v s (code i).1 (code i).2.1 (code i).2.2.1 (code i).2.2.2) dispatch
      (fun σ σ' => Res B wp P.length s (i.effect wp s) σ') 300 := by
  have hB20 : 20 < B := by have := H.hB; simp only [Bnd] at this; have := Nat.two_pow_pos wp; omega
  obtain ⟨hB, hw, hzB, hzE, hzE', hpl, hpc⟩ := H
  cases i with
  | set a n =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 0 a n 0 hB20 (by omega) (blk0_spec a n 0 hB hw hpc hpl hL.2.1)).mono (by omega)
  | load a b =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 1 a b 0 hB20 (by omega) (blk1_spec a b 0 hB hw hpc hpl)).mono (by omega)
  | store a b =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 2 a b 0 hB20 (by omega) (blk2_spec a b 0 hB hw hpc hpl)).mono (by omega)
  | add a b c =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 3 a b c hB20 (by omega) (blk3_spec a b c hB hw hpc hpl)).mono (by omega)
  | sub a b c =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 4 a b c hB20 (by omega) (blk4_spec a b c hB hw hpc hpl)).mono (by omega)
  | mul a b c =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 5 a b c hB20 (by omega) (blk5_spec a b c hB hw hpc hpl)).mono (by omega)
  | div a b c =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 6 a b c hB20 (by omega) (blk6_spec a b c hB hw hpc hpl)).mono (by omega)
  | and a b c =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 7 a b c hB20 (by omega) (blk7_spec a b c hB hw hpc hpl)).mono (by omega)
  | shiftl a b c =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 8 a b c hB20 (by omega) (blk8_spec a b c hB hw hpc hpl)).mono (by omega)
  | not a b =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 9 a b 0 hB20 (by omega) (blk9_spec a b 0 hB hw hpc hpl)).mono (by omega)
  | jump l =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 10 l 0 0 hB20 (by omega) (blk10_spec l 0 0 hB hw hpc hpl hL.1)).mono (by omega)
  | jzero a l =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 11 a l 0 hB20 (by omega) (blk11_spec a l 0 hB hw hpc hpl hL.2.1)).mono (by omega)
  | jeof l =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 12 l 0 0 hB20 (by omega) (blk12_spec l 0 0 hB hw hpc hpl hL.1 hzB)).mono (by omega)
  | inputLength a =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 13 a 0 0 hB20 (by omega) (blk13_spec a 0 0 hB hw hpc hpl hzB)).mono (by omega)
  | inputLoad a b =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 14 a b 0 hB20 (by omega) (blk14_spec a b 0 hB hw hpc hpl hzB hzE hzE')).mono (by omega)
  | halt =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 15 0 0 0 hB20 (by omega) (blk15_spec 0 0 0 hB hw hpc hpl)).mono (by omega)
  | read a =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 16 a 0 0 hB20 (by omega) (blk16_spec a 0 0 hB hw hpc hpl hzB hzE hzE')).mono (by omega)
  | write a =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 17 a 0 0 hB20 (by omega) (blk17_spec a 0 0 hB hw hpc hpl)).mono (by omega)

end Lax117284Proofs.Machine.ClSim
