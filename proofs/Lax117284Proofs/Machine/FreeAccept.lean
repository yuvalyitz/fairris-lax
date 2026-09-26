import Lax117284Proofs.Machine.FreeCheck

/-!
The whole of the reduction after the tokenizer has accepted: read the counts off the array,
check the table, find the gap, and write either the output or the rejected word.
-/

namespace Lax117284Proofs.Machine.FreeAccept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.FreeProg Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.Flag

variable {B : ℕ}

/-- Read the counts and the parameter off the array. -/
def prepF : Com :=
  .seq (.assign "n" (.get "TK" (.lit 0)))
  (.seq (.assign "m" (.get "TK" (.lit 1)))
  (.seq (.assign "N" (mul (V "m") (V "n")))
  (.seq (.assign "N2" (mul (.lit 2) (V "N")))
  (.seq (.assign "m1" (add (V "m") (.lit 1)))
  (.seq (.assign "g" (.lit 0))
  (.seq (.assign "kp" (add (.get "TK" (add (.lit 2) (V "N2"))) (.lit 1)))
    (.ite (.lt (.lit 0) (V "m")) (.assign "ok" (.lit 1)) (.assign "ok" (.lit 0)))))))))

theorem prepF_spec (arr : List ℕ)
    (hE : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), arr.getD k 0 + 8 < B)
    (hL : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B) (hlen : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) ≤ arr.length)
    (hNB : 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B) :
    Spec B (fun σ => σ.arrs "TK" = arr) prepF
      (fun σ σ' => σ'.vars "n" = arr.getD 0 0 ∧ σ'.vars "m" = arr.getD 1 0 ∧
        σ'.vars "N" = arr.getD 1 0 * arr.getD 0 0 ∧
        σ'.vars "N2" = 2 * (arr.getD 1 0 * arr.getD 0 0) ∧
        σ'.vars "m1" = arr.getD 1 0 + 1 ∧ σ'.vars "g" = 0 ∧
        σ'.vars "kp" = paramOf arr + 1 ∧
        σ'.vars "ok" = (if 0 < arr.getD 1 0 then 1 else 0) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        ∀ y, y ≠ "n" → y ≠ "m" → y ≠ "N" → y ≠ "N2" → y ≠ "m1" → y ≠ "g" → y ≠ "kp" →
          y ≠ "ok" → σ'.vars y = σ.vars y) 60 := by
  run_vcg
  all_goals (
    have hA := ‹σ.arrs "TK" = arr›
    have e0 := hE 0 (by omega)
    have e1 := hE 1 (by omega)
    have ekp := hE (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) (by omega)
    subst hA
    try simp only [Env.setVar] at *
    try simp at *)
  all_goals try omega
  all_goals (
    refine ⟨by simp [paramOf], by omega, fun y a b c d e f g h => ?_⟩
    simp [a, b, c, d, e, f, g, h])

/-- Write the rejected word. -/
def rejectPrint : Com := .seq (emitLit 1) (.seq (emitLit 0) (emitLit 1))

theorem rejectPrint_run (Sz : ℕ) (σ : Env) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hB : 6 < B) :
    ∃ σ', Run B rejectPrint σ σ' (3 * (48 * Sz + 50)) ∧ σ'.out = σ.out ++ numBits [1, 0, 1] ∧
      σ'.arrs = σ.arrs ∧ ∀ y, y ∉ ["v", "s", "u", "i2"] → σ'.vars y = σ.vars y := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := (emitLit_spec (B := B) 1 Sz (by omega) (hs _ (by omega))) σ trivial
  obtain ⟨σ2, r2, o2, v2, a2⟩ := (emitLit_spec (B := B) 0 Sz (by omega) (hs _ (by omega))) σ1 trivial
  obtain ⟨σ3, r3, o3, v3, a3⟩ := (emitLit_spec (B := B) 1 Sz (by omega) (hs _ (by omega))) σ2 trivial
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), ?_, by rw [a3, a2, a1], fun y hy => ?_⟩
  · rw [o3, o2, o1]
    simp [numBits]
  · rw [v3 y hy, v2 y hy, v1 y hy]

/-- The whole of the reduction, after the tokenizer has accepted. -/
def acceptFree : Com :=
  .seq prepF (.seq okLoop
    (.ite (.eq (V "ok") (.lit 1)) (.seq gapLoop printFree) rejectPrint))

/-- The cost of the accepting phase. -/
def Kacc (Sz N : ℕ) : ℕ :=
  200 + 78 * N + (96 * Sz + 200) * (3 * N + 4) + 3 * (48 * Sz + 50)

theorem acceptFree_run (Sz : ℕ) (arr : List ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hE : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), arr.getD k 0 + 8 < B)
    (hL : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hlen : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) ≤ arr.length)
    (hNB : 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hprod : 0 < arr.getD 1 0 → arr.getD 0 0 * gapOf arr + 8 < B)
    (hA : σ.arrs "TK" = arr) :
    ∃ σ', Run B acceptFree σ σ' (Kacc Sz (arr.getD 1 0 * arr.getD 0 0)) ∧
      σ'.out = σ.out ++
        (if 0 < arr.getD 1 0 ∧ ∀ t < arr.getD 1 0 * arr.getD 0 0, Pass arr t
          then numBits (outFree arr) else numBits [1, 0, 1]) := by
  set n := arr.getD 0 0 with hn'
  set m := arr.getD 1 0 with hm'
  set N := m * n with hN'
  have hB2 : 6 < B := by omega
  have hn0 : n + 8 < B := hE 0 (by omega)
  have hm0 : m + 8 < B := hE 1 (by omega)
  have hkpB : paramOf arr + 1 + 4 < B := by
    have := hE (2 + 2 * N) (by omega)
    have hp : paramOf arr = arr.getD (2 + 2 * N) 0 := rfl
    omega
  -- the counts
  obtain ⟨σ1, r1, e1n, e1m, e1N, e1N2, e1m1, e1g, e1kp, e1ok, e1a, e1o, e1f⟩ :=
    (prepF_spec (B := B) arr hE hL hlen hNB) σ hA
  have A1 : σ1.arrs "TK" = arr := by rw [e1a]; exact hA
  -- the pass over the table
  obtain ⟨σ2, r2, e2ok, e2a, e2o, e2f⟩ := okLoop_spec (B := B) arr N (if 0 < m then 1 else 0) σ1
    (fun k hk => hE k (by omega)) (by omega) (by omega) (by omega) (by split <;> omega) A1 e1N e1ok
  have A2 : σ2.arrs "TK" = arr := by rw [e2a]; exact A1
  have z2 : ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → y ≠ "d" → σ2.vars y = σ1.vars y := e2f
  have hcond : (σ2.vars "ok" = 1) ↔ (0 < m ∧ ∀ t < N, Pass arr t) := by
    rw [e2ok, flagTo_eq_one]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra h0
      rw [if_neg h0] at h1
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [if_pos h1], h2⟩
  by_cases hok : σ2.vars "ok" = 1
  · -- the table is fine
    obtain ⟨hm, hpass⟩ := hcond.1 hok
    have hnN : n ≤ N := Nat.le_mul_of_pos_left n hm
    -- the gap
    obtain ⟨σ3, r3, e3g, e3a, e3o, e3f⟩ := gapLoop_spec (B := B) arr n σ2 (fun k hk => hE k (by omega)) (by omega) (by omega)
      (by omega) A2 (by rw [z2 "n" (by decide) (by decide) (by decide) (by decide), e1n])
      (by rw [z2 "g" (by decide) (by decide) (by decide) (by decide), e1g])
    have A3 : σ3.arrs "TK" = arr := by rw [e3a]; exact A2
    have z3 : ∀ y, y ≠ "g" → y ≠ "i" → y ≠ "p" → y ≠ "ok" → y ≠ "d" →
        σ3.vars y = σ1.vars y := fun y a b c d e => by
      rw [e3f y a b c, z2 y d b c e]
    have hg3 : σ3.vars "g" = gapOf arr := by rw [e3g]; rfl
    have hprod' := hprod hm
    have hgB : gapOf arr + 8 < B := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · have : gapOf arr = 0 := by unfold gapOf; rw [← hn', h0]; simp
        omega
      · have : gapOf arr ≤ n * gapOf arr := Nat.le_mul_of_pos_left _ h0
        omega
    obtain ⟨σ4, r4, e4o⟩ := printFree_run (B := B) Sz arr σ3 hs hE hL hlen hm hprod' hgB hNB A3
      (by rw [z3 "n" (by decide) (by decide) (by decide) (by decide) (by decide), e1n])
      (by rw [z3 "m1" (by decide) (by decide) (by decide) (by decide) (by decide), e1m1])
      (by rw [z3 "N2" (by decide) (by decide) (by decide) (by decide) (by decide), e1N2])
      hg3
      (by rw [z3 "kp" (by decide) (by decide) (by decide) (by decide) (by decide), e1kp]) hkpB
    have hokB : σ2.vars "ok" < B := by
      rw [e2ok]; have := flagTo_le (Pass arr) (if 0 < m then 1 else 0) N; omega
    have hcondT : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some true := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    refine ⟨σ4, ?_, ?_⟩
    · refine (r1.seq (r2.seq (Run.ite_true hcondT (r3.seq r4)))).mono ?_
      unfold Kacc Kprint
      simp only [Cond.size, Expr.size]
      nlinarith [Nat.zero_le Sz, Nat.zero_le N, Nat.zero_le n, hnN,
        Nat.mul_le_mul_left (96 * Sz + 200) hnN]
    · rw [e4o, e3o, e2o, e1o, if_pos ⟨hm, hpass⟩]
  · have hno : ¬ (0 < m ∧ ∀ t < N, Pass arr t) := fun h => hok (hcond.2 h)
    obtain ⟨σ3, r3, e3o, e3a, e3f⟩ := rejectPrint_run (B := B) Sz σ2 hs hB2
    have hokB : σ2.vars "ok" < B := by
      rw [e2ok]; have := flagTo_le (Pass arr) (if 0 < m then 1 else 0) N; omega
    have hcondF : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some false := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    refine ⟨σ3, ?_, ?_⟩
    · refine (r1.seq (r2.seq (Run.ite_false hcondF r3))).mono ?_
      unfold Kacc
      simp only [Cond.size, Expr.size]
      nlinarith [Nat.zero_le Sz, Nat.zero_le N, Nat.zero_le n]
    · rw [e3o, e2o, e1o, if_neg hno]

end Lax117284Proofs.Machine.FreeAccept
