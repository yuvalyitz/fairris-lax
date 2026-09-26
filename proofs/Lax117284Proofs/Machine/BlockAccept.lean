import Lax117284Proofs.Machine.BlockProg
import Lax117284Proofs.Machine.FreeAccept

/-!
The whole of the blocking-day reduction after the tokenizer has accepted: read the counts off the
array, check the table and the parameter, find the largest due date, and write either the output
or the rejected word.
-/

namespace Lax117284Proofs.Machine.BlockAccept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.InstSem Lax117284Proofs.Machine.BlockSem
open Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.Flag Lax117284Proofs.Machine.BlockCheck
open Lax117284Proofs.Machine.BlockProg Lax117284Proofs.Machine.FreeAccept

variable {B : ℕ}

/-- Read the counts and the parameter off the array. -/
def prepB : Com :=
  .seq (.assign "n" (.get "TK" (.lit 0)))
  (.seq (.assign "m" (.get "TK" (.lit 1)))
  (.seq (.assign "N" (mul (V "m") (V "n")))
  (.seq (.assign "N2" (mul (.lit 2) (V "N")))
  (.seq (.assign "n1" (add (V "n") (.lit 1)))
  (.seq (.assign "m1" (add (V "m") (.lit 1)))
  (.seq (.assign "M1" (mul (V "m1") (V "n1")))
  (.seq (.assign "g" (.lit 0))
  (.seq (.assign "kp" (.get "TK" (add (.lit 2) (V "N2"))))
    (.ite (.lt (.lit 0) (V "m"))
      (.ite (.eq (V "kp") (.lit 1)) (.assign "ok" (.lit 1)) (.assign "ok" (.lit 0)))
      (.assign "ok" (.lit 0)))))))))))

set_option maxHeartbeats 1600000 in
theorem prepB_spec (arr : List ℕ)
    (hE : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), arr.getD k 0 + 8 < B)
    (hL : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hlen : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) ≤ arr.length)
    (hNB : 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hM1 : (arr.getD 1 0 + 1) * (arr.getD 0 0 + 1) + 8 < B) :
    Spec B (fun σ => σ.arrs "TK" = arr) prepB
      (fun σ σ' => σ'.vars "n" = arr.getD 0 0 ∧ σ'.vars "m" = arr.getD 1 0 ∧
        σ'.vars "N" = arr.getD 1 0 * arr.getD 0 0 ∧
        σ'.vars "N2" = 2 * (arr.getD 1 0 * arr.getD 0 0) ∧
        σ'.vars "n1" = arr.getD 0 0 + 1 ∧ σ'.vars "m1" = arr.getD 1 0 + 1 ∧
        σ'.vars "M1" = (arr.getD 1 0 + 1) * (arr.getD 0 0 + 1) ∧ σ'.vars "g" = 0 ∧
        σ'.vars "kp" = paramOf arr ∧
        σ'.vars "ok" = (if 0 < arr.getD 1 0 ∧ paramOf arr = 1 then 1 else 0) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        ∀ y, y ≠ "n" → y ≠ "m" → y ≠ "N" → y ≠ "N2" → y ≠ "n1" → y ≠ "m1" → y ≠ "M1" →
          y ≠ "g" → y ≠ "kp" → y ≠ "ok" → σ'.vars y = σ.vars y) 100 := by
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
    refine ⟨by simp [paramOf], ?_, fun y a b c d e f g h i j => ?_⟩
    · simp only [paramOf, List.getD_eq_getElem?_getD]
      first | omega | (constructor <;> omega) | (intro h1 h2; omega)
    · simp [a, b, c, d, e, f, g, h, i, j])


/-- Write the output of an instance without clients. -/
def print0 : Com := .seq (emitLit 0) (.seq (emitVar "m1") (emitLit 1))

theorem print0_run (Sz m : ℕ) (σ : Env) (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hm1 : σ.vars "m1" = m + 1) (hmB : m + 8 < B) :
    ∃ σ', Run B print0 σ σ' (3 * (48 * Sz + 50)) ∧ σ'.out = σ.out ++ numBits [0, m + 1, 1] := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := (emitLit_spec (B := B) 0 Sz (by omega) (hs _ (by omega))) σ trivial
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitVar_spec (B := B) "m1" Sz σ1
    ⟨by rw [v1 "m1" (by decide), hm1]; omega,
      by rw [v1 "m1" (by decide), hm1]; exact hs _ (by omega)⟩
  obtain ⟨σ3, r3, o3, v3, a3⟩ := (emitLit_spec (B := B) 1 Sz (by omega) (hs _ (by omega))) σ2 trivial
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), ?_⟩
  rw [o3, o2, o1, v1 "m1" (by decide), hm1]
  simp [numBits]

/-- The numbers of the output, read off the array. -/
def outBlockG (arr : List ℕ) : List ℕ :=
  if arr.getD 0 0 = 0 then [0, arr.getD 1 0 + 1, 1]
  else outG arr (arr.getD 0 0) (arr.getD 1 0) (runMaxD arr (arr.getD 1 0 * arr.getD 0 0) + 1)

/-- The whole of the reduction, after the tokenizer has accepted. -/
def acceptBlock : Com :=
  .seq prepB (.seq okLoop
    (.ite (.eq (V "ok") (.lit 1))
      (.ite (.eq (V "n") (.lit 0)) print0
        (.seq dmaxLoop (.seq (.assign "bd" (add (V "g") (.lit 1))) printBlock)))
      rejectPrint))

/-- The cost of the accepting phase. -/
def Kacc (Sz N : ℕ) : ℕ := 300 + 88 * N + Kprint Sz (4 * N) + 3 * (48 * Sz + 50)

lemma runMaxD_le (arr : List ℕ) (N b : ℕ) (h : ∀ k < 3 + 2 * N, arr.getD k 0 ≤ b) :
    runMaxD arr N ≤ b :=
  foldl_max_le (fun j => arr.getD (2 + 2 * j + 1) 0) b N 0 (Nat.zero_le _)
    (fun j hj => h _ (by omega))

lemma Kprint_mono (Sz a b : ℕ) (h : a ≤ b) : Kprint Sz a ≤ Kprint Sz b := by
  unfold Kprint
  have := Nat.mul_le_mul_left (Kcell Sz + 10 + 4) h
  omega

theorem acceptBlock_run (Sz : ℕ) (arr : List ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hE : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), arr.getD k 0 + 16 < B)
    (hL : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hlen : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) ≤ arr.length)
    (hNB : 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hM1 : (arr.getD 1 0 + 1) * (arr.getD 0 0 + 1) + 8 < B)
    (hA : σ.arrs "TK" = arr) :
    ∃ σ', Run B acceptBlock σ σ' (Kacc Sz (arr.getD 1 0 * arr.getD 0 0)) ∧
      σ'.out = σ.out ++
        (if 0 < arr.getD 1 0 ∧ paramOf arr = 1 ∧ ∀ t < arr.getD 1 0 * arr.getD 0 0, Pass arr t
          then numBits (outBlockG arr) else numBits [1, 0, 1]) := by
  set n := arr.getD 0 0 with hn'
  set m := arr.getD 1 0 with hm'
  set N := m * n with hN'
  have hB2 : 6 < B := by omega
  have hE8 : ∀ k < 3 + 2 * N, arr.getD k 0 + 8 < B := fun k hk => by
    have := hE k hk; omega
  have hn0 : n + 8 < B := hE8 0 (by omega)
  have hm0 : m + 8 < B := hE8 1 (by omega)
  -- the counts
  obtain ⟨σ1, r1, e1n, e1m, e1N, e1N2, e1n1, e1m1, e1M1, e1g, e1kp, e1ok, e1a, e1o, e1f⟩ :=
    (prepB_spec (B := B) arr hE8 hL hlen hNB hM1) σ hA
  have A1 : σ1.arrs "TK" = arr := by rw [e1a]; exact hA
  -- the pass over the table
  obtain ⟨σ2, r2, e2ok, e2a, e2o, e2f⟩ := okLoop_spec (B := B) arr N
    (if 0 < m ∧ paramOf arr = 1 then 1 else 0) σ1
    (fun k hk => hE8 k (by omega)) (by omega) (by omega) (by omega) (by split <;> omega) A1 e1N e1ok
  have A2 : σ2.arrs "TK" = arr := by rw [e2a]; exact A1
  have z2 : ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → y ≠ "d" → σ2.vars y = σ1.vars y := e2f
  have hcond : (σ2.vars "ok" = 1) ↔ ((0 < m ∧ paramOf arr = 1) ∧ ∀ t < N, Pass arr t) := by
    rw [e2ok, flagTo_eq_one]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra h0
      rw [if_neg h0] at h1
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [if_pos h1], h2⟩
  have hokB : σ2.vars "ok" < B := by
    rw [e2ok]; have := flagTo_le (Pass arr) (if 0 < m ∧ paramOf arr = 1 then 1 else 0) N; omega
  have hn2 : σ2.vars "n" = n := by
    rw [z2 "n" (by decide) (by decide) (by decide) (by decide), e1n]
  have hm12 : σ2.vars "m1" = m + 1 := by
    rw [z2 "m1" (by decide) (by decide) (by decide) (by decide), e1m1]
  by_cases hok : σ2.vars "ok" = 1
  · obtain ⟨⟨hm, hp⟩, hpass⟩ := hcond.1 hok
    have hcondT : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some true := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    have hnB : σ2.vars "n" < B := by omega
    by_cases hn00 : n = 0
    · have hcondT2 : (Cond.eq (V "n") (.lit 0)).evalB B σ2 = some true := by
        rw [evalB_condEq (evalB_var hnB) (evalB_lit (by omega))]
        simp [hn2, hn00]
      obtain ⟨σ3, r3, o3⟩ := print0_run (B := B) Sz m σ2 hs hm12 (by omega)
      refine ⟨σ3, (r1.seq (r2.seq (Run.ite_true hcondT (Run.ite_true hcondT2 r3)))).mono ?_, ?_⟩
      · unfold Kacc Kprint
        simp only [Cond.size, Expr.size]
        omega
      · rw [o3, e2o, e1o, if_pos ⟨hm, hp, hpass⟩]
        unfold outBlockG
        rw [if_pos hn00]
    · have hcondF2 : (Cond.eq (V "n") (.lit 0)).evalB B σ2 = some false := by
        rw [evalB_condEq (evalB_var hnB) (evalB_lit (by omega))]
        simp [hn2, hn00]
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn00
      have hnN : n ≤ N := Nat.le_mul_of_pos_left n hm
      have hmN : m ≤ N := Nat.le_mul_of_pos_right m hnpos
      -- the largest due date
      obtain ⟨σ3, r3, e3g, e3a, e3o, e3f⟩ := dmaxLoop_spec (B := B) arr N σ2 (fun k hk => hE8 k (by omega)) (by omega) (by omega) (by omega) A2
        (by rw [z2 "N" (by decide) (by decide) (by decide) (by decide), e1N])
        (by rw [z2 "g" (by decide) (by decide) (by decide) (by decide), e1g])
      have A3 : σ3.arrs "TK" = arr := by rw [e3a]; exact A2
      have z3 : ∀ y, y ≠ "g" → y ≠ "i" → y ≠ "p" → y ≠ "ok" → y ≠ "d" →
          σ3.vars y = σ1.vars y := fun y a b c d e => by
        rw [e3f y a b c, z2 y d b c e]
      have hB17 : 17 ≤ B := by have := hE 0 (by omega); omega
      have hrm : runMaxD arr N + 16 ≤ B := by
        have := runMaxD_le arr N (B - 17) (fun k hk => by have := hE k hk; omega)
        omega
      -- the base
      have hg3 : σ3.vars "g" = runMaxD arr N := e3g
      have hgB : σ3.vars "g" + 1 < B := by omega
      have r4 : Run B (.assign "bd" (add (V "g") (.lit 1))) σ3
          (σ3.setVar "bd" (runMaxD arr N + 1)) (1 + (add (V "g") (.lit 1)).size) := by
        refine Run.assign ?_
        have h := evalB_bin (B := B) (op := .add) (evalB_var (B := B) (x := "g") (σ := σ3) (by omega))
          (evalB_lit (B := B) (σ := σ3) (n := 1) (by omega)) (by simp [hg3]; omega)
        simpa [hg3] using h
      set σ4 := σ3.setVar "bd" (runMaxD arr N + 1) with hσ4
      have A4 : σ4.arrs "TK" = arr := by simp [hσ4, Env.setVar, A3]
      have z4 : ∀ y, y ≠ "g" → y ≠ "i" → y ≠ "p" → y ≠ "ok" → y ≠ "d" → y ≠ "bd" →
          σ4.vars y = σ1.vars y := fun y a b c d e f => by
        simp only [hσ4, Env.setVar, if_neg f]
        exact z3 y a b c d e
      have hbd4 : σ4.vars "bd" = runMaxD arr N + 1 := by simp [hσ4, Env.setVar]
      have hM4 : (m + 1) * (n + 1) ≤ 4 * N := by nlinarith
      obtain ⟨σ5, r5, o5⟩ := printBlock_run (B := B) Sz arr n m (runMaxD arr N + 1) σ4 hs A4
        (by rw [z4 "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e1n])
        (by rw [z4 "m" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e1m])
        (by rw [z4 "n1" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e1n1])
        (by rw [z4 "m1" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e1m1])
        hbd4
        (by rw [z4 "M1" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e1M1])
        hM1 (by omega) (by omega) (by omega) hm hE8 hL hlen
      refine ⟨σ5, (r1.seq (r2.seq (Run.ite_true hcondT (Run.ite_false hcondF2
        (r3.seq (r4.seq r5)))))).mono ?_, ?_⟩
      · unfold Kacc
        simp only [Cond.size, Expr.size]
        have := Kprint_mono Sz _ _ hM4
        omega
      · have e4o : σ4.out = σ3.out := by simp [hσ4, Env.setVar]
        rw [o5, e4o, e3o, e2o, e1o, if_pos ⟨hm, hp, hpass⟩]
        unfold outBlockG
        rw [if_neg hn00]
  · have hno : ¬ ((0 < m ∧ paramOf arr = 1) ∧ ∀ t < N, Pass arr t) := fun h => hok (hcond.2 h)
    obtain ⟨σ3, r3, e3o, e3a, e3f⟩ := rejectPrint_run (B := B) Sz σ2 hs hB2
    have hcondF : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some false := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_false hcondF r3))).mono ?_, ?_⟩
    · unfold Kacc
      simp only [Cond.size, Expr.size]
      omega
    · rw [e3o, e2o, e1o, if_neg (by rintro ⟨h1, h2, h3⟩; exact hno ⟨⟨h1, h2⟩, h3⟩)]

end Lax117284Proofs.Machine.BlockAccept
