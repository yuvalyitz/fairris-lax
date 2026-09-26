import Lax117284Proofs.Machine.PerProg
import Lax117284Proofs.Machine.FreeAccept
import Lax117284Proofs.Machine.BlockAccept

/-!
The whole of the reduction of Lemma 15 after the tokenizer has accepted: read the counts off the
array, check the table and the parameters, find the largest due date, and write either the image or
the rejected word.
-/

namespace Lax117284Proofs.Machine.PerAccept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.InstSem Lax117284Proofs.Machine.BlockSem
open Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.Flag Lax117284Proofs.Machine.BlockCheck
open Lax117284Proofs.Machine.PerSem Lax117284Proofs.Machine.PerCheck Lax117284Proofs.Machine.PerProg
open Lax117284Proofs.Machine.FreeAccept

variable {B : ℕ}

/-- Read the counts off the array. -/
def prepP : Com :=
  .seq (.assign "n" (.get "TK" (.lit 0)))
  (.seq (.assign "m" (.get "TK" (.lit 1)))
  (.seq (.assign "N" (mul (V "m") (V "n")))
  (.seq (.assign "N2" (mul (.lit 2) (V "N")))
  (.seq (.assign "n1" (add (V "n") (.lit 1)))
  (.seq (.assign "n2" (add (V "n") (.lit 2)))
  (.seq (.assign "m2" (mul (.lit 2) (V "m")))
  (.seq (.assign "M2" (mul (V "m2") (V "n2")))
  (.seq (.assign "g" (.lit 0))
    (.assign "ok" (.lit 1))))))))))

set_option maxHeartbeats 1600000 in
theorem prepP_spec (arr : List ℕ)
    (hE : ∀ k < 2 + 2 * (arr.getD 1 0 * arr.getD 0 0) + arr.getD 0 0, arr.getD k 0 + 8 < B)
    (hL : 2 + 2 * (arr.getD 1 0 * arr.getD 0 0) + arr.getD 0 0 + 8 < B)
    (hlen : 2 + 2 * (arr.getD 1 0 * arr.getD 0 0) + arr.getD 0 0 ≤ arr.length)
    (hNB : 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hm2 : 2 * arr.getD 1 0 + 8 < B)
    (hM2 : 2 * arr.getD 1 0 * (arr.getD 0 0 + 2) + 8 < B) :
    Spec B (fun σ => σ.arrs "TK" = arr) prepP
      (fun σ σ' => σ'.vars "n" = arr.getD 0 0 ∧ σ'.vars "m" = arr.getD 1 0 ∧
        σ'.vars "N" = arr.getD 1 0 * arr.getD 0 0 ∧
        σ'.vars "N2" = 2 * (arr.getD 1 0 * arr.getD 0 0) ∧
        σ'.vars "n1" = arr.getD 0 0 + 1 ∧ σ'.vars "n2" = arr.getD 0 0 + 2 ∧
        σ'.vars "m2" = 2 * arr.getD 1 0 ∧
        σ'.vars "M2" = 2 * arr.getD 1 0 * (arr.getD 0 0 + 2) ∧ σ'.vars "g" = 0 ∧
        σ'.vars "ok" = 1 ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        ∀ y, y ≠ "n" → y ≠ "m" → y ≠ "N" → y ≠ "N2" → y ≠ "n1" → y ≠ "n2" → y ≠ "m2" →
          y ≠ "M2" → y ≠ "g" → y ≠ "ok" → σ'.vars y = σ.vars y) 100 := by
  run_vcg
  all_goals (
    have hA := ‹σ.arrs "TK" = arr›
    have e0 := hE 0 (by omega)
    have e1 := hE 1 (by omega)
    subst hA
    try simp only [Env.setVar] at *
    try simp at *)
  all_goals try omega
  all_goals (
    intro y a b c d e f g h i j
    simp [a, b, c, d, e, f, g, h, i, j])


/-- The whole of the reduction, after the tokenizer has accepted. -/
def acceptP : Com :=
  .seq prepP (.seq okLoop (.seq parLoop
    (.ite (.eq (V "ok") (.lit 1))
      (.ite (.eq (V "n") (.lit 0)) print0L (.seq dmaxLoop printL))
      rejectPrint)))

/-- The numbers of the image, read off the array. -/
def outPG (arr : List ℕ) : List ℕ :=
  if arr.getD 0 0 = 0 then [0, 0, 0]
  else outLG arr (arr.getD 0 0) (arr.getD 1 0) (runMaxD arr (arr.getD 1 0 * arr.getD 0 0))

/-- The cost of the accepting phase, on an input of `l` numbers. -/
def KaccP (Sz l : ℕ) : ℕ := 400 + 132 * l + 3 * (48 * Sz + 50) + KprintL Sz (6 * l)

lemma KprintL_mono (Sz a b : ℕ) (h : a ≤ b) : KprintL Sz a ≤ KprintL Sz b := by
  unfold KprintL
  have := Nat.mul_le_mul_left (KcellP Sz + 10 + 4) h
  omega

lemma KaccP_mono (Sz a b : ℕ) (h : a ≤ b) : KaccP Sz a ≤ KaccP Sz b := by
  unfold KaccP
  have := KprintL_mono Sz (6 * a) (6 * b) (by omega)
  omega

theorem acceptP_run (Sz l : ℕ) (arr : List ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hE : ∀ k < 2 + 2 * (arr.getD 1 0 * arr.getD 0 0) + arr.getD 0 0, arr.getD k 0 + 16 < B)
    (hL : 2 + 2 * (arr.getD 1 0 * arr.getD 0 0) + arr.getD 0 0 + 8 < B)
    (hlen : 2 + 2 * (arr.getD 1 0 * arr.getD 0 0) + arr.getD 0 0 ≤ arr.length)
    (hNB : 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hm2 : 2 * arr.getD 1 0 + 8 < B)
    (hM2 : 2 * arr.getD 1 0 * (arr.getD 0 0 + 2) + 8 < B)
    (hsum : runMaxD arr (arr.getD 1 0 * arr.getD 0 0) + 2 * arr.getD 0 0 + 16 < B)
    (hl : arr.getD 1 0 * arr.getD 0 0 + arr.getD 0 0 ≤ l)
    (hA : σ.arrs "TK" = arr) :
    ∃ σ', Run B acceptP σ σ' (KaccP Sz l) ∧
      σ'.out = σ.out ++
        (if (∀ t < arr.getD 1 0 * arr.getD 0 0, Pass arr t) ∧
            (∀ j < arr.getD 0 0, PassK arr (arr.getD 1 0) (2 * (arr.getD 1 0 * arr.getD 0 0)) j)
          then numBits (outPG arr) else numBits [1, 0, 1]) := by
  set n := arr.getD 0 0 with hn'
  set m := arr.getD 1 0 with hm'
  set N := m * n with hN'
  have hB2 : 6 < B := by omega
  have hE8 : ∀ k < 2 + 2 * N + n, arr.getD k 0 + 8 < B := fun k hk => by
    have := hE k hk; omega
  have hn0 : n + 8 < B := hE8 0 (by omega)
  have hm0 : m + 8 < B := hE8 1 (by omega)
  obtain ⟨σ1, r1, e1n, e1m, e1N, e1N2, e1n1, e1n2, e1m2, e1M2, e1g, e1ok, e1a, e1o, e1f⟩ :=
    (prepP_spec (B := B) arr hE8 hL hlen hNB hm2 hM2) σ hA
  have A1 : σ1.arrs "TK" = arr := by rw [e1a]; exact hA
  -- the table
  obtain ⟨σ2, r2, e2ok, e2a, e2o, e2f⟩ := okLoop_spec (B := B) arr N 1 σ1
    (fun k hk => hE8 k (by omega)) (by omega) (by omega) (by omega) le_rfl A1 e1N e1ok
  have A2 : σ2.arrs "TK" = arr := by rw [e2a]; exact A1
  have z2 : ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → y ≠ "d" → σ2.vars y = σ1.vars y := e2f
  -- the parameters
  obtain ⟨σ3, r3, e3ok, e3a, e3o, e3f⟩ := parLoop_spec (B := B) arr n m (2 * N)
    (flagTo (Pass arr) 1 N) σ2 hE8 hL hlen hn0 hm0 (flagTo_le _ _ _) A2
    (by rw [z2 "n" (by decide) (by decide) (by decide) (by decide), e1n])
    (by rw [z2 "m" (by decide) (by decide) (by decide) (by decide), e1m])
    (by rw [z2 "N2" (by decide) (by decide) (by decide) (by decide), e1N2]) e2ok
  have A3 : σ3.arrs "TK" = arr := by rw [e3a]; exact A2
  have z3 : ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → y ≠ "d" → σ3.vars y = σ1.vars y :=
    fun y a b c d => by rw [e3f y a b c, z2 y a b c d]
  have hcond : (σ3.vars "ok" = 1) ↔
      ((∀ t < N, Pass arr t) ∧ (∀ j < n, PassK arr m (2 * N) j)) := by
    rw [e3ok, flagTo_eq_one, flagTo_eq_one]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨rfl, h1⟩, h2⟩
  have hokB : σ3.vars "ok" < B := by
    rw [e3ok]; have := flagTo_le (PassK arr m (2 * N)) (flagTo (Pass arr) 1 N) n; omega
  have hn3 : σ3.vars "n" = n := by
    rw [z3 "n" (by decide) (by decide) (by decide) (by decide), e1n]
  by_cases hok : σ3.vars "ok" = 1
  · obtain ⟨hpass, hparam⟩ := hcond.1 hok
    have hcondT : (Cond.eq (V "ok") (.lit 1)).evalB B σ3 = some true := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    have hnB : σ3.vars "n" < B := by omega
    by_cases hn00 : n = 0
    · have hcondT2 : (Cond.eq (V "n") (.lit 0)).evalB B σ3 = some true := by
        rw [evalB_condEq (evalB_var hnB) (evalB_lit (by omega))]
        simp [hn3, hn00]
      obtain ⟨σ4, r4, o4⟩ := print0L_run (B := B) Sz σ3 hs hB2
      refine ⟨σ4, (r1.seq (r2.seq (r3.seq (Run.ite_true hcondT (Run.ite_true hcondT2 r4))))).mono ?_, ?_⟩
      · unfold KaccP KprintL
        simp only [Cond.size, Expr.size]
        omega
      · rw [o4, e3o, e2o, e1o, if_pos ⟨hpass, hparam⟩]
        unfold outPG
        rw [if_pos hn00]
    · have hcondF2 : (Cond.eq (V "n") (.lit 0)).evalB B σ3 = some false := by
        rw [evalB_condEq (evalB_var hnB) (evalB_lit (by omega))]
        simp [hn3, hn00]
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn00
      -- the largest due date
      obtain ⟨σ4, r4, e4g, e4a, e4o, e4f⟩ := dmaxLoop_spec (B := B) arr N σ3
        (fun k hk => hE8 k (by omega)) (by omega) (by omega) (by omega) A3
        (by rw [z3 "N" (by decide) (by decide) (by decide) (by decide), e1N])
        (by rw [z3 "g" (by decide) (by decide) (by decide) (by decide), e1g])
      have A4 : σ4.arrs "TK" = arr := by rw [e4a]; exact A3
      have z4 : ∀ y, y ≠ "g" → y ≠ "i" → y ≠ "p" → y ≠ "ok" → y ≠ "d" →
          σ4.vars y = σ1.vars y := fun y a b c d e => by
        rw [e4f y a b c, z3 y d b c e]
      have hg4 : σ4.vars "g" = runMaxD arr N := e4g
      have hM2' : 2 * m * (n + 2) ≤ 6 * l := by
        rcases Nat.eq_zero_or_pos m with hm00 | hm00
        · rw [hm00]; simp
        · have : n + 2 ≤ 3 * n := by omega
          have h2 := Nat.mul_le_mul_left (2 * m) this
          have h3 : 2 * m * (3 * n) = 6 * (m * n) := by ring
          omega
      obtain ⟨σ5, r5, o5⟩ := printL_run (B := B) Sz arr n m (runMaxD arr N) σ4 hs A4
        (by rw [z4 "n" (by decide) (by decide) (by decide) (by decide) (by decide), e1n])
        (by rw [z4 "m" (by decide) (by decide) (by decide) (by decide) (by decide), e1m])
        (by rw [z4 "n2" (by decide) (by decide) (by decide) (by decide) (by decide), e1n2])
        (by rw [z4 "m2" (by decide) (by decide) (by decide) (by decide) (by decide), e1m2])
        (by rw [z4 "n1" (by decide) (by decide) (by decide) (by decide) (by decide), e1n1])
        hg4
        (by rw [z4 "N2" (by decide) (by decide) (by decide) (by decide) (by decide), e1N2])
        (by rw [z4 "M2" (by decide) (by decide) (by decide) (by decide) (by decide), e1M2])
        hM2 hn0 hm0 hsum hE8 hL hlen
      refine ⟨σ5, (r1.seq (r2.seq (r3.seq (Run.ite_true hcondT (Run.ite_false hcondF2
        (r4.seq r5)))))).mono ?_, ?_⟩
      · unfold KaccP
        simp only [Cond.size, Expr.size]
        have := KprintL_mono Sz _ _ hM2'
        omega
      · rw [o5, e4o, e3o, e2o, e1o, if_pos ⟨hpass, hparam⟩]
        unfold outPG
        rw [if_neg hn00]
  · have hno : ¬ ((∀ t < N, Pass arr t) ∧ (∀ j < n, PassK arr m (2 * N) j)) :=
      fun h => hok (hcond.2 h)
    obtain ⟨σ4, r4, e4o, e4a, e4f⟩ := rejectPrint_run (B := B) Sz σ3 hs hB2
    have hcondF : (Cond.eq (V "ok") (.lit 1)).evalB B σ3 = some false := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    refine ⟨σ4, (r1.seq (r2.seq (r3.seq (Run.ite_false hcondF r4)))).mono ?_, ?_⟩
    · unfold KaccP
      simp only [Cond.size, Expr.size]
      omega
    · rw [e4o, e3o, e2o, e1o, if_neg hno]

end Lax117284Proofs.Machine.PerAccept
