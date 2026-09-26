import Lax117284Proofs.Machine.T9Print
import Lax117284Proofs.Machine.FreeAccept

/-!
The whole of the reduction of Theorem 9 after the tokenizer has accepted: read the counts and the
parameter off the array, check the table and the parameter, and write either the formula or the
unsatisfiable one.
-/

namespace Lax117284Proofs.Machine.T9Accept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.T9Sem Lax117284Proofs.Machine.T9Print Lax117284Proofs.Machine.FreeAccept
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.T9Prog Lax117284Proofs.Machine.T9Comp1

variable {B : ℕ}

/-- Read the counts and the parameter off the array. -/
def prepT : Com :=
  .seq (.assign "n" (.get "TK" (.lit 0)))
  (.seq (.assign "m" (.get "TK" (.lit 1)))
  (.seq (.assign "N" (mul (V "m") (V "n")))
  (.seq (.assign "N2" (mul (.lit 2) (V "N")))
  (.seq (.assign "kp" (.get "TK" (add (.lit 2) (V "N2"))))
  (.seq (.assign "k1" (add (V "kp") (.lit 1)))
  (.seq (.assign "nn" (mul (V "n") (V "n")))
  (.seq (.assign "mm" (mul (V "m") (V "m")))
  (.seq (.assign "V1" (add (V "N") (.lit 1)))
  (.seq (.assign "C1" (mul (V "N") (V "n")))
  (.seq (.assign "tq" (mul (V "n") (V "m")))
  (.seq (.assign "C2" (mul (V "tq") (V "m")))
  (.seq (.assign "CC" (add (V "C1") (V "C2")))
    (.ite (.eq (V "k1") (V "m")) (.assign "ok" (.lit 1)) (.assign "ok" (.lit 0)))))))))))))))

set_option maxHeartbeats 6400000 in
theorem prepT_spec (arr : List ℕ)
    (hE : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), arr.getD k 0 + 8 < B)
    (hL : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hlen : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) ≤ arr.length)
    (hNB : 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hnn : arr.getD 0 0 * arr.getD 0 0 + 8 < B) (hmm : arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (hC1 : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 + 8 < B)
    (hC2 : arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (hCC : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 +
      arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (htq : arr.getD 0 0 * arr.getD 1 0 + 8 < B) :
    Spec B (fun σ => σ.arrs "TK" = arr) prepT
      (fun σ σ' => σ'.vars "n" = arr.getD 0 0 ∧ σ'.vars "m" = arr.getD 1 0 ∧
        σ'.vars "N" = arr.getD 1 0 * arr.getD 0 0 ∧
        σ'.vars "N2" = 2 * (arr.getD 1 0 * arr.getD 0 0) ∧
        σ'.vars "nn" = arr.getD 0 0 * arr.getD 0 0 ∧
        σ'.vars "mm" = arr.getD 1 0 * arr.getD 1 0 ∧
        σ'.vars "V1" = arr.getD 1 0 * arr.getD 0 0 + 1 ∧
        σ'.vars "C1" = arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 ∧
        σ'.vars "C2" = arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 ∧
        σ'.vars "CC" = arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 +
          arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 ∧
        σ'.vars "ok" = (if paramOf arr + 1 = arr.getD 1 0 then 1 else 0) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        ∀ y, y ≠ "n" → y ≠ "m" → y ≠ "N" → y ≠ "N2" → y ≠ "kp" → y ≠ "k1" → y ≠ "nn" →
          y ≠ "mm" → y ≠ "V1" → y ≠ "C1" → y ≠ "tq" → y ≠ "C2" → y ≠ "CC" → y ≠ "ok" →
          σ'.vars y = σ.vars y) 200 := by
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
    refine ⟨?_, fun y a b c d e f g h i j k l o p => ?_⟩
    · simp only [paramOf, List.getD_eq_getElem?_getD]
      first | omega | (intro h1; omega)
    · simp [a, b, c, d, e, f, g, h, i, j, k, l, o, p])


/-- Write the unsatisfiable formula. -/
def rejT9 : Com :=
  .seq (emitLit 1) (.seq (emitLit 2) (.seq (emitLit 0) (.seq (.write (.lit 1))
    (.seq (emitLit 0) (.seq (.write (.lit 1)) (.seq (emitLit 0) (.seq (.write (.lit 0))
    (.seq (emitLit 0) (.write (.lit 0))))))))))

/-- The cost of writing the unsatisfiable formula. -/
def Krej9 (Sz : ℕ) : ℕ := 6 * (48 * Sz + 50) + 20

lemma unsat_bits : natBits (Lax117284.TwoSatisfiability.encodeFormula
    Lax117284.TwoSatisfiability.unsatisfiable) =
    bitsNat 1 ++ bitsNat 2 ++ (bitsNat 0 ++ [1] ++ bitsNat 0 ++ [1]) ++
      (bitsNat 0 ++ [0] ++ bitsNat 0 ++ [0]) := by
  have hf2 : List.finRange 2 = [0, 1] := by decide
  unfold Lax117284.TwoSatisfiability.encodeFormula Lax117284.TwoSatisfiability.unsatisfiable
  have hf : List.finRange 2 = [0, 1] := hf2
  simp only [hf, List.flatMap_cons, List.flatMap_nil, List.append_nil, natBits_app,
    natBits_encodeNat, List.length_cons, List.append_assoc]
  simp [natBits, natBits_encodeNat]

theorem rejT9_run (Sz : ℕ) (σ : Env) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hB : 6 < B) :
    ∃ σ', Run B rejT9 σ σ' (Krej9 Sz) ∧
      σ'.out = σ.out ++ natBits (Lax117284.TwoSatisfiability.encodeFormula
        Lax117284.TwoSatisfiability.unsatisfiable) := by
  have e : ∀ (n : ℕ) (σ : Env), n + 4 < B → ∃ σ', Run B (emitLit n) σ σ' (48 * Sz + 50) ∧
      σ'.out = σ.out ++ bitsNat n := fun n σ hn => by
    obtain ⟨σ', r, o, -, -⟩ := emitLit_spec (B := B) n Sz hn (hs _ hn) σ trivial
    exact ⟨σ', r, o⟩
  obtain ⟨σ1, r1, o1⟩ := e 1 σ (by omega)
  obtain ⟨σ2, r2, o2⟩ := e 2 σ1 (by omega)
  obtain ⟨σ3, r3, o3⟩ := e 0 σ2 (by omega)
  have w4 := write_bit (B := B) 1 (by omega) σ3
  obtain ⟨σ5, r5, o5⟩ := e 0 { σ3 with out := σ3.out ++ [1] } (by omega)
  have w6 := write_bit (B := B) 1 (by omega) σ5
  obtain ⟨σ7, r7, o7⟩ := e 0 { σ5 with out := σ5.out ++ [1] } (by omega)
  have w8 := write_bit (B := B) 0 (by omega) σ7
  obtain ⟨σ9, r9, o9⟩ := e 0 { σ7 with out := σ7.out ++ [0] } (by omega)
  have w10 := write_bit (B := B) 0 (by omega) σ9
  refine ⟨{ σ9 with out := σ9.out ++ [0] }, (r1.seq (r2.seq (r3.seq (w4.seq (r5.seq (w6.seq
    (r7.seq (w8.seq (r9.seq w10))))))))).mono (by unfold Krej9; omega), ?_⟩
  simp only [o9, o7, o5, o3, o2, o1, unsat_bits, List.append_assoc]

/-- The whole of the reduction, after the tokenizer has accepted. -/
def acceptT : Com :=
  .seq prepT (.seq okLoop (.ite (.eq (V "ok") (.lit 1)) printT9 rejT9))

/-- The cost of the accepting phase, on an input of `l` numbers. -/
def KaccT (Sz l : ℕ) : ℕ := 400 + 44 * l + KprintT Sz (l * l) (l * l) + Krej9 Sz

lemma KprintT_mono (Sz a b c d : ℕ) (h1 : a ≤ c) (h2 : b ≤ d) :
    KprintT Sz a b ≤ KprintT Sz c d := by
  unfold KprintT
  have := Nat.mul_le_mul_left (K1 Sz + 10 + 4) h1
  have := Nat.mul_le_mul_left (K1 Sz + 10 + 4) h2
  omega

lemma KaccT_mono (Sz a b : ℕ) (h : a ≤ b) : KaccT Sz a ≤ KaccT Sz b := by
  unfold KaccT
  have := KprintT_mono Sz (a * a) (a * a) (b * b) (b * b) (Nat.mul_le_mul h h) (Nat.mul_le_mul h h)
  omega

theorem acceptT_run (Sz l : ℕ) (arr : List ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hE : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), arr.getD k 0 + 8 < B)
    (hL : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hlen : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) ≤ arr.length)
    (hNB : 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hnn : arr.getD 0 0 * arr.getD 0 0 + 8 < B) (hmm : arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (hC1 : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 + 8 < B)
    (hC2 : arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (hCC : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 +
      arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (htq : arr.getD 0 0 * arr.getD 1 0 + 8 < B)
    (hl1 : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 ≤ l * l)
    (hl2 : arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 ≤ l * l)
    (hl : arr.getD 1 0 * arr.getD 0 0 ≤ l)
    (hA : σ.arrs "TK" = arr) :
    ∃ σ', Run B acceptT σ σ' (KaccT Sz l) ∧
      σ'.out = σ.out ++
        (if (∀ t < arr.getD 1 0 * arr.getD 0 0, Pass arr t) ∧ paramOf arr + 1 = arr.getD 1 0
          then natBits (outT9 arr (arr.getD 0 0) (arr.getD 1 0))
          else natBits (Lax117284.TwoSatisfiability.encodeFormula
            Lax117284.TwoSatisfiability.unsatisfiable)) := by
  set n := arr.getD 0 0 with hn'
  set m := arr.getD 1 0 with hm'
  set N := m * n with hN'
  have hB2 : 6 < B := by omega
  have hn0 : n + 8 < B := hE 0 (by omega)
  have hm0 : m + 8 < B := hE 1 (by omega)
  obtain ⟨σ1, r1, e1n, e1m, e1N, e1N2, e1nn, e1mm, e1V, e1C1, e1C2, e1CC, e1ok, e1a, e1o, e1f⟩ :=
    (prepT_spec (B := B) arr hE hL hlen hNB hnn hmm hC1 hC2 hCC htq) σ hA
  have A1 : σ1.arrs "TK" = arr := by rw [e1a]; exact hA
  obtain ⟨σ2, r2, e2ok, e2a, e2o, e2f⟩ := okLoop_spec (B := B) arr N
    (if paramOf arr + 1 = m then 1 else 0) σ1
    (fun k hk => hE k (by omega)) (by omega) (by omega) (by omega) (by split <;> omega) A1 e1N e1ok
  have A2 : σ2.arrs "TK" = arr := by rw [e2a]; exact A1
  have z2 : ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → y ≠ "d" → σ2.vars y = σ1.vars y := e2f
  have hcond : (σ2.vars "ok" = 1) ↔ ((∀ t < N, Pass arr t) ∧ paramOf arr + 1 = m) := by
    rw [e2ok, flagTo_eq_one]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      by_contra h0
      rw [if_neg h0] at h1
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [if_pos h2], h1⟩
  have hokB : σ2.vars "ok" < B := by
    rw [e2ok]; have := flagTo_le (Pass arr) (if paramOf arr + 1 = m then 1 else 0) N; omega
  by_cases hok : σ2.vars "ok" = 1
  · obtain ⟨hpass, hp⟩ := hcond.1 hok
    have hcondT : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some true := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    have hnnB' : n * n + 8 < B := hnn
    obtain ⟨σ3, r3, o3⟩ := printT9_run (B := B) Sz arr n m σ2 hs A2
      (by rw [z2 "n" (by decide) (by decide) (by decide) (by decide), e1n])
      (by rw [z2 "m" (by decide) (by decide) (by decide) (by decide), e1m])
      (by rw [z2 "nn" (by decide) (by decide) (by decide) (by decide), e1nn])
      (by rw [z2 "mm" (by decide) (by decide) (by decide) (by decide), e1mm])
      (by rw [z2 "V1" (by decide) (by decide) (by decide) (by decide), e1V])
      (by rw [z2 "CC" (by decide) (by decide) (by decide) (by decide), e1CC])
      (by rw [z2 "C1" (by decide) (by decide) (by decide) (by decide), e1C1])
      (by rw [z2 "C2" (by decide) (by decide) (by decide) (by decide), e1C2])
      hCC hn0 hm0 hnn hmm (by omega) (fun k hk => hE k hk) hL hlen
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_true hcondT r3))).mono ?_, ?_⟩
    · unfold KaccT
      simp only [Cond.size, Expr.size]
      have := KprintT_mono Sz (m * n * n) (n * m * m) (l * l) (l * l) hl1 hl2
      have hK : KprintT Sz (m * n * n) (n * m * m) ≤ KprintT Sz (l * l) (l * l) := this
      omega
    · rw [o3, e2o, e1o, if_pos ⟨hpass, hp⟩]
  · have hno : ¬ ((∀ t < N, Pass arr t) ∧ paramOf arr + 1 = m) := fun h => hok (hcond.2 h)
    obtain ⟨σ3, r3, o3⟩ := rejT9_run (B := B) Sz σ2 hs hB2
    have hcondF : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some false := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_false hcondF r3))).mono ?_, ?_⟩
    · unfold KaccT
      simp only [Cond.size, Expr.size]
      omega
    · rw [o3, e2o, e1o, if_neg hno]

end Lax117284Proofs.Machine.T9Accept
