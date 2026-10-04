import Lax117284Proofs.Machine.T9Print
import Lax117284Proofs.Machine.X1Sem
import Lax117284Proofs.Machine.T9Accept
import Lax117284Proofs.Machine.MisBlk

/-! ### `Lax117284Proofs.Machine.X1Print` -/

section
/-!
Writing the formula of a conflict-free instance: the two counts, the loop over the conflict
clauses of Theorem 9, and one clause for every variable asking for it to be true.
-/

namespace Lax117284Proofs.Machine.X1Print

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.T9Sem
open Lax117284Proofs.Machine.InstSem Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Machine.T9Comp1 Lax117284Proofs.Machine.T9Comp2 Lax117284Proofs.Machine.T9Prog
open Lax117284Proofs.Machine.T9Print Lax117284Proofs.Machine.X1Sem

variable {B : ℕ}

/-- One unit clause: the variable the counter names, asked to be true. -/
def bodyU : Com := emitClause "i" "i" 1 1

/-- **A unit clause.** -/
theorem bodyU_run (Sz : ℕ) (σ : Env) (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hi : σ.vars "i" + 4 < B) (hB : 1 < B) :
    ∃ σ', Run B bodyU σ σ' (2 * (48 * Sz + 50) + 4) ∧
      σ'.out = σ.out ++ (bitsNat (σ.vars "i") ++ [1] ++ bitsNat (σ.vars "i") ++ [1]) ∧
      (∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs :=
  emitClause_run (B := B) Sz "i" "i" 1 1 σ hs (by decide) (by decide) hi hi hB hB

/-- **The loop over the unit clauses.** -/
theorem unitLoop_run (Sz : ℕ) (N : ℕ) (σ0 : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hN : σ0.vars "N" = N) (hNB : N + 8 < B) :
    ∃ σ', Run B (outLoop "N" bodyU) σ0 σ' ((2 * (48 * Sz + 50) + 4 + 10 + 4) * N + 6) ∧
      σ'.out = σ0.out ++ (List.range N).flatMap
        (fun v => bitsNat v ++ [1] ++ bitsNat v ++ [1]) ∧
      (∀ y ∉ "i" :: S9, σ'.vars y = σ0.vars y) ∧ σ'.arrs = σ0.arrs := by
  obtain ⟨σ', r, o, hAg⟩ := eLoop (B := B) "N" bodyU ("i" :: S9)
    (fun v => bitsNat v ++ [1] ++ bitsNat v ++ [1]) (2 * (48 * Sz + 50) + 4) N σ0 (by simp)
    (by decide) hN (by omega) (by
      intro σ hAg hlt
      obtain ⟨σ1, r1, o1, v1, a1⟩ := bodyU_run (B := B) Sz σ hs (by omega) (by omega)
      refine ⟨σ1, r1, o1, ⟨a1.trans hAg.1, fun y hy => ?_⟩, ?_⟩
      · have hy' : y ∉ S9 := fun h => hy (List.mem_cons_of_mem _ h)
        rw [v1 y (nscr_of_s9 hy'), hAg.2 y hy]
      · exact v1 "i" (by decide))
  exact ⟨σ', r, o, hAg.2, hAg.1⟩

/-- Write the whole formula. -/
def printU : Com :=
  .seq (emitVar "V1") (.seq (emitVar "CU")
    (.seq (outLoop "C1" body1) (outLoop "N" bodyU)))

/-- The cost of writing the formula. -/
def KprintU (Sz C1 N : ℕ) : ℕ :=
  2 * (48 * Sz + 50) + ((K1 Sz + 10 + 4) * C1 + 6) + ((2 * (48 * Sz + 50) + 4 + 10 + 4) * N + 6)

lemma KprintU_le (Sz C1 N C2 : ℕ) (h : N ≤ C2) : KprintU Sz C1 N ≤ KprintT Sz C1 C2 := by
  unfold KprintU KprintT K1
  have := Nat.mul_le_mul_left (2 * (48 * Sz + 50) + 4 + 10 + 4) h
  have h2 : (2 * (48 * Sz + 50) + 4 + 10 + 4) * C2 ≤ (320 + 2 * (48 * Sz + 50) + 10 + 4) * C2 :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- **Writing the formula.** -/
theorem printU_run (Sz : ℕ) (arr : List ℕ) (n m : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hnn : σ.vars "nn" = n * n)
    (hV : σ.vars "V1" = m * n + 1) (hCU : σ.vars "CU" = m * n * n + m * n)
    (hC1 : σ.vars "C1" = m * n * n) (hN : σ.vars "N" = m * n)
    (hCUB : m * n * n + m * n + 8 < B) (hnB : n + 8 < B)
    (hnnB : n * n + 8 < B) (hmnB : m * n + 8 < B)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 + 8 < B) (hL : 3 + 2 * (m * n) + 8 < B)
    (hlen : 3 + 2 * (m * n) ≤ arr.length) :
    ∃ σ', Run B printU σ σ' (KprintU Sz (m * n * n) (m * n)) ∧
      σ'.out = σ.out ++ natBits (outU arr n m) := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "V1" Sz σ
    ⟨by rw [hV]; omega, by rw [hV]; exact hs _ (by omega)⟩
  have z1 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ1.vars y = σ.vars y := v1
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitVar_spec (B := B) "CU" Sz σ1
    ⟨by rw [v1 "CU" (by decide), hCU]; omega,
      by rw [v1 "CU" (by decide), hCU]; exact hs _ (by omega)⟩
  have z2 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ2.vars y = σ.vars y := fun y hy => by
    rw [v2 y hy, v1 y hy]
  have A2 : σ2.arrs "TK" = arr := by rw [a2, a1]; exact hA
  have hC1B : m * n * n + 8 < B := by omega
  obtain ⟨σ3, r3, o3, v3, a3⟩ := cl1Loop_run (B := B) Sz arr n m σ2 hs A2
    (by rw [z2 "n" (by decide)]; exact hn) (by rw [z2 "nn" (by decide)]; exact hnn)
    (by rw [z2 "C1" (by decide)]; exact hC1) hC1B hnB hnnB hmnB hE hL hlen
  have z3 : ∀ y, y ∉ "i" :: S9 → σ3.vars y = σ.vars y := fun y hy => by
    rw [v3 y hy]; exact z2 y (fun h => hy (List.mem_cons_of_mem _ (by
      simp only [S9, SCR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      tauto)))
  obtain ⟨σ4, r4, o4, v4, a4⟩ := unitLoop_run (B := B) Sz (m * n) σ3 hs
    (by rw [z3 "N" (by decide)]; exact hN) hmnB
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by unfold KprintU; omega), ?_⟩
  rw [o4, o3, o2, o1, z1 "CU" (by decide), hCU, hV]
  unfold outU
  have e1 : natBits ((List.range (m * n * n)).flatMap (clW arr n m)) =
      (List.range (m * n * n)).flatMap (clB arr n m) := by
    simp only [natBits, List.map_flatMap]
    exact List.flatMap_congr fun c _ => natBits_clW arr n m c
  have hv : ∀ v : ℕ, natBits (encodeNat v ++ ([true] ++ (encodeNat v ++ [true]))) =
      bitsNat v ++ ([1] ++ (bitsNat v ++ [1])) := fun v => by
    simp only [natBits_app, natBits_encodeNat]
    simp [natBits]
  have e2 : natBits ((List.range (m * n)).flatMap
      (fun v => encodeNat v ++ ([true] ++ (encodeNat v ++ [true])))) =
      (List.range (m * n)).flatMap (fun v => bitsNat v ++ ([1] ++ (bitsNat v ++ [1]))) := by
    simp only [natBits, List.map_flatMap]
    exact List.flatMap_congr fun v _ => hv v
  simp only [natBits_app, natBits_encodeNat, List.append_assoc, e1, e2]

end Lax117284Proofs.Machine.X1Print

end

/-! ### `Lax117284Proofs.Machine.X1Accept` -/

section
/-!
The whole of the reduction of the tractable parameters after the tokenizer has accepted: read the
counts and the parameter off the array, check the table and the parameter, and write the formula
of the case the instance is in, or the unsatisfiable one.
-/

namespace Lax117284Proofs.Machine.X1Accept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.T9Sem Lax117284Proofs.Machine.T9Print Lax117284Proofs.Machine.FreeAccept
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.T9Prog Lax117284Proofs.Machine.T9Comp1
open Lax117284Proofs.Machine.T9Accept Lax117284Proofs.Machine.X1Sem Lax117284Proofs.Machine.X1Print
open Lax117284Proofs.Machine.MisBlk (asgE condEq_true condEq_false)

variable {B : ℕ}

/-- The parameter, the scalars of the third case, and the check of the parameter. -/
def fixOk : Com :=
  .seq (.assign "kp" (.get "TK" (add (.lit 2) (V "N2"))))
  (.seq (.assign "k1" (add (V "kp") (.lit 1)))
  (.seq (.assign "CU" (add (V "C1") (V "N")))
    (.ite (.eq (V "k1") (V "m")) (.assign "ok" (.lit 1))
      (.ite (.eq (V "kp") (V "m")) (.assign "ok" (.lit 1))
        (.ite (.eq (V "kp") (.lit 0)) (.assign "ok" (.lit 1)) (.assign "ok" (.lit 0)))))))

/-- Write the satisfiable formula. -/
def printZ : Com := .seq (emitLit 1) (emitLit 0)

/-- The whole of the reduction, after the tokenizer has accepted. -/
def acceptX : Com :=
  .seq prepT (.seq fixOk (.seq okLoop (.ite (.eq (V "ok") (.lit 1))
    (.ite (.eq (V "k1") (V "m")) printT9 (.ite (.eq (V "kp") (V "m")) printU printZ))
    rejT9)))

/-- The cost of the accepting phase, on an input of `l` numbers. -/
def KaccX (Sz l : ℕ) : ℕ := KaccT Sz l + 400

lemma KaccX_mono (Sz a b : ℕ) (h : a ≤ b) : KaccX Sz a ≤ KaccX Sz b := by
  unfold KaccX
  have := KaccT_mono Sz a b h
  omega

set_option maxHeartbeats 3200000 in
/-- **The parameter and the check.** -/
theorem fixOk_run (arr : List ℕ) (σ : Env) (m n : ℕ)
    (hA : σ.arrs "TK" = arr) (hm : σ.vars "m" = m) (hn2 : σ.vars "N2" = 2 * (m * n))
    (hN : σ.vars "N" = m * n) (hC1 : σ.vars "C1" = m * n * n)
    (hlen : 3 + 2 * (m * n) ≤ arr.length) (hkp : arr.getD (2 + 2 * (m * n)) 0 + 8 < B)
    (hmB : m + 8 < B) (hCU : m * n * n + m * n + 8 < B) (hmnB : m * n + 8 < B)
    (hNB : 2 * (m * n) + 8 < B) :
    ∃ σ', Run B fixOk σ σ' 80 ∧ σ'.vars "kp" = arr.getD (2 + 2 * (m * n)) 0 ∧
      σ'.vars "k1" = arr.getD (2 + 2 * (m * n)) 0 + 1 ∧ σ'.vars "CU" = m * n * n + m * n ∧
      σ'.vars "ok" = (if arr.getD (2 + 2 * (m * n)) 0 + 1 = m ∨
        arr.getD (2 + 2 * (m * n)) 0 = m ∨ arr.getD (2 + 2 * (m * n)) 0 = 0 then 1 else 0) ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ≠ "kp" → y ≠ "k1" → y ≠ "CU" → y ≠ "ok" → σ'.vars y = σ.vars y := by
  obtain ⟨kv, hkv⟩ : ∃ kv, kv = arr.getD (2 + 2 * (m * n)) 0 := ⟨_, rfl⟩
  rw [← hkv] at hkp ⊢
  have hidx : (add (.lit 2) (V "N2")).evalB B σ = some (2 + 2 * (m * n)) := by
    have h := evalB_bin (B := B) (op := .add) (evalB_lit (B := B) (σ := σ) (n := 2) (by omega))
      (evalB_var (B := B) (x := "N2") (σ := σ) (by rw [hn2]; omega)) (by simp [hn2]; omega)
    simpa [hn2] using h
  have hev := RunStep.eval_get B σ "TK" _ (2 + 2 * (m * n)) hidx (by rw [hA]; omega)
    (by rw [hA]; rw [hkv] at hkp; omega)
  rw [hA] at hev
  have s1 : Run B (.assign "kp" (.get "TK" (add (.lit 2) (V "N2")))) σ
      (σ.setVar "kp" (arr.getD (2 + 2 * (m * n)) 0)) 10 :=
    (Run.assign hev).mono (by simp [Expr.size])
  rw [← hkv] at s1
  set σ1 := σ.setVar "kp" kv with hσ1
  have kp1 : σ1.vars "kp" = kv := by simp [hσ1, Env.setVar]
  have s2 := asgE (B := B) "k1" (add (V "kp") (.lit 1)) σ1 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.small_lit, MisBlk.den_bin,
      MisBlk.den_var, MisBlk.den_lit, Bop.apply_add, kp1]; omega)
  set σ2 := σ1.setVar "k1" (MisBlk.den σ1 (add (V "kp") (.lit 1))) with hσ2
  have k1_2 : σ2.vars "k1" = kv + 1 := by
    simp [hσ2, MisBlk.den, Env.setVar, kp1]
  have kp2 : σ2.vars "kp" = kv := by simp [hσ2, Env.setVar, kp1]
  have hC1_2 : σ2.vars "C1" = m * n * n := by simp [hσ2, hσ1, Env.setVar, hC1]
  have hN_2 : σ2.vars "N" = m * n := by simp [hσ2, hσ1, Env.setVar, hN]
  have hm_2 : σ2.vars "m" = m := by simp [hσ2, hσ1, Env.setVar, hm]
  have s3 := asgE (B := B) "CU" (add (V "C1") (V "N")) σ2 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_bin,
      MisBlk.den_var, Bop.apply_add, hC1_2, hN_2]; omega)
  set σ3 := σ2.setVar "CU" (MisBlk.den σ2 (add (V "C1") (V "N"))) with hσ3
  have CU3 : σ3.vars "CU" = m * n * n + m * n := by
    simp [hσ3, MisBlk.den, Env.setVar, hC1_2, hN_2]
  have k1_3 : σ3.vars "k1" = kv + 1 := by simp [hσ3, Env.setVar, k1_2]
  have kp3 : σ3.vars "kp" = kv := by simp [hσ3, Env.setVar, kp2]
  have hm_3 : σ3.vars "m" = m := by simp [hσ3, Env.setVar, hm_2]
  have hk1B : MisBlk.small B σ3 (V "k1") := by simp [MisBlk.small, k1_3]; omega
  have hmB' : MisBlk.small B σ3 (V "m") := by simp [MisBlk.small, hm_3]; omega
  have hkpB : MisBlk.small B σ3 (V "kp") := by simp [MisBlk.small, kp3]; omega
  have h0B : MisBlk.small B σ3 (.lit 0) := by simp [MisBlk.small]; omega
  have hA3 : σ3.arrs = σ.arrs := by simp [hσ3, hσ2, hσ1, Env.setVar]
  have hO3 : σ3.out = σ.out := by simp [hσ3, hσ2, hσ1, Env.setVar]
  have l1 := MisBlk.asgE (B := B) "ok" (.lit 1) σ3 (by simp [MisBlk.small]; omega)
  have l0 := MisBlk.asgE (B := B) "ok" (.lit 0) σ3 (by simp [MisBlk.small]; omega)
  have hfr : ∀ y, y ≠ "kp" → y ≠ "k1" → y ≠ "CU" → y ≠ "ok" →
      (σ3.setVar "ok" 0).vars y = σ.vars y ∧ (σ3.setVar "ok" 1).vars y = σ.vars y := by
    intro y a b c d
    simp [hσ3, hσ2, hσ1, Env.setVar, a, b, c, d]
  have hvals : ∀ v, (σ3.setVar "ok" v).vars "kp" = kv ∧ (σ3.setVar "ok" v).vars "k1" = kv + 1 ∧
      (σ3.setVar "ok" v).vars "CU" = m * n * n + m * n := fun v => by
    simp [Env.setVar, kp3, k1_3, CU3]
  have hAO : ∀ v, (σ3.setVar "ok" v).arrs = σ.arrs ∧ (σ3.setVar "ok" v).out = σ.out := fun v => by
    simp [Env.setVar, hA3, hO3]
  by_cases h1 : kv + 1 = m
  · have hT : (Cond.eq (V "k1") (V "m")).evalB B σ3 = some true :=
      condEq_true _ _ σ3 hk1B hmB' (by simp [MisBlk.den, k1_3, hm_3, h1])
    obtain ⟨a1, a2, a3⟩ := hvals 1
    obtain ⟨b1, b2⟩ := hAO 1
    refine ⟨_, (s1.seq (s2.seq (s3.seq (Run.ite_true hT l1)))).mono (by
      simp [Cond.size, Expr.size]), a1, a2, a3, ?_, b1, b2, fun y a b c d => (hfr y a b c d).2⟩
    simp [MisBlk.den, Env.setVar, h1]
  · have hF : (Cond.eq (V "k1") (V "m")).evalB B σ3 = some false :=
      condEq_false _ _ σ3 hk1B hmB' (by simp [MisBlk.den, k1_3, hm_3, h1])
    by_cases h2 : kv = m
    · have hT : (Cond.eq (V "kp") (V "m")).evalB B σ3 = some true :=
        condEq_true _ _ σ3 hkpB hmB' (by simp [MisBlk.den, kp3, hm_3, h2])
      obtain ⟨a1, a2, a3⟩ := hvals 1
      obtain ⟨b1, b2⟩ := hAO 1
      refine ⟨_, (s1.seq (s2.seq (s3.seq (Run.ite_false hF (Run.ite_true hT l1))))).mono (by
        simp [Cond.size, Expr.size]), a1, a2, a3, ?_, b1, b2, fun y a b c d => (hfr y a b c d).2⟩
      simp [MisBlk.den, Env.setVar, h2]
    · have hF2 : (Cond.eq (V "kp") (V "m")).evalB B σ3 = some false :=
        condEq_false _ _ σ3 hkpB hmB' (by simp [MisBlk.den, kp3, hm_3, h2])
      by_cases h3 : kv = 0
      · have hT : (Cond.eq (V "kp") (.lit 0)).evalB B σ3 = some true :=
          condEq_true _ _ σ3 hkpB h0B (by simp [MisBlk.den, kp3, h3])
        obtain ⟨a1, a2, a3⟩ := hvals 1
        obtain ⟨b1, b2⟩ := hAO 1
        refine ⟨_, (s1.seq (s2.seq (s3.seq (Run.ite_false hF (Run.ite_false hF2
          (Run.ite_true hT l1)))))).mono (by simp [Cond.size, Expr.size]), a1, a2, a3, ?_, b1, b2,
          fun y a b c d => (hfr y a b c d).2⟩
        simp [MisBlk.den, Env.setVar, h3]
      · have hF3 : (Cond.eq (V "kp") (.lit 0)).evalB B σ3 = some false :=
          condEq_false _ _ σ3 hkpB h0B (by simp [MisBlk.den, kp3, h3])
        obtain ⟨a1, a2, a3⟩ := hvals 0
        obtain ⟨b1, b2⟩ := hAO 0
        refine ⟨_, (s1.seq (s2.seq (s3.seq (Run.ite_false hF (Run.ite_false hF2
          (Run.ite_false hF3 l0)))))).mono (by simp [Cond.size, Expr.size]), a1, a2, a3, ?_, b1, b2,
          fun y a b c d => (hfr y a b c d).1⟩
        simp [MisBlk.den, Env.setVar, h1, h2, h3]

open Classical in
set_option maxHeartbeats 6400000 in
/-- **The accepting phase.** -/
theorem acceptX_run (Sz l : ℕ) (arr : List ℕ) (σ : Env)
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
    (hCU : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0 + 8 < B)
    (hl1 : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 ≤ l * l)
    (hl2 : arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 ≤ l * l)
    (hl : arr.getD 1 0 * arr.getD 0 0 ≤ l)
    (hA : σ.arrs "TK" = arr) :
    ∃ σ', Run B acceptX σ σ' (KaccX Sz l) ∧
      σ'.out = σ.out ++
        (if (∀ t < arr.getD 1 0 * arr.getD 0 0, Pass arr t) ∧
            (paramOf arr = 0 ∨ paramOf arr + 1 = arr.getD 1 0 ∨ paramOf arr = arr.getD 1 0)
          then natBits (outX arr)
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
  have hkpB : arr.getD (2 + 2 * N) 0 + 8 < B := hE _ (by omega)
  obtain ⟨σ2, r2, f2kp, f2k1, f2CU, f2ok, f2a, f2o, f2f⟩ := fixOk_run (B := B) arr σ1 m n A1 e1m
    e1N2 e1N e1C1 hlen hkpB hm0 hCU (by omega) hNB
  have A2 : σ2.arrs "TK" = arr := by rw [f2a]; exact A1
  have hpar : paramOf arr = arr.getD (2 + 2 * N) 0 := rfl
  obtain ⟨σ3, r3, e3ok, e3a, e3o, e3f⟩ := okLoop_spec (B := B) arr N
    (if paramOf arr + 1 = m ∨ paramOf arr = m ∨ paramOf arr = 0 then 1 else 0) σ2
    (fun k hk => hE k (by omega)) (by omega) (by omega) (by omega) (by split <;> omega) A2
    (by rw [f2f "N" (by decide) (by decide) (by decide) (by decide)]; exact e1N)
    (by rw [f2ok, hpar])
  have hext : (paramOf arr + 1 = m ∨ paramOf arr = m ∨ paramOf arr = 0) ↔
      (paramOf arr = 0 ∨ paramOf arr + 1 = m ∨ paramOf arr = m) := by tauto
  have A3 : σ3.arrs "TK" = arr := by rw [e3a]; exact A2
  have z : ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → y ≠ "d" → y ≠ "kp" → y ≠ "k1" → y ≠ "CU" →
      σ3.vars y = σ1.vars y := fun y a b c d e f g => by
    rw [e3f y a b c d, f2f y e f g a]
  have hcond : (σ3.vars "ok" = 1) ↔ ((∀ t < N, Pass arr t) ∧
      (paramOf arr = 0 ∨ paramOf arr + 1 = m ∨ paramOf arr = m)) := by
    rw [e3ok, flagTo_eq_one]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, hext.1 ?_⟩
      by_contra h0
      rw [if_neg h0] at h1
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [if_pos (hext.2 h2)], h1⟩
  have hokB : σ3.vars "ok" < B := by
    rw [e3ok]
    have := flagTo_le (Pass arr) (if paramOf arr + 1 = m ∨ paramOf arr = m ∨ paramOf arr = 0
      then 1 else 0) N
    omega
  have hkpv : σ3.vars "kp" = paramOf arr := by
    rw [e3f "kp" (by decide) (by decide) (by decide) (by decide), f2kp, hpar]
  have hk1v : σ3.vars "k1" = paramOf arr + 1 := by
    rw [e3f "k1" (by decide) (by decide) (by decide) (by decide), f2k1, hpar]
  have hmv : σ3.vars "m" = m := by
    rw [z "m" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      e1m]
  have hCUv : σ3.vars "CU" = m * n * n + m * n := by
    rw [e3f "CU" (by decide) (by decide) (by decide) (by decide), f2CU]
  by_cases hok : σ3.vars "ok" = 1
  · obtain ⟨hpass, hp⟩ := hcond.1 hok
    have hcondT : (Cond.eq (V "ok") (.lit 1)).evalB B σ3 = some true :=
      condEq_true _ _ σ3 (by simp [MisBlk.small]; exact hokB) (by simp [MisBlk.small]; omega)
        (by simp [MisBlk.den, hok])
    have hk1lt : σ3.vars "k1" < B := by rw [hk1v, hpar]; omega
    have hkplt : σ3.vars "kp" < B := by rw [hkpv, hpar]; omega
    have hmlt : σ3.vars "m" < B := by rw [hmv]; omega
    have hk1B : MisBlk.small B σ3 (V "k1") := hk1lt
    have hkpB' : MisBlk.small B σ3 (V "kp") := hkplt
    have hmB' : MisBlk.small B σ3 (V "m") := hmlt
    by_cases hk1 : paramOf arr + 1 = m
    · have hcond1 : (Cond.eq (V "k1") (V "m")).evalB B σ3 = some true :=
        condEq_true _ _ σ3 hk1B hmB' (by simp [MisBlk.den, hk1v, hmv, hk1])
      obtain ⟨σ4, r4, o4⟩ := printT9_run (B := B) Sz arr n m σ3 hs A3
        (by rw [z "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), e1n])
        (by rw [hmv])
        (by rw [z "nn" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), e1nn])
        (by rw [z "mm" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), e1mm])
        (by rw [z "V1" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), e1V])
        (by rw [z "CC" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), e1CC])
        (by rw [z "C1" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), e1C1])
        (by rw [z "C2" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), e1C2])
        hCC hn0 hm0 hnn hmm (by omega) (fun k hk => hE k hk) hL hlen
      have hK := KprintT_mono Sz (m * n * n) (n * m * m) (l * l) (l * l) hl1 hl2
      refine ⟨σ4, (r1.seq (r2.seq (r3.seq (Run.ite_true hcondT (Run.ite_true hcond1 r4))))).mono
        ?_, ?_⟩
      · unfold KaccX KaccT
        simp only [Cond.size, Expr.size]
        omega
      · rw [o4, e3o, f2o, e1o, if_pos ⟨hpass, hp⟩]
        congr 1
        unfold outX
        rw [if_pos hk1]
    · have hcond1 : (Cond.eq (V "k1") (V "m")).evalB B σ3 = some false :=
        condEq_false _ _ σ3 hk1B hmB' (by simp [MisBlk.den, hk1v, hmv, hk1])
      by_cases hk2 : paramOf arr = m
      · have hcond2 : (Cond.eq (V "kp") (V "m")).evalB B σ3 = some true :=
          condEq_true _ _ σ3 hkpB' hmB' (by simp [MisBlk.den, hkpv, hmv, hk2])
        obtain ⟨σ4, r4, o4⟩ := printU_run (B := B) Sz arr n m σ3 hs A3
          (by rw [z "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide), e1n])
          (by rw [z "nn" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide), e1nn])
          (by rw [z "V1" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide), e1V])
          hCUv
          (by rw [z "C1" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide), e1C1])
          (by rw [z "N" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide), e1N])
          hCU hn0 hnn (by omega) (fun k hk => hE k hk) hL hlen
        have hK := KprintT_mono Sz (m * n * n) (l * l) (l * l) (l * l) hl1 le_rfl
        have hK3 : KprintU Sz (m * n * n) (m * n) ≤ KprintT Sz (l * l) (l * l) :=
          le_trans (KprintU_le Sz (m * n * n) (m * n) (l * l) (le_trans hl (Nat.le_mul_self l))) hK
        refine ⟨σ4, (r1.seq (r2.seq (r3.seq (Run.ite_true hcondT (Run.ite_false hcond1
          (Run.ite_true hcond2 r4)))))).mono ?_, ?_⟩
        · unfold KaccX KaccT
          simp only [Cond.size, Expr.size]
          omega
        · rw [o4, e3o, f2o, e1o, if_pos ⟨hpass, hp⟩]
          congr 1
          unfold outX
          rw [if_neg hk1, if_pos hk2]
      · have hcond2 : (Cond.eq (V "kp") (V "m")).evalB B σ3 = some false :=
          condEq_false _ _ σ3 hkpB' hmB' (by simp [MisBlk.den, hkpv, hmv, hk2])
        have hp0 : paramOf arr = 0 := by
          rcases hp with h | h | h
          · exact h
          · exact absurd h hk1
          · exact absurd h hk2
        obtain ⟨σ4, r4, o4, -, -⟩ := (emitLit_spec (B := B) 1 Sz (by omega) (hs 1 (by omega))) σ3 trivial
        obtain ⟨σ5, r5, o5, -, -⟩ := (emitLit_spec (B := B) 0 Sz (by omega) (hs 0 (by omega))) σ4 trivial
        have hK := KprintT_mono Sz 0 0 (l * l) (l * l) (Nat.zero_le _) (Nat.zero_le _)
        refine ⟨σ5, (r1.seq (r2.seq (r3.seq (Run.ite_true hcondT (Run.ite_false hcond1
          (Run.ite_false hcond2 (r4.seq r5))))))).mono ?_, ?_⟩
        · unfold KaccX KaccT
          unfold KprintT at hK ⊢
          simp only [Cond.size, Expr.size]
          omega
        · rw [o5, o4, e3o, f2o, e1o, if_pos ⟨hpass, hp⟩]
          unfold outX
          rw [if_neg hk1, if_neg hk2]
          simp only [natBits_app, natBits_encodeNat, List.append_assoc]
  · have hno : ¬ ((∀ t < N, Pass arr t) ∧
        (paramOf arr = 0 ∨ paramOf arr + 1 = m ∨ paramOf arr = m)) := fun h => hok (hcond.2 h)
    obtain ⟨σ4, r4, o4⟩ := rejT9_run (B := B) Sz σ3 hs hB2
    have hcondF : (Cond.eq (V "ok") (.lit 1)).evalB B σ3 = some false :=
      condEq_false _ _ σ3 (by simp [MisBlk.small]; exact hokB) (by simp [MisBlk.small]; omega)
        (by simp [MisBlk.den, hok])
    refine ⟨σ4, (r1.seq (r2.seq (r3.seq (Run.ite_false hcondF r4)))).mono ?_, ?_⟩
    · unfold KaccX KaccT
      simp only [Cond.size, Expr.size]
      omega
    · rw [o4, e3o, f2o, e1o, if_neg hno]

end Lax117284Proofs.Machine.X1Accept

end
