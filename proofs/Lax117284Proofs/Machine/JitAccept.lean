import Lax117284Proofs.Machine.JitPrint
import Lax117284Proofs.Machine.FreeAccept

/-!
The whole of the reduction of Theorem 11 after the tokenizer has accepted: read the counts off the
array, check the table, and write either the image or the rejected word.
-/

namespace Lax117284Proofs.Machine.JitAccept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.JitSem Lax117284Proofs.Machine.JitCheck Lax117284Proofs.Machine.JitPass
open Lax117284Proofs.Machine.JitPrint Lax117284Proofs.Machine.FreeAccept

variable {B : ℕ}

/-- The numbers of the image, read off an array. -/
def outJG (arr : List ℕ) (n m : ℕ) : List ℕ :=
  [n, m] ++ (List.range (m * n)).flatMap
    (fun t => [arr.getD (2 + n + t) 0, arr.getD (2 + (t - t / n * n)) 0]) ++ [1]

/-- **A loop over the cells.** -/
theorem cellLoopJ_run (Sz : ℕ) (arr : List ℕ) (n m : ℕ) (σ0 : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hA : σ0.arrs "TK" = arr)
    (hn : σ0.vars "n" = n) (ho : σ0.vars "o" = 2 + n) (hN : σ0.vars "N" = m * n)
    (hE : ∀ k < 2 + n + m * n, arr.getD k 0 + 8 < B) (hL : 2 + n + m * n + 8 < B)
    (hlen : 2 + n + m * n ≤ arr.length) (hnB : n + 8 < B) :
    ∃ σ', Run B (outLoop "N" cellPrint) σ0 σ' ((KcellJ Sz + 10 + 4) * (m * n) + 6) ∧
      σ'.out = σ0.out ++ numBits ((List.range (m * n)).flatMap
        (fun t => [arr.getD (2 + n + t) 0, arr.getD (2 + (t - t / n * n)) 0])) ∧
      (∀ y ∉ "i" :: SJ, σ'.vars y = σ0.vars y) ∧ σ'.arrs = σ0.arrs := by
  obtain ⟨σ', r, o, hAg⟩ := eLoop (B := B) "N" cellPrint ("i" :: SJ)
    (fun t => bitsNat (arr.getD (2 + n + t) 0) ++ bitsNat (arr.getD (2 + (t - t / n * n)) 0))
    (KcellJ Sz) (m * n) σ0 (by simp) (by decide) hN (by omega) (by
      intro σ hAg hlt
      have hA' : σ.arrs "TK" = arr := by rw [hAg.1]; exact hA
      have hn' : σ.vars "n" = n := by rw [hAg.2 "n" (by decide)]; exact hn
      have ho' : σ.vars "o" = 2 + n := by rw [hAg.2 "o" (by decide)]; exact ho
      have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h => by rw [h] at hlt; simp at hlt)
      have hnm : n ≤ m * n := Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero (fun h => by
        rw [h] at hlt; simp at hlt))
      have hq : σ.vars "i" / n * n ≤ σ.vars "i" := Nat.div_mul_le_self _ _
      have hdiv2 : σ.vars "i" - σ.vars "i" / n * n < n := by
        have := Nat.mod_lt (σ.vars "i") hn0
        have := Nat.mod_def (σ.vars "i") n
        have e : σ.vars "i" / n * n = n * (σ.vars "i" / n) := Nat.mul_comm _ _
        omega
      have hp := hE (2 + n + σ.vars "i") (by omega)
      have hd := hE (2 + (σ.vars "i" - σ.vars "i" / n * n)) (by omega)
      obtain ⟨σ1, r1, o1, v1, a1⟩ := cellPrint_run (B := B) Sz arr n (2 + n) (σ.vars "i") σ hs hA'
        rfl hn' ho' hn0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      refine ⟨σ1, r1, o1, ⟨a1.trans hAg.1, fun y hy => ?_⟩, ?_⟩
      · have hy' : y ∉ SJ := fun h => hy (List.mem_cons_of_mem _ h)
        rw [v1 y hy', hAg.2 y hy]
      · exact v1 "i" (by decide))
  refine ⟨σ', r, ?_, hAg.2, hAg.1⟩
  rw [o]
  congr 1
  simp only [numBits, List.flatMap_assoc]
  refine List.flatMap_congr fun t _ => ?_
  simp [numBits]


/-- Write the whole image. -/
def printJ : Com :=
  .seq (emitVar "n") (.seq (emitVar "m") (.seq (outLoop "N" cellPrint) (emitLit 1)))

/-- The cost of writing the image. -/
def KprintJ (Sz N : ℕ) : ℕ := 3 * (48 * Sz + 50) + (KcellJ Sz + 10 + 4) * N + 6

/-- **Writing the image.** -/
theorem printJ_run (Sz : ℕ) (arr : List ℕ) (n m : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hA : σ.arrs "TK" = arr)
    (hn : σ.vars "n" = n) (hm : σ.vars "m" = m) (ho : σ.vars "o" = 2 + n)
    (hN : σ.vars "N" = m * n)
    (hE : ∀ k < 2 + n + m * n, arr.getD k 0 + 8 < B) (hL : 2 + n + m * n + 8 < B)
    (hlen : 2 + n + m * n ≤ arr.length) (hnB : n + 8 < B) (hmB : m + 8 < B) :
    ∃ σ', Run B printJ σ σ' (KprintJ Sz (m * n)) ∧
      σ'.out = σ.out ++ numBits (outJG arr n m) := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "n" Sz σ
    ⟨by rw [hn]; omega, by rw [hn]; exact hs _ (by omega)⟩
  have z1 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ1.vars y = σ.vars y := v1
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitVar_spec (B := B) "m" Sz σ1
    ⟨by rw [v1 "m" (by decide), hm]; omega,
      by rw [v1 "m" (by decide), hm]; exact hs _ (by omega)⟩
  have z2 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ2.vars y = σ.vars y := fun y hy => by
    rw [v2 y hy, v1 y hy]
  have A2 : σ2.arrs "TK" = arr := by rw [a2, a1]; exact hA
  obtain ⟨σ3, r3, o3, v3, a3⟩ := cellLoopJ_run (B := B) Sz arr n m σ2 hs A2
    (by rw [z2 "n" (by decide)]; exact hn) (by rw [z2 "o" (by decide)]; exact ho)
    (by rw [z2 "N" (by decide)]; exact hN) hE hL hlen hnB
  obtain ⟨σ4, r4, o4, v4, a4⟩ := (emitLit_spec (B := B) 1 Sz (by omega) (hs _ (by omega))) σ3 trivial
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by unfold KprintJ; omega), ?_⟩
  rw [o4, o3, o2, o1, z1 "m" (by decide), hm, hn]
  unfold outJG
  simp only [numBits_append, numBits_cons, numBits_nil, List.append_nil, List.append_assoc]

/-- Read the counts off the array. -/
def prepJ : Com :=
  .seq (.assign "n" (.get "TK" (.lit 0)))
  (.seq (.assign "m" (.get "TK" (.lit 1)))
  (.seq (.assign "N" (mul (V "m") (V "n")))
  (.seq (.assign "o" (add (.lit 2) (V "n")))
    (.assign "ok" (.lit 1)))))

theorem prepJ_spec (arr : List ℕ)
    (hE : ∀ k < 2 + arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0, arr.getD k 0 + 8 < B)
    (hL : 2 + arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0 + 8 < B) (hlen : 2 ≤ arr.length) :
    Spec B (fun σ => σ.arrs "TK" = arr) prepJ
      (fun σ σ' => σ'.vars "n" = arr.getD 0 0 ∧ σ'.vars "m" = arr.getD 1 0 ∧
        σ'.vars "N" = arr.getD 1 0 * arr.getD 0 0 ∧ σ'.vars "o" = 2 + arr.getD 0 0 ∧
        σ'.vars "ok" = 1 ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        ∀ y, y ≠ "n" → y ≠ "m" → y ≠ "N" → y ≠ "o" → y ≠ "ok" → σ'.vars y = σ.vars y) 40 := by
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
    intro y a b c d e
    simp [a, b, c, d, e])

/-- The whole of the reduction, after the tokenizer has accepted. -/
def acceptJ : Com :=
  .seq prepJ (.seq jokLoop (.ite (.eq (V "ok") (.lit 1)) printJ rejectPrint))

/-- The cost of the accepting phase, on an input of `l` numbers. -/
def KaccJ (Sz l : ℕ) : ℕ := 200 + 84 * l + KprintJ Sz l + 3 * (48 * Sz + 50)

lemma KaccJ_mono (Sz a b : ℕ) (h : a ≤ b) : KaccJ Sz a ≤ KaccJ Sz b := by
  unfold KaccJ KprintJ
  have := Nat.mul_le_mul_left (KcellJ Sz + 10 + 4) h
  omega

theorem acceptJ_run (Sz l : ℕ) (arr : List ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hE : ∀ k < 2 + arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0, arr.getD k 0 + 8 < B)
    (hL : 2 + arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0 + 8 < B)
    (hlen : 2 + arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0 ≤ arr.length)
    (hl : arr.getD 1 0 * arr.getD 0 0 ≤ l) (hA : σ.arrs "TK" = arr) :
    ∃ σ', Run B acceptJ σ σ' (KaccJ Sz l) ∧
      σ'.out = σ.out ++
        (if ∀ t < arr.getD 1 0 * arr.getD 0 0, PassJ arr (arr.getD 0 0) t
          then numBits (outJG arr (arr.getD 0 0) (arr.getD 1 0)) else numBits [1, 0, 1]) := by
  set n := arr.getD 0 0 with hn'
  set m := arr.getD 1 0 with hm'
  have hB2 : 6 < B := by omega
  have hnB : n + 8 < B := hE 0 (by omega)
  have hmB : m + 8 < B := hE 1 (by omega)
  obtain ⟨σ1, r1, e1n, e1m, e1N, e1o, e1ok, e1a, e1o', e1f⟩ :=
    (prepJ_spec (B := B) arr hE hL (by omega)) σ hA
  have A1 : σ1.arrs "TK" = arr := by rw [e1a]; exact hA
  obtain ⟨σ2, r2, e2ok, e2a, e2o, e2f⟩ := jokLoop_spec (B := B) arr m n 1 σ1 e1n e1o hE hL hlen hnB
    le_rfl A1 e1N e1ok
  have A2 : σ2.arrs "TK" = arr := by rw [e2a]; exact A1
  have hokB : σ2.vars "ok" < B := by
    rw [e2ok]; have := flagTo_le (PassJ arr n) 1 (m * n); omega
  have hcond : (σ2.vars "ok" = 1) ↔ ∀ t < m * n, PassJ arr n t := by
    rw [e2ok, flagTo_eq_one]
    exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  by_cases hok : σ2.vars "ok" = 1
  · have hpass := hcond.1 hok
    have hcondT : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some true := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    obtain ⟨σ3, r3, o3⟩ := printJ_run (B := B) Sz arr n m σ2 hs A2
      (by rw [e2f "n" (by simp [AJ, AI]), e1n])
      (by rw [e2f "m" (by simp [AJ, AI]), e1m])
      (by rw [e2f "o" (by simp [AJ, AI]), e1o])
      (by rw [e2f "N" (by simp [AJ, AI]), e1N]) hE hL hlen hnB hmB
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_true hcondT r3))).mono ?_, ?_⟩
    · unfold KaccJ
      simp only [Cond.size, Expr.size]
      have : KprintJ Sz (m * n) ≤ KprintJ Sz l := by
        unfold KprintJ
        have := Nat.mul_le_mul_left (KcellJ Sz + 10 + 4) hl
        omega
      omega
    · rw [o3, e2o, e1o', if_pos hpass]
  · have hno : ¬ ∀ t < m * n, PassJ arr n t := fun h => hok (hcond.2 h)
    obtain ⟨σ3, r3, e3o, e3a, e3f⟩ := rejectPrint_run (B := B) Sz σ2 hs hB2
    have hcondF : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some false := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_false hcondF r3))).mono ?_, ?_⟩
    · unfold KaccJ
      simp only [Cond.size, Expr.size]
      omega
    · rw [e3o, e2o, e1o', if_neg hno]

end Lax117284Proofs.Machine.JitAccept
