import Lax117284Proofs.Machine.T9Print
import Lax117284Proofs.Machine.X1Sem

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
