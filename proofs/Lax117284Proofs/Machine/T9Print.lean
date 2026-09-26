import Lax117284Proofs.Machine.T9Prog

/-!
Writing the whole formula of Theorem 9: the two counts, then the loop over the conflict clauses and
the loop over the validation clauses.
-/

namespace Lax117284Proofs.Machine.T9Print

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.T9Sem
open Lax117284Proofs.Machine.InstSem Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Machine.T9Comp1 Lax117284Proofs.Machine.T9Comp2 Lax117284Proofs.Machine.T9Prog

variable {B : ℕ}

/-- **The loop over the conflict clauses.** -/
theorem cl1Loop_run (Sz : ℕ) (arr : List ℕ) (n m : ℕ) (σ0 : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ0.arrs "TK" = arr) (hn : σ0.vars "n" = n) (hnn : σ0.vars "nn" = n * n)
    (hC : σ0.vars "C1" = m * n * n) (hCB : m * n * n + 8 < B) (hnB : n + 8 < B)
    (hnnB : n * n + 8 < B) (hmnB : m * n + 8 < B)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 + 8 < B) (hL : 3 + 2 * (m * n) + 8 < B)
    (hlen : 3 + 2 * (m * n) ≤ arr.length) :
    ∃ σ', Run B (outLoop "C1" body1) σ0 σ' ((K1 Sz + 10 + 4) * (m * n * n) + 6) ∧
      σ'.out = σ0.out ++ (List.range (m * n * n)).flatMap (clB arr n m) ∧
      (∀ y ∉ "i" :: S9, σ'.vars y = σ0.vars y) ∧ σ'.arrs = σ0.arrs := by
  obtain ⟨σ', r, o, hAg⟩ := eLoop (B := B) "C1" body1 ("i" :: S9) (clB arr n m) (K1 Sz)
    (m * n * n) σ0 (by simp) (by decide) hC (by omega) (by
      intro σ hAg hlt
      have hA' : σ.arrs "TK" = arr := by rw [hAg.1]; exact hA
      have hn' : σ.vars "n" = n := by rw [hAg.2 "n" (by decide)]; exact hn
      have hnn' : σ.vars "nn" = n * n := by rw [hAg.2 "nn" (by decide)]; exact hnn
      obtain ⟨σ1, r1, o1, v1, a1⟩ := body1_run (B := B) Sz arr n m (σ.vars "i") σ hs hA' rfl hn'
        hnn' hlt (by omega) hnB hnnB hmnB hE hL hlen
      refine ⟨σ1, r1, o1, ⟨a1.trans hAg.1, fun y hy => ?_⟩, ?_⟩
      · have hy' : y ∉ S9 := fun h => hy (List.mem_cons_of_mem _ h)
        rw [v1 y hy', hAg.2 y hy]
      · exact v1 "i" (by decide))
  exact ⟨σ', r, o, hAg.2, hAg.1⟩

/-- **The loop over the validation clauses.** -/
theorem cl2Loop_run (Sz : ℕ) (n m : ℕ) (σ0 : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hn : σ0.vars "n" = n) (hm : σ0.vars "m" = m) (hmm : σ0.vars "mm" = m * m)
    (hC : σ0.vars "C2" = n * m * m) (hCB : n * m * m + 8 < B) (hmB : m + 8 < B)
    (hmmB : m * m + 8 < B) (hmnB : m * n + 8 < B) (arr : List ℕ) :
    ∃ σ', Run B (outLoop "C2" body2) σ0 σ' ((K1 Sz + 10 + 4) * (n * m * m) + 6) ∧
      σ'.out = σ0.out ++ (List.range (n * m * m)).flatMap (fun c => clB arr n m (m * n * n + c)) ∧
      (∀ y ∉ "i" :: S9, σ'.vars y = σ0.vars y) ∧ σ'.arrs = σ0.arrs := by
  obtain ⟨σ', r, o, hAg⟩ := eLoop (B := B) "C2" body2 ("i" :: S9)
    (fun c => clB arr n m (m * n * n + c)) (K1 Sz) (n * m * m) σ0 (by simp) (by decide) hC
    (by omega) (by
      intro σ hAg hlt
      have hn' : σ.vars "n" = n := by rw [hAg.2 "n" (by decide)]; exact hn
      have hm' : σ.vars "m" = m := by rw [hAg.2 "m" (by decide)]; exact hm
      have hmm' : σ.vars "mm" = m * m := by rw [hAg.2 "mm" (by decide)]; exact hmm
      obtain ⟨σ1, r1, o1, v1, a1⟩ := body2_run (B := B) Sz arr n m (σ.vars "i") σ hs rfl hn' hm'
        hmm' hlt (by omega) hmB hmmB hmnB
      refine ⟨σ1, r1, o1, ⟨a1.trans hAg.1, fun y hy => ?_⟩, ?_⟩
      · have hy' : y ∉ S9 := fun h => hy (List.mem_cons_of_mem _ h)
        rw [v1 y hy', hAg.2 y hy]
      · exact v1 "i" (by decide))
  exact ⟨σ', r, o, hAg.2, hAg.1⟩

/-- Write the whole formula. -/
def printT9 : Com :=
  .seq (emitVar "V1") (.seq (emitVar "CC")
    (.seq (outLoop "C1" body1) (outLoop "C2" body2)))

/-- The cost of writing the formula. -/
def KprintT (Sz C1 C2 : ℕ) : ℕ :=
  2 * (48 * Sz + 50) + ((K1 Sz + 10 + 4) * C1 + 6) + ((K1 Sz + 10 + 4) * C2 + 6)

/-- **Writing the formula.** -/
theorem printT9_run (Sz : ℕ) (arr : List ℕ) (n m : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hm : σ.vars "m" = m)
    (hnn : σ.vars "nn" = n * n) (hmm : σ.vars "mm" = m * m)
    (hV : σ.vars "V1" = m * n + 1) (hCC : σ.vars "CC" = m * n * n + n * m * m)
    (hC1 : σ.vars "C1" = m * n * n) (hC2 : σ.vars "C2" = n * m * m)
    (hCCB : m * n * n + n * m * m + 8 < B) (hnB : n + 8 < B) (hmB : m + 8 < B)
    (hnnB : n * n + 8 < B) (hmmB : m * m + 8 < B) (hmnB : m * n + 8 < B)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 + 8 < B) (hL : 3 + 2 * (m * n) + 8 < B)
    (hlen : 3 + 2 * (m * n) ≤ arr.length) :
    ∃ σ', Run B printT9 σ σ' (KprintT Sz (m * n * n) (n * m * m)) ∧
      σ'.out = σ.out ++ natBits (outT9 arr n m) := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "V1" Sz σ
    ⟨by rw [hV]; omega, by rw [hV]; exact hs _ (by omega)⟩
  have z1 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ1.vars y = σ.vars y := v1
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitVar_spec (B := B) "CC" Sz σ1
    ⟨by rw [v1 "CC" (by decide), hCC]; omega,
      by rw [v1 "CC" (by decide), hCC]; exact hs _ (by omega)⟩
  have z2 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ2.vars y = σ.vars y := fun y hy => by
    rw [v2 y hy, v1 y hy]
  have A2 : σ2.arrs "TK" = arr := by rw [a2, a1]; exact hA
  have hC1B : m * n * n + 8 < B := by omega
  have hC2B : n * m * m + 8 < B := by omega
  obtain ⟨σ3, r3, o3, v3, a3⟩ := cl1Loop_run (B := B) Sz arr n m σ2 hs A2
    (by rw [z2 "n" (by decide)]; exact hn) (by rw [z2 "nn" (by decide)]; exact hnn)
    (by rw [z2 "C1" (by decide)]; exact hC1) hC1B hnB hnnB hmnB hE hL hlen
  have z3 : ∀ y, y ∉ "i" :: S9 → σ3.vars y = σ.vars y := fun y hy => by
    rw [v3 y hy]; exact z2 y (fun h => hy (List.mem_cons_of_mem _ (by
      simp only [S9, SCR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      tauto)))
  obtain ⟨σ4, r4, o4, v4, a4⟩ := cl2Loop_run (B := B) Sz n m σ3 hs
    (by rw [z3 "n" (by decide)]; exact hn) (by rw [z3 "m" (by decide)]; exact hm)
    (by rw [z3 "mm" (by decide)]; exact hmm) (by rw [z3 "C2" (by decide)]; exact hC2) hC2B hmB
    hmmB hmnB arr
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by unfold KprintT; omega), ?_⟩
  rw [o4, o3, o2, o1, z1 "CC" (by decide), hCC, hV]
  unfold outT9
  have hrange : List.range (m * n * n + n * m * m) = List.range (m * n * n) ++
      (List.range (n * m * m)).map (fun c => m * n * n + c) := List.range_add ..
  have e1 : natBits ((List.range (m * n * n)).flatMap (clW arr n m)) =
      (List.range (m * n * n)).flatMap (clB arr n m) := by
    simp only [natBits, List.map_flatMap]
    exact List.flatMap_congr fun c _ => natBits_clW arr n m c
  have e2 : natBits ((List.range (n * m * m)).flatMap (fun c => clW arr n m (m * n * n + c))) =
      (List.range (n * m * m)).flatMap (fun c => clB arr n m (m * n * n + c)) := by
    simp only [natBits, List.map_flatMap]
    exact List.flatMap_congr fun c _ => natBits_clW arr n m (m * n * n + c)
  rw [hrange, List.flatMap_append, List.flatMap_map]
  simp only [natBits_app, natBits_encodeNat, List.append_assoc, Function.comp_def]
  rw [e1, e2]

end Lax117284Proofs.Machine.T9Print
