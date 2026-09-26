import Lax117284Proofs.Machine.Out
import Lax117284Proofs.Machine.FreeSem

/-!
The program that writes the reduction of Corollary 8 that adds a conflict-free day, once the
numbers of its input are in an array: the counts, the old table, the new day, the parameter.
-/

namespace Lax117284Proofs.Machine.FreeProg

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.InstSem

/-- Write the old table entry by entry. -/
def loop1 : Com := outLoop "N2" (emitTK (add (.lit 2) (V "i")))

/-- Write a cell of the new day: the processing time of the first day, and `(j + 1)` times the
gap, the gap being in the base. -/
def step2 : Com :=
  .seq (emitTK (add (.lit 2) (mul (.lit 2) (V "i"))))
    (emitVal (mul (add (V "i") (.lit 1)) (V "b3")))

def loop2 : Com := outLoop "n" step2

/-- Write the whole output. -/
def printFree : Com :=
  .seq (emitVar "n") (.seq (emitVar "m1") (.seq loop1 (.seq (.assign "b3" (V "g"))
    (.seq loop2 (emitVar "kp")))))

variable {B : ℕ}

/-- The old table is the array from position two on. -/
lemma numBits_take_drop (arr : List ℕ) (K : ℕ) (h : 2 + K ≤ arr.length) :
    numBits ((arr.drop 2).take K) = (List.range K).flatMap (fun i => bitsNat (arr.getD (2 + i) 0)) := by
  have : (arr.drop 2).take K = (List.range K).map (fun i => arr.getD (2 + i) 0) := by
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
      simp only [List.length_take, List.length_drop] at h1
      rw [List.getD_eq_getElem _ _ (by omega)]
  rw [this]
  simp only [numBits, List.flatMap_map]

lemma numBits_pairs (arr : List ℕ) (n g : ℕ) :
    numBits ((List.range n).flatMap (fun j => [arr.getD (2 + 2 * j) 0, (j + 1) * g]))
      = (List.range n).flatMap (fun j => bitsNat (arr.getD (2 + 2 * j) 0) ++ bitsNat ((j + 1) * g)) := by
  simp only [numBits, List.flatMap_assoc]
  refine List.flatMap_congr fun j _ => ?_
  simp

/-- The cost of writing the output. -/
def Kprint (Sz n N2 : ℕ) : ℕ := (96 * Sz + 200) * (N2 + n + 4)

/-- What an entry of the array must satisfy for its code to be written. -/
def Cell (B Sz : ℕ) (t : List ℕ) (k : ℕ) : Prop :=
  k < t.length ∧ k < B ∧ t.getD k 0 + 4 < B ∧ (t.getD k 0).size ≤ Sz

theorem step1_ok (Sz : ℕ) (hB : 2 < B) :
    OStep B (emitTK (add (.lit 2) (V "i"))) (fun t i _ => Cell B Sz t (2 + i))
      (fun t i _ => bitsNat (t.getD (2 + i) 0)) (1 + 3 + (48 * Sz + 50)) := by
  have := oEmitTK (B := B) (add (.lit 2) (V "i")) (fun i _ => 2 + i) Sz
    (fun t i _ => Cell B Sz t (2 + i))
    (fun σ h => by
      obtain ⟨-, h2, -⟩ := h
      exact evalB_bin (evalB_lit hB) (evalB_var (by omega)) (by simpa using h2))
    (fun t i b3 h => h)
  simpa [Expr.size] using this

theorem step2_ok (Sz : ℕ) (hB : 2 < B) :
    OStep B step2
      (fun t i b3 => Cell B Sz t (2 + 2 * i) ∧ i + 2 < B ∧ b3 < B ∧
        (i + 1) * b3 + 4 < B ∧ ((i + 1) * b3).size ≤ Sz)
      (fun t i b3 => bitsNat (t.getD (2 + 2 * i) 0) ++ bitsNat ((i + 1) * b3))
      ((1 + 5 + (48 * Sz + 50)) + (1 + 5 + (48 * Sz + 40))) := by
  have h1 := oEmitTK (B := B) (add (.lit 2) (mul (.lit 2) (V "i"))) (fun i _ => 2 + 2 * i) Sz
    (fun t i b3 => Cell B Sz t (2 + 2 * i) ∧ i + 2 < B ∧ b3 < B ∧
        (i + 1) * b3 + 4 < B ∧ ((i + 1) * b3).size ≤ Sz)
    (fun σ h => by
      obtain ⟨⟨-, h2, -⟩, h3, -⟩ := h
      exact evalB_bin (evalB_lit hB) (evalB_bin (evalB_lit hB) (evalB_var (by omega))
        (by simp; omega)) (by simp; omega))
    (fun t i b3 h => h.1)
  have h2 := oEmitVal (B := B) (mul (add (V "i") (.lit 1)) (V "b3")) (fun i b3 => (i + 1) * b3) Sz
    (fun t i b3 => Cell B Sz t (2 + 2 * i) ∧ i + 2 < B ∧ b3 < B ∧
        (i + 1) * b3 + 4 < B ∧ ((i + 1) * b3).size ≤ Sz)
    (fun σ h => by
      obtain ⟨-, h3, h4, h5, -⟩ := h
      exact evalB_bin (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
        (evalB_var h4) (by simp; omega))
    (fun t i b3 h => ⟨h.2.2.2.1, h.2.2.2.2⟩)
  have := OStep.seq h1 h2
  unfold step2
  refine OStep.weaken this (fun t i b3 h => ⟨h, h⟩) (fun t i b3 _ => rfl) ?_
  simp [Expr.size]

/-- **Writing the output.** -/
theorem printFree_run (Sz : ℕ) (arr : List ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hE : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), arr.getD k 0 + 8 < B)
    (hL : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hlen : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) ≤ arr.length)
    (hmpos : 0 < arr.getD 1 0)
    (hprod : arr.getD 0 0 * gapOf arr + 8 < B) (hgB : gapOf arr + 8 < B)
    (hN2 : 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = arr.getD 0 0)
    (hm1 : σ.vars "m1" = arr.getD 1 0 + 1)
    (hN2v : σ.vars "N2" = 2 * (arr.getD 1 0 * arr.getD 0 0)) (hg : σ.vars "g" = gapOf arr)
    (hkp : σ.vars "kp" = paramOf arr + 1) (hkpB : paramOf arr + 1 + 4 < B) :
    ∃ σ', Run B printFree σ σ'
        (Kprint Sz (arr.getD 0 0) (2 * (arr.getD 1 0 * arr.getD 0 0))) ∧
      σ'.out = σ.out ++ numBits (outFree arr) := by
  have hB2 : 2 < B := by omega
  set n := arr.getD 0 0 with hn'
  set m := arr.getD 1 0 with hm'
  set N2 := 2 * (m * n) with hN2'
  have hn0 : n + 8 < B := hE 0 (by omega)
  have hm0 : m + 8 < B := hE 1 (by omega)
  -- the count of clients
  obtain ⟨σ1, r1, o1, v1, a1⟩ := (emitVar_spec (B := B) "n" Sz) σ
    ⟨by rw [hn]; omega, by rw [hn]; exact hs _ (by omega)⟩
  have A1 : σ1.arrs "TK" = arr := by rw [a1]; exact hA
  -- the number of days plus one
  obtain ⟨σ2, r2, o2, v2, a2⟩ := (emitVar_spec (B := B) "m1" Sz) σ1
    ⟨by rw [v1 "m1" (by decide), hm1]; omega,
      by rw [v1 "m1" (by decide), hm1]; exact hs _ (by omega)⟩
  have A2 : σ2.arrs "TK" = arr := by rw [a2]; exact A1
  have z2 : ∀ x, x ∈ ["n", "m1", "N2", "g", "kp", "b3"] →
      σ2.vars x = σ.vars x := fun x hx => by
    rw [v2 x (by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      v1 x (by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  -- the old table
  obtain ⟨σ3, r3, o3, v3, a3⟩ := outLoop_spec (B := B) "N2" (emitTK (add (.lit 2) (V "i")))
    (fun t i _ => Cell B Sz t (2 + i)) (fun t i _ => bitsNat (t.getD (2 + i) 0))
    (1 + 3 + (48 * Sz + 50)) (step1_ok Sz hB2) (by decide) (by decide) N2 σ2
    (by rw [z2 "N2" (by simp), hN2v]) (by omega)
    (fun i hi => by
      rw [A2]
      have h1 : 2 + i < arr.length := by omega
      have h1' : 2 + i < 3 + 2 * (m * n) := by omega
      exact ⟨h1, by omega, by have := hE _ h1'; omega, hs _ (by have := hE _ h1'; omega)⟩)
  have A3 : σ3.arrs "TK" = arr := by rw [a3]; exact A2
  have z3 : ∀ x, x ∈ ["n", "m1", "N2", "g", "kp", "b3"] →
      σ3.vars x = σ.vars x := fun x hx => by
    rw [v3 x (by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), z2 x hx]
  -- the gap goes into the base
  have r4 : Run B (.assign "b3" (V "g")) σ3 (σ3.setVar "b3" (gapOf arr)) (1 + 1) := by
    refine Run.assign (evalB_var (by rw [z3 "g" (by simp), hg]; omega) |>.trans ?_)
    rw [z3 "g" (by simp), hg]
  set σ4 := σ3.setVar "b3" (gapOf arr) with hσ4
  have A4 : σ4.arrs "TK" = arr := by simp [hσ4, Env.setVar, A3]
  have z4 : ∀ x, x ∈ ["n", "m1", "N2", "g", "kp"] → σ4.vars x = σ.vars x := fun x hx => by
    have hxb : x ≠ "b3" := by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [hσ4, Env.setVar, if_neg hxb]
    exact z3 x (by simp at hx ⊢; tauto)
  have hb4 : σ4.vars "b3" = gapOf arr := by simp [hσ4, Env.setVar]
  -- the new day
  obtain ⟨σ5, r5, o5, v5, a5⟩ := outLoop_spec (B := B) "n" step2
    (fun t i b3 => Cell B Sz t (2 + 2 * i) ∧ i + 2 < B ∧ b3 < B ∧
        (i + 1) * b3 + 4 < B ∧ ((i + 1) * b3).size ≤ Sz)
    (fun t i b3 => bitsNat (t.getD (2 + 2 * i) 0) ++ bitsNat ((i + 1) * b3))
    ((1 + 5 + (48 * Sz + 50)) + (1 + 5 + (48 * Sz + 40))) (step2_ok Sz hB2) (by decide)
    (by decide) n σ4 (by rw [z4 "n" (by simp), hn]) (by omega)
    (fun i hi => by
      rw [A4, hb4]
      have hnm : n ≤ m * n := Nat.le_mul_of_pos_left n hmpos
      have h1 : 2 + 2 * i < arr.length := by omega
      have h1' : 2 + 2 * i < 3 + 2 * (m * n) := by omega
      have hip : (i + 1) * gapOf arr ≤ n * gapOf arr := Nat.mul_le_mul_right _ (by omega)
      exact ⟨⟨h1, by omega, by have := hE _ h1'; omega, hs _ (by have := hE _ h1'; omega)⟩,
        by omega, by omega, by omega, hs _ (by omega)⟩)
  have z5 : ∀ x, x ∈ ["kp"] → σ5.vars x = σ.vars x := fun x hx => by
    rw [v5 x (by simp at hx; rcases hx with rfl <;> decide)
      (by simp at hx; rcases hx with rfl <;> decide), z4 x (by simp at hx ⊢; tauto)]
  -- the fairness parameter
  obtain ⟨σ6, r6, o6, v6, a6⟩ := (emitVar_spec (B := B) "kp" Sz) σ5
    ⟨by rw [z5 "kp" (by simp), hkp]; omega, by rw [z5 "kp" (by simp), hkp]; exact hs _ (by omega)⟩
  refine ⟨σ6, ?_, ?_⟩
  · refine (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono ?_
    unfold Kprint
    nlinarith [Nat.zero_le Sz, Nat.zero_le N2, Nat.zero_le n]
  · have e4 : σ4.out = σ3.out := by simp [hσ4, Env.setVar]
    rw [o6, o5, e4, o3, o2, o1, z5 "kp" (by simp), hkp, A2, A4, hb4, v1 "m1" (by decide), hm1]
    unfold outFree
    have hl2 : 2 + N2 ≤ arr.length := by omega
    simp only [numBits_append, numBits_cons, numBits_nil, List.append_nil]
    rw [numBits_take_drop arr N2 hl2, numBits_pairs]
    simp only [List.append_assoc, hn']
    rw [hn]

end Lax117284Proofs.Machine.FreeProg
