import Lax117284Proofs.Machine.FreeCheck
import Lax117284Proofs.Machine.PerSem

/-!
The pass over the parameters that checks that none of them exceeds the number of days.
-/

namespace Lax117284Proofs.Machine.PerCheck

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Flag Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.PerSem

variable {B : ℕ}

/-- The test on parameter `i`. -/
def parChk : Com :=
  .seq (.assign "p" (.get "TK" (add (add (.lit 2) (V "N2")) (V "i"))))
    (.ite (.lt (V "m") (V "p")) (.assign "ok" (.lit 0)) .skip)

def parBody : Com := .seq parChk (.assign "i" (.bin .add (V "i") (.lit 1)))

def parLoop : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "n")) parBody)

/-- Parameter `j` does not exceed `m`. -/
def PassK (arr : List ℕ) (m N2 j : ℕ) : Prop := arr.getD (2 + N2 + j) 0 ≤ m

instance (arr : List ℕ) (m N2 : ℕ) : DecidablePred (PassK arr m N2) := fun j => by
  unfold PassK; infer_instance

lemma flagK_fail (arr : List ℕ) (m N2 ok0 i : ℕ) (h : ¬ PassK arr m N2 i) :
    flagTo (PassK arr m N2) ok0 (i + 1) = 0 := by
  rw [flagTo_succ]; simp [h]

lemma flagK_pass (arr : List ℕ) (m N2 ok0 i : ℕ) (h : PassK arr m N2 i) (hok : ok0 ≤ 1) :
    flagTo (PassK arr m N2) ok0 (i + 1) = flagTo (PassK arr m N2) ok0 i := by
  rw [flagTo_succ]
  have := flagTo_le (PassK arr m N2) ok0 i
  by_cases h1 : flagTo (PassK arr m N2) ok0 i = 1
  · simp [h1, h]
  · have : flagTo (PassK arr m N2) ok0 i = 0 := by omega
    simp [this]

structure ParInv (arr : List ℕ) (n m N2 ok0 : ℕ) (σ0 σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vn : σ.vars "n" = n
  vm : σ.vars "m" = m
  vN2 : σ.vars "N2" = N2
  hi : σ.vars "i" ≤ n
  hok : σ.vars "ok" = flagTo (PassK arr m N2) ok0 (σ.vars "i")
  fr : ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → σ.vars y = σ0.vars y

theorem parBody_spec (arr : List ℕ) (n m N2 ok0 : ℕ) (σ0 : Env)
    (hE : ∀ k < 2 + N2 + n, arr.getD k 0 + 8 < B) (hL : 2 + N2 + n + 8 < B)
    (hN : 2 + N2 + n ≤ arr.length) (hnB : n + 8 < B) (hmB : m + 8 < B) (hok0 : ok0 ≤ 1) :
    Spec B (fun σ => ParInv arr n m N2 ok0 σ0 σ ∧ σ.vars "i" < n) parBody
      (fun σ σ' => ParInv arr n m N2 ok0 σ0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  run_vcg
  all_goals (
    have hI := ‹ParInv arr n m N2 ok0 σ0 σ›
    have hlt := ‹σ.vars "i" < n›
    have hsa := hI.arrs
    have hso := hI.out
    have hA0 := hI.hA
    have hnv := hI.vn
    have hmv := hI.vm
    have hN2 := hI.vN2
    have hi := hI.hi
    have hok := hI.hok
    have hfr := hI.fr
    clear hI
    have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
    have h1 := hE (2 + σ.vars "N2" + σ.vars "i") (by omega)
    have hN2r : N2 = σ.vars "N2" := hN2.symm
    subst hA
    try simp only [Env.setVar] at *
    try simp at *)
  all_goals try omega
  all_goals (
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun y a b c => ?_⟩
    · exact hsa
    · exact hso
    · exact hA0
    · simp [hnv]
    · simp [hmv]
    · simp [hN2]
    · simp; omega
    · simp
      first
        | exact (flagK_fail (σ.arrs "TK") m N2 ok0 _ (by simp [PassK, hN2r]; omega)).symm
        | (rw [flagK_pass (σ.arrs "TK") m N2 ok0 _ (by simp [PassK, hN2r]; omega) hok0, hok])
    · simp [a, b, c]; exact hfr y a b c)

theorem parLoop_spec (arr : List ℕ) (n m N2 ok0 : ℕ) (σ : Env)
    (hE : ∀ k < 2 + N2 + n, arr.getD k 0 + 8 < B) (hL : 2 + N2 + n + 8 < B)
    (hN : 2 + N2 + n ≤ arr.length) (hnB : n + 8 < B) (hmB : m + 8 < B) (hok0 : ok0 ≤ 1)
    (hA : σ.arrs "TK" = arr) (hnv : σ.vars "n" = n) (hmv : σ.vars "m" = m)
    (hN2 : σ.vars "N2" = N2) (hok : σ.vars "ok" = ok0) :
    ∃ σ', Run B parLoop σ σ' ((40 + 4) * n + 6) ∧
      σ'.vars "ok" = flagTo (PassK arr m N2) ok0 n ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := parBody) "i" "n"
    (ParInv arr n m N2 ok0 σ) n 40 (by omega) (fun _ h => h.hi) (fun _ h => h.vn)
    (parBody_spec arr n m N2 ok0 σ hE hL hN hnB hmB hok0)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, hnv, hmv, hN2, by simp [Env.setVar], by
      simp only [Env.setVar]
      simp [flagTo_zero (PassK arr m N2) ok0 hok0, hok], fun y a b c => by
      simp [Env.setVar, b]⟩
  refine ⟨σ', r, ?_, hI.arrs.trans (by simp [Env.setVar]), hI.out.trans (by simp [Env.setVar]), ?_⟩
  · rw [hI.hok, hi]
  · intro y a b c
    rw [hI.fr y a b c]

end Lax117284Proofs.Machine.PerCheck
