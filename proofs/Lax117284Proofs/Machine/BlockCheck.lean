import Lax117284Proofs.Machine.FreeCheck
import Lax117284Proofs.Machine.BlockSem

/-!
The pass over the table that finds the largest due date.
-/

namespace Lax117284Proofs.Machine.BlockCheck

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.BlockSem

variable {B : ℕ}

def dmaxChk : Com :=
  .seq (.assign "p" (.get "TK" (add (add (.lit 2) (mul (.lit 2) (V "i"))) (.lit 1))))
    (.ite (.lt (V "g") (V "p")) (.assign "g" (V "p")) .skip)

def dmaxBody : Com := .seq dmaxChk (.assign "i" (.bin .add (V "i") (.lit 1)))

def dmaxLoop : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "N")) dmaxBody)

/-- The running maximum of the due dates after `i` cells. -/
def runMaxD (arr : List ℕ) (i : ℕ) : ℕ :=
  (List.range i).foldl (fun g j => max g (arr.getD (2 + 2 * j + 1) 0)) 0

lemma runMaxD_succ (arr : List ℕ) (i : ℕ) :
    runMaxD arr (i + 1) = max (runMaxD arr i) (arr.getD (2 + 2 * i + 1) 0) := by
  unfold runMaxD
  rw [List.range_succ, List.foldl_append]
  simp

structure DInv (B : ℕ) (arr : List ℕ) (N : ℕ) (σ0 : Env) (σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vN : σ.vars "N" = N
  hi : σ.vars "i" ≤ N
  hg : σ.vars "g" = runMaxD arr (σ.vars "i")
  hgB : σ.vars "g" < B
  fr : ∀ y, y ≠ "g" → y ≠ "i" → y ≠ "p" → σ.vars y = σ0.vars y

theorem dmaxBody_spec (arr : List ℕ) (N : ℕ) (σ0 : Env)
    (hE : ∀ k < 2 + 2 * N, arr.getD k 0 + 8 < B) (hL : 2 + 2 * N + 8 < B)
    (hn : 2 + 2 * N ≤ arr.length) (hnB : N + 8 < B) :
    Spec B (fun σ => DInv B arr N σ0 σ ∧ σ.vars "i" < N) dmaxBody
      (fun σ σ' => DInv B arr N σ0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  run_vcg
  all_goals (
    have hI := ‹DInv B arr N σ0 σ›
    have hlt := ‹σ.vars "i" < N›
    have hA0 := hI.hA
    have hgB := hI.hgB
    obtain ⟨hsa, hso, -, hnv, hi, hg, -, hfr⟩ := hI
    have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
    have h1 := hE (2 + 2 * σ.vars "i" + 1) (by omega)
    have hrm := runMaxD_succ arr (σ.vars "i")
    have hg8 : runMaxD arr (σ.vars "i") ≤ σ.vars "g" := by omega
    subst hA
    try simp only [Env.setVar] at *
    try simp at *)
  all_goals try omega
  all_goals (
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun y a b c => ?_⟩
    · exact hsa
    · exact hso
    · exact hA0
    · simp [hnv]
    · simp; omega
    · simp only [Env.setVar]
      simp [hrm, max_def]
      first | omega | (split_ifs <;> omega) | (intro h; omega)
    · simp; omega
    · simp [a, b, c]; exact hfr y a b c)

theorem dmaxLoop_spec (arr : List ℕ) (N : ℕ) (σ : Env)
    (hE : ∀ k < 2 + 2 * N, arr.getD k 0 + 8 < B) (hL : 2 + 2 * N + 8 < B)
    (hn : 2 + 2 * N ≤ arr.length) (hnB : N + 8 < B)
    (hA : σ.arrs "TK" = arr) (hnv : σ.vars "N" = N) (hg0 : σ.vars "g" = 0) :
    ∃ σ', Run B dmaxLoop σ σ' ((40 + 4) * N + 6) ∧ σ'.vars "g" = runMaxD arr N ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ≠ "g" → y ≠ "i" → y ≠ "p" → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := dmaxBody) "i" "N"
    (DInv B arr N σ) N 40 (by omega) (fun _ h => h.hi) (fun _ h => h.vN)
    (dmaxBody_spec arr N σ hE hL hn hnB)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, hnv, by simp [Env.setVar], by
      simp only [Env.setVar]
      simp [runMaxD, hg0], by simp [Env.setVar, hg0]; omega, fun y a b c => by
      simp [Env.setVar, b]⟩
  refine ⟨σ', r, ?_, hI.arrs.trans (by simp [Env.setVar]), hI.out.trans (by simp [Env.setVar]), ?_⟩
  · rw [hI.hg, hi]
  · intro y a b c
    rw [hI.fr y a b c]

end Lax117284Proofs.Machine.BlockCheck
