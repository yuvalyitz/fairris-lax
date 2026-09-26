import Lax117284Proofs.Machine.FreeProg
import Lax117284Proofs.Machine.Flag

/-!
The two passes over the table that precede the writing: one that checks that every job takes
some time and is not due before it starts, and one that finds the largest processing time of
the first day.
-/

namespace Lax117284Proofs.Machine.FreeCheck

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Flag Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.Out

variable {B : ℕ}

/-- The test on the cell `i`: a positive processing time not exceeding the due date. -/
def okChk : Com :=
  .seq (.assign "p" (.get "TK" (add (.lit 2) (mul (.lit 2) (V "i")))))
    (.seq (.assign "d" (.get "TK" (add (add (.lit 2) (mul (.lit 2) (V "i"))) (.lit 1))))
      (.ite (.lt (.lit 0) (V "p"))
        (.ite (.lt (V "d") (V "p")) (.assign "ok" (.lit 0)) .skip)
        (.assign "ok" (.lit 0))))

def okBody : Com := .seq okChk (.assign "i" (.bin .add (V "i") (.lit 1)))

def okLoop : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "N")) okBody)

/-- The cell `t` passes the test. -/
def Pass (arr : List ℕ) (t : ℕ) : Prop :=
  0 < arr.getD (2 + 2 * t) 0 ∧ arr.getD (2 + 2 * t) 0 ≤ arr.getD (2 + 2 * t + 1) 0

instance (arr : List ℕ) : DecidablePred (Pass arr) := fun t => by unfold Pass; infer_instance

/-- The invariant of the pass over the table: the state started in `σ0`, which holds the
array. -/
structure OkInv (arr : List ℕ) (N ok0 : ℕ) (σ0 : Env) (σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vN : σ.vars "N" = N
  hi : σ.vars "i" ≤ N
  hok : σ.vars "ok" = flagTo (Pass arr) ok0 (σ.vars "i")
  fr : ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → y ≠ "d" → σ.vars y = σ0.vars y

lemma flag_fail (arr : List ℕ) (ok0 i : ℕ) (h : ¬ Pass arr i) :
    flagTo (Pass arr) ok0 (i + 1) = 0 := by
  rw [flagTo_succ]; simp [h]

lemma flag_pass (arr : List ℕ) (ok0 i : ℕ) (h : Pass arr i) (hok : ok0 ≤ 1) :
    flagTo (Pass arr) ok0 (i + 1) = flagTo (Pass arr) ok0 i := by
  rw [flagTo_succ]
  have := flagTo_le (Pass arr) ok0 i
  by_cases h1 : flagTo (Pass arr) ok0 i = 1
  · simp [h1, h]
  · have : flagTo (Pass arr) ok0 i = 0 := by omega
    simp [this]

theorem okBody_spec (arr : List ℕ) (N ok0 : ℕ) (σ0 : Env)
    (hE : ∀ k < 2 + 2 * N, arr.getD k 0 + 8 < B) (hL : 2 + 2 * N + 8 < B)
    (hN : 2 + 2 * N ≤ arr.length) (hNB : N + 8 < B) (hok0 : ok0 ≤ 1) :
    Spec B (fun σ => OkInv arr N ok0 σ0 σ ∧ σ.vars "i" < N) okBody
      (fun σ σ' => OkInv arr N ok0 σ0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  run_vcg
  all_goals (
    have hI := ‹OkInv arr N ok0 σ0 σ›
    have hlt := ‹σ.vars "i" < N›
    have hsa := hI.arrs
    have hso := hI.out
    have hA0 := hI.hA
    have hNv := hI.vN
    have hi := hI.hi
    have hok := hI.hok
    have hfr := hI.fr
    clear hI
    have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
    have h1 := hE (2 + 2 * σ.vars "i") (by omega)
    have h2 := hE (2 + 2 * σ.vars "i" + 1) (by omega)
    subst hA
    try simp only [Env.setVar] at *
    try simp at *)
  all_goals try omega
  all_goals (
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun y a b c d => ?_⟩
    · exact hsa
    · exact hso
    · exact hA0
    · simp [hNv]
    · simp; omega
    · simp
      first
        | exact (flag_fail (σ.arrs "TK") ok0 _ (by simp [Pass]; omega)).symm
        | (rw [flag_pass (σ.arrs "TK") ok0 _ (by simp [Pass]; omega) hok0, hok])
    · simp [a, b, c, d]; exact hfr y a b c d)

theorem okLoop_spec (arr : List ℕ) (N ok0 : ℕ) (σ : Env)
    (hE : ∀ k < 2 + 2 * N, arr.getD k 0 + 8 < B) (hL : 2 + 2 * N + 8 < B)
    (hN : 2 + 2 * N ≤ arr.length) (hNB : N + 8 < B) (hok0 : ok0 ≤ 1)
    (hA : σ.arrs "TK" = arr) (hNv : σ.vars "N" = N) (hok : σ.vars "ok" = ok0) :
    ∃ σ', Run B okLoop σ σ' ((40 + 4) * N + 6) ∧ σ'.vars "ok" = flagTo (Pass arr) ok0 N ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → y ≠ "d" → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := okBody) "i" "N"
    (OkInv arr N ok0 σ) N 40 (by omega) (fun _ h => h.hi) (fun _ h => h.vN)
    (okBody_spec arr N ok0 σ hE hL hN hNB hok0)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, hNv, by simp [Env.setVar], by
      simp only [Env.setVar]
      simp [flagTo_zero (Pass arr) ok0 hok0, hok], fun y a b c d => by
      simp [Env.setVar, b]⟩
  refine ⟨σ', r, ?_, hI.arrs.trans (by simp [Env.setVar]), hI.out.trans (by simp [Env.setVar]), ?_⟩
  · rw [hI.hok, hi]
  · intro y a b c d
    rw [hI.fr y a b c d]

/-! ### The largest processing time of the first day -/

def gapChk : Com :=
  .seq (.assign "p" (.get "TK" (add (.lit 2) (mul (.lit 2) (V "i")))))
    (.ite (.lt (V "g") (V "p")) (.assign "g" (V "p")) .skip)

def gapBody : Com := .seq gapChk (.assign "i" (.bin .add (V "i") (.lit 1)))

def gapLoop : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "n")) gapBody)

/-- The running maximum after `i` cells of the first day. -/
def runMax (arr : List ℕ) (i : ℕ) : ℕ :=
  (List.range i).foldl (fun g j => max g (arr.getD (2 + 2 * j) 0)) 0

lemma runMax_succ (arr : List ℕ) (i : ℕ) :
    runMax arr (i + 1) = max (runMax arr i) (arr.getD (2 + 2 * i) 0) := by
  unfold runMax
  rw [List.range_succ, List.foldl_append]
  simp

structure GapInv (B : ℕ) (arr : List ℕ) (n : ℕ) (σ0 : Env) (σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vn : σ.vars "n" = n
  hi : σ.vars "i" ≤ n
  hg : σ.vars "g" = runMax arr (σ.vars "i")
  hgB : σ.vars "g" < B
  fr : ∀ y, y ≠ "g" → y ≠ "i" → y ≠ "p" → σ.vars y = σ0.vars y

theorem gapBody_spec (arr : List ℕ) (n : ℕ) (σ0 : Env)
    (hE : ∀ k < 2 + 2 * n, arr.getD k 0 + 8 < B) (hL : 2 + 2 * n + 8 < B)
    (hn : 2 + 2 * n ≤ arr.length) (hnB : n + 8 < B) :
    Spec B (fun σ => GapInv B arr n σ0 σ ∧ σ.vars "i" < n) gapBody
      (fun σ σ' => GapInv B arr n σ0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 30 := by
  run_vcg
  all_goals (
    have hI := ‹GapInv B arr n σ0 σ›
    have hlt := ‹σ.vars "i" < n›
    have hsa := hI.arrs
    have hso := hI.out
    have hA0 := hI.hA
    have hnv := hI.vn
    have hi := hI.hi
    have hg := hI.hg
    have hgB := hI.hgB
    have hfr := hI.fr
    clear hI
    have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
    have h1 := hE (2 + 2 * σ.vars "i") (by omega)
    have hrm := runMax_succ arr (σ.vars "i")
    have hg8 : runMax arr (σ.vars "i") ≤ σ.vars "g" := by omega
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

theorem gapLoop_spec (arr : List ℕ) (n : ℕ) (σ : Env)
    (hE : ∀ k < 2 + 2 * n, arr.getD k 0 + 8 < B) (hL : 2 + 2 * n + 8 < B)
    (hn : 2 + 2 * n ≤ arr.length) (hnB : n + 8 < B)
    (hA : σ.arrs "TK" = arr) (hnv : σ.vars "n" = n) (hg0 : σ.vars "g" = 0) :
    ∃ σ', Run B gapLoop σ σ' ((30 + 4) * n + 6) ∧ σ'.vars "g" = runMax arr n ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ≠ "g" → y ≠ "i" → y ≠ "p" → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := gapBody) "i" "n"
    (GapInv B arr n σ) n 30 (by omega) (fun _ h => h.hi) (fun _ h => h.vn)
    (gapBody_spec arr n σ hE hL hn hnB)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, hnv, by simp [Env.setVar], by
      simp only [Env.setVar]
      simp [runMax, hg0], by simp [Env.setVar, hg0]; omega, fun y a b c => by
      simp [Env.setVar, b]⟩
  refine ⟨σ', r, ?_, hI.arrs.trans (by simp [Env.setVar]), hI.out.trans (by simp [Env.setVar]), ?_⟩
  · rw [hI.hg, hi]
  · intro y a b c
    rw [hI.fr y a b c]

end Lax117284Proofs.Machine.FreeCheck
