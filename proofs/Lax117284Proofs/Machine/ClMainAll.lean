import Lax117284Proofs.Machine.ClMainBr

/-!
The main program, whole: read the word, test its length, then either build the integer program and
run the oracle on it, or brute-force.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846.Ram
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff code simCom SV SA Pre0 HypS simCom_spec Bnd)
open Lax117284Proofs.Machine.ClBuild
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The main program. -/
def mainCom (P : Program) (c1 : ℕ) : Com :=
  .seq readCom (.seq critCom (.ite (.lt (lit 0) (V "fit")) (fitBranch P c1) bruteBranch))

variable {B k c1 : ℕ} {I : Instance} {x : List ℕ} {P : Program}

/-- The machine's start: the input, an empty output, the arrays of the declared lengths. -/
def M0 (P : Program) (c1 : ℕ) (x : List ℕ) (σ : Env) : Prop :=
  σ.inp = x ∧ σ.out = [] ∧ ∀ a, σ.arrs a = List.replicate (extF P c1 x a) 0

/-- After the reading and the test. -/
def R2 (P : Program) (c1 : ℕ) (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  F0 P c1 I x k σ ∧ σ.vars "L" = x.length ∧
    σ.vars "fit" = if Q I.clients + 2 ≤ x.length then 1 else 0

theorem critCom_frame : (∀ y, y ∉ ["fit", "E", "cp", "ci"] → y ∉ critCom.wvars) ∧
    (∀ a, a ∉ critCom.warrs) ∧ ¬ critCom.reads ∧ critCom.NoWrite := by
  refine ⟨fun y hy h => ?_, fun a h => ?_, ?_, ?_⟩
  · simp [critCom, critFit, critLoop, critStep, Com.wvars, seqs, asg] at h hy
    tauto
  · simp [critCom, critFit, critLoop, critStep, Com.warrs, seqs, asg] at h
  · simp [critCom, critFit, critLoop, critStep, Com.reads, seqs, asg]
  · simp [critCom, critFit, critLoop, critStep, Com.NoWrite, seqs, asg]

theorem read_spec (hdec : Lax117284.InstanceEncoding.EncodesUniform x I k)
    (hL : x.length < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (M0 P c1 x) readCom (fun _ σ' => F0 P c1 I x k σ' ∧ σ'.vars "L" = x.length)
      (24 * x.length + 60) := by
  refine Spec.post (Spec.pre (readCom_spec hdec hL hX) ?_) ?_
  · rintro σ ⟨hi, ho, hZ⟩
    refine ⟨hi, ho, ?_⟩
    rw [hZ "X"]; simp [extF]
  · rintro σ σ' ⟨hi, ho, hZ⟩ ⟨hC, hLv, hi', ho', hA, hV⟩
    exact ⟨⟨hC, fun a ha => by rw [hA a ha, hZ a], hi', ho'⟩, hLv⟩

theorem test_spec (hdec : Lax117284.InstanceEncoding.EncodesUniform x I k)
    (hnB : I.clients + 1 < B) (h3 : 3 * x.length + 8 < B) :
    Spec B (fun σ => F0 P c1 I x k σ ∧ σ.vars "L" = x.length) critCom (fun _ σ' => R2 P c1 I x k σ')
      (90 * x.length + 300) := by
  have hl := ClientsWord.len_eq hdec
  have hs := (critCom_spec (n := I.clients) (L := x.length) (B := B) (by omega) hnB h3).frame
  refine Spec.post (Spec.pre hs ?_) ?_
  · rintro σ ⟨⟨hC, -, -, -⟩, hLv⟩
    exact ⟨hC.n, hLv⟩
  · rintro σ σ' ⟨⟨hC, hZ, hi, ho⟩, hLv⟩ ⟨hfit, hv, ha, hr, hw⟩
    obtain ⟨fv, fa, fr, fw⟩ := critCom_frame
    have hv' : ∀ y, y ∉ ["fit", "E", "cp", "ci"] → σ'.vars y = σ.vars y := fun y hy => hv y (fv y hy)
    have hA' : σ'.arrs = σ.arrs := funext fun a => ha a (fa a)
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, hfit⟩
    · rw [hA']; exact hC.X
    · rw [hv' _ (by decide)]; exact hC.n
    · rw [hv' _ (by decide)]; exact hC.m
    · rw [hv' _ (by decide)]; exact hC.k
    · intro a' ha'; rw [hA']; exact hZ a' ha'
    · rw [hr fr, hi]
    · rw [hw fw, ho]
    · rw [hv' _ (by decide)]; exact hLv

open Classical in
theorem main_core (hdec : Lax117284.InstanceEncoding.EncodesUniform x I k)
    (hL : x.length < B) (hX : ∀ v ∈ x, v < B) (hnB : I.clients + 1 < B) (h3 : 3 * x.length + 8 < B)
    (K1 K2 : ℕ)
    (hT : Q I.clients + 2 ≤ x.length → Spec B (F0 P c1 I x k) (fitBranch P c1)
      (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0]) K1)
    (hF : ¬ Q I.clients + 2 ≤ x.length → Spec B (F0 P c1 I x k) bruteBranch
      (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0]) K2) :
    Spec B (M0 P c1 x) (mainCom P c1) (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0])
      ((24 * x.length + 60) + ((90 * x.length + 300) +
        (4 + (if Q I.clients + 2 ≤ x.length then K1 else K2)))) := by
  have hl := ClientsWord.len_eq hdec
  have hsz : (Cond.lt (lit 0) (V "fit")).size = 3 := by simp [lit, V]
  have hite : Spec B (R2 P c1 I x k) (.ite (.lt (lit 0) (V "fit")) (fitBranch P c1) bruteBranch)
      (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0])
      (4 + (if Q I.clients + 2 ≤ x.length then K1 else K2)) := by
    have hdef : ∀ σ, R2 P c1 I x k σ → ∃ v, (Cond.lt (lit 0) (V "fit")).evalB B σ = some v := by
      intro σ hσ
      refine cond0_def (by omega) ?_
      rw [hσ.2.2]; split_ifs <;> omega
    by_cases hc : Q I.clients + 2 ≤ x.length
    · have := Spec.ite (P := R2 P c1 I x k) (b := Cond.lt (lit 0) (V "fit")) (c := fitBranch P c1) (d := bruteBranch) hdef
        (Spec.pre (hT hc) (fun σ hσ => hσ.1.1))
        (fun σ ⟨hR, hev⟩ => by
          have := cond0_false hev
          rw [hR.2.2, if_pos hc] at this
          omega)
      rw [hsz] at this
      rw [if_pos hc]
      exact Spec.mono this (by omega)
    · have := Spec.ite (P := R2 P c1 I x k) (b := Cond.lt (lit 0) (V "fit")) (c := fitBranch P c1) (d := bruteBranch) hdef
        (fun σ ⟨hR, hev⟩ => by
          have := cond0_true hev
          rw [hR.2.2, if_neg hc] at this
          omega)
        (Spec.pre (hF hc) (fun σ hσ => hσ.1.1))
      rw [hsz] at this
      rw [if_neg hc]
      exact Spec.mono this (by omega)
  unfold mainCom
  exact Spec.seq (read_spec hdec hL hX) (Spec.seq (test_spec hdec hnB h3) hite (fun _ _ _ h => h)
    (fun _ _ _ _ _ h => h)) (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)

end Lax117284Proofs.Machine.ClMain
