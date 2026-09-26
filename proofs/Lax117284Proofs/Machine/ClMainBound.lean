import Lax117284Proofs.Machine.ClMainOk

/-!
The bound on the values of the main program, as a function of the word, and what it entails.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846.Ram
open Lax117284Proofs.Machine.ClSim (V lit asg seqs code simCom)
open Lax117284Proofs.Machine.ClBuild
open Lax117284Proofs.ClientsILP Lax117284.Scheduling

/-- The layout of the main program: the scalars it mentions, the ten arrays, twelve temporaries. -/
def layoutF (P : Program) (c1 : ℕ) : Layout := ⟨cS (mainCom P c1), arrs10, 12⟩

theorem layout_ok (P : Program) (c1 : ℕ) : Com.Ok (layoutF P c1) (mainCom P c1) := by
  have h1 : ∀ y ∈ cS (mainCom P c1), y ∈ (layoutF P c1).scalars := fun y h => h
  have h2 : ∀ a ∈ cA (mainCom P c1), a ∈ (layoutF P c1).arrays := (fine_main P c1).1
  have h3 : cD (mainCom P c1) ≤ (layoutF P c1).temps := (fine_main P c1).2
  exact com_ok (layoutF P c1) (mainCom P c1) h1 h2 h3

/-- The bound on the values of the main program on the word `x`. -/
def Bx (P : Program) (c1 : ℕ) (x : List ℕ) : ℕ :=
  16 * (c1 * (2 * x.length + Mx x + 1) ^ (c1 - 1)) + 16 * (2 * x.length + Mx x + 1) + 64 + 4 * x.length +
    P.length + PB P + 1

variable {P : Program} {c1 : ℕ} {I : Instance} {x : List ℕ} {k : ℕ}

theorem mem_x (hdec : Lax117284.InstanceEncoding.EncodesUniform x I k) (j : ℕ) : x.getD j 0 ≤ Mx x := by
  by_cases hj : j < x.length
  · rw [List.getD_eq_getElem _ _ hj]; exact le_Mx (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]; omega

structure BxFacts (P : Program) (c1 : ℕ) (I : Instance) (x : List ℕ) (B : ℕ) : Prop where
  hL : x.length < B
  hX : ∀ v ∈ x, v < B
  hnB : I.clients + 1 < B
  h3 : 3 * x.length + 8 < B
  h4 : 4 * x.length + 64 < B
  hbB : 2 * x.length + I.days + 1 < B
  hw : 16 * (c1 * (2 * x.length + I.days + 1) ^ (c1 - 1)) + 32 < B
  hP : P.length < B
  hLits : ∀ i ∈ P, (code i).2.1 < B ∧ (code i).2.2.1 < B ∧ (code i).2.2.2 < B

theorem bxFacts (hdec : Lax117284.InstanceEncoding.EncodesUniform x I k) (hc1 : 1 ≤ c1) :
    BxFacts P c1 I x (Bx P c1 x) := by
  have hn := mem_x hdec 0
  have hm := mem_x hdec 1
  rw [Lax117284Proofs.ClientsWord.x0 hdec] at hn
  rw [Lax117284Proofs.ClientsWord.x1 hdec] at hm
  have e2 : c1 * (2 * x.length + I.days + 1) ^ (c1 - 1) ≤ c1 * (2 * x.length + Mx x + 1) ^ (c1 - 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hb : Bx P c1 x = 16 * (c1 * (2 * x.length + Mx x + 1) ^ (c1 - 1)) + 16 * (2 * x.length + Mx x + 1) +
    64 + 4 * x.length + P.length + PB P + 1 := rfl
  refine ⟨by omega, fun v hv => ?_, by omega, by omega, by omega, by omega, by omega, by omega, fun i hi => ?_⟩
  · have := le_Mx hv; omega
  · have := le_PB hi; omega

end Lax117284Proofs.Machine.ClMain
