import Lax117284Proofs.Treewidth.Fun.VMSolveGuard
import Lax117284Proofs.Treewidth.Fun.LibEmbeds

/-!
# GATE G1: an end-to-end toy — `x ↦ x.reverse` on words of the format `graphK`, through the compiler

The smallest real function of the library (`Lib2.fReverse`, embedded in `LibEmbeds.embeds_reverse`) is compiled to a single word-RAM
program (`compileProgram solveLayout (solveCom Lib.Δ 128 34 Fmt.graphK toyP)`), and `ComputesInTime` is proved for it.
No axioms, no `sorry`.
-/

namespace Lax117284Proofs.Treewidth.Fun.Load.Toy

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax117284Proofs.Treewidth.Fun.VM.Ram Lax808846.Ram Lax808846.RamComputes ToVal

/-- The cost formula of the toy: `K x = 22 · 2^(kw³) · (|x| + 1)`. -/
def toyP : KP := ⟨22, 1, 1, 1⟩

/-- Admissible inputs: the words `n :: (n² entries) ++ [k]`. -/
def Dtoy : Set (List ℕ) := {x | fmtLen Fmt.graphK x = x.length}

theorem toy_hN : ∀ f, 128 ≤ f → Lib.Δ f = none := by
  intro f hf
  cases h : Lib.Δ f with
  | none => rfl
  | some b => exact absurd (Lib.Δ_lt h) (by have : Lib.reserved = 128 := rfl; omega)

theorem maxNat_toVal (x : List ℕ) : (toVal x).maxNat = maxEntry x := by
  induction x with
  | nil => rfl
  | cons a l ih =>
    show max a (toVal l).maxNat = _
    rw [ih]; rfl

theorem toy_K (x : List ℕ) : 22 * (x.length + 1) ≤ Kx toyP Fmt.graphK x := by
  unfold Kx KP.k toyP
  have : 1 ≤ 2 ^ (1 * (Fmt.graphK.kw x) ^ 3) := Nat.one_le_two_pow
  simp only [pow_one]
  nlinarith

theorem toy_runs : ∀ x ∈ Dtoy, Runs Lib.Δ (Bx toyP Fmt.graphK x) Lib2.fReverse [toVal x] (toVal x.reverse)
    (Kx toyP Fmt.graphK x) := by
  intro x _
  have hK := toy_K x
  have hemb := Lib.embeds_reverse (Δ' := Lib.Δ) (Ext.refl _) (α := ℕ)
  have hfit : Fits (Bx toyP Fmt.graphK x) (toVal x) (12 * x.length + 10) := by
    unfold Fits
    rw [maxNat_toVal]
    unfold Bx bexp
    have : maxEntry x + (12 * x.length + 10) + 2 ≤ maxEntry x + Kx toyP Fmt.graphK x + 2 := by omega
    have := Nat.pow_le_pow_left this 2
    omega
  obtain ⟨b, hb, c', hc', hev⟩ := hemb (Bx toyP Fmt.graphK x) x trivial hfit
  beta_reduce at hc'
  exact ⟨b, hb, c', by omega, hev⟩

/-- **GATE G1.**  One machine program computes `List.reverse` on `Dtoy` at every word length satisfying the guard. -/
theorem G1 : ∃ (prog : Program) (c : ℕ), ∀ w, (∀ x ∈ Dtoy, ∀ v ∈ x,
      c * 2 ^ (c * (Fmt.graphK.kw x) ^ 3) * (x.length + v + 1) ^ c ≤ 2 ^ w) →
    ComputesInTime w prog Dtoy List.reverse (fun x =>
      10 * kappa Lib.Δ 128 Lib2.fReverse toyP * (Kx toyP Fmt.graphK x + x.length + 1) + 1) := by
  obtain ⟨prog, c, h⟩ := compile_computes Lib.Δ toy_hN Lib2.fReverse Fmt.graphK toyP (by decide) (by decide)
    (by decide)
  refine ⟨prog, c, fun w hw => h Dtoy List.reverse (fun x hx => hx) toy_runs (fun x hx => ?_) w hw⟩
  have := toy_K x
  simp only [List.length_reverse]
  omega

end Lax117284Proofs.Treewidth.Fun.Load.Toy
