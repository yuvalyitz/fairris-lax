import Lax117284Proofs.Machine.ClMainRead

/-!
The test of the main program: whether the word is long enough for the integer program's word
to be built, `Q n + 2 ≤ |x|`. It is decided by doubling a counter that is held at the length, so
that no value exceeds twice the length, and only when `n * (n + 1) ≤ |x|`, so that the number of
doublings, `2 n² + n + 3`, is itself bounded by a multiple of the length.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.Machine.ClBuild
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- One doubling, the counter held at the length. -/
def critStep : Com := seqs [asg "cp" (cap (mul (lit 2) (V "cp")) (V "L")),
  asg "ci" (add (V "ci") (lit 1))]

def critLoop : Com := .seq (asg "ci" (lit 0)) (.while (.lt (V "ci") (V "E")) critStep)

/-- The doubling part: `cp` becomes `min (2 ^ E) L`. -/
def critFit : Com := seqs [
  asg "E" (add (add (mul (lit 2) (mul (V "n") (V "n"))) (V "n")) (lit 3)),
  asg "cp" (lit 1), critLoop,
  .ite (.lt (add (V "cp") (lit 2)) (add (V "L") (lit 1))) (asg "fit" (lit 1)) .skip]

/-- The test: `fit` is `1` when `Q n + 2 ≤ L`. -/
def critCom : Com := seqs [asg "fit" (lit 0),
  .ite (.lt (V "n") (add (dv (V "L") (add (V "n") (lit 1))) (lit 1))) critFit .skip]

variable {B n L : ℕ}

/-- The invariant of the doubling loop. -/
def CI (n L : ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "L" = L ∧ σ.vars "E" = 2 * (n * n) + n + 3 ∧
    σ.vars "ci" ≤ 2 * (n * n) + n + 3 ∧ σ.vars "cp" = min (2 ^ σ.vars "ci") L ∧
      σ.vars "fit" = 0

theorem critStep_spec (hL : 1 ≤ L) (hB : 2 * L < B) (hEB : 2 * (n * n) + n + 4 < B) :
    Spec B (fun σ => CI n L σ ∧ σ.vars "ci" < 2 * (n * n) + n + 3) critStep
      (fun σ σ' => CI n L σ' ∧ σ'.vars "ci" = σ.vars "ci" + 1) 40 := by
  run_vcg
  all_goals rename_i hσ hlt
  all_goals obtain ⟨hn, hLv, hE, hci, hcp, hf⟩ := hσ
  have hp : 2 ^ (σ.vars "ci" + 1) = 2 * 2 ^ σ.vars "ci" := by ring
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [Env.setVar, hn, hLv, hE, hf]
    · omega
    · rw [hp]; omega
  all_goals omega

theorem critLoop_spec (hL : 1 ≤ L) (hB : 2 * L < B) (hEB : 2 * (n * n) + n + 4 < B) :
    Spec B (fun σ => CI n L (σ.setVar "ci" 0)) critLoop
      (fun _ σ' => CI n L σ' ∧ σ'.vars "ci" = 2 * (n * n) + n + 3) ((40 + 4) * (2 * (n * n) + n + 3) + 6) :=
  Spec.forRangeZero "ci" "E" (CI n L) (2 * (n * n) + n + 3) 40 (by omega)
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.1) (critStep_spec hL hB hEB)

theorem Q_eq (n : ℕ) : Q n = 2 ^ (2 * (n * n) + n + 3) := rfl

/-- What the doubling part starts from. -/
def CP (n L : ℕ) (σ : Env) : Prop := σ.vars "n" = n ∧ σ.vars "L" = L ∧ σ.vars "fit" = 0

theorem critFit_spec (hL : 1 ≤ L) (hnL : n * n + n ≤ L) (hB : 3 * L + 8 < B) :
    Spec B (CP n L) critFit
      (fun _ σ' => σ'.vars "fit" = if Q n + 2 ≤ L then 1 else 0) (44 * (2 * (n * n) + n + 3) + 100) := by
  have hEB : 2 * (n * n) + n + 4 < B := by omega
  run_vcg [critLoop_spec (n := n) (L := L) hL (by omega) hEB]
  all_goals try obtain ⟨hn, hLv, hf⟩ := ‹CP n L σ›
  all_goals try (simp only [hn]; omega)
  · rename_i w hCI hc
    obtain ⟨⟨-, hLw, -, -, hcp, -⟩, hci⟩ := hCI
    rw [hci, ← Q_eq] at hcp
    simp only [Env.setVar, if_true]
    rw [if_pos]; omega
  · rename_i w hCI hc
    obtain ⟨⟨-, hLw, -, -, hcp, hfw⟩, hci⟩ := hCI
    rw [hci, ← Q_eq] at hcp
    rw [hfw, if_neg]; omega
  · simp [CI, Env.setVar, hn, hLv, hf]; omega
  all_goals (rename_i w hCI; obtain ⟨⟨-, hLw, -, -, hcp, -⟩, -⟩ := hCI; omega)

theorem Q_gt (hn : L < n * n + n) : L < Q n := by
  have := @Nat.lt_two_pow_self (2 * (n * n) + n + 3)
  rw [Q_eq]; omega

theorem critCom_spec (hL : 1 ≤ L) (hnB : n + 1 < B) (hB : 3 * L + 8 < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.vars "L" = L) critCom
      (fun _ σ' => σ'.vars "fit" = if Q n + 2 ≤ L then 1 else 0) (90 * L + 300) := by
  have hcs : Spec B (fun σ => CP n L σ ∧ n * n + n ≤ L) critFit
      (fun _ σ' => σ'.vars "fit" = if Q n + 2 ≤ L then 1 else 0) (88 * L + 240) :=
    fun σ ⟨h1, h2⟩ => Spec.mono (critFit_spec hL h2 hB) (by omega) σ h1
  run_vcg [hcs]
  · assumption
  · rename_i hn hL' hc
    simp [Env.setVar, hn, hL'] at hc ⊢
    have h1 : L / (n + 1) < n := by omega
    have h2 : L < n * (n + 1) := (Nat.div_lt_iff_lt_mul (Nat.succ_pos n)).mp h1
    have := Q_gt (n := n) (L := L) (by nlinarith)
    omega
  · rename_i hn hL'
    have := Nat.div_le_self L (n + 1)
    simp [Env.setVar, hn, hL']
    omega
  · rename_i hn hL'
    have := Nat.div_le_self L (n + 1)
    simp [Env.setVar, hn, hL']
    omega
  · rename_i hn hL' hc
    simp [Env.setVar, hn, hL'] at hc
    have h1 : n ≤ L / (n + 1) := by omega
    have h2 : n * (n + 1) ≤ L := (Nat.le_div_iff_mul_le (Nat.succ_pos n)).mp h1
    exact ⟨⟨by simp [CP, Env.setVar, hn, hL'], by simp [CP, Env.setVar, hn, hL'], by simp [CP, Env.setVar]⟩,
      by nlinarith⟩

end Lax117284Proofs.Machine.ClMain
