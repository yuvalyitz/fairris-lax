import Lax117284Proofs.Machine.Emit

/-!
A loop that folds a function of the counter into one scalar: a flag, a count or a running maximum.
The body computes the next value of the scalar from the counter and the previous value, and touches
no other scalar the loop reads.
-/

namespace Lax117284Proofs.Machine.FoldLoop

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Emit

variable {B : ℕ}

/-- The loop over the counter `ctr` up to the scalar `mv`. -/
def fLoop (ctr mv : String) (c : Com) : Com :=
  .seq (.assign ctr (.lit 0))
    (.while (.lt (.var ctr) (.var mv)) (.seq c (.assign ctr (.bin .add (.var ctr) (.lit 1)))))

/-- **A loop that folds.** -/
theorem fLoop_spec (ctr mv acc : String) (c : Com) (S : List String) (step : ℕ → ℕ → ℕ)
    (Q : ℕ → ℕ → Prop) (K N : ℕ) (σ0 : Env)
    (hi : ctr ∈ S) (hmv : mv ∉ S) (hca : ctr ≠ acc) (hN : σ0.vars mv = N) (hNB : N + 1 < B)
    (hQ0 : Q 0 (σ0.vars acc)) (hQs : ∀ j a, Q j a → Q (j + 1) (step j a))
    (hc : ∀ σ, Agr S σ0 σ → σ.vars ctr < N → Q (σ.vars ctr) (σ.vars acc) →
      ∃ σ', Run B c σ σ' K ∧ σ'.vars acc = step (σ.vars ctr) (σ.vars acc) ∧ Agr S σ0 σ' ∧
        σ'.vars ctr = σ.vars ctr ∧ σ'.out = σ.out) :
    ∃ σ', Run B (fLoop ctr mv c) σ0 σ' ((K + 10 + 4) * N + 6) ∧
      σ'.vars acc = (List.range N).foldl (fun a j => step j a) (σ0.vars acc) ∧ Agr S σ0 σ' ∧
      σ'.out = σ0.out := by
  let I : Env → Prop := fun σ => Agr S σ0 σ ∧ σ.vars ctr ≤ N ∧
    σ.vars acc = (List.range (σ.vars ctr)).foldl (fun a j => step j a) (σ0.vars acc) ∧
    Q (σ.vars ctr) (σ.vars acc) ∧ σ.out = σ0.out
  have hbody : Spec B (fun σ => I σ ∧ σ.vars ctr < N)
      (.seq c (.assign ctr (.bin .add (.var ctr) (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars ctr = σ.vars ctr + 1) (K + 10) := by
    intro σ ⟨⟨hA, hle, hacc, hq, hout⟩, hlt⟩
    obtain ⟨σ1, r1, ha1, hA1, hi1, ho1⟩ := hc σ hA hlt hq
    have r2 : Run B (.assign ctr (.bin .add (.var ctr) (.lit 1))) σ1
        (σ1.setVar ctr (σ1.vars ctr + 1)) (1 + (Expr.bin .add (.var ctr) (.lit 1)).size) :=
      Run.assign (evalB_bin (evalB_var (by rw [hi1]; omega)) (evalB_lit (by omega))
        (by simp [hi1]; omega))
    refine ⟨_, (r1.seq r2).mono (by simp [Expr.size] <;> omega), ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [Env.setVar]; exact hA1.1
    · intro y hy
      have hyi : y ≠ ctr := fun h => hy (h ▸ hi)
      simp only [Env.setVar, if_neg hyi]
      exact hA1.2 y hy
    · simp [Env.setVar, hi1]; omega
    · simp only [Env.setVar, if_true, hi1, if_neg hca.symm]
      rw [ha1, hacc, List.range_succ, List.foldl_append]
      simp
    · simp only [Env.setVar, if_true, hi1, if_neg hca.symm]
      rw [ha1]
      exact hQs _ _ hq
    · simp only [Env.setVar]; rw [ho1, hout]
    · simp [Env.setVar, hi1]
  obtain ⟨σ', r, hI', hi'⟩ := (Spec.forRangeZero (B := B) (c := .seq c (.assign ctr
      (.bin .add (.var ctr) (.lit 1)))) ctr mv I N (K + 10) (by omega) (fun _ h => h.2.1)
    (fun σ h => (h.1.2 mv hmv).trans hN) hbody) σ0
    ⟨⟨by simp [Env.setVar], fun y hy => by
        have hyi : y ≠ ctr := fun h => hy (h ▸ hi)
        simp [Env.setVar, hyi]⟩, by simp [Env.setVar], by simp [Env.setVar, hca.symm], by
      simp [Env.setVar, hca.symm]; exact hQ0, by simp [Env.setVar]⟩
  refine ⟨σ', r, ?_, hI'.1, hI'.2.2.2.2⟩
  rw [hI'.2.2.1, hi']

end Lax117284Proofs.Machine.FoldLoop
