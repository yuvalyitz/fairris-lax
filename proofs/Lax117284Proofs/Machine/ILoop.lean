import Lax117284Proofs.Machine.FoldLoop

/-!
The loop over a counter with an arbitrary invariant of the whole state: the invariant says how far
the loop has come, does not mention the counter, and the body carries it from one round to the next.
-/

namespace Lax117284Proofs.Machine.ILoop

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.FoldLoop

variable {B : ℕ}

/-- **A loop with an invariant.** -/
theorem iLoop_spec (ctr mv : String) (c : Com) (Q : ℕ → Env → Prop) (K N : ℕ) (σ0 : Env)
    (hmv : σ0.vars mv = N) (hmvQ : ∀ j σ, Q j σ → σ.vars mv = N) (hmc : mv ≠ ctr)
    (hNB : N + 1 < B) (hQ0 : Q 0 (σ0.setVar ctr 0))
    (hQctr : ∀ j σ v, Q j σ → Q j (σ.setVar ctr v))
    (hc : ∀ j σ, Q j σ → σ.vars ctr = j → j < N →
      ∃ σ', Run B c σ σ' K ∧ Q (j + 1) σ' ∧ σ'.vars ctr = j) :
    ∃ σ', Run B (fLoop ctr mv c) σ0 σ' ((K + 10 + 4) * N + 6) ∧ Q N σ' := by
  let I : Env → Prop := fun σ => σ.vars ctr ≤ N ∧ Q (σ.vars ctr) σ
  have hbody : Spec B (fun σ => I σ ∧ σ.vars ctr < N)
      (.seq c (.assign ctr (.bin .add (.var ctr) (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars ctr = σ.vars ctr + 1) (K + 10) := by
    intro σ ⟨⟨hle, hq⟩, hlt⟩
    obtain ⟨σ1, r1, hq1, hi1⟩ := hc _ σ hq rfl hlt
    have r2 : Run B (.assign ctr (.bin .add (.var ctr) (.lit 1))) σ1
        (σ1.setVar ctr (σ1.vars ctr + 1)) (1 + (Expr.bin .add (.var ctr) (.lit 1)).size) :=
      Run.assign (evalB_bin (evalB_var (by rw [hi1]; omega)) (evalB_lit (by omega))
        (by simp [hi1]; omega))
    refine ⟨_, (r1.seq r2).mono (by simp [Expr.size] <;> omega), ⟨?_, ?_⟩, ?_⟩
    · simp [Env.setVar, hi1]; omega
    · simp only [Env.setVar, if_true, hi1]
      have := hQctr _ _ (σ1.vars ctr + 1) hq1
      simpa [Env.setVar, hi1] using this
    · simp [Env.setVar, hi1]
  obtain ⟨σ', r, hI', hi'⟩ := (Spec.forRangeZero (B := B) (c := .seq c (.assign ctr
      (.bin .add (.var ctr) (.lit 1)))) ctr mv I N (K + 10) (by omega) (fun _ h => h.1)
    (fun σ h => hmvQ _ σ h.2) hbody) σ0 ⟨by simp [Env.setVar], by simpa [Env.setVar] using hQ0⟩
  refine ⟨σ', r, ?_⟩
  have := hI'.2
  rwa [hi'] at this

end Lax117284Proofs.Machine.ILoop
