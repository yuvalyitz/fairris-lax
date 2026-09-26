import Lax117284Proofs.Machine.TwAnswer2

/-!
The whole dynamic program: the loop over the nodes, then the answer.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP

variable {P : Params} {B : ℕ} {σ : Env}

/-- **The dynamic program.** -/
def dpCom : Com := .seq nodeLoop answerCom

/-- What the dynamic program costs. -/
def dpCost (P : Params) : ℕ := loopCost P + answerCost P

open Classical in
/-- **The dynamic program answers the question**, on an environment that meets the context. -/
theorem dpCom_run (hC : NC P B σ) :
    ∃ σ', Run B dpCom σ σ' (dpCost P) ∧
      σ'.out = σ.out ++ [if P.I.HasKFairSchedule P.kk then 1 else 0] := by
  obtain ⟨σ1, r1, hC1, hN1, -, ho1⟩ := nodeLoop_run hC
  obtain ⟨σ2, r2, ho2⟩ := answerCom_run hC1 hN1
  exact ⟨σ2, r1.seq r2, by rw [ho2, ho1]⟩

end Lax117284Proofs.Machine.TwNode
