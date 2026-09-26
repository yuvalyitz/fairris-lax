import Lax117284Proofs.Machine.TwLoop2

/-!
The loop over the nodes.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

lemma NC.setVar_i (h : NC P B σ) (v : ℕ) : NC P B (σ.setVar "i" v) :=
  h.transfer (fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Env.setVar])
    (by simp) (by simp) (by simp) (by simp) (by simp)

/-- **The loop over the nodes.** -/
def nodeLoop : Com := fLoop "i" "N" nodeCom

/-- What the loop over the nodes costs. -/
def loopCost (P : Params) : ℕ := (nodeCost P + 10 + 4) * P.N + 6

theorem nodeLoop_run (hC : NC P B σ) :
    ∃ σ', Run B nodeLoop σ σ' (loopCost P) ∧ NC P B σ' ∧
      NI P.I P.kk P.D P.wid P.tabs P.N σ' ∧ σ'.vars "i" = P.N ∧ σ'.out = σ.out := by
  let I : Env → Prop := fun τ => NC P B τ ∧ NI P.I P.kk P.D P.wid P.tabs (τ.vars "i") τ ∧
    τ.vars "i" ≤ P.N ∧ τ.out = σ.out
  have hb3 := hC.b3
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "i" < P.N)
      (.seq nodeCom (.assign "i" (.bin .add (.var "i") (.lit 1))))
      (fun τ τ' => I τ' ∧ τ'.vars "i" = τ.vars "i" + 1) (nodeCost P + 10) := by
    rintro τ ⟨⟨hC1, hN1, hle, ho⟩, hlt⟩
    obtain ⟨τ1, r1, kk1, hN2, ho1⟩ := nodeCom_run hC1 hN1 rfl hlt
    have hi1 : τ1.vars "i" = τ.vars "i" := kk1.vars "i" (by simp [SN, SV, Stt, St2, SD])
    have hlt1 : τ1.vars "i" + 1 < B := by
      have := hC1.b3; rw [hi1]; omega
    have r2 : Run B (.assign "i" (.bin .add (.var "i") (.lit 1))) τ1
        (τ1.setVar "i" (τ1.vars "i" + 1)) (1 + (Expr.bin .add (.var "i") (.lit 1)).size) :=
      Run.assign (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; try omega))
    refine ⟨_, (r1.seq r2).mono (by simp [Expr.size]; try omega), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · exact (kk1.nc hC1).setVar_i _
    · simp only [vars_setVar, if_true, hi1]
      exact hN2.of_arrs (by simp)
    · simp only [vars_setVar, if_true, hi1]; omega
    · simp [ho1, ho]
    · simp [hi1]
  have hres := (Spec.forRangeZero (B := B)
    (c := .seq nodeCom (.assign "i" (.bin .add (.var "i") (.lit 1)))) "i" "N" I P.N
    (nodeCost P + 10) (by omega) (fun τ h => h.2.2.1) (fun τ h => h.1.N_) hbody) σ (by
      refine ⟨hC.setVar_i _, ?_, by simp, by simp⟩
      exact ⟨fun j hj => by simp at hj, fun j hj => by simp at hj, fun j hj => by simp at hj⟩)
  obtain ⟨σ', r, hI, hi⟩ := hres
  refine ⟨σ', r.mono (by unfold loopCost; omega), hI.1, ?_, hi, hI.2.2.2⟩
  have := hI.2.1
  rwa [hi] at this

end Lax117284Proofs.Machine.TwNode
