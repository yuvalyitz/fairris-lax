import Lax117284Proofs.Machine.ClBruteFeas2

/-!
The feasibility scan, over the days.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

/-- The state of the loop over the days. -/
structure IInv (x : List ℕ) (I : Instance) (k : ℕ) (f : ℕ → ℕ) (ok0 : ℕ) (σ : Env) : Prop where
  ctx : Ctx x I k f σ
  hi : σ.vars "bfi" ≤ I.days
  hok : σ.vars "bfok" ≤ 1
  hiff : σ.vars "bfok" = 1 ↔ ok0 = 1 ∧ ∀ i', i' < σ.vars "bfi" → ∀ a b, ¬ Bad I f i' a b

theorem ro_spec (hb : Bd B x I k) (f : ℕ → ℕ) (ok0 : ℕ) :
    Spec B (fun σ => IInv x I k f ok0 σ ∧ σ.vars "bfi" < I.days)
      (asg "bfro" (.mul (V "bfi") (V "n")))
      (fun σ σ' => σ' = σ.setVar "bfro" (σ.vars "bfi" * σ.vars "n")) 4 := by
  refine Spec.assign (f := fun σ => σ.vars "bfi" * σ.vars "n") fun σ h => ?_
  have hnn : σ.vars "n" = I.clients := h.1.ctx.hn
  have hlt := h.2
  have hbig := hb.big
  have hmB := hb.mB
  have hmn := hb.mnB
  have hlen := hb.len
  have hnB := hb.nB
  have : σ.vars "bfi" * I.clients ≤ I.days * I.clients := Nat.mul_le_mul_right _ hlt.le
  exact evalB_bin (evalB_var (by omega)) (evalB_var (by omega)) (by rw [Bop.apply_mul, hnn]; omega)

theorem iStep_spec (hb : Bd B x I k) (f : ℕ → ℕ) (ok0 : ℕ) :
    Spec B (fun σ => IInv x I k f ok0 σ ∧ σ.vars "bfi" < I.days) iStep
      (fun σ σ' => IInv x I k f ok0 σ' ∧ σ'.vars "bfi" = σ.vars "bfi" + 1)
      (4 + (((23 + ((65 + 4) * I.clients + 6 + 4) + 4) * I.clients + 6) + 4)) := by
  intro σ ⟨hI, hlt⟩
  have hbig := hb.big
  have hmB := hb.mB
  have hnn : σ.vars "n" = I.clients := hI.ctx.hn
  obtain ⟨σ1, hr1, h1⟩ := ro_spec hb f ok0 σ ⟨hI, hlt⟩
  have hc1 : Ctx x I k f σ1 := by rw [h1]; exact hI.ctx.setVar _ (by decide)
  have hv1 : ∀ y, y ≠ "bfro" → σ1.vars y = σ.vars y := by
    intro y hy; rw [h1]; simp [hy]
  have hro1 : σ1.vars "bfro" = σ.vars "bfi" * I.clients := by rw [h1]; simp [hnn]
  obtain ⟨σ2, hr2, hAI, han⟩ := aLoop_spec hb f (σ.vars "bfi") hlt σ1
    ⟨hc1, by rw [hv1 _ (by decide)], hro1, by rw [hv1 _ (by decide)]; exact hI.hok⟩
  have hbi : σ2.vars "bfi" = σ.vars "bfi" := hAI.hi
  obtain ⟨σ3, hr3, rfl⟩ := (bump_spec (B := B) "bfi") σ2 ⟨by omega, by omega⟩
  refine ⟨_, hr1.seq (hr2.seq hr3), ⟨hAI.ctx.setVar _ (by decide), ?_, ?_, ?_⟩, ?_⟩
  · simp only [vars_setVar, if_true, hbi]; omega
  · simpa using hAI.hok
  · have h1' := hAI.hiff
    rw [han, row_iff] at h1'
    simp only [vars_setVar, if_true, hbi, String.reduceEq, not_false_eq_true, if_neg]
    have h2 : (σ1.vars "bfok") = σ.vars "bfok" := hv1 _ (by decide)
    rw [h1', h2, hI.hiff, lt_succ_forall]
    tauto
  · simp only [vars_setVar, if_true, hbi]

theorem feasCom_spec (hb : Bd B x I k) (f : ℕ → ℕ) :
    Spec B (fun σ => Ctx x I k f σ ∧ σ.vars "bfok" ≤ 1) feasCom
      (fun σ σ' => IInv x I k f (σ.vars "bfok") σ' ∧ σ'.vars "bfi" = I.days)
      ((4 + (((23 + ((65 + 4) * I.clients + 6 + 4) + 4) * I.clients + 6) + 4) + 4) * I.days + 6) := by
  intro σ ⟨hctx, h1⟩
  obtain ⟨σ', hrun, hI, hbn⟩ := (Spec.forRangeZero (B := B) "bfi" "m"
    (IInv x I k f (σ.vars "bfok")) I.days
    (4 + (((23 + ((65 + 4) * I.clients + 6 + 4) + 4) * I.clients + 6) + 4)) hb.mB
    (fun _ h => h.hi) (fun _ h => h.ctx.hm) (iStep_spec hb f (σ.vars "bfok"))) σ
    ⟨hctx.setVar 0 (by decide), by simp, by simpa using h1, by simp⟩
  exact ⟨σ', hrun, hI, hbn⟩

end Lax117284Proofs.Machine.ClBrute
