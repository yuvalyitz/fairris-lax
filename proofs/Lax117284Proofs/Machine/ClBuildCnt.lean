import Lax117284Proofs.Machine.ClBuildType

/-!
The type number of a day as a loop over the positions, and the table of counts as a loop over the
days.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The state between the phases of the type loop's body. -/
def Mid (I : Instance) (x : List ℕ) (k i : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ci" = i ∧ σ.vars "q" < I.clients * I.clients ∧
    σ.vars "tt" = bitsNum (fconf I i) (σ.vars "q") ∧ σ.vars "qa" = σ.vars "q" / I.clients ∧
    σ.vars "qb" = σ.vars "q" % I.clients ∧ σ.vars "qa" < I.clients ∧ σ.vars "qb" < I.clients

theorem typeBody_spec' (h : Bh I x k B) (i : ℕ) (hi : i < I.days) :
    Spec B (fun σ => TInv I x k i σ ∧ σ.vars "q" < I.clients * I.clients) typeBody
      (fun σ σ' => TInv I x k i σ' ∧ σ'.vars "q" = σ.vars "q" + 1) 200 := by
  have hnB := h.n_lt
  have hnnB := h.nn_lt
  rcases Nat.eq_zero_or_pos I.clients with h0 | hn
  · intro σ ⟨_, hq⟩
    rw [h0] at hq; simp at hq
  unfold typeBody
  have hA := Spec.pre (phaseA_spec h hn) (fun σ (hσ : TInv I x k i σ ∧ _) =>
    (⟨hσ.1.1, hσ.2, lt_trans hσ.2 hnnB⟩ : Ctx0 I x k σ ∧ _ ∧ _))
  have hB := phaseB_spec h i hi
  have hC := phaseC_spec h i
  have hBC : Spec B (Mid I x k i) (.seq phaseB phaseC)
      (fun σ σ' => TInv I x k i σ' ∧ σ'.vars "q" = σ.vars "q" + 1) (100 + 50) := by
    refine Spec.seq (P' := PC I x k i B) (Spec.pre hB (fun σ (hσ : Mid I x k i σ) =>
      ⟨hσ.1, hσ.2.2.1, hσ.2.2.2.2.2.2.2.1, hσ.2.2.2.2.2.2.2.2⟩)) hC ?_ ?_
    · rintro σ σ1 ⟨hC0, hS, hci, hq, htt, hqa, hqb, hqa', hqb'⟩ ⟨hA, hda, hpa, hdb, hpb⟩
      have hq1 : σ1.vars "q" = σ.vars "q" := hA.2.2.2 "q" (by decide)
      have hqa1 : σ1.vars "qa" = σ.vars "qa" := hA.2.2.2 "qa" (by decide)
      have hqb1 : σ1.vars "qb" = σ.vars "qb" := hA.2.2.2 "qb" (by decide)
      have htt1 : σ1.vars "tt" = σ.vars "tt" := hA.2.2.2 "tt" (by decide)
      refine ⟨hC0.agree hA (by decide) (by decide) (by decide), hS.agree hA (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hq1]; exact hq
      · rw [htt1, hq1]; exact htt
      · rw [hda, hqa, hq1]
      · rw [hpa, hqa, hq1]
      · rw [hdb, hqb, hq1]
      · rw [hpb, hqb, hq1]
      · rw [hda]; exact h.dAt_lt hi hqa'
      · rw [hpa]; exact h.pAt_lt hi hqa'
      · rw [hdb]; exact h.dAt_lt hi hqb'
      · rw [hpb]; exact h.pAt_lt hi hqb'
    · rintro σ σ1 σ2 ⟨hC0, hS, hci, hq, htt, hqa, hqb, hqa', hqb'⟩ ⟨hA, -⟩ ⟨hA2, hq2, htt2⟩
      have hq1 : σ1.vars "q" = σ.vars "q" := hA.2.2.2 "q" (by decide)
      have hci1 : σ1.vars "ci" = σ.vars "ci" := hA.2.2.2 "ci" (by decide)
      have hci2 : σ2.vars "ci" = σ1.vars "ci" := hA2.2.2.2 "ci" (by decide)
      have hσ1C := hC0.agree hA (by decide) (by decide) (by decide)
      have hσ1S := hS.agree hA (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)
      refine ⟨⟨hσ1C.agree hA2 (by decide) (by decide) (by decide),
        hσ1S.agree hA2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), by rw [hci2, hci1]; exact hci, ?_, ?_⟩, ?_⟩
      · omega
      · rw [htt2, ← hq2]
      · rw [hq2, hq1]
  refine Spec.mono (Spec.seq (P' := Mid I x k i) hA hBC ?_ ?_) (by omega)
  · rintro σ σ1 ⟨⟨hC0, hS, hci, hq0, htt⟩, hq⟩ ⟨hAg, hqa, hqb⟩
    have hq1 : σ1.vars "q" = σ.vars "q" := hAg.2.2.2 "q" (by decide)
    refine ⟨hC0.agree hAg (by decide) (by decide) (by decide),
      hS.agree hAg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), by rw [hAg.2.2.2 "ci" (by decide)]; exact hci, by rw [hq1]; exact hq,
      by rw [hAg.2.2.2 "tt" (by decide), hq1]; exact htt, by rw [hqa, hq1],
      by rw [hqb, hq1], ?_, ?_⟩
    · rw [hqa]; exact Nat.div_lt_of_lt_mul hq
    · rw [hqb]; exact Nat.mod_lt _ hn
  · rintro σ σ1 σ2 _ ⟨hAg, -⟩ ⟨hT, hq2⟩
    refine ⟨hT, ?_⟩
    rw [hq2, hAg.2.2.2 "q" (by decide)]

/-- The scalars the type loop may change. -/
def TL : List String := ["tt", "q", "qa", "qb", "da", "pa", "db", "pb", "fl"]

theorem typeLoop_frame : ∀ (c : Com), c = (Com.seq (.assign "q" (.lit 0))
      (.while (.lt (.var "q") (.var "nn")) typeBody)) →
    (∀ y ∈ c.wvars, y ∈ TL) ∧ (∀ a ∈ c.warrs, False) ∧ ¬ c.reads ∧ c.NoWrite := by
  intro c hc
  subst hc
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro a ha
  have : (Com.seq (.assign "q" (.lit 0)) (.while (.lt (.var "q") (.var "nn")) typeBody)).warrs = [] := by
    decide
  rw [this] at ha; simp at ha

theorem typeLoop_spec (h : Bh I x k B) (i : ℕ) (hi : i < I.days) :
    Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ci" = i) typeLoop
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧ σ'.vars "ci" = i ∧
        σ'.vars "tt" = typeNum I i ∧ AgreeOff TL σ σ') (((200 + 4) * (I.clients * I.clients) + 6) + 2) := by
  have hnnB := h.nn_lt
  have hloop := Spec.forRangeZero (B := B) (c := typeBody) "q" "nn" (TInv I x k i)
    (I.clients * I.clients) 200 hnnB (fun σ hσ => hσ.2.2.2.1) (fun σ hσ => hσ.2.1.nn)
    (typeBody_spec' h i hi)
  have hasg : Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ci" = i) (asg "tt" (lit 0))
      (fun σ σ' => σ' = σ.setVar "tt" 0) (1 + 1) := by
    have := Spec.assign (B := B) (P := fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ci" = i)
      (x := "tt") (e := lit 0) (f := fun _ => 0) (fun σ _ => evalB_lit (by omega))
    simpa using this
  have hfr := Spec.frame hloop
  unfold typeLoop
  refine Spec.mono (Spec.seq (P' := fun σ => TInv I x k i (σ.setVar "q" 0)) hasg hfr ?_ ?_)
    (by simp [Expr.size]; omega)
  · rintro σ σ1 ⟨hC, hS, hci⟩ rfl
    have hnn : σ.vars "nn" = I.clients * I.clients := hS.nn
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals simp [Env.setVar, hC.X, hC.n, hC.m, hC.k, hS.nn, hS.T, hS.Z, hS.Vv, hS.N, hS.M, hS.zl,
      hci, bitsNum]
  · rintro σ σ1 σ2 ⟨hC, hS, hci⟩ rfl ⟨⟨hT, hq⟩, hf1, hf2, hf3, hf4⟩
    obtain ⟨hv, ha, hr, hw⟩ := typeLoop_frame _ rfl
    have hA1 : AgreeOff ["tt"] σ (σ.setVar "tt" 0) :=
      ⟨rfl, rfl, rfl, fun y hy => by simp at hy; simp [Env.setVar, hy]⟩
    have hA2 := agree_of_frame_gen hv ha hr hw hf1 hf2 hf3 hf4
    refine ⟨hT.1, hT.2.1, hT.2.2.1, ?_, AgreeOff.mono' (AgreeOff.trans' hA1 hA2) ?_⟩
    · have := hT.2.2.2.2
      rw [this, hq]; rfl
    · intro y hy
      simp only [TL, List.mem_append, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      tauto

end Lax117284Proofs.Machine.ClBuild
