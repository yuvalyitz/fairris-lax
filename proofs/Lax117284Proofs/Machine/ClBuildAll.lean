import Lax117284Proofs.Machine.ClBuildFill3

/-!
The builder, whole: the sizes, the table of counts, the table of independent pairs, the word.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The whole builder. -/
def buildCom : Com := seqs [sizesCom, cntCom, okCom, fillCom]

/-- The scalars and arrays the builder may change. -/
def BV : List String := ["nn", "T", "Z", "Vv", "N", "M", "zl"] ++ (CV ++ (OV ++ FV))
def BA : List String := CA ++ (OA ++ FA)

theorem sizes_agreeA (h : Bh I x k B) {σ σ' : Env}
    (hf : (∀ y, y ∉ ["nn", "T", "Z", "Vv", "N", "M", "zl"] → σ'.vars y = σ.vars y) ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) :
    AgreeA ["nn", "T", "Z", "Vv", "N", "M", "zl"] [] σ σ' :=
  ⟨fun a _ => by rw [hf.2.1], hf.2.2.1, hf.2.2.2, hf.1⟩

/-- The state before the table of counts. -/
def B2 (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ σ.arrs "cnt" = List.replicate (nT I.clients) 0 ∧
    σ.arrs "okt" = List.replicate (nV I.clients) 0 ∧ σ.arrs "z" = List.replicate (zLen I.clients) 0

/-- The state after the table of counts. -/
def B3 (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ (σ.arrs "cnt").length = nT I.clients ∧
    (∀ t < nT I.clients, (σ.arrs "cnt").getD t 0 = cntN I t) ∧
    σ.arrs "okt" = List.replicate (nV I.clients) 0 ∧ σ.arrs "z" = List.replicate (zLen I.clients) 0

/-- The state after the table of independent pairs. -/
def B4 (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ (σ.arrs "okt").length = nV I.clients ∧
    (∀ c < nV I.clients, (σ.arrs "okt").getD c 0 =
      if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0) ∧
    (σ.arrs "cnt").length = nT I.clients ∧
    (∀ t < nT I.clients, (σ.arrs "cnt").getD t 0 = cntN I t) ∧
    (σ.arrs "z").length = zLen I.clients

theorem build234_spec (h : Bh I x k B) :
    Spec B (B2 I x k) (.seq cntCom (.seq okCom fillCom))
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧
        σ'.arrs "z" = zList I.clients I.days k (cntN I) ∧ AgreeA (CV ++ (OV ++ FV)) (CA ++ (OA ++ FA)) σ σ')
      ((((204 * (I.clients * I.clients) + 40) + 4) * I.days + 6) +
        ((((200 + 4) * (I.clients * I.clients) + 6) + 2 + 60 + 4) * nV I.clients + 6) +
        ((((10 + 10 + 10 + (100 + 10) + 100 + 10) + 20) + 4) * zLen I.clients + 6)) := by
  have hc := Spec.pre (cntCom_spec h) (fun σ (hσ : B2 I x k σ) =>
    (⟨hσ.1, hσ.2.1, hσ.2.2.1⟩ : Ctx0 I x k σ ∧ Sizes I σ ∧ σ.arrs "cnt" = List.replicate (nT I.clients) 0))
  have ho := Spec.pre (okCom_spec h) (fun σ (hσ : B3 I x k σ) =>
    (⟨hσ.1, hσ.2.1, hσ.2.2.2.2.1⟩ : Ctx0 I x k σ ∧ Sizes I σ ∧ σ.arrs "okt" = List.replicate (nV I.clients) 0))
  have hf := Spec.pre (fillCom_spec h) (fun σ (hσ : B4 I x k σ) => hσ)
  have hOF : Spec B (B3 I x k) (.seq okCom fillCom)
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧ σ'.arrs "z" = zList I.clients I.days k (cntN I) ∧
        AgreeA (OV ++ FV) (OA ++ FA) σ σ')
      (((((200 + 4) * (I.clients * I.clients) + 6) + 2 + 60 + 4) * nV I.clients + 6) +
        ((((10 + 10 + 10 + (100 + 10) + 100 + 10) + 20) + 4) * zLen I.clients + 6)) := by
    refine Spec.seq (P' := B4 I x k) ho hf ?_ ?_
    · rintro σ σ1 ⟨hC, hS, hcl, hce, hoke, hzr⟩ ⟨hC1, hS1, hol, hoe, hA⟩
      have hcn1 : σ1.arrs "cnt" = σ.arrs "cnt" := hA.1 "cnt" (by decide)
      have hz1 : σ1.arrs "z" = σ.arrs "z" := hA.1 "z" (by decide)
      refine ⟨hC1, hS1, hol, hoe, by rw [hcn1]; exact hcl, fun t ht => by rw [hcn1]; exact hce t ht, ?_⟩
      rw [hz1, hzr]; simp
    · rintro σ σ1 σ2 hσ ⟨hC1, hS1, hol, hoe, hA1⟩ ⟨hC2, hS2, hz2, hA2⟩
      exact ⟨hC2, hS2, hz2, AgreeA.trans hA1 hA2⟩
  refine Spec.mono (Spec.seq (P' := B3 I x k) hc hOF ?_ ?_) (by omega)
  · rintro σ σ1 ⟨hC, hS, hcn, hok, hzr⟩ ⟨hC1, hS1, hcl, hce, hA⟩
    have hok1 : σ1.arrs "okt" = σ.arrs "okt" := hA.1 "okt" (by decide)
    have hz1 : σ1.arrs "z" = σ.arrs "z" := hA.1 "z" (by decide)
    exact ⟨hC1, hS1, hcl, hce, by rw [hok1]; exact hok, by rw [hz1]; exact hzr⟩
  · rintro σ σ1 σ2 hσ ⟨hC1, hS1, hcl, hce, hA1⟩ ⟨hC2, hS2, hz2, hA2⟩
    exact ⟨hC2, hS2, hz2, AgreeA.trans hA1 hA2⟩

/-- The cost of the builder. -/
def buildCost (I : Instance) : ℕ :=
  100 + ((((204 * (I.clients * I.clients) + 40) + 4) * I.days + 6) +
    ((((200 + 4) * (I.clients * I.clients) + 6) + 2 + 60 + 4) * nV I.clients + 6) +
    ((((10 + 10 + 10 + (100 + 10) + 100 + 10) + 20) + 4) * zLen I.clients + 6))

/-- **The builder computes the word of the integer program.** -/
theorem buildCom_spec (h : Bh I x k B) :
    Spec B (fun σ => Ctx0 I x k σ ∧ σ.arrs "cnt" = List.replicate (nT I.clients) 0 ∧
        σ.arrs "okt" = List.replicate (nV I.clients) 0 ∧ σ.arrs "z" = List.replicate (zLen I.clients) 0)
      buildCom
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧
        σ'.arrs "z" = zList I.clients I.days k (cntN I) ∧ AgreeA BV BA σ σ') (buildCost I) := by
  have hs := Spec.pre (sizesCom_spec h) (fun σ (hσ : Ctx0 I x k σ ∧ σ.arrs "cnt" = List.replicate (nT I.clients) 0 ∧
    σ.arrs "okt" = List.replicate (nV I.clients) 0 ∧ σ.arrs "z" = List.replicate (zLen I.clients) 0) => hσ.1)
  have h234 := build234_spec h
  unfold buildCom buildCost
  refine Spec.mono (Spec.seq (P' := B2 I x k) hs h234 ?_ ?_) (by omega)
  · rintro σ σ1 ⟨hC, hcn, hok, hz⟩ ⟨hC1, hS1, hf, harr, hinp, hout⟩
    exact ⟨hC1, hS1, by rw [harr]; exact hcn, by rw [harr]; exact hok, by rw [harr]; exact hz⟩
  · rintro σ σ1 σ2 hσ ⟨hC1, hS1, hf, harr, hinp, hout⟩ ⟨hC2, hS2, hz2, hA2⟩
    refine ⟨hC2, hS2, hz2, ?_⟩
    exact AgreeA.mono (AgreeA.trans (sizes_agreeA h ⟨hf, harr, hinp, hout⟩) hA2)
      (fun y hy => by simp only [BV, List.mem_append] at hy ⊢; tauto)
      (fun a ha => by simp only [BA, List.mem_append, List.not_mem_nil, false_or] at ha ⊢; tauto)

end Lax117284Proofs.Machine.ClBuild
