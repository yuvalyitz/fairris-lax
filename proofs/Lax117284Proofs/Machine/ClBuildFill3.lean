import Lax117284Proofs.Machine.ClBuildFill2

/-!
The loop over the entries of the word.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- One entry and the increment. -/
def fillBody : Com := .seq zBody (asg "idx" (add (V "idx") (lit 1)))

/-- The invariant of the loop over the entries. -/
def FInv (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ (σ.arrs "okt").length = nV I.clients ∧
    (∀ c < nV I.clients, (σ.arrs "okt").getD c 0 =
      if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0) ∧
    (σ.arrs "cnt").length = nT I.clients ∧
    (∀ t < nT I.clients, (σ.arrs "cnt").getD t 0 = cntN I t) ∧
    (σ.arrs "z").length = zLen I.clients ∧ σ.vars "idx" ≤ zLen I.clients ∧
    ∀ i < σ.vars "idx", (σ.arrs "z").getD i 0 = zFunRaw I.clients I.days k (cntN I) i

theorem incr_spec : Spec B (fun σ => σ.vars "idx" + 1 < B ∧ 1 < B ∧ σ.vars "idx" < B)
    (asg "idx" (add (V "idx") (lit 1)))
    (fun σ σ' => σ' = σ.setVar "idx" (σ.vars "idx" + 1)) 10 := by
  run_vcg
  all_goals try rfl

theorem zPre_of_finv {σ : Env} (hF : FInv I x k σ) (hlt : σ.vars "idx" < zLen I.clients) :
    ZPre I x k σ :=
  ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2.1, hF.2.2.2.2.2.1, hF.2.2.2.2.2.2.1, hlt⟩

theorem fillBody_spec (h : Bh I x k B) :
    Spec B (fun σ => FInv I x k σ ∧ σ.vars "idx" < zLen I.clients) fillBody
      (fun σ σ' => FInv I x k σ' ∧ σ'.vars "idx" = σ.vars "idx" + 1)
      ((10 + 10 + 10 + (100 + 10) + 100 + 10) + 20) := by
  have hzl := h.hzB
  have hL := h.hL
  unfold fillBody
  have hz := Spec.pre (zBody_spec h) (fun σ (hσ : FInv I x k σ ∧ _) => zPre_of_finv hσ.1 hσ.2)
  have hB1 : 1 < B := by have := h.mn_le; omega
  refine Spec.seq (P' := fun σ => σ.vars "idx" + 1 < B ∧ 1 < B ∧ σ.vars "idx" < B) hz
    (Spec.mono (Spec.pre (incr_spec (B := B)) (fun σ hσ => hσ)) (by omega)) ?_ ?_
  · rintro σ σ1 ⟨hF, hlt⟩ ⟨hA, hzeq⟩
    have hidx1 : σ1.vars "idx" = σ.vars "idx" := hA.2.2.2 "idx" (by decide)
    refine ⟨by rw [hidx1]; omega, hB1, by rw [hidx1]; omega⟩
  · rintro σ σ1 σ2 ⟨hF, hlt⟩ ⟨hA, hzeq⟩ hσ2
    subst hσ2
    have hidx1 : σ1.vars "idx" = σ.vars "idx" := hA.2.2.2 "idx" (by decide)
    obtain ⟨hC, hS, hol, hoe, hcl, hce, hzl2, hle, hent⟩ := hF
    have hz1 : ∀ a, a ≠ "z" → σ1.arrs a = σ.arrs a := fun a ha => hA.1 a (by simpa using ha)
    have hzlen1 : (σ1.arrs "z").length = zLen I.clients := by
      rw [hzeq, List.length_set]; exact hzl2
    have hV : ∀ y, y ∉ ZV → σ1.vars y = σ.vars y := hA.2.2.2
    have hX1 := hz1 "X" (by decide)
    have hok1 := hz1 "okt" (by decide)
    have hcn1 := hz1 "cnt" (by decide)
    have hv : ∀ y, y ≠ "idx" → y ≠ "fq" → y ≠ "fr" → y ≠ "fc" → y ≠ "ct" → y ≠ "cs" → y ≠ "cf" →
        σ1.vars y = σ.vars y := fun y h1 h2 h3 h4 h5 h6 h7 =>
      hV y (by simp [ZV, h2, h3, h4, h5, h6, h7])
    have hnv := hv "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hmv := hv "m" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hkv := hv "k" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hnnv := hv "nn" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hTv := hv "T" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hZv := hv "Z" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hVv := hv "Vv" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hNv := hv "N" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hMv := hv "M" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hzlv := hv "zl" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals simp [Env.setVar, hX1, hC.X, hnv, hC.n, hmv, hC.m, hkv, hC.k, hnnv, hS.nn, hTv, hS.T,
      hZv, hS.Z, hVv, hS.Vv, hNv, hS.N, hMv, hS.M, hzlv, hS.zl, hok1, hol, hcn1, hcl, hzlen1, hidx1]
    all_goals try (intro c hc; simpa [List.getD_eq_getElem?_getD] using hoe c hc)
    all_goals try (intro t ht; simpa [List.getD_eq_getElem?_getD] using hce t ht)
    all_goals try exact hlt
    all_goals try
      (intro i hi
       rw [hzeq]
       by_cases hie : i = σ.vars "idx"
       · subst hie
         have : σ.vars "idx" < (σ.arrs "z").length := by rw [hzl2]; exact hlt
         simp [List.getElem?_set_self this]
       · have hlt' : i < σ.vars "idx" := by omega
         rw [List.getElem?_set_ne (Ne.symm hie)]
         simpa [List.getD_eq_getElem?_getD] using hent i hlt')

/-- The scalars and arrays the fill may change. -/
def FV : List String := "idx" :: ZV
def FA : List String := ["z"]

theorem fillCom_frame : (∀ y ∈ fillCom.wvars, y ∈ FV) ∧ (∀ a ∈ fillCom.warrs, a ∈ FA) ∧
    ¬ fillCom.reads ∧ fillCom.NoWrite := by
  exact ⟨by decide, by decide, by decide, by decide⟩

theorem fillCom_spec (h : Bh I x k B) :
    Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ (σ.arrs "okt").length = nV I.clients ∧
        (∀ c < nV I.clients, (σ.arrs "okt").getD c 0 =
          if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0) ∧
        (σ.arrs "cnt").length = nT I.clients ∧
        (∀ t < nT I.clients, (σ.arrs "cnt").getD t 0 = cntN I t) ∧
        (σ.arrs "z").length = zLen I.clients) fillCom
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧
        σ'.arrs "z" = zList I.clients I.days k (cntN I) ∧ AgreeA FV FA σ σ')
      ((((10 + 10 + 10 + (100 + 10) + 100 + 10) + 20) + 4) * zLen I.clients + 6) := by
  have hzl := h.hzB
  have hL := h.hL
  have hzB : zLen I.clients < B := by omega
  have hloop := Spec.forRangeZero (B := B) (c := fillBody) "idx" "zl" (FInv I x k) (zLen I.clients)
    ((10 + 10 + 10 + (100 + 10) + 100 + 10) + 20) hzB (fun σ hσ => hσ.2.2.2.2.2.2.2.1)
    (fun σ hσ => hσ.2.1.zl) (fillBody_spec h)
  have hfr := Spec.frame hloop
  obtain ⟨hv, ha, hr, hw⟩ := fillCom_frame
  have hpre : ∀ σ : Env, (Ctx0 I x k σ ∧ Sizes I σ ∧ (σ.arrs "okt").length = nV I.clients ∧
        (∀ c < nV I.clients, (σ.arrs "okt").getD c 0 =
          if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0) ∧
        (σ.arrs "cnt").length = nT I.clients ∧
        (∀ t < nT I.clients, (σ.arrs "cnt").getD t 0 = cntN I t) ∧
        (σ.arrs "z").length = zLen I.clients) → FInv I x k (σ.setVar "idx" 0) := by
    rintro σ ⟨hC, hS, hol, hoe, hcl, hce, hzl2⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [Env.setVar, hC.X, hC.n, hC.m, hC.k, hS.nn, hS.T, hS.Z, hS.Vv, hS.N, hS.M, hS.zl,
      hol, hcl, hzl2]
    · intro c hc; simpa [List.getD_eq_getElem?_getD] using hoe c hc
    · intro t ht; simpa [List.getD_eq_getElem?_getD] using hce t ht
  refine Spec.conseq hfr hpre ?_ le_rfl
  rintro σ σ' hσ ⟨⟨⟨hC, hS, hol, hoe, hcl, hce, hzl2, hle, hent⟩, hidx⟩, hf1, hf2, hf3, hf4⟩
  refine ⟨hC, hS, ?_, agreeA_of_frame hv ha hr hw hf1 hf2 hf3 hf4⟩
  refine List.ext_getElem (by rw [hzl2]; simp [zList, zLen]) fun i hi1 hi2 => ?_
  have hi : i < zLen I.clients := by rw [hzl2] at hi1; exact hi1
  have := hent i (by rw [hidx]; exact hi)
  rw [List.getD_eq_getElem _ _ hi1] at this
  rw [this]
  simp [zList, List.getElem_map, List.getElem_range]

end Lax117284Proofs.Machine.ClBuild
