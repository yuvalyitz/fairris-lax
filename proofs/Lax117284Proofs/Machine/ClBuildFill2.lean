import Lax117284Proofs.Machine.ClBuildFill

/-!
The entries of the word: a coefficient, a right-hand side, or one of the two counts.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The state at an entry of the word: the tables and the array of the word. -/
def ZPre (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ (σ.arrs "okt").length = nV I.clients ∧
    (∀ c < nV I.clients, (σ.arrs "okt").getD c 0 =
      if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0) ∧
    (σ.arrs "cnt").length = nT I.clients ∧
    (∀ t < nT I.clients, (σ.arrs "cnt").getD t 0 = cntN I t) ∧
    (σ.arrs "z").length = zLen I.clients ∧ σ.vars "idx" < zLen I.clients

/-- The scalars an entry may change. -/
def ZV : List String := ["fq", "fr", "fc", "ct", "cs", "cf"]

theorem idxCom_spec (h : Bh I x k B) :
    Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ 2 ≤ σ.vars "idx" ∧ σ.vars "idx" < zLen I.clients)
      idxCom
      (fun σ σ' => AgreeOff ["fq", "fr", "fc", "ct", "cs"] σ σ' ∧
        σ'.vars "fr" = (σ.vars "idx" - 2) / nN I.clients ∧
        σ'.vars "fc" = (σ.vars "idx" - 2) % nN I.clients ∧
        σ'.vars "ct" = σ'.vars "fc" / nZ I.clients ∧ σ'.vars "cs" = σ'.vars "fc" % nZ I.clients) 100 := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hmod : ∀ q n : ℕ, q - q / n * n = q % n := fun q n => by
    rw [Nat.mul_comm]; exact (Nat.mod_def q n).symm
  run_vcg
  all_goals
    have hC : Ctx0 I x k σ := ‹_›
    have hS : Sizes I σ := ‹_›
    have hi2 : 2 ≤ σ.vars "idx" := ‹_›
    have hil : σ.vars "idx" < zLen I.clients := ‹_›
    have hd1 : (σ.vars "idx" - 2) / nN I.clients ≤ σ.vars "idx" - 2 := Nat.div_le_self _ _
    have hd2 : (σ.vars "idx" - 2) / nN I.clients * nN I.clients ≤ σ.vars "idx" - 2 := Nat.div_mul_le_self _ _
    have hd3 : (σ.vars "idx" - 2) % nN I.clients ≤ σ.vars "idx" - 2 := Nat.mod_le _ _
    have hd4 : (σ.vars "idx" - 2) % nN I.clients / nZ I.clients ≤ (σ.vars "idx" - 2) % nN I.clients := Nat.div_le_self _ _
    have hd5 : (σ.vars "idx" - 2) % nN I.clients / nZ I.clients * nZ I.clients ≤ (σ.vars "idx" - 2) % nN I.clients := Nat.div_mul_le_self _ _
  all_goals try refine ⟨⟨rfl, rfl, rfl, fun y hy => ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals try
    (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
     simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2])
  all_goals try simp [Env.setVar, hS.N, hS.Z, hmod]
  all_goals try omega

theorem zStore_spec :
    Spec B (fun σ => σ.vars "idx" < (σ.arrs "z").length ∧ σ.vars "cf" < B ∧ σ.vars "idx" < B) zStore
      (fun σ σ' => σ' = σ.setArr "z" (σ.vars "idx") (σ.vars "cf")) 10 := by
  run_vcg
  all_goals try rfl

theorem coefPart_eq : coefPart = .seq idxCom (.seq coefCom zStore) := rfl

/-- The state after the coordinates of the entry are known. -/
def CP (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  CoefPre I x k σ ∧ (σ.arrs "z").length = zLen I.clients ∧ σ.vars "idx" < zLen I.clients ∧
    σ.vars "fr" = (σ.vars "idx" - 2) / nN I.clients ∧ σ.vars "fc" = (σ.vars "idx" - 2) % nN I.clients

theorem coefRaw_le (n r c : ℕ) : coefRaw n r c ≤ 1 := by
  unfold coefRaw
  split_ifs <;> omega

/-- The state before the coefficient's entry is computed. -/
def PZ (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  ZPre I x k σ ∧ 2 ≤ σ.vars "idx" ∧ σ.vars "idx" < 2 + nM I.clients * nN I.clients

theorem coefPart_spec (h : Bh I x k B) :
    Spec B (PZ I x k) coefPart
      (fun σ σ' => AgreeA ZV ["z"] σ σ' ∧
        σ'.arrs "z" = (σ.arrs "z").set (σ.vars "idx")
          (coefRaw I.clients ((σ.vars "idx" - 2) / nN I.clients) ((σ.vars "idx" - 2) % nN I.clients)))
      (100 + (100 + 10)) := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hB3 : 2 < B := by have := h.mn_le; omega
  have hidx := Spec.pre (idxCom_spec h) (fun σ (hσ : PZ I x k σ) =>
    (⟨hσ.1.1, hσ.1.2.1, hσ.2.1, hσ.1.2.2.2.2.2.2.2⟩ : Ctx0 I x k σ ∧ Sizes I σ ∧ 2 ≤ σ.vars "idx" ∧
      σ.vars "idx" < zLen I.clients))
  have hcoef := Spec.pre (coefCom_spec h (B := B)) (fun σ (hσ : CP I x k σ) => hσ.1)
  rw [coefPart_eq]
  have hin : Spec B (CP I x k) (.seq coefCom zStore)
      (fun σ σ' => AgreeA ["cf"] ["z"] σ σ' ∧ σ'.arrs "z" = (σ.arrs "z").set (σ.vars "idx")
        (coefRaw I.clients (σ.vars "fr") (σ.vars "fc"))) (100 + 10) := by
    refine Spec.seq (P' := fun σ => σ.vars "idx" < (σ.arrs "z").length ∧ σ.vars "cf" < B ∧
      σ.vars "idx" < B) hcoef zStore_spec ?_ ?_
    · rintro σ σ1 hσ ⟨hcf, hA⟩
      have hidx1 : σ1.vars "idx" = σ.vars "idx" := hA.2.2.2 "idx" (by decide)
      have hz1 : σ1.arrs "z" = σ.arrs "z" := by rw [hA.1]
      have hil := hσ.2.2.1
      refine ⟨by rw [hidx1, hz1, hσ.2.1]; exact hσ.2.2.1, ?_, by rw [hidx1]; omega⟩
      rw [hcf]
      have := coefRaw_le I.clients (σ.vars "fr") (σ.vars "fc")
      omega
    · rintro σ σ1 σ2 hσ ⟨hcf, hA⟩ hσ2
      subst hσ2
      have hz1 : σ1.arrs "z" = σ.arrs "z" := by rw [hA.1]
      have hidx1 : σ1.vars "idx" = σ.vars "idx" := hA.2.2.2 "idx" (by decide)
      have hfr1 : σ1.vars "fr" = σ.vars "fr" := hA.2.2.2 "fr" (by decide)
      have hfc1 : σ1.vars "fc" = σ.vars "fc" := hA.2.2.2 "fc" (by decide)
      refine ⟨⟨fun a ha => ?_, hA.2.1, hA.2.2.1, fun y hy => ?_⟩, ?_⟩
      · have : a ≠ "z" := by simpa using ha
        simp [Env.setArr, this, hA.1]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        simp [Env.setArr, hA.2.2.2 y (by simpa using hy)]
      · simp [Env.setArr, hz1, hidx1, hcf, hfr1, hfc1]
  refine Spec.mono (Spec.seq (P' := CP I x k) hidx hin ?_ ?_) (by omega)
  · rintro σ σ1 ⟨⟨hC, hS, hol, hoe, hcl, hce, hzl, hil⟩, hi2, hlt⟩ ⟨hA, hfr, hfc, hct, hcs⟩
    have hidx1 : σ1.vars "idx" = σ.vars "idx" := hA.2.2.2 "idx" (by decide)
    have hq : σ.vars "idx" - 2 < nM I.clients * nN I.clients := by omega
    have hN := nN_pos I.clients
    refine ⟨⟨hC.agree hA (by decide) (by decide) (by decide),
      hS.agree hA (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      by rw [hA.1]; exact hol, fun c hc => by rw [hA.1]; exact hoe c hc, hct, hcs, ?_, ?_⟩,
      by rw [hA.1]; exact hzl, by rw [hidx1]; exact hil, by rw [hfr, hidx1], by rw [hfc, hidx1]⟩
    · rw [hfr, Nat.div_lt_iff_lt_mul hN]; exact hq
    · rw [hfc]; exact Nat.mod_lt _ hN
  · rintro σ σ1 σ2 ⟨⟨hC, hS, hol, hoe, hcl, hce, hzl, hil⟩, hi2, hlt⟩ ⟨hA, hfr, hfc, hct, hcs⟩ ⟨hA2, hz2⟩
    have hidx1 : σ1.vars "idx" = σ.vars "idx" := hA.2.2.2 "idx" (by decide)
    have hz1 : σ1.arrs "z" = σ.arrs "z" := by rw [hA.1]
    refine ⟨?_, ?_⟩
    · exact AgreeA.mono (AgreeA.trans (AgreeOff.toA hA) hA2) (by
        intro y hy; simp only [ZV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
        tauto) (by intro a ha; simp at ha ⊢; tauto)
    · rw [hz2, hz1, hidx1, hfr, hfc]

/-- The state before the entry of a right-hand side. -/
def PR (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  ZPre I x k σ ∧ 2 + nM I.clients * nN I.clients ≤ σ.vars "idx"

theorem rhsCom_spec (h : Bh I x k B) :
    Spec B (PR I x k) rhsCom
      (fun σ σ' => AgreeOff ["fr", "cf"] σ σ' ∧
        σ'.vars "cf" = rhsRaw I.clients I.days k (cntN I) (σ.vars "idx" - 2 - nM I.clients * nN I.clients))
      100 := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hmB := h.m_lt
  have hkB := h.k_lt
  run_vcg
  all_goals
    obtain ⟨⟨hC, hS, hol, hoe, hcl, hce, hzl, hil⟩, hge⟩ := ‹PR I x k _›
    have hMN : σ.vars "M" * σ.vars "N" = nM I.clients * nN I.clients := by rw [hS.M, hS.N]
    have hMv : σ.vars "M" < B := by rw [hS.M]; omega
    have hNv : σ.vars "N" < B := by rw [hS.N]; omega
    have hcntle : ∀ r, cntN I r ≤ I.days := fun r => (Finset.card_filter_le _ _).trans (by simp)
  all_goals try refine ⟨⟨rfl, rfl, rfl, fun y hy => ?_⟩, ?_⟩
  all_goals try
    (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
     simp [Env.setVar, hy.1, hy.2])
  all_goals try simp [Env.setVar, rhsRaw, hS.T, hC.m, hC.k, hMN]
  all_goals try omega
  all_goals try simp_all [rhsRaw, hS.T, hC.m, hC.k, hMN, hce]
  all_goals try (exact lt_of_le_of_lt (hcntle _) hmB)

theorem rhsPart_spec (h : Bh I x k B) :
    Spec B (PR I x k) rhsPart
      (fun σ σ' => AgreeA ZV ["z"] σ σ' ∧
        σ'.arrs "z" = (σ.arrs "z").set (σ.vars "idx")
          (rhsRaw I.clients I.days k (cntN I) (σ.vars "idx" - 2 - nM I.clients * nN I.clients)))
      (100 + 10) := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hB3 : 2 < B := by have := h.mn_le; omega
  have hmB := h.m_lt
  have hkB := h.k_lt
  have hcntle : ∀ r, cntN I r ≤ I.days := fun r => (Finset.card_filter_le _ _).trans (by simp)
  unfold rhsPart
  refine Spec.seq (P' := fun σ => σ.vars "idx" < (σ.arrs "z").length ∧ σ.vars "cf" < B ∧
    σ.vars "idx" < B) (Spec.pre (rhsCom_spec h) (fun σ (hσ : PR I x k σ) => hσ)) zStore_spec ?_ ?_
  · rintro σ σ1 hσ ⟨hA, hcf⟩
    have hidx1 : σ1.vars "idx" = σ.vars "idx" := hA.2.2.2 "idx" (by decide)
    have hz1 : σ1.arrs "z" = σ.arrs "z" := by rw [hA.1]
    obtain ⟨⟨hC, hS, hol, hoe, hcl, hce, hzl, hil⟩, hge⟩ := hσ
    refine ⟨by rw [hidx1, hz1, hzl]; exact hil, ?_, by rw [hidx1]; omega⟩
    rw [hcf]
    unfold rhsRaw
    split_ifs
    · exact lt_of_le_of_lt (hcntle _) hmB
    · omega
  · rintro σ σ1 σ2 hσ ⟨hA, hcf⟩ hσ2
    subst hσ2
    have hz1 : σ1.arrs "z" = σ.arrs "z" := by rw [hA.1]
    have hidx1 : σ1.vars "idx" = σ.vars "idx" := hA.2.2.2 "idx" (by decide)
    refine ⟨⟨fun a ha => ?_, hA.2.1, hA.2.2.1, fun y hy => ?_⟩, ?_⟩
    · have : a ≠ "z" := by simpa using ha
      simp [Env.setArr, this, hA.1]
    · simp only [ZV, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [Env.setArr, hA.2.2.2 y (by simp; tauto)]
    · simp [Env.setArr, hz1, hidx1, hcf]

theorem zBody_spec (h : Bh I x k B) :
    Spec B (ZPre I x k) zBody
      (fun σ σ' => AgreeA ZV ["z"] σ σ' ∧
        σ'.arrs "z" = (σ.arrs "z").set (σ.vars "idx") (zFunRaw I.clients I.days k (cntN I) (σ.vars "idx")))
      (10 + 10 + 10 + (100 + 10) + 100 + 10) := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hB3 : 2 < B := by have := h.mn_le; omega
  unfold zBody
  run_vcg [coefPart_spec h, rhsPart_spec h]
  all_goals
    have hZ : ZPre I x k σ := ‹_›
    obtain ⟨hC, hS, hol, hoe, hcl, hce, hzl, hil⟩ := hZ
    have hMN : σ.vars "M" * σ.vars "N" = nM I.clients * nN I.clients := by rw [hS.M, hS.N]
    have hMv : σ.vars "M" < B := by rw [hS.M]; omega
    have hNv : σ.vars "N" < B := by rw [hS.N]; omega
    have hidxB : σ.vars "idx" < B := by omega
    have hMNle : 2 + nM I.clients * nN I.clients ≤ zLen I.clients := by simp only [zLen]; omega
  all_goals try omega
  all_goals try (rw [hMN]; omega)
  all_goals try
    (refine ⟨⟨hC, hS, hol, hoe, hcl, hce, hzl, hil⟩, ?_, ?_⟩ <;> rw [← hMN] at * <;> omega)
  all_goals try
    (refine ⟨⟨hC, hS, hol, hoe, hcl, hce, hzl, hil⟩, ?_⟩; rw [← hMN] at *; omega)
  all_goals try
    (refine ⟨?_, ?_⟩
     · exact ⟨fun a ha => by simp [Env.setArr, (by simpa using ha : a ≠ "z")], rfl, rfl,
         fun y hy => rfl⟩
     · simp [Env.setArr, zFunRaw, hS.N, hS.M, *])
  all_goals try
    (obtain ⟨hAg, hzeq⟩ := ‹AgreeA ZV ["z"] σ _ ∧ _›
     refine ⟨hAg, ?_⟩
     rw [hzeq]
     have hc' : ¬ σ.vars "idx" < 2 + nM I.clients * nN I.clients := by
       rw [← hMN]; assumption
     simp only [zFunRaw, if_neg hc', *]
     simp_all)
  all_goals try
    (obtain ⟨hAg, hzeq⟩ := ‹AgreeA ZV ["z"] σ _ ∧ _›
     refine ⟨hAg, ?_⟩
     rw [hzeq]
     have hc' : σ.vars "idx" < 2 + nM I.clients * nN I.clients := by
       rw [← hMN]; assumption
     simp only [zFunRaw, if_pos hc', *]
     simp_all)

end Lax117284Proofs.Machine.ClBuild
