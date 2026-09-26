import Lax117284Proofs.Machine.ClBuildOk

/-!
The table of independent pairs: the loop over the positions gives the flag of one pair, the loop
over the columns fills the table.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The scalars the flag loop may change. -/
def OL : List String := ["fg", "q", "qa", "qb", "bd"]

theorem okInner_frame : ∀ (c : Com), c = (Com.seq (.assign "q" (.lit 0))
      (.while (.lt (.var "q") (.var "nn")) okStep)) →
    (∀ y ∈ c.wvars, y ∈ OL) ∧ (∀ a ∈ c.warrs, False) ∧ ¬ c.reads ∧ c.NoWrite := by
  intro c hc
  subst hc
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro a ha
  have : (Com.seq (.assign "q" (.lit 0)) (.while (.lt (.var "q") (.var "nn")) okStep)).warrs = [] := by
    decide
  rw [this] at ha; simp at ha

theorem okInner_spec (h : Bh I x k B) (c : ℕ) (hc : c < nV I.clients) :
    Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ct" = c / nZ I.clients ∧
        σ.vars "cs" = c % nZ I.clients) okInner
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧ σ'.vars "ct" = c / nZ I.clients ∧
        σ'.vars "cs" = c % nZ I.clients ∧
        σ'.vars "fg" = (if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0) ∧
        AgreeOff OL σ σ') (((200 + 4) * (I.clients * I.clients) + 6) + 2) := by
  have hnnB := h.nn_lt
  have hloop := Spec.forRangeZero (B := B) (c := okStep) "q" "nn" (OInv I x k c)
    (I.clients * I.clients) 200 hnnB (fun σ hσ => hσ.2.2.2.2.1) (fun σ hσ => hσ.2.1.nn)
    (okStep_spec h c hc)
  have hfr := Spec.frame hloop
  have hasg : Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ct" = c / nZ I.clients ∧
      σ.vars "cs" = c % nZ I.clients) (asg "fg" (lit 1)) (fun σ σ' => σ' = σ.setVar "fg" 1) (1 + 1) := by
    have := Spec.assign (B := B) (P := fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧
      σ.vars "ct" = c / nZ I.clients ∧ σ.vars "cs" = c % nZ I.clients)
      (x := "fg") (e := lit 1) (f := fun _ => 1) (fun σ _ => evalB_lit (by have := h.hL; have := h.mn_le; omega))
    simpa using this
  unfold okInner
  refine Spec.mono (Spec.seq (P' := fun σ => OInv I x k c (σ.setVar "q" 0)) hasg hfr ?_ ?_)
    (by simp [Expr.size]; omega)
  · rintro σ σ1 ⟨hC, hS, hct, hcs⟩ rfl
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    all_goals simp [Env.setVar, hC.X, hC.n, hC.m, hC.k, hS.nn, hS.T, hS.Z, hS.Vv, hS.N, hS.M, hS.zl,
      hct, hcs]
  · rintro σ σ1 σ2 ⟨hC, hS, hct, hcs⟩ rfl ⟨⟨hT, hq⟩, hf1, hf2, hf3, hf4⟩
    obtain ⟨hv, ha, hr, hw⟩ := okInner_frame _ rfl
    have hA1 : AgreeOff ["fg"] σ (σ.setVar "fg" 1) :=
      ⟨rfl, rfl, rfl, fun y hy => by simp at hy; simp [Env.setVar, hy]⟩
    have hA2 := agree_of_frame_gen hv ha hr hw hf1 hf2 hf3 hf4
    obtain ⟨hT1, hT2, hT3, hT4, hT5, hT6⟩ := hT
    refine ⟨hT1, hT2, hT3, hT4, ?_, AgreeOff.mono' (AgreeOff.trans' hA1 hA2) ?_⟩
    · rw [hT6, hq]
      have := indepB_iff_q I.clients (c / nZ I.clients) (c % nZ I.clients)
      by_cases hb : indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true
      · rw [if_pos hb, if_pos (this.mp hb)]
      · rw [if_neg hb, if_neg (fun hh => hb (this.mpr hh))]
    · intro y hy
      simp only [OL, List.mem_append, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      tauto

theorem okBump_spec :
    Spec B (fun σ => σ.vars "cc" < (σ.arrs "okt").length ∧ σ.vars "fg" < B ∧ σ.vars "cc" + 1 < B ∧
        σ.vars "cc" < B) okBump
      (fun σ σ' => σ' = (σ.setArr "okt" (σ.vars "cc") (σ.vars "fg")).setVar "cc" (σ.vars "cc" + 1)) 20 := by
  run_vcg
  all_goals try rfl

/-- The invariant of the loop over the columns. -/
def OkInv (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "cc" ≤ nV I.clients ∧ (σ.arrs "okt").length = nV I.clients ∧
    ∀ c < σ.vars "cc", (σ.arrs "okt").getD c 0 =
      if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0

theorem okSplit_spec (h : Bh I x k B) :
    Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "cc" < nV I.clients)
      (.seq (asg "ct" (dv (V "cc") (V "Z"))) (asg "cs" (sub (V "cc") (mul (V "ct") (V "Z")))))
      (fun σ σ' => AgreeOff ["ct", "cs"] σ σ' ∧ σ'.vars "ct" = σ.vars "cc" / nZ I.clients ∧
        σ'.vars "cs" = σ.vars "cc" % nZ I.clients) 20 := by
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
    have hcc : σ.vars "cc" < nV I.clients := ‹_›
    have hd1 : σ.vars "cc" / nZ I.clients ≤ σ.vars "cc" := Nat.div_le_self _ _
    have hd2 : σ.vars "cc" / nZ I.clients * nZ I.clients ≤ σ.vars "cc" := Nat.div_mul_le_self _ _
  all_goals try refine ⟨⟨rfl, rfl, rfl, fun y hy => ?_⟩, ?_, ?_⟩
  all_goals try
    (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
     simp [Env.setVar, hy.1, hy.2])
  all_goals try simp [Env.setVar, hS.Z, hmod]
  all_goals try omega

/-- The state between the phases of the body. -/
def OkMid (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  OkInv I x k σ ∧ σ.vars "cc" < nV I.clients ∧ σ.vars "ct" = σ.vars "cc" / nZ I.clients ∧
    σ.vars "cs" = σ.vars "cc" % nZ I.clients

theorem okBody_spec (h : Bh I x k B) :
    Spec B (fun σ => OkInv I x k σ ∧ σ.vars "cc" < nV I.clients) okBody
      (fun σ σ' => OkInv I x k σ' ∧ σ'.vars "cc" = σ.vars "cc" + 1)
      (((200 + 4) * (I.clients * I.clients) + 6) + 2 + 60) := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hB3 : 2 < B := by have := h.mn_le; omega
  unfold okBody
  have hS1 := Spec.pre (okSplit_spec h) (fun σ (hσ : OkInv I x k σ ∧ σ.vars "cc" < nV I.clients) =>
    (⟨hσ.1.1, hσ.1.2.1, hσ.2⟩ : Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "cc" < nV I.clients))
  have hS2 : Spec B (fun σ => OkMid I x k σ) okInner
      (fun σ σ' => OkInv I x k σ' ∧ σ'.vars "cc" = σ.vars "cc" ∧ σ'.vars "cc" < nV I.clients ∧
        σ'.vars "fg" = (if indepB I.clients (σ.vars "cc" / nZ I.clients) (σ.vars "cc" % nZ I.clients) = true
          then 1 else 0)) (((200 + 4) * (I.clients * I.clients) + 6) + 2) := by
    intro σ hσ
    obtain ⟨hOK, hlt, hct, hcs⟩ := hσ
    obtain ⟨σ', hr, hq⟩ := okInner_spec h (σ.vars "cc") hlt σ ⟨hOK.1, hOK.2.1, hct, hcs⟩
    obtain ⟨hC', hS', hct', hcs', hfg', hA⟩ := hq
    have hlt' : σ'.vars "cc" = σ.vars "cc" := hA.2.2.2 "cc" (by decide)
    refine ⟨σ', hr, ⟨⟨hC', hS', ?_, ?_, ?_⟩, hlt', by rw [hlt']; exact hlt, hfg'⟩⟩
    · rw [hlt']; exact hOK.2.2.1
    · rw [hA.1]; exact hOK.2.2.2.1
    · intro c hc
      rw [hA.1, hlt'] at *
      exact hOK.2.2.2.2 c (by rw [← hlt']; exact hc)
  have hS3 : Spec B (fun σ => OkInv I x k σ ∧ σ.vars "cc" < nV I.clients ∧
      σ.vars "fg" = (if indepB I.clients (σ.vars "cc" / nZ I.clients) (σ.vars "cc" % nZ I.clients) = true
        then 1 else 0)) okBump
      (fun σ σ' => OkInv I x k σ' ∧ σ'.vars "cc" = σ.vars "cc" + 1) 20 := by
    intro σ ⟨hOK, hlt, hfg⟩
    obtain ⟨hC, hS, hle, hlen, hent⟩ := hOK
    have hcc : σ.vars "cc" < (σ.arrs "okt").length := by rw [hlen]; exact hlt
    have hfgB : σ.vars "fg" < B := by rw [hfg]; split_ifs <;> omega
    obtain ⟨σ', hr, hσ'⟩ := okBump_spec σ ⟨hcc, hfgB, by omega, by omega⟩
    refine ⟨σ', hr, ?_, by rw [hσ']; rfl⟩
    subst hσ'
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals simp [Env.setVar, Env.setArr, hC.X, hC.n, hC.m, hC.k, hS.nn, hS.T, hS.Z, hS.Vv, hS.N,
      hS.M, hS.zl]
    · omega
    · rw [hlen]
    · intro c hc
      by_cases hce : c = σ.vars "cc"
      · subst hce
        simp [List.getElem?_set_self hcc, hfg]
      · have hlt' : c < σ.vars "cc" := by omega
        rw [List.getElem?_set_ne (Ne.symm hce)]
        simpa [List.getD_eq_getElem?_getD] using hent c hlt'
  have hS23 : Spec B (OkMid I x k) (.seq okInner okBump)
      (fun σ σ' => OkInv I x k σ' ∧ σ'.vars "cc" = σ.vars "cc" + 1)
      ((((200 + 4) * (I.clients * I.clients) + 6) + 2) + 20) := by
    refine Spec.seq (P' := fun σ => OkInv I x k σ ∧ σ.vars "cc" < nV I.clients ∧
      σ.vars "fg" = (if indepB I.clients (σ.vars "cc" / nZ I.clients) (σ.vars "cc" % nZ I.clients) = true
        then 1 else 0)) hS2 hS3 ?_ ?_
    · rintro σ σ1 hσ ⟨hOK1, hcc1, hlt1, hfg1⟩
      exact ⟨hOK1, hlt1, by rw [hcc1]; exact hfg1⟩
    · rintro σ σ1 σ2 hσ ⟨hOK1, hcc1, hlt1, hfg1⟩ ⟨hOK2, hcc2⟩
      exact ⟨hOK2, by rw [hcc2, hcc1]⟩
  refine Spec.mono (Spec.seq (P' := OkMid I x k) hS1 hS23 ?_ ?_) (by omega)
  · rintro σ σ1 ⟨⟨hC, hS, hle, hlen, hent⟩, hlt⟩ ⟨hA, hct, hcs⟩
    have hcc1 : σ1.vars "cc" = σ.vars "cc" := hA.2.2.2 "cc" (by decide)
    refine ⟨⟨hC.agree hA (by decide) (by decide) (by decide),
      hS.agree hA (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      by rw [hcc1]; exact hle, by rw [hA.1]; exact hlen, ?_⟩, by rw [hcc1]; exact hlt,
      by rw [hct, hcc1], by rw [hcs, hcc1]⟩
    intro c hc
    rw [hA.1]
    exact hent c (by rw [← hcc1]; exact hc)
  · rintro σ σ1 σ2 hσ hQ1 ⟨hOK2, hcc2⟩
    have hcc1 : σ1.vars "cc" = σ.vars "cc" := hQ1.1.2.2.2 "cc" (by decide)
    exact ⟨hOK2, by rw [hcc2, hcc1]⟩

/-- The scalars and arrays the table loop may change. -/
def OV : List String := "cc" :: "ct" :: "cs" :: OL
def OA : List String := ["okt"]

theorem okCom_frame : (∀ y ∈ okCom.wvars, y ∈ OV) ∧ (∀ a ∈ okCom.warrs, a ∈ OA) ∧
    ¬ okCom.reads ∧ okCom.NoWrite := by
  exact ⟨by decide, by decide, by decide, by decide⟩

theorem okCom_spec (h : Bh I x k B) :
    Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.arrs "okt" = List.replicate (nV I.clients) 0)
      okCom
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧ (σ'.arrs "okt").length = nV I.clients ∧
        (∀ c < nV I.clients, (σ'.arrs "okt").getD c 0 =
          if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0) ∧
        AgreeA OV OA σ σ')
      ((((200 + 4) * (I.clients * I.clients) + 6) + 2 + 60 + 4) * nV I.clients + 6) := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hVB : nV I.clients < B := by omega
  have hloop := Spec.forRangeZero (B := B) (c := okBody) "cc" "Vv" (OkInv I x k) (nV I.clients)
    (((200 + 4) * (I.clients * I.clients) + 6) + 2 + 60) hVB (fun σ hσ => hσ.2.2.1)
    (fun σ hσ => hσ.2.1.Vv) (okBody_spec h)
  have hfr := Spec.frame hloop
  obtain ⟨hv, ha, hr, hw⟩ := okCom_frame
  have hpre : ∀ σ : Env, (Ctx0 I x k σ ∧ Sizes I σ ∧ σ.arrs "okt" = List.replicate (nV I.clients) 0) →
      OkInv I x k (σ.setVar "cc" 0) := by
    rintro σ ⟨hC, hS, hok⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals simp [Env.setVar, hC.X, hC.n, hC.m, hC.k, hS.nn, hS.T, hS.Z, hS.Vv, hS.N, hS.M, hS.zl,
      hok]
  refine Spec.conseq hfr hpre ?_ le_rfl
  rintro σ σ' hσ ⟨⟨⟨hC, hS, hle, hlen, hent⟩, hcc⟩, hf1, hf2, hf3, hf4⟩
  refine ⟨hC, hS, hlen, fun c hc => ?_, agreeA_of_frame hv ha hr hw hf1 hf2 hf3 hf4⟩
  exact hent c (by rw [hcc]; exact hc)

end Lax117284Proofs.Machine.ClBuild
