import Lax117284Proofs.Machine.ClBuildCnt

/-!
The table of counts: for every day, the number of its type is computed and the entry of the table
is incremented.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- One day: its type number, then the increment of the entry. -/
def dayBody : Com := seqs [typeLoop, .store "cnt" (V "tt") (add (.get "cnt" (V "tt")) (lit 1)),
  asg "ci" (add (V "ci") (lit 1))]

/-- The table of counts of the days below `ci`. -/
def cntCom : Com := seqs [asg "ci" (lit 0), .while (.lt (V "ci") (V "m")) dayBody]

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The invariant of the loop over the days. -/
def CInv (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ci" ≤ I.days ∧ (σ.arrs "cnt").length = nT I.clients ∧
    ∀ t < nT I.clients, (σ.arrs "cnt").getD t 0 =
      ((range (σ.vars "ci")).filter fun i' => typeNum I i' = t).card

/-- The store and the increment. -/
def bumpCom : Com := seqs [.store "cnt" (V "tt") (add (.get "cnt" (V "tt")) (lit 1)),
  asg "ci" (add (V "ci") (lit 1))]

theorem bump_spec :
    Spec B (fun σ => σ.vars "tt" < (σ.arrs "cnt").length ∧ (σ.arrs "cnt").getD (σ.vars "tt") 0 + 1 < B ∧
        σ.vars "ci" + 1 < B ∧ σ.vars "tt" < B) bumpCom
      (fun σ σ' => σ' = (σ.setArr "cnt" (σ.vars "tt") ((σ.arrs "cnt").getD (σ.vars "tt") 0 + 1)).setVar
        "ci" (σ.vars "ci" + 1)) 20 := by
  run_vcg
  all_goals try rfl

theorem dayBody_eq : dayBody = .seq typeLoop bumpCom := rfl

theorem typeAll_spec (h : Bh I x k B) :
    Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ci" < I.days) typeLoop
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧ σ'.vars "ci" = σ.vars "ci" ∧
        σ'.vars "tt" = typeNum I (σ.vars "ci") ∧ AgreeOff TL σ σ')
      (((200 + 4) * (I.clients * I.clients) + 6) + 2) := by
  intro σ ⟨hC, hS, hci⟩
  obtain ⟨σ', hr, hq⟩ := typeLoop_spec h (σ.vars "ci") hci σ ⟨hC, hS, rfl⟩
  exact ⟨σ', hr, hq.1, hq.2.1, by rw [hq.2.2.1], hq.2.2.2.1, hq.2.2.2.2⟩

theorem card_filter_succ (f : ℕ → ℕ) (t i : ℕ) :
    ((range (i + 1)).filter fun i' => f i' = t).card =
      ((range i).filter fun i' => f i' = t).card + if f i = t then 1 else 0 := by
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : f i = t
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp), if_pos h]
  · rw [if_neg h, if_neg h]; simp

theorem getD_set_ite (l : List ℕ) (i v t : ℕ) (hi : i < l.length) :
    (l.set i v).getD t 0 = if t = i then v else l.getD t 0 := by
  by_cases h : t = i
  · subst h; simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hi]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h), h]

theorem dayBody_spec (h : Bh I x k B) :
    Spec B (fun σ => CInv I x k σ ∧ σ.vars "ci" < I.days) dayBody
      (fun σ σ' => CInv I x k σ' ∧ σ'.vars "ci" = σ.vars "ci" + 1)
      (204 * (I.clients * I.clients) + 40) := by
  have hmB := h.m_lt
  have hnnB := h.nn_lt
  have hnT := h.nT_lt
  rw [dayBody_eq]
  have hT := Spec.pre (typeAll_spec h) (fun σ (hσ : CInv I x k σ ∧ σ.vars "ci" < I.days) =>
    (⟨hσ.1.1, hσ.1.2.1, hσ.2⟩ : Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ci" < I.days))
  refine Spec.mono (Spec.seq (P' := fun σ => σ.vars "tt" < (σ.arrs "cnt").length ∧
      (σ.arrs "cnt").getD (σ.vars "tt") 0 + 1 < B ∧ σ.vars "ci" + 1 < B ∧ σ.vars "tt" < B)
    hT bump_spec ?_ ?_) (by omega)
  · rintro σ σ1 ⟨hCI, hlt⟩ ⟨hC1, hS1, hci1, htt1, hA⟩
    obtain ⟨hC, hS, hcile, hlen, hcnt⟩ := hCI
    have harr : σ1.arrs "cnt" = σ.arrs "cnt" := by rw [hA.1]
    have hty := typeNum_lt I (σ.vars "ci")
    have hcardle : ((range (σ.vars "ci")).filter fun i' => typeNum I i' = typeNum I (σ.vars "ci")).card
        ≤ σ.vars "ci" := by
      refine le_trans (Finset.card_filter_le _ _) (by simp)
    refine ⟨by rw [htt1, harr, hlen]; exact hty, ?_, by omega, by rw [htt1]; omega⟩
    rw [htt1, harr, hcnt _ hty]
    omega
  · rintro σ σ1 σ2 ⟨hCI, hlt⟩ ⟨hC1, hS1, hci1, htt1, hA⟩ hσ2
    obtain ⟨hC, hS, hcile, hlen, hcnt⟩ := hCI
    have harr : σ1.arrs "cnt" = σ.arrs "cnt" := by rw [hA.1]
    have hci1' : σ1.vars "ci" = σ.vars "ci" := hci1
    have hty := typeNum_lt I (σ.vars "ci")
    subst hσ2
    have hlen1 : σ1.vars "tt" < (σ1.arrs "cnt").length := by rw [htt1, harr, hlen]; exact hty
    have hlen1' : ((σ1.arrs "cnt").set (σ1.vars "tt") ((σ1.arrs "cnt").getD (σ1.vars "tt") 0 + 1)).length = (σ.arrs "cnt").length := by
      rw [List.length_set, harr]
    have hents : ∀ t < nT I.clients,
        ((σ1.arrs "cnt").set (σ1.vars "tt") ((σ1.arrs "cnt").getD (σ1.vars "tt") 0 + 1)).getD t 0 =
          ((range (σ.vars "ci" + 1)).filter fun i' => typeNum I i' = t).card := by
      intro t ht
      rw [getD_set_ite _ _ _ _ hlen1, htt1, harr, card_filter_succ, hcnt t ht]
      by_cases hte : t = typeNum I (σ.vars "ci")
      · subst hte
        rw [if_pos rfl, if_pos rfl, hcnt _ ht]
      · rw [if_neg hte, if_neg (fun e => hte e.symm)]; simp
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
    all_goals simp [Env.setVar, Env.setArr, hC1.X, hC1.n, hC1.m, hC1.k, hS1.nn, hS1.T, hS1.Z,
      hS1.Vv, hS1.N, hS1.M, hS1.zl, hci1']
    · omega
    · rw [harr, hlen]
    · intro t ht
      simpa [List.getD_eq_getElem?_getD, hci1'] using hents t ht

/-- The scalars and arrays the table loop may change. -/
def CV : List String := "ci" :: TL
def CA : List String := ["cnt"]

theorem cntCom_frame : (∀ y ∈ cntCom.wvars, y ∈ CV) ∧ (∀ a ∈ cntCom.warrs, a ∈ CA) ∧
    ¬ cntCom.reads ∧ cntCom.NoWrite := by
  exact ⟨by decide, by decide, by decide, by decide⟩

theorem cntCom_spec (h : Bh I x k B) :
    Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.arrs "cnt" = List.replicate (nT I.clients) 0)
      cntCom
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧ (σ'.arrs "cnt").length = nT I.clients ∧
        (∀ t < nT I.clients, (σ'.arrs "cnt").getD t 0 = cntN I t) ∧ AgreeA CV CA σ σ')
      (((204 * (I.clients * I.clients) + 40) + 4) * I.days + 6) := by
  have hmB := h.m_lt
  have hloop := Spec.forRangeZero (B := B) (c := dayBody) "ci" "m" (CInv I x k) I.days
    (204 * (I.clients * I.clients) + 40) hmB (fun σ hσ => hσ.2.2.1) (fun σ hσ => hσ.1.m)
    (dayBody_spec h)
  have hfr := Spec.frame hloop
  obtain ⟨hv, ha, hr, hw⟩ := cntCom_frame
  have hpre : ∀ σ : Env, (Ctx0 I x k σ ∧ Sizes I σ ∧ σ.arrs "cnt" = List.replicate (nT I.clients) 0) →
      CInv I x k (σ.setVar "ci" 0) := by
    rintro σ ⟨hC, hS, hcnt⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals simp [Env.setVar, hC.X, hC.n, hC.m, hC.k, hS.nn, hS.T, hS.Z, hS.Vv, hS.N, hS.M, hS.zl,
      hcnt]
  refine Spec.conseq hfr hpre ?_ le_rfl
  rintro σ σ' hσ ⟨⟨⟨hC, hS, hle, hlen, hcnt⟩, hci⟩, hf1, hf2, hf3, hf4⟩
  refine ⟨hC, hS, hlen, fun t ht => ?_, agreeA_of_frame hv ha hr hw hf1 hf2 hf3 hf4⟩
  rw [hcnt t ht, hci]; rfl

end Lax117284Proofs.Machine.ClBuild
