import Lax117284Proofs.Treewidth.Chars.RealizeWhole

/-!
# `winPlans` is realised by `processRun` (work package C5, part 10)
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem forall2_imp_mem {α β : Type} {R R' : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') (hi : ∀ a ∈ l, ∀ b, R a b → R' a b) : List.Forall₂ R' l l' := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b l l' hab _ ih =>
    exact List.Forall₂.cons (hi a List.mem_cons_self b hab) (ih (fun a' ha' b' h' => hi a' (List.mem_cons_of_mem _ ha') b' h'))

theorem win_claim (v : ℕ) (B : Finset ℕ) (hvB : v ∉ B) : ∀ x : AR, RunOk v B x →
    ∀ (pre : Option Cut) (w : WPlan) (rep : CT) (cov : Finset ℕ),
      PreOk (typical (csz x.chain)).length pre →
      (w, rep, cov) ∈ winPlans v (preLo pre) (AR.charF Finset.card x) →
      PRC v B x (processRun v pre w x) (topRep x.S (typical (csz x.chain)) pre rep) cov pre.isSome := by
  intro x
  induction x using AR.ind with
  | _ S ns ks ih =>
    intro hx pre w rep cov hpre hmem
    have hc : AR.charF Finset.card (.run S ns ks) =
        CT.node S (typical (csz ns)) (ks.map (AR.charF Finset.card)) := AR.charF_run _ _ _ _
    rw [hc] at hmem
    simp only [AR.S, AR.chain] at *
    simp only [winPlans, List.mem_append, List.mem_map] at hmem
    rcases hmem with (⟨f, hf, h⟩ | ⟨f, hf, h⟩) | ⟨combo, hcombo, h⟩
    · -- end, first type
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [List.mem_range'_1] at hf
      have hv : (Cut.t1 f).Valid (typical (csz ns)).length := by simp only [CT.Cut.Valid]; omega
      have hlh : LoHi pre (.endAt (Cut.t1 f)) := by
        cases pre with
        | none => trivial
        | some c1 => show cLo c1 ≤ f; have : preLo (some c1) = cLo c1 := rfl; omega
      exact pr_end v B S ns ks hvB hx pre (Cut.t1 f) hpre hv hlh
    · -- end, second type
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [List.mem_range'_1] at hf
      have hv : (Cut.t2 f).Valid (typical (csz ns)).length := by simp only [CT.Cut.Valid]; omega
      have hlh : LoHi pre (.endAt (Cut.t2 f)) := by
        cases pre with
        | none => trivial
        | some c1 => show cLo c1 ≤ f; have : preLo (some c1) = cLo c1 := rfl; omega
      exact pr_end v B S ns ks hvB hx pre (Cut.t2 f) hpre hv hlh
    · -- whole
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hkids := (runOk_run hx).2.2.1
      have h2 := (kidChoices_forall2 v _ _).1 hcombo
      rw [List.forall₂_map_left_iff] at h2
      have hkc : List.Forall₂ (fun k o => KC v B k (applyOpt v o.1 k) o.2.1 o.2.2) ks combo := by
        refine forall2_imp_mem h2 ?_
        intro k hk o ho
        rcases ho with ⟨h1, h2, h3⟩ | ⟨wp, h1, h2⟩
        · rw [h1, applyOpt, h2, h3]
          exact kc_unchanged hvB (hkids k hk)
        · rw [h1, applyOpt]
          have := ih k hk (hkids k hk) none wp o.2.1 o.2.2 (by simp [PreOk]) (by simpa [preLo] using h2)
          simpa [topRep] using this.kc
      exact pr_whole v B S ns ks hvB hx pre combo hpre hkc

end Lax117284Proofs.Treewidth.Chars
