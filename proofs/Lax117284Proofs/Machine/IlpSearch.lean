import Lax117284Proofs.Machine.IlpOdo

/-!
The search: every number below `R ^ D` is decoded and tested.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

theorem foundUpd_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => σ.vars "ok" ≤ 1)
      (.ite (.eq (V "ok") (lit 1)) (asg "found" (lit 1)) .skip)
      (fun σ σ' => σ'.vars "found" = if σ.vars "ok" = 1 then 1 else σ.vars "found") 20 := by
  run_vcg
  all_goals
    have hB5 := hb.five_lt_B
    have hok : σ.vars "ok" ≤ 1 := ‹σ.vars "ok" ≤ 1›
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | (split_ifs <;> omega))

theorem doneAssign_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => σ.vars "cy" ≤ 1) (asg "done" (V "cy"))
      (fun σ σ' => σ' = σ.setVar "done" (σ.vars "cy")) 20 := by
  run_vcg
  all_goals
    have hB5 := hb.five_lt_B
    have hcy : σ.vars "cy" ≤ 1 := ‹σ.vars "cy" ≤ 1›
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | rfl)

theorem found_step (P : ℕ → Prop) (t : ℕ) :
    (if P t then 1 else if ∃ t' < t, P t' then 1 else 0) = if ∃ t' < t + 1, P t' then 1 else 0 := by
  by_cases h : P t
  · rw [if_pos h, if_pos]
    exact ⟨t, by omega, h⟩
  · rw [if_neg h]
    by_cases h2 : ∃ t' < t, P t'
    · rw [if_pos h2, if_pos]
      obtain ⟨t', ht', hp⟩ := h2
      exact ⟨t', by omega, hp⟩
    · rw [if_neg h2, if_neg]
      rintro ⟨t', ht', hp⟩
      by_cases hh : t' = t
      · subst hh; exact h hp
      · exact h2 ⟨t', by omega, hp⟩

/-- The cost of a turn of the search. -/
def Kturn (n : ℕ) : ℕ := Keval n + 20 + (2 + ((40 + 4) * Dn n + 6)) + 20

theorem digitsOf_le_K (n t q : ℕ) : digitsOf (Rd n) t q ≤ Kn n := by
  have h := digitsOf_lt (R := Rd n) (by unfold Rd; omega) t q
  have e : Rd n = Kn n + 1 := rfl
  omega

/-- **One turn of the search.** -/
theorem searchBody_step {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (t : ℕ)
    (ht : t < Rd n ^ Dn n) (σ : Env) (hC : Ctx n cnt bb σ)
    (hdg : σ.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) t))
    (hfound : σ.vars "found" = if ∃ t' < t, AccT n cnt bb t' then 1 else 0) :
    ∃ σ', Run B searchBody σ σ' (Kturn n) ∧ Ctx n cnt bb σ' ∧
      ((t + 1 < Rd n ^ Dn n ∧ σ'.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) (t + 1)) ∧
          σ'.vars "done" = 0 ∧ σ'.vars "found" = if ∃ t' < t + 1, AccT n cnt bb t' then 1 else 0) ∨
        (t + 1 = Rd n ^ Dn n ∧ σ'.vars "done" = 1 ∧
          σ'.vars "found" = if ∃ t' < Rd n ^ Dn n, AccT n cnt bb t' then 1 else 0)) := by
  have hv := fun q (_ : q < Dn n) => digitsOf_le_K n t q
  obtain ⟨σ1, r1, ⟨hC1, hok1⟩, hv1, ha1, -, -⟩ :=
    (evalCom_spec hb (digitsOf (Rd n) t) hv).frame σ ⟨hC, hdg⟩
  have hdg1 : σ1.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) t) := hC1.2
  have hC1' : Ctx n cnt bb σ1 := hC1.1
  have hfound1 : σ1.vars "found" = σ.vars "found" := hv1 "found" (by decide)
  have hok1' : σ1.vars "ok" ≤ 1 := by rw [hok1]; split_ifs <;> omega
  obtain ⟨σ2, r2, hfnd2⟩ := foundUpd_vals hb σ1 hok1'
  obtain ⟨σ2, r2, hfnd2, hk2⟩ := spec_keeps (foundUpd_vals hb) σ1 hok1'
  have hC2 : Ctx n cnt bb σ2 :=
    (Ctx.stable (c := .ite (.eq (V "ok") (lit 1)) (asg "found" (lit 1)) .skip)
      (by decide) (by decide)) σ1 σ2 hC1' hk2
  have hdg2 : σ2.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) t) := by
    rw [hk2.2.1 "dg" (by decide)]; exact hdg1
  have hfound2 : σ2.vars "found" =
      if AccT n cnt bb t then 1 else (if ∃ t' < t, AccT n cnt bb t' then 1 else 0) := by
    rw [hfnd2, hfound1, hfound, hok1]
    by_cases h : AccSpec n cnt bb (certVec n (digitsOf (Rd n) t))
    · have h' : AccT n cnt bb t := h
      simp [h, h']
    · have h' : ¬ AccT n cnt bb t := h
      simp [h, h']
  obtain ⟨σ3, r3, ⟨hC3, hcy3, hdg3⟩, hv3, ha3, -, -⟩ :=
    (odoCom_spec hb t ht).frame σ2 ⟨hC2, hdg2⟩
  have hfound3 : σ3.vars "found" = σ2.vars "found" := hv3 "found" (by decide)
  have hcy3' : σ3.vars "cy" ≤ 1 := by rw [hcy3]; split_ifs <;> omega
  obtain ⟨σ4, r4, e4⟩ := doneAssign_vals hb σ3 hcy3'
  have hC4 : Ctx n cnt bb σ4 := by rw [e4]; exact hC3.setVar (by decide) _
  have hfound4 : σ4.vars "found" = σ3.vars "found" := by rw [e4]; simp [Env.setVar]
  have hdone4 : σ4.vars "done" = σ3.vars "cy" := by rw [e4]; simp [Env.setVar]
  have hdg4 : σ4.arrs "dg" = σ3.arrs "dg" := by rw [e4]; rfl
  refine ⟨σ4, ?_, hC4, ?_⟩
  · refine Run.mono (show Run B searchBody σ σ4 _ from r1.seq (r2.seq (r3.seq r4))) ?_
    unfold Kturn; omega
  · by_cases hlast : t + 1 = Rd n ^ Dn n
    · right
      refine ⟨hlast, ?_, ?_⟩
      · rw [hdone4, hcy3, if_pos hlast]
      · rw [hfound4, hfound3, hfound2, found_step, ← hlast]
    · left
      have hlt : t + 1 < Rd n ^ Dn n := by omega
      refine ⟨hlt, ?_, ?_, ?_⟩
      · rw [hdg4, hdg3, Nat.mod_eq_of_lt hlt]
      · rw [hdone4, hcy3, if_neg hlast]
      · rw [hfound4, hfound3, hfound2, found_step]

/-- The number whose digits are in `dg`. -/
def tOf (n : ℕ) (σ : Env) : ℕ := encR (Rd n) (fun q => (σ.arrs "dg").getD q 0) (Dn n)

theorem tOf_digits (n t : ℕ) (σ : Env) (ht : t < Rd n ^ Dn n)
    (hdg : σ.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) t)) : tOf n σ = t := by
  have hR : 0 < Rd n := by unfold Rd; omega
  unfold tOf
  rw [encR_congr' (Rd n) (g := digitsOf (Rd n) t) (fun q hq => by rw [hdg]; exact getD_arrOf_lt hq)]
  exact encR_digitsOf hR (Dn n) t ht

/-- The invariant of the search. -/
def SInv (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (σ : Env) : Prop :=
  Ctx n cnt bb σ ∧
    ((∃ t, t < Rd n ^ Dn n ∧ σ.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) t) ∧
        σ.vars "done" = 0 ∧ σ.vars "found" = if ∃ t' < t, AccT n cnt bb t' then 1 else 0) ∨
      (σ.vars "done" = 1 ∧
        σ.vars "found" = if ∃ t' < Rd n ^ Dn n, AccT n cnt bb t' then 1 else 0))

/-- The potential of the search. -/
def SPot (n : ℕ) (σ : Env) : ℕ :=
  if σ.vars "done" = 0 then (Rd n ^ Dn n - tOf n σ) * (Kturn n + 4) else 0

/-- The cost of the search. -/
def Ksearch (n : ℕ) : ℕ := 2 + 2 + (Rd n ^ Dn n * (Kturn n + 4) + 4)

theorem done_eq_zero_of_true {B : ℕ} {σ : Env}
    (h : (Cond.eq (V "done") (lit 0)).evalB B σ = some true) : σ.vars "done" = 0 := by
  simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff] at h
  obtain ⟨m, n', ⟨hm, -⟩, ⟨hn, -⟩, hr⟩ := h
  subst hm; subst hn
  simpa using hr.symm

theorem done_ne_zero_of_false {B : ℕ} {σ : Env}
    (h : (Cond.eq (V "done") (lit 0)).evalB B σ = some false) : σ.vars "done" ≠ 0 := by
  simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff] at h
  obtain ⟨m, n', ⟨hm, -⟩, ⟨hn, -⟩, hr⟩ := h
  subst hm; subst hn
  intro h0
  rw [h0] at hr
  simp at hr

theorem SInv.done_le {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {σ : Env} (h : SInv n cnt bb σ) :
    σ.vars "done" ≤ 1 := by
  rcases h.2 with ⟨t, -, -, hd, -⟩ | ⟨hd, -⟩ <;> omega

/-- **The search.** -/
theorem searchCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) (fun _ => 0))
      searchCom
      (fun _ σ' => Ctx n cnt bb σ' ∧
        σ'.vars "found" = if ∃ t < Rd n ^ Dn n, AccT n cnt bb t then 1 else 0)
      (Ksearch n) := by
  have hR : 0 < Rd n := by unfold Rd; omega
  have hRD : 0 < Rd n ^ Dn n := pow_pos hR _
  have hloop : Spec B (fun σ => SInv n cnt bb σ ∧ σ.vars "done" = 0 ∧ tOf n σ = 0)
      (.while (.eq (V "done") (lit 0)) searchBody)
      (fun _ σ' => SInv n cnt bb σ' ∧ (Cond.eq (V "done") (lit 0)).evalB B σ' = some false)
      (Rd n ^ Dn n * (Kturn n + 4) + 4) := by
    refine Spec.while_potential (B := B) (b := .eq (V "done") (lit 0)) (c := searchBody)
      (SInv n cnt bb) (SPot n) ?_ ?_ (fun σ h => h.1) ?_
    · intro σ hI
      have hd := hI.done_le
      have h1 := hb.five_lt_B
      exact (evalB_condEq_isSome (evalB_var (by omega)) (evalB_lit (by omega))).elim
        fun v hv => ⟨v, hv.1⟩
    · intro σ hI hcond
      have hdone := done_eq_zero_of_true hcond
      obtain ⟨hC, hd⟩ := hI
      rcases hd with ⟨t, ht, hdg, hdn, hfound⟩ | ⟨hd1, -⟩
      · obtain ⟨σ', hr, hC', hcases⟩ := searchBody_step hb t ht σ hC hdg hfound
        have htσ : tOf n σ = t := tOf_digits n t σ ht hdg
        refine ⟨σ', Kturn n, hr, ⟨hC', ?_⟩, ?_⟩
        · rcases hcases with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
          · exact Or.inl ⟨t + 1, h1, h2, h3, h4⟩
          · exact Or.inr ⟨h2, h3⟩
        · unfold SPot
          rw [if_pos hdn, htσ]
          have hcs : (Cond.eq (V "done") (lit 0)).size = 3 := by simp
          rw [hcs]
          rcases hcases with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
          · rw [if_pos h3, tOf_digits n (t + 1) σ' h1 h2]
            have : Rd n ^ Dn n - t = (Rd n ^ Dn n - (t + 1)) + 1 := by omega
            rw [this]; nlinarith
          · rw [if_neg (by omega)]
            have : Rd n ^ Dn n - t = 1 := by omega
            rw [this]; omega
      · omega
    · intro σ hP
      obtain ⟨hI, hdone, ht0⟩ := hP
      unfold SPot
      rw [if_pos hdone, ht0]
      have hcs : (Cond.eq (V "done") (lit 0)).size = 3 := by simp
      rw [hcs, Nat.sub_zero]
  have hz0 : ∀ σ : Env, σ.arrs "dg" = arrOf (Dn n) (fun _ => 0) →
      σ.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) 0) := by
    intro σ h
    rw [h]; exact arrOf_congr fun q _ => by simp [digitsOf]
  have hA : Spec B (fun σ => Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) (fun _ => 0))
      (asg "found" (lit 0)) (fun σ σ' => σ' = σ.setVar "found" 0) 2 :=
    Spec.pre (assign_lit_spec (B := B) "found" 0 (by have := hb.five_lt_B; omega)) (fun _ _ => trivial)
  have hA' : Spec B (fun σ => (Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) (fun _ => 0)) ∧
        σ.vars "found" = 0)
      (asg "done" (lit 0)) (fun σ σ' => σ' = σ.setVar "done" 0) 2 :=
    Spec.pre (assign_lit_spec (B := B) "done" 0 (by have := hb.five_lt_B; omega)) (fun _ _ => trivial)
  have hfin : Spec B (fun σ => SInv n cnt bb σ ∧ σ.vars "done" = 0 ∧ tOf n σ = 0)
      (.while (.eq (V "done") (lit 0)) searchBody)
      (fun _ σ' => Ctx n cnt bb σ' ∧
        σ'.vars "found" = if ∃ t < Rd n ^ Dn n, AccT n cnt bb t then 1 else 0)
      (Rd n ^ Dn n * (Kturn n + 4) + 4) := by
    refine Spec.post hloop ?_
    rintro σ σ' - ⟨⟨hC, hd⟩, hfalse⟩
    have hne := done_ne_zero_of_false hfalse
    rcases hd with ⟨t, -, -, hd0, -⟩ | ⟨-, hf⟩
    · exact absurd hd0 hne
    · exact ⟨hC, hf⟩
  have h2 : Spec B (fun σ => (Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) (fun _ => 0)) ∧
        σ.vars "found" = 0)
      (.seq (asg "done" (lit 0)) (.while (.eq (V "done") (lit 0)) searchBody))
      (fun _ σ' => Ctx n cnt bb σ' ∧
        σ'.vars "found" = if ∃ t < Rd n ^ Dn n, AccT n cnt bb t then 1 else 0)
      (2 + (Rd n ^ Dn n * (Kturn n + 4) + 4)) := by
    have hmid : ∀ σ σ1 : Env, ((Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) (fun _ => 0)) ∧
          σ.vars "found" = 0) → σ1 = σ.setVar "done" 0 →
        (SInv n cnt bb σ1 ∧ σ1.vars "done" = 0 ∧ tOf n σ1 = 0) := by
      rintro σ σ1 ⟨⟨hC, hdg⟩, hf⟩ e
      rw [e]
      have hC1 : Ctx n cnt bb (σ.setVar "done" 0) := hC.setVar (by decide) _
      have hdg1 : (σ.setVar "done" 0).arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) 0) := by
        simpa using hz0 σ hdg
      refine ⟨⟨hC1, Or.inl ⟨0, hRD, hdg1, by simp, by simp [hf]⟩⟩, by simp, ?_⟩
      exact tOf_digits n 0 _ hRD hdg1
    exact Spec.mono (Spec.seq hA' hfin hmid (fun σ σ1 σ2 _ _ hp => hp)) le_rfl
  have h1 : Spec B (fun σ => Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) (fun _ => 0))
      (.seq (asg "found" (lit 0)) (.seq (asg "done" (lit 0)) (.while (.eq (V "done") (lit 0)) searchBody)))
      (fun _ σ' => Ctx n cnt bb σ' ∧
        σ'.vars "found" = if ∃ t < Rd n ^ Dn n, AccT n cnt bb t then 1 else 0)
      (2 + (2 + (Rd n ^ Dn n * (Kturn n + 4) + 4))) := by
    have hmid : ∀ σ σ1 : Env, (Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) (fun _ => 0)) →
        σ1 = σ.setVar "found" 0 →
        ((Ctx n cnt bb σ1 ∧ σ1.arrs "dg" = arrOf (Dn n) (fun _ => 0)) ∧ σ1.vars "found" = 0) := by
      rintro σ σ1 ⟨hC, hdg⟩ e
      rw [e]
      exact ⟨⟨hC.setVar (by decide) _, by simpa using hdg⟩, by simp⟩
    exact Spec.mono (Spec.seq hA h2 hmid (fun σ σ1 σ2 _ _ hp => hp)) le_rfl
  unfold searchCom
  refine Spec.mono h1 ?_
  unfold Ksearch; omega

end

end Lax117284Proofs.Machine.Ilp
