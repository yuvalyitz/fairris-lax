import Lax117284Proofs.Machine.ClBruteFeas1

/-!
The feasibility scan: every client `a` of a day against every client, every day.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

/-- Adding one to a scalar. -/
theorem bump_spec (v : String) :
    Spec B (fun σ => σ.vars v + 1 < B ∧ 1 < B) (asg v (.add (V v) (lit 1)))
      (fun σ σ' => σ' = σ.setVar v (σ.vars v + 1)) 4 :=
  Spec.assign (f := fun σ => σ.vars v + 1) fun σ h =>
    evalB_bin (evalB_var (by omega)) (evalB_lit h.2) h.1

/-- The state of the loop over the clients `a` of day `i`. -/
structure AInv (x : List ℕ) (I : Instance) (k : ℕ) (f : ℕ → ℕ) (i ok0 : ℕ) (σ : Env) : Prop where
  ctx : Ctx x I k f σ
  hi : σ.vars "bfi" = i
  hro : σ.vars "bfro" = i * I.clients
  ha : σ.vars "bfa" ≤ I.clients
  hok : σ.vars "bfok" ≤ 1
  hiff : σ.vars "bfok" = 1 ↔ ok0 = 1 ∧ ∀ a', a' < σ.vars "bfa" → ∀ b, ¬ Bad I f i a' b

set_option maxHeartbeats 1600000 in
theorem aSetup_vals (hb : Bd B x I k) (f : ℕ → ℕ) (i ok0 : ℕ) (hi : i < I.days) :
    Spec B (fun σ => AInv x I k f i ok0 σ ∧ σ.vars "bfa" < I.clients) aSetup
      (fun σ σ' => σ'.vars "bfba" = (σ.arrs "bfsc").getD (σ.vars "bfro" + σ.vars "bfa") 0 ∧
        σ'.vars "bfda" = (σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfa")) 0 ∧
        σ'.vars "bfsa" = (σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfa")) 0 -
          (σ.arrs "X").getD (2 + (σ.vars "bfro" + σ.vars "bfa")) 0) 23 := by
  run_vcg
  all_goals have hro := (‹AInv x I k f i ok0 σ›).hro
  all_goals obtain ⟨hctx, hi', -, ha', hok, hiff⟩ := ‹AInv x I k f i ok0 σ›
  all_goals have hal : σ.vars "bfa" < I.clients := ‹σ.vars "bfa" < I.clients›
  all_goals have hmn := hb.mnB
  all_goals have hlen := hb.len
  all_goals have hbig := hb.big
  all_goals have hq : σ.vars "bfro" + σ.vars "bfa" < I.days * I.clients := (by
    rw [hro]; exact idx_lt I hi hal)
  all_goals have hmn' := hctx.hmn
  all_goals have hscb : (σ.arrs "bfsc").getD (σ.vars "bfro" + σ.vars "bfa") 0 ≤ 1 := (by
    rw [hctx.scGet hq]; exact hctx.hf _ hq)
  all_goals have hscl := hctx.scLen
  all_goals have hxl := hctx.xLen hb
  all_goals have hx1 : (σ.arrs "X").getD (2 + (σ.vars "bfro" + σ.vars "bfa")) 0 < B := (by
    rw [hctx.xGet]; exact hb.xg _)
  all_goals have hx2 : (σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfa")) 0 < B := (by
    rw [hctx.xGet]; exact hb.xg _)
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte]
  all_goals try omega
  trivial

theorem aSetup_spec (hb : Bd B x I k) (f : ℕ → ℕ) (i ok0 : ℕ) (hi : i < I.days) :
    Spec B (fun σ => AInv x I k f i ok0 σ ∧ σ.vars "bfa" < I.clients) aSetup
      (fun σ σ' => Ctx x I k f σ' ∧ σ'.vars "bfi" = i ∧ σ'.vars "bfro" = i * I.clients ∧
        σ'.vars "bfa" = σ.vars "bfa" ∧ σ'.vars "bfok" = σ.vars "bfok" ∧
        σ'.vars "bfba" = f (i * I.clients + σ.vars "bfa") ∧
        σ'.vars "bfda" = I.dAt i (σ.vars "bfa") ∧
        σ'.vars "bfsa" = I.dAt i (σ.vars "bfa") - I.pAt i (σ.vars "bfa")) 23 := by
  refine ((aSetup_vals hb f i ok0 hi).frame).post ?_
  rintro σ σ' ⟨hA, hlt⟩ ⟨⟨hba, hda, hsa⟩, hfv, hfa, -, -⟩
  have hro := hA.hro
  obtain ⟨hctx, hi', -, ha', hok, hiff⟩ := hA
  have hq : i * I.clients + σ.vars "bfa" < I.days * I.clients := idx_lt I hi hlt
  have hp : (σ.arrs "X").getD (2 + (σ.vars "bfro" + σ.vars "bfa")) 0 = I.pAt i (σ.vars "bfa") := by
    rw [hctx.xGet, hro, ← Nat.add_assoc]
    exact Lax117284Proofs.ClientsWord.proc_eq hb.dec hi hlt
  have hd : (σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfa")) 0 =
      I.dAt i (σ.vars "bfa") := by
    rw [hctx.xGet, hro, hctx.hmn, ← Nat.add_assoc]
    exact Lax117284Proofs.ClientsWord.due_eq hb.dec hi hlt
  refine ⟨hctx.frame hfv hfa (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfv "bfi" (by decide)]; exact hi'
  · rw [hfv "bfro" (by decide)]; exact hro
  · rw [hfv "bfa" (by decide)]
  · rw [hfv "bfok" (by decide)]
  · rw [hba, hro, hctx.scGet hq]
  · rw [hda, hd]
  · rw [hsa, hd, hp]

lemma col_iff (f : ℕ → ℕ) (i a : ℕ) :
    (∀ b, b < I.clients → ¬ Bad I f i a b) ↔ ∀ b, ¬ Bad I f i a b :=
  ⟨fun h b hbad => h b hbad.2.1 hbad, fun h b _ => h b⟩

lemma row_iff (f : ℕ → ℕ) (i : ℕ) :
    (∀ a, a < I.clients → ∀ b, ¬ Bad I f i a b) ↔ ∀ a b, ¬ Bad I f i a b :=
  ⟨fun h a b hbad => h a (lt_trans hbad.1 hbad.2.1) b hbad, fun h a _ b => h a b⟩

theorem aStep_spec (hb : Bd B x I k) (f : ℕ → ℕ) (i ok0 : ℕ) (hi : i < I.days) :
    Spec B (fun σ => AInv x I k f i ok0 σ ∧ σ.vars "bfa" < I.clients) aStep
      (fun σ σ' => AInv x I k f i ok0 σ' ∧ σ'.vars "bfa" = σ.vars "bfa" + 1)
      (23 + ((65 + 4) * I.clients + 6 + 4)) := by
  intro σ ⟨hA, hlt⟩
  obtain ⟨σ1, hr1, hC1, hi1, hro1, ha1, hok1, hba1, hda1, hsa1⟩ :=
    aSetup_spec hb f i ok0 hi σ ⟨hA, hlt⟩
  obtain ⟨σ2, hr2, hBI, hbn⟩ := bLoop_spec hb f i (σ.vars "bfa") hi hlt σ1
    ⟨hC1, hi1, hro1, ha1, hba1, hda1, hsa1, by rw [hok1]; exact hA.hok⟩
  have hbig := hb.big
  have hnB := hb.nB
  have ha2 : σ2.vars "bfa" = σ.vars "bfa" := hBI.ha
  obtain ⟨σ3, hr3, rfl⟩ := (bump_spec (B := B) "bfa") σ2 ⟨by omega, by omega⟩
  refine ⟨_, hr1.seq (hr2.seq hr3), ⟨hBI.ctx.setVar _ (by decide), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa using hBI.hi
  · simpa using hBI.hro
  · simp only [vars_setVar, if_true]; omega
  · simpa using hBI.hok
  · have h1 := hBI.hiff
    rw [hbn, hok1, hA.hiff, col_iff] at h1
    simp only [vars_setVar, if_true, ha2, String.reduceEq, not_false_eq_true, if_neg]
    rw [h1, lt_succ_forall]
    tauto
  · simp only [vars_setVar, if_true, ha2]

theorem aLoop_spec (hb : Bd B x I k) (f : ℕ → ℕ) (i : ℕ) (hi : i < I.days) :
    Spec B (fun σ => Ctx x I k f σ ∧ σ.vars "bfi" = i ∧ σ.vars "bfro" = i * I.clients ∧
        σ.vars "bfok" ≤ 1) (forZ "bfa" "n" aStep)
      (fun σ σ' => AInv x I k f i (σ.vars "bfok") σ' ∧ σ'.vars "bfa" = I.clients)
      ((23 + ((65 + 4) * I.clients + 6 + 4) + 4) * I.clients + 6) := by
  intro σ ⟨hctx, h1, h2, h3⟩
  obtain ⟨σ', hrun, hI, hbn⟩ := (Spec.forRangeZero (B := B) "bfa" "n"
    (AInv x I k f i (σ.vars "bfok")) I.clients (23 + ((65 + 4) * I.clients + 6 + 4)) hb.nB
    (fun _ h => h.ha) (fun _ h => h.ctx.hn) (aStep_spec hb f i (σ.vars "bfok") hi)) σ
    ⟨hctx.setVar 0 (by decide), by simpa using h1, by simpa using h2, by simp,
      by simpa using h3, by simp⟩
  exact ⟨σ', hrun, hI, hbn⟩

end Lax117284Proofs.Machine.ClBrute
