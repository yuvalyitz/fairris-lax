import Lax117284Proofs.Machine.ClBruteFeas3

/-!
The fairness scan: the number of days each client is served, against `k`.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

/-- The state of the count of client `j` over the days. -/
structure CInv (x : List ℕ) (I : Instance) (k : ℕ) (f : ℕ → ℕ) (j : ℕ) (σ : Env) : Prop where
  ctx : Ctx x I k f σ
  hj : σ.vars "bfj" = j
  hi : σ.vars "bfi" ≤ I.days
  hc : σ.vars "bfc" = ∑ i ∈ Finset.range (σ.vars "bfi"), f (i * I.clients + j)
  hcle : σ.vars "bfc" ≤ σ.vars "bfi"

set_option maxHeartbeats 1600000 in
theorem cStep_vals (hb : Bd B x I k) (f : ℕ → ℕ) (j : ℕ) (hj : j < I.clients) :
    Spec B (fun σ => CInv x I k f j σ ∧ σ.vars "bfi" < I.days) cStep
      (fun σ σ' => σ'.vars "bfc" = σ.vars "bfc" +
          (σ.arrs "bfsc").getD (σ.vars "bfi" * σ.vars "n" + σ.vars "bfj") 0 ∧
        σ'.vars "bfi" = σ.vars "bfi" + 1) 13 := by
  run_vcg
  all_goals obtain ⟨hctx, hj', hi', hc, hcle⟩ := ‹CInv x I k f j σ›
  all_goals have hil : σ.vars "bfi" < I.days := ‹σ.vars "bfi" < I.days›
  all_goals have hmn := hb.mnB
  all_goals have hlen := hb.len
  all_goals have hbig := hb.big
  all_goals have hnB := hb.nB
  all_goals have hmB := hb.mB
  all_goals have hq : σ.vars "bfi" * σ.vars "n" + σ.vars "bfj" < I.days * I.clients := (by
    rw [hctx.hn, hj']; exact idx_lt I hil hj)
  all_goals have hscb : (σ.arrs "bfsc").getD (σ.vars "bfi" * σ.vars "n" + σ.vars "bfj") 0 ≤ 1 := (by
    rw [hctx.scGet hq]; exact hctx.hf _ hq)
  all_goals have hscl := hctx.scLen
  all_goals have hn' := hctx.hn
  all_goals have hprod : σ.vars "bfi" * σ.vars "n" ≤ I.days * I.clients := (by
    rw [hn']; exact Nat.mul_le_mul_right _ hil.le)
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte]
  all_goals try omega
  exact ⟨trivial, trivial⟩

theorem cStep_spec (hb : Bd B x I k) (f : ℕ → ℕ) (j : ℕ) (hj : j < I.clients) :
    Spec B (fun σ => CInv x I k f j σ ∧ σ.vars "bfi" < I.days) cStep
      (fun σ σ' => CInv x I k f j σ' ∧ σ'.vars "bfi" = σ.vars "bfi" + 1) 13 := by
  refine ((cStep_vals hb f j hj).frame).post ?_
  rintro σ σ' ⟨hC, hlt⟩ ⟨⟨hc', hi'⟩, hfv, hfa, -, -⟩
  have hq' : σ.vars "bfi" * I.clients + j < I.days * I.clients := idx_lt I hlt hj
  have hbit : (σ.arrs "bfsc").getD (σ.vars "bfi" * σ.vars "n" + σ.vars "bfj") 0 =
      f (σ.vars "bfi" * I.clients + j) := by
    rw [hC.ctx.hn, hC.hj]; exact hC.ctx.scGet hq'
  have hf1 : f (σ.vars "bfi" * I.clients + j) ≤ 1 := hC.ctx.hf _ hq'
  have hcle := hC.hcle
  refine ⟨⟨hC.ctx.frame hfv hfa (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_⟩, hi'⟩
  · rw [hfv "bfj" (by decide)]; exact hC.hj
  · omega
  · rw [hc', hi', Finset.sum_range_succ, hC.hc, hbit]
  · rw [hc', hi', hbit]; omega

theorem cLoop_spec (hb : Bd B x I k) (f : ℕ → ℕ) (j : ℕ) (hj : j < I.clients) :
    Spec B (fun σ => Ctx x I k f σ ∧ σ.vars "bfj" = j ∧ σ.vars "bfc" = 0) (forZ "bfi" "m" cStep)
      (fun _ σ' => CInv x I k f j σ' ∧ σ'.vars "bfi" = I.days) ((13 + 4) * I.days + 6) := by
  intro σ ⟨hctx, h1, h2⟩
  obtain ⟨σ', hrun, hI, hbn⟩ := (Spec.forRangeZero (B := B) "bfi" "m"
    (CInv x I k f j) I.days 13 hb.mB (fun _ h => h.hi) (fun _ h => h.ctx.hm)
    (cStep_spec hb f j hj)) σ
    ⟨hctx.setVar 0 (by decide), by simpa using h1, by simp, by simpa using h2, by simp [h2]⟩
  exact ⟨σ', hrun, hI, hbn⟩

set_option maxHeartbeats 1600000 in
theorem jTail_vals (hb : Bd B x I k) (f : ℕ → ℕ) :
    Spec B (fun σ => Ctx x I k f σ ∧ σ.vars "bfc" ≤ I.days ∧ σ.vars "bfok" ≤ 1 ∧
        σ.vars "bfj" < I.clients) jTail
      (fun σ σ' => σ'.vars "bfok" = σ.vars "bfok" - (1 - (1 - (σ.vars "k" - σ.vars "bfc"))) ∧
        σ'.vars "bfj" = σ.vars "bfj" + 1) 20 := by
  run_vcg
  all_goals have hctx : Ctx x I k f σ := ‹Ctx x I k f σ›
  all_goals have hc : σ.vars "bfc" ≤ I.days := ‹σ.vars "bfc" ≤ I.days›
  all_goals have hok : σ.vars "bfok" ≤ 1 := ‹σ.vars "bfok" ≤ 1›
  all_goals have hjl : σ.vars "bfj" < I.clients := ‹σ.vars "bfj" < I.clients›
  all_goals have hmB := hb.mB
  all_goals have hnB := hb.nB
  all_goals have hkB := hb.kB
  all_goals have hbig := hb.big
  all_goals have hkk := hctx.hk
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte]
  all_goals try omega
  exact ⟨trivial, trivial⟩

/-- The state of the loop over the clients. -/
structure JInv (x : List ℕ) (I : Instance) (k : ℕ) (f : ℕ → ℕ) (ok0 : ℕ) (σ : Env) : Prop where
  ctx : Ctx x I k f σ
  hj : σ.vars "bfj" ≤ I.clients
  hok : σ.vars "bfok" ≤ 1
  hiff : σ.vars "bfok" = 1 ↔ ok0 = 1 ∧ ∀ j', j' < σ.vars "bfj" →
    k ≤ ∑ i ∈ Finset.range I.days, f (i * I.clients + j')

open Classical in
lemma iff_step2 {ok ok0 b c : ℕ} {P : ℕ → Prop} (hok : ok ≤ 1)
    (h : ok = 1 ↔ ok0 = 1 ∧ ∀ b', b' < b → P b') (hc : c = if P b then 0 else 1) :
    ok - c = 1 ↔ ok0 = 1 ∧ ∀ b', b' < b + 1 → P b' := by
  rw [lt_succ_forall]
  by_cases hp : P b
  · rw [if_pos hp] at hc; subst hc
    rw [Nat.sub_zero, h]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, hp⟩
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rw [if_neg hp] at hc; subst hc
    constructor
    · intro h1; omega
    · rintro ⟨-, -, h2⟩; exact absurd h2 hp

theorem jStep_spec (hb : Bd B x I k) (f : ℕ → ℕ) (ok0 : ℕ) :
    Spec B (fun σ => JInv x I k f ok0 σ ∧ σ.vars "bfj" < I.clients) jStep
      (fun σ σ' => JInv x I k f ok0 σ' ∧ σ'.vars "bfj" = σ.vars "bfj" + 1)
      (2 + (((13 + 4) * I.days + 6) + 20)) := by
  intro σ ⟨hJ, hlt⟩
  have hbig := hb.big
  have hmB := hb.mB
  obtain ⟨σ1, hr1, h1⟩ := (Spec.assign (B := B) (x := "bfc") (e := lit 0) (f := fun _ => 0)
    (P := fun σ => JInv x I k f ok0 σ ∧ σ.vars "bfj" < I.clients)
    (fun σ h => evalB_lit (by have := hb.big; omega))) σ ⟨hJ, hlt⟩
  have hc1 : Ctx x I k f σ1 := by rw [h1]; exact hJ.ctx.setVar _ (by decide)
  have hv1 : ∀ y, y ≠ "bfc" → σ1.vars y = σ.vars y := by
    intro y hy; rw [h1]; simp [hy]
  obtain ⟨σ2, hr2, ⟨hCI, hbn⟩, hfv, -, -, -⟩ := (cLoop_spec hb f (σ.vars "bfj") hlt).frame σ1
    ⟨hc1, hv1 _ (by decide), by rw [h1]; simp⟩
  have hok2 : σ2.vars "bfok" = σ.vars "bfok" := by
    rw [hfv "bfok" (by decide), hv1 _ (by decide)]
  have hbj2 : σ2.vars "bfj" = σ.vars "bfj" := by
    rw [hCI.hj]
  have hcle : σ2.vars "bfc" ≤ I.days := by have := hCI.hcle; omega
  obtain ⟨σ3, hr3, ⟨hok3, hj3⟩, hfv3, hfa3, -, -⟩ := (jTail_vals hb f).frame σ2
    ⟨hCI.ctx, hcle, by rw [hok2]; exact hJ.hok, by rw [hbj2]; exact hlt⟩
  have hs : (lit 0).size = 1 := rfl
  have hS : σ2.vars "bfc" = ∑ i ∈ Finset.range I.days, f (i * I.clients + σ.vars "bfj") := by
    rw [hCI.hc, hbn]
  have hkk : σ2.vars "k" = k := hCI.ctx.hk
  refine ⟨σ3, hr1.seq (hr2.seq hr3) |>.mono (by omega),
    ⟨hCI.ctx.frame hfv3 hfa3 (by decide) (by decide) (by decide), ?_, ?_, ?_⟩, ?_⟩
  · rw [hj3, hbj2]; omega
  · rw [hok3]; exact le_trans (Nat.sub_le _ _) (by rw [hok2]; exact hJ.hok)
  · rw [hok3, hj3, hbj2, hok2]
    exact iff_step2 hJ.hok hJ.hiff (by rw [hS, hkk, ltf_eq]; split_ifs <;> omega)
  · rw [hj3, hbj2]

theorem fairCom_spec (hb : Bd B x I k) (f : ℕ → ℕ) :
    Spec B (fun σ => Ctx x I k f σ ∧ σ.vars "bfok" ≤ 1) fairCom
      (fun σ σ' => JInv x I k f (σ.vars "bfok") σ' ∧ σ'.vars "bfj" = I.clients)
      ((2 + (((13 + 4) * I.days + 6) + 20) + 4) * I.clients + 6) := by
  intro σ ⟨hctx, h1⟩
  obtain ⟨σ', hrun, hI, hbn⟩ := (Spec.forRangeZero (B := B) "bfj" "n"
    (JInv x I k f (σ.vars "bfok")) I.clients (2 + (((13 + 4) * I.days + 6) + 20)) hb.nB
    (fun _ h => h.hj) (fun _ h => h.ctx.hn) (jStep_spec hb f (σ.vars "bfok"))) σ
    ⟨hctx.setVar 0 (by decide), by simp, by simpa using h1, by simp⟩
  exact ⟨σ', hrun, hI, hbn⟩

end Lax117284Proofs.Machine.ClBrute
