import Lax117284Proofs.Machine.ClBruteFair

/-!
The odometer: add one to the vector, the carry running from cell to cell.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

set_option maxHeartbeats 1600000 in
theorem oStep_vals (hb : Bd B x I k) (g : ℕ → ℕ) :
    Spec B (fun σ => Ctx x I k g σ ∧ σ.vars "bfq" < I.days * I.clients ∧ σ.vars "bfcy" ≤ 1) oStep
      (fun σ σ' => σ'.vars "bfcy" = ((σ.arrs "bfsc").getD (σ.vars "bfq") 0 + σ.vars "bfcy") / 2 ∧
        σ'.arrs "bfsc" = (σ.arrs "bfsc").set (σ.vars "bfq")
          (((σ.arrs "bfsc").getD (σ.vars "bfq") 0 + σ.vars "bfcy") -
            ((σ.arrs "bfsc").getD (σ.vars "bfq") 0 + σ.vars "bfcy") / 2 * 2) ∧
        σ'.vars "bfq" = σ.vars "bfq" + 1) 20 := by
  run_vcg
  all_goals have hctx : Ctx x I k g σ := ‹Ctx x I k g σ›
  all_goals have hq : σ.vars "bfq" < I.days * I.clients := ‹σ.vars "bfq" < I.days * I.clients›
  all_goals have hcy : σ.vars "bfcy" ≤ 1 := ‹σ.vars "bfcy" ≤ 1›
  all_goals have hmn := hb.mnB
  all_goals have hbig := hb.big
  all_goals have hlen := hb.len
  all_goals have hscb : (σ.arrs "bfsc").getD (σ.vars "bfq") 0 ≤ 1 := (by
    rw [hctx.scGet hq]; exact hctx.hf _ hq)
  all_goals have hscl := hctx.scLen
  all_goals try simp only [Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte]
  all_goals try omega
  exact ⟨trivial, trivial, trivial⟩

/-- The state of the increment after `bfq` cells: the cells before `bfq` hold the new bits
`g`, the others are still `f`, and `g` with the carry adds one to `f` there. -/
def OInv (x : List ℕ) (I : Instance) (k : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  ∃ g : ℕ → ℕ, Ctx x I k g σ ∧ σ.vars "bfq" ≤ I.days * I.clients ∧ σ.vars "bfcy" ≤ 1 ∧
    (∀ r, σ.vars "bfq" ≤ r → g r = f r) ∧
    enc g (σ.vars "bfq") + σ.vars "bfcy" * 2 ^ σ.vars "bfq" = enc f (σ.vars "bfq") + 1

lemma Ctx.frame_sc {c : Com} {f g : ℕ → ℕ} {σ σ' : Env} (h : Ctx x I k f σ)
    (hv : ∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y)
    (ha : ∀ a, a ∉ c.warrs → σ'.arrs a = σ.arrs a)
    (h1 : ∀ y ∈ ["n", "m", "k", "bfmn"], y ∉ c.wvars) (h2 : "X" ∉ c.warrs)
    (hsc : σ'.arrs "bfsc" = arrOf (I.days * I.clients) g)
    (hg : ∀ r, r < I.days * I.clients → g r ≤ 1) : Ctx x I k g σ' :=
  ⟨by rw [ha _ h2]; exact h.hx, by rw [hv _ (h1 _ (by simp))]; exact h.hn,
    by rw [hv _ (h1 _ (by simp))]; exact h.hm, by rw [hv _ (h1 _ (by simp))]; exact h.hk,
    by rw [hv _ (h1 _ (by simp))]; exact h.hmn, hsc, hg⟩

lemma odo_arith (E1 E2 P a cy c d : ℕ) (hd : d + c * 2 = a + cy) (hE : E1 + cy * P = E2 + 1) :
    E1 + d * P + c * (P * 2) = E2 + a * P + 1 := by
  have hm : (d + c * 2) * P = (a + cy) * P := by rw [hd]
  nlinarith [hm, hE]

theorem oStep_spec (hb : Bd B x I k) (f : ℕ → ℕ) :
    Spec B (fun σ => OInv x I k f σ ∧ σ.vars "bfq" < I.days * I.clients) oStep
      (fun σ σ' => OInv x I k f σ' ∧ σ'.vars "bfq" = σ.vars "bfq" + 1) 20 := by
  intro σ ⟨⟨g, hctx, hq, hcy, hrest, henc⟩, hlt⟩
  obtain ⟨σ', hr, ⟨hcy', hsc', hq'⟩, hfv, hfa, -, -⟩ := (oStep_vals hb g).frame σ ⟨hctx, hlt, hcy⟩
  have hgq : (σ.arrs "bfsc").getD (σ.vars "bfq") 0 = g (σ.vars "bfq") := hctx.scGet hlt
  rw [hgq] at hcy' hsc'
  have hg1 : g (σ.vars "bfq") ≤ 1 := hctx.hf _ hlt
  refine ⟨σ', hr, ⟨fun r => if r = σ.vars "bfq" then
      (g r + σ.vars "bfcy") - (g r + σ.vars "bfcy") / 2 * 2 else g r, ?_, ?_, ?_, ?_, ?_⟩, hq'⟩
  · refine hctx.frame_sc hfv hfa (by decide) (by decide) ?_ ?_
    · rw [hsc', hctx.hsc, set_arrOf]
      refine arrOf_congr fun r _ => ?_
      by_cases h : r = σ.vars "bfq"
      · subst h; simp
      · simp [h]
    · intro r hr
      by_cases h : r = σ.vars "bfq"
      · subst h; simp only [if_true]; omega
      · simp only [h, if_false]; exact hctx.hf r hr
  · rw [hq']; omega
  · rw [hcy']; omega
  · intro r hr
    rw [hq'] at hr
    have h : r ≠ σ.vars "bfq" := by omega
    simp only [h, if_false]
    exact hrest r (by omega)
  · rw [hq', hcy', enc_succ, enc_succ, pow_succ]
    have hc : enc (fun r => if r = σ.vars "bfq" then
        (g r + σ.vars "bfcy") - (g r + σ.vars "bfcy") / 2 * 2 else g r) (σ.vars "bfq") =
        enc g (σ.vars "bfq") :=
      enc_congr fun r hr => by simp only [show r ≠ σ.vars "bfq" by omega, if_false]
    rw [hc, if_pos rfl, hrest _ le_rfl]
    have := odo_arith (enc g (σ.vars "bfq")) (enc f (σ.vars "bfq")) (2 ^ σ.vars "bfq")
      (g (σ.vars "bfq")) (σ.vars "bfcy") ((g (σ.vars "bfq") + σ.vars "bfcy") / 2)
      ((g (σ.vars "bfq") + σ.vars "bfcy") - (g (σ.vars "bfq") + σ.vars "bfcy") / 2 * 2)
      (by omega) henc
    rw [hrest _ le_rfl] at this
    linarith

/-- **The increment**: the vector `f` becomes a vector `g` with `g + carry * 2 ^ (m * n) = f + 1`
(as numbers), the carry being `0` or `1`. -/
theorem odoCom_spec (hb : Bd B x I k) (f : ℕ → ℕ) :
    Spec B (fun σ => Ctx x I k f σ) odoCom
      (fun _ σ' => ∃ g, Ctx x I k g σ' ∧ σ'.vars "bfcy" ≤ 1 ∧
        enc g (I.days * I.clients) + σ'.vars "bfcy" * 2 ^ (I.days * I.clients) =
          enc f (I.days * I.clients) + 1 ∧ σ'.vars "bfq" = I.days * I.clients)
      (2 + ((20 + 4) * (I.days * I.clients) + 6)) := by
  intro σ hctx
  have hbig := hb.big
  obtain ⟨σ1, hr1, h1⟩ := (Spec.assign (B := B) (x := "bfcy") (e := lit 1) (f := fun _ => 1)
    (P := fun σ => Ctx x I k f σ)
    (fun _ _ => evalB_lit (by have := hb.big; omega))) σ hctx
  have hs : (lit 1).size = 1 := rfl
  have hc1 : Ctx x I k f σ1 := by rw [h1]; exact hctx.setVar _ (by decide)
  obtain ⟨σ2, hr2, ⟨g, hg, hq, hcy, -, henc⟩, hq2⟩ := (Spec.forRangeZero (B := B) "bfq" "bfmn"
    (OInv x I k f) (I.days * I.clients) 20 (by have := hb.mnB; omega)
    (fun _ h => by obtain ⟨g, -, h, -⟩ := h; exact h)
    (fun _ h => by obtain ⟨g, hg, -⟩ := h; exact hg.hmn) (oStep_spec hb f)) σ1
    ⟨f, hc1.setVar _ (by decide), by simp, by simp [h1], fun _ _ => rfl, by simp [h1, enc_zero]⟩
  refine ⟨σ2, (hr1.seq hr2).mono (by omega), g, hg, hcy, ?_, hq2⟩
  rw [hq2] at henc
  exact henc

end Lax117284Proofs.Machine.ClBrute
