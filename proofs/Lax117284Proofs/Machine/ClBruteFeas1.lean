import Lax117284Proofs.Machine.ClBruteCtx

/-!
The pair loop: one client `a` of day `i` against every client `b`.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

/-- The state of the pair loop of client `a` on day `i`. -/
structure BInv (x : List ℕ) (I : Instance) (k : ℕ) (f : ℕ → ℕ) (i a ok0 : ℕ) (σ : Env) : Prop where
  ctx : Ctx x I k f σ
  hi : σ.vars "bfi" = i
  hro : σ.vars "bfro" = i * I.clients
  ha : σ.vars "bfa" = a
  hba : σ.vars "bfba" = f (i * I.clients + a)
  hda : σ.vars "bfda" = I.dAt i a
  hsa : σ.vars "bfsa" = I.dAt i a - I.pAt i a
  hb : σ.vars "bfb" ≤ I.clients
  hok : σ.vars "bfok" ≤ 1
  hiff : σ.vars "bfok" = 1 ↔ ok0 = 1 ∧ ∀ b, b < σ.vars "bfb" → ¬ Bad I f i a b

lemma mul_le1 {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
  calc a * b ≤ 1 * 1 := Nat.mul_le_mul ha hb
    _ = 1 := rfl

set_option maxHeartbeats 1600000 in
theorem bStep_vals (hb : Bd B x I k) (f : ℕ → ℕ) (i a ok0 : ℕ) (hi : i < I.days)
    (ha : a < I.clients) :
    Spec B (fun σ => BInv x I k f i a ok0 σ ∧ σ.vars "bfb" < I.clients) bStep
      (fun σ σ' => σ'.vars "bfok" = σ.vars "bfok" -
          cl (σ.vars "bfba") ((σ.arrs "bfsc").getD (σ.vars "bfro" + σ.vars "bfb") 0)
            (σ.vars "bfa") (σ.vars "bfb") (σ.vars "bfsa")
            ((σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfb")) 0)
            ((σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfb")) 0 -
              (σ.arrs "X").getD (2 + (σ.vars "bfro" + σ.vars "bfb")) 0)
            (σ.vars "bfda") ∧
        σ'.vars "bfb" = σ.vars "bfb" + 1) 65 := by
  run_vcg
  all_goals obtain ⟨hctx, hi', hro, ha', hba, hda, hsa, hb', hok, hiff⟩ := ‹BInv x I k f i a ok0 σ›
  all_goals have hbl : σ.vars "bfb" < I.clients := ‹σ.vars "bfb" < I.clients›
  all_goals have hmn := hb.mnB
  all_goals have hnB := hb.nB
  all_goals have hmB := hb.mB
  all_goals have hkB := hb.kB
  all_goals have hbig := hb.big
  all_goals have hlen := hb.len
  all_goals have hq : σ.vars "bfro" + σ.vars "bfb" < I.days * I.clients := (by
    rw [hro]; exact idx_lt I hi hbl)
  all_goals have hmn' := hctx.hmn
  all_goals have hscb : (σ.arrs "bfsc").getD (σ.vars "bfro" + σ.vars "bfb") 0 ≤ 1 := (by
    rw [hctx.scGet hq]; exact hctx.hf _ hq)
  all_goals have hscl := hctx.scLen
  all_goals have hxl := hctx.xLen hb
  all_goals have hx1 : (σ.arrs "X").getD (2 + (σ.vars "bfro" + σ.vars "bfb")) 0 < B := (by
    rw [hctx.xGet]; exact hb.xg _)
  all_goals have hx2 : (σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfb")) 0 < B := (by
    rw [hctx.xGet]; exact hb.xg _)
  all_goals have hba1 : σ.vars "bfba" ≤ 1 := (by rw [hba]; exact hctx.hf _ (idx_lt I hi ha))
  all_goals have han := hctx.hn
  all_goals have hkk := hctx.hk
  all_goals have hdaB : σ.vars "bfda" < B := (by
    rw [hda, ← Lax117284Proofs.ClientsWord.due_eq hb.dec hi ha]; exact hb.xg _)
  all_goals have hsaB : σ.vars "bfsa" ≤ σ.vars "bfda" := (by rw [hsa, hda]; omega)
  all_goals have p1 := mul_le1 hba1 hscb
  all_goals have p2 := mul_le1 p1 (show 1 - (1 - (σ.vars "bfb" - σ.vars "bfa")) ≤ 1 by omega)
  all_goals have p3 := mul_le1 p2 (show 1 - (1 - ((σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfb")) 0 - σ.vars "bfsa")) ≤ 1 by omega)
  all_goals have p4 := mul_le1 p3 (show 1 - (1 - (σ.vars "bfda" - ((σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfb")) 0 - (σ.arrs "X").getD (2 + (σ.vars "bfro" + σ.vars "bfb")) 0))) ≤ 1 by omega)
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte]
  all_goals try omega
  exact ⟨by unfold cl; rfl, trivial⟩


/-! ### From the values to the invariant -/

lemma lt_succ_forall {Q : ℕ → Prop} {c : ℕ} :
    (∀ b, b < c + 1 → Q b) ↔ (∀ b, b < c → Q b) ∧ Q c := by
  constructor
  · intro h; exact ⟨fun b hb => h b (by omega), h c (by omega)⟩
  · rintro ⟨h1, h2⟩ b hb
    rcases Nat.lt_succ_iff_lt_or_eq.mp hb with h | rfl
    · exact h1 b h
    · exact h2

open Classical in
/-- Removing a clash from the flag. -/
lemma iff_step {ok ok0 b c : ℕ} {Q : ℕ → Prop} (hok : ok ≤ 1)
    (h : ok = 1 ↔ ok0 = 1 ∧ ∀ b', b' < b → ¬ Q b') (hc : c = if Q b then 1 else 0) :
    ok - c = 1 ↔ ok0 = 1 ∧ ∀ b', b' < b + 1 → ¬ Q b' := by
  rw [lt_succ_forall]
  by_cases hq : Q b
  · rw [if_pos hq] at hc; subst hc
    constructor
    · intro h1; omega
    · rintro ⟨-, -, h2⟩; exact absurd hq h2
  · rw [if_neg hq] at hc; subst hc
    rw [Nat.sub_zero, h]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, hq⟩
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩

lemma Ctx.frame {c : Com} {f : ℕ → ℕ} {σ σ' : Env} (h : Ctx x I k f σ)
    (hv : ∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y)
    (ha : ∀ a, a ∉ c.warrs → σ'.arrs a = σ.arrs a)
    (h1 : ∀ y ∈ ["n", "m", "k", "bfmn"], y ∉ c.wvars) (h2 : "X" ∉ c.warrs)
    (h3 : "bfsc" ∉ c.warrs) : Ctx x I k f σ' :=
  ⟨by rw [ha _ h2]; exact h.hx, by rw [hv _ (h1 _ (by simp))]; exact h.hn,
    by rw [hv _ (h1 _ (by simp))]; exact h.hm, by rw [hv _ (h1 _ (by simp))]; exact h.hk,
    by rw [hv _ (h1 _ (by simp))]; exact h.hmn, by rw [ha _ h3]; exact h.hsc, h.hf⟩

lemma Ctx.setVar {f : ℕ → ℕ} {σ : Env} (h : Ctx x I k f σ) {y : String} (v : ℕ)
    (hy : y ≠ "n" ∧ y ≠ "m" ∧ y ≠ "k" ∧ y ≠ "bfmn") : Ctx x I k f (σ.setVar y v) :=
  ⟨h.hx, by rw [vars_setVar, if_neg hy.1.symm]; exact h.hn,
    by rw [vars_setVar, if_neg hy.2.1.symm]; exact h.hm,
    by rw [vars_setVar, if_neg hy.2.2.1.symm]; exact h.hk,
    by rw [vars_setVar, if_neg hy.2.2.2.symm]; exact h.hmn, h.hsc, h.hf⟩

open Classical in
/-- The value the clash expression takes is the truth of `Bad`. -/
lemma cl_bad (hb : Bd B x I k) {f : ℕ → ℕ} {σ : Env} {i a : ℕ} (hi : i < I.days)
    (ha : a < I.clients) (hctx : Ctx x I k f σ) (hro : σ.vars "bfro" = i * I.clients)
    (ha' : σ.vars "bfa" = a) (hba : σ.vars "bfba" = f (i * I.clients + a))
    (hda : σ.vars "bfda" = I.dAt i a) (hsa : σ.vars "bfsa" = I.dAt i a - I.pAt i a)
    (hlt : σ.vars "bfb" < I.clients) :
    cl (σ.vars "bfba") ((σ.arrs "bfsc").getD (σ.vars "bfro" + σ.vars "bfb") 0)
        (σ.vars "bfa") (σ.vars "bfb") (σ.vars "bfsa")
        ((σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfb")) 0)
        ((σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfb")) 0 -
          (σ.arrs "X").getD (2 + (σ.vars "bfro" + σ.vars "bfb")) 0)
        (σ.vars "bfda") = if Bad I f i a (σ.vars "bfb") then 1 else 0 := by
  have hq : i * I.clients + σ.vars "bfb" < I.days * I.clients := idx_lt I hi hlt
  have hbb : (σ.arrs "bfsc").getD (σ.vars "bfro" + σ.vars "bfb") 0 = f (i * I.clients + σ.vars "bfb") := by
    rw [hro, hctx.scGet hq]
  have hp : (σ.arrs "X").getD (2 + (σ.vars "bfro" + σ.vars "bfb")) 0 = I.pAt i (σ.vars "bfb") := by
    rw [hctx.xGet, hro, ← Nat.add_assoc]
    exact Lax117284Proofs.ClientsWord.proc_eq hb.dec hi hlt
  have hd : (σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfb")) 0 =
      I.dAt i (σ.vars "bfb") := by
    rw [hctx.xGet, hro, hctx.hmn, ← Nat.add_assoc]
    exact Lax117284Proofs.ClientsWord.due_eq hb.dec hi hlt
  have hba1 : σ.vars "bfba" ≤ 1 := by rw [hba]; exact hctx.hf _ (idx_lt I hi ha)
  have hbb1 : f (i * I.clients + σ.vars "bfb") ≤ 1 := hctx.hf _ hq
  rw [hbb, hd, hp, hda, hsa, ha', hba, cl_eq (by rw [← hba]; exact hba1) hbb1]
  refine if_congr ?_ rfl rfl
  simp only [Bad, Instance.ConflictAt]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h3, hlt, h1, h2, h4, h5⟩
  · rintro ⟨h3, -, h1, h2, h4, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩

theorem bStep_spec (hb : Bd B x I k) (f : ℕ → ℕ) (i a ok0 : ℕ) (hi : i < I.days)
    (ha : a < I.clients) :
    Spec B (fun σ => BInv x I k f i a ok0 σ ∧ σ.vars "bfb" < I.clients) bStep
      (fun σ σ' => BInv x I k f i a ok0 σ' ∧ σ'.vars "bfb" = σ.vars "bfb" + 1) 65 := by
  refine ((bStep_vals hb f i a ok0 hi ha).frame).post ?_
  rintro σ σ' ⟨hB, hlt⟩ ⟨⟨hok', hb'⟩, hfv, hfa, -, -⟩
  have hclb := cl_bad hb hi ha hB.ctx hB.hro hB.ha hB.hba hB.hda hB.hsa hlt
  obtain ⟨hctx, hi', hro, ha', hba, hda, hsa, hb1, hok, hiff⟩ := hB
  refine ⟨⟨hctx.frame hfv hfa (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, hb'⟩
  · rw [hfv "bfi" (by decide)]; exact hi'
  · rw [hfv "bfro" (by decide)]; exact hro
  · rw [hfv "bfa" (by decide)]; exact ha'
  · rw [hfv "bfba" (by decide)]; exact hba
  · rw [hfv "bfda" (by decide)]; exact hda
  · rw [hfv "bfsa" (by decide)]; exact hsa
  · omega
  · rw [hok']; exact le_trans (Nat.sub_le _ _) hok
  · rw [hb', hok']
    exact iff_step hok hiff hclb

/-- The pair loop of client `a` of day `i`: the flag loses the clashes of `a` with the later
clients. -/
theorem bLoop_spec (hb : Bd B x I k) (f : ℕ → ℕ) (i a : ℕ) (hi : i < I.days)
    (ha : a < I.clients) :
    Spec B (fun σ => Ctx x I k f σ ∧ σ.vars "bfi" = i ∧ σ.vars "bfro" = i * I.clients ∧
        σ.vars "bfa" = a ∧ σ.vars "bfba" = f (i * I.clients + a) ∧ σ.vars "bfda" = I.dAt i a ∧
        σ.vars "bfsa" = I.dAt i a - I.pAt i a ∧ σ.vars "bfok" ≤ 1) bLoop
      (fun σ σ' => BInv x I k f i a (σ.vars "bfok") σ' ∧ σ'.vars "bfb" = I.clients)
      ((65 + 4) * I.clients + 6) := by
  intro σ ⟨hctx, h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨σ', hrun, hI, hbn⟩ := (Spec.forRangeZero (B := B) "bfb" "n"
    (BInv x I k f i a (σ.vars "bfok")) I.clients 65 hb.nB (fun _ h => h.hb)
    (fun _ h => h.ctx.hn) (bStep_spec hb f i a (σ.vars "bfok") hi ha)) σ
    ⟨hctx.setVar 0 (by decide), by simpa using h1, by simpa using h2, by simpa using h3,
      by simpa using h4, by simpa using h5, by simpa using h6, by simp, by simpa using h7,
      by simp⟩
  exact ⟨σ', hrun, hI, hbn⟩

end Lax117284Proofs.Machine.ClBrute
