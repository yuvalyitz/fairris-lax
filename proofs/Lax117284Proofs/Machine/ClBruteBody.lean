import Lax117284Proofs.Machine.ClBruteEval

/-!
One round of the search: test the vector, record a success, add one.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

/-- The cost of the increment. -/
def costOdo (m n : ℕ) : ℕ := 2 + ((20 + 4) * (m * n) + 6)

/-- The cost of one round. -/
def costBody (m n : ℕ) : ℕ := costEval m n + (7 + (costOdo m n + 2))

/-- The state of the search: the vector `f` in `bfsc`; while `bfdn = 0`, `bfans` says whether a
vector below `f` passed; once `bfdn = 1`, whether any vector passed. -/
def J (x : List ℕ) (I : Instance) (k : ℕ) (σ : Env) : Prop :=
  ∃ f : ℕ → ℕ, Ctx x I k f σ ∧ σ.vars "bfans" ≤ 1 ∧ σ.vars "bfdn" ≤ 1 ∧
    (σ.vars "bfdn" = 0 → (σ.vars "bfans" = 1 ↔
      ∃ s, s < enc f (I.days * I.clients) ∧ Chk I k s)) ∧
    (σ.vars "bfdn" = 1 → (σ.vars "bfans" = 1 ↔ ∃ s, s < 2 ^ (I.days * I.clients) ∧ Chk I k s))

/-- The number of the vector in `bfsc`. -/
def encA (I : Instance) (σ : Env) : ℕ :=
  enc (fun r => (σ.arrs "bfsc").getD r 0) (I.days * I.clients)

/-- What is left to search. -/
def Vm (I : Instance) (σ : Env) : ℕ :=
  if σ.vars "bfdn" = 0 then 2 ^ (I.days * I.clients) - encA I σ else 0

lemma encA_eq {f : ℕ → ℕ} {σ : Env} (h : Ctx x I k f σ) : encA I σ = enc f (I.days * I.clients) :=
  enc_congr fun _ hr => h.scGet hr

lemma chk_iff {f : ℕ → ℕ} (hf : ∀ r, r < I.days * I.clients → f r ≤ 1) :
    Chk I k (enc f (I.days * I.clients)) ↔ FeasF I f ∧ FairF I k f := by
  have hd : ∀ r, r < I.days * I.clients → dig (enc f (I.days * I.clients)) r = f r :=
    fun r hr => dig_enc hf r hr
  unfold Chk
  rw [feasF_congr I hd, fairF_congr I hd]

lemma succ_exists (P : ℕ → Prop) (S : ℕ) :
    (∃ s, s < S + 1 ∧ P s) ↔ (∃ s, s < S ∧ P s) ∨ P S := by
  constructor
  · rintro ⟨s, hs, hp⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | rfl
    · exact Or.inl ⟨s, h, hp⟩
    · exact Or.inr hp
  · rintro (⟨s, hs, hp⟩ | hp)
    · exact ⟨s, by omega, hp⟩
    · exact ⟨S, by omega, hp⟩

open Classical in
lemma record_iff {ans0 ok S T : ℕ} {P : ℕ → Prop} (hT : T = S + 1)
    (h0 : ans0 = 1 ↔ ∃ s, s < S ∧ P s) (hok : ok = 1 ↔ P S) :
    (if ok = 1 then 1 else ans0) = 1 ↔ ∃ s, s < T ∧ P s := by
  rw [hT, succ_exists]
  by_cases h : ok = 1
  · rw [if_pos h]; exact ⟨fun _ => Or.inr (hok.mp h), fun _ => rfl⟩
  · rw [if_neg h, h0]
    constructor
    · exact Or.inl
    · rintro (h1 | h1)
      · exact h1
      · exact absurd (hok.mpr h1) h

theorem body_spec (hb : Bd B x I k) :
    Spec B (fun σ => J x I k σ ∧ σ.vars "bfdn" = 0) bodyCom
      (fun σ σ' => J x I k σ' ∧ Vm I σ' < Vm I σ) (costBody I.days I.clients) := by
  intro σ ⟨⟨f, hctx, hans, hdn, h0, h1⟩, hd0⟩
  have hbig := hb.big
  obtain ⟨σ1, hr1, hc1, hok1, hiff1, hans1, hdn1⟩ := evalCom_spec hb f σ hctx
  obtain ⟨σ2, hr2, hans2, hfv2, hfa2, -, -⟩ := (rec_spec (B := B)).frame σ1
    ⟨hok1, by omega⟩
  have hc2 : Ctx x I k f σ2 := hc1.frame hfv2 hfa2 (by decide) (by decide) (by decide)
  obtain ⟨σ3, hr3, ⟨g, hc3, hcy3, henc3, -⟩, hfv3, hfa3, -, -⟩ := (odoCom_spec hb f).frame σ2 hc2
  obtain ⟨σ4, hr4, h4⟩ := (Spec.assign (B := B) (x := "bfdn") (e := V "bfcy")
    (f := fun σ => σ.vars "bfcy")
    (P := fun σ => σ.vars "bfcy" ≤ 1)
    (fun σ h => evalB_var (by omega))) σ3 hcy3
  have hsv : (V "bfcy").size = 1 := rfl
  have hc4 : Ctx x I k g σ4 := by rw [h4]; exact hc3.setVar _ (by decide)
  have hans3 : σ3.vars "bfans" = σ2.vars "bfans" := hfv3 _ (by decide)
  have hans4 : σ4.vars "bfans" = σ3.vars "bfans" := by rw [h4]; simp
  have hdn4 : σ4.vars "bfdn" = σ3.vars "bfcy" := by rw [h4]; simp
  have hS : enc f (I.days * I.clients) < 2 ^ (I.days * I.clients) := enc_lt hctx.hf
  have hset : σ2.vars "bfans" =
      if σ1.vars "bfok" = 1 then 1 else σ1.vars "bfans" := hans2
  have hv : σ1.vars "bfans" = σ.vars "bfans" := hans1
  have hdn' : σ1.vars "bfdn" = σ.vars "bfdn" := hdn1
  have hchk : σ1.vars "bfok" = 1 ↔ Chk I k (enc f (I.days * I.clients)) := by
    rw [chk_iff hctx.hf]; exact hiff1
  have h0' := h0 hd0
  have hV : Vm I σ = 2 ^ (I.days * I.clients) - enc f (I.days * I.clients) := by
    rw [Vm, if_pos hd0, encA_eq hctx]
  have hE4 : encA I σ4 = enc g (I.days * I.clients) := encA_eq hc4
  refine ⟨σ4, hr1.seq (hr2.seq (hr3.seq hr4)) |>.mono (le_of_eq (by simp only [hsv]; rfl)),
    ⟨g, hc4, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hans4, hans3, hset, hv]; split_ifs <;> omega
  · rw [hdn4]; exact hcy3
  · intro hd
    rw [hdn4] at hd
    rw [hd] at henc3
    rw [hans4, hans3, hset, hv]
    refine record_iff (by omega) h0' hchk
  · intro hd
    rw [hdn4] at hd
    rw [hd] at henc3
    rw [hans4, hans3, hset, hv]
    refine record_iff (by omega) h0' hchk
  · rw [hV, Vm, hdn4]
    by_cases hc : σ3.vars "bfcy" = 0
    · rw [if_pos hc, hE4]; rw [hc] at henc3; omega
    · rw [if_neg hc]; omega

end Lax117284Proofs.Machine.ClBrute
