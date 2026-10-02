import Lax117284Proofs.Treewidth.Seq.Dom
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Order.Interval.Finset.Nat

/-!
# Concatenation and splits (Lemmas 3.17–3.20, Def. 3.10)

Concatenation `∘ab` of the paper is `a ++ b`.
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- **Lemma 3.17**: `τ(∘ab) = τ(∘τ(a)τ(b))`. -/
theorem typical_append_typical (a b : List ℕ) :
    typical (a ++ b) = typical (typical a ++ typical b) :=
  typical_reach ((reach_typical a).append (reach_typical b))

theorem typical_append_typical_left (a b : List ℕ) :
    typical (a ++ b) = typical (typical a ++ b) :=
  typical_reach ((reach_typical a).append_right b)

theorem typical_append_typical_right (a b : List ℕ) :
    typical (a ++ b) = typical (a ++ typical b) :=
  typical_reach ((reach_typical b).append_left a)

/-- **Lemma 3.18**: `a* ∈ E(a)`, `b* ∈ E(b)` ⟹ `∘a*b* ∈ E(∘ab)`. -/
theorem ext_append {a b a' b' : List ℕ} (h1 : Ext a a') (h2 : Ext b b') :
    Ext (a ++ b) (a' ++ b') := h1.append h2

/-- **Lemma 3.19**: `a' ≺ a` and `b' ≺ b` ⟹ `∘a'b' ≺ ∘ab`. -/
theorem Dom.append {a b a' b' : List ℕ} (h1 : Dom a' a) (h2 : Dom b' b) :
    Dom (a' ++ b') (a ++ b) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h1
  obtain ⟨u, v, hu, hv, huv⟩ := h2
  exact ⟨x ++ u, y ++ v, hx.append hu, hy.append hv, hxy.append huv⟩

theorem DomEquiv.append {a b a' b' : List ℕ} (h1 : DomEquiv a' a) (h2 : DomEquiv b' b) :
    DomEquiv (a' ++ b') (a ++ b) := ⟨h1.1.append h2.1, h1.2.append h2.2⟩

/-! ### Splits (Def. 3.10) -/

/-- A split of the first type: `δ₁ = (a₁..a_f)`, `δ₂ = (a_f..a_n)` (`1 ≤ f ≤ n`). -/
def Split1 (a d1 d2 : List ℕ) : Prop :=
  ∃ f, 1 ≤ f ∧ f ≤ a.length ∧ d1 = a.take f ∧ d2 = a.drop (f - 1)

/-- A split of the second type: `δ₁ = (a₁..a_f)`, `δ₂ = (a_{f+1}..a_n)` (`1 ≤ f < n`, so that
`δ₂` is a sequence). -/
def Split2 (a d1 d2 : List ℕ) : Prop :=
  ∃ f, 1 ≤ f ∧ f < a.length ∧ d1 = a.take f ∧ d2 = a.drop f

/-- The splits of the first type, as a finite set. -/
def splits1 (a : List ℕ) : Finset (List ℕ × List ℕ) :=
  (Finset.Icc 1 a.length).image (fun f => (a.take f, a.drop (f - 1)))

/-- The splits of the second type, as a finite set. -/
def splits2 (a : List ℕ) : Finset (List ℕ × List ℕ) :=
  (Finset.Ico 1 a.length).image (fun f => (a.take f, a.drop f))

/-- All splits of `a` (both types). -/
def splits (a : List ℕ) : Finset (List ℕ × List ℕ) := splits1 a ∪ splits2 a

theorem mem_splits1 {a d1 d2 : List ℕ} : (d1, d2) ∈ splits1 a ↔ Split1 a d1 d2 := by
  unfold splits1 Split1
  simp only [Finset.mem_image, Finset.mem_Icc, Prod.mk.injEq]
  constructor
  · rintro ⟨f, ⟨h1, h2⟩, rfl, rfl⟩; exact ⟨f, h1, h2, rfl, rfl⟩
  · rintro ⟨f, h1, h2, rfl, rfl⟩; exact ⟨f, ⟨h1, h2⟩, rfl, rfl⟩

theorem mem_splits2 {a d1 d2 : List ℕ} : (d1, d2) ∈ splits2 a ↔ Split2 a d1 d2 := by
  unfold splits2 Split2
  simp only [Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro ⟨f, ⟨h1, h2⟩, rfl, rfl⟩; exact ⟨f, h1, h2, rfl, rfl⟩
  · rintro ⟨f, h1, h2, rfl, rfl⟩; exact ⟨f, ⟨h1, h2⟩, rfl, rfl⟩

theorem mem_splits {a d1 d2 : List ℕ} :
    (d1, d2) ∈ splits a ↔ Split1 a d1 d2 ∨ Split2 a d1 d2 := by
  unfold splits; rw [Finset.mem_union, mem_splits1, mem_splits2]

/-! ### Lemma 3.20 -/

/-- Cutting an extension after the block of the first `f` entries. -/
theorem ext_cut : ∀ {t a : List ℕ} (f : ℕ), Ext t a →
    ∃ a1 a2, a = a1 ++ a2 ∧ Ext (t.take f) a1 ∧ Ext (t.drop f) a2 := by
  intro t
  induction t with
  | nil =>
    intro a f h
    rw [ext_nil_iff] at h; subst h
    exact ⟨[], [], rfl, by simp, by simp⟩
  | cons x t ih =>
    intro a f h
    cases f with
    | zero => exact ⟨[], a, rfl, by simp, by simpa using h⟩
    | succ f =>
      obtain ⟨p, a0, rfl, ha0⟩ := ext_cons_iff.mp h
      obtain ⟨a1, a2, rfl, h1, h2⟩ := ih f ha0
      refine ⟨List.replicate (p + 1) x ++ a1, a2, by simp, ?_, by simpa using h2⟩
      rw [List.take_succ_cons]
      exact ext_cons_iff.mpr ⟨p, a1, rfl, h1⟩

theorem ext_getLast? : ∀ {u w : List ℕ}, Ext u w → w.getLast? = u.getLast? := by
  intro u w
  induction w generalizing u with
  | nil => intro h; rw [ext_nil_right] at h; subst h; rfl
  | cons y w ih =>
    intro h
    cases u with
    | nil => exact absurd h (ext_nil_cons _ _)
    | cons x a =>
      obtain ⟨rfl, h | h⟩ := ext_cons_cons.mp h
      · cases w with
        | nil => exact absurd h (ext_cons_nil _ _)
        | cons z w' =>
          rw [List.getLast?_cons_cons]; exact ih h
      · cases w with
        | nil =>
          rw [ext_nil_right] at h; subst h; rfl
        | cons z w' =>
          rw [List.getLast?_cons_cons, ih h]
          cases a with
          | nil => exact absurd h (ext_nil_cons _ _)
          | cons b a' => rw [List.getLast?_cons_cons]

/-- The pieces of a split of a normal form are normal forms. -/
theorem nf_of_split {t d1 d2 : List ℕ} (ht : NF t) (h : Split1 t d1 d2 ∨ Split2 t d1 d2) :
    NF d1 ∧ NF d2 := by
  rcases h with ⟨f, -, -, rfl, rfl⟩ | ⟨f, -, -, rfl, rfl⟩
  · refine ⟨?_, ?_⟩
    · rw [← List.take_append_drop f t] at ht; exact ht.append_left
    · rw [← List.take_append_drop (f - 1) t] at ht; exact ht.append_right
  · refine ⟨?_, ?_⟩
    · rw [← List.take_append_drop f t] at ht; exact ht.append_left
    · rw [← List.take_append_drop f t] at ht; exact ht.append_right

/-- **Lemma 3.20**, second half: if `a₁ ∈ E(δ₁)`, `a₂ ∈ E(δ₂)` for the pieces of a split of
a typical sequence, then `τ(a₁) = δ₁` and `τ(a₂) = δ₂`. -/
theorem typical_of_split_ext {t d1 d2 a1 a2 : List ℕ} (ht : NF t)
    (h : Split1 t d1 d2 ∨ Split2 t d1 d2) (h1 : Ext d1 a1) (h2 : Ext d2 a2) :
    typical a1 = d1 ∧ typical a2 = d2 := by
  obtain ⟨n1, n2⟩ := nf_of_split ht h
  exact ⟨by rw [h1.typical, typical_of_nf n1], by rw [h2.typical, typical_of_nf n2]⟩

theorem ext_ne_nil {u w : List ℕ} (h : Ext u w) (hu : u ≠ []) : w ≠ [] := by
  rintro rfl; exact hu (ext_nil_right.mp h)

/-- **Lemma 3.20**, first half (existence), first type. -/
theorem split1_ext_exists {t a d1 d2 : List ℕ} (hext : Ext t a) (h : Split1 t d1 d2) :
    ∃ a1 a2, Split1 a a1 a2 ∧ Ext d1 a1 ∧ Ext d2 a2 := by
  obtain ⟨f, hf1, hf2, rfl, rfl⟩ := h
  obtain ⟨a1, a2, rfl, h1, h2⟩ := ext_cut (f - 1) hext
  have hdrop : t.drop (f - 1) = t[f - 1] :: t.drop f := by
    rw [List.drop_eq_getElem_cons (by omega)]
    congr 2; omega
  have hd2 := h2
  rw [hdrop] at h2
  obtain ⟨p, a3, rfl, h3⟩ := ext_cons_iff.mp h2
  set x := t[f - 1] with hx
  have htake : t.take f = t.take (f - 1) ++ [x] := by
    have := List.take_succ_eq_append_getElem (l := t) (i := f - 1) (by omega)
    rwa [Nat.sub_add_cancel hf1] at this
  have e1 : a1 ++ (List.replicate (p + 1) x ++ a3) = (a1 ++ List.replicate (p + 1) x) ++ a3 := by
    simp
  have e2 : a1 ++ (List.replicate (p + 1) x ++ a3) = (a1 ++ List.replicate p x) ++ (x :: a3) := by
    simp [List.replicate_succ']
  refine ⟨a1 ++ List.replicate (p + 1) x, x :: a3, ⟨a1.length + p + 1, by omega,
    by simp; omega, ?_, ?_⟩, ?_, ?_⟩
  · rw [e1]; exact (List.take_left' (by simp; omega)).symm
  · have : a1.length + p + 1 - 1 = (a1 ++ List.replicate p x).length := by simp
    rw [this, e2]; exact (List.drop_left' rfl).symm
  · rw [htake]
    have hr : Ext [x] (List.replicate (p + 1) x) := by
      have := ext_replicate (x := x) (p := 1) (q := p + 1) (by omega) (by omega)
      simpa using this
    exact Ext.append h1 hr
  · rw [hdrop]; exact ext_cons_cons.mpr ⟨rfl, Or.inr h3⟩

/-- **Lemma 3.20**, first half (existence), second type. -/
theorem split2_ext_exists {t a d1 d2 : List ℕ} (hext : Ext t a) (h : Split2 t d1 d2) :
    ∃ a1 a2, Split2 a a1 a2 ∧ Ext d1 a1 ∧ Ext d2 a2 := by
  obtain ⟨f, hf1, hf2, rfl, rfl⟩ := h
  obtain ⟨a1, a2, rfl, h1, h2⟩ := ext_cut f hext
  have hne1 : t.take f ≠ [] := by
    intro h0
    have h1 : (t.take f).length = f := by simp; omega
    rw [h0] at h1; simp at h1; omega
  have hne2 : t.drop f ≠ [] := by
    intro h0
    have h1 : (t.drop f).length = t.length - f := by simp
    rw [h0] at h1; simp at h1; omega
  have ha1 := ext_ne_nil h1 hne1
  have ha2 := ext_ne_nil h2 hne2
  refine ⟨a1, a2, ⟨a1.length, List.length_pos_iff.mpr ha1, ?_, ?_, ?_⟩, h1, h2⟩
  · simp; exact List.length_pos_iff.mpr ha2
  · exact (List.take_left).symm
  · exact (List.drop_left).symm

/-- **Lemma 3.20** for splits of the first type (both halves). -/
theorem lemma_3_20_split1 {a d1 d2 : List ℕ} (hext : Ext (typical a) a)
    (h : Split1 (typical a) d1 d2) :
    ∃ a1 a2, Split1 a a1 a2 ∧ Ext d1 a1 ∧ Ext d2 a2 ∧ typical a1 = d1 ∧ typical a2 = d2 := by
  obtain ⟨a1, a2, hs, h1, h2⟩ := split1_ext_exists hext h
  obtain ⟨t1, t2⟩ := typical_of_split_ext (nf_typical a) (Or.inl h) h1 h2
  exact ⟨a1, a2, hs, h1, h2, t1, t2⟩

/-- **Lemma 3.20** for splits of the second type (both halves). -/
theorem lemma_3_20_split2 {a d1 d2 : List ℕ} (hext : Ext (typical a) a)
    (h : Split2 (typical a) d1 d2) :
    ∃ a1 a2, Split2 a a1 a2 ∧ Ext d1 a1 ∧ Ext d2 a2 ∧ typical a1 = d1 ∧ typical a2 = d2 := by
  obtain ⟨a1, a2, hs, h1, h2⟩ := split2_ext_exists hext h
  obtain ⟨t1, t2⟩ := typical_of_split_ext (nf_typical a) (Or.inr h) h1 h2
  exact ⟨a1, a2, hs, h1, h2, t1, t2⟩

end Lax117284Proofs.Treewidth.Seq
