import Lax117284Proofs.Treewidth.Seq.Concat

/-!
# Split transport (S1): the sequence-level heart of the introduce transition

`Dom` transports splits in both directions:

* `split_transport_up`: if `y ≺ a` and `a` is split (exactly, or by duplicating one entry), then `y`
  has a split (a `splits` pair of Def. 3.10) whose two parts dominate the two parts of `a`;
* `split_transport_down`: if `τ a ≺ y` and `(d₁, d₂)` is a split of `y`, then `a` has an exact split
  whose typical parts dominate `d₁, d₂`.

Both are corollaries of one *core lemma* (`dom_append_split`): if `s ≺ w₁ ++ w₂` (with `w₁, w₂ ≠ []`)
then `s` itself splits as `s₁, s₂` (`IsSplit`) with `s₁ ≺ w₁`, `s₂ ≺ w₂`.  The core lemma is the cut
of an extension of `s` at an arbitrary index (`ext_split_cases`), which either falls between two
blocks (an exact split) or inside a block (a split with one entry duplicated).

No typicality hypothesis is needed anywhere (the blueprint's `typical y = y` is redundant).
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- `a₁, a₂` is a split of the *exact* sequence `a`: either `a = a₁ ++ a₂` with both parts non-empty
(a cut between two entries), or `a = p ++ x :: q`, `a₁ = p ++ [x]`, `a₂ = x :: q` (a cut *at* an
entry, which is duplicated).  Both parts are non-empty. -/
def IsSplit (a a₁ a₂ : List ℕ) : Prop :=
  (a₁ ≠ [] ∧ a₂ ≠ [] ∧ a = a₁ ++ a₂) ∨ ∃ p x q, a = p ++ x :: q ∧ a₁ = p ++ [x] ∧ a₂ = x :: q

/-! ### Cutting an extension at an arbitrary index -/

theorem ext_append_split {w₁ w₂ v : List ℕ} (h : Ext (w₁ ++ w₂) v) :
    ∃ v₁ v₂, v = v₁ ++ v₂ ∧ Ext w₁ v₁ ∧ Ext w₂ v₂ := by
  obtain ⟨a1, a2, rfl, h1, h2⟩ := ext_cut w₁.length h
  rw [List.take_left' rfl] at h1
  rw [List.drop_left' rfl] at h2
  exact ⟨a1, a2, rfl, h1, h2⟩

theorem ext_dup (p q : List ℕ) (x : ℕ) : Ext (p ++ x :: q) ((p ++ [x]) ++ x :: q) := by
  have h : Ext (x :: q) (x :: x :: q) :=
    ext_cons_iff.mpr ⟨1, q, by simp [List.replicate_succ], Ext.refl q⟩
  have := Ext.append (Ext.refl p) h
  simpa using this

theorem ext_single_replicate {x m : ℕ} (hm : 1 ≤ m) : Ext [x] (List.replicate m x) := by
  simpa using ext_replicate (x := x) (p := 1) (q := m) le_rfl hm

/-- **Cut of an extension.**  An extension of `t` that is written `w₁ ++ w₂` (both non-empty) comes
from a cut of `t` between two entries, or at one entry (which is then shared). -/
theorem ext_split_cases : ∀ {t w₁ w₂ : List ℕ}, Ext t (w₁ ++ w₂) → w₁ ≠ [] → w₂ ≠ [] →
    (∃ t₁ t₂, t = t₁ ++ t₂ ∧ Ext t₁ w₁ ∧ Ext t₂ w₂) ∨
    (∃ p z q, t = p ++ z :: q ∧ Ext (p ++ [z]) w₁ ∧ Ext (z :: q) w₂) := by
  intro t
  induction t with
  | nil =>
    intro w₁ w₂ h h1 _
    rw [ext_nil_iff] at h
    exact absurd (List.append_eq_nil_iff.mp h).1 h1
  | cons x t ih =>
    intro w₁ w₂ h h1 h2
    obtain ⟨p, u, hw, hu⟩ := ext_cons_iff.mp h
    rcases List.append_eq_append_iff.mp hw with ⟨a', hrep, hw2⟩ | ⟨c', hw1, hu'⟩
    · -- the cut falls inside the first block of `x`
      obtain ⟨hlen, hw1, ha'⟩ := List.replicate_eq_append_iff.mp hrep
      by_cases ha0 : a' = []
      · subst ha0
        left
        refine ⟨[x], t, rfl, ?_, by simpa using (hw2 ▸ hu)⟩
        rw [hw1]
        exact ext_single_replicate (by
          have : w₁.length ≠ 0 := by simpa using h1
          omega)
      · right
        refine ⟨[], x, t, rfl, ?_, ?_⟩
        · rw [hw1]
          simp only [List.nil_append]
          exact ext_single_replicate (by
            have : w₁.length ≠ 0 := by simpa using h1
            omega)
        · refine ext_cons_iff.mpr ⟨a'.length - 1, u, ?_, hu⟩
          have : a'.length ≠ 0 := by simpa using ha0
          rw [hw2, ha']
          have hh : a'.length - 1 + 1 = a'.length := by omega
          simp [hh]
    · -- the cut falls after the first block of `x`
      by_cases hc0 : c' = []
      · subst hc0
        left
        rw [hu', List.nil_append] at hu
        refine ⟨[x], t, rfl, ?_, hu⟩
        rw [hw1]
        simpa using ext_single_replicate (x := x) (m := p + 1) (by omega)
      · rw [hu'] at hu
        rcases ih hu hc0 h2 with ⟨t₁, t₂, rfl, e1, e2⟩ | ⟨p', z, q, rfl, e1, e2⟩
        · left
          exact ⟨x :: t₁, t₂, rfl, ext_cons_iff.mpr ⟨p, c', hw1, e1⟩, e2⟩
        · right
          refine ⟨x :: p', z, q, rfl, ?_, e2⟩
          exact ext_cons_iff.mpr ⟨p, c', hw1, e1⟩

theorem ne_nil_of_ext {u w : List ℕ} (h : Ext u w) (hw : w ≠ []) : u ≠ [] := by
  rintro rfl
  exact hw (ext_nil_iff.mp h)

/-! ### The core lemma -/

/-- **Core.**  If `s ≺ w₁ ++ w₂` with `w₁, w₂` non-empty, then `s` splits into `s₁, s₂` with
`s₁ ≺ w₁` and `s₂ ≺ w₂`. -/
theorem dom_append_split {s w₁ w₂ : List ℕ} (h : Dom s (w₁ ++ w₂)) (h1 : w₁ ≠ []) (h2 : w₂ ≠ []) :
    ∃ s₁ s₂, IsSplit s s₁ s₂ ∧ Dom s₁ w₁ ∧ Dom s₂ w₂ := by
  obtain ⟨s', v, hs, hv, hle⟩ := h
  obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := ext_append_split hv
  have hle₁ : LeSeq (s'.take v₁.length) v₁ := List.forall₂_take_append s' v₁ v₂ hle
  have hle₂ : LeSeq (s'.drop v₁.length) v₂ := List.forall₂_drop_append s' v₁ v₂ hle
  have hs' : s' = s'.take v₁.length ++ s'.drop v₁.length := (List.take_append_drop _ _).symm
  set c₁ := s'.take v₁.length with hc₁
  set c₂ := s'.drop v₁.length with hc₂
  have hv₁0 : v₁ ≠ [] := by
    intro h0; subst h0; exact h1 (ext_nil_right.mp hv₁)
  have hv₂0 : v₂ ≠ [] := by
    intro h0; subst h0; exact h2 (ext_nil_right.mp hv₂)
  have hc₁0 : c₁ ≠ [] := by
    intro h0; rw [h0] at hle₁; exact hv₁0 (List.forall₂_nil_left_iff.mp hle₁)
  have hc₂0 : c₂ ≠ [] := by
    intro h0; rw [h0] at hle₂; exact hv₂0 (List.forall₂_nil_left_iff.mp hle₂)
  rw [hs'] at hs
  rcases ext_split_cases hs hc₁0 hc₂0 with ⟨t₁, t₂, rfl, e1, e2⟩ | ⟨p, z, q, rfl, e1, e2⟩
  · exact ⟨t₁, t₂, Or.inl ⟨ne_nil_of_ext e1 hc₁0, ne_nil_of_ext e2 hc₂0, rfl⟩,
      ⟨c₁, v₁, e1, hv₁, hle₁⟩, ⟨c₂, v₂, e2, hv₂, hle₂⟩⟩
  · exact ⟨p ++ [z], z :: q, Or.inr ⟨p, z, q, rfl, rfl, rfl⟩,
      ⟨c₁, v₁, e1, hv₁, hle₁⟩, ⟨c₂, v₂, e2, hv₂, hle₂⟩⟩

/-! ### Splits and `IsSplit` -/

/-- A split in the sense of `splits` is an `IsSplit`. -/
theorem isSplit_of_mem_splits {y d₁ d₂ : List ℕ} (h : (d₁, d₂) ∈ splits y) : IsSplit y d₁ d₂ := by
  rcases mem_splits.mp h with ⟨f, hf1, hf2, rfl, rfl⟩ | ⟨f, hf1, hf2, rfl, rfl⟩
  · right
    refine ⟨y.take (f - 1), y[f - 1], y.drop f, ?_, ?_, ?_⟩
    · have hd : y.drop (f - 1) = y[f - 1] :: y.drop f := by
        rw [List.drop_eq_getElem_cons (by omega)]
        congr 2; omega
      conv_lhs => rw [← List.take_append_drop (f - 1) y]
      rw [hd]
    · have := List.take_succ_eq_append_getElem (l := y) (i := f - 1) (by omega)
      rwa [Nat.sub_add_cancel hf1] at this
    · rw [List.drop_eq_getElem_cons (by omega)]
      congr 2; omega
  · left
    refine ⟨?_, ?_, (List.take_append_drop f y).symm⟩
    · intro h0
      have h1 : (y.take f).length = f := by simp; omega
      rw [h0] at h1; simp at h1; omega
    · intro h0
      have h1 : (y.drop f).length = y.length - f := by simp
      rw [h0] at h1; simp at h1; omega

/-- An `IsSplit` is a split in the sense of `splits`. -/
theorem mem_splits_of_isSplit {y d₁ d₂ : List ℕ} (h : IsSplit y d₁ d₂) : (d₁, d₂) ∈ splits y := by
  rcases h with ⟨h1, h2, rfl⟩ | ⟨p, x, q, rfl, rfl, rfl⟩
  · refine mem_splits.mpr (Or.inr ⟨d₁.length, List.length_pos_iff.mpr h1, ?_, ?_, ?_⟩)
    · simp; exact List.length_pos_iff.mpr h2
    · exact (List.take_left' rfl).symm
    · exact (List.drop_left' rfl).symm
  · refine mem_splits.mpr (Or.inl ⟨p.length + 1, by omega, by simp, ?_, ?_⟩)
    · have : p ++ x :: q = (p ++ [x]) ++ q := by simp
      rw [this, List.take_left' (by simp)]
    · rw [Nat.add_sub_cancel]
      exact (List.drop_left' rfl).symm

/-- An exact sequence is `≡` to the concatenation of the two parts of any of its splits (it is
an extension of it, or equal to it). -/
theorem IsSplit.dom_append {a a₁ a₂ : List ℕ} (h : IsSplit a a₁ a₂) : Dom a (a₁ ++ a₂) := by
  rcases h with ⟨-, -, rfl⟩ | ⟨p, x, q, rfl, rfl, rfl⟩
  · exact Dom.refl _
  · exact (domEquiv_of_ext (ext_dup p q x)).2

theorem IsSplit.ne_nil_left {a a₁ a₂ : List ℕ} (h : IsSplit a a₁ a₂) : a₁ ≠ [] := by
  rcases h with ⟨h1, -, -⟩ | ⟨p, x, q, -, rfl, -⟩
  · exact h1
  · simp

theorem IsSplit.ne_nil_right {a a₁ a₂ : List ℕ} (h : IsSplit a a₁ a₂) : a₂ ≠ [] := by
  rcases h with ⟨-, h2, -⟩ | ⟨p, x, q, -, -, rfl⟩
  · exact h2
  · simp

/-! ### The two transports -/

/-- **Split transport, upwards** (general form, no typicality needed).  If `y ≺ a` and `a₁, a₂` is
a split of the exact sequence `a`, then some split of `y` has parts `≺ a₁`, `≺ a₂`. -/
theorem split_up_of_dom {y a a₁ a₂ : List ℕ} (h : Dom y a) (hs : IsSplit a a₁ a₂) :
    ∃ d₁ d₂, (d₁, d₂) ∈ splits y ∧ Dom d₁ a₁ ∧ Dom d₂ a₂ := by
  obtain ⟨d₁, d₂, hd, h1, h2⟩ := dom_append_split (h.trans hs.dom_append) hs.ne_nil_left
    hs.ne_nil_right
  exact ⟨d₁, d₂, mem_splits_of_isSplit hd, h1, h2⟩

end Lax117284Proofs.Treewidth.Seq
