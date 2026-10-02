import Lax117284Proofs.Treewidth.Chars.Alg
import Lax117284Proofs.Treewidth.Trees.NiceLemmas

/-!
# Kloks' conversion, part 1: `forgetMany`, `introMany`, the child converter and the join fold (C8a)

Specifications of the building blocks of `niceOf`, each proved by induction on the list:

* `forgetMany_spec` / `introMany_spec` : shape (`Wf`), root bag, vertices, the bags occurring, the connectedness
  predicate `NConn`, and the number of nodes;
* `conv_spec`  : `conv X t = introMany (X \ bag t) (forgetMany (bag t \ X) t)` has root bag `X`;
* `fold_spec`, `fold_nconn` : the left fold of `NT.join` over trees with a common bag.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Trees Lax117284Proofs.Treewidth.Trees.NT

theorem forgetMany_nil (t : NT) : forgetMany [] t = t := rfl
theorem forgetMany_cons (x : ℕ) (l : List ℕ) (t : NT) : forgetMany (x :: l) t = forgetMany l (NT.forget x t) := rfl
theorem introMany_nil (t : NT) : introMany [] t = t := rfl
theorem introMany_cons (x : ℕ) (l : List ℕ) (t : NT) : introMany (x :: l) t = introMany l (NT.intro x t) := rfl

theorem vs_forget_eq (x : ℕ) (t : NT) : (NT.forget x t).vs = t.vs := by
  rw [vs_forget]
  apply Finset.union_eq_right.2
  intro u hu
  exact bag_subset_vs t (Finset.mem_of_mem_erase hu)

theorem vs_intro_eq (x : ℕ) (t : NT) : (NT.intro x t).vs = insert x t.vs := by
  rw [vs_intro, bag_intro]
  ext u
  simp only [Finset.mem_union, Finset.mem_insert]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (bag_subset_vs t h)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h

theorem forgetMany_spec : ∀ (l : List ℕ) (t : NT), l.Nodup → (∀ x ∈ l, x ∈ t.bag) → t.Wf →
    (forgetMany l t).Wf ∧ (forgetMany l t).bag = t.bag \ l.toFinset ∧ (forgetMany l t).vs = t.vs ∧
    (∀ Y ∈ (forgetMany l t).bs, ∃ Z ∈ t.bs, Y ⊆ Z) ∧ (∀ Y ∈ t.bs, Y ∈ (forgetMany l t).bs) ∧
    (t.NConn → (forgetMany l t).NConn) ∧ (forgetMany l t).size = t.size + l.length := by
  intro l
  induction l with
  | nil =>
    intro t _ _ hw
    refine ⟨hw, by simp [forgetMany_nil], rfl, fun Y hY => ⟨Y, hY, Finset.Subset.refl _⟩, fun Y hY => hY,
      fun h => h, by simp [forgetMany_nil]⟩
  | cons x l ih =>
    intro t hnd hmem hw
    have hx : x ∈ t.bag := hmem x (by simp)
    have hnd' := List.nodup_cons.1 hnd
    have hw' : (NT.forget x t).Wf := ⟨hx, hw⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih (NT.forget x t) hnd'.2
      (fun y hy => by
        rw [bag_forget]
        exact Finset.mem_erase.2 ⟨fun e => hnd'.1 (e ▸ hy), hmem y (by simp [hy])⟩) hw'
    rw [forgetMany_cons]
    refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h2, bag_forget]
      ext u; simp [and_assoc, and_comm, and_left_comm]
    · rw [h3, vs_forget_eq]
    · intro Y hY
      obtain ⟨Z, hZ, hYZ⟩ := h4 Y hY
      rw [bs_forget, List.mem_cons] at hZ
      rcases hZ with rfl | hZ
      · exact ⟨t.bag, bag_mem_bs t, hYZ.trans (by rw [bag_forget]; exact Finset.erase_subset _ _)⟩
      · exact ⟨Z, hZ, hYZ⟩
    · intro Y hY
      apply h5
      rw [bs_forget]; exact List.mem_cons_of_mem _ hY
    · intro hn
      apply h6
      simpa [NConn] using hn
    · rw [h7]; simp [NT.size]; omega

theorem introMany_spec : ∀ (l : List ℕ) (t : NT), l.Nodup → (∀ x ∈ l, x ∉ t.bag) → t.Wf →
    (introMany l t).Wf ∧ (introMany l t).bag = t.bag ∪ l.toFinset ∧ (introMany l t).vs = t.vs ∪ l.toFinset ∧
    (∀ Y ∈ (introMany l t).bs, Y ∈ t.bs ∨ Y ⊆ t.bag ∪ l.toFinset) ∧ (∀ Y ∈ t.bs, Y ∈ (introMany l t).bs) ∧
    ((∀ x ∈ l, x ∉ t.vs) → t.NConn → (introMany l t).NConn) ∧ (introMany l t).size = t.size + l.length := by
  intro l
  induction l with
  | nil =>
    intro t _ _ hw
    refine ⟨hw, by simp [introMany_nil], by simp [introMany_nil], fun Y hY => Or.inl hY, fun Y hY => hY,
      fun _ h => h, by simp [introMany_nil]⟩
  | cons x l ih =>
    intro t hnd hmem hw
    have hx : x ∉ t.bag := hmem x (by simp)
    have hnd' := List.nodup_cons.1 hnd
    have hw' : (NT.intro x t).Wf := ⟨hx, hw⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih (NT.intro x t) hnd'.2
      (fun y hy => by
        rw [bag_intro]
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun e => hnd'.1 (e ▸ hy), hmem y (by simp [hy])⟩) hw'
    rw [introMany_cons]
    refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h2, bag_intro]
      ext u; simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]; tauto
    · rw [h3, vs_intro_eq]
      ext u; simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]; tauto
    · intro Y hY
      rcases h4 Y hY with hY | hY
      · rw [bs_intro, List.mem_cons] at hY
        rcases hY with rfl | hY
        · right
          rw [bag_intro]
          intro u hu
          simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons] at hu ⊢
          tauto
        · exact Or.inl hY
      · right
        rw [bag_intro] at hY
        intro u hu
        have := hY hu
        simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons] at this ⊢
        tauto
    · intro Y hY
      apply h5
      rw [bs_intro]; exact List.mem_cons_of_mem _ hY
    · intro hv hn
      apply h6
      · intro y hy
        rw [vs_intro_eq]
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun e => hnd'.1 (e ▸ hy), hv y (by simp [hy])⟩
      · exact ⟨hv x (by simp), hn⟩
    · rw [h7]; simp [NT.size]; omega

/-- The child converter of `niceOf`: forget what the child has extra, introduce what it lacks. -/
def conv (X : Finset ℕ) (t : NT) : NT :=
  introMany ((X \ t.bag).sort (· ≤ ·)) (forgetMany ((t.bag \ X).sort (· ≤ ·)) t)

theorem conv_spec (X : Finset ℕ) (t : NT) (hw : t.Wf) :
    (conv X t).Wf ∧ (conv X t).bag = X ∧ (conv X t).vs = t.vs ∪ X ∧
    (∀ Y ∈ (conv X t).bs, (∃ Z ∈ t.bs, Y ⊆ Z) ∨ Y ⊆ X) ∧ (∀ Y ∈ t.bs, Y ∈ (conv X t).bs) ∧
    ((∀ v ∈ X, v ∈ t.vs → v ∈ t.bag) → t.NConn → (conv X t).NConn) ∧
    (conv X t).size = t.size + (t.bag \ X).card + (X \ t.bag).card := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := forgetMany_spec ((t.bag \ X).sort (· ≤ ·)) t
    (Finset.sort_nodup _ _) (fun x hx => (Finset.mem_sdiff.1 ((Finset.mem_sort _).1 hx)).1) hw
  rw [Finset.sort_toFinset] at f2
  have hb : (forgetMany ((t.bag \ X).sort (· ≤ ·)) t).bag = t.bag ∩ X := by
    rw [f2]; ext u; simp
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := introMany_spec ((X \ t.bag).sort (· ≤ ·))
    (forgetMany ((t.bag \ X).sort (· ≤ ·)) t) (Finset.sort_nodup _ _)
    (fun x hx => by
      rw [hb]
      have := (Finset.mem_sdiff.1 ((Finset.mem_sort _).1 hx)).2
      simp [this]) f1
  simp only [Finset.sort_toFinset] at i2 i3 i4
  refine ⟨i1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [conv, i2, hb]
    ext u; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  · rw [conv, i3, f3]
    ext u; simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · by_cases hu : u ∈ t.bag
        · exact Or.inl (bag_subset_vs t hu)
        · exact Or.inr ⟨h, hu⟩
  · intro Y hY
    rw [conv] at hY
    rcases i4 Y hY with hY | hY
    · obtain ⟨Z, hZ, hYZ⟩ := f4 Y hY
      exact Or.inl ⟨Z, hZ, hYZ⟩
    · right
      refine hY.trans ?_
      rw [hb]
      intro u hu; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hu; tauto
  · intro Y hY
    exact i5 _ (f5 Y hY)
  · intro hX hn
    rw [conv]
    apply i6
    · intro x hx
      rw [f3]
      have := (Finset.mem_sdiff.1 ((Finset.mem_sort _).1 hx))
      intro hxv
      exact this.2 (hX x this.1 hxv)
    · exact f6 hn
  · rw [conv, i7, f7, Finset.length_sort, Finset.length_sort]

end Lax117284Proofs.Treewidth.Chars
