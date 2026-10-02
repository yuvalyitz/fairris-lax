import Lax117284Proofs.Treewidth.Trees.WordLayout

/-!
# The subtree of a node of a word in arbitrary layout (T2)

`desc D i` (the nodes below `i`) satisfies: it is closed under children, contained in `[0, i]`, transitive, its members
are linearly ordered along parent chains, the two subtrees of a join are disjoint, and `desc D (N-1)` is everything.
All from `Lay` (the unique parent).
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace Word

open Lax117284.GraphWords

variable {n : ℕ} {D : List ℕ}

lemma self_mem_desc (D : List ℕ) (i : ℕ) : i ∈ desc D i := by
  cases i with
  | zero => simp [desc_zero]
  | succ i =>
    rw [desc]
    split_ifs <;> simp

lemma desc_le (D : List ℕ) : ∀ i j, j ∈ desc D i → j ≤ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j hj
    cases i with
    | zero => simp [desc_zero] at hj; omega
    | succ i =>
      rw [desc] at hj
      split_ifs at hj with h1 h2 h3
      · rcases Finset.mem_insert.1 hj with rfl | hj
        · exact le_rfl
        · exact (ih i (by omega) j hj).trans (by omega)
      · rcases Finset.mem_insert.1 hj with rfl | hj
        · exact le_rfl
        · rcases Finset.mem_union.1 hj with hj | hj
          · exact (ih i (by omega) j hj).trans (by omega)
          · exact (ih _ (by omega) j hj).trans (by omega)
      · simp at hj; omega
      · simp at hj; omega

lemma kind_zero (L : Lay n D) : kind D 0 = 0 := by
  rcases L.shape 0 L.nonempty with h | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact h
  all_goals omega

/-- Children of the node `i + 1`. -/
lemma Lay.isChild_succ_leaf (_L : Lay n D) {i c : ℕ} (_hi : i + 1 < nodeCount D) (h1 : kind D (i + 1) ≠ 1)
    (h2 : kind D (i + 1) ≠ 2) (h3 : kind D (i + 1) ≠ 3) : ¬ IsChild D c (i + 1) := by
  rintro ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩ <;> omega

lemma Lay.isChild_succ_unary (_L : Lay n D) {i c : ℕ} (hk : kind D (i + 1) = 1 ∨ kind D (i + 1) = 2)
    (hi : i + 1 < nodeCount D) : IsChild D c (i + 1) ↔ c = i := by
  constructor
  · rintro ⟨-, ⟨-, h⟩ | ⟨h, -⟩⟩
    · omega
    · omega
  · rintro rfl; exact ⟨hi, Or.inl ⟨hk, rfl⟩⟩

lemma Lay.isChild_succ_join (_L : Lay n D) {i c : ℕ} (hk : kind D (i + 1) = 3)
    (hi : i + 1 < nodeCount D) : IsChild D c (i + 1) ↔ c = i ∨ c = other D (i + 1) := by
  constructor
  · rintro ⟨-, ⟨h, -⟩ | ⟨-, h | h⟩⟩
    · omega
    · left; omega
    · right; exact h
  · rintro (rfl | rfl)
    · exact ⟨hi, Or.inr ⟨hk, Or.inl rfl⟩⟩
    · exact ⟨hi, Or.inr ⟨hk, Or.inr rfl⟩⟩

lemma Lay.not_isChild_zero (L : Lay n D) {c : ℕ} : ¬ IsChild D c 0 := by
  rintro ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩ <;> rw [kind_zero L] at h <;> omega

/-- Descent: a node is below `m` iff it is `m` or below a child. -/
lemma Lay.mem_desc_iff (L : Lay n D) {m x : ℕ} (hm : m < nodeCount D) :
    x ∈ desc D m ↔ x = m ∨ ∃ c, IsChild D c m ∧ x ∈ desc D c := by
  cases m with
  | zero =>
    simp only [desc_zero, Finset.mem_singleton]
    constructor
    · exact Or.inl
    · rintro (h | ⟨c, hc, -⟩)
      · exact h
      · exact absurd hc L.not_isChild_zero
  | succ i =>
    rcases L.node hm with ⟨h1, h2, h3⟩ | ⟨hkd, -, -⟩ | ⟨hkd, -, -⟩ | ⟨hkd, ho, -⟩
    · rw [desc_leaf h1 h2 h3]
      simp only [Finset.mem_singleton]
      constructor
      · exact Or.inl
      · rintro (h | ⟨c, hc, -⟩)
        · exact h
        · exact absurd hc (L.isChild_succ_leaf hm h1 h2 h3)
    · rw [desc_intro hkd, Finset.mem_insert]
      simp only [L.isChild_succ_unary (Or.inl hkd) hm]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨i, rfl, h⟩
      · rintro (h | ⟨c, rfl, h⟩)
        · exact Or.inl h
        · exact Or.inr h
    · rw [desc_forget hkd, Finset.mem_insert]
      simp only [L.isChild_succ_unary (Or.inr hkd) hm]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨i, rfl, h⟩
      · rintro (h | ⟨c, rfl, h⟩)
        · exact Or.inl h
        · exact Or.inr h
    · rw [desc_join hkd ho, Finset.mem_insert, Finset.mem_union]
      simp only [L.isChild_succ_join hkd hm]
      constructor
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inr ⟨i, Or.inl rfl, h⟩
        · exact Or.inr ⟨_, Or.inr rfl, h⟩
      · rintro (h | ⟨c, rfl | rfl, h⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

/-- Children have smaller indices. -/
lemma Lay.child_desc_sub (L : Lay n D) {c p : ℕ} (h : IsChild D c p) : desc D c ⊆ desc D p := by
  intro x hx
  exact (L.mem_desc_iff h.1).2 (Or.inr ⟨c, h, hx⟩)

/-- Transitivity of descent. -/
lemma Lay.desc_trans (L : Lay n D) : ∀ c a b, c < nodeCount D → a ∈ desc D b → b ∈ desc D c → a ∈ desc D c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro a b hc hab hbc
    rcases (L.mem_desc_iff hc).1 hbc with rfl | ⟨c', hc', hbc'⟩
    · exact hab
    · have hlt := L.isChild_lt hc'
      exact L.child_desc_sub hc' (ih c' hlt.1 a b (by omega) hab hbc')

lemma Lay.desc_sub_of_mem (L : Lay n D) {b c : ℕ} (hc : c < nodeCount D) (h : b ∈ desc D c) :
    desc D b ⊆ desc D c := fun _ ha => L.desc_trans c _ b hc ha h

/-- The parent, unique. -/
lemma Lay.parent_unique (L : Lay n D) {x p q : ℕ} (hp : IsChild D x p) (hq : IsChild D x q) : p = q := by
  have hx : x + 1 < nodeCount D := by
    have := L.isChild_lt hp; omega
  obtain ⟨r, -, hr⟩ := L.parent x hx
  rw [hr p hp, hr q hq]

/-- Every node is below the last one. -/
lemma Lay.desc_full (L : Lay n D) : desc D (nodeCount D - 1) = Finset.range (nodeCount D) := by
  have hN := L.nonempty
  ext x
  simp only [Finset.mem_range]
  constructor
  · intro hx; have := desc_le D _ x hx; omega
  · intro hx
    obtain ⟨k, hk⟩ : ∃ k, nodeCount D - 1 - x = k := ⟨_, rfl⟩
    induction k using Nat.strong_induction_on generalizing x with
    | _ k ih =>
      by_cases hxl : x = nodeCount D - 1
      · subst hxl; exact self_mem_desc D _
      · have hx1 : x + 1 < nodeCount D := by omega
        obtain ⟨p, hp, -⟩ := L.parent x hx1
        have hlt := L.isChild_lt hp
        have hpm : p ∈ desc D (nodeCount D - 1) := ih (nodeCount D - 1 - p) (by omega) p hlt.2 rfl
        exact L.desc_sub_of_mem (by omega) hpm ((L.mem_desc_iff hlt.2).2 (Or.inr ⟨x, hp, self_mem_desc D x⟩))

end Word

end Lax117284Proofs.Treewidth.Trees
