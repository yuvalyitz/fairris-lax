import Lax117284Proofs.Treewidth.Trees.WordTree

/-!
# Connectedness of occurrence sets in the word tree (T2)

`ConnOn D S`: the set `S` of nodes is nonempty and any two of its members are joined by a chain of tree edges
staying in `S`.  We prove, for a word with `Lay n D`:

* `Lay.loc_of_connOn`: if all the occurrence sets are connected, the local conditions `Loc` hold (a *cut* argument:
  the subtree below a node `c` is left only through `c`);
* `Lay.connOn_of_loc`: conversely, the local conditions give connected occurrence sets (a *gluing* induction).
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace Word

open Lax117284.GraphWords

variable {n : ℕ} {D : List ℕ}

/-- Adjacency of two nodes in the tree. -/
def Adj' (D : List ℕ) (a b : ℕ) : Prop := IsChild D a b ∨ IsChild D b a

lemma Adj'.symm' {a b : ℕ} (h : Adj' D a b) : Adj' D b a := Or.symm h

/-- The tree edges inside `S`. -/
def RelOn (D : List ℕ) (S : Set ℕ) (a b : ℕ) : Prop := a ∈ S ∧ b ∈ S ∧ Adj' D a b

/-- `S` is nonempty and connected by tree edges inside `S`. -/
def ConnOn (D : List ℕ) (S : Set ℕ) : Prop :=
  S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S, Relation.ReflTransGen (RelOn D S) x y

/-- The occurrence set of the vertex `v`. -/
def Sv (n : ℕ) (D : List ℕ) (v : ℕ) : Set ℕ := {j | j < nodeCount D ∧ v ∈ bagN n D j}

lemma RelOn.mono {S T : Set ℕ} (h : S ⊆ T) {a b : ℕ} (hab : RelOn D S a b) : RelOn D T a b :=
  ⟨h hab.1, h hab.2.1, hab.2.2⟩

lemma ConnOn.union {A B : Set ℕ} (hA : ConnOn D A) (hB : ConnOn D B) {x y : ℕ} (hx : x ∈ A) (hy : y ∈ B)
    (hxy : Adj' D x y) : ConnOn D (A ∪ B) := by
  have mA : ∀ {a b}, Relation.ReflTransGen (RelOn D A) a b → Relation.ReflTransGen (RelOn D (A ∪ B)) a b :=
    fun h => Relation.ReflTransGen.mono (fun _ _ hab => RelOn.mono Set.subset_union_left hab) _ _ h
  have mB : ∀ {a b}, Relation.ReflTransGen (RelOn D B) a b → Relation.ReflTransGen (RelOn D (A ∪ B)) a b :=
    fun h => Relation.ReflTransGen.mono (fun _ _ hab => RelOn.mono Set.subset_union_right hab) _ _ h
  have step : Relation.ReflTransGen (RelOn D (A ∪ B)) x y :=
    Relation.ReflTransGen.single ⟨Or.inl hx, Or.inr hy, hxy⟩
  have step' : Relation.ReflTransGen (RelOn D (A ∪ B)) y x :=
    Relation.ReflTransGen.single ⟨Or.inr hy, Or.inl hx, hxy.symm'⟩
  refine ⟨⟨x, Or.inl hx⟩, ?_⟩
  rintro p (hp | hp) q (hq | hq)
  · exact mA (hA.2 p hp q hq)
  · exact ((mA (hA.2 p hp x hx)).trans step).trans (mB (hB.2 y hy q hq))
  · exact ((mB (hB.2 p hp y hy)).trans step').trans (mA (hA.2 x hx q hq))
  · exact mB (hB.2 p hp q hq)

lemma ConnOn.singleton (x : ℕ) : ConnOn D {x} := by
  refine ⟨⟨x, rfl⟩, ?_⟩
  rintro p rfl q rfl
  exact Relation.ReflTransGen.refl

lemma ConnOn.insert {A : Set ℕ} (hA : ConnOn D A) {x y : ℕ} (hy : y ∈ A) (hxy : Adj' D x y) :
    ConnOn D (insert x A) := by
  have := (ConnOn.singleton (D := D) x).union hA (Set.mem_singleton x) hy hxy
  rwa [Set.singleton_union] at this

/-! ## the cut argument -/

/-! ## the gluing argument -/

/-- The occurrences of `v` below the node `m`. -/
def Av (n : ℕ) (D : List ℕ) (v m : ℕ) : Set ℕ := {j | j ∈ desc D m ∧ v ∈ bagN n D j}

/-- Empty or connected. -/
def EoC (D : List ℕ) (A : Set ℕ) : Prop := A = ∅ ∨ ConnOn D A

lemma Lay.eoc_unary (_L : Lay n D) {i v : ℕ}
    (hd : desc D (i + 1) = insert (i + 1) (desc D i))
    (hc : IsChild D i (i + 1))
    (hkey : v ∈ bagN n D (i + 1) → v ∈ bagN n D i ∨ ∀ j ∈ desc D i, v ∉ bagN n D j)
    (ih : EoC D (Av n D v i)) : EoC D (Av n D v (i + 1)) := by
  by_cases hv : v ∈ bagN n D (i + 1)
  · rcases hkey hv with hvi | hvi
    · have hA : Av n D v (i + 1) = insert (i + 1) (Av n D v i) := by
        ext j
        simp only [Av, hd, Finset.mem_insert, Set.mem_ofPred_eq, Set.mem_insert_iff]
        constructor
        · rintro ⟨rfl | h, hj⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨h, hj⟩
        · rintro (rfl | ⟨h, hj⟩)
          · exact ⟨Or.inl rfl, hv⟩
          · exact ⟨Or.inr h, hj⟩
      have hne : i ∈ Av n D v i := ⟨self_mem_desc D i, hvi⟩
      rcases ih with h | h
      · rw [h] at hne; exact absurd hne (Set.notMem_empty _)
      · rw [hA]; exact Or.inr (h.insert hne (Or.inr hc))
    · have hA : Av n D v (i + 1) = {i + 1} := by
        ext j
        simp only [Av, hd, Finset.mem_insert, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨rfl | h, hj⟩
          · rfl
          · exact absurd hj (hvi j h)
        · rintro rfl; exact ⟨Or.inl rfl, hv⟩
      rw [hA]; exact Or.inr (ConnOn.singleton _)
  · have hA : Av n D v (i + 1) = Av n D v i := by
      ext j
      simp only [Av, hd, Finset.mem_insert, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨rfl | h, hj⟩
        · exact absurd hj hv
        · exact ⟨h, hj⟩
      · rintro ⟨h, hj⟩; exact ⟨Or.inr h, hj⟩
    rw [hA]; exact ih

lemma Lay.eoc_join (_L : Lay n D) {i o v : ℕ}
    (hd : desc D (i + 1) = insert (i + 1) (desc D i ∪ desc D o))
    (hci : IsChild D i (i + 1)) (hco : IsChild D o (i + 1))
    (hbo : bagN n D o = bagN n D i) (hb : bagN n D (i + 1) = bagN n D i)
    (hloc : ∀ x ∈ desc D i, ∀ y ∈ desc D o, ∀ u, u ∈ bagN n D x → u ∈ bagN n D y → u ∈ bagN n D (i + 1))
    (ih1 : EoC D (Av n D v i)) (ih2 : EoC D (Av n D v o)) : EoC D (Av n D v (i + 1)) := by
  by_cases hv : v ∈ bagN n D (i + 1)
  · have hvi : v ∈ bagN n D i := hb ▸ hv
    have hvo : v ∈ bagN n D o := hbo ▸ hvi
    have hA : Av n D v (i + 1) = insert (i + 1) (Av n D v i) ∪ Av n D v o := by
      ext j
      simp only [Av, hd, Finset.mem_insert, Finset.mem_union, Set.mem_ofPred_eq, Set.mem_union,
        Set.mem_insert_iff]
      constructor
      · rintro ⟨rfl | h | h, hj⟩
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr ⟨h, hj⟩)
        · exact Or.inr ⟨h, hj⟩
      · rintro ((rfl | ⟨h, hj⟩) | ⟨h, hj⟩)
        · exact ⟨Or.inl rfl, hv⟩
        · exact ⟨Or.inr (Or.inl h), hj⟩
        · exact ⟨Or.inr (Or.inr h), hj⟩
    have hAi : i ∈ Av n D v i := ⟨self_mem_desc D i, hvi⟩
    have hAo : o ∈ Av n D v o := ⟨self_mem_desc D o, hvo⟩
    have c1 : ConnOn D (Av n D v i) := ih1.resolve_left (fun h => by rw [h] at hAi; exact hAi)
    have c2 : ConnOn D (Av n D v o) := ih2.resolve_left (fun h => by rw [h] at hAo; exact hAo)
    have c3 := c1.insert hAi (Or.inr hci)
    rw [hA]
    exact Or.inr (c3.union c2 (Set.mem_insert _ _) hAo (Or.inr hco))
  · have hA : Av n D v (i + 1) = Av n D v i ∪ Av n D v o := by
      ext j
      simp only [Av, hd, Finset.mem_insert, Finset.mem_union, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨rfl | h | h, hj⟩
        · exact absurd hj hv
        · exact Or.inl ⟨h, hj⟩
        · exact Or.inr ⟨h, hj⟩
      · rintro (⟨h, hj⟩ | ⟨h, hj⟩)
        · exact ⟨Or.inr (Or.inl h), hj⟩
        · exact ⟨Or.inr (Or.inr h), hj⟩
    have hor : Av n D v i = ∅ ∨ Av n D v o = ∅ := by
      by_contra hcon
      push Not at hcon
      obtain ⟨⟨x, hx, hux⟩, ⟨y, hy, huy⟩⟩ := hcon
      exact hv (hloc x hx y hy v hux huy)
    rw [hA]
    rcases hor with h | h
    · rw [h, Set.empty_union]; exact ih2
    · rw [h, Set.union_empty]; exact ih1

/-- Local conditions give connected occurrence sets. -/
lemma Lay.eoc_of_loc (L : Lay n D) (hloc : ∀ j, j < nodeCount D → Loc n D j) (v : ℕ) :
    ∀ i, i < nodeCount D → EoC D (Av n D v i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    cases i with
    | zero =>
      by_cases hv : v ∈ bagN n D 0
      · right
        have : Av n D v 0 = {0} := by
          ext j; simp only [Av, desc_zero, Finset.mem_singleton, Set.mem_ofPred_eq, Set.mem_singleton_iff]
          constructor
          · exact fun h => h.1
          · rintro rfl; exact ⟨rfl, hv⟩
        rw [this]; exact ConnOn.singleton _
      · left
        ext j; simp only [Av, desc_zero, Finset.mem_singleton, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false, not_and]
        rintro rfl; exact hv
    | succ i =>
      have ih' := ih i (by omega) (by omega)
      have hl := hloc (i + 1) hi
      rcases L.node hi with ⟨h1, h2, h3⟩ | ⟨hkd, hv, hn⟩ | ⟨hkd, hv, hn⟩ | ⟨hkd, ho, hbe⟩
      · left
        ext j
        simp only [Av, desc_leaf h1 h2 h3, Finset.mem_singleton, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false, not_and]
        rintro rfl; rw [bagN_succ_leaf h1 h2 h3]; simp
      · refine L.eoc_unary (desc_intro hkd) ((L.isChild_succ_unary (Or.inl hkd) hi).2 rfl) ?_ ih'
        intro hvm
        rw [bagN_succ_intro hkd hv] at hvm
        rcases Finset.mem_insert.1 hvm with rfl | h
        · right
          have := hl.1 hkd
          simpa using this
        · exact Or.inl h
      · refine L.eoc_unary (desc_forget hkd) ((L.isChild_succ_unary (Or.inr hkd) hi).2 rfl) ?_ ih'
        intro hvm
        rw [bagN_succ_forget hkd hv] at hvm
        exact Or.inl (Finset.mem_of_mem_erase hvm)
      · refine L.eoc_join (desc_join hkd ho) ((L.isChild_succ_join hkd hi).2 (Or.inl rfl))
          ((L.isChild_succ_join hkd hi).2 (Or.inr rfl)) hbe (bagN_succ_join hkd) ?_ ih'
          (ih _ (by omega) (by omega))
        intro x hx y hy u hux huy
        exact (hl.2 hkd) x (by simpa using hx) y hy u hux huy

/-- Connected occurrence sets, given the local conditions and that the vertex occurs. -/
lemma Lay.connOn_of_loc (L : Lay n D) (hloc : ∀ j, j < nodeCount D → Loc n D j) {v : ℕ}
    (hocc : ∃ j, j < nodeCount D ∧ v ∈ bagN n D j) : ConnOn D (Sv n D v) := by
  have hS : Sv n D v = Av n D v (nodeCount D - 1) := by
    ext j
    simp only [Sv, Av, Set.mem_ofPred_eq, L.desc_full, Finset.mem_range]
  rw [hS]
  rcases L.eoc_of_loc hloc v (nodeCount D - 1) (by have := L.nonempty; omega) with h | h
  · obtain ⟨j, hj, hvj⟩ := hocc
    have : j ∈ Av n D v (nodeCount D - 1) := by
      rw [← hS]; exact ⟨hj, hvj⟩
    rw [h] at this; exact absurd this (Set.notMem_empty _)
  · exact h

end Word

end Lax117284Proofs.Treewidth.Trees
