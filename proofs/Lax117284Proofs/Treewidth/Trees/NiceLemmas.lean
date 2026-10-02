import Lax117284Proofs.Treewidth.Trees.Basic

/-!
# Basic facts about nice trees (T2)

The recursive predicates `RT.Conn`, `RT.Width`, `RT.IsTD` unfolded on `NT.toRT`, so that everything can be proved by
induction on `NT` (a plain inductive type).
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace NT

@[simp] lemma bag_leaf : bag leaf = ∅ := rfl
@[simp] lemma bag_intro (v : ℕ) (c : NT) : bag (intro v c) = insert v (bag c) := rfl
@[simp] lemma bag_forget (v : ℕ) (c : NT) : bag (forget v c) = (bag c).erase v := rfl
@[simp] lemma bag_join (a b : NT) : bag (join a b) = bag a := rfl

/-- All vertices occurring in the tree. -/
abbrev vs (t : NT) : Finset ℕ := t.toRT.verts

/-- The bags of all nodes (root first). -/
abbrev bs (t : NT) : List (Finset ℕ) := t.toRT.bags

@[simp] lemma vs_leaf : vs leaf = ∅ := by simp [vs, toRT, RT.verts, RT.vertsL]
@[simp] lemma vs_intro (v : ℕ) (c : NT) : vs (intro v c) = bag (intro v c) ∪ vs c := by
  simp [vs, toRT, RT.verts, RT.vertsL]
@[simp] lemma vs_forget (v : ℕ) (c : NT) : vs (forget v c) = bag (forget v c) ∪ vs c := by
  simp [vs, toRT, RT.verts, RT.vertsL]
@[simp] lemma vs_join (a b : NT) : vs (join a b) = bag a ∪ (vs a ∪ vs b) := by
  simp [vs, toRT, RT.verts, RT.vertsL]

@[simp] lemma bs_leaf : bs leaf = [∅] := by simp [bs, toRT, RT.bags, RT.bagsL]
@[simp] lemma bs_intro (v : ℕ) (c : NT) : bs (intro v c) = bag (intro v c) :: bs c := by
  simp [bs, toRT, RT.bags, RT.bagsL]
@[simp] lemma bs_forget (v : ℕ) (c : NT) : bs (forget v c) = bag (forget v c) :: bs c := by
  simp [bs, toRT, RT.bags, RT.bagsL]
@[simp] lemma bs_join (a b : NT) : bs (join a b) = bag a :: (bs a ++ bs b) := by
  simp [bs, toRT, RT.bags, RT.bagsL]

/-- The root bag is the first bag. -/
lemma bag_mem_bs (t : NT) : t.bag ∈ bs t := by
  cases t <;> simp

/-- The root bag is among the vertices. -/
lemma bag_subset_vs (t : NT) : t.bag ⊆ vs t := by
  cases t <;> simp

/-- Membership in `vs` as membership in some bag. -/
lemma mem_vs_iff (t : NT) (u : ℕ) : u ∈ vs t ↔ ∃ X ∈ bs t, u ∈ X := by
  induction t with
  | leaf => simp
  | intro v c ih => simp [ih, or_assoc]
  | forget v c ih => simp [ih]
  | join a b ih₁ ih₂ =>
    simp only [vs_join, bs_join, Finset.mem_union, List.mem_cons, List.mem_append, ih₁, ih₂]
    constructor
    · rintro (h | ⟨X, hX, hu⟩ | ⟨X, hX, hu⟩)
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨X, Or.inr (Or.inl hX), hu⟩
      · exact ⟨X, Or.inr (Or.inr hX), hu⟩
    · rintro ⟨X, (rfl | hX | hX), hu⟩
      · exact Or.inl hu
      · exact Or.inr (Or.inl ⟨X, hX, hu⟩)
      · exact Or.inr (Or.inr ⟨X, hX, hu⟩)

lemma vs_subset_of_mem_bs {t : NT} {X : Finset ℕ} (h : X ∈ bs t) : X ⊆ vs t := by
  intro u hu; exact (mem_vs_iff t u).2 ⟨X, h, hu⟩

/-- `RT.Conn` of a nice tree, unfolded. -/
def NConn : NT → Prop
  | leaf => True
  | intro v c => v ∉ vs c ∧ NConn c
  | forget _ c => NConn c
  | join a b => (∀ u, u ∈ vs a → u ∈ vs b → u ∈ bag a) ∧ NConn a ∧ NConn b

@[simp] lemma rootBag_toRT (t : NT) : t.toRT.rootBag = t.bag := by
  cases t <;> rfl

lemma conn_toRT_iff {t : NT} (h : t.Wf) : t.toRT.Conn ↔ NConn t := by
  induction t with
  | leaf => simp [toRT, RT.Conn, RT.ConnL, NConn]
  | intro v c ih =>
    obtain ⟨hv, hc⟩ := h
    have := ih hc
    simp only [toRT, RT.Conn, RT.ConnL, NConn, this, List.mem_singleton, forall_eq, rootBag_toRT,
      List.pairwise_singleton, and_true]
    constructor
    · rintro ⟨hn, hall⟩
      refine ⟨fun hvc => hv (hall v (by simp) hvc), hn⟩
    · rintro ⟨hvc, hn⟩
      refine ⟨hn, fun u hu hu' => ?_⟩
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact absurd hu' hvc
      · exact hu
  | forget v c ih =>
    have := ih h.2
    simp only [toRT, RT.Conn, RT.ConnL, NConn, this, List.mem_singleton, forall_eq, rootBag_toRT,
      List.pairwise_singleton, and_true]
    constructor
    · exact fun h => h.1
    · exact fun hn => ⟨hn, fun u hu _ => Finset.mem_of_mem_erase hu⟩
  | join a b ih₁ ih₂ =>
    obtain ⟨hab, ha, hb⟩ := h
    have h1 := ih₁ ha
    have h2 := ih₂ hb
    simp [toRT, RT.Conn, RT.ConnL, NConn, h1, h2, hab]
    constructor
    · rintro ⟨⟨h1, h2⟩, -, hj⟩
      exact ⟨hj, h1, h2⟩
    · rintro ⟨hj, h1, h2⟩
      exact ⟨⟨h1, h2⟩, ⟨fun _ hv _ => hv, fun _ hv _ => hv⟩, hj⟩

end NT

end Lax117284Proofs.Treewidth.Trees
