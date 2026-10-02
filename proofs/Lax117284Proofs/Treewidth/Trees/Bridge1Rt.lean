import Lax117284Proofs.Treewidth.Trees.Basic

/-!
# Basic facts about `RT`

Induction principle, membership characterisations of `verts`/`bags`, and unfolding of `Conn`.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace RT

mutual
theorem ind_rec {P : RT → Prop} (h : ∀ b ks, (∀ k ∈ ks, P k) → P (.node b ks)) : ∀ t, P t
  | .node b ks => h b ks (indL_rec h ks)
theorem indL_rec {P : RT → Prop} (h : ∀ b ks, (∀ k ∈ ks, P k) → P (.node b ks)) :
    ∀ ks : List RT, ∀ k ∈ ks, P k
  | [] => by simp
  | k' :: ks => by
    intro k hk
    rcases List.mem_cons.1 hk with e | hk
    · exact e ▸ ind_rec h k'
    · exact indL_rec h ks k hk
end

theorem ind_pair : (type_of% @ind_rec) ∧ (type_of% @indL_rec) :=
  ⟨@ind_rec, @indL_rec⟩

/-- Induction principle for `RT` (nested through `List`). -/
theorem ind : type_of% @ind_rec := ind_pair.1

mutual
theorem mem_verts_iff : ∀ (t : RT) (x : ℕ), x ∈ t.verts ↔ ∃ X ∈ t.bags, x ∈ X
  | .node b ks, x => by
    simp only [verts, bags, Finset.mem_union, List.mem_cons, exists_eq_or_imp]
    rw [mem_vertsL_iff ks x]
    simp only [mem_bagsL_iff ks]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact Or.inl h
      · obtain ⟨X, hX, hx⟩ := (mem_verts_iff k x).1 h
        exact Or.inr ⟨X, ⟨k, hk, hX⟩, hx⟩
    · rintro (h | ⟨X, ⟨k, hk, hX⟩, hx⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, hk, (mem_verts_iff k x).2 ⟨X, hX, hx⟩⟩
theorem mem_vertsL_iff : ∀ (ks : List RT) (x : ℕ), x ∈ vertsL ks ↔ ∃ k ∈ ks, x ∈ k.verts
  | [], x => by simp [vertsL]
  | k :: ks, x => by
    simp only [vertsL, Finset.mem_union, List.mem_cons, exists_eq_or_imp]
    rw [mem_vertsL_iff ks x]
theorem mem_bagsL_iff : ∀ (ks : List RT) (X : Finset ℕ), X ∈ bagsL ks ↔ ∃ k ∈ ks, X ∈ k.bags
  | [], X => by simp [bagsL]
  | k :: ks, X => by
    simp only [bagsL, List.mem_append, List.mem_cons, exists_eq_or_imp]
    rw [mem_bagsL_iff ks X]
end

mutual
theorem connL_iff : ∀ ks : List RT, ConnL ks ↔ ∀ k ∈ ks, Conn k
  | [] => by simp [ConnL]
  | k :: ks => by
    simp only [ConnL, List.mem_cons, forall_eq_or_imp]
    rw [connL_iff ks]
end

theorem conn_node_iff (b : Finset ℕ) (ks : List RT) :
    Conn (.node b ks) ↔ (∀ k ∈ ks, Conn k) ∧ (∀ k ∈ ks, ∀ v ∈ b, v ∈ verts k → v ∈ rootBag k) ∧
      ks.Pairwise (fun k₁ k₂ => ∀ v, v ∈ verts k₁ → v ∈ verts k₂ → v ∈ b) := by
  rw [Conn, connL_iff]

theorem verts_node {x : ℕ} (b : Finset ℕ) (ks : List RT) :
    x ∈ verts (.node b ks) ↔ x ∈ b ∨ ∃ k ∈ ks, x ∈ verts k := by
  simp only [verts, Finset.mem_union, mem_vertsL_iff]

theorem bags_node {X : Finset ℕ} (b : Finset ℕ) (ks : List RT) :
    X ∈ bags (.node b ks) ↔ X = b ∨ ∃ k ∈ ks, X ∈ bags k := by
  simp only [bags, List.mem_cons, mem_bagsL_iff]

theorem root_mem_bags (t : RT) : t.rootBag ∈ t.bags := by
  cases t; simp [rootBag, bags]

end RT

end Lax117284Proofs.Treewidth.Trees
