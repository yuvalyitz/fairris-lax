import Lax117284Proofs.Treewidth.Trees.Basic
import Lax117284Proofs.Treewidth.Trees.Bridge1Rt

/-!
# Adding a vertex to every bag

`RT.addAll v t` inserts `v` into every bag of `t`.  If `t` decomposes `G[U]` with width `≤ k`, then
`addAll v t` decomposes `G[U ∪ {v}]` with width `≤ k + 1` (for arbitrary neighbours of `v`): the RT-level
statement of the wrapper's step (PLAN §e).
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace RT

mutual
/-- Insert `v` into every bag. -/
def addAll (v : ℕ) : RT → RT
  | .node b ks => .node (insert v b) (addAllL v ks)
def addAllL (v : ℕ) : List RT → List RT
  | [] => []
  | k :: ks => addAll v k :: addAllL v ks
end

theorem addAllL_eq (v : ℕ) : ∀ ks : List RT, addAllL v ks = ks.map (addAll v)
  | [] => rfl
  | k :: ks => by simp [addAllL, addAllL_eq v ks]

theorem addAll_node (v : ℕ) (b : Finset ℕ) (ks : List RT) :
    addAll v (.node b ks) = .node (insert v b) (ks.map (addAll v)) := by
  simp [addAll, addAllL_eq]

theorem rootBag_addAll (v : ℕ) (t : RT) : (addAll v t).rootBag = insert v t.rootBag := by
  cases t; simp [addAll, rootBag]

theorem mem_bags_addAll (v : ℕ) : ∀ (t : RT) (X : Finset ℕ),
    X ∈ (addAll v t).bags ↔ ∃ Y ∈ t.bags, X = insert v Y := by
  intro t
  induction t using RT.ind with
  | _ b ks ih =>
    intro X
    rw [addAll_node, bags_node]
    constructor
    · rintro (rfl | ⟨k, hk, hX⟩)
      · exact ⟨b, (bags_node b ks).2 (Or.inl rfl), rfl⟩
      · obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hk
        obtain ⟨Y, hY, e⟩ := (ih k' hk' X).1 hX
        exact ⟨Y, (bags_node b ks).2 (Or.inr ⟨k', hk', hY⟩), e⟩
    · rintro ⟨Y, hY, rfl⟩
      rcases (bags_node b ks).1 hY with rfl | ⟨k, hk, hY⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨addAll v k, List.mem_map.2 ⟨k, hk, rfl⟩, (ih k hk _).2 ⟨Y, hY, rfl⟩⟩

theorem mem_verts_addAll (v : ℕ) (t : RT) (x : ℕ) :
    x ∈ (addAll v t).verts ↔ x = v ∨ x ∈ t.verts := by
  rw [mem_verts_iff, mem_verts_iff]
  constructor
  · rintro ⟨X, hX, hx⟩
    obtain ⟨Y, hY, rfl⟩ := (mem_bags_addAll v t X).1 hX
    rcases Finset.mem_insert.1 hx with h | h
    · exact Or.inl h
    · exact Or.inr ⟨Y, hY, h⟩
  · rintro (rfl | ⟨Y, hY, hx⟩)
    · exact ⟨insert x t.rootBag, (mem_bags_addAll x t _).2 ⟨t.rootBag, root_mem_bags t, rfl⟩,
        Finset.mem_insert_self _ _⟩
    · exact ⟨insert v Y, (mem_bags_addAll v t _).2 ⟨Y, hY, rfl⟩, Finset.mem_insert_of_mem hx⟩

theorem Conn.addAll (v : ℕ) : ∀ t : RT, t.Conn → (addAll v t).Conn := by
  intro t
  induction t using RT.ind with
  | _ b ks ih =>
    intro hc
    obtain ⟨hks, h2, h3⟩ := (conn_node_iff b ks).1 hc
    rw [addAll_node, conn_node_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro k' hk'
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
      exact ih k hk (hks k hk)
    · intro k' hk' x hx hxv
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
      rw [mem_verts_addAll] at hxv
      rw [rootBag_addAll]
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Finset.mem_insert_self _ _
      · rcases hxv with rfl | hxv
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (h2 k hk x hx hxv)
    · rw [List.pairwise_map]
      refine h3.imp ?_
      intro k1 k2 h x hx1 hx2
      rw [mem_verts_addAll] at hx1 hx2
      rcases hx1 with rfl | hx1
      · exact Finset.mem_insert_self _ _
      · rcases hx2 with rfl | hx2
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (h x hx1 hx2)

theorem Width.addAll {t : RT} {w : ℕ} (v : ℕ) (h : t.Width w) : (addAll v t).Width (w + 1) := by
  intro X hX
  obtain ⟨Y, hY, rfl⟩ := (mem_bags_addAll v t X).1 hX
  exact le_trans (Finset.card_insert_le _ _) (by have := h Y hY; omega)

theorem IsTD.addAll {G : SimpleGraph ℕ} {U : Finset ℕ} {t : RT} (h : t.IsTD G U) (v : ℕ) :
    (addAll v t).IsTD G (insert v U) := by
  refine ⟨?_, ?_, Conn.addAll v t h.conn⟩
  · ext x
    rw [mem_verts_addAll, h.verts_eq, Finset.mem_insert]
  · intro a b hab ha hb
    rcases Finset.mem_insert.1 ha with rfl | ha'
    · rcases Finset.mem_insert.1 hb with rfl | hb'
      · exact absurd rfl hab.ne
      · obtain ⟨X, hX, hbX⟩ := (mem_verts_iff _ _).1 (h.verts_eq ▸ hb' : b ∈ t.verts)
        exact ⟨insert a X, (mem_bags_addAll a t _).2 ⟨X, hX, rfl⟩, Finset.mem_insert_self _ _,
          Finset.mem_insert_of_mem hbX⟩
    · rcases Finset.mem_insert.1 hb with rfl | hb'
      · obtain ⟨X, hX, haX⟩ := (mem_verts_iff _ _).1 (h.verts_eq ▸ ha' : a ∈ t.verts)
        exact ⟨insert b X, (mem_bags_addAll b t _).2 ⟨X, hX, rfl⟩, Finset.mem_insert_of_mem haX,
          Finset.mem_insert_self _ _⟩
      · obtain ⟨X, hX, haX, hbX⟩ := h.edges a b hab ha' hb'
        exact ⟨insert v X, (mem_bags_addAll v t _).2 ⟨X, hX, rfl⟩, Finset.mem_insert_of_mem haX,
          Finset.mem_insert_of_mem hbX⟩

end RT

end Lax117284Proofs.Treewidth.Trees
