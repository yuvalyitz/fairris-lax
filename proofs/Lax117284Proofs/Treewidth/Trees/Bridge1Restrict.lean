import Lax117284Proofs.Treewidth.Trees.Basic
import Lax117284Proofs.Treewidth.Trees.Bridge1Rt

/-!
# Restricting an `RT` to a vertex set

`RT.restrict U t` intersects every bag with `U`; this keeps `Conn`, edges among `U`, and does not increase width.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace RT

mutual
/-- Intersect every bag with `U`. -/
def restrict (U : Finset ℕ) : RT → RT
  | .node b ks => .node (b ∩ U) (restrictL U ks)
def restrictL (U : Finset ℕ) : List RT → List RT
  | [] => []
  | k :: ks => restrict U k :: restrictL U ks
end

theorem restrictL_eq (U : Finset ℕ) : ∀ ks : List RT, restrictL U ks = ks.map (restrict U)
  | [] => rfl
  | k :: ks => by simp [restrictL, restrictL_eq U ks]

theorem restrict_node (U : Finset ℕ) (b : Finset ℕ) (ks : List RT) :
    restrict U (.node b ks) = .node (b ∩ U) (ks.map (restrict U)) := by
  simp [restrict, restrictL_eq]

theorem rootBag_restrict (U : Finset ℕ) (t : RT) : (restrict U t).rootBag = t.rootBag ∩ U := by
  cases t; simp [restrict, rootBag]

theorem mem_bags_restrict (U : Finset ℕ) : ∀ (t : RT) (X : Finset ℕ),
    X ∈ (restrict U t).bags ↔ ∃ Y ∈ t.bags, X = Y ∩ U := by
  intro t
  induction t using RT.ind with
  | _ b ks ih =>
    intro X
    rw [restrict_node, bags_node]
    constructor
    · rintro (rfl | ⟨k, hk, hX⟩)
      · exact ⟨b, (bags_node b ks).2 (Or.inl rfl), rfl⟩
      · obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hk
        obtain ⟨Y, hY, e⟩ := (ih k' hk' X).1 hX
        exact ⟨Y, (bags_node b ks).2 (Or.inr ⟨k', hk', hY⟩), e⟩
    · rintro ⟨Y, hY, rfl⟩
      rcases (bags_node b ks).1 hY with rfl | ⟨k, hk, hY⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨restrict U k, List.mem_map.2 ⟨k, hk, rfl⟩, (ih k hk _).2 ⟨Y, hY, rfl⟩⟩

theorem mem_verts_restrict (U : Finset ℕ) (t : RT) (x : ℕ) :
    x ∈ (restrict U t).verts ↔ x ∈ t.verts ∧ x ∈ U := by
  rw [mem_verts_iff, mem_verts_iff]
  constructor
  · rintro ⟨X, hX, hx⟩
    obtain ⟨Y, hY, rfl⟩ := (mem_bags_restrict U t X).1 hX
    exact ⟨⟨Y, hY, (Finset.mem_inter.1 hx).1⟩, (Finset.mem_inter.1 hx).2⟩
  · rintro ⟨⟨Y, hY, hx⟩, hxU⟩
    exact ⟨Y ∩ U, (mem_bags_restrict U t _).2 ⟨Y, hY, rfl⟩, Finset.mem_inter.2 ⟨hx, hxU⟩⟩

theorem Conn.restrict (U : Finset ℕ) : ∀ t : RT, t.Conn → (restrict U t).Conn := by
  intro t
  induction t using RT.ind with
  | _ b ks ih =>
    intro hc
    obtain ⟨hks, h2, h3⟩ := (conn_node_iff b ks).1 hc
    rw [restrict_node, conn_node_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro k' hk'
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
      exact ih k hk (hks k hk)
    · intro k' hk' x hx hxv
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
      rw [mem_verts_restrict] at hxv
      rw [rootBag_restrict]
      exact Finset.mem_inter.2 ⟨h2 k hk x (Finset.mem_inter.1 hx).1 hxv.1, hxv.2⟩
    · rw [List.pairwise_map]
      refine h3.imp ?_
      intro k1 k2 h x hx1 hx2
      rw [mem_verts_restrict] at hx1 hx2
      exact Finset.mem_inter.2 ⟨h x hx1.1 hx2.1, hx1.2⟩

theorem Width.restrict {t : RT} {w : ℕ} (U : Finset ℕ) (h : t.Width w) : (restrict U t).Width w := by
  intro X hX
  obtain ⟨Y, hY, rfl⟩ := (mem_bags_restrict U t X).1 hX
  exact le_trans (Finset.card_le_card Finset.inter_subset_left) (h Y hY)

theorem IsTD.mono {G G' : SimpleGraph ℕ} {U : Finset ℕ} {t : RT} (h : t.IsTD G U) (hle : G' ≤ G) :
    t.IsTD G' U :=
  ⟨h.verts_eq, fun u v huv hu hv => h.edges u v (hle huv) hu hv, h.conn⟩

theorem IsTD.restrict {G : SimpleGraph ℕ} {U₀ : Finset ℕ} {t : RT} (h : t.IsTD G U₀) (U : Finset ℕ) :
    (restrict U t).IsTD G (U₀ ∩ U) := by
  refine ⟨?_, ?_, Conn.restrict U t h.conn⟩
  · ext x
    rw [mem_verts_restrict, h.verts_eq, Finset.mem_inter]
  · intro u v huv hu hv
    obtain ⟨X, hX, hu', hv'⟩ := h.edges u v huv (Finset.mem_inter.1 hu).1 (Finset.mem_inter.1 hv).1
    exact ⟨X ∩ U, (mem_bags_restrict U t _).2 ⟨X, hX, rfl⟩,
      Finset.mem_inter.2 ⟨hu', (Finset.mem_inter.1 hu).2⟩,
      Finset.mem_inter.2 ⟨hv', (Finset.mem_inter.1 hv).2⟩⟩

end RT

end Lax117284Proofs.Treewidth.Trees
