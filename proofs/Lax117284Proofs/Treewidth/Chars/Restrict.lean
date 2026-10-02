import Lax117284Proofs.Treewidth.Chars.Alg
import Lax117284Proofs.Treewidth.Trees.NiceLemmas

/-!
# Graph-level basics of the exact layer (C2/C3 part 1)

* `good_of_isNiceTD`: a nice tree decomposition of `G[U]` satisfies the side conditions `NT.Good`;
* `PTD.restrict_intro`, `PTD.restrict_join_left`, `PTD.restrict_join_right`: restricting a partial decomposition
  of a node to the vertices below a child gives a partial decomposition of the child.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

/-! ## `NT.under` versus the vertices of the tree -/

theorem NT.under_subset_vs : ∀ t : NT, t.under ⊆ t.vs := by
  intro t
  induction t with
  | leaf => simp [NT.under]
  | intro v c ih =>
    intro x hx
    simp only [NT.under, Finset.mem_insert] at hx
    rw [NT.vs_intro]
    rcases hx with rfl | hx
    · exact Finset.mem_union_left _ (by simp)
    · exact Finset.mem_union_right _ (ih hx)
  | forget v c ih =>
    intro x hx
    rw [NT.vs_forget]
    exact Finset.mem_union_right _ (ih hx)
  | join a b iha ihb =>
    intro x hx
    simp only [NT.under, Finset.mem_union] at hx
    rw [NT.vs_join]
    rcases hx with hx | hx
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (iha hx))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (ihb hx))

/-! ## a child of a tree decomposition is a tree decomposition -/

theorem RT.IsTD.kid {G : SimpleGraph ℕ} {U : Finset ℕ} {b : Finset ℕ} {ks : List RT}
    (h : (RT.node b ks).IsTD G U) {k : RT} (hk : k ∈ ks) : k.IsTD G k.verts := by
  obtain ⟨hks, h2, h3⟩ := (RT.conn_node_iff b ks).1 h.conn
  refine ⟨rfl, ?_, hks k hk⟩
  intro u v huv hu hv
  have hUu : u ∈ U := by
    rw [← h.verts_eq, RT.verts_node]; exact Or.inr ⟨k, hk, hu⟩
  have hUv : v ∈ U := by
    rw [← h.verts_eq, RT.verts_node]; exact Or.inr ⟨k, hk, hv⟩
  obtain ⟨X, hX, hxu, hxv⟩ := h.edges u v huv hUu hUv
  rcases (RT.bags_node b ks).1 hX with rfl | ⟨k', hk', hX'⟩
  · exact ⟨k.rootBag, RT.root_mem_bags k, h2 k hk u hxu hu, h2 k hk v hxv hv⟩
  · by_cases hkk : k' = k
    · subst hkk; exact ⟨X, hX', hxu, hxv⟩
    · have hu' : u ∈ k'.verts := (RT.mem_verts_iff k' u).2 ⟨X, hX', hxu⟩
      have hv' : v ∈ k'.verts := (RT.mem_verts_iff k' v).2 ⟨X, hX', hxv⟩
      have hpw := List.pairwise_iff_get.1 h3
      obtain ⟨i, rfl⟩ := List.get_of_mem hk
      obtain ⟨j, rfl⟩ := List.get_of_mem hk'
      have hne : i ≠ j := fun e => hkk (by rw [e])
      have key : ∀ x, x ∈ (ks.get j).verts → x ∈ (ks.get i).verts → x ∈ b := by
        intro x hxj hxi
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact hpw i j hlt x hxi hxj
        · exact hpw j i hlt x hxj hxi
      exact ⟨(ks.get i).rootBag, RT.root_mem_bags _, h2 _ (List.get_mem _ _) u (key u hu' hu) hu,
        h2 _ (List.get_mem _ _) v (key v hv' hv) hv⟩

/-! ## `good_of_isNiceTD` -/

theorem good_of_isTD {adj : Adj} : ∀ {t : NT} {U : Finset ℕ}, t.Wf → t.toRT.IsTD adj.graph U → t.Good adj := by
  intro t
  induction t with
  | leaf => intro U _ _; trivial
  | intro v c ih =>
    intro U hw h
    obtain ⟨hv, hwc⟩ := hw
    have hkid : c.toRT.IsTD adj.graph c.toRT.verts := by
      have h' : (RT.node (NT.bag (NT.intro v c)) [c.toRT]).IsTD adj.graph U := h
      exact RT.IsTD.kid h' (List.mem_singleton_self _)
    have hgood := ih hwc hkid
    have hconn := (NT.conn_toRT_iff (t := NT.intro v c) ⟨hv, hwc⟩).1 h.conn
    have hvs : v ∉ c.vs := hconn.1
    refine ⟨hv, ?_, fun hu => hvs (NT.under_subset_vs c hu), hgood⟩
    intro u hu hadj
    have huvs : u ∈ c.vs := NT.under_subset_vs c hu
    have hne : v ≠ u := fun e => hvs (e ▸ huvs)
    have hadjG : adj.graph.Adj v u := by
      simp only [Adj.graph, SimpleGraph.fromRel_adj]; exact ⟨hne, Or.inl hadj⟩
    have hvU : v ∈ U := by
      rw [← h.verts_eq]; simp [NT.toRT, RT.verts_node]
    have huU : u ∈ U := by
      rw [← h.verts_eq]
      simp only [NT.toRT, RT.verts_node]; exact Or.inr ⟨c.toRT, List.mem_singleton_self _, huvs⟩
    obtain ⟨X, hX, hxv, hxu⟩ := h.edges v u hadjG hvU huU
    have hX' : X ∈ (RT.node (NT.bag (NT.intro v c)) [c.toRT]).bags := hX
    rcases (RT.bags_node _ _).1 hX' with rfl | ⟨k, hk, hXk⟩
    · rcases Finset.mem_insert.1 hxu with rfl | hu'
      · exact absurd rfl hne
      · exact hu'
    · rw [List.mem_singleton] at hk; subst hk
      exact absurd ((NT.mem_vs_iff c v).2 ⟨X, hXk, hxv⟩) hvs
  | forget v c ih =>
    intro U hw h
    obtain ⟨hv, hwc⟩ := hw
    have hkid : c.toRT.IsTD adj.graph c.toRT.verts := by
      have h' : (RT.node (NT.bag (NT.forget v c)) [c.toRT]).IsTD adj.graph U := h
      exact RT.IsTD.kid h' (List.mem_singleton_self _)
    exact ⟨hv, ih hwc hkid⟩
  | join a b iha ihb =>
    intro U hw h
    obtain ⟨hab, hwa, hwb⟩ := hw
    have h' : (RT.node (NT.bag a) [a.toRT, b.toRT]).IsTD adj.graph U := h
    have hka : a.toRT.IsTD adj.graph a.toRT.verts := RT.IsTD.kid h' (by simp)
    have hkb : b.toRT.IsTD adj.graph b.toRT.verts := RT.IsTD.kid h' (by simp)
    have hconn := (NT.conn_toRT_iff (t := NT.join a b) ⟨hab, hwa, hwb⟩).1 h.conn
    refine ⟨hab, ?_, iha hwa hka, ihb hwb hkb, ?_⟩
    · intro u hu
      exact hconn.1 u (NT.under_subset_vs a (Finset.mem_inter.1 hu).1) (NT.under_subset_vs b (Finset.mem_inter.1 hu).2)
    · -- no edge between the two sides outside the bag
      intro u hu v hv hadj
      by_cases huv : u = v
      · subst huv
        exact Or.inl (hconn.1 u (NT.under_subset_vs a hu) (NT.under_subset_vs b hv))
      · have hadjG : adj.graph.Adj u v := by
          simp only [Adj.graph, SimpleGraph.fromRel_adj]; exact ⟨huv, hadj⟩
        have hua : u ∈ a.vs := NT.under_subset_vs a hu
        have hvb : v ∈ b.vs := NT.under_subset_vs b hv
        have huU : u ∈ U := by
          rw [← h.verts_eq]
          simp only [NT.toRT, RT.verts_node]; exact Or.inr ⟨a.toRT, by simp, hua⟩
        have hvU : v ∈ U := by
          rw [← h.verts_eq]
          simp only [NT.toRT, RT.verts_node]; exact Or.inr ⟨b.toRT, by simp, hvb⟩
        obtain ⟨X, hX, hxu, hxv⟩ := h.edges u v hadjG huU hvU
        have hX' : X ∈ (RT.node (NT.bag a) [a.toRT, b.toRT]).bags := hX
        rcases (RT.bags_node _ _).1 hX' with rfl | ⟨k, hk, hXk⟩
        · exact Or.inl hxu
        · rcases List.mem_cons.1 hk with rfl | hk
          · exact Or.inr (hconn.1 v ((NT.mem_vs_iff _ v).2 ⟨X, hXk, hxv⟩) hvb)
          · rw [List.mem_singleton] at hk; subst hk
            exact Or.inl (hconn.1 u hua ((NT.mem_vs_iff _ u).2 ⟨X, hXk, hxu⟩))

theorem good_of_isNiceTD {adj : Adj} {U : Finset ℕ} {t : NT} {w : ℕ}
    (h : t.IsNiceTD adj.graph U w) : t.Good adj :=
  good_of_isTD h.1 h.2.1

/-! ## restrictions of partial decompositions -/

theorem PTD.restrict_intro {adj : Adj} {v : ℕ} {c : NT} {k : ℕ} {t : RT} (_hg : (NT.intro v c).Good adj)
    (h : PTD adj (.intro v c) k t) : PTD adj c k (t.restrict c.under) := by
  refine ⟨?_, h.2.restrict _⟩
  have := RT.IsTD.restrict h.1 c.under
  have e : NT.under (NT.intro v c) ∩ c.under = c.under := by
    simp [NT.under]
  rwa [e] at this

theorem PTD.restrict_join_left {adj : Adj} {a b : NT} {k : ℕ} {t : RT} (_hg : (NT.join a b).Good adj)
    (h : PTD adj (.join a b) k t) : PTD adj a k (t.restrict a.under) := by
  refine ⟨?_, h.2.restrict _⟩
  have := RT.IsTD.restrict h.1 a.under
  have e : NT.under (NT.join a b) ∩ a.under = a.under := by
    simp [NT.under]
  rwa [e] at this

theorem PTD.restrict_join_right {adj : Adj} {a b : NT} {k : ℕ} {t : RT} (_hg : (NT.join a b).Good adj)
    (h : PTD adj (.join a b) k t) : PTD adj b k (t.restrict b.under) := by
  refine ⟨?_, h.2.restrict _⟩
  have := RT.IsTD.restrict h.1 b.under
  have e : NT.under (NT.join a b) ∩ b.under = b.under := by
    simp [NT.under]
  rwa [e] at this

end Lax117284Proofs.Treewidth.Chars
