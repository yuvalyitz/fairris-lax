import Lax117284Proofs.Treewidth.Wrap.CompressTD
import Lax117284Proofs.Treewidth.Wrap.NiceSizeConn

/-!
# `compress`: the decomposition facts and the size bound (WP P0)

* `compress_isTD`, `compress_width` ;
* `size_le_of_comp` : a connected, compressed tree has at most `1 + |V \ root bag|` nodes (every non-root node owns
  the vertices of its bag that are not in its parent's bag; connectedness makes these sets disjoint);
* `compress_size_le` : `(compress t).size ≤ |V(t)| + 1` for a connected `t`.
-/

namespace Lax117284Proofs.Treewidth.Trees

open Lax117284Proofs.Treewidth.Chars

theorem compress_isTD {G : SimpleGraph ℕ} {U : Finset ℕ} {t : RT} (h : t.IsTD G U) : (compress t).IsTD G U := by
  refine ⟨by rw [RT.verts_compress]; exact h.verts_eq, ?_, (RT.compress_conn_comp t h.conn).1⟩
  intro u v huv hu hv
  obtain ⟨X, hX, hxu, hxv⟩ := h.edges u v huv hu hv
  obtain ⟨X', hX', hXX'⟩ := RT.bags_compress_cover t X hX
  exact ⟨X', hX', hXX' hxu, hXX' hxv⟩

theorem compress_width {t : RT} {w : ℕ} (h : t.Width w) : (compress t).Width w :=
  fun X hX => h X (RT.bags_compress_sub t X hX)

namespace RT

theorem size_le_of_comp : ∀ t : RT, Conn t → Comp t → t.size ≤ 1 + (t.verts \ t.rootBag).card := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro hc hcomp
    obtain ⟨h1, h2, h3⟩ := (conn_node_iff X ks).1 hc
    have hk := (comp_node_iff X ks).1 hcomp
    have hkid : ∀ k ∈ ks, k.size ≤ (k.verts \ X).card := by
      intro k hk'
      obtain ⟨hnot, hcompk⟩ := hk k hk'
      have i1 := ih k hk' (h1 k hk') hcompk
      have i2 := conn_kid_card (rootBag_sub_verts k) (h2 k hk')
      have i3 : 0 < (k.rootBag \ X).card := by
        apply Finset.card_pos.2
        by_contra hne
        exact hnot (Finset.sdiff_eq_empty_iff_subset.1 (Finset.not_nonempty_iff_eq_empty.1 hne))
      omega
    have hsum : (ks.map (fun k => (k.verts \ X).card)).sum ≤ ((RT.node X ks).verts \ X).card := by
      apply sum_card_le ks h3
      intro k hk' v hv
      have := Finset.mem_sdiff.1 hv
      exact Finset.mem_sdiff.2 ⟨sub_verts hk' this.1, this.2⟩
    have hle : (ks.map size).sum ≤ (ks.map (fun k => (k.verts \ X).card)).sum :=
      List.sum_le_sum (fun k hk' => by simpa using hkid k (by simpa using hk'))
    rw [size_node]
    simp only [rootBag]
    omega

end RT

theorem compress_size_le {t : RT} (h : t.Conn) : (compress t).size ≤ t.verts.card + 1 := by
  obtain ⟨hc, hcomp⟩ := RT.compress_conn_comp t h
  have := RT.size_le_of_comp _ hc hcomp
  rw [RT.verts_compress] at this
  have h2 := Finset.card_le_card (Finset.sdiff_subset (s := t.verts) (t := (compress t).rootBag))
  omega

end Lax117284Proofs.Treewidth.Trees
