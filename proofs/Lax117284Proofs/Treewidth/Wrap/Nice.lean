import Lax117284Proofs.Treewidth.Wrap.NiceMany
import Lax117284Proofs.Treewidth.Trees.Bridge1Rt

/-!
# Kloks' conversion: `niceOf_spec` (C8a)

`niceOf t` is a nice decomposition of the same graph and of the same width as the rooted decomposition `t`.

The invariants proved together by induction on `t` (`niceOf_facts`): `Wf`, root bag `= t.rootBag`, vertices `= t.verts`,
every bag of `niceOf t` is contained in a bag of `t`, every bag of `t` is a bag of `niceOf t`, and connectedness
(`NConn`) if `t.Conn`.  `niceOf_size_le_uncond` is the unconditional size bound; `niceOf_size_le` is in `Wrap/NiceSize`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Trees Lax117284Proofs.Treewidth.Trees.NT

theorem fold_spec : ∀ (ts : List NT) (t : NT), t.Wf → (∀ s ∈ ts, s.Wf ∧ s.bag = t.bag) →
    (ts.foldl NT.join t).Wf ∧ (ts.foldl NT.join t).bag = t.bag ∧
    (∀ u, u ∈ (ts.foldl NT.join t).vs ↔ u ∈ t.vs ∨ ∃ s ∈ ts, u ∈ s.vs) ∧
    (∀ Y, Y ∈ (ts.foldl NT.join t).bs ↔ Y ∈ t.bs ∨ ∃ s ∈ ts, Y ∈ s.bs) ∧
    (ts.foldl NT.join t).size = t.size + (ts.map NT.size).sum + ts.length := by
  intro ts
  induction ts with
  | nil =>
    intro t hw _
    exact ⟨hw, rfl, by simp, by simp, by simp⟩
  | cons s ts ih =>
    intro t hw hs
    obtain ⟨hsw, hsb⟩ := hs s (by simp)
    have hj : (NT.join t s).Wf := ⟨hsb.symm, hw, hsw⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (NT.join t s) hj (fun s' hs' => by
      obtain ⟨a, b⟩ := hs s' (List.mem_cons_of_mem _ hs')
      exact ⟨a, by rw [b]; rfl⟩)
    simp only [List.foldl_cons]
    refine ⟨h1, by rw [h2]; rfl, ?_, ?_, ?_⟩
    · intro u
      rw [h3, vs_join]
      simp only [Finset.mem_union, List.mem_cons, exists_eq_or_imp]
      have := bag_subset_vs t
      constructor
      · rintro ((h | h | h) | h)
        · exact Or.inl (this h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr h
    · intro Y
      rw [h4, bs_join]
      simp only [List.mem_cons, List.mem_append, exists_eq_or_imp]
      have := bag_mem_bs t
      constructor
      · rintro ((h | h | h) | h)
        · exact Or.inl (h ▸ this)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr h
    · rw [h5]; simp [NT.size]; omega

theorem fold_nconn (X : Finset ℕ) : ∀ (ts : List NT) (t : NT),
    (∀ s ∈ t :: ts, s.bag = X ∧ s.NConn) →
    (t :: ts).Pairwise (fun a b => ∀ u, u ∈ a.vs → u ∈ b.vs → u ∈ X) → (ts.foldl NT.join t).NConn := by
  intro ts
  induction ts with
  | nil => intro t h _; exact (h t (by simp)).2
  | cons s ts ih =>
    intro t h hp
    simp only [List.foldl_cons]
    rw [List.pairwise_cons, List.pairwise_cons] at hp
    obtain ⟨hts, hs, hp'⟩ := hp
    have ht := h t (by simp)
    have hs' := h s (by simp)
    apply ih
    · intro s' hs''
      rcases List.mem_cons.1 hs'' with rfl | hs''
      · refine ⟨ht.1, ?_⟩
        show (∀ u, u ∈ t.vs → u ∈ s.vs → u ∈ t.bag) ∧ t.NConn ∧ s.NConn
        exact ⟨fun u hu hu' => ht.1 ▸ hts s (by simp) u hu hu', ht.2, hs'.2⟩
      · exact h s' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs''))
    · rw [List.pairwise_cons]
      refine ⟨fun b hb u hu hub => ?_, hp'⟩
      rw [vs_join] at hu
      simp only [Finset.mem_union] at hu
      rcases hu with hu | hu | hu
      · rw [← ht.1]; exact hu
      · exact hts b (List.mem_cons_of_mem _ hb) u hu hub
      · exact hs b hb u hu hub

/-- `niceKids` is the map of the child converter. -/
theorem niceKids_eq (X : Finset ℕ) : ∀ ks : List RT, niceKids X ks = ks.map (fun k => conv X (niceOf k))
  | [] => by simp [niceKids]
  | k :: ks => by simp [niceKids, niceKids_eq X ks, conv]

theorem niceOf_node (X : Finset ℕ) (ks : List RT) :
    niceOf (.node X ks) =
      match ks.map (fun k => conv X (niceOf k)) with
      | [] => introMany (X.sort (· ≤ ·)) .leaf
      | t :: ts => ts.foldl NT.join t := by
  rw [niceOf, niceKids_eq]
  rfl

theorem niceOf_facts : ∀ t : RT, (niceOf t).Wf ∧ (niceOf t).bag = t.rootBag ∧ (niceOf t).vs = t.verts ∧
    (∀ Y ∈ (niceOf t).bs, ∃ Z ∈ t.bags, Y ⊆ Z) ∧ (∀ Z ∈ t.bags, Z ∈ (niceOf t).bs) ∧
    (t.Conn → (niceOf t).NConn) := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    rcases ks with _ | ⟨k, ks'⟩
    · -- a leaf of the rooted tree
      rw [niceOf_node]
      simp only [List.map_nil]
      obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := introMany_spec (X.sort (· ≤ ·)) .leaf (Finset.sort_nodup _ _)
        (fun x _ => by simp) trivial
      simp only [Finset.sort_toFinset] at i2 i3 i4
      refine ⟨i1, by simpa [RT.rootBag] using i2, by simpa [RT.verts, RT.vertsL] using i3, ?_, ?_, ?_⟩
      · intro Y hY
        rcases i4 Y hY with hY | hY
        · exact ⟨X, by simp [RT.bags, RT.bagsL], by simp at hY; simp [hY]⟩
        · exact ⟨X, by simp [RT.bags, RT.bagsL], by simpa using hY⟩
      · intro Z hZ
        have : Z = X := by simpa [RT.bags, RT.bagsL] using hZ
        subst this
        have := bag_mem_bs (introMany (Z.sort (· ≤ ·)) .leaf)
        rwa [i2, bag_leaf, Finset.empty_union] at this
      · intro _
        apply i6 (fun x _ => by simp) trivial
    · -- some kids
      have hk : ∀ k' ∈ k :: ks', (niceOf k').Wf := fun k' hk' => (ih k' hk').1
      let f : RT → NT := fun k => conv X (niceOf k)
      have hf : ∀ k' ∈ k :: ks', (f k').Wf ∧ (f k').bag = X ∧ (f k').vs = k'.verts ∪ X ∧
          (∀ Y ∈ (f k').bs, (∃ Z ∈ k'.bags, Y ⊆ Z) ∨ Y ⊆ X) ∧ (∀ Y ∈ k'.bags, Y ∈ (f k').bs) ∧
          (k'.Conn → (∀ v ∈ X, v ∈ k'.verts → v ∈ k'.rootBag) → (f k').NConn) ∧ True := by
        intro k' hk'
        obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih k' hk'
        obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := conv_spec X (niceOf k') a1
        refine ⟨c1, c2, by rw [c3, a3], ?_, ?_, ?_, trivial⟩
        · intro Y hY
          rcases c4 Y hY with ⟨Z, hZ, hYZ⟩ | hY
          · obtain ⟨Z', hZ', hZZ'⟩ := a4 Z hZ
            exact Or.inl ⟨Z', hZ', hYZ.trans hZZ'⟩
          · exact Or.inr hY
        · intro Y hY; exact c5 Y (a5 Y hY)
        · intro hc hX
          exact c6 (by rw [a3, a2]; exact hX) (a6 hc)
      have hfun : niceOf (.node X (k :: ks')) = (ks'.map f).foldl NT.join (f k) := by
        rw [niceOf_node]; simp [f]
      rw [hfun]
      obtain ⟨g1, g2, g3, g4, g5⟩ := fold_spec (ks'.map f) (f k) (hf k (by simp)).1 (by
        intro s hs
        obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hs
        exact ⟨(hf k' (List.mem_cons_of_mem _ hk')).1, by rw [(hf k' (List.mem_cons_of_mem _ hk')).2.1,
          (hf k (by simp)).2.1]⟩)
      have hroot : (f k).bag = X := (hf k (by simp)).2.1
      refine ⟨g1, by rw [g2, hroot]; rfl, ?_, ?_, ?_, ?_⟩
      · ext u
        rw [g3]
        simp only [RT.verts_node, List.mem_map, exists_exists_and_eq_and]
        rw [(hf k (by simp)).2.2.1]
        constructor
        · rintro (h | ⟨k', hk', h⟩)
          · rcases Finset.mem_union.1 h with h | h
            · exact Or.inr ⟨k, by simp, h⟩
            · exact Or.inl h
          · rw [(hf k' (List.mem_cons_of_mem _ hk')).2.2.1] at h
            rcases Finset.mem_union.1 h with h | h
            · exact Or.inr ⟨k', List.mem_cons_of_mem _ hk', h⟩
            · exact Or.inl h
        · rintro (h | ⟨k', hk', h⟩)
          · exact Or.inl (Finset.mem_union_right _ h)
          · rcases List.mem_cons.1 hk' with rfl | hk'
            · exact Or.inl (Finset.mem_union_left _ h)
            · exact Or.inr ⟨k', hk', by
                rw [(hf k' (List.mem_cons_of_mem _ hk')).2.2.1]; exact Finset.mem_union_left _ h⟩
      · intro Y hY
        rcases (g4 Y).1 hY with hY | ⟨s, hs, hY⟩
        · rcases (hf k (by simp)).2.2.2.1 Y hY with h | h
          · obtain ⟨Z, hZ, hYZ⟩ := h
            exact ⟨Z, by rw [RT.bags_node]; exact Or.inr ⟨k, by simp, hZ⟩, hYZ⟩
          · exact ⟨X, by simp [RT.bags], h⟩
        · obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hs
          rcases (hf k' (List.mem_cons_of_mem _ hk')).2.2.2.1 Y hY with ⟨Z, hZ, hYZ⟩ | h
          · exact ⟨Z, by rw [RT.bags_node]; exact Or.inr ⟨k', List.mem_cons_of_mem _ hk', hZ⟩, hYZ⟩
          · exact ⟨X, by simp [RT.bags], h⟩
      · intro Z hZ
        rw [RT.bags_node] at hZ
        rw [g4]
        rcases hZ with rfl | ⟨k', hk', hZ⟩
        · left
          rw [← hroot]
          exact bag_mem_bs _
        · rcases List.mem_cons.1 hk' with rfl | hk'
          · exact Or.inl ((hf k' (by simp)).2.2.2.2.1 Z hZ)
          · exact Or.inr ⟨f k', List.mem_map.2 ⟨k', hk', rfl⟩,
              (hf k' (List.mem_cons_of_mem _ hk')).2.2.2.2.1 Z hZ⟩
      · intro hc
        obtain ⟨hc1, hc2, hc3⟩ := (RT.conn_node_iff X _).1 hc
        apply fold_nconn X
        · intro s hs
          rcases List.mem_cons.1 hs with rfl | hs
          · exact ⟨hroot, (hf k (by simp)).2.2.2.2.2.1 (hc1 k (by simp)) (hc2 k (by simp))⟩
          · obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hs
            have hk'' := List.mem_cons_of_mem k hk'
            exact ⟨(hf k' hk'').2.1, (hf k' hk'').2.2.2.2.2.1 (hc1 k' hk'') (hc2 k' hk'')⟩
        · have hm : ((k :: ks').map f) = f k :: ks'.map f := rfl
          rw [← hm, List.pairwise_map]
          refine (List.Pairwise.and_mem.1 hc3).imp ?_
          rintro a b ⟨ha, hb, hab⟩ u hua hub
          rw [(hf a ha).2.2.1] at hua
          rw [(hf b hb).2.2.1] at hub
          rcases Finset.mem_union.1 hua with h | h
          · rcases Finset.mem_union.1 hub with h' | h'
            · exact hab u h h'
            · exact h'
          · exact h

/-- **Kloks' conversion** (`niceOf_spec`): a tree decomposition of `G[U]` of width `≤ w` becomes a nice one. -/
theorem niceOf_spec {G : SimpleGraph ℕ} {U : Finset ℕ} {t : RT} {w : ℕ} (h : t.IsTD G U) (hw : t.Width w) :
    (niceOf t).IsNiceTD G U w := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := niceOf_facts t
  refine ⟨f1, ⟨?_, ?_, ?_⟩, ?_⟩
  · show (niceOf t).vs = U
    rw [f3, h.verts_eq]
  · intro u v huv hu hv
    obtain ⟨X, hX, hxu, hxv⟩ := h.edges u v huv hu hv
    exact ⟨X, f5 X hX, hxu, hxv⟩
  · exact (conn_toRT_iff f1).2 (f6 h.conn)
  · intro Y hY
    obtain ⟨Z, hZ, hYZ⟩ := f4 Y hY
    exact (Finset.card_le_card hYZ).trans (hw Z hZ)

end Lax117284Proofs.Treewidth.Chars
