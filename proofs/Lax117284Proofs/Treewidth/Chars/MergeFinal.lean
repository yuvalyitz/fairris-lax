import Lax117284Proofs.Treewidth.Chars.MergeSpec

/-!
# `mergeReal_spec`, `realJoin_spec`, `realize_join` (C3)

The realisation of a join option: two partial decompositions `ta`, `tb` of the two sides of a join node, and an option
`c` of the join of their characteristics, are merged by `mergeReal` into a partial decomposition of the join node
whose characteristic is dominated by `c`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem allne_analyze (B : Finset ℕ) (t : RT) : AR.All (fun _ c => c ≠ []) (analyze B t) :=
  AR.All.mono (fun _ c h => h.1) _ (analyze_all B t)

/-- `mergeReal`: for a join option `c` of the *actual* characteristics. -/
theorem mergeReal_spec {adj : Adj} {a b : NT} {k : ℕ} {ta tb : RT} (hg : (NT.join a b).Good adj)
    (ha : PTD adj a k ta) (hb : PTD adj b k tb) {c : CT}
    (hc : c ∈ CT.joinC (k + 1) (ta.char a.bag) (tb.char a.bag)) :
    ∃ t, mergeReal a.bag ta tb c = some t ∧ PTD adj (.join a b) k t ∧ DomC (t.char a.bag) c := by
  have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
  obtain ⟨hab, hsub, -, -, hcross⟩ := hg'
  have hBa : a.bag ⊆ a.under := NT.bag_subset_under a
  have hBb : a.bag ⊆ b.under := hab ▸ NT.bag_subset_under b
  have hUab : a.under ∩ b.under = a.bag := Finset.Subset.antisymm hsub (Finset.subset_inter hBa hBb)
  set B := a.bag with hB
  set A := analyze B ta with hA
  set A' := analyze B tb with hA'
  have hcA : Canon B A := analyze_canon B ta
  have hcA' : Canon B A' := analyze_canon B tb
  have hpA : Pkg a.under A := pkg_analyze B a.under ta ha.1.conn (by rw [ha.1.verts_eq])
  have hpA' : Pkg b.under A' := pkg_analyze B b.under tb hb.1.conn (by rw [hb.1.verts_eq])
  have hc' : c ∈ joinC (k + 1) (AR.charF Finset.card A) (AR.charF Finset.card A') := by
    rw [char_eq_charF, char_eq_charF] at hc; exact hc
  obtain ⟨M, hM⟩ := mergeAR_exists (k + 1) A A' c (allne_analyze B ta) (allne_analyze B tb) hc'
  have hWA : ∀ X ∈ (AR.toRT A).bags, X.card ≤ k + 1 := width_toRT_analyze B ha.2
  have hWB : ∀ X ∈ (AR.toRT A').bags, X.card ≤ k + 1 := width_toRT_analyze B hb.2
  obtain ⟨hdom, hwidth⟩ := merge_props hUab (k + 1) A A' c M hcA hcA' hpA hpA' hWA hWB hc' hM
  have hiface := merge_interface hUab (k + 1) A A' c M hcA hcA' hpA hpA' hc' hM
  have hcanon := (merge_canon hUab (k + 1) A A' c M hcA hcA' hpA hpA' hc' hM).1
  refine ⟨AR.toRT M, ?_, ⟨⟨?_, ?_, hiface.conn⟩, hwidth⟩, ?_⟩
  · unfold mergeReal
    rw [hM]; rfl
  · -- vertices
    rw [hiface.verts, verts_toRT_analyze, verts_toRT_analyze, ha.1.verts_eq, hb.1.verts_eq]
    rfl
  · -- edges
    intro u v huv hu hv
    have hcov : ∀ {X : Finset ℕ}, X ∈ ta.bags ∨ X ∈ tb.bags → u ∈ X → v ∈ X →
        ∃ Y ∈ (AR.toRT M).bags, u ∈ Y ∧ v ∈ Y := by
      intro X hX hu' hv'
      rcases hX with hX | hX
      · obtain ⟨Y, hY, hXY⟩ := hiface.bagsA X ((mem_bags_toRT_analyze B ta X).2 hX)
        exact ⟨Y, hY, hXY hu', hXY hv'⟩
      · obtain ⟨Y, hY, hXY⟩ := hiface.bagsB X ((mem_bags_toRT_analyze B tb X).2 hX)
        exact ⟨Y, hY, hXY hu', hXY hv'⟩
    simp only [NT.under, Finset.mem_union] at hu hv
    by_cases hua : u ∈ a.under
    · by_cases hva : v ∈ a.under
      · obtain ⟨X, hX, hxu, hxv⟩ := ha.1.edges u v huv hua hva
        exact hcov (Or.inl hX) hxu hxv
      · have hvb : v ∈ b.under := hv.resolve_left hva
        by_cases hub : u ∈ b.under
        · obtain ⟨X, hX, hxu, hxv⟩ := hb.1.edges u v huv hub hvb
          exact hcov (Or.inr hX) hxu hxv
        · exfalso
          have hadj : adj u v = true ∨ adj v u = true := by
            have h := huv
            simp only [Adj.graph, SimpleGraph.fromRel_adj] at h
            exact h.2
          rcases hcross u hua v hvb hadj with h | h
          · exact hub (hBb h)
          · exact hva (hBa h)
    · have hub : u ∈ b.under := hu.resolve_left hua
      by_cases hvb : v ∈ b.under
      · obtain ⟨X, hX, hxu, hxv⟩ := hb.1.edges u v huv hub hvb
        exact hcov (Or.inr hX) hxu hxv
      · have hva : v ∈ a.under := hv.resolve_right hvb
        exfalso
        have hadj : adj v u = true ∨ adj u v = true := by
          have h := huv.symm
          simp only [Adj.graph, SimpleGraph.fromRel_adj] at h
          exact h.2
        rcases hcross v hva u hub hadj with h | h
        · exact hvb (hBb h)
        · exact hua (hBa h)
  · -- the characteristic
    rw [char_eq_charF, analyze_toRT B M hcanon]
    exact hdom

/-- Join, realised. -/
theorem realize_join {adj : Adj} {a b : NT} {k : ℕ} {ta tb : RT} (hg : (NT.join a b).Good adj)
    (ha : PTD adj a k ta) (hb : PTD adj b k tb) {c : CT}
    (hc : c ∈ CT.joinC (k + 1) (ta.char a.bag) (tb.char a.bag)) :
    ∃ t, PTD adj (.join a b) k t ∧ DomC (t.char a.bag) c := by
  obtain ⟨t, -, h1, h2⟩ := mergeReal_spec hg ha hb hc
  exact ⟨t, h1, h2⟩

/-- **NEW** the join step of the extraction (uses `joinC_mono`, `mergeReal_spec`). -/
theorem realJoin_spec {adj : Adj} {a b : NT} {k : ℕ} {ta tb : RT} (hg : (NT.join a b).Good adj)
    (ha : PTD adj a k ta) (hb : PTD adj b k tb) {ca cb c : CT} (hca : DomC (ta.char a.bag) ca)
    (hcb : DomC (tb.char a.bag) cb) (hc : c ∈ CT.joinC (k + 1) ca cb) :
    ∃ t, realJoin (k + 1) a.bag ta tb c = some t ∧ PTD adj (.join a b) k t ∧ DomC (t.char a.bag) c := by
  obtain ⟨d, hd, hdc⟩ := joinC_mono (k + 1) hca hcb c hc
  have hsome : ((CT.joinC (k + 1) (ta.char a.bag) (tb.char a.bag)).find? (fun e => domCB e c)).isSome = true :=
    List.find?_isSome.2 ⟨d, hd, domCB_iff.2 hdc⟩
  obtain ⟨d0, hd0⟩ := Option.isSome_iff_exists.1 hsome
  have hmem := List.mem_of_find?_eq_some hd0
  have hpred : DomC d0 c := domCB_iff.1 (List.find?_some (p := fun e => domCB e c) hd0)
  obtain ⟨t, ht, h1, h2⟩ := mergeReal_spec hg ha hb hmem
  refine ⟨t, ?_, h1, DomC.trans h2 hpred⟩
  unfold realJoin
  rw [hd0]
  exact ht

end Lax117284Proofs.Treewidth.Chars
