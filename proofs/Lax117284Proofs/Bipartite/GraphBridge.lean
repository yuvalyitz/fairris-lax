import Lax117284.BipartiteKuhnCorrect
import Lax117284Proofs.Bipartite.KuhnCorrect

/-!
The bridge between the relation Kuhn's algorithm works on and Mathlib's matchings of a graph on
`Fin V` split at `n`: a matching `μ : Fin (V - n) → Option (Fin n)` of the relation
`leftRel G n hn` is turned into a subgraph of `G` with one edge `s(l, n + r)` per matched right
vertex `r`, and conversely a matching subgraph `M` of `G` is read as the relation matching
sending each right vertex to its unique neighbour in `M`, which the split places on the left.
Both directions preserve the size, so the matching number of `G` is the largest size of a
relation matching, which is the size of the algorithm's result.
-/

namespace Lax117284Proofs.Bipartite.GraphBridge

open Lax117284.BipartiteKuhn Lax117284.BipartiteGraph Lax117284Proofs.Bipartite.Matching Lax117284Proofs.Bipartite.Maximum

/-! ### The two sides of the split as vertices of the graph -/

section Sides

variable {V n : ℕ} (hn : n ≤ V)

/-- A left vertex as a vertex of the graph. -/
def lv (i : Fin n) : Fin V := ⟨i, by omega⟩

/-- A right vertex as a vertex of the graph. -/
def rv (j : Fin (V - n)) : Fin V := ⟨n + j, by omega⟩

lemma lv_injective : Function.Injective (lv hn) := by
  intro i j h
  exact Fin.ext (Fin.mk.inj h)

lemma rv_injective : Function.Injective (rv hn) := by
  intro i j h
  have := Fin.mk.inj h
  exact Fin.ext (by omega)

lemma lv_ne_rv (i : Fin n) (j : Fin (V - n)) : lv hn i ≠ rv hn j := fun h => by
  have := Fin.mk.inj h
  have := i.isLt
  omega

lemma lv_mem_leftSide (i : Fin n) : lv hn i ∈ leftSide V n := i.isLt

lemma rv_mem_rightSide (j : Fin (V - n)) : rv hn j ∈ rightSide V n :=
  show n ≤ n + (j : ℕ) from Nat.le_add_right _ _

lemma lv_notMem_rightSide (i : Fin n) : lv hn i ∉ rightSide V n := fun h => by
  have : n ≤ (i : ℕ) := h
  have := i.isLt
  omega

lemma rv_notMem_leftSide (j : Fin (V - n)) : rv hn j ∉ leftSide V n := fun h => by
  have : n + (j : ℕ) < n := h
  omega

lemma mem_leftSide_iff {v : Fin V} : v ∈ leftSide V n ↔ ∃ i, v = lv hn i := by
  constructor
  · intro h
    have h' : (v : ℕ) < n := h
    exact ⟨⟨v, h'⟩, Fin.ext rfl⟩
  · rintro ⟨i, rfl⟩
    exact lv_mem_leftSide hn i

lemma mem_rightSide_iff {v : Fin V} : v ∈ rightSide V n ↔ ∃ j, v = rv hn j := by
  constructor
  · intro h
    have h' : n ≤ (v : ℕ) := h
    have hv := v.isLt
    exact ⟨⟨v - n, by omega⟩, Fin.ext (show (v : ℕ) = n + (v - n) by omega)⟩
  · rintro ⟨j, rfl⟩
    exact rv_mem_rightSide hn j

lemma eq_lv_or_rv (v : Fin V) : (∃ i, v = lv hn i) ∨ ∃ j, v = rv hn j := by
  by_cases h : (v : ℕ) < n
  · exact Or.inl ((mem_leftSide_iff hn).1 h)
  · exact Or.inr ((mem_rightSide_iff hn).1 (Nat.le_of_not_lt h))

end Sides

/-! ### Sizes of relation matchings -/

section Sizes

variable {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

omit [DecidableEq L] [DecidableEq R] in
lemma size_le_card_left {μ : R → Option L} (hinj : InjOnSupport μ) :
    size μ ≤ Fintype.card L := by
  rw [size_eq_card_matchedL hinj]; exact Finset.card_le_univ _

omit [DecidableEq L] [DecidableEq R] in
lemma size_eq_card_left_iff {μ : R → Option L} (hinj : InjOnSupport μ) :
    size μ = Fintype.card L ↔ ∀ l, Matched μ l := by
  rw [size_eq_card_matchedL hinj, Finset.card_eq_iff_eq_univ, Finset.eq_univ_iff_forall]
  simp only [mem_matchedL]

omit [Fintype L] [DecidableEq L] [DecidableEq R] in
lemma size_le_card_right (μ : R → Option L) : size μ ≤ Fintype.card R :=
  Finset.card_le_univ _

omit [Fintype L] [DecidableEq L] [DecidableEq R] in
lemma size_eq_card_right_iff (μ : R → Option L) :
    size μ = Fintype.card R ↔ ∀ r, ∃ l, μ r = some l := by
  unfold size
  rw [Finset.card_eq_iff_eq_univ, Finset.eq_univ_iff_forall]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_exists]

omit [Fintype L] [DecidableEq L] [DecidableEq R] in
/-- The matched right vertices, as the set whose cardinality `size` counts. -/
lemma coe_filter_isSome (μ : R → Option L) :
    ((Finset.univ.filter fun r => (μ r).isSome : Finset R) : Set R) =
      {r | ∃ l, μ r = some l} := by
  ext r
  simp [Option.isSome_iff_exists]

omit [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
lemma choose_eq {μ : R → Option L} {r : R} (h : ∃ l, μ r = some l) {l : L}
    (hl : μ r = some l) : h.choose = l :=
  Option.some.inj (h.choose_spec.symm.trans hl)

end Sizes

/-! ### From a relation matching to a subgraph -/

section ToSubgraph

variable {V n : ℕ} (G : SimpleGraph (Fin V)) (hn : n ≤ V)

/-- The subgraph of the relation matching `μ`: the edges `s(l, n + r)` with `μ r = some l`,
on their endpoints. -/
def toSubgraph (μ : Fin (V - n) → Option (Fin n))
    (hres : Respects (Lax117284.BipartiteKuhnCorrect.leftRel G n hn) μ) : G.Subgraph where
  verts := {v | ∃ r l, μ r = some l ∧ (v = lv hn l ∨ v = rv hn r)}
  Adj v w := ∃ r l, μ r = some l ∧ ((v = lv hn l ∧ w = rv hn r) ∨ (v = rv hn r ∧ w = lv hn l))
  adj_sub := by
    rintro v w ⟨r, l, hμ, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hres r l hμ
    · exact (hres r l hμ).symm
  edge_vert := by
    rintro v w ⟨r, l, hμ, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨r, l, hμ, Or.inl rfl⟩
    · exact ⟨r, l, hμ, Or.inr rfl⟩
  symm := ⟨by
    rintro v w ⟨r, l, hμ, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨r, l, hμ, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨r, l, hμ, Or.inl ⟨rfl, rfl⟩⟩⟩

variable {G hn}

theorem toSubgraph_isMatching {μ : Fin (V - n) → Option (Fin n)}
    (hres : Respects (Lax117284.BipartiteKuhnCorrect.leftRel G n hn) μ) (hinj : InjOnSupport μ) :
    (toSubgraph G hn μ hres).IsMatching := by
  rintro v ⟨r, l, hμ, rfl | rfl⟩
  · refine ⟨rv hn r, ⟨r, l, hμ, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
    rintro w ⟨r', l', hμ', ⟨hv, rfl⟩ | ⟨hv, rfl⟩⟩
    · obtain rfl := lv_injective hn hv
      obtain rfl := hinj r r' l hμ hμ'
      rfl
    · exact absurd hv (lv_ne_rv hn _ _)
  · refine ⟨lv hn l, ⟨r, l, hμ, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
    rintro w ⟨r', l', hμ', ⟨hv, rfl⟩ | ⟨hv, rfl⟩⟩
    · exact absurd hv.symm (lv_ne_rv hn _ _)
    · obtain rfl := rv_injective hn hv
      rw [hμ] at hμ'
      cases hμ'
      rfl

theorem ncard_edgeSet_toSubgraph {μ : Fin (V - n) → Option (Fin n)}
    (hres : Respects (Lax117284.BipartiteKuhnCorrect.leftRel G n hn) μ) :
    (toSubgraph G hn μ hres).edgeSet.ncard = size μ := by
  unfold size
  rw [← Set.ncard_coe_finset, coe_filter_isSome]
  symm
  refine Set.ncard_congr (fun r hr => s(lv hn hr.choose, rv hn r)) ?_ ?_ ?_
  · intro r hr
    rw [SimpleGraph.Subgraph.mem_edgeSet]
    exact ⟨r, hr.choose, hr.choose_spec, Or.inl ⟨rfl, rfl⟩⟩
  · intro r r' hr hr' h
    rcases Sym2.eq_iff.1 h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact rv_injective hn h2
    · exact absurd h1 (lv_ne_rv hn _ _)
  · intro e he
    revert he
    refine Sym2.inductionOn e fun v w he => ?_
    rw [SimpleGraph.Subgraph.mem_edgeSet] at he
    obtain ⟨r, l, hμ, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := he
    · refine ⟨r, ⟨l, hμ⟩, ?_⟩
      rw [choose_eq _ hμ]
    · refine ⟨r, ⟨l, hμ⟩, ?_⟩
      rw [choose_eq _ hμ, Sym2.eq_swap]

end ToSubgraph

/-! ### From a matching subgraph to a relation matching -/

section OfSubgraph

variable {V n : ℕ} {G : SimpleGraph (Fin V)} (hn : n ≤ V)

open Classical in
/-- The relation matching of a subgraph: each right vertex goes to a left neighbour in `M`, if it
has one. -/
noncomputable def ofSubgraph (M : G.Subgraph) : Fin (V - n) → Option (Fin n) :=
  fun r => if h : ∃ l, M.Adj (rv hn r) (lv hn l) then some h.choose else none

variable {hn} {M : G.Subgraph}

lemma ofSubgraph_eq_some_iff (hM : M.IsMatching) {r : Fin (V - n)} {l : Fin n} :
    ofSubgraph hn M r = some l ↔ M.Adj (rv hn r) (lv hn l) := by
  unfold ofSubgraph
  split_ifs with h
  · constructor
    · intro he
      rw [← Option.some.inj he]
      exact h.choose_spec
    · intro hadj
      rw [lv_injective hn (hM.eq_of_adj_left h.choose_spec hadj)]
  · exact ⟨fun he => (by cases he), fun hadj => (h ⟨l, hadj⟩).elim⟩

lemma ofSubgraph_respects (hM : M.IsMatching) :
    Respects (Lax117284.BipartiteKuhnCorrect.leftRel G n hn) (ofSubgraph hn M) := by
  intro r l h
  exact (M.adj_sub ((ofSubgraph_eq_some_iff hM).1 h)).symm

lemma ofSubgraph_injOnSupport (hM : M.IsMatching) : InjOnSupport (ofSubgraph hn M) := by
  intro r r' l h h'
  exact rv_injective hn (hM.eq_of_adj_right ((ofSubgraph_eq_some_iff hM).1 h)
    ((ofSubgraph_eq_some_iff hM).1 h'))

/-- A left vertex of `M` is matched by the relation matching. -/
lemma matched_ofSubgraph_of_mem_verts (hs : SplitAt G n) (hM : M.IsMatching) {l : Fin n}
    (hv : lv hn l ∈ M.verts) : Matched (ofSubgraph hn M) l := by
  obtain ⟨w, hw, -⟩ := hM hv
  rcases hs.mem_of_adj (M.adj_sub hw) with ⟨-, hw'⟩ | ⟨hv', -⟩
  · obtain ⟨r, rfl⟩ := (mem_rightSide_iff hn).1 hw'
    exact ⟨r, (ofSubgraph_eq_some_iff hM).2 hw.symm⟩
  · exact absurd hv' (lv_notMem_rightSide hn l)

/-- A right vertex of `M` is matched by the relation matching. -/
lemma isSome_ofSubgraph_of_mem_verts (hs : SplitAt G n) (hM : M.IsMatching) {r : Fin (V - n)}
    (hv : rv hn r ∈ M.verts) : ∃ l, ofSubgraph hn M r = some l := by
  obtain ⟨w, hw, -⟩ := hM hv
  rcases hs.mem_of_adj (M.adj_sub hw) with ⟨hv', -⟩ | ⟨-, hw'⟩
  · exact absurd hv' (rv_notMem_leftSide hn r)
  · obtain ⟨l, rfl⟩ := (mem_leftSide_iff hn).1 hw'
    exact ⟨l, (ofSubgraph_eq_some_iff hM).2 hw⟩

theorem size_ofSubgraph (hs : SplitAt G n) (hM : M.IsMatching) :
    size (ofSubgraph hn M) = M.edgeSet.ncard := by
  unfold size
  rw [← Set.ncard_coe_finset, coe_filter_isSome]
  refine Set.ncard_congr (fun r hr => s(rv hn r, lv hn hr.choose)) ?_ ?_ ?_
  · intro r hr
    rw [SimpleGraph.Subgraph.mem_edgeSet]
    exact (ofSubgraph_eq_some_iff hM).1 hr.choose_spec
  · intro r r' hr hr' h
    rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact rv_injective hn h1
    · exact absurd h1.symm (lv_ne_rv hn _ _)
  · intro e he
    revert he
    refine Sym2.inductionOn e fun v w he => ?_
    rw [SimpleGraph.Subgraph.mem_edgeSet] at he
    rcases hs.mem_of_adj (M.adj_sub he) with ⟨hv, hw⟩ | ⟨hv, hw⟩
    · obtain ⟨l, rfl⟩ := (mem_leftSide_iff hn).1 hv
      obtain ⟨r, rfl⟩ := (mem_rightSide_iff hn).1 hw
      have hμ : ofSubgraph hn M r = some l := (ofSubgraph_eq_some_iff hM).2 he.symm
      refine ⟨r, ⟨l, hμ⟩, ?_⟩
      rw [choose_eq _ hμ, Sym2.eq_swap]
    · obtain ⟨r, rfl⟩ := (mem_rightSide_iff hn).1 hv
      obtain ⟨l, rfl⟩ := (mem_leftSide_iff hn).1 hw
      have hμ : ofSubgraph hn M r = some l := (ofSubgraph_eq_some_iff hM).2 he
      refine ⟨r, ⟨l, hμ⟩, ?_⟩
      rw [choose_eq _ hμ]

end OfSubgraph

/-! ### The matching number -/

section MatchingNumber

variable {V : ℕ} (G : SimpleGraph (Fin V)) (n : ℕ) (hn : n ≤ V)

open scoped Classical in
/--
---
conclusion: Lax117284.BipartiteKuhnCorrect.kuhn_matchingNumber
---
The result of the algorithm is a relation matching, hence a matching subgraph of the same size;
and every matching subgraph is a relation matching of the same size, which the algorithm's result
outnumbers. So the set of sizes of matchings has the result's size as its greatest element.
-/
theorem kuhn_matchingNumber (hs : SplitAt G n) :
    size (kuhn (Lax117284.BipartiteKuhnCorrect.leftRel G n hn)) = Lax117284.BipartiteMatching.matchingNumber G := by
  unfold Lax117284.BipartiteMatching.matchingNumber
  have hK := Lax117284Proofs.Bipartite.KuhnCorrect.kuhn_isMatching (Lax117284.BipartiteKuhnCorrect.leftRel G n hn)
  have hmem : size (kuhn (Lax117284.BipartiteKuhnCorrect.leftRel G n hn)) ∈
      {k | ∃ M : G.Subgraph, M.IsMatching ∧ Lax117284.BipartiteMatching.size G M = k} :=
    ⟨toSubgraph G hn _ hK.1, toSubgraph_isMatching hK.1 hK.2, ncard_edgeSet_toSubgraph hK.1⟩
  have hbd : ∀ k ∈ {k | ∃ M : G.Subgraph, M.IsMatching ∧ Lax117284.BipartiteMatching.size G M = k},
      k ≤ size (kuhn (Lax117284.BipartiteKuhnCorrect.leftRel G n hn)) := by
    rintro k ⟨M, hM, rfl⟩
    rw [Lax117284.BipartiteMatching.size, ← size_ofSubgraph (hn := hn) hs hM]
    exact Lax117284Proofs.Bipartite.KuhnCorrect.kuhn_maximum _ _ (ofSubgraph_respects hM)
      (ofSubgraph_injOnSupport hM)
  exact le_antisymm (le_csSup ⟨_, hbd⟩ hmem) (csSup_le ⟨_, hmem⟩ hbd)

include hn in
open scoped Classical in
/-- **A matching saturating the left side exists exactly when the matching number is `n`.** -/
theorem exists_saturating_iff (hs : SplitAt G n) :
    (∃ M : G.Subgraph, M.IsMatching ∧ Lax117284.BipartiteMatching.Saturates G M (leftSide V n)) ↔
      Lax117284.BipartiteMatching.matchingNumber G = n := by
  rw [← kuhn_matchingNumber G n hn hs]
  have hK := Lax117284Proofs.Bipartite.KuhnCorrect.kuhn_isMatching (Lax117284.BipartiteKuhnCorrect.leftRel G n hn)
  have hle : size (kuhn (Lax117284.BipartiteKuhnCorrect.leftRel G n hn)) ≤ n := by
    have := size_le_card_left hK.2
    rwa [Fintype.card_fin] at this
  constructor
  · rintro ⟨M, hM, hsat⟩
    have hall : ∀ l, Matched (ofSubgraph hn M) l := fun l =>
      matched_ofSubgraph_of_mem_verts hs hM (hsat (lv_mem_leftSide hn l))
    refine le_antisymm hle ?_
    calc n = size (ofSubgraph hn M) := by
          rw [(size_eq_card_left_iff (ofSubgraph_injOnSupport hM)).2 hall, Fintype.card_fin]
      _ ≤ _ := Lax117284Proofs.Bipartite.KuhnCorrect.kuhn_maximum _ _ (ofSubgraph_respects hM)
          (ofSubgraph_injOnSupport hM)
  · intro h
    have hall : ∀ l, Matched (kuhn (Lax117284.BipartiteKuhnCorrect.leftRel G n hn)) l :=
      (size_eq_card_left_iff hK.2).1 (by rw [h, Fintype.card_fin])
    refine ⟨toSubgraph G hn _ hK.1, toSubgraph_isMatching hK.1 hK.2, ?_⟩
    intro v hv
    obtain ⟨l, rfl⟩ := (mem_leftSide_iff hn).1 hv
    obtain ⟨r, hr⟩ := hall l
    exact ⟨r, l, hr, Or.inl rfl⟩

include hn in
open scoped Classical in
/-- **A perfect matching exists exactly when twice the matching number is the number of
vertices.** -/
theorem exists_perfect_iff (hs : SplitAt G n) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔ 2 * Lax117284.BipartiteMatching.matchingNumber G = V := by
  rw [← kuhn_matchingNumber G n hn hs]
  have hK := Lax117284Proofs.Bipartite.KuhnCorrect.kuhn_isMatching (Lax117284.BipartiteKuhnCorrect.leftRel G n hn)
  have hle : size (kuhn (Lax117284.BipartiteKuhnCorrect.leftRel G n hn)) ≤ n := by
    have := size_le_card_left hK.2
    rwa [Fintype.card_fin] at this
  have hle' : size (kuhn (Lax117284.BipartiteKuhnCorrect.leftRel G n hn)) ≤ V - n := by
    have := size_le_card_right (kuhn (Lax117284.BipartiteKuhnCorrect.leftRel G n hn))
    rwa [Fintype.card_fin] at this
  constructor
  · rintro ⟨M, hM, hsp⟩
    have hL : size (ofSubgraph hn M) = n := by
      rw [(size_eq_card_left_iff (ofSubgraph_injOnSupport hM)).2
        (fun l => matched_ofSubgraph_of_mem_verts hs hM (hsp (lv hn l))), Fintype.card_fin]
    have hR : size (ofSubgraph hn M) = V - n := by
      rw [(size_eq_card_right_iff _).2
        (fun r => isSome_ofSubgraph_of_mem_verts hs hM (hsp (rv hn r))), Fintype.card_fin]
    have h3 : size (ofSubgraph hn M) ≤ size (kuhn (Lax117284.BipartiteKuhnCorrect.leftRel G n hn)) :=
      Lax117284Proofs.Bipartite.KuhnCorrect.kuhn_maximum _ _ (ofSubgraph_respects hM)
        (ofSubgraph_injOnSupport hM)
    omega
  · intro h
    have hL : ∀ l, Matched (kuhn (Lax117284.BipartiteKuhnCorrect.leftRel G n hn)) l :=
      (size_eq_card_left_iff hK.2).1 (by rw [Fintype.card_fin]; omega)
    have hR : ∀ r, ∃ l, kuhn (Lax117284.BipartiteKuhnCorrect.leftRel G n hn) r = some l :=
      (size_eq_card_right_iff _).1 (by rw [Fintype.card_fin]; omega)
    refine ⟨toSubgraph G hn _ hK.1, toSubgraph_isMatching hK.1 hK.2, ?_⟩
    intro v
    rcases eq_lv_or_rv hn v with ⟨l, rfl⟩ | ⟨r, rfl⟩
    · obtain ⟨r, hr⟩ := hL l
      exact ⟨r, l, hr, Or.inl rfl⟩
    · obtain ⟨l, hl⟩ := hR r
      exact ⟨r, l, hl, Or.inr rfl⟩

end MatchingNumber

end Lax117284Proofs.Bipartite.GraphBridge
