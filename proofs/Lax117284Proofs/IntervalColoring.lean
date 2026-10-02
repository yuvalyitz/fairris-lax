import Mathlib.Data.Finset.Max
import Lax117284Proofs.ConflictGraph

/-!
# Interval Graphs Are Perfect

Theorem 13 needs one fact about the daily conflict graph, and the paper disposes of it in
a sentence:

> *"It is not hard to see that interval graphs are perfect graphs, meaning that their
> chromatic number equals the size of their largest clique [25]."*

`[25]` is Golumbic's book, so this is a citation the repository's conventions would let us
take as an `axiom`. It is proved here instead, because — as the paper says — it is not
hard, and because the only half Theorem 13 uses (`χ ≤ ω`: a graph of largest clique `ω` is
`ω`-colorable) has a three-line argument that specializes to *these* intervals with no
theory of interval graphs at all:

* Among any set `S` of clients, take the one whose day-`i` job **starts last**, say `j₀`.
* Every neighbour of `j₀` in `S` starts no later than `j₀` and ends after it does, so every
  one of them is running at the instant `start j₀` — as is `j₀`. Jobs sharing an instant
  pairwise conflict, so `N_S(j₀) ∪ {j₀}` is a clique and `|N_S(j₀)| ≤ ω - 1`.
* Colour `S \ {j₀}` by induction and give `j₀` one of the `ω` colours its at most `ω - 1`
  neighbours left free.

The other half, `ω ≤ χ` (a clique needs `|K|` colours), holds in every graph and is
`cliqueNum_le_of_colorable` below. Together they give `χ = ω` for every daily conflict
graph — `chromaticNumber_dayGraph`, which is the sentence quoted above, for this paper's
graphs, proved.
-/


namespace Lax117284Proofs.Model

namespace Instance

variable {I : Instance}

/-! ## 1. Jobs sharing an instant conflict -/

/-- If some instant `t` lies in both jobs' intervals, the two jobs conflict. -/
lemma conflict_of_mem_mem {i : I.Day} {j j' : I.Client} {t : ℕ}
    (h1 : I.start i j ≤ t) (h2 : t < I.d i j) (h3 : I.start i j' ≤ t) (h4 : t < I.d i j') :
    I.Conflict i j j' := ⟨by omega, by omega⟩

/-! ## 2. `ω` colours suffice -/

/-- The greedy argument, as an induction over the set of clients still to be coloured. The
hypothesis `hω` is "every clique has at most `ω` vertices"; the conclusion colours all of
`S` with colours below `ω`. -/
private lemma exists_greedy_coloring (I : Instance) (i : I.Day) (ω : ℕ)
    (hω : ∀ K : Finset I.Client, (I.dayGraph i).IsClique (K : Set I.Client) → K.card ≤ ω)
    (S : Finset I.Client) :
    ∃ c : I.Client → ℕ, (∀ j ∈ S, c j < ω) ∧
      ∀ j ∈ S, ∀ j' ∈ S, (I.dayGraph i).Adj j j' → c j ≠ c j' := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => 0, by simp, by simp⟩
    -- the client whose day-`i` job starts last
    obtain ⟨j₀, hj₀S, hj₀max⟩ := S.exists_max_image (I.start i) hne
    -- its neighbours inside `S`
    set N : Finset I.Client := S.filter fun j => (I.dayGraph i).Adj j₀ j with hN
    -- `N ∪ {j₀}` is a clique: everything in it runs at the instant `start i j₀`
    have hrun : ∀ j ∈ insert j₀ N, I.start i j ≤ I.start i j₀ ∧ I.start i j₀ < I.d i j := by
      intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact ⟨le_rfl, start_lt_d i j⟩
      · rw [hN, Finset.mem_filter] at hj
        exact ⟨hj₀max j hj.1, hj.2.2.1⟩
    have hclique : (I.dayGraph i).IsClique ((insert j₀ N : Finset I.Client) : Set I.Client) := by
      intro a ha b hb hab
      obtain ⟨ha1, ha2⟩ := hrun a (by simpa using ha)
      obtain ⟨hb1, hb2⟩ := hrun b (by simpa using hb)
      exact ⟨hab, conflict_of_mem_mem ha1 ha2 hb1 hb2⟩
    have hcard : N.card + 1 ≤ ω := by
      have hj₀ : j₀ ∉ N := fun h => (Finset.mem_filter.1 h).2.ne rfl
      have := hω _ hclique
      rwa [Finset.card_insert_of_notMem hj₀] at this
    -- colour the rest by induction
    obtain ⟨c', hlt', hproper'⟩ :=
      ih (S.erase j₀) (Finset.erase_ssubset hj₀S)
    -- pick a colour below `ω` that no neighbour uses
    have hfree : ∃ v, v < ω ∧ v ∉ N.image c' := by
      by_contra hcon
      push Not at hcon
      have hsub : Finset.range ω ⊆ N.image c' := fun v hv =>
        hcon v (Finset.mem_range.1 hv)
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      exact absurd (le_trans this (Finset.card_image_le)) (by omega)
    obtain ⟨v, hvω, hvfree⟩ := hfree
    refine ⟨Function.update c' j₀ v, ?_, ?_⟩
    · intro j hj
      by_cases hjj : j = j₀
      · simpa [hjj] using hvω
      · rw [Function.update_of_ne hjj]
        exact hlt' j (Finset.mem_erase.2 ⟨hjj, hj⟩)
    · intro a ha b hb hadj
      have hab : a ≠ b := hadj.ne
      by_cases hA : a = j₀
      · subst hA
        have hbN : b ∈ N := by
          rw [hN, Finset.mem_filter]; exact ⟨hb, hadj⟩
        rw [Function.update_of_ne (Ne.symm hab), Function.update_self]
        exact fun hEq => hvfree (Finset.mem_image.2 ⟨b, hbN, hEq.symm⟩)
      · by_cases hB : b = j₀
        · subst hB
          have haN : a ∈ N := by
            rw [hN, Finset.mem_filter]; exact ⟨ha, hadj.symm⟩
          rw [Function.update_of_ne hA, Function.update_self]
          exact fun hEq => hvfree (Finset.mem_image.2 ⟨a, haN, hEq⟩)
        · rw [Function.update_of_ne hA, Function.update_of_ne hB]
          exact hproper' a (Finset.mem_erase.2 ⟨hA, ha⟩) b (Finset.mem_erase.2 ⟨hB, hb⟩) hadj

/-- **Interval graphs are `ω`-colourable.** Every daily conflict graph can be properly
coloured with as many colours as its largest clique has vertices. -/
theorem dayGraph_colorable_cliqueNum (I : Instance) (i : I.Day) :
    (I.dayGraph i).Colorable (I.dayGraph i).cliqueNum := by
  classical
  obtain ⟨c, hlt, hproper⟩ :=
    exists_greedy_coloring I i (I.dayGraph i).cliqueNum
      (fun K hK => SimpleGraph.IsClique.card_le_cliqueNum (tc := hK)) Finset.univ
  exact ⟨SimpleGraph.Coloring.mk (fun j => ⟨c j, hlt j (Finset.mem_univ j)⟩)
    fun {a b} hadj => by
      simpa using hproper a (Finset.mem_univ a) b (Finset.mem_univ b) hadj⟩

/-! ## 3. `ω ≤ χ`, and the equality

The converse bound is true in every graph and needs no interval structure: the vertices of
a clique get pairwise different colours, so a clique embeds into the colour set. -/

/-- A `c`-colourable graph has no clique with more than `c` vertices. -/
lemma cliqueNum_le_of_colorable {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {c : ℕ} (h : G.Colorable c) : G.cliqueNum ≤ c := by
  obtain ⟨K, hK, hKcard⟩ := G.exists_isNClique_cliqueNum
  obtain ⟨C⟩ := h
  have hinj : Set.InjOn C (K : Set V) := by
    intro a ha b hb hEq
    by_contra hne
    exact C.valid (hK ha hb hne) hEq
  have := Finset.card_le_card_of_injOn C (fun _ _ => Finset.mem_univ _) hinj
  rw [hKcard] at this
  simpa using this

/-- **`χ = ω` for every daily conflict graph** — the sentence the paper cites Golumbic for,
proved here for the interval graphs this paper actually builds. -/
theorem chromaticNumber_dayGraph (I : Instance) (i : I.Day) :
    (I.dayGraph i).chromaticNumber = (I.dayGraph i).cliqueNum := by
  classical
  refine le_antisymm ((dayGraph_colorable_cliqueNum I i).chromaticNumber_le) ?_
  rw [SimpleGraph.le_chromaticNumber_iff_colorable]
  intro c hc
  exact_mod_cast cliqueNum_le_of_colorable hc

end Instance

end Lax117284Proofs.Model
