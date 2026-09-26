import Lax117284.BipartiteGraph
import Lax117284.BipartiteKuhnCorrect
import Lax117284Proofs.Bipartite.Ram2.Word

/-!
From the concept's `EncodesBipartite x V G n` to what the machine needs: the arithmetic facts
`Good x`, the header values, the adjacency across the split as the machine reads it
(`adjw x`, which is `leftRel G n`), and `wordGraph x = G`.

The word is `g ++ [n]` with `g` the CSR block; every position the machine reads below
`g.length` reads the block, and the last position reads `n`.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax271696.GraphEncoding Lax117284.BipartiteGraph Lax117284.BipartiteKuhnCorrect

theorem getD_append_lt {g : List ℕ} {i : ℕ} (hi : i < g.length) (v : ℕ) :
    (g ++ [v]).getD i 0 = g.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_last (g : List ℕ) (v : ℕ) : (g ++ [v]).getD g.length 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
  simp

/-- A function nondecreasing below `V` is bounded by its value at `V`. -/
theorem mono_chain (f : ℕ → ℕ) (V : ℕ) (hmono : ∀ i < V, f i ≤ f (i + 1)) :
    ∀ i ≤ V, f i ≤ f V := by
  have key : ∀ k i, i + k ≤ V → f i ≤ f (i + k) := by
    intro k
    induction k with
    | zero => intro i _; simp
    | succ k ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := hmono (i + k) (by omega)
      calc f i ≤ f (i + k) := h1
        _ ≤ f (i + k + 1) := h2
        _ = f (i + (k + 1)) := by rw [Nat.add_assoc]
  intro i hi
  have := key (V - i) i (by omega)
  rwa [Nat.add_sub_cancel' hi] at this

section Block

variable {x g : List ℕ} {V : ℕ} {G : SimpleGraph (Fin V)} {n : ℕ}
  (hx : x = g ++ [n]) (hg : EncodesGraph g V G)
include hx hg

theorem Vw_eq' : Vw x = V := by
  subst hx
  have := hg.length_eq
  show (g ++ [n]).getD 0 0 = V
  rw [getD_append_lt (by omega)]
  exact hg.vertexCount_eq

theorem edge_eq' : x.getD 1 0 = edgeCount g := by
  subst hx
  have := hg.length_eq
  exact getD_append_lt (by omega) n

omit hg in
theorem nw_eq' : nw x = n := by
  subst hx
  show (g ++ [n]).getD ((g ++ [n]).length - 1) 0 = n
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel]
  exact getD_append_last g n

theorem len_eq' : x.length = 4 + V + 2 * edgeCount g := by
  subst hx
  have := hg.length_eq
  rw [List.length_append, List.length_singleton]
  omega

theorem offw_eq' {i : ℕ} (hi : i ≤ V) : offw x i = offset g i := by
  subst hx
  have := hg.length_eq
  exact getD_append_lt (by omega) n

theorem tgtw_eq' {s : ℕ} (hs : s < 2 * edgeCount g) : tgtw x s = target g s := by
  have hV := Vw_eq' hx hg
  unfold tgtw target
  rw [hV, hg.vertexCount_eq]
  subst hx
  have := hg.length_eq
  exact getD_append_lt (by omega) n

omit hx in
/-- Slots of a row below `V` are slots of the target array. -/
theorem slot_lt' {l s : ℕ} (hl : l < V) (hs : s < offset g (l + 1)) : s < 2 * edgeCount g := by
  have hchain := mono_chain (offset g) V hg.offset_mono
  rw [← hg.offset_last]
  exact lt_of_lt_of_le hs (hchain (l + 1) hl)

end Block

section Bridge

variable {x : List ℕ} {V : ℕ} {G : SimpleGraph (Fin V)} {n : ℕ}

theorem vertexCount_eq (h : EncodesBipartite x V G n) : vertexCount x = V := by
  obtain ⟨g, hx, hg, -, -⟩ := h
  exact Vw_eq' hx hg

theorem nw_eq (h : EncodesBipartite x V G n) : nw x = n := by
  obtain ⟨g, hx, hg, -, -⟩ := h
  exact nw_eq' hx

theorem leftCount_eq (h : EncodesBipartite x V G n) : leftCount x = n := by
  show x.getLastD 0 = n
  rw [← nw_eq_getLastD]; exact nw_eq h

/-- **An admissible word is `Good`.** -/
theorem good_of_encodes (h : EncodesBipartite x V G n) : Good x := by
  obtain ⟨g, hx, hg, hnV, hs⟩ := h
  have hV := Vw_eq' hx hg
  have hn := nw_eq' hx
  have hlen := len_eq' hx hg
  have hoffV : offw x V = 2 * edgeCount g := by
    rw [offw_eq' hx hg le_rfl]; exact hg.offset_last
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hV, hn]; exact hnV
  · intro i hi
    rw [hV] at hi
    rw [offw_eq' hx hg (by omega), offw_eq' hx hg (by omega)]
    exact hg.offset_mono i hi
  · rw [hV, hoffV]; exact hlen
  · rw [hV, hoffV, edge_eq' hx hg]
  · intro s hs'
    rw [hV, hoffV] at hs'
    rw [hV, tgtw_eq' hx hg hs']
    exact hg.target_lt s hs'
  · intro l hl s hs1 hs2
    rw [hn] at hl ⊢
    rw [offw_eq' hx hg (by omega)] at hs1
    rw [offw_eq' hx hg (by omega)] at hs2
    have hs2E : s < 2 * edgeCount g := slot_lt' hg (by omega) hs2
    rw [tgtw_eq' hx hg hs2E]
    have ht : target g s < V := hg.target_lt s hs2E
    have hadj : G.Adj ⟨l, by omega⟩ ⟨target g s, ht⟩ := (hg.adj_iff _ _).2 ⟨s, hs1, hs2, rfl⟩
    rcases hs.mem_of_adj hadj with ⟨-, hr⟩ | ⟨hl', -⟩
    · exact hr
    · exact absurd hl' (by show ¬ n ≤ l; omega)

/-- **The machine's adjacency across the split is the graph's.** -/
theorem adjw_iff (h : EncodesBipartite x V G n) (i j : ℕ) (hi : i < n) (hj : j < V - n) :
    adjw x i j ↔ G.Adj ⟨i, by omega⟩ ⟨n + j, by omega⟩ := by
  obtain ⟨g, hx, hg, hnV, -⟩ := h
  have hn := nw_eq' hx
  rw [hg.adj_iff]
  unfold adjw adjOff
  rw [hn, offw_eq' hx hg (by omega), offw_eq' hx hg (by omega)]
  constructor
  · rintro ⟨s, h1, h2, h3⟩
    refine ⟨s, h1, h2, ?_⟩
    have hs2E : s < 2 * edgeCount g := slot_lt' hg (by omega) h2
    rw [← tgtw_eq' hx hg hs2E]
    exact h3
  · rintro ⟨s, h1, h2, h3⟩
    refine ⟨s, h1, h2, ?_⟩
    have hs2E : s < 2 * edgeCount g := slot_lt' hg (by omega) h2
    rw [tgtw_eq' hx hg hs2E]
    exact h3

/-- `Lists` is the graph's adjacency. -/
theorem lists_iff (h : EncodesBipartite x V G n) (u v : Fin V) : Lists x u v ↔ G.Adj u v := by
  obtain ⟨g, hx, hg, -, -⟩ := h
  rw [hg.adj_iff]
  unfold Lists
  have e1 : offset x u = offset g u := by rw [← offw_eq' hx hg (le_of_lt u.2)]; rfl
  have e2 : offset x (u + 1) = offset g (u + 1) := by rw [← offw_eq' hx hg u.2]; rfl
  rw [e1, e2]
  constructor
  · rintro ⟨s, h1, h2, h3⟩
    refine ⟨s, h1, h2, ?_⟩
    have hs2E : s < 2 * edgeCount g := slot_lt' hg u.2 h2
    rw [← h3]
    show target g s = tgtw x s
    exact (tgtw_eq' hx hg hs2E).symm
  · rintro ⟨s, h1, h2, h3⟩
    refine ⟨s, h1, h2, ?_⟩
    have hs2E : s < 2 * edgeCount g := slot_lt' hg u.2 h2
    rw [← h3]
    show tgtw x s = target g s
    exact tgtw_eq' hx hg hs2E

end Bridge

/-- **The word's graph is the graph it encodes.** -/
theorem wordGraph_eq {x : List ℕ} {G : SimpleGraph (Fin (vertexCount x))} {n : ℕ}
    (h : EncodesBipartite x (vertexCount x) G n) : wordGraph x = G := by
  ext u v
  unfold wordGraph
  rw [SimpleGraph.fromRel_adj, lists_iff h u v, lists_iff h v u]
  constructor
  · rintro ⟨-, h1 | h1⟩
    · exact h1
    · exact h1.symm
  · intro h1; exact ⟨h1.ne, Or.inl h1⟩

end Lax117284Proofs.Bipartite.Ram2
