import Lax117284Proofs.Machine.MatchGuard
import Lax117284.BipartiteDecision

/-!
The CSR word of a table, read as the cited decider of `lax-817977` reads it: with the accessors
of the compressed sparse row encoding (`lax-271696`) it is well formed, its graph `wordGraph` is
the bipartite graph of the table (a left vertex `i` and a right vertex `R + j` are adjacent
exactly when the cell `(i, j)` is nonzero; no other pairs are adjacent), and so a matching
saturating its left side, in Mathlib's sense, exists exactly when the table has a full matching
in the sense of `UnitPGraph` (`Yes`). Hence, on every word, the cited `saturatingAnswer` of the
converted word is `gfun`: the answer on the fixed words `W1` and `W0` of the guards is `[1]` and
`[0]`.
-/

namespace Lax117284Proofs.Machine.MatchWord

open Lax271696.GraphEncoding Lax117284.BipartiteGraph Lax117284.BipartiteMatching Lax117284.BipartiteDecision
open Lax117284Proofs.Machine.MatchGuard
open Lax117284Proofs.UnitPGraph (Yes decodeAdj HasFullMatching)
open scoped Classical

/-! ### The word through the accessors of the encoding -/

section Accessors

variable (x : List ℕ) (R C : ℕ)

theorem vertexCount_csrP : vertexCount (csrP x R C) = R + C := rfl

theorem edgeCount_csrP : edgeCount (csrP x R C) = E x R C / 2 := rfl

theorem leftCount_csrP : leftCount (csrP x R C) = R := csrP_getLastD x R C

theorem offset_csrP {i : ℕ} (hi : i ≤ R + C) : offset (csrP x R C) i = off' x R C i :=
  csrP_off x R C hi

theorem target_csrP {s : ℕ} (hs : s < E x R C) : target (csrP x R C) s = tgt x R C s := by
  unfold target
  rw [vertexCount_csrP]
  exact csrP_tgt x R C hs

/-- The offset of a right vertex, and of the vertex after it, is the end of the target array. -/
theorem off'_of_R_le {u : ℕ} (hu : R ≤ u) : off' x R C u = E x R C := by
  rcases Nat.lt_or_ge R u with h | h
  · exact off'_of_lt x R C h
  · have : u = R := by omega
    rw [this, off'_of_le x R C le_rfl]
    rfl

/-- **The CSR word of every table is well formed.** -/
theorem wellFormed_csrP : WellFormed (csrP x R C) where
  left_le := by rw [leftCount_csrP, vertexCount_csrP]; omega
  length_eq := by rw [length_csrP, vertexCount_csrP, edgeCount_csrP, E_even]
  offset_zero := by
    rw [offset_csrP x R C (by omega), off'_of_le x R C (by omega), off_zero]
  offset_last := by
    rw [vertexCount_csrP, edgeCount_csrP, offset_csrP x R C le_rfl, off'_V, E_even]
  offset_mono := by
    intro i hi
    rw [vertexCount_csrP] at hi
    rw [offset_csrP x R C (by omega), offset_csrP x R C (by omega)]
    exact off'_mono x R C i
  target_lt := by
    intro j hj
    rw [edgeCount_csrP, E_even] at hj
    rw [vertexCount_csrP, target_csrP x R C hj]
    exact tgt_lt_V x R C hj
  crosses := by
    intro u hu j h1 h2
    rw [vertexCount_csrP] at hu
    rw [leftCount_csrP]
    rw [offset_csrP x R C (by omega)] at h1
    rw [offset_csrP x R C (by omega)] at h2
    by_cases hl : u < R
    · rw [off'_of_le x R C (by omega)] at h1
      rw [off'_of_le x R C (by omega)] at h2
      have hjE : j < E x R C := lt_of_lt_of_le h2 (off_mono x R C hl)
      rw [target_csrP x R C hjE]
      exact ⟨fun _ => R_le_tgt x R C hjE, fun _ => hl⟩
    · exfalso
      rw [off'_of_R_le x R C (by omega)] at h1
      rw [off'_of_R_le x R C (by omega)] at h2
      omega

/-- **A left vertex lists exactly the right vertices of its nonzero cells.** -/
theorem lists_csrP_left {l v : ℕ} (hl : l < R) :
    Lists (csrP x R C) l v ↔ ∃ c < C, tab x C l c ≠ 0 ∧ v = R + c := by
  unfold Lists
  rw [offset_csrP x R C (by omega), off'_of_le x R C (by omega),
    offset_csrP x R C (by omega), off'_of_le x R C (by omega)]
  have hE : off x R C (l + 1) ≤ E x R C := off_mono x R C hl
  constructor
  · rintro ⟨s, h1, h2, h3⟩
    rw [target_csrP x R C (by omega)] at h3
    obtain ⟨k, rfl⟩ : ∃ k, s = off x R C l + k := ⟨s - off x R C l, by omega⟩
    have hk : k < (row x R C l).length := by rw [off_succ] at h2; omega
    rw [tgt_row x R C hl hk] at h3
    have hmem : (row x R C l).getD k 0 ∈ row x R C l := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact List.getElem_mem _
    obtain ⟨c, hc, ht, he⟩ := (mem_row x R C).1 hmem
    exact ⟨c, hc, ht, by omega⟩
  · rintro ⟨c, hc, ht, rfl⟩
    have hmem : R + c ∈ row x R C l := (mem_row x R C).2 ⟨c, hc, ht, rfl⟩
    obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.1 hmem
    refine ⟨off x R C l + k, by omega, by rw [off_succ]; omega, ?_⟩
    rw [target_csrP x R C (by rw [off_succ] at hE; omega), tgt_row x R C hl hk,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    exact hkv

/-- **A right vertex lists nothing.** -/
theorem not_lists_csrP_right {u v : ℕ} (hu : R ≤ u) (huV : u < R + C) :
    ¬ Lists (csrP x R C) u v := by
  rintro ⟨s, h1, h2, -⟩
  rw [offset_csrP x R C (by omega), off'_of_R_le x R C hu] at h1
  rw [offset_csrP x R C (by omega), off'_of_R_le x R C (by omega)] at h2
  omega

end Accessors

/-! ### The graph of the word -/

section Graph

variable {x : List ℕ} {R C : ℕ}

theorem val_lt (u : Fin (vertexCount (csrP x R C))) : (u : ℕ) < R + C := u.isLt

/-- A left vertex of the table, as a vertex of the graph. -/
def lv (x : List ℕ) (R C : ℕ) (i : Fin R) : Fin (vertexCount (csrP x R C)) :=
  ⟨i, by rw [vertexCount_csrP]; omega⟩

/-- A right vertex of the table, as a vertex of the graph. -/
def rv (x : List ℕ) (R C : ℕ) (j : Fin C) : Fin (vertexCount (csrP x R C)) :=
  ⟨R + j, by rw [vertexCount_csrP]; omega⟩

theorem adj_iff (u v : Fin (vertexCount (csrP x R C))) :
    (wordGraph (csrP x R C)).Adj u v ↔
      u ≠ v ∧ (Lists (csrP x R C) u v ∨ Lists (csrP x R C) v u) := by
  unfold wordGraph
  exact SimpleGraph.fromRel_adj _ _ _

/-- Every edge of the graph joins a left vertex to a right vertex of a nonzero cell. -/
theorem adj_cases {u v : Fin (vertexCount (csrP x R C))}
    (h : (wordGraph (csrP x R C)).Adj u v) :
    ∃ (i : Fin R) (j : Fin C), tab x C i j ≠ 0 ∧
      (((u : ℕ) = i ∧ (v : ℕ) = R + j) ∨ ((u : ℕ) = R + j ∧ (v : ℕ) = i)) := by
  rw [adj_iff] at h
  obtain ⟨-, h | h⟩ := h
  · rcases Nat.lt_or_ge (u : ℕ) R with hu | hu
    · obtain ⟨c, hc, ht, he⟩ := (lists_csrP_left x R C hu).1 h
      exact ⟨⟨u, hu⟩, ⟨c, hc⟩, ht, Or.inl ⟨rfl, he⟩⟩
    · exact absurd h (not_lists_csrP_right x R C hu (val_lt u))
  · rcases Nat.lt_or_ge (v : ℕ) R with hv | hv
    · obtain ⟨c, hc, ht, he⟩ := (lists_csrP_left x R C hv).1 h
      exact ⟨⟨v, hv⟩, ⟨c, hc⟩, ht, Or.inr ⟨he, rfl⟩⟩
    · exact absurd h (not_lists_csrP_right x R C hv (val_lt v))

/-- A nonzero cell is an edge. -/
theorem adj_of_tab {i : Fin R} {j : Fin C} (ht : tab x C i j ≠ 0) :
    (wordGraph (csrP x R C)).Adj (lv x R C i) (rv x R C j) := by
  rw [adj_iff]
  refine ⟨fun h => ?_, Or.inl ((lists_csrP_left x R C i.isLt).2 ⟨j, j.isLt, ht, rfl⟩)⟩
  have h' := congrArg Fin.val h
  change (i : ℕ) = R + j at h'
  have := i.isLt
  omega

/-- The matching subgraph of an injection `f` of the left vertices along the edges: the edges
`{i, R + f i}` on their endpoints. -/
def matchSub (x : List ℕ) (R C : ℕ) (f : Fin R → Fin C) (hf : ∀ i : Fin R, tab x C i (f i) ≠ 0) :
    (wordGraph (csrP x R C)).Subgraph where
  verts := {v | ∃ i : Fin R, v = lv x R C i ∨ v = rv x R C (f i)}
  Adj v w := ∃ i : Fin R,
    (v = lv x R C i ∧ w = rv x R C (f i)) ∨ (v = rv x R C (f i) ∧ w = lv x R C i)
  adj_sub := by
    rintro v w ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact adj_of_tab (hf i)
    · exact (adj_of_tab (hf i)).symm
  edge_vert := by
    rintro v w ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨i, Or.inl rfl⟩
    · exact ⟨i, Or.inr rfl⟩
  symm := ⟨by
    rintro v w ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨i, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨i, Or.inl ⟨rfl, rfl⟩⟩⟩

theorem matchSub_isMatching (f : Fin R → Fin C) (hinj : Function.Injective f)
    (hf : ∀ i : Fin R, tab x C i (f i) ≠ 0) : (matchSub x R C f hf).IsMatching := by
  rintro v ⟨i, rfl | rfl⟩
  · refine ⟨rv x R C (f i), ⟨i, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
    rintro w ⟨i', ⟨hv, rfl⟩ | ⟨hv, rfl⟩⟩
    · have h' := congrArg Fin.val hv
      change (i : ℕ) = i' at h'
      obtain rfl : i = i' := Fin.ext h'
      rfl
    · exfalso
      have h' := congrArg Fin.val hv
      change (i : ℕ) = R + f i' at h'
      have := i.isLt
      omega
  · refine ⟨lv x R C i, ⟨i, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
    rintro w ⟨i', ⟨hv, rfl⟩ | ⟨hv, rfl⟩⟩
    · exfalso
      have h' := congrArg Fin.val hv
      change R + (f i : ℕ) = i' at h'
      have := i'.isLt
      omega
    · have h' := congrArg Fin.val hv
      change R + (f i : ℕ) = R + f i' at h'
      obtain rfl : i = i' := hinj (Fin.ext (by omega))
      rfl

/-- **A matching saturating the left side exists exactly when the table has a full
matching.** -/
theorem exists_saturating_iff (x : List ℕ) (R C : ℕ) :
    (∃ M : (wordGraph (csrP x R C)).Subgraph, M.IsMatching ∧
        Saturates (wordGraph (csrP x R C)) M (leftSide (vertexCount (csrP x R C)) R)) ↔
      HasFullMatching (fun (i : Fin R) (j : Fin C) => tab x C i j ≠ 0) := by
  constructor
  · rintro ⟨M, hM, hsat⟩
    have key : ∀ i : Fin R, ∃ j : Fin C, tab x C i j ≠ 0 ∧ M.Adj (lv x R C i) (rv x R C j) := by
      intro i
      have hmem : lv x R C i ∈ M.verts := hsat (show ((lv x R C i : ℕ)) < R from i.isLt)
      obtain ⟨w, hw, -⟩ := hM hmem
      obtain ⟨i', j, ht, h | h⟩ := adj_cases (M.adj_sub hw)
      · obtain rfl : i' = i := Fin.ext h.1.symm
        have hw' : w = rv x R C j := Fin.ext h.2
        rw [hw'] at hw
        exact ⟨j, ht, hw⟩
      · exfalso
        have h' := h.1
        change (i : ℕ) = R + j at h'
        have := i.isLt
        omega
    choose f hf using key
    refine ⟨f, fun a b hab => ?_, fun i => (hf i).1⟩
    have h1 := (hf a).2
    have h2 := (hf b).2
    rw [hab] at h1
    have h3 := congrArg Fin.val (hM.eq_of_adj_right h1 h2)
    change (a : ℕ) = b at h3
    exact Fin.ext h3
  · rintro ⟨f, hinj, hf⟩
    refine ⟨matchSub x R C f hf, matchSub_isMatching f hinj hf, ?_⟩
    intro v hv
    exact ⟨⟨v, hv⟩, Or.inl (Fin.ext rfl)⟩

end Graph

/-! ### The answer of the cited decider on the converted words -/

/-- **The cited decider answers `Yes` on the CSR word of a table.** -/
theorem saturatingAnswer_csrOf (x : List ℕ) :
    saturatingAnswer (csrOf x) = [if Yes x then 1 else 0] := by
  unfold saturatingAnswer csrOf
  rw [leftCount_csrP]
  have h := exists_saturating_iff x (x.getD 0 0) (x.getD 1 0)
  have hw := wellFormed_csrP x (x.getD 0 0) (x.getD 1 0)
  by_cases hy : Yes x
  · have hy' : HasFullMatching (fun (i : Fin (x.getD 0 0)) (j : Fin (x.getD 1 0)) =>
        tab x (x.getD 1 0) i j ≠ 0) := hy
    rw [if_pos hy, if_pos ⟨hw, h.2 hy'⟩]
  · rw [if_neg hy, if_neg (fun hh => hy (h.1 hh.2))]

/-- The empty graph: its empty left side is saturated. -/
theorem saturatingAnswer_W1 : saturatingAnswer W1 = [1] := by
  unfold saturatingAnswer
  rw [if_pos]
  have hV : vertexCount W1 = 0 := rfl
  have hE : edgeCount W1 = 0 := rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⊥, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · intro i hi; omega
  · intro j hj; omega
  · intro u hu; omega
  · intro v hv
    rw [SimpleGraph.Subgraph.verts_bot] at hv
    exact absurd hv (Set.notMem_empty v)
  · intro v _
    have := v.isLt
    omega

/-- One isolated left vertex: no matching saturates it. -/
theorem saturatingAnswer_W0 : saturatingAnswer W0 = [0] := by
  unfold saturatingAnswer
  rw [if_neg]
  rintro ⟨-, M, hM, hsat⟩
  have hV : vertexCount W0 = 1 := rfl
  have hn : leftCount W0 = 1 := rfl
  have h0 : (0 : ℕ) < vertexCount W0 := by rw [hV]; exact Nat.zero_lt_one
  have hmem : (⟨0, h0⟩ : Fin (vertexCount W0)) ∈ M.verts :=
    hsat (show (0 : ℕ) < leftCount W0 by rw [hn]; exact Nat.zero_lt_one)
  obtain ⟨w, hw, -⟩ := hM hmem
  apply (M.adj_sub hw).ne
  have : (w : ℕ) < 1 := w.isLt
  exact Fin.ext (show (0 : ℕ) = w by omega)

/-- **The cited decider, after the guarded conversion, computes `gfun` on every word.** -/
theorem saturatingAnswer_conv (x : List ℕ) : saturatingAnswer (conv x) = gfun x := by
  unfold conv gfun
  by_cases hH : Heavy x
  · rw [if_pos hH, if_pos hH]
    exact saturatingAnswer_csrOf x
  · rw [if_neg hH, if_neg hH]
    by_cases h0 : x.getD 0 0 = 0
    · rw [if_pos h0, if_pos h0]
      exact saturatingAnswer_W1
    · rw [if_neg h0, if_neg h0]
      exact saturatingAnswer_W0

end Lax117284Proofs.Machine.MatchWord
