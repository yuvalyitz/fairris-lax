import Lax117284.BipartiteDecision
import Lax117284Proofs.Bipartite.Ram2.SymmMath
import Lax117284Proofs.Bipartite.Ram2.Bridge
import Lax117284Proofs.Bipartite.Machine

/-!
The symmetrized word `sx x` of a word `x`: the same header, the offsets `offS`, the target
array `tgtS` (the left rows are the unions of each left row of `x` and the transposed right
rows; the right rows are empty), and the same last entry. On a well-formed word it is `Good`,
its adjacency across the split is that of `wordGraph x`, and so the size of Kuhn's matching of
it is `n` exactly when `wordGraph x` has a matching saturating its left side. Every word encoding
a bipartite graph is well formed (`wellFormed_of_encodes`).
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax271696.GraphEncoding Lax117284.BipartiteGraph Lax117284.BipartiteDecision Lax117284.BipartiteKuhn
open Lax117284Proofs.Bipartite.Matching Lax117284.BipartiteMatching Lax808846Proofs.Reasoning
open scoped Classical

theorem getD_app_left {a b : List ℕ} {s : ℕ} (h : s < a.length) :
    (a ++ b).getD s 0 = a.getD s 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_right {a b : List ℕ} {s : ℕ} (h : a.length ≤ s) :
    (a ++ b).getD s 0 = b.getD (s - a.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_cons2 (a b : ℕ) (l : List ℕ) (i : ℕ) :
    (a :: b :: l).getD (2 + i) 0 = l.getD i 0 := by
  rw [show 2 + i = i + 1 + 1 by omega]
  rfl

/-- **The symmetrized word.** -/
def sx (x : List ℕ) : List ℕ :=
  Vw x :: x.getD 1 0 :: (arrOf (Vw x + 1) (offS x) ++ (arrOf (offS x (nw x)) (tgtS x) ++ [nw x]))

section Facts

variable {x : List ℕ}

theorem nw_eq_leftCount (x : List ℕ) : nw x = leftCount x := nw_eq_getLastD x

theorem length_sx (x : List ℕ) : (sx x).length = 4 + Vw x + offS x (nw x) := by
  simp [sx]; omega


theorem sx_one (x : List ℕ) : (sx x).getD 1 0 = x.getD 1 0 := rfl

theorem sx_off (x : List ℕ) {i : ℕ} (hi : i ≤ Vw x) : (sx x).getD (2 + i) 0 = offS x i := by
  unfold sx
  rw [getD_cons2, getD_app_left (by simp; omega), getD_arrOf _ (by omega)]

theorem sx_tgt (x : List ℕ) {s : ℕ} (hs : s < offS x (nw x)) :
    (sx x).getD (3 + Vw x + s) 0 = tgtS x s := by
  unfold sx
  rw [show 3 + Vw x + s = 2 + (Vw x + 1 + s) by omega, getD_cons2,
    getD_app_right (by simp), length_arrOf, Nat.add_sub_cancel_left, getD_app_left (by simpa),
    getD_arrOf _ hs]

theorem sx_last (x : List ℕ) : (sx x).getD (3 + Vw x + offS x (nw x)) 0 = nw x := by
  unfold sx
  rw [show 3 + Vw x + offS x (nw x) = 2 + (Vw x + 1 + offS x (nw x)) by omega, getD_cons2,
    getD_app_right (by simp), length_arrOf, Nat.add_sub_cancel_left,
    getD_app_right (by simp), length_arrOf, Nat.sub_self]
  rfl

theorem Vw_sx (x : List ℕ) : Vw (sx x) = Vw x := rfl

theorem nw_sx (x : List ℕ) : nw (sx x) = nw x := by
  unfold nw
  rw [length_sx, show 4 + Vw x + offS x (nw x) - 1 = 3 + Vw x + offS x (nw x) by omega]
  exact sx_last x

theorem offw_sx (x : List ℕ) {i : ℕ} (hi : i ≤ Vw x) : offw (sx x) i = offS x i := sx_off x hi

theorem tgtw_sx (x : List ℕ) {s : ℕ} (hs : s < offS x (nw x)) : tgtw (sx x) s = tgtS x s := by
  unfold tgtw; rw [Vw_sx]; exact sx_tgt x hs

/-! ### Well-formed words -/

theorem wf_nV (hw : WellFormed x) : nw x ≤ Vw x := by
  rw [nw_eq_leftCount]; exact hw.left_le

theorem wf_nV' (hw : WellFormed x) : nw x ≤ vertexCount x := wf_nV hw

theorem wf_len (hw : WellFormed x) : x.length = 4 + Vw x + 2 * x.getD 1 0 := hw.length_eq

theorem wf_off0 (hw : WellFormed x) : offw x 0 = 0 := hw.offset_zero

theorem wf_offV (hw : WellFormed x) : offw x (Vw x) = 2 * x.getD 1 0 := hw.offset_last

theorem wf_mono (hw : WellFormed x) : ∀ i < Vw x, offw x i ≤ offw x (i + 1) :=
  hw.offset_mono

theorem wf_tgt_lt (hw : WellFormed x) : ∀ s < 2 * x.getD 1 0, tgtw x s < Vw x :=
  hw.target_lt

theorem wf_cross (hw : WellFormed x) {u j : ℕ} (hu : u < Vw x) (h1 : offw x u ≤ j)
    (h2 : j < offw x (u + 1)) : (u < nw x ↔ nw x ≤ tgtw x j) := by
  rw [nw_eq_leftCount]; exact hw.crosses u hu j h1 h2

theorem wf_off_le (hw : WellFormed x) {i : ℕ} (hi : i ≤ Vw x) :
    offw x i ≤ 2 * x.getD 1 0 := by
  rw [← (wf_offV hw)]; exact mono_chain (offw x) (Vw x) (wf_mono hw) i hi

/-- Every slot of a well-formed word has a left destination. -/
theorem wf_dest_lt (hw : WellFormed x) {p : ℕ × ℕ} (hp : p ∈ allPairs x) :
    dest x p < nw x := by
  obtain ⟨h1, h2, h3⟩ := (mem_allPairs x).1 hp
  unfold dest
  split_ifs with h
  · exact h
  · have := (wf_cross hw) h1 h2 h3
    omega

theorem wf_length_allPairs (hw : WellFormed x) :
    (allPairs x).length = 2 * x.getD 1 0 := by
  unfold allPairs
  rw [length_pairsUpto x (wf_off0 hw) (wf_mono hw) _ le_rfl, (wf_offV hw)]

theorem wf_offS_n (hw : WellFormed x) : offS x (nw x) = 2 * x.getD 1 0 := by
  rw [sum_deg_eq x (fun p hp => (wf_dest_lt hw) hp), (wf_length_allPairs hw)]

theorem wf_length_sx (hw : WellFormed x) : (sx x).length = x.length := by
  rw [Ram2.length_sx, (wf_offS_n hw), (wf_len hw)]

/-- Every value of a slot is a vertex. -/
theorem wf_val_lt (hw : WellFormed x) {p : ℕ × ℕ} (hp : p ∈ allPairs x) :
    val x p < Vw x := by
  obtain ⟨h1, h2, h3⟩ := (mem_allPairs x).1 hp
  unfold val
  split_ifs with h
  · exact (wf_tgt_lt hw) _ (lt_of_lt_of_le h3 ((wf_off_le hw) h1))
  · exact h1

/-- The value of a slot destined to a left vertex is a right vertex. -/
theorem wf_val_ge (hw : WellFormed x) {p : ℕ × ℕ} (hp : p ∈ allPairs x) :
    nw x ≤ val x p := by
  obtain ⟨h1, h2, h3⟩ := (mem_allPairs x).1 hp
  unfold val
  split_ifs with h
  · exact ((wf_cross hw) h1 h2 h3).1 h
  · omega

/-- **The symmetrized word of a well-formed word is `Good`.** -/
theorem wf_good_sx (hw : WellFormed x) : Good (sx x) := by
  have hV := Vw_sx x
  have hn := nw_sx x
  have hoffV : offw (sx x) (Vw x) = offS x (nw x) := by
    rw [offw_sx x le_rfl, offS_of_ge x (wf_nV hw)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hV, hn]; exact (wf_nV hw)
  · intro i hi
    rw [hV] at hi
    rw [offw_sx x (by omega), offw_sx x (by omega)]
    exact offS_succ_le x i
  · rw [hV, hoffV, Ram2.length_sx]
  · rw [hV, hoffV, sx_one, (wf_offS_n hw)]
  · intro s hs
    rw [hV, hoffV] at hs
    rw [hV, tgtw_sx x hs]
    have hmem : tgtS x s ∈ segs x := by
      unfold tgtS
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [length_segs]; exact hs)]
      exact List.getElem_mem _
    obtain ⟨p, hp, -, hv⟩ := mem_segs x hmem
    rw [← hv]; exact (wf_val_lt hw) hp
  · intro l hl s hs1 hs2
    rw [hn] at hl ⊢
    rw [offw_sx x (by have := (wf_nV hw); omega)] at hs1
    rw [offw_sx x (by have := (wf_nV hw); omega), offS_succ_of_lt x hl] at hs2
    obtain ⟨k, rfl⟩ : ∃ k, s = offS x l + k := ⟨s - offS x l, by omega⟩
    have hk : k < deg x l := by omega
    have hsn : offS x l + k < offS x (nw x) := by
      have := offS_mono x (i := l + 1) (i' := nw x) hl
      rw [offS_succ_of_lt x hl] at this
      omega
    rw [tgtw_sx x hsn, tgtS_seg x hl hk]
    have hmem : (seg x l (allPairs x)).getD k 0 ∈ seg x l (allPairs x) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact List.getElem_mem _
    obtain ⟨p, hp, -, hv⟩ := (mem_seg x).1 hmem
    rw [← hv]; exact (wf_val_ge hw) hp

/-- **The adjacency across the split of the symmetrized word is the symmetric closure of the
lists.** -/
theorem adjw_sx {l j : ℕ} (hl : l < nw x) (hj : j < Vw x - nw x) :
    adjw (sx x) l j ↔ Lists x l (nw x + j) ∨ Lists x (nw x + j) l := by
  have hV : nw x ≤ Vw x := by omega
  unfold adjw adjOff
  rw [nw_sx, offw_sx x (by omega), offw_sx x (by omega), offS_succ_of_lt x hl]
  have hsn : ∀ k < deg x l, offS x l + k < offS x (nw x) := fun k hk => by
    have := offS_mono x (i := l + 1) (i' := nw x) hl
    rw [offS_succ_of_lt x hl] at this
    omega
  have hmem : (∃ s, offS x l ≤ s ∧ s < offS x l + deg x l ∧ tgtw (sx x) s = nw x + j) ↔
      nw x + j ∈ seg x l (allPairs x) := by
    constructor
    · rintro ⟨s, h1, h2, h3⟩
      obtain ⟨k, rfl⟩ : ∃ k, s = offS x l + k := ⟨s - offS x l, by omega⟩
      have hk : k < deg x l := by omega
      rw [tgtw_sx x (hsn k hk), tgtS_seg x hl hk] at h3
      rw [← h3, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact List.getElem_mem _
    · intro h
      obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.1 h
      refine ⟨offS x l + k, by omega, by unfold deg at *; omega, ?_⟩
      rw [tgtw_sx x (hsn k hk), tgtS_seg x hl hk, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hk]
      exact hkv
  rw [hmem, mem_seg]
  constructor
  · rintro ⟨⟨u, j'⟩, hp, hd, hv⟩
    obtain ⟨h1, h2, h3⟩ := (mem_allPairs x).1 hp
    simp only at h1 h2 h3
    unfold dest at hd
    unfold val at hv
    simp only at hd hv
    by_cases hu : u < nw x
    · rw [if_pos hu] at hd hv
      subst hd
      exact Or.inl ⟨j', h2, h3, hv⟩
    · rw [if_neg hu] at hd hv
      subst hv
      exact Or.inr ⟨j', h2, h3, hd⟩
  · rintro (⟨j', h1, h2, h3⟩ | ⟨j', h1, h2, h3⟩)
    · refine ⟨(l, j'), (mem_allPairs x).2 ⟨by simp; omega, h1, h2⟩, ?_, ?_⟩
      · unfold dest; simp [hl]
      · unfold val; simp [hl]; exact h3
    · refine ⟨(nw x + j, j'), (mem_allPairs x).2 ⟨by simp; omega, h1, h2⟩, ?_, ?_⟩
      · unfold dest; simp; exact h3
      · unfold val; simp

end Facts

/-! ### The bridge to Mathlib -/

section Bridge

variable {x : List ℕ}

theorem wordGraph_adj_iff {u v : Fin (vertexCount x)} :
    (wordGraph x).Adj u v ↔ u ≠ v ∧ (Lists x u v ∨ Lists x v u) := by
  unfold wordGraph
  rw [SimpleGraph.fromRel_adj]

/-- **A well-formed word's graph is split at its last entry.** -/
theorem wf_splitAt (hw : WellFormed x) : SplitAt (wordGraph x) (leftCount x) := by
  have hcross : ∀ u v : Fin (vertexCount x), Lists x u v →
      ((u : ℕ) < leftCount x ↔ leftCount x ≤ (v : ℕ)) := by
    rintro u v ⟨j, h1, h2, h3⟩
    rw [← h3]
    exact hw.crosses u u.2 j h1 h2
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    intro v h1 h2
    have : (v : ℕ) < leftCount x := h1
    have : leftCount x ≤ (v : ℕ) := h2
    omega
  · intro u v hadj
    obtain ⟨-, h | h⟩ := wordGraph_adj_iff.1 hadj
    · have := hcross u v h
      by_cases hu : (u : ℕ) < leftCount x
      · exact Or.inl ⟨hu, this.1 hu⟩
      · right
        refine ⟨Nat.le_of_not_lt hu, ?_⟩
        show (v : ℕ) < leftCount x
        by_contra hv
        exact hu (this.2 (Nat.le_of_not_lt hv))
    · have := hcross v u h
      by_cases hv : (v : ℕ) < leftCount x
      · exact Or.inr ⟨this.1 hv, hv⟩
      · left
        refine ⟨?_, Nat.le_of_not_lt hv⟩
        show (u : ℕ) < leftCount x
        by_contra hu
        exact hv (this.2 (Nat.le_of_not_lt hu))

theorem kuhnSize_eq_of {x' : List ℕ} {n m : ℕ} (hn : nw x' = n) (hm : mw x' = m) :
    kuhnSize x' = size (kuhn (adjF (adjw x') n m)) := by
  subst hn; subst hm; rfl

/-- The adjacency of the symmetrized word is the relation of Kuhn's algorithm on the graph. -/
theorem adjF_sx (hw : WellFormed x) :
    adjF (adjw (sx x)) (nw x) (vertexCount x - nw x) =
      Lax117284.BipartiteKuhnCorrect.leftRel (wordGraph x) (nw x) (wf_nV' hw) := by
  funext i j
  apply propext
  unfold adjF Lax117284.BipartiteKuhnCorrect.leftRel
  rw [adjw_sx i.2 j.2, wordGraph_adj_iff]
  constructor
  · intro h
    refine ⟨?_, h⟩
    intro he
    have := congrArg Fin.val he
    simp at this
    have := i.2
    omega
  · exact fun h => h.2

/-- **Kuhn's matching of the symmetrized word saturates the left side exactly when the graph
has a matching saturating its left side.** -/
theorem kuhnSize_sx_iff (hw : WellFormed x) :
    kuhnSize (sx x) = nw x ↔ ∃ M : (wordGraph x).Subgraph, M.IsMatching ∧
      Saturates (wordGraph x) M (leftSide (vertexCount x) (leftCount x)) := by
  have hn := nw_eq_leftCount x
  have hmw : mw (sx x) = vertexCount x - nw x := by unfold mw; rw [Vw_sx, nw_sx]; rfl
  rw [kuhnSize_eq_of (nw_sx x) hmw, adjF_sx hw,
    Lax117284Proofs.Bipartite.GraphBridge.kuhn_matchingNumber (wordGraph x) (nw x) (wf_nV' hw)
      (by rw [hn]; exact (wf_splitAt hw))]
  rw [hn]
  exact (Lax117284Proofs.Bipartite.GraphBridge.exists_saturating_iff (wordGraph x) (leftCount x)
    hw.left_le (wf_splitAt hw)).symm

/-- **Every word encoding a bipartite graph is well formed.** -/
theorem wellFormed_of_encodes {V : ℕ} {G : SimpleGraph (Fin V)} {n : ℕ}
    (h : EncodesBipartite x V G n) : WellFormed x := by
  have hg := good_of_encodes h
  have hlc := leftCount_eq h
  have hV : vertexCount x = V := vertexCount_eq h
  obtain ⟨g, hx, hge, hnV, hs⟩ := h
  have hE : x.getD 1 0 = edgeCount g := edge_eq' hx hge
  have hoffV : offw x V = 2 * edgeCount g := by rw [offw_eq' hx hge le_rfl]; exact hge.offset_last
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlc, hV]; exact hnV
  · show x.length = 4 + vertexCount x + 2 * x.getD 1 0
    rw [hV, hE]; exact len_eq' hx hge
  · show offw x 0 = 0
    rw [offw_eq' hx hge (by omega)]; exact hge.offset_zero
  · show offw x (vertexCount x) = 2 * x.getD 1 0
    rw [hV, hE]; exact hoffV
  · intro i hi
    rw [hV] at hi
    show offw x i ≤ offw x (i + 1)
    rw [offw_eq' hx hge (by omega), offw_eq' hx hge (by omega)]
    exact hge.offset_mono i hi
  · intro s hs
    change s < 2 * x.getD 1 0 at hs
    rw [hE] at hs
    show tgtw x s < vertexCount x
    rw [hV, tgtw_eq' hx hge hs]
    exact hge.target_lt s hs
  · intro u hu j h1 h2
    rw [hV] at hu
    rw [hlc]
    change offw x u ≤ j at h1
    change j < offw x (u + 1) at h2
    rw [offw_eq' hx hge (by omega)] at h1
    rw [offw_eq' hx hge (by omega)] at h2
    have hs2E : j < 2 * edgeCount g := slot_lt' hge hu h2
    show u < n ↔ n ≤ tgtw x j
    rw [tgtw_eq' hx hge hs2E]
    have ht : target g j < V := hge.target_lt j hs2E
    have hadj : G.Adj ⟨u, hu⟩ ⟨target g j, ht⟩ := (hge.adj_iff _ _).2 ⟨j, h1, h2, rfl⟩
    rcases hs.mem_of_adj hadj with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact ⟨fun _ => hr, fun _ => hl⟩
    · have h1' : n ≤ u := hl
      have h2' : target g j < n := hr
      exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

end Bridge

end Lax117284Proofs.Bipartite.Ram2
