import Lax117284Proofs.Bipartite.Ram2.Word
import Lax117284.BipartiteDecision
import Lax117284Proofs.Bipartite.Ram2.Bridge
import Lax117284Proofs.Bipartite.Machine
import Lax117284Proofs.Bipartite.Ram2.Wrap

/-! ### `Lax117284Proofs.Bipartite.Ram2.SymmMath` -/

section
/-!
The mathematics of the symmetrizer: the slots of a word as pairs `(u, j)` in the order the
program visits them, the *destination* of a slot (the left vertex whose row of the symmetrized
word receives it: `u` itself for a left row, the target for a right row) and its *value* (the
target for a left row, `u` for a right row), the segments `seg l P` of values destined to `l`
among the slots `P` visited so far, the degrees `deg l` and offsets `offS i` of the symmetrized
word, and its target array `tgtS`.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open scoped Classical

section Pairs

variable (x : List ℕ)

/-- The slots of row `u`, as pairs `(u, j)`. -/
def rowPairs (u : ℕ) : List (ℕ × ℕ) :=
  (List.range (offw x (u + 1) - offw x u)).map (fun k => (u, offw x u + k))

/-- The slots of the rows below `u`. -/
def pairsUpto (u : ℕ) : List (ℕ × ℕ) := (List.range u).flatMap (rowPairs x)

/-- The slots of the rows below `u`, then the slots of row `u` below `j`. -/
def pairsAt (u j : ℕ) : List (ℕ × ℕ) :=
  pairsUpto x u ++ (List.range (j - offw x u)).map (fun k => (u, offw x u + k))

/-- All slots. -/
def allPairs : List (ℕ × ℕ) := pairsUpto x (Vw x)

theorem pairsUpto_succ (u : ℕ) : pairsUpto x (u + 1) = pairsUpto x u ++ rowPairs x u := by
  unfold pairsUpto
  rw [List.range_succ, List.flatMap_append]
  simp

theorem pairsAt_start (u : ℕ) : pairsAt x u (offw x u) = pairsUpto x u := by
  simp [pairsAt]

theorem pairsAt_succ {u j : ℕ} (h1 : offw x u ≤ j) :
    pairsAt x u (j + 1) = pairsAt x u j ++ [(u, j)] := by
  unfold pairsAt
  rw [show j + 1 - offw x u = (j - offw x u) + 1 by omega, List.range_succ, List.map_append,
    List.append_assoc]
  simp only [List.map_cons, List.map_nil]
  rw [Nat.add_sub_cancel' h1]

theorem pairsAt_end (u : ℕ) : pairsAt x u (offw x (u + 1)) = pairsUpto x (u + 1) := by
  rw [pairsUpto_succ]; rfl

theorem mem_rowPairs {u : ℕ} {p : ℕ × ℕ} :
    p ∈ rowPairs x u ↔ p.1 = u ∧ offw x u ≤ p.2 ∧ p.2 < offw x (u + 1) := by
  unfold rowPairs
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨rfl, by simp, by simp; omega⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨p.2 - offw x u, by omega, ?_⟩
    obtain ⟨a, b⟩ := p
    simp only at h1 h2 h3
    subst h1
    congr 1
    omega

theorem mem_pairsUpto {u : ℕ} {p : ℕ × ℕ} :
    p ∈ pairsUpto x u ↔ p.1 < u ∧ offw x p.1 ≤ p.2 ∧ p.2 < offw x (p.1 + 1) := by
  unfold pairsUpto
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨u', hu', hp⟩
    obtain ⟨rfl, h2, h3⟩ := (mem_rowPairs x).1 hp
    exact ⟨hu', h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨p.1, h1, (mem_rowPairs x).2 ⟨rfl, h2, h3⟩⟩

theorem mem_allPairs {p : ℕ × ℕ} :
    p ∈ allPairs x ↔ p.1 < Vw x ∧ offw x p.1 ≤ p.2 ∧ p.2 < offw x (p.1 + 1) :=
  mem_pairsUpto x

theorem length_rowPairs (u : ℕ) : (rowPairs x u).length = offw x (u + 1) - offw x u := by
  simp [rowPairs]

/-- The number of slots of the rows below `u` is `off u` when the offsets are nondecreasing
from `0`. -/
theorem length_pairsUpto (h0 : offw x 0 = 0) (hmono : ∀ i < Vw x, offw x i ≤ offw x (i + 1)) :
    ∀ u ≤ Vw x, (pairsUpto x u).length = offw x u := by
  intro u
  induction u with
  | zero => intro _; simp [pairsUpto, h0]
  | succ u ih =>
    intro hu
    rw [pairsUpto_succ, List.length_append, ih (by omega), length_rowPairs]
    have := hmono u (by omega)
    omega

theorem range_prefix {a b : ℕ} (h : a ≤ b) : ∃ l, List.range b = List.range a ++ l := by
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
  exact ⟨_, List.range_add⟩

theorem pairsUpto_prefix {u u' : ℕ} (h : u ≤ u') : ∃ Q, pairsUpto x u' = pairsUpto x u ++ Q := by
  have key : ∀ k, ∃ Q, pairsUpto x (u + k) = pairsUpto x u ++ Q := by
    intro k
    induction k with
    | zero => exact ⟨[], by simp⟩
    | succ k ih =>
      obtain ⟨Q, hQ⟩ := ih
      rw [← Nat.add_assoc, pairsUpto_succ, hQ, List.append_assoc]
      exact ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ := key (u' - u)
  rw [Nat.add_sub_cancel' h] at hQ
  exact ⟨Q, hQ⟩

/-- Every slot of `pairsAt u j` is a slot of the word: `pairsAt u j` is a prefix of all the
slots. -/
theorem pairsAt_prefix (u j : ℕ) (hu : u < Vw x) (hj : j ≤ offw x (u + 1)) :
    ∃ Q, allPairs x = pairsAt x u j ++ Q := by
  obtain ⟨Q₁, hQ₁⟩ := pairsUpto_prefix x (u := u + 1) (u' := Vw x) hu
  obtain ⟨l, hl⟩ := range_prefix (a := j - offw x u) (b := offw x (u + 1) - offw x u) (by omega)
  refine ⟨l.map (fun k => (u, offw x u + k)) ++ Q₁, ?_⟩
  unfold allPairs
  rw [hQ₁, pairsUpto_succ]
  unfold rowPairs pairsAt
  rw [hl, List.map_append]
  simp only [List.append_assoc]

end Pairs


/-! ### Destinations, values, segments -/

section Seg

variable (x : List ℕ)

/-- The left vertex whose row of the symmetrized word receives a slot: the row itself for a
left row, the target for a right row. -/
def dest (p : ℕ × ℕ) : ℕ := if p.1 < nw x then p.1 else tgtw x p.2

/-- The value a slot contributes: the target for a left row, the row for a right row. -/
def val (p : ℕ × ℕ) : ℕ := if p.1 < nw x then tgtw x p.2 else p.1

/-- The values destined to `l` among the slots `P`, in order. -/
def seg (l : ℕ) (P : List (ℕ × ℕ)) : List ℕ :=
  (P.filter (fun p => dest x p = l)).map (val x)

theorem seg_nil (l : ℕ) : seg x l [] = [] := rfl

theorem seg_append (l : ℕ) (P Q : List (ℕ × ℕ)) : seg x l (P ++ Q) = seg x l P ++ seg x l Q := by
  unfold seg
  rw [List.filter_append, List.map_append]

theorem seg_single (l : ℕ) (p : ℕ × ℕ) :
    seg x l [p] = if dest x p = l then [val x p] else [] := by
  unfold seg
  by_cases h : dest x p = l <;> simp [h]

theorem mem_seg {l : ℕ} {P : List (ℕ × ℕ)} {v : ℕ} :
    v ∈ seg x l P ↔ ∃ p ∈ P, dest x p = l ∧ val x p = v := by
  unfold seg
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨p, ⟨hp, hd⟩, rfl⟩; exact ⟨p, hp, hd, rfl⟩
  · rintro ⟨p, hp, hd, rfl⟩; exact ⟨p, ⟨hp, hd⟩, rfl⟩

/-- The degree of `l` in the symmetrized word. -/
def deg (l : ℕ) : ℕ := (seg x l (allPairs x)).length

/-- A prefix of the slots gives a prefix of every segment. -/
theorem seg_prefix {l : ℕ} {P Q : List (ℕ × ℕ)} (h : allPairs x = P ++ Q) :
    ∃ R, seg x l (allPairs x) = seg x l P ++ R := by
  rw [h, seg_append]; exact ⟨_, rfl⟩

theorem length_seg_le {l : ℕ} {P Q : List (ℕ × ℕ)} (h : allPairs x = P ++ Q) :
    (seg x l P).length ≤ deg x l := by
  obtain ⟨R, hR⟩ := seg_prefix x (l := l) h
  unfold deg; rw [hR, List.length_append]; omega

/-- The offset of row `i` in the symmetrized word: the degrees of the left vertices below `i`
(the right rows are empty). -/
def offS (i : ℕ) : ℕ := ∑ l ∈ Finset.range (min i (nw x)), deg x l

theorem offS_zero : offS x 0 = 0 := by simp [offS]

theorem offS_succ_of_lt {i : ℕ} (hi : i < nw x) : offS x (i + 1) = offS x i + deg x i := by
  unfold offS
  rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega), Finset.sum_range_succ]

theorem offS_of_ge {i : ℕ} (hi : nw x ≤ i) : offS x i = offS x (nw x) := by
  unfold offS
  rw [Nat.min_eq_right hi, Nat.min_self]

theorem offS_succ_le (i : ℕ) : offS x i ≤ offS x (i + 1) := by
  rcases Nat.lt_or_ge i (nw x) with h | h
  · rw [offS_succ_of_lt x h]; omega
  · rw [offS_of_ge x h, offS_of_ge x (i := i + 1) (by omega)]

theorem offS_mono {i i' : ℕ} (h : i ≤ i') : offS x i ≤ offS x i' := by
  obtain ⟨k, rfl⟩ : ∃ k, i' = i + k := ⟨i' - i, by omega⟩
  clear h
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans (by rw [← Nat.add_assoc]; exact offS_succ_le x _)

/-- The segments of all left vertices, end to end: the target array of the symmetrized word. -/
def segs : List ℕ := (List.range (nw x)).flatMap (fun l => seg x l (allPairs x))

/-- The target at slot `s` of the symmetrized word. -/
def tgtS (s : ℕ) : ℕ := (segs x).getD s 0

theorem length_segs_upto : ∀ i ≤ nw x,
    ((List.range i).flatMap (fun l => seg x l (allPairs x))).length = offS x i := by
  intro i
  induction i with
  | zero => intro _; simp [offS_zero]
  | succ i ih =>
    intro hi
    rw [List.range_succ, List.flatMap_append, List.length_append, ih (by omega),
      offS_succ_of_lt x (by omega)]
    simp [deg]

theorem length_segs : (segs x).length = offS x (nw x) := length_segs_upto x _ le_rfl

/-- The target at `offS l + k` is entry `k` of the segment of `l`. -/
theorem tgtS_seg {l k : ℕ} (hl : l < nw x) (hk : k < deg x l) :
    tgtS x (offS x l + k) = (seg x l (allPairs x)).getD k 0 := by
  unfold tgtS segs
  obtain ⟨R, hR⟩ : ∃ R, List.range (nw x) = List.range (l + 1) ++ R := range_prefix hl
  rw [hR, List.flatMap_append, List.range_succ, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hlen := length_segs_upto x l (by omega)
  rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen,
    Nat.add_sub_cancel_left, List.getElem?_append_left (by simpa [deg] using hk)]
  rfl

theorem mem_segs {v : ℕ} (h : v ∈ segs x) : ∃ p ∈ allPairs x, dest x p < nw x ∧ val x p = v := by
  unfold segs at h
  obtain ⟨l, hl, hv⟩ := List.mem_flatMap.1 h
  obtain ⟨p, hp, hd, rfl⟩ := (mem_seg x).1 hv
  exact ⟨p, hp, by rw [hd]; exact List.mem_range.1 hl, rfl⟩

/-- **The degrees of the left vertices sum to the number of slots** when every slot has a left
destination. -/
theorem sum_deg_eq (hd : ∀ p ∈ allPairs x, dest x p < nw x) :
    offS x (nw x) = (allPairs x).length := by
  have key : ∀ P : List (ℕ × ℕ), (∀ p ∈ P, dest x p < nw x) →
      ∑ l ∈ Finset.range (nw x), (seg x l P).length = P.length := by
    intro P
    induction P using List.reverseRecOn with
    | nil => intro _; simp [seg_nil]
    | append_singleton P p ih =>
      intro hP
      have h1 := ih (fun q hq => hP q (List.mem_append_left _ hq))
      have h2 := hP p (List.mem_append_right _ (List.mem_singleton_self p))
      simp only [seg_append, seg_single, List.length_append, Finset.sum_add_distrib, h1,
        List.length_append, List.length_singleton]
      congr 1
      have : ∀ l, (if dest x p = l then [val x p] else []).length = if l = dest x p then 1 else 0 := by
        intro l
        by_cases h : dest x p = l
        · subst h; simp
        · rw [if_neg h, if_neg (Ne.symm h)]; rfl
      simp only [this]
      rw [Finset.sum_ite_eq' (Finset.range (nw x)) (dest x p) (fun _ => 1)]
      rw [if_pos (Finset.mem_range.2 h2)]
  unfold offS
  rw [Nat.min_self]
  exact key _ hd

end Seg

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.SymmWord` -/

section
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


end Bridge

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.Validate` -/

section
/-!
The validator: the word is read into `t`, its header into `V`, `E`, `n`, and the syntactic
conditions of `WellFormed` other than `crosses` are checked in linear time, a flag `ok` (`1` or
`0`) recording the verdict: `n ≤ V`, the length `4 + V + 2E`, the first offset `0`, the last
offset `2E`, nondecreasing offsets, every target a vertex. The checks are ordered so that every
array read of a later check is in range once the earlier ones passed; a failed check clears the
flag and the later checks are skipped. `WF3 x` names what the flag certifies.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteDecision
open scoped Classical

variable {B : ℕ}

/-! ### The word in `t` -/

/-- The word is in the array `t`. -/
def TabOK (x : List ℕ) (σ : Env) : Prop := σ.arrs "t" = arrOf x.length (fun i => x.getD i 0)

theorem TabOK.length {x : List ℕ} {σ : Env} (h : TabOK x σ) : (σ.arrs "t").length = x.length := by
  rw [h]; simp

theorem TabOK.getD {x : List ℕ} {σ : Env} (h : TabOK x σ) {i : ℕ} (hi : i < x.length) :
    (σ.arrs "t").getD i 0 = x.getD i 0 := by rw [h]; exact getD_arrOf _ hi

theorem TabOK.congr {x : List ℕ} {σ σ' : Env} (h : TabOK x σ) (ha : σ'.arrs "t" = σ.arrs "t") :
    TabOK x σ' := by unfold TabOK; rw [ha]; exact h

theorem getD_lt_of_mem {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hB : 0 < B) (i : ℕ) :
    x.getD i 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : x[i]? with _ | v
  · exact hB
  · exact hx v (List.mem_of_getElem? h)

/-- One entry: read it, store it, advance. -/
def readTBody : Com :=
  .seq (.read "v")
    (.seq (.store "t" (.var "rt") (.var "v")) (.assign "rt" (.add (.var "rt") (.lit 1))))

/-- Read the whole word into `t`. -/
def readT : Com :=
  .seq (.assign "rt" (.lit 0)) (.while (.lt (.var "rt") (.var "len")) readTBody)

/-- Invariant of the read: `rt` entries consumed and stored. -/
def ReadTInv (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "len" = x.length ∧ σ.vars "rt" ≤ x.length ∧ σ.inp = x.drop (σ.vars "rt") ∧
    σ.arrs "t" = arrOf x.length (fun i => if i < σ.vars "rt" then x.getD i 0 else 0)

theorem readTBody_spec {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hlB : x.length < B) :
    Spec B (fun σ => ReadTInv x σ ∧ σ.vars "rt" < x.length) readTBody
      (fun σ σ' => ReadTInv x σ' ∧ σ'.vars "rt" = σ.vars "rt" + 1) 10 := by
  rintro σ ⟨⟨hl, hrt, hinp, ha⟩, hlt⟩
  have hlen : (σ.arrs "t").length = x.length := by rw [ha]; simp
  have hdrop : σ.inp = x[σ.vars "rt"]'hlt :: x.drop (σ.vars "rt" + 1) := by
    rw [hinp, List.drop_eq_getElem_cons hlt]
  have hgetE : x[σ.vars "rt"]?.getD 0 = x[σ.vars "rt"]'hlt := by
    rw [List.getElem?_eq_getElem hlt]; rfl
  have htail : σ.inp.tail = x.drop (σ.vars "rt" + 1) := by rw [hdrop]; rfl
  have hne : σ.inp ≠ [] := by rw [hdrop]; exact List.cons_ne_nil _ _
  have hhead' : σ.inp.head?.getD 0 = x[σ.vars "rt"]'hlt := by rw [hdrop]; rfl
  have hv' : σ.inp.head?.getD 0 < B := by rw [hhead']; exact hx _ (List.getElem_mem hlt)
  have hhead : σ.inp.headD 0 = x[σ.vars "rt"]'hlt := by rw [hdrop]; rfl
  have hv : σ.inp.headD 0 < B := by rw [hhead]; exact hx _ (List.getElem_mem hlt)
  unfold readTBody
  run_vcg
  all_goals (simp [ReadTInv, hl, htail]; try omega)
  refine ⟨hlt, ?_⟩
  rw [ha, set_arrOf]
  refine arrOf_congr (fun k _ => ?_)
  by_cases hk : k = σ.vars "rt"
  · subst hk; simp [hhead', hgetE]
  · simp only [hk, if_false]
    split_ifs <;> first | rfl | omega

/-- **The read leaves the word in `t`.** -/
theorem readT_spec {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hlB : x.length < B) :
    Spec B (fun σ => σ.vars "len" = x.length ∧ σ.inp = x ∧
        σ.arrs "t" = arrOf x.length (fun _ => 0))
      readT (fun _ σ' => σ'.inp = [] ∧ TabOK x σ' ∧ σ'.vars "len" = x.length)
      ((10 + 4) * x.length + 6) := by
  have hloop := Spec.forRangeZero (B := B) (c := readTBody) "rt" "len" (ReadTInv x) x.length 10
    hlB (fun σ hσ => hσ.2.1) (fun σ hσ => hσ.1) (readTBody_spec hx hlB)
  refine hloop.conseq ?_ ?_ le_rfl
  · rintro σ ⟨hl, hinp, ha⟩
    refine ⟨by simpa using hl, by simp, by simpa using hinp, ?_⟩
    simpa using ha
  · rintro σ σ' _ ⟨⟨hl, -, hinp, ha⟩, hrt⟩
    rw [hrt] at hinp ha
    refine ⟨?_, ?_, hl⟩
    · rw [hinp]; exact List.drop_eq_nil_of_le le_rfl
    · unfold TabOK
      rw [ha]
      exact arrOf_congr (fun k hk => by simp [hk])

/-! ### The header and the facts the validator establishes -/

/-- The scalars of the header, in place, and the word in `t`. -/
structure Base (x : List ℕ) (σ : Env) : Prop where
  tab : TabOK x σ
  len : σ.vars "len" = x.length
  V : σ.vars "V" = Vw x
  E : σ.vars "E" = x.getD 1 0
  n : σ.vars "n" = nw x

theorem Base.setVar {x : List ℕ} {σ : Env} (h : Base x σ) (y : String)
    (hy : y ∉ ["len", "V", "E", "n"]) (v : ℕ) : Base x (σ.setVar y v) := by
  refine ⟨h.tab.congr rfl, ?_, ?_, ?_, ?_⟩
  · simp only [vars_setVar]; rw [if_neg (by rintro rfl; simp at hy)]; exact h.len
  · simp only [vars_setVar]; rw [if_neg (by rintro rfl; simp at hy)]; exact h.V
  · simp only [vars_setVar]; rw [if_neg (by rintro rfl; simp at hy)]; exact h.E
  · simp only [vars_setVar]; rw [if_neg (by rintro rfl; simp at hy)]; exact h.n

theorem Base.setArr {x : List ℕ} {σ : Env} (h : Base x σ) {a : String} (ha : a ≠ "t") (i v : ℕ) :
    Base x (σ.setArr a i v) :=
  ⟨h.tab.congr (by simp only [arrs_setArr]; rw [if_neg (Ne.symm ha)]), h.len, h.V, h.E, h.n⟩

/-- **What the validator certifies**: `WellFormed` without `crosses`. -/
structure WF3 (x : List ℕ) : Prop where
  nV : nw x ≤ Vw x
  len : x.length = 4 + Vw x + 2 * x.getD 1 0
  off0 : offw x 0 = 0
  offV : offw x (Vw x) = 2 * x.getD 1 0
  mono : ∀ i < Vw x, offw x i ≤ offw x (i + 1)
  tgt_lt : ∀ s < 2 * x.getD 1 0, tgtw x s < Vw x

theorem WF3.off_le {x : List ℕ} (h : WF3 x) {i : ℕ} (hi : i ≤ Vw x) :
    offw x i ≤ 2 * x.getD 1 0 := by
  rw [← h.offV]; exact mono_chain (offw x) (Vw x) h.mono i hi

/-- Well-formedness is `WF3` and `crosses`. -/
theorem wellFormed_iff {x : List ℕ} :
    WellFormed x ↔ WF3 x ∧ ∀ u < Vw x, ∀ j, offw x u ≤ j → j < offw x (u + 1) →
      (u < nw x ↔ nw x ≤ tgtw x j) := by
  constructor
  · intro hw
    exact ⟨⟨wf_nV hw, wf_len hw, wf_off0 hw, wf_offV hw, wf_mono hw, wf_tgt_lt hw⟩,
      fun u hu j h1 h2 => wf_cross hw hu h1 h2⟩
  · rintro ⟨h3, hc⟩
    refine ⟨?_, h3.len, h3.off0, h3.offV, h3.mono, h3.tgt_lt, ?_⟩
    · rw [← nw_eq_leftCount]; exact h3.nV
    · intro u hu j h1 h2
      rw [← nw_eq_leftCount]
      exact hc u hu j h1 h2

/-- The header: `V := t[0]; E := t[1]; n := t[len - 1]`. -/
def hdrT : Com :=
  .seq (.assign "V" (.get "t" (.lit 0)))
    (.seq (.assign "E" (.get "t" (.lit 1)))
      (.assign "n" (.get "t" (.sub (.var "len") (.lit 1)))))

theorem hdrT_spec {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hlB : x.length < B) (h4 : 4 ≤ x.length) :
    Spec B (fun σ => TabOK x σ ∧ σ.vars "len" = x.length) hdrT
      (fun σ σ' => σ' = ((σ.setVar "V" (Vw x)).setVar "E" (x.getD 1 0)).setVar "n" (nw x)) 14 := by
  rintro σ ⟨htab, hl⟩
  have hlen := htab.length
  have hB : 4 < B := by omega
  have hg0 : (σ.arrs "t").getD 0 0 = Vw x := htab.getD (by omega)
  have hg1 : (σ.arrs "t").getD 1 0 = x.getD 1 0 := htab.getD (by omega)
  have hgn : (σ.arrs "t").getD (x.length - 1) 0 = nw x := htab.getD (by omega)
  have hVB : Vw x < B := getD_lt_of_mem hx (by omega) 0
  have hEB : x.getD 1 0 < B := getD_lt_of_mem hx (by omega) 1
  have hnB : nw x < B := getD_lt_of_mem hx (by omega) _
  rw [List.getD_eq_getElem?_getD] at hg0 hg1 hgn
  unfold hdrT
  run_vcg
  all_goals (try simp [hl, hg0, hg1, hgn])
  all_goals (try omega)

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.RowIter` -/

section
/-!
The generic pass over the slots of a word in `t`: for every row `u`, for every slot `j` of the
row, a body. Its specification is stated for an invariant `Inv P σ` indexed by the list `P` of
slots visited so far (`pairsAt x u j`), the body being asked to take `Inv (pairsAt x u j)` to
`Inv (pairsAt x u (j + 1))`. The cost is amortized over the slots: `Kb + 8` per slot, `22` per
row, so that the pass is linear in the word.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open scoped Classical

variable {B : ℕ}

/-- `u := 0; while u < V: j := t[2+u]; je := t[3+u]; while j < je: body; j := j+1; u := u+1`. -/
def rowIter (body : Com) : Com :=
  .seq (.assign "u" (.lit 0))
    (.while (.lt (.var "u") (.var "V"))
      (.seq (.assign "j" (.get "t" (.add (.lit 2) (.var "u"))))
        (.seq (.assign "je" (.get "t" (.add (.lit 3) (.var "u"))))
          (.seq (.while (.lt (.var "j") (.var "je"))
              (.seq body (.assign "j" (.add (.var "j") (.lit 1)))))
            (.assign "u" (.add (.var "u") (.lit 1)))))))

section Iter

variable {x : List ℕ} {Inv : List (ℕ × ℕ) → Env → Prop} {body : Com} {Kb : ℕ}

/-- The invariant of the inner loop, row `u`. -/
def InnerInv (x : List ℕ) (Inv : List (ℕ × ℕ) → Env → Prop) (u : ℕ) (σ : Env) : Prop :=
  Inv (pairsAt x u (σ.vars "j")) σ ∧ Base x σ ∧ σ.vars "u" = u ∧
    σ.vars "je" = offw x (u + 1) ∧ offw x u ≤ σ.vars "j" ∧ σ.vars "j" ≤ offw x (u + 1)

theorem inner_spec (h3 : WF3 x) (hB : 8 * x.length + 40 ≤ B)
    (hfr : ∀ y ∈ body.wvars, y ∉ ["u", "j", "je"])
    (hset : ∀ P σ y v, y ∈ ["u", "j", "je"] → Inv P σ → Inv P (σ.setVar y v))
    (hbody : ∀ u j, u < Vw x → offw x u ≤ j → j < offw x (u + 1) →
      Spec B (fun σ => Inv (pairsAt x u j) σ ∧ Base x σ ∧ σ.vars "u" = u ∧ σ.vars "j" = j) body
        (fun _ σ' => Inv (pairsAt x u (j + 1)) σ' ∧ Base x σ') Kb)
    {u : ℕ} (hu : u < Vw x) :
    Spec B (fun σ => InnerInv x Inv u σ ∧ σ.vars "j" = offw x u)
      (.while (.lt (.var "j") (.var "je")) (.seq body (.assign "j" (.add (.var "j") (.lit 1)))))
      (fun _ σ' => InnerInv x Inv u σ' ∧ σ'.vars "j" = offw x (u + 1))
      ((Kb + 8) * (offw x (u + 1) - offw x u) + 4) := by
  have hlen := h3.len
  have hoff1 : offw x (u + 1) ≤ 2 * x.getD 1 0 := h3.off_le hu
  have hjB : ∀ j ≤ offw x (u + 1), j + 1 < B := fun j hj => by omega
  refine Spec.forRange "j" "je" (InnerInv x Inv u) (offw x (u + 1)) (Kb + 4) _
    (fun σ hσ => by have := hσ.2.2.2.2.2; have := hjB _ this; omega)
    (fun σ hσ => by have := hjB _ (le_refl (offw x (u + 1))); rw [hσ.2.2.2.1]; omega)
    (fun σ hσ => hσ.2.2.2.1) (fun σ hσ => hσ.2.2.2.2.2) ?_ (fun σ hσ => hσ.1)
    (fun σ hσ => by rw [hσ.2] <;> exact le_rfl)
  rintro σ ⟨⟨hI, hb, hu', hje, hj1, hj2⟩, hlt⟩
  obtain ⟨σ', r1, ⟨hI', hb'⟩, hfv, -, -, -⟩ :=
    (hbody u (σ.vars "j") hu hj1 hlt).frame.run ⟨hI, hb, hu', rfl⟩
  have hv : ∀ y, y ∈ ["u", "j", "je"] → σ'.vars y = σ.vars y := fun y hy =>
    hfv y (fun h => hfr y h hy)
  have hj' : σ'.vars "j" = σ.vars "j" := hv "j" (by simp)
  have r2 := RunStep.assign B σ' "j" (.add (.var "j") (.lit 1)) (σ.vars "j" + 1)
    (RunStep.eval_add B σ' (.var "j") (.lit 1) _ _
      (by rw [← hj']; exact RunStep.eval_var B σ' "j" (by rw [hj']; have := hjB _ hj2; omega))
      (RunStep.eval_lit B 1 σ' (by omega)) (hjB _ hj2))
  refine ⟨_, (r1.seq r2).mono (by simp), ⟨?_, hb'.setVar "j" (by simp) _, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    exact hset _ _ "j" _ (by simp) hI'
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]; rw [hv "u" (by simp)]; exact hu'
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]; rw [hv "je" (by simp)]; exact hje
  · simp; omega
  · simp; omega
  · simp

/-- The invariant of the outer loop. -/
def RowOuterInv (x : List ℕ) (Inv : List (ℕ × ℕ) → Env → Prop) (σ : Env) : Prop :=
  Inv (pairsUpto x (σ.vars "u")) σ ∧ Base x σ ∧ σ.vars "u" ≤ Vw x

/-- **The pass over the slots.** -/
theorem rowIter_spec (h3 : WF3 x) (hB : 8 * x.length + 40 ≤ B) (body : Com) (Kb : ℕ)
    (hfr : ∀ y ∈ body.wvars, y ∉ ["u", "j", "je"])
    (hset : ∀ P σ y v, y ∈ ["u", "j", "je"] → Inv P σ → Inv P (σ.setVar y v))
    (hbody : ∀ u j, u < Vw x → offw x u ≤ j → j < offw x (u + 1) →
      Spec B (fun σ => Inv (pairsAt x u j) σ ∧ Base x σ ∧ σ.vars "u" = u ∧ σ.vars "j" = j) body
        (fun _ σ' => Inv (pairsAt x u (j + 1)) σ' ∧ Base x σ') Kb) :
    Spec B (fun σ => Inv [] σ ∧ Base x σ) (rowIter body)
      (fun _ σ' => Inv (allPairs x) σ' ∧ Base x σ')
      ((Kb + 8) * (2 * x.getD 1 0) + 22 * Vw x + 6) := by
  have hlen := h3.len
  have hVB : Vw x < B := by omega
  have hoffB : ∀ i ≤ Vw x, offw x i < B := fun i hi => by have := h3.off_le hi; omega
  rintro σ₀ ⟨hI₀, hb₀⟩
  have r0 := RunStep.assign B σ₀ "u" (.lit 0) 0 (RunStep.eval_lit B 0 σ₀ (by omega))
  set σ₁ := σ₀.setVar "u" 0 with hσ₁
  have hO₁ : RowOuterInv x Inv σ₁ := by
    refine ⟨?_, hb₀.setVar "u" (by simp) 0, by simp [hσ₁]⟩
    simp only [hσ₁, vars_setVar, String.reduceEq, ↓reduceIte]
    show Inv (pairsUpto x 0) _
    have h0 : pairsUpto x 0 = [] := by simp [pairsUpto]
    rw [h0]
    exact hset _ _ "u" 0 (by simp) hI₀
  have hdef : ∀ τ, RowOuterInv x Inv τ → ∃ v, (Cond.lt (.var "u") (.var "V")).evalB B τ = some v :=
    fun τ hτ => evalB_condLt_vars (by have := hτ.2.2; omega) (by rw [hτ.2.1.V]; exact hVB)
  have hstep : ∀ τ, RowOuterInv x Inv τ → (Cond.lt (.var "u") (.var "V")).evalB B τ = some true →
      ∃ τ' K, Run B (.seq (.assign "j" (.get "t" (.add (.lit 2) (.var "u"))))
        (.seq (.assign "je" (.get "t" (.add (.lit 3) (.var "u"))))
          (.seq (.while (.lt (.var "j") (.var "je"))
              (.seq body (.assign "j" (.add (.var "j") (.lit 1)))))
            (.assign "u" (.add (.var "u") (.lit 1)))))) τ τ' K ∧ RowOuterInv x Inv τ' ∧
        1 + (Cond.lt (.var "u") (.var "V")).size + K +
          ((Kb + 8) * (2 * x.getD 1 0 - offw x (τ'.vars "u")) + 22 * (Vw x - τ'.vars "u")) ≤
        (Kb + 8) * (2 * x.getD 1 0 - offw x (τ.vars "u")) + 22 * (Vw x - τ.vars "u") := by
    intro τ ⟨hI, hb, hule⟩ hcond
    have hu : τ.vars "u" < Vw x := by
      have := lt_of_condLt_true hcond; rw [hb.V] at this; exact this
    generalize hu_eq : τ.vars "u" = u at hI hule hu ⊢
    have hlenT := hb.tab.length
    have hg2 : (τ.arrs "t").getD (2 + u) 0 = offw x u := hb.tab.getD (by omega)
    have hg3 : (τ.arrs "t").getD (3 + u) 0 = offw x (u + 1) := by
      rw [hb.tab.getD (by omega)]; unfold offw; congr 1; omega
    have hmono := h3.mono u hu
    have hoff1 := h3.off_le (i := u + 1) hu
    -- j := t[2 + u]
    have hue : (Expr.var "u").evalB B τ = some u := by
      rw [← hu_eq]; exact RunStep.eval_var B τ "u" (by rw [hu_eq]; omega)
    have e2 : (Expr.add (.lit 2) (.var "u")).evalB B τ = some (2 + u) :=
      RunStep.eval_add B τ _ _ _ _ (RunStep.eval_lit B 2 τ (by omega)) hue (by omega)
    have r1 := RunStep.assign B τ "j" _ _ (RunStep.eval_get B τ "t" _ _ e2 (by omega)
      (by rw [hg2]; exact hoffB u (by omega)))
    rw [hg2] at r1
    set τ₁ := τ.setVar "j" (offw x u) with hτ₁
    -- je := t[3 + u]
    have e3 : (Expr.add (.lit 3) (.var "u")).evalB B τ₁ = some (3 + u) :=
      RunStep.eval_add B τ₁ _ _ _ _ (RunStep.eval_lit B 3 τ₁ (by omega))
        (by have : τ₁.vars "u" = u := by simp [hτ₁, hu_eq]
            rw [← this]; exact RunStep.eval_var B τ₁ "u" (by rw [this]; omega)) (by omega)
    have hg3' : (τ₁.arrs "t").getD (3 + u) 0 = offw x (u + 1) := by simpa [hτ₁] using hg3
    have r2 := RunStep.assign B τ₁ "je" _ _ (RunStep.eval_get B τ₁ "t" _ _ e3
      (by simp [hτ₁]; omega) (by rw [hg3']; exact hoffB (u + 1) hu))
    rw [hg3'] at r2
    set τ₂ := τ₁.setVar "je" (offw x (u + 1)) with hτ₂
    -- the inner loop
    obtain ⟨τ₃, r3, ⟨hI₃, hb₃, hu₃, -, -, -⟩, hj₃⟩ :=
      (inner_spec h3 hB hfr hset hbody hu).run (σ := τ₂) (by
        refine ⟨⟨?_, (hb.setVar "j" (by simp) _).setVar "je" (by simp) _, by simp [hτ₂, hτ₁, hu_eq],
          by simp [hτ₂], by simp [hτ₂, hτ₁], by simp [hτ₂, hτ₁]; exact hmono⟩, by simp [hτ₂, hτ₁]⟩
        simp only [hτ₂, hτ₁, vars_setVar, String.reduceEq, ↓reduceIte]
        rw [pairsAt_start]
        exact hset _ _ "je" _ (by simp) (hset _ _ "j" _ (by simp) hI))
    rw [hj₃, pairsAt_end] at hI₃
    -- u := u + 1
    have r4 := RunStep.assign B τ₃ "u" (.add (.var "u") (.lit 1)) (u + 1)
      (RunStep.eval_add B τ₃ (.var "u") (.lit 1) _ _
        (by rw [← hu₃]; exact RunStep.eval_var B τ₃ "u" (by rw [hu₃]; omega))
        (RunStep.eval_lit B 1 τ₃ (by omega)) (by omega))
    refine ⟨_, _, r1.seq (r2.seq (r3.seq r4)), ⟨?_, hb₃.setVar "u" (by simp) _, by simp; omega⟩, ?_⟩
    · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
      exact hset _ _ "u" _ (by simp) hI₃
    · simp only [vars_setVar, String.reduceEq, ↓reduceIte, size_condLt, size_var, size_get,
        size_add, size_lit, Expr.add_def, size_bin]
      have h1 : (Kb + 8) * (2 * x.getD 1 0 - offw x u) =
          (Kb + 8) * (2 * x.getD 1 0 - offw x (u + 1)) + (Kb + 8) * (offw x (u + 1) - offw x u) := by
        rw [← Nat.mul_add]; congr 1; omega
      rw [h1]
      have h2 : 22 * (Vw x - u) = 22 * (Vw x - (u + 1)) + 22 := by
        rw [show Vw x - u = (Vw x - (u + 1)) + 1 by omega, Nat.mul_add]
      rw [h2]
      omega
  obtain ⟨σ', K, hrun, ⟨hI', hb', hu'⟩, hfalse, hpay⟩ := Run.while_potential (B := B)
    (b := .lt (.var "u") (.var "V")) (RowOuterInv x Inv)
    (fun τ => (Kb + 8) * (2 * x.getD 1 0 - offw x (τ.vars "u")) + 22 * (Vw x - τ.vars "u"))
    hdef hstep hO₁
  have hueq : σ'.vars "u" = Vw x := by
    have := le_of_condLt_false hfalse
    rw [hb'.V] at this
    omega
  refine ⟨σ', (r0.seq hrun).mono ?_, ?_, hb'⟩
  · simp only [size_condLt, size_var, size_lit, hσ₁, vars_setVar, String.reduceEq, ↓reduceIte,
      h3.off0, Nat.sub_zero] at hpay ⊢
    omega
  · rw [hueq] at hI'; exact hI'

end Iter

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.SymmDeg` -/

section
/-!
The degree pass: for every slot `(u, j)` of the word in `t`, with target `tt`, check that the
edge crosses the split (`u < n ↔ n ≤ tt`), clearing `ok` otherwise, and count the slot for its
destination in `deg` (`u` for a left row, `tt` for a right row). After the pass `ok = 1` exactly
when every listed edge crosses the split — with the syntactic checks of `Validate.lean`, exactly
when the word is well formed — and then `deg` holds the degrees of the symmetrized word.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open scoped Classical

variable {B : ℕ}

theorem getD_set_self {l : List ℕ} {i v : ℕ} (h : i < l.length) : (l.set i v).getD i 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]; rfl

theorem getD_set_ne {l : List ℕ} {i j v : ℕ} (h : i ≠ j) : (l.set i v).getD j 0 = l.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

/-- The slot crosses the split. -/
def Cross (x : List ℕ) (p : ℕ × ℕ) : Prop := p.1 < nw x ↔ nw x ≤ tgtw x p.2

/-- The invariant of the degree pass, over the slots `P` visited so far. -/
structure DegInv (x : List ℕ) (P : List (ℕ × ℕ)) (σ : Env) : Prop where
  okle : σ.vars "ok" ≤ 1
  okiff : σ.vars "ok" = 1 ↔ ∀ p ∈ P, Cross x p
  lenD : (σ.arrs "deg").length = nw x
  bd : ∀ l < nw x, (σ.arrs "deg").getD l 0 ≤ P.length
  deg : σ.vars "ok" = 1 → ∀ l < nw x, (σ.arrs "deg").getD l 0 = (seg x l P).length

theorem DegInv.setVar {x : List ℕ} {P : List (ℕ × ℕ)} {σ : Env} (h : DegInv x P σ) (y : String)
    (hy : y ≠ "ok") (v : ℕ) : DegInv x P (σ.setVar y v) := by
  have e : (σ.setVar y v).vars "ok" = σ.vars "ok" := by simp [Ne.symm hy]
  exact ⟨by rw [e]; exact h.okle, by rw [e]; exact h.okiff, h.lenD, h.bd, by rw [e]; exact h.deg⟩

/-- `tt := t[3 + V + j]; if u < n then (if tt < n then ok := 0); deg[u]++ else (if tt < n then
deg[tt]++ else ok := 0)`. -/
def degThen : Com :=
  .seq (.ite (.lt (.var "tt") (.var "n")) (.assign "ok" (.lit 0)) .skip)
    (.store "deg" (.var "u") (.add (.get "deg" (.var "u")) (.lit 1)))

def degElse : Com :=
  .ite (.lt (.var "tt") (.var "n"))
    (.store "deg" (.var "tt") (.add (.get "deg" (.var "tt")) (.lit 1)))
    (.assign "ok" (.lit 0))

def degBody : Com :=
  .seq (.assign "tt" (.get "t" (.add (.add (.lit 3) (.var "V")) (.var "j"))))
    (.ite (.lt (.var "u") (.var "n")) degThen degElse)

/-- Counting one slot for its destination. -/
theorem DegInv.count {x : List ℕ} {P : List (ℕ × ℕ)} {σ : Env} (h : DegInv x P σ) (p : ℕ × ℕ)
    (hd : dest x p < nw x) (hc : Cross x p) :
    DegInv x (P ++ [p]) (σ.setArr "deg" (dest x p) ((σ.arrs "deg").getD (dest x p) 0 + 1)) := by
  have hlen := h.lenD
  refine ⟨h.okle, ?_, by simp [hlen], fun l hl => ?_, fun hok l hl => ?_⟩
  · simp only [vars_setArr]
    rw [h.okiff]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · intro hall q hq
      rcases hq with hq | rfl
      · exact hall q hq
      · exact hc
    · intro hall q hq; exact hall q (Or.inl hq)
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [List.length_append, List.length_singleton]
    by_cases hld : l = dest x p
    · subst hld; rw [getD_set_self (by omega)]; have := h.bd _ hl; omega
    · rw [getD_set_ne (Ne.symm hld)]; have := h.bd l hl; omega
  · simp only [vars_setArr] at hok
    simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [seg_append, seg_single, List.length_append]
    by_cases hld : l = dest x p
    · subst hld
      rw [getD_set_self (by omega), if_pos rfl, h.deg hok _ hl]; rfl
    · rw [getD_set_ne (Ne.symm hld), if_neg (Ne.symm hld), h.deg hok l hl]; rfl

/-- Clearing the flag on a slot that does not cross. -/
theorem DegInv.fail {x : List ℕ} {P : List (ℕ × ℕ)} {σ : Env} (h : DegInv x P σ) (p : ℕ × ℕ)
    (hc : ¬ Cross x p) : DegInv x (P ++ [p]) (σ.setVar "ok" 0) := by
  refine ⟨by simp, ?_, h.lenD, fun l hl => ?_, fun hok => by simp at hok⟩
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    constructor
    · intro h0; omega
    · intro hall; exact absurd (hall p (List.mem_append_right _ (List.mem_singleton_self p))) hc
  · simp only [arrs_setVar]
    rw [List.length_append]; have := h.bd l hl; omega

/-- Clearing the flag on a left-row slot that does not cross, then still counting it. -/
theorem DegInv.failCount {x : List ℕ} {P : List (ℕ × ℕ)} {σ : Env} (h : DegInv x P σ) (p : ℕ × ℕ)
    (hc : ¬ Cross x p) (hd : dest x p < nw x) :
    DegInv x (P ++ [p])
      ((σ.setVar "ok" 0).setArr "deg" (dest x p) ((σ.arrs "deg").getD (dest x p) 0 + 1)) := by
  have h1 := h.fail p hc
  have hlen := h.lenD
  refine ⟨by simp, by simpa using h1.okiff, by simp [hlen], fun l hl => ?_, fun hok => by simp at hok⟩
  simp only [arrs_setArr, arrs_setVar, String.reduceEq, ↓reduceIte]
  rw [List.length_append, List.length_singleton]
  by_cases hld : l = dest x p
  · subst hld; rw [getD_set_self (by omega)]; have := h.bd _ hl; omega
  · rw [getD_set_ne (Ne.symm hld)]; have := h.bd l hl; omega

theorem degBody_spec {x : List ℕ} (h3 : WF3 x) (hB : 8 * x.length + 40 ≤ B) {u j : ℕ}
    (hu : u < Vw x) (hj1 : offw x u ≤ j) (hj2 : j < offw x (u + 1)) :
    Spec B (fun σ => DegInv x (pairsAt x u j) σ ∧ Base x σ ∧ σ.vars "u" = u ∧ σ.vars "j" = j)
      degBody (fun _ σ' => DegInv x (pairsAt x u (j + 1)) σ' ∧ Base x σ') 30 := by
  rintro σ ⟨hI, hb, hu', hj'⟩
  have hlen := h3.len
  have hlenT := hb.tab.length
  have hV := hb.V
  have hn := hb.n
  have hj2E : j < 2 * x.getD 1 0 := lt_of_lt_of_le hj2 (h3.off_le hu)
  have hg : (σ.arrs "t").getD (3 + Vw x + j) 0 = tgtw x j := hb.tab.getD (by omega)
  have htV : tgtw x j < Vw x := h3.tgt_lt j hj2E
  have hnV := h3.nV
  have hlenD := hI.lenD
  have hPlen : (pairsAt x u j).length ≤ 2 * x.getD 1 0 := by
    obtain ⟨Q, hQ⟩ := pairsAt_prefix x u j hu (le_of_lt hj2)
    have := congrArg List.length hQ
    rw [List.length_append] at this
    have h2 : (allPairs x).length = 2 * x.getD 1 0 := by
      unfold allPairs; rw [length_pairsUpto x h3.off0 h3.mono _ le_rfl, h3.offV]
    omega
  set p : ℕ × ℕ := (u, j) with hp
  have hstep : pairsAt x u (j + 1) = pairsAt x u j ++ [p] := pairsAt_succ x hj1
  -- tt := t[3 + V + j]
  have hVe : (Expr.var "V").evalB B σ = some (Vw x) := by
    rw [← hV]; exact RunStep.eval_var B σ "V" (by omega)
  have hje : (Expr.var "j").evalB B σ = some j := by
    rw [← hj']; exact RunStep.eval_var B σ "j" (by rw [hj']; omega)
  have hidx := RunStep.eval_add B σ _ _ _ _
    (RunStep.eval_add B σ _ _ _ _ (RunStep.eval_lit B 3 σ (by omega)) hVe (by omega)) hje (by omega)
  have r1 := RunStep.assign B σ "tt" _ _ (RunStep.eval_get B σ "t" _ _ hidx (by omega)
    (by rw [hg]; omega))
  rw [hg] at r1
  set σ₁ := σ.setVar "tt" (tgtw x j) with hσ₁
  have hI₁ : DegInv x (pairsAt x u j) σ₁ := hI.setVar "tt" (by decide) _
  have hb₁ : Base x σ₁ := hb.setVar "tt" (by simp) _
  have hu₁ : σ₁.vars "u" = u := by simp [hσ₁, hu']
  have hn₁ : σ₁.vars "n" = nw x := by simp [hσ₁, hn]
  have htt₁ : σ₁.vars "tt" = tgtw x j := by simp [hσ₁]
  have hue : (Expr.var "u").evalB B σ₁ = some u := by
    rw [← hu₁]; exact RunStep.eval_var B σ₁ "u" (by rw [hu₁]; omega)
  have hne : (Expr.var "n").evalB B σ₁ = some (nw x) := by
    rw [← hn₁]; exact RunStep.eval_var B σ₁ "n" (by rw [hn₁]; omega)
  have htte : (Expr.var "tt").evalB B σ₁ = some (tgtw x j) := by
    rw [← htt₁]; exact RunStep.eval_var B σ₁ "tt" (by rw [htt₁]; omega)
  have hlenD₁ : (σ₁.arrs "deg").length = nw x := by simp [hσ₁, hlenD]
  have hdegB : ∀ l < nw x, (σ₁.arrs "deg").getD l 0 + 1 < B := fun l hl => by
    have := hI₁.bd l hl; omega
  -- the increment of `deg[y]`, for `y` holding `d < n`
  have hinc : ∀ (y : String) (d : ℕ), σ₁.vars y = d → d < nw x →
      Run B (.store "deg" (.var y) (.add (.get "deg" (.var y)) (.lit 1))) σ₁
        (σ₁.setArr "deg" d ((σ₁.arrs "deg").getD d 0 + 1)) 7 := by
    intro y d hy hd
    have hye : (Expr.var y).evalB B σ₁ = some d := by
      rw [← hy]; exact RunStep.eval_var B σ₁ y (by rw [hy]; omega)
    have hget := RunStep.eval_get B σ₁ "deg" _ _ hye (by omega) (by have := hdegB d hd; omega)
    have hadd := RunStep.eval_add B σ₁ _ _ _ _ hget (RunStep.eval_lit B 1 σ₁ (by omega)) (hdegB d hd)
    exact (RunStep.store B σ₁ "deg" _ _ _ _ hye hadd (by omega)).mono (by simp)
  have hcross_iff : Cross x p ↔ (u < nw x ↔ nw x ≤ tgtw x j) := Iff.rfl
  by_cases hun : u < nw x
  · -- a left row
    have hcu := RunStep.cond_lt_true B σ₁ _ _ _ _ hue hne hun
    have hdest : dest x p = u := by unfold dest; simp [hp, hun]
    by_cases htn : tgtw x j < nw x
    · -- the target is a left vertex: no crossing
      have hct := RunStep.cond_lt_true B σ₁ _ _ _ _ htte hne htn
      have rA := RunStep.ite_true B _ (.assign "ok" (.lit 0)) .skip σ₁ _ 2 hct
        (RunStep.assign B σ₁ "ok" (.lit 0) 0 (RunStep.eval_lit B 0 σ₁ (by omega)))
      set σ₂ := σ₁.setVar "ok" 0 with hσ₂
      have hu₂ : σ₂.vars "u" = u := by simp [hσ₂, hu₁]
      have hlenD₂ : (σ₂.arrs "deg").length = nw x := by simp [hσ₂, hlenD₁]
      have rB : Run B (.store "deg" (.var "u") (.add (.get "deg" (.var "u")) (.lit 1))) σ₂
          (σ₂.setArr "deg" u ((σ₂.arrs "deg").getD u 0 + 1)) 7 := by
        have hye : (Expr.var "u").evalB B σ₂ = some u := by
          rw [← hu₂]; exact RunStep.eval_var B σ₂ "u" (by rw [hu₂]; omega)
        have hb2 : (σ₂.arrs "deg").getD u 0 + 1 < B := by
          simp only [hσ₂, arrs_setVar]; exact hdegB u hun
        have hget := RunStep.eval_get B σ₂ "deg" _ _ hye (by omega) (by omega)
        have hadd := RunStep.eval_add B σ₂ _ _ _ _ hget (RunStep.eval_lit B 1 σ₂ (by omega)) hb2
        exact (RunStep.store B σ₂ "deg" _ _ _ _ hye hadd (by omega)).mono (by simp)
      have rite := RunStep.ite_true B _ degThen degElse σ₁ _ _ hcu (rA.seq rB)
      refine ⟨_, (r1.seq rite).mono (by simp), ?_, (hb₁.setVar "ok" (by simp) 0).setArr (by decide) _ _⟩
      rw [hstep]
      have := hI₁.failCount p (by rw [hcross_iff]; omega) (by rw [hdest]; exact hun)
      rw [hdest] at this
      simpa [hσ₂] using this
    · -- the target is a right vertex: the slot crosses
      have hct := RunStep.cond_lt_false B σ₁ _ _ _ _ htte hne htn
      have rA := RunStep.ite_false B _ (.assign "ok" (.lit 0)) .skip σ₁ σ₁ 2 hct
        ((RunStep.skip B σ₁).mono (by omega))
      have rB := hinc "u" u hu₁ hun
      have rite := RunStep.ite_true B _ degThen degElse σ₁ _ _ hcu (rA.seq rB)
      refine ⟨_, (r1.seq rite).mono (by simp), ?_, hb₁.setArr (by decide) _ _⟩
      rw [hstep]
      have := hI₁.count p (by rw [hdest]; exact hun) (by rw [hcross_iff]; omega)
      rw [hdest] at this
      exact this
  · -- a right row
    have hcu := RunStep.cond_lt_false B σ₁ _ _ _ _ hue hne hun
    have hdest : dest x p = tgtw x j := by unfold dest; simp [hp, hun]
    by_cases htn : tgtw x j < nw x
    · -- the target is a left vertex: the slot crosses
      have hct := RunStep.cond_lt_true B σ₁ _ _ _ _ htte hne htn
      have rB := hinc "tt" (tgtw x j) htt₁ htn
      have rA := RunStep.ite_true B _ _ (.assign "ok" (.lit 0)) σ₁ _ _ hct rB
      have rite := RunStep.ite_false B _ degThen degElse σ₁ _ _ hcu rA
      refine ⟨_, (r1.seq rite).mono (by simp), ?_, hb₁.setArr (by decide) _ _⟩
      rw [hstep]
      have := hI₁.count p (by rw [hdest]; exact htn) (by rw [hcross_iff]; omega)
      rw [hdest] at this
      exact this
    · -- no crossing
      have hct := RunStep.cond_lt_false B σ₁ _ _ _ _ htte hne htn
      have rA := RunStep.ite_false B _
        (.store "deg" (.var "tt") (.add (.get "deg" (.var "tt")) (.lit 1))) _ σ₁ _ 2 hct
        (RunStep.assign B σ₁ "ok" (.lit 0) 0 (RunStep.eval_lit B 0 σ₁ (by omega)))
      have rite := RunStep.ite_false B _ degThen degElse σ₁ _ _ hcu rA
      refine ⟨_, (r1.seq rite).mono (by simp), ?_, hb₁.setVar "ok" (by simp) 0⟩
      rw [hstep]
      exact hI₁.fail p (by rw [hcross_iff]; omega)

/-- **The degree pass.** -/
def degPass : Com := rowIter degBody

theorem degBody_wvars : ∀ y ∈ degBody.wvars, y ∉ ["u", "j", "je"] := by
  intro y hy
  simp [degBody, degThen, degElse, Com.wvars] at hy
  rcases hy with rfl | rfl <;> simp

/-- The crossing condition of all slots is `WellFormed.crosses`. -/
theorem cross_all_iff (x : List ℕ) :
    (∀ p ∈ allPairs x, Cross x p) ↔
      ∀ u < Vw x, ∀ j, offw x u ≤ j → j < offw x (u + 1) → (u < nw x ↔ nw x ≤ tgtw x j) := by
  constructor
  · intro h u hu j h1 h2
    exact h (u, j) ((mem_allPairs x).2 ⟨hu, h1, h2⟩)
  · rintro h ⟨u, j⟩ hp
    obtain ⟨hu, h1, h2⟩ := (mem_allPairs x).1 hp
    exact h u hu j h1 h2

/-- **After the pass**: `ok = 1` exactly when the word is well formed (given `WF3`), and then
`deg` holds the degrees. -/
theorem degPass_spec {x : List ℕ} (h3 : WF3 x) (hB : 8 * x.length + 40 ≤ B) :
    Spec B (fun σ => Base x σ ∧ σ.vars "ok" = 1 ∧ σ.arrs "deg" = List.replicate (nw x) 0) degPass
      (fun _ σ' => Base x σ' ∧ σ'.vars "ok" ≤ 1 ∧ (σ'.vars "ok" = 1 ↔ Lax117284.BipartiteDecision.WellFormed x) ∧
        (σ'.vars "ok" = 1 → ∀ l < nw x, (σ'.arrs "deg").getD l 0 = deg x l) ∧
        (σ'.arrs "deg").length = nw x)
      ((30 + 8) * (2 * x.getD 1 0) + 22 * Vw x + 6) := by
  have hspec := rowIter_spec (Inv := DegInv x) h3 hB degBody 30 degBody_wvars
    (fun P σ y v hy hI => hI.setVar y (by simp at hy; rcases hy with rfl | rfl | rfl <;> decide) v)
    (fun u j hu hj1 hj2 => degBody_spec h3 hB hu hj1 hj2)
  refine hspec.conseq ?_ ?_ le_rfl
  · rintro σ ⟨hb, hok, hdeg⟩
    refine ⟨⟨by omega, by simp [hok], by simp [hdeg], fun l hl => ?_, fun _ l hl => ?_⟩, hb⟩
    · rw [hdeg, replicate_eq_arrOf, getD_arrOf _ hl]; simp
    · rw [hdeg, replicate_eq_arrOf, getD_arrOf _ hl, seg_nil]; rfl
  · rintro σ σ' - ⟨hI, hb⟩
    refine ⟨hb, hI.okle, ?_, fun hok l hl => hI.deg hok l hl, hI.lenD⟩
    rw [hI.okiff, cross_all_iff, wellFormed_iff]
    exact ⟨fun h => ⟨h3, h⟩, fun h => h.2⟩

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.SymmPrefix` -/

section
/-!
The symmetrized word built in `a`, first half: the header, the offsets `offS` by prefix sums of
the degrees, the last entry, and the cursors `pos` at the offsets (`FixedA`, `PosOK`).
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteDecision
open scoped Classical

variable {B : ℕ}

theorem offS_le_n (x : List ℕ) (i : ℕ) : offS x i ≤ offS x (nw x) := by
  rcases Nat.lt_or_ge i (nw x) with h | h
  · exact offS_mono x (le_of_lt h)
  · rw [offS_of_ge x h]

theorem deg_le_n (x : List ℕ) {l : ℕ} (hl : l < nw x) : deg x l ≤ offS x (nw x) := by
  have h1 := offS_succ_of_lt x hl
  have h2 := offS_le_n x (l + 1)
  omega

/-- The owner of a slot of the target array. -/
theorem exists_owner (x : List ℕ) {s : ℕ} (hs : s < offS x (nw x)) :
    ∃ l < nw x, offS x l ≤ s ∧ s < offS x (l + 1) := by
  have key : ∀ i ≤ nw x, s < offS x i → ∃ l < i, offS x l ≤ s ∧ s < offS x (l + 1) := by
    intro i
    induction i with
    | zero => intro _ h; rw [offS_zero] at h; omega
    | succ i ih =>
      intro hi h
      rcases Nat.lt_or_ge s (offS x i) with h' | h'
      · obtain ⟨l, hl, h1, h2⟩ := ih (by omega) h'
        exact ⟨l, by omega, h1, h2⟩
      · exact ⟨i, by omega, h', h⟩
  exact key _ le_rfl hs

/-! ### The fixed cells of `a` -/

/-- The header, the offsets and the last entry of the symmetrized word, in `a`. -/
structure FixedA (x : List ℕ) (σ : Env) : Prop where
  len : (σ.arrs "a").length = x.length
  h0 : (σ.arrs "a").getD 0 0 = Vw x
  h1 : (σ.arrs "a").getD 1 0 = x.getD 1 0
  off : ∀ i ≤ Vw x, (σ.arrs "a").getD (2 + i) 0 = offS x i
  last : (σ.arrs "a").getD (3 + Vw x + 2 * x.getD 1 0) 0 = nw x

theorem FixedA.congr {x : List ℕ} {σ σ' : Env} (h : FixedA x σ) (ha : σ'.arrs "a" = σ.arrs "a") :
    FixedA x σ' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [ha]
  exacts [h.len, h.h0, h.h1, h.off, h.last]

/-- A store into the target area keeps the fixed cells. -/
theorem FixedA.setTgt {x : List ℕ} {σ : Env} (hw : WellFormed x) (h : FixedA x σ) {s v : ℕ}
    (hs : s < 2 * x.getD 1 0) : FixedA x (σ.setArr "a" (3 + Vw x + s) v) := by
  have hlen := wf_len hw
  refine ⟨by simp [h.len], ?_, ?_, fun i hi => ?_, ?_⟩
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [getD_set_ne (by omega)]; exact h.h0
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [getD_set_ne (by omega)]; exact h.h1
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [getD_set_ne (by omega)]; exact h.off i hi
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [getD_set_ne (by omega)]; exact h.last

/-! ### The prefix sums -/

/-- `if i < n then a[3 + i] := a[2 + i] + deg[i] else a[3 + i] := a[2 + i]; i := i + 1`. -/
def prefixThen : Com :=
  .store "a" (.add (.lit 3) (.var "i"))
    (.add (.get "a" (.add (.lit 2) (.var "i"))) (.get "deg" (.var "i")))

def prefixElse : Com := .store "a" (.add (.lit 3) (.var "i")) (.get "a" (.add (.lit 2) (.var "i")))

def prefixBody : Com :=
  .seq (.ite (.lt (.var "i") (.var "n")) prefixThen prefixElse)
    (.assign "i" (.add (.var "i") (.lit 1)))

/-- The header, the offsets by prefix sums, the last entry. -/
def prefixCom : Com :=
  .seq (.store "a" (.lit 0) (.var "V"))
    (.seq (.store "a" (.lit 1) (.var "E"))
      (.seq (.store "a" (.lit 2) (.lit 0))
        (.seq (.seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") (.var "V")) prefixBody))
          (.store "a" (.add (.add (.lit 3) (.var "V")) (.mul (.lit 2) (.var "E"))) (.var "n")))))

/-- The degrees in `deg`. -/
def DegOK (x : List ℕ) (σ : Env) : Prop :=
  (σ.arrs "deg").length = nw x ∧ ∀ l < nw x, (σ.arrs "deg").getD l 0 = deg x l

/-- The invariant of the prefix loop. -/
structure PreInv (x : List ℕ) (σ : Env) : Prop where
  base : Base x σ
  deg : DegOK x σ
  len : (σ.arrs "a").length = x.length
  h0 : (σ.arrs "a").getD 0 0 = Vw x
  h1 : (σ.arrs "a").getD 1 0 = x.getD 1 0
  i_le : σ.vars "i" ≤ Vw x
  off : ∀ i ≤ σ.vars "i", (σ.arrs "a").getD (2 + i) 0 = offS x i

theorem prefixBody_spec {x : List ℕ} (hw : WellFormed x) (hB : 8 * x.length + 40 ≤ B) :
    Spec B (fun σ => PreInv x σ ∧ σ.vars "i" < Vw x) prefixBody
      (fun σ σ' => PreInv x σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 24 := by
  rintro σ ⟨hPre, hlt⟩
  have hb := hPre.base
  obtain ⟨hlenD, hdeg⟩ := hPre.deg
  have hlen := hPre.len
  have h0 := hPre.h0
  have h1 := hPre.h1
  have hi := hPre.i_le
  have hoff := hPre.off
  have hxlen := wf_len hw
  have hoffn := wf_offS_n hw
  have hn := hb.n
  set i := σ.vars "i" with hidef
  have hie : (Expr.var "i").evalB B σ = some i := RunStep.eval_var B σ "i" (by omega)
  have hne : (Expr.var "n").evalB B σ = some (nw x) := by
    rw [← hn]; exact RunStep.eval_var B σ "n" (by rw [hn]; have := wf_nV hw; omega)
  have hidx : (Expr.add (.lit 3) (.var "i")).evalB B σ = some (3 + i) :=
    RunStep.eval_add B σ _ _ _ _ (RunStep.eval_lit B 3 σ (by omega)) hie (by omega)
  have hoffi : (σ.arrs "a").getD (2 + i) 0 = offS x i := hoff i le_rfl
  have hoffB : offS x i < B := by have := offS_le_n x i; omega
  have hread : (Expr.get "a" (.add (.lit 2) (.var "i"))).evalB B σ = some (offS x i) := by
    rw [← hoffi]
    exact RunStep.eval_get B σ "a" _ _
      (RunStep.eval_add B σ _ _ _ _ (RunStep.eval_lit B 2 σ (by omega)) hie (by omega))
      (by omega) (by rw [hoffi]; exact hoffB)
  have hinc : ∀ (τ : Env) (v : ℕ), Run B (.assign "i" (.add (.var "i") (.lit 1)))
      (σ.setArr "a" (3 + i) v) ((σ.setArr "a" (3 + i) v).setVar "i" (i + 1)) 4 := fun τ v =>
    RunStep.assign B _ "i" _ _ (RunStep.eval_add B _ (.var "i") (.lit 1) _ _
      (RunStep.eval_var B _ "i" (by simp; omega)) (RunStep.eval_lit B 1 _ (by omega)) (by omega))
  have hpost : ∀ v, v = offS x (i + 1) →
      PreInv x ((σ.setArr "a" (3 + i) v).setVar "i" (i + 1)) := by
    intro v hv
    refine ⟨(hb.setArr (by decide) _ _).setVar "i" (by simp) _, ⟨by simpa using hlenD,
      by simpa using hdeg⟩, by simp [hlen], ?_, ?_, by simp; omega, fun i' hi' => ?_⟩
    · simp only [arrs_setVar, arrs_setArr, String.reduceEq, ↓reduceIte]
      rw [getD_set_ne (by omega)]; exact h0
    · simp only [arrs_setVar, arrs_setArr, String.reduceEq, ↓reduceIte]
      rw [getD_set_ne (by omega)]; exact h1
    · simp only [arrs_setVar, arrs_setArr, String.reduceEq, ↓reduceIte, vars_setVar] at hi' ⊢
      by_cases hii : i' = i + 1
      · subst hii
        rw [show 2 + (i + 1) = 3 + i by omega, getD_set_self (by omega), hv]
      · rw [getD_set_ne (by omega)]; exact hoff i' (by omega)
  by_cases hin : i < nw x
  · have hc := RunStep.cond_lt_true B σ _ _ _ _ hie hne hin
    have hdegi : (σ.arrs "deg").getD i 0 = deg x i := hdeg i hin
    have hdegB : deg x i < B := by have := deg_le_n x hin; omega
    have hgd : (Expr.get "deg" (.var "i")).evalB B σ = some (deg x i) := by
      rw [← hdegi]
      exact RunStep.eval_get B σ "deg" _ _ hie (by omega) (by rw [hdegi]; exact hdegB)
    have hsum := RunStep.eval_add B σ _ _ _ _ hread hgd (by
      have := offS_succ_of_lt x hin; have := offS_le_n x (i + 1); omega)
    have rs := RunStep.store B σ "a" _ _ _ _ hidx hsum (by omega)
    have rite := RunStep.ite_true B _ prefixThen prefixElse σ _ _ hc rs
    refine ⟨_, (rite.seq (hinc σ _)).mono (by simp), hpost _ (offS_succ_of_lt x hin).symm,
      by simp only [vars_setVar, ↓reduceIte]; omega⟩
  · have hc := RunStep.cond_lt_false B σ _ _ _ _ hie hne hin
    have rs := RunStep.store B σ "a" _ _ _ _ hidx hread (by omega)
    have rite := RunStep.ite_false B _ prefixThen prefixElse σ _ _ hc rs
    refine ⟨_, (rite.seq (hinc σ _)).mono (by simp), hpost _ ?_,
      by simp only [vars_setVar, ↓reduceIte]; omega⟩
    rw [offS_of_ge x (by omega), offS_of_ge x (i := i + 1) (by omega)]

/-- **The prefix sums**: from a zero `a`, the fixed cells of the symmetrized word. -/
theorem prefix_spec {x : List ℕ} (hw : WellFormed x) (hB : 8 * x.length + 40 ≤ B) :
    Spec B (fun σ => Base x σ ∧ DegOK x σ ∧ σ.arrs "a" = List.replicate x.length 0) prefixCom
      (fun _ σ' => Base x σ' ∧ DegOK x σ' ∧ FixedA x σ')
      (3 + 3 + 3 + ((24 + 4) * Vw x + 6) + 10) := by
  rintro σ ⟨hb, hdeg, ha⟩
  have hxlen := wf_len hw
  have hoffn := wf_offS_n hw
  have hnV := wf_nV hw
  have hlen : (σ.arrs "a").length = x.length := by rw [ha]; simp
  have hV := hb.V
  have hE := hb.E
  have hn := hb.n
  have hVB : Vw x < B := by omega
  have hEB : 2 * x.getD 1 0 < B := by omega
  -- the three header stores
  have r1 := RunStep.store B σ "a" (.lit 0) (.var "V") 0 (Vw x) (RunStep.eval_lit B 0 σ (by omega))
    (by rw [← hV]; exact RunStep.eval_var B σ "V" (by rw [hV]; omega)) (by omega)
  set σ₁ := σ.setArr "a" 0 (Vw x) with hσ₁
  have hE₁ : σ₁.vars "E" = x.getD 1 0 := by simp [hσ₁, hE]
  have r2 := RunStep.store B σ₁ "a" (.lit 1) (.var "E") 1 (x.getD 1 0)
    (RunStep.eval_lit B 1 σ₁ (by omega))
    (by rw [← hE₁]; exact RunStep.eval_var B σ₁ "E" (by rw [hE₁]; omega)) (by simp [hσ₁]; omega)
  set σ₂ := σ₁.setArr "a" 1 (x.getD 1 0) with hσ₂
  have r3 := RunStep.store B σ₂ "a" (.lit 2) (.lit 0) 2 0 (RunStep.eval_lit B 2 σ₂ (by omega))
    (RunStep.eval_lit B 0 σ₂ (by omega)) (by simp [hσ₂, hσ₁]; omega)
  set σ₃ := σ₂.setArr "a" 2 0 with hσ₃
  -- the loop
  have hloop := Spec.forRangeZero (B := B) (c := prefixBody) "i" "V" (PreInv x) (Vw x) 24 hVB
    (fun σ hσ => hσ.i_le) (fun σ hσ => hσ.base.V) (prefixBody_spec hw hB)
  have hb₃ : Base x σ₃ := ((hb.setArr (by decide) _ _).setArr (by decide) _ _).setArr (by decide) _ _
  have hdeg₃ : DegOK x σ₃ := by simpa [DegOK, hσ₃, hσ₂, hσ₁] using hdeg
  obtain ⟨σ₄, r4, hPost₄, hi₄⟩ := hloop.run (σ := σ₃) (by
    refine ⟨hb₃.setVar "i" (by simp) 0, by simpa [DegOK] using hdeg₃, by simp [hσ₃, hσ₂, hσ₁, hlen],
      ?_, ?_, by simp, fun i hi => ?_⟩
    · simp only [arrs_setVar, hσ₃, hσ₂, hσ₁, arrs_setArr, String.reduceEq, ↓reduceIte]
      rw [getD_set_ne (i := 2) (j := 0) (by decide), getD_set_ne (i := 1) (j := 0) (by decide),
        getD_set_self (by omega)]
    · simp only [arrs_setVar, hσ₃, hσ₂, hσ₁, arrs_setArr, String.reduceEq, ↓reduceIte]
      rw [getD_set_ne (i := 2) (j := 1) (by decide), getD_set_self (by simp only [List.length_set]; omega)]
    · simp only [vars_setVar, String.reduceEq, ↓reduceIte] at hi
      have : i = 0 := by omega
      subst this
      simp only [arrs_setVar, hσ₃, hσ₂, hσ₁, arrs_setArr, String.reduceEq, ↓reduceIte]
      rw [getD_set_self (by simp only [List.length_set]; omega), offS_zero])
  have hb₄ := hPost₄.base
  have hdeg₄ := hPost₄.deg
  have hlen₄ := hPost₄.len
  have h0₄ := hPost₄.h0
  have h1₄ := hPost₄.h1
  have hoff₄ := hPost₄.off
  rw [hi₄] at hoff₄
  -- the last entry
  have hV₄ := hb₄.V
  have hE₄ := hb₄.E
  have hn₄ := hb₄.n
  have hidx : (Expr.add (.add (.lit 3) (.var "V")) (.mul (.lit 2) (.var "E"))).evalB B σ₄ =
      some (3 + Vw x + 2 * x.getD 1 0) := by
    have hVe : (Expr.var "V").evalB B σ₄ = some (Vw x) := by
      rw [← hV₄]; exact RunStep.eval_var B σ₄ "V" (by rw [hV₄]; omega)
    have hEe : (Expr.var "E").evalB B σ₄ = some (x.getD 1 0) := by
      rw [← hE₄]; exact RunStep.eval_var B σ₄ "E" (by rw [hE₄]; omega)
    exact RunStep.eval_add B σ₄ _ _ _ _
      (RunStep.eval_add B σ₄ _ _ _ _ (RunStep.eval_lit B 3 σ₄ (by omega)) hVe (by omega))
      (RunStep.eval_mul B σ₄ _ _ _ _ (RunStep.eval_lit B 2 σ₄ (by omega)) hEe hEB) (by omega)
  have r5 := RunStep.store B σ₄ "a" _ (.var "n") _ (nw x) hidx
    (by rw [← hn₄]; exact RunStep.eval_var B σ₄ "n" (by rw [hn₄]; omega)) (by omega)
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by
    simp only [size_lit, size_var, size_add, size_mul, size_bin, Expr.add_def, Expr.mul_def]
    omega), hb₄.setArr (by decide) _ _,
    by simpa [DegOK] using hdeg₄, ⟨by simp [hlen₄], ?_, ?_, fun i hi => ?_, ?_⟩⟩
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [getD_set_ne (by omega)]; exact h0₄
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [getD_set_ne (by omega)]; exact h1₄
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [getD_set_ne (by omega)]; exact hoff₄ i hi
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [getD_set_self (by omega)]

/-! ### The cursors -/

/-- `l := 0; while l < n do pos[l] := a[2 + l]; l := l + 1`. -/
def posBody : Com :=
  .seq (.store "pos" (.var "l") (.get "a" (.add (.lit 2) (.var "l"))))
    (.assign "l" (.add (.var "l") (.lit 1)))

def posCom : Com := .seq (.assign "l" (.lit 0)) (.while (.lt (.var "l") (.var "n")) posBody)

/-- The cursors at the offsets. -/
def PosOK (x : List ℕ) (σ : Env) : Prop :=
  (σ.arrs "pos").length = nw x ∧ ∀ l < nw x, (σ.arrs "pos").getD l 0 = offS x l

structure PosInv (x : List ℕ) (σ : Env) : Prop where
  base : Base x σ
  fixed : FixedA x σ
  lenP : (σ.arrs "pos").length = nw x
  l_le : σ.vars "l" ≤ nw x
  pos : ∀ l < σ.vars "l", (σ.arrs "pos").getD l 0 = offS x l

theorem posBody_spec {x : List ℕ} (hw : WellFormed x) (hB : 8 * x.length + 40 ≤ B) :
    Spec B (fun σ => PosInv x σ ∧ σ.vars "l" < nw x) posBody
      (fun σ σ' => PosInv x σ' ∧ σ'.vars "l" = σ.vars "l" + 1) 12 := by
  rintro σ ⟨hPos, hlt⟩
  have hb := hPos.base
  have hf := hPos.fixed
  have hlenP := hPos.lenP
  have hl := hPos.l_le
  have hpos := hPos.pos
  have hxlen := wf_len hw
  have hoffn := wf_offS_n hw
  have hnV := wf_nV hw
  have hlenA := hf.len
  set l := σ.vars "l" with hldef
  have hle : (Expr.var "l").evalB B σ = some l := RunStep.eval_var B σ "l" (by omega)
  have hoffl : (σ.arrs "a").getD (2 + l) 0 = offS x l := hf.off l (by omega)
  have hoffB : offS x l < B := by have := offS_le_n x l; omega
  have hread : (Expr.get "a" (.add (.lit 2) (.var "l"))).evalB B σ = some (offS x l) := by
    rw [← hoffl]
    exact RunStep.eval_get B σ "a" _ _
      (RunStep.eval_add B σ _ _ _ _ (RunStep.eval_lit B 2 σ (by omega)) hle (by omega))
      (by omega) (by rw [hoffl]; exact hoffB)
  have rs := RunStep.store B σ "pos" _ _ _ _ hle hread (by omega)
  set σ₁ := σ.setArr "pos" l (offS x l) with hσ₁
  have ri := RunStep.assign B σ₁ "l" (.add (.var "l") (.lit 1)) (l + 1)
    (RunStep.eval_add B σ₁ (.var "l") (.lit 1) _ _ (RunStep.eval_var B σ₁ "l" (by simp [hσ₁]; omega))
      (RunStep.eval_lit B 1 σ₁ (by omega)) (by omega))
  refine ⟨_, (rs.seq ri).mono (by simp), ⟨(hb.setArr (by decide) _ _).setVar "l" (by simp) _,
    hf.congr (by simp [hσ₁]), by simp [hσ₁, hlenP], by simp; omega, fun l' hl' => ?_⟩,
    by simp only [vars_setVar, ↓reduceIte]; omega⟩
  simp only [vars_setVar, String.reduceEq, ↓reduceIte, hσ₁, arrs_setVar, arrs_setArr] at hl' ⊢
  by_cases hll : l' = l
  · subst hll; rw [getD_set_self (by omega)]
  · rw [getD_set_ne (Ne.symm hll)]; exact hpos l' (by omega)

theorem pos_spec {x : List ℕ} (hw : WellFormed x) (hB : 8 * x.length + 40 ≤ B) :
    Spec B (fun σ => Base x σ ∧ FixedA x σ ∧ (σ.arrs "pos").length = nw x) posCom
      (fun _ σ' => Base x σ' ∧ FixedA x σ' ∧ PosOK x σ') ((12 + 4) * nw x + 6) := by
  have hnB : nw x < B := by have := wf_nV hw; have := wf_len hw; omega
  have hloop := Spec.forRangeZero (B := B) (c := posBody) "l" "n" (PosInv x) (nw x) 12 hnB
    (fun σ hσ => hσ.l_le) (fun σ hσ => hσ.base.n) (posBody_spec hw hB)
  refine hloop.conseq ?_ ?_ le_rfl
  · rintro σ ⟨hb, hf, hlenP⟩
    exact ⟨hb.setVar "l" (by simp) 0, hf.congr rfl, by simpa using hlenP, by simp,
      fun l hl => by simp at hl⟩
  · rintro σ σ' - ⟨hPos, hl⟩
    have hb := hPos.base
    have hf := hPos.fixed
    have hlenP := hPos.lenP
    have hpos := hPos.pos
    rw [hl] at hpos
    exact ⟨hb, hf, hlenP, hpos⟩

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.SymmFill` -/

section
/-!
The symmetrized word built in `a`, second half: the fill pass — for every slot `(u, j)` the
value (the target for a left row, `u` for a right row) is written at the cursor of its
destination. After the pass `a` holds `sx x` (`ArrOK (sx x)`).
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteDecision
open scoped Classical

variable {B : ℕ}

/-! ### The fill pass -/

/-- The invariant of the fill pass, over the slots `P` visited so far. -/
structure FillInv (x : List ℕ) (P : List (ℕ × ℕ)) (σ : Env) : Prop where
  hfixed : FixedA x σ
  hlenP : (σ.arrs "pos").length = nw x
  hpos : ∀ l < nw x, (σ.arrs "pos").getD l 0 = offS x l + (seg x l P).length
  hseg : ∀ l < nw x, ∀ k < (seg x l P).length,
    (σ.arrs "a").getD (3 + Vw x + offS x l + k) 0 = (seg x l P).getD k 0

theorem FillInv.setVar {x : List ℕ} {P : List (ℕ × ℕ)} {σ : Env} (h : FillInv x P σ) (y : String)
    (v : ℕ) : FillInv x P (σ.setVar y v) :=
  ⟨h.hfixed.congr rfl, h.hlenP, h.hpos, h.hseg⟩

/-- The segment of a slot's destination is not yet full when the slot is reached. -/
theorem seg_length_lt_deg (x : List ℕ) {P Q : List (ℕ × ℕ)} {p : ℕ × ℕ}
    (hpre : allPairs x = P ++ [p] ++ Q) :
    (seg x (dest x p) P).length < deg x (dest x p) := by
  have hpre' : allPairs x = (P ++ [p]) ++ Q := by rw [hpre]
  have := length_seg_le x (l := dest x p) hpre'
  rw [seg_append, seg_single, if_pos rfl, List.length_append, List.length_singleton] at this
  omega

/-- **One slot placed.** -/
theorem FillInv.step {x : List ℕ} {P Q : List (ℕ × ℕ)} {σ : Env} (hw : WellFormed x)
    (h : FillInv x P σ) (p : ℕ × ℕ) (hpre : allPairs x = P ++ [p] ++ Q) (hd : dest x p < nw x) :
    FillInv x (P ++ [p])
      ((σ.setArr "a" (3 + Vw x + (offS x (dest x p) + (seg x (dest x p) P).length)) (val x p)).setArr
        "pos" (dest x p) (offS x (dest x p) + (seg x (dest x p) P).length + 1)) := by
  have hoffn := wf_offS_n hw
  have hxlen := wf_len hw
  set d := dest x p with hddef
  set k := (seg x d P).length with hkdef
  have hpre' : allPairs x = (P ++ [p]) ++ Q := by rw [hpre]
  have hpreP : allPairs x = P ++ ([p] ++ Q) := by rw [hpre, List.append_assoc]
  have hlenP' : ∀ l, (seg x l (P ++ [p])).length ≤ deg x l := fun l => length_seg_le x hpre'
  have hsegle : ∀ l, (seg x l P).length ≤ deg x l := fun l => length_seg_le x hpreP
  have hsegd : seg x d (P ++ [p]) = seg x d P ++ [val x p] := by
    rw [seg_append, seg_single, if_pos rfl]
  have hsego : ∀ l, l ≠ d → seg x l (P ++ [p]) = seg x l P := fun l hl => by
    rw [seg_append, seg_single, if_neg (Ne.symm hl), List.append_nil]
  have hk : k < deg x d := seg_length_lt_deg x hpre
  have hkE : offS x d + k < offS x (nw x) := by
    have := offS_succ_of_lt x hd; have := offS_le_n x (d + 1); omega
  have hlenA := h.hfixed.len
  have hlenP := h.hlenP
  refine ⟨?_, by simp [h.hlenP], fun l hl => ?_, fun l hl k' hk' => ?_⟩
  · refine (h.hfixed.setTgt hw (s := offS x d + k) (v := val x p) (by omega)).congr ?_
    simp
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    by_cases hld : l = d
    · subst hld
      rw [getD_set_self (by omega), hsegd, List.length_append, List.length_singleton]
      omega
    · rw [getD_set_ne (Ne.symm hld), hsego l hld]; exact h.hpos l hl
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    by_cases hld : l = d
    · subst hld
      rw [hsegd, List.length_append, List.length_singleton] at hk'
      rcases Nat.lt_or_ge k' k with hlt | hge
      · rw [getD_set_ne (by omega), hsegd, getD_app_left hlt]
        exact h.hseg d hl k' hlt
      · have : k' = k := by omega
        subst this
        have hk0 : k - (seg x d P).length = 0 := by omega
        rw [show 3 + Vw x + offS x d + k = 3 + Vw x + (offS x d + k) by omega,
          getD_set_self (by omega), hsegd, getD_app_right (by omega), hk0]
        rfl
    · rw [hsego l hld] at hk' ⊢
      have hkl : k' < deg x l := lt_of_lt_of_le hk' (hsegle l)
      have hne : 3 + Vw x + (offS x d + k) ≠ 3 + Vw x + offS x l + k' := by
        rcases Nat.lt_or_ge l d with h1 | h1
        · have := offS_succ_of_lt x hl
          have := offS_mono x (i := l + 1) (i' := d) h1
          omega
        · have h2 : d < l := lt_of_le_of_ne h1 (Ne.symm hld)
          have := offS_succ_of_lt x hd
          have := offS_mono x (i := d + 1) (i' := l) h2
          omega
      rw [getD_set_ne hne]
      exact h.hseg l hl k' hk'

/-- `tt := t[3 + V + j]; if u < n then (a[3 + V + pos[u]] := tt; pos[u]++) else
(a[3 + V + pos[tt]] := u; pos[tt]++)`. -/
def fillThen : Com :=
  .seq (.store "a" (.add (.add (.lit 3) (.var "V")) (.get "pos" (.var "u"))) (.var "tt"))
    (.store "pos" (.var "u") (.add (.get "pos" (.var "u")) (.lit 1)))

def fillElse : Com :=
  .seq (.store "a" (.add (.add (.lit 3) (.var "V")) (.get "pos" (.var "tt"))) (.var "u"))
    (.store "pos" (.var "tt") (.add (.get "pos" (.var "tt")) (.lit 1)))

def fillBody : Com :=
  .seq (.assign "tt" (.get "t" (.add (.add (.lit 3) (.var "V")) (.var "j"))))
    (.ite (.lt (.var "u") (.var "n")) fillThen fillElse)

theorem fillBody_wvars : ∀ y ∈ fillBody.wvars, y ∉ ["u", "j", "je"] := by
  intro y hy
  simp [fillBody, fillThen, fillElse, Com.wvars] at hy
  subst hy; simp

theorem fillBody_spec {x : List ℕ} (hw : WellFormed x) (hB : 8 * x.length + 40 ≤ B) {u j : ℕ}
    (hu : u < Vw x) (hj1 : offw x u ≤ j) (hj2 : j < offw x (u + 1)) :
    Spec B (fun σ => FillInv x (pairsAt x u j) σ ∧ Base x σ ∧ σ.vars "u" = u ∧ σ.vars "j" = j)
      fillBody (fun _ σ' => FillInv x (pairsAt x u (j + 1)) σ' ∧ Base x σ') 40 := by
  rintro σ ⟨hI, hb, hu', hj'⟩
  have h3 := (wellFormed_iff.1 hw).1
  have hxlen := wf_len hw
  have hoffn := wf_offS_n hw
  have hnV := wf_nV hw
  have hlenT := hb.tab.length
  have hV := hb.V
  have hn := hb.n
  have hj2E : j < 2 * x.getD 1 0 := lt_of_lt_of_le hj2 (h3.off_le hu)
  have hg : (σ.arrs "t").getD (3 + Vw x + j) 0 = tgtw x j := hb.tab.getD (by omega)
  have htV : tgtw x j < Vw x := h3.tgt_lt j hj2E
  have hcross := wf_cross hw hu hj1 hj2
  have hlenA := hI.hfixed.len
  have hlenP := hI.hlenP
  set p : ℕ × ℕ := (u, j) with hp
  have hstep : pairsAt x u (j + 1) = pairsAt x u j ++ [p] := pairsAt_succ x hj1
  obtain ⟨Q, hQ⟩ := pairsAt_prefix x u (j + 1) hu hj2
  rw [hstep] at hQ
  have hd : dest x p < nw x := wf_dest_lt hw (by rw [hQ]; simp)
  -- tt := t[3 + V + j]
  have hVe : (Expr.var "V").evalB B σ = some (Vw x) := by
    rw [← hV]; exact RunStep.eval_var B σ "V" (by omega)
  have hje : (Expr.var "j").evalB B σ = some j := by
    rw [← hj']; exact RunStep.eval_var B σ "j" (by rw [hj']; omega)
  have hidx := RunStep.eval_add B σ _ _ _ _
    (RunStep.eval_add B σ _ _ _ _ (RunStep.eval_lit B 3 σ (by omega)) hVe (by omega)) hje (by omega)
  have r1 := RunStep.assign B σ "tt" _ _ (RunStep.eval_get B σ "t" _ _ hidx (by omega)
    (by rw [hg]; omega))
  rw [hg] at r1
  set σ₁ := σ.setVar "tt" (tgtw x j) with hσ₁
  have hI₁ : FillInv x (pairsAt x u j) σ₁ := hI.setVar "tt" _
  have hb₁ : Base x σ₁ := hb.setVar "tt" (by simp) _
  have hu₁ : σ₁.vars "u" = u := by simp [hσ₁, hu']
  have hn₁ : σ₁.vars "n" = nw x := by simp [hσ₁, hn]
  have htt₁ : σ₁.vars "tt" = tgtw x j := by simp [hσ₁]
  have hV₁ : σ₁.vars "V" = Vw x := by simp [hσ₁, hV]
  have hue : (Expr.var "u").evalB B σ₁ = some u := by
    rw [← hu₁]; exact RunStep.eval_var B σ₁ "u" (by rw [hu₁]; omega)
  have hne : (Expr.var "n").evalB B σ₁ = some (nw x) := by
    rw [← hn₁]; exact RunStep.eval_var B σ₁ "n" (by rw [hn₁]; omega)
  have htte : (Expr.var "tt").evalB B σ₁ = some (tgtw x j) := by
    rw [← htt₁]; exact RunStep.eval_var B σ₁ "tt" (by rw [htt₁]; omega)
  have hVe₁ : (Expr.var "V").evalB B σ₁ = some (Vw x) := by
    rw [← hV₁]; exact RunStep.eval_var B σ₁ "V" (by rw [hV₁]; omega)
  have hlenA₁ : (σ₁.arrs "a").length = x.length := by simp [hσ₁, hlenA]
  have hlenP₁ : (σ₁.arrs "pos").length = nw x := by simp [hσ₁, hlenP]
  -- the two stores, for a destination `d` held in `y` and a value `v` held in `z`
  have hplace : ∀ (y z : String) (d v : ℕ), σ₁.vars y = d → σ₁.vars z = v → d < nw x → v < B →
      (seg x d (pairsAt x u j)).length < deg x d →
      Run B (.seq (.store "a" (.add (.add (.lit 3) (.var "V")) (.get "pos" (.var y))) (.var z))
        (.store "pos" (.var y) (.add (.get "pos" (.var y)) (.lit 1)))) σ₁
        ((σ₁.setArr "a" (3 + Vw x + (offS x d + (seg x d (pairsAt x u j)).length)) v).setArr
          "pos" d (offS x d + (seg x d (pairsAt x u j)).length + 1)) 20 := by
    intro y z d v hy hz hdn hvB hkd'
    have hoff1 := offS_succ_of_lt x hdn
    have hoff2 := offS_le_n x (d + 1)
    have hposd : (σ₁.arrs "pos").getD d 0 = offS x d + (seg x d (pairsAt x u j)).length := by
      simp only [hσ₁, arrs_setVar]; exact hI.hpos d hdn
    have hkd : (seg x d (pairsAt x u j)).length ≤ deg x d := length_seg_le x (by rw [hQ, List.append_assoc])
    have hposB : offS x d + (seg x d (pairsAt x u j)).length + 1 < B := by
      have := offS_succ_of_lt x hdn; have := offS_le_n x (d + 1); omega
    have hye : (Expr.var y).evalB B σ₁ = some d := by
      rw [← hy]; exact RunStep.eval_var B σ₁ y (by rw [hy]; omega)
    have hze : (Expr.var z).evalB B σ₁ = some v := by
      rw [← hz]; exact RunStep.eval_var B σ₁ z (by rw [hz]; exact hvB)
    have hgp : (Expr.get "pos" (.var y)).evalB B σ₁ =
        some (offS x d + (seg x d (pairsAt x u j)).length) := by
      rw [← hposd]
      exact RunStep.eval_get B σ₁ "pos" _ _ hye (by omega) (by rw [hposd]; omega)
    have hidxA := RunStep.eval_add B σ₁ _ _ _ _
      (RunStep.eval_add B σ₁ _ _ _ _ (RunStep.eval_lit B 3 σ₁ (by omega)) hVe₁ (by omega)) hgp
      (by omega)
    have rA := RunStep.store B σ₁ "a" _ _ _ _ hidxA hze (by
      show 3 + Vw x + (offS x d + (seg x d (pairsAt x u j)).length) < (σ₁.arrs "a").length
      have h1 := offS_succ_of_lt x hdn
      have h2 := offS_le_n x (d + 1)
      omega)
    set σ₂ := σ₁.setArr "a" (3 + Vw x + (offS x d + (seg x d (pairsAt x u j)).length)) v with hσ₂
    have hye₂ : (Expr.var y).evalB B σ₂ = some d := by simpa [hσ₂] using hye
    have hposd₂ : (σ₂.arrs "pos").getD d 0 = offS x d + (seg x d (pairsAt x u j)).length := by
      simpa [hσ₂] using hposd
    have hgp₂ : (Expr.get "pos" (.var y)).evalB B σ₂ =
        some (offS x d + (seg x d (pairsAt x u j)).length) := by
      rw [← hposd₂]
      exact RunStep.eval_get B σ₂ "pos" _ _ hye₂ (by simp [hσ₂]; omega) (by rw [hposd₂]; omega)
    have hsum := RunStep.eval_add B σ₂ _ _ _ _ hgp₂ (RunStep.eval_lit B 1 σ₂ (by omega)) hposB
    have rP := RunStep.store B σ₂ "pos" _ _ _ _ hye₂ hsum (by simp [hσ₂]; omega)
    exact (rA.seq rP).mono (by simp)
  by_cases hun : u < nw x
  · have hc := RunStep.cond_lt_true B σ₁ _ _ _ _ hue hne hun
    have hdest : dest x p = u := by unfold dest; simp [hp, hun]
    have hval : val x p = tgtw x j := by unfold val; simp [hp, hun]
    have rr := hplace "u" "tt" u (tgtw x j) hu₁ htt₁ hun (by omega)
      (by have := seg_length_lt_deg x hQ; rwa [hdest] at this)
    have rite := RunStep.ite_true B _ fillThen fillElse σ₁ _ _ hc rr
    refine ⟨_, (r1.seq rite).mono (by simp), ?_, (hb₁.setArr (by decide) _ _).setArr (by decide) _ _⟩
    rw [hstep]
    have := hI₁.step hw p hQ hd
    rw [hdest, hval] at this
    exact this
  · have hc := RunStep.cond_lt_false B σ₁ _ _ _ _ hue hne hun
    have hdest : dest x p = tgtw x j := by unfold dest; simp [hp, hun]
    have hval : val x p = u := by unfold val; simp [hp, hun]
    have htn : tgtw x j < nw x := by rw [hdest] at hd; exact hd
    have rr := hplace "tt" "u" (tgtw x j) u htt₁ hu₁ htn (by omega)
      (by have := seg_length_lt_deg x hQ; rwa [hdest] at this)
    have rite := RunStep.ite_false B _ fillThen fillElse σ₁ _ _ hc rr
    refine ⟨_, (r1.seq rite).mono (by simp), ?_, (hb₁.setArr (by decide) _ _).setArr (by decide) _ _⟩
    rw [hstep]
    have := hI₁.step hw p hQ hd
    rw [hdest, hval] at this
    exact this

/-- **The fill pass.** -/
def fillPass : Com := rowIter fillBody

/-- **After the fill pass, `a` holds the symmetrized word.** -/
theorem fillPass_spec {x : List ℕ} (hw : WellFormed x) (hB : 8 * x.length + 40 ≤ B) :
    Spec B (fun σ => Base x σ ∧ FixedA x σ ∧ PosOK x σ) fillPass
      (fun _ σ' => Base x σ' ∧ ArrOK (sx x) σ')
      ((40 + 8) * (2 * x.getD 1 0) + 22 * Vw x + 6) := by
  have h3 := (wellFormed_iff.1 hw).1
  have hspec := rowIter_spec (Inv := FillInv x) h3 hB fillBody 40 fillBody_wvars
    (fun P σ y v _ hI => hI.setVar y v) (fun u j hu hj1 hj2 => fillBody_spec hw hB hu hj1 hj2)
  refine hspec.conseq ?_ ?_ le_rfl
  · rintro σ ⟨hb, hf, hlenP, hpos⟩
    exact ⟨⟨hf, hlenP, fun l hl => by rw [hpos l hl, seg_nil]; rfl,
      fun l hl k hk => by rw [seg_nil] at hk; simp at hk⟩, hb⟩
  · rintro σ σ' - ⟨hI, hb⟩
    refine ⟨hb, ?_⟩
    have hxlen := wf_len hw
    have hoffn := wf_offS_n hw
    have hlen' := wf_length_sx hw
    unfold ArrOK
    rw [hlen', ← hI.hfixed.len]
    refine List.ext_getElem (by simp) (fun t ht₁ ht₂ => ?_)
    have ht : t < x.length := by rwa [hI.hfixed.len] at ht₁
    have e1 : (σ'.arrs "a")[t] = (σ'.arrs "a").getD t 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht₁]; rfl
    have e2 : (arrOf (σ'.arrs "a").length (fun t => (sx x).getD t 0))[t] = (sx x).getD t 0 := by
      have := getD_arrOf (n := (σ'.arrs "a").length) (fun t => (sx x).getD t 0) ht₁
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht₂] at this
      exact this
    rw [e1, e2]
    -- by cases on the position
    rcases Nat.lt_or_ge t 2 with h2 | h2
    · interval_cases t
      · rw [hI.hfixed.h0]; rfl
      · rw [hI.hfixed.h1]; rfl
    rcases Nat.lt_or_ge t (3 + Vw x) with h3' | h3'
    · have e : t = 2 + (t - 2) := by omega
      rw [e, hI.hfixed.off (t - 2) (by omega), sx_off x (by omega)]
    rcases Nat.lt_or_ge t (3 + Vw x + 2 * x.getD 1 0) with h4 | h4
    · have e : t = 3 + Vw x + (t - 3 - Vw x) := by omega
      have hs : t - 3 - Vw x < offS x (nw x) := by omega
      rw [e, sx_tgt x hs]
      obtain ⟨l, hl, hl1, hl2⟩ := exists_owner x hs
      rw [offS_succ_of_lt x hl] at hl2
      have e2 : t - 3 - Vw x = offS x l + (t - 3 - Vw x - offS x l) := by omega
      rw [e2, tgtS_seg x hl (by omega), ← Nat.add_assoc]
      exact hI.hseg l hl _ (by unfold deg at *; omega)
    · have e : t = 3 + Vw x + 2 * x.getD 1 0 := by omega
      rw [e, hI.hfixed.last, ← hoffn, sx_last]

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.Checks` -/

section
/-!
The three syntactic checks of the validator, each a `Spec` on the flag `ok`: `n ≤ V` and the
length (`chk1`), the offsets (`chk2`), the targets (`chk3`). Every array read of a later check is
in range once the earlier ones passed; a failed check clears the flag.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteDecision
open scoped Classical

variable {B : ℕ}

/-! ### The checks -/

/-- A guard clearing the flag: `if b then ok := 0 else skip`. -/
theorem okGuard_run {σ : Env} {b : Cond} {v : Bool} (hb : b.evalB B σ = some v) (h0 : 0 < B) :
    Run B (.ite b (.assign "ok" (.lit 0)) .skip) σ (if v then σ.setVar "ok" 0 else σ)
      (1 + b.size + 2) := by
  cases v
  · exact RunStep.ite_false B b _ .skip σ σ 2 hb ((RunStep.skip B σ).mono (by omega))
  · exact RunStep.ite_true B b _ .skip σ _ 2 hb
      (RunStep.assign B σ "ok" (.lit 0) 0 (RunStep.eval_lit B 0 σ h0))

/-- A guard keeping the flag: `if b then skip else ok := 0`. -/
theorem okGuard_run' {σ : Env} {b : Cond} {v : Bool} (hb : b.evalB B σ = some v) (h0 : 0 < B) :
    Run B (.ite b .skip (.assign "ok" (.lit 0))) σ (if v then σ else σ.setVar "ok" 0)
      (1 + b.size + 2) := by
  cases v
  · exact RunStep.ite_false B b .skip _ σ _ 2 hb
      (RunStep.assign B σ "ok" (.lit 0) 0 (RunStep.eval_lit B 0 σ h0))
  · exact RunStep.ite_true B b .skip _ σ σ 2 hb ((RunStep.skip B σ).mono (by omega))

/-- The flag after a guard: `1` exactly when it was `1` and the guard did not fire. -/
theorem ok_ite {σ : Env} (v : Bool) :
    (if v then σ.setVar "ok" 0 else σ).vars "ok" = if v then 0 else σ.vars "ok" := by
  cases v <;> simp

theorem ok_ite' {σ : Env} (v : Bool) :
    (if v then σ else σ.setVar "ok" 0).vars "ok" = if v then σ.vars "ok" else 0 := by
  cases v <;> simp

theorem base_ite {x : List ℕ} {σ : Env} (hb : Base x σ) (v : Bool) :
    Base x (if v then σ.setVar "ok" 0 else σ) := by
  cases v
  · exact hb
  · exact hb.setVar "ok" (by simp) 0

theorem base_ite' {x : List ℕ} {σ : Env} (hb : Base x σ) (v : Bool) :
    Base x (if v then σ else σ.setVar "ok" 0) := by
  cases v
  · exact hb.setVar "ok" (by simp) 0
  · exact hb

theorem vars_ite {σ : Env} (v : Bool) (y : String) (hy : y ≠ "ok") :
    (if v then σ.setVar "ok" 0 else σ).vars y = σ.vars y := by
  cases v <;> simp [hy]

theorem vars_ite' {σ : Env} (v : Bool) (y : String) (hy : y ≠ "ok") :
    (if v then σ else σ.setVar "ok" 0).vars y = σ.vars y := by
  cases v <;> simp [hy]

theorem arrs_ite' {σ : Env} (v : Bool) : (if v then σ else σ.setVar "ok" 0).arrs = σ.arrs := by
  cases v <;> rfl

/-- `if V < n then ok := 0; if len = 4 + V + 2E then skip else ok := 0`. -/
def chk1 : Com :=
  .seq (.ite (.lt (.var "V") (.var "n")) (.assign "ok" (.lit 0)) .skip)
    (.ite (.eq (.var "len") (.add (.add (.lit 4) (.var "V")) (.mul (.lit 2) (.var "E"))))
      .skip (.assign "ok" (.lit 0)))

theorem chk1_spec {x : List ℕ}
    (hB : 8 * (x.length + Vw x + x.getD 1 0 + nw x) + 40 ≤ B) :
    Spec B (fun σ => Base x σ ∧ σ.vars "ok" = 1) chk1
      (fun _ σ' => Base x σ' ∧ σ'.vars "ok" ≤ 1 ∧
        (σ'.vars "ok" = 1 ↔ nw x ≤ Vw x ∧ x.length = 4 + Vw x + 2 * x.getD 1 0)) 24 := by
  rintro σ ⟨hb, hok⟩
  have hl := hb.len
  have hV := hb.V
  have hE := hb.E
  have hn := hb.n
  have hc1 : (Cond.lt (.var "V") (.var "n")).evalB B σ = some (decide (Vw x < nw x)) := by
    have := evalB_condLt (B := B) (σ := σ) (evalB_var (x := "V") (by omega))
      (evalB_var (x := "n") (by omega))
    rwa [hV, hn] at this
  have r1 := okGuard_run hc1 (by omega)
  set σ₁ := (if decide (Vw x < nw x) then σ.setVar "ok" 0 else σ) with hσ₁
  have hb₁ : Base x σ₁ := base_ite hb _
  have hsum : (Expr.add (.add (.lit 4) (.var "V")) (.mul (.lit 2) (.var "E"))).evalB B σ₁ =
      some (4 + Vw x + 2 * x.getD 1 0) := by
    have hVe : (Expr.var "V").evalB B σ₁ = some (Vw x) := by
      rw [← hb₁.V]; exact RunStep.eval_var B σ₁ "V" (by rw [hb₁.V]; omega)
    have hEe : (Expr.var "E").evalB B σ₁ = some (x.getD 1 0) := by
      rw [← hb₁.E]; exact RunStep.eval_var B σ₁ "E" (by rw [hb₁.E]; omega)
    have h4 := RunStep.eval_add B σ₁ _ _ _ _ (RunStep.eval_lit B 4 σ₁ (by omega)) hVe (by omega)
    have h2 := RunStep.eval_mul B σ₁ _ _ _ _ (RunStep.eval_lit B 2 σ₁ (by omega)) hEe (by omega)
    exact RunStep.eval_add B σ₁ _ _ _ _ h4 h2 (by omega)
  have hc2 : Cond.evalB B (Cond.eq (.var "len")
      (.add (.add (.lit 4) (.var "V")) (.mul (.lit 2) (.var "E")))) σ₁ =
      some (decide (x.length = 4 + Vw x + 2 * x.getD 1 0)) := by
    have hle : (Expr.var "len").evalB B σ₁ = some x.length := by
      rw [← hb₁.len]; exact RunStep.eval_var B σ₁ "len" (by rw [hb₁.len]; omega)
    rw [evalB_condEq hle hsum]
    congr 1
    try (by_cases h : x.length = 4 + Vw x + 2 * x.getD 1 0 <;> simp [h])
  have r2 := okGuard_run' hc2 (by omega)
  refine ⟨_, (r1.seq r2).mono (by simp), base_ite' hb₁ _, ?_, ?_⟩
  · rw [ok_ite']; split_ifs
    · rw [hσ₁, ok_ite]; split_ifs <;> omega
    · exact Nat.zero_le _
  · rw [ok_ite', hσ₁, ok_ite, hok]
    by_cases h1 : Vw x < nw x <;> by_cases h2 : x.length = 4 + Vw x + 2 * x.getD 1 0 <;>
      simp [h1, h2] <;> omega

/-- The offsets: `t[2] = 0`, `t[2 + V] = 2E`, and `t[2 + i] ≤ t[3 + i]` for `i < V`. -/
def chk2Body : Com :=
  .seq (.ite (.lt (.get "t" (.add (.lit 3) (.var "i"))) (.get "t" (.add (.lit 2) (.var "i"))))
      (.assign "ok" (.lit 0)) .skip)
    (.assign "i" (.add (.var "i") (.lit 1)))

def chk2 : Com :=
  .seq (.ite (.eq (.get "t" (.lit 2)) (.lit 0)) .skip (.assign "ok" (.lit 0)))
    (.seq (.ite (.eq (.get "t" (.add (.lit 2) (.var "V"))) (.mul (.lit 2) (.var "E"))) .skip
        (.assign "ok" (.lit 0)))
      (.seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") (.var "V")) chk2Body)))

/-- The invariant of the offsets loop. -/
def Chk2Inv (x : List ℕ) (σ : Env) : Prop :=
  Base x σ ∧ σ.vars "i" ≤ Vw x ∧ σ.vars "ok" ≤ 1 ∧
    (σ.vars "ok" = 1 ↔ (offw x 0 = 0 ∧ offw x (Vw x) = 2 * x.getD 1 0 ∧
      ∀ i < σ.vars "i", offw x i ≤ offw x (i + 1)))

theorem chk2Body_spec {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hB : 8 * x.length + 40 ≤ B)
    (hlen : x.length = 4 + Vw x + 2 * x.getD 1 0) :
    Spec B (fun σ => Chk2Inv x σ ∧ σ.vars "i" < Vw x) chk2Body
      (fun σ σ' => Chk2Inv x σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 20 := by
  rintro σ ⟨⟨hb, hi, hok, hiff⟩, hlt⟩
  have hlenT := hb.tab.length
  have hV := hb.V
  set i := σ.vars "i" with hidef
  have hg2 : (σ.arrs "t").getD (2 + i) 0 = offw x i := hb.tab.getD (by omega)
  have hg3 : (σ.arrs "t").getD (3 + i) 0 = offw x (i + 1) := by
    rw [hb.tab.getD (by omega)]; unfold offw; congr 1; omega
  have h2B : offw x i < B := getD_lt_of_mem hx (by omega) _
  have h3B : offw x (i + 1) < B := getD_lt_of_mem hx (by omega) _
  have hiB : i + 1 < B := by omega
  have e2 : (Expr.get "t" (.add (.lit 2) (.var "i"))).evalB B σ = some (offw x i) := by
    rw [← hg2]
    exact RunStep.eval_get B σ "t" _ _ (RunStep.eval_add B σ _ _ _ _ (RunStep.eval_lit B 2 σ (by omega))
      (RunStep.eval_var B σ "i" (by omega)) (by omega)) (by omega) (by rw [hg2]; exact h2B)
  have e3 : (Expr.get "t" (.add (.lit 3) (.var "i"))).evalB B σ = some (offw x (i + 1)) := by
    rw [← hg3]
    exact RunStep.eval_get B σ "t" _ _ (RunStep.eval_add B σ _ _ _ _ (RunStep.eval_lit B 3 σ (by omega))
      (RunStep.eval_var B σ "i" (by omega)) (by omega)) (by omega) (by rw [hg3]; exact h3B)
  have hc := evalB_condLt e3 e2
  have r1 := okGuard_run hc (by omega)
  set σ₁ := (if decide (offw x (i + 1) < offw x i) then σ.setVar "ok" 0 else σ) with hσ₁
  have hi₁ : σ₁.vars "i" = i := vars_ite _ "i" (by decide)
  have r2 := RunStep.assign B σ₁ "i" (.add (.var "i") (.lit 1)) (i + 1)
    (RunStep.eval_add B σ₁ (.var "i") (.lit 1) _ _
      (by rw [← hi₁]; exact RunStep.eval_var B σ₁ "i" (by rw [hi₁]; omega))
      (RunStep.eval_lit B 1 σ₁ (by omega)) hiB)
  refine ⟨_, (r1.seq r2).mono (by simp), ⟨(base_ite hb _).setVar "i" (by simp) _,
    by simp only [vars_setVar, String.reduceEq, ↓reduceIte]; omega, ?_, ?_⟩,
    by simp only [vars_setVar, String.reduceEq, ↓reduceIte]; omega⟩
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hσ₁, ok_ite]; split_ifs <;> omega
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hσ₁, ok_ite]
    by_cases h : offw x (i + 1) < offw x i
    · rw [if_pos (by simpa using h)]
      constructor
      · intro h0; omega
      · rintro ⟨-, -, hall⟩
        exfalso
        have := hall i (by omega)
        omega
    · rw [if_neg (by simpa using h), hiff]
      constructor
      · rintro ⟨h0, hV', hall⟩
        refine ⟨h0, hV', fun i' hi' => ?_⟩
        rcases Nat.lt_or_ge i' i with h' | h'
        · exact hall i' h'
        · have : i' = i := by omega
          subst this; omega
      · rintro ⟨h0, hV', hall⟩
        exact ⟨h0, hV', fun i' hi' => hall i' (by omega)⟩

theorem chk2_spec {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hB : 8 * x.length + 40 ≤ B)
    (hlen : x.length = 4 + Vw x + 2 * x.getD 1 0) :
    Spec B (fun σ => Base x σ ∧ σ.vars "ok" = 1) chk2
      (fun _ σ' => Base x σ' ∧ σ'.vars "ok" ≤ 1 ∧
        (σ'.vars "ok" = 1 ↔ (offw x 0 = 0 ∧ offw x (Vw x) = 2 * x.getD 1 0 ∧
          ∀ i < Vw x, offw x i ≤ offw x (i + 1))))
      (16 + 16 + ((20 + 4) * Vw x + 6)) := by
  have hloop := Spec.forRangeZero (B := B) (c := chk2Body) "i" "V" (Chk2Inv x) (Vw x) 20
    (by omega) (fun σ hσ => hσ.2.1) (fun σ hσ => hσ.1.V) (chk2Body_spec hx hB hlen)
  rintro σ ⟨hb, hok⟩
  have hlenT := hb.tab.length
  have hV := hb.V
  have hE := hb.E
  have hg2 : (σ.arrs "t").getD 2 0 = offw x 0 := hb.tab.getD (by omega)
  have hgV : (σ.arrs "t").getD (2 + Vw x) 0 = offw x (Vw x) := hb.tab.getD (by omega)
  have h2B : offw x 0 < B := getD_lt_of_mem hx (by omega) _
  have hVB : offw x (Vw x) < B := getD_lt_of_mem hx (by omega) _
  have hEB : 2 * x.getD 1 0 < B := by omega
  -- `t[2] = 0`
  have e2 : (Expr.get "t" (.lit 2)).evalB B σ = some (offw x 0) := by
    rw [← hg2]
    exact RunStep.eval_get B σ "t" _ _ (RunStep.eval_lit B 2 σ (by omega)) (by omega)
      (by rw [hg2]; exact h2B)
  have hc1 := evalB_condEq e2 (RunStep.eval_lit B 0 σ (by omega))
  have r1 := okGuard_run' hc1 (by omega)
  set σ₁ := (if (offw x 0 == 0) then σ else σ.setVar "ok" 0) with hσ₁
  have hb₁ : Base x σ₁ := base_ite' hb _
  have ha₁ : σ₁.arrs = σ.arrs := arrs_ite' _
  -- `t[2 + V] = 2E`
  have eV : (Expr.get "t" (.add (.lit 2) (.var "V"))).evalB B σ₁ = some (offw x (Vw x)) := by
    have hVe : (Expr.var "V").evalB B σ₁ = some (Vw x) := by
      rw [← hb₁.V]; exact RunStep.eval_var B σ₁ "V" (by rw [hb₁.V]; omega)
    rw [← hgV, ← ha₁]
    exact RunStep.eval_get B σ₁ "t" _ _
      (RunStep.eval_add B σ₁ _ _ _ _ (RunStep.eval_lit B 2 σ₁ (by omega)) hVe (by omega))
      (by rw [ha₁]; omega) (by rw [ha₁, hgV]; exact hVB)
  have eE : (Expr.mul (.lit 2) (.var "E")).evalB B σ₁ = some (2 * x.getD 1 0) := by
    have hEe : (Expr.var "E").evalB B σ₁ = some (x.getD 1 0) := by
      rw [← hb₁.E]; exact RunStep.eval_var B σ₁ "E" (by rw [hb₁.E]; omega)
    exact RunStep.eval_mul B σ₁ _ _ _ _ (RunStep.eval_lit B 2 σ₁ (by omega)) hEe hEB
  have hc2 := evalB_condEq eV eE
  have r2 := okGuard_run' hc2 (by omega)
  set σ₂ := (if (offw x (Vw x) == 2 * x.getD 1 0) then σ₁ else σ₁.setVar "ok" 0) with hσ₂
  have hb₂ : Base x σ₂ := base_ite' hb₁ _
  -- the loop
  obtain ⟨σ₃, r3, ⟨hb₃, -, hok₃, hiff₃⟩, hi₃⟩ := hloop.run (σ := σ₂) (by
    refine ⟨hb₂.setVar "i" (by simp) 0, by simp, ?_, ?_⟩
    · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
      rw [hσ₂, ok_ite']; split_ifs
      · rw [hσ₁, ok_ite']; split_ifs <;> omega
      · exact Nat.zero_le _
    · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
      rw [hσ₂, ok_ite', hσ₁, ok_ite', hok]
      by_cases h1 : offw x 0 = 0 <;> by_cases h2 : offw x (Vw x) = 2 * x.getD 1 0 <;>
        simp [h1, h2])
  rw [hi₃] at hiff₃
  exact ⟨σ₃, (r1.seq (r2.seq r3)).mono (by simp only [size_condEq, size_get, size_lit, size_var,
    size_add, size_mul, size_bin, Expr.add_def, Expr.mul_def]; omega), hb₃, hok₃, hiff₃⟩

/-- The targets: `t[3 + V + j] < V` for `j < 2E`. -/
def chk3Body : Com :=
  .seq (.ite (.lt (.get "t" (.add (.add (.lit 3) (.var "V")) (.var "j"))) (.var "V")) .skip
      (.assign "ok" (.lit 0)))
    (.assign "j" (.add (.var "j") (.lit 1)))

def chk3 : Com :=
  .seq (.assign "e2" (.mul (.lit 2) (.var "E")))
    (.seq (.assign "j" (.lit 0)) (.while (.lt (.var "j") (.var "e2")) chk3Body))

/-- The invariant of the targets loop. -/
def Chk3Inv (x : List ℕ) (σ : Env) : Prop :=
  Base x σ ∧ σ.vars "e2" = 2 * x.getD 1 0 ∧ σ.vars "j" ≤ 2 * x.getD 1 0 ∧ σ.vars "ok" ≤ 1 ∧
    (σ.vars "ok" = 1 ↔ ∀ j < σ.vars "j", tgtw x j < Vw x)

theorem chk3Body_spec {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hB : 8 * x.length + 40 ≤ B)
    (hlen : x.length = 4 + Vw x + 2 * x.getD 1 0) :
    Spec B (fun σ => Chk3Inv x σ ∧ σ.vars "j" < 2 * x.getD 1 0) chk3Body
      (fun σ σ' => Chk3Inv x σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 20 := by
  rintro σ ⟨⟨hb, he2, hj, hok, hiff⟩, hlt⟩
  have hlenT := hb.tab.length
  have hV := hb.V
  set j := σ.vars "j" with hjdef
  have hg : (σ.arrs "t").getD (3 + Vw x + j) 0 = tgtw x j := hb.tab.getD (by omega)
  have hgB : tgtw x j < B := getD_lt_of_mem hx (by omega) _
  have hVB : Vw x < B := by omega
  have hjB : j + 1 < B := by omega
  have eg : (Expr.get "t" (.add (.add (.lit 3) (.var "V")) (.var "j"))).evalB B σ =
      some (tgtw x j) := by
    have hVe : (Expr.var "V").evalB B σ = some (Vw x) := by
      rw [← hV]; exact RunStep.eval_var B σ "V" (by omega)
    have h3 := RunStep.eval_add B σ _ _ _ _ (RunStep.eval_lit B 3 σ (by omega)) hVe (by omega)
    have h4 := RunStep.eval_add B σ _ _ _ _ h3 (RunStep.eval_var B σ "j" (by omega)) (by omega)
    rw [← hg]
    exact RunStep.eval_get B σ "t" _ _ h4 (by omega) (by rw [hg]; exact hgB)
  have hVe : (Expr.var "V").evalB B σ = some (Vw x) := by
    rw [← hV]; exact RunStep.eval_var B σ "V" (by omega)
  have hc := evalB_condLt eg hVe
  have r1 := okGuard_run' hc (by omega)
  set σ₁ := (if decide (tgtw x j < Vw x) then σ else σ.setVar "ok" 0) with hσ₁
  have hj₁ : σ₁.vars "j" = j := vars_ite' _ "j" (by decide)
  have r2 := RunStep.assign B σ₁ "j" (.add (.var "j") (.lit 1)) (j + 1)
    (RunStep.eval_add B σ₁ (.var "j") (.lit 1) _ _
      (by rw [← hj₁]; exact RunStep.eval_var B σ₁ "j" (by rw [hj₁]; omega))
      (RunStep.eval_lit B 1 σ₁ (by omega)) hjB)
  have he2₁ : σ₁.vars "e2" = 2 * x.getD 1 0 := by
    rw [hσ₁, vars_ite' _ "e2" (by decide)]; exact he2
  refine ⟨_, (r1.seq r2).mono (by simp), ⟨(base_ite' hb _).setVar "j" (by simp) _,
    by simp only [vars_setVar, String.reduceEq, ↓reduceIte]; exact he2₁,
    by simp only [vars_setVar, String.reduceEq, ↓reduceIte]; omega, ?_, ?_⟩,
    by simp only [vars_setVar, String.reduceEq, ↓reduceIte]; omega⟩
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hσ₁, ok_ite']; split_ifs <;> omega
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hσ₁, ok_ite']
    by_cases h : tgtw x j < Vw x
    · rw [if_pos (by simpa using h), hiff]
      constructor
      · intro hall j' hj'
        rcases Nat.lt_or_ge j' j with h' | h'
        · exact hall j' h'
        · have : j' = j := by omega
          subst this; exact h
      · intro hall j' hj'; exact hall j' (by omega)
    · rw [if_neg (by simpa using h)]
      constructor
      · intro h0; omega
      · intro hall
        exfalso
        exact h (hall j (by omega))

theorem chk3_spec {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hB : 8 * x.length + 40 ≤ B)
    (hlen : x.length = 4 + Vw x + 2 * x.getD 1 0) :
    Spec B (fun σ => Base x σ ∧ σ.vars "ok" = 1) chk3
      (fun _ σ' => Base x σ' ∧ σ'.vars "ok" ≤ 1 ∧
        (σ'.vars "ok" = 1 ↔ ∀ s < 2 * x.getD 1 0, tgtw x s < Vw x))
      (4 + ((20 + 4) * (2 * x.getD 1 0) + 6)) := by
  have hloop := Spec.forRangeZero (B := B) (c := chk3Body) "j" "e2" (Chk3Inv x)
    (2 * x.getD 1 0) 20 (by omega) (fun σ hσ => hσ.2.2.1) (fun σ hσ => hσ.2.1)
    (chk3Body_spec hx hB hlen)
  rintro σ ⟨hb, hok⟩
  have hE := hb.E
  have hEB : 2 * x.getD 1 0 < B := by omega
  have r1 := RunStep.assign B σ "e2" (.mul (.lit 2) (.var "E")) (2 * x.getD 1 0)
    (RunStep.eval_mul B σ (.lit 2) (.var "E") 2 (x.getD 1 0) (RunStep.eval_lit B 2 σ (by omega))
      (by rw [← hE]; exact RunStep.eval_var B σ "E" (by omega)) hEB)
  set σ₁ := σ.setVar "e2" (2 * x.getD 1 0) with hσ₁
  obtain ⟨σ₂, r2, ⟨hb₂, -, -, hok₂, hiff₂⟩, hj₂⟩ := hloop.run (σ := σ₁) (by
    refine ⟨(hb.setVar "e2" (by simp) _).setVar "j" (by simp) _, by simp [hσ₁], by simp,
      by simp [hσ₁, hok], ?_⟩
    simp [hσ₁, hok])
  rw [hj₂] at hiff₂
  exact ⟨σ₂, (r1.seq r2).mono (by simp), hb₂, hok₂, hiff₂⟩

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.Total` -/

section
/-!
The total program: read the word into `t`; answer `0` if it is shorter than four entries; read
the header; run the syntactic checks and the degree pass (which checks `crosses`), each guarded
by the flag `ok`; if the flag stands, build the symmetrized word in `a` and run Kuhn's algorithm
on it, answering whether every left vertex is matched; otherwise answer `0`.

This file: the program, the `ok`-guard combinator, and what every phase leaves alone
(`Untouched`: the search's own arrays and scalars, the output tape).
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteDecision
open scoped Classical

variable {B : ℕ}

/-- Write whether the count is `n`. -/
def finalC : Com :=
  .ite (.eq (.var "count") (.var "n")) (.write (.lit 1)) (.write (.lit 0))

/-- **The heavy path**: symmetrize, search from every left vertex, count, compare. -/
def heavyTot : Com :=
  .seq prefixCom
    (.seq posCom
      (.seq fillPass
        (.seq (.assign "m" (.sub (.var "V") (.var "n")))
          (.seq (.assign "l0" (.lit 0)) (.seq outerLoop (.seq countCom finalC))))))

/-- A phase run only while the flag stands. -/
def guarded (c : Com) : Com := .ite (.eq (.var "ok") (.lit 1)) c .skip

/-- **The total program**, after the length has been read into `len`. -/
def totCom : Com :=
  .seq readT
    (.ite (.lt (.var "len") (.lit 4)) (.write (.lit 0))
      (.seq hdrT
        (.seq (.assign "ok" (.lit 1))
          (.seq chk1
            (.seq (guarded chk2)
              (.seq (guarded chk3)
                (.seq (guarded degPass)
                  (.ite (.eq (.var "ok") (.lit 1)) heavyTot (.write (.lit 0))))))))))

/-- The array lengths declared to the run. -/
def extT (x : List ℕ) : String → ℕ := fun a =>
  if a = "t" ∨ a = "a" then x.length
  else if a = "deg" ∨ a = "pos" then nw x
  else if a = "vis" ∨ a = "mu" then Vw x - nw x
  else Vw x - nw x + 1

/-! ### What the phases leave alone -/

/-- The search's scalars and arrays are as at the start, and nothing has been written. -/
structure Untouched (x : List ℕ) (σ : Env) : Prop where
  top : σ.vars "top" = 0
  vis : σ.arrs "vis" = List.replicate (Vw x - nw x) 0
  mu : σ.arrs "mu" = List.replicate (Vw x - nw x) 0
  stkL : σ.arrs "stkL" = List.replicate (Vw x - nw x + 1) 0
  stkR : σ.arrs "stkR" = List.replicate (Vw x - nw x + 1) 0
  stkX : σ.arrs "stkX" = List.replicate (Vw x - nw x + 1) 0
  out : σ.out = []

/-- A run of a command that writes neither `top` nor the search's arrays nor the output keeps
`Untouched`. -/
theorem Untouched.of_run {x : List ℕ} {σ σ' : Env} {c : Com} {K : ℕ} (h : Untouched x σ)
    (hr : Run B c σ σ' K) (htop : "top" ∉ c.wvars)
    (harr : ∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ c.warrs) (hw : c.NoWrite) :
    Untouched x σ' := by
  have hv := hr.frame_var "top" htop
  have ha : ∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], σ'.arrs a = σ.arrs a :=
    fun a ha => hr.frame_arr a (harr a ha)
  refine ⟨by rw [hv]; exact h.top, ?_, ?_, ?_, ?_, ?_, by rw [hr.out_eq hw]; exact h.out⟩
  · rw [ha "vis" (by simp)]; exact h.vis
  · rw [ha "mu" (by simp)]; exact h.mu
  · rw [ha "stkL" (by simp)]; exact h.stkL
  · rw [ha "stkR" (by simp)]; exact h.stkR
  · rw [ha "stkX" (by simp)]; exact h.stkX

theorem Untouched.setVar {x : List ℕ} {σ : Env} (h : Untouched x σ) (y : String) (hy : y ≠ "top")
    (v : ℕ) : Untouched x (σ.setVar y v) :=
  ⟨by simp [Ne.symm hy]; exact h.top, h.vis, h.mu, h.stkL, h.stkR, h.stkX, h.out⟩

/-- The frame conditions of the phases before the search, read off their syntax. -/
theorem frame_readT : "top" ∉ readT.wvars ∧
    (∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ readT.warrs) ∧ readT.NoWrite := by
  simp [readT, readTBody, Com.wvars, Com.warrs, Com.NoWrite]

theorem frame_chk1 : "top" ∉ chk1.wvars ∧
    (∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ chk1.warrs) ∧ chk1.NoWrite := by
  simp [chk1, Com.wvars, Com.warrs, Com.NoWrite]

theorem frame_chk2 : "top" ∉ chk2.wvars ∧
    (∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ chk2.warrs) ∧ chk2.NoWrite := by
  simp [chk2, chk2Body, Com.wvars, Com.warrs, Com.NoWrite]

theorem frame_chk3 : "top" ∉ chk3.wvars ∧
    (∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ chk3.warrs) ∧ chk3.NoWrite := by
  simp [chk3, chk3Body, Com.wvars, Com.warrs, Com.NoWrite]

theorem frame_degPass : "top" ∉ degPass.wvars ∧
    (∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ degPass.warrs) ∧ degPass.NoWrite := by
  simp [degPass, rowIter, degBody, degThen, degElse, Com.wvars, Com.warrs, Com.NoWrite]

theorem frame_prefix : "top" ∉ prefixCom.wvars ∧
    (∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ prefixCom.warrs) ∧ prefixCom.NoWrite := by
  simp [prefixCom, prefixBody, prefixThen, prefixElse, Com.wvars, Com.warrs, Com.NoWrite]

theorem frame_pos : "top" ∉ posCom.wvars ∧
    (∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ posCom.warrs) ∧ posCom.NoWrite := by
  simp [posCom, posBody, Com.wvars, Com.warrs, Com.NoWrite]

theorem frame_fillPass : "top" ∉ fillPass.wvars ∧
    (∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ fillPass.warrs) ∧ fillPass.NoWrite := by
  simp [fillPass, rowIter, fillBody, fillThen, fillElse, Com.wvars, Com.warrs, Com.NoWrite]

/-- The arrays `deg`, `pos`, `a` are untouched by the checks. -/
theorem warrs_checks : ∀ a ∈ ["deg", "pos", "a"],
    a ∉ readT.warrs ∧ a ∉ hdrT.warrs ∧ a ∉ chk1.warrs ∧ a ∉ chk2.warrs ∧ a ∉ chk3.warrs := by
  simp [readT, readTBody, hdrT, chk1, chk2, chk2Body, chk3, chk3Body, Com.warrs]

theorem warrs_degPass : ∀ a ∈ ["pos", "a"], a ∉ degPass.warrs := by
  simp [degPass, rowIter, degBody, degThen, degElse, Com.warrs]

theorem warrs_prefix : "pos" ∉ prefixCom.warrs := by
  simp [prefixCom, prefixBody, prefixThen, prefixElse, Com.warrs]

/-! ### The guard -/

/-- **A guarded phase.** If the flag stands, the phase runs and refines the flag by `Q'`; if not,
nothing happens and the flag stays down. -/
theorem guarded_run {Q Q' : Prop} {c : Com} {σ : Env} {Kc : ℕ} (Post : Env → Prop) (h1B : 1 < B)
    (hok : σ.vars "ok" ≤ 1) (hiff : σ.vars "ok" = 1 ↔ Q) (hpost : Post σ)
    (hc : σ.vars "ok" = 1 → ∃ σ' K, Run B c σ σ' K ∧ K ≤ Kc ∧ σ'.vars "ok" ≤ 1 ∧
      (σ'.vars "ok" = 1 ↔ Q') ∧ Post σ') :
    ∃ σ' K, Run B (guarded c) σ σ' K ∧ K ≤ 5 + (if σ.vars "ok" = 1 then Kc else 0) ∧
      σ'.vars "ok" ≤ 1 ∧ (σ'.vars "ok" = 1 ↔ Q ∧ Q') ∧ Post σ' := by
  have hokB : σ.vars "ok" < B := by omega
  by_cases h : σ.vars "ok" = 1
  · obtain ⟨σ', K, hr, hK, hok', hiff', hp'⟩ := hc h
    have hcond := RunStep.cond_eq_true B σ (.var "ok") (.lit 1) _ _ (RunStep.eval_var B σ "ok" hokB)
      (RunStep.eval_lit B 1 σ h1B) h
    refine ⟨σ', _, RunStep.ite_true B _ c .skip σ σ' K hcond hr, by rw [if_pos h]; simp; omega,
      hok', ?_, hp'⟩
    rw [hiff']
    exact ⟨fun hq' => ⟨hiff.1 h, hq'⟩, fun hq => hq.2⟩
  · have hcond := RunStep.cond_eq_false B σ (.var "ok") (.lit 1) _ _ (RunStep.eval_var B σ "ok" hokB)
      (RunStep.eval_lit B 1 σ h1B) h
    refine ⟨σ, _, RunStep.ite_false B _ c .skip σ σ 1 hcond (RunStep.skip B σ),
      by rw [if_neg h]; simp, hok, ?_, hpost⟩
    exact ⟨fun h' => absurd h' h, fun hq => absurd (hiff.2 hq.1) h⟩

/-- The cost of the total program: linear in the word, plus `400 · (|x| + 1) · n` for the
searches of a well-formed word. -/
noncomputable def totCost (x : List ℕ) : ℕ :=
  600 * (x.length + 1) + (if WellFormed x then 400 * ((x.length + 1) * nw x) else 0)

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.TotalRun` -/

section
/-!
**The total program on every word**: from the entry state of `Wrap.lean` (the word on the input
tape, its length in `len`, everything else zero), `totCom` halts within `totCost x` with the
output `saturatingAnswer x`, under the value bound `8 (|x| + max x + 1) + 40`.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteDecision Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching
open scoped Classical

variable {B : ℕ}

/-- The largest entry of the word. -/
def mxE (x : List ℕ) : ℕ := x.foldr max 0

theorem le_mxE {x : List ℕ} {v : ℕ} (h : v ∈ x) : v ≤ mxE x := by
  induction x with
  | nil => simp at h
  | cons a t ih =>
      rw [mxE, List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

theorem mxE_cases (x : List ℕ) : mxE x = 0 ∨ mxE x ∈ x := by
  induction x with
  | nil => left; simp [mxE]
  | cons a t ih =>
      rw [mxE, List.foldr_cons]
      change max a (mxE t) = 0 ∨ max a (mxE t) ∈ a :: t
      rcases max_choice a (mxE t) with h | h
      · rw [h]; right; exact List.mem_cons_self
      · rw [h]
        rcases ih with h0 | h0
        · left; exact h0
        · right; exact List.mem_cons_of_mem _ h0

theorem getD_le_mxE (x : List ℕ) (i : ℕ) : x.getD i 0 ≤ mxE x := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : x[i]? with _ | v
  · exact Nat.zero_le _
  · exact le_mxE (List.mem_of_getElem? h)

/-- The value bound the program runs under. -/
def BofT (x : List ℕ) : ℕ := 8 * (x.length + 3 * mxE x + 1) + 40

theorem write_run {σ : Env} (v : ℕ) (hv : v < B) :
    Run B (.write (.lit v)) σ { σ with out := σ.out ++ [v] } 2 :=
  (Run.write (evalB_lit hv)).mono (by simp)

theorem finalC_run {σ : Env} (hcB : σ.vars "count" < B) (hnB : σ.vars "n" < B) (h1B : 1 < B) :
    Run B finalC σ { σ with out := σ.out ++ [if σ.vars "count" = σ.vars "n" then 1 else 0] } 6 := by
  have e1 := RunStep.eval_var B σ "count" hcB
  have e2 := RunStep.eval_var B σ "n" hnB
  have w1 := RunStep.write B σ (.lit 1) 1 (RunStep.eval_lit _ 1 σ h1B)
  have w0 := RunStep.write B σ (.lit 0) 0 (RunStep.eval_lit _ 0 σ (by omega))
  by_cases h : σ.vars "count" = σ.vars "n"
  · rw [if_pos h]
    exact RunStep.ite_true _ _ _ _ σ _ _ (RunStep.cond_eq_true _ σ _ _ _ _ e1 e2 h) w1
  · rw [if_neg h]
    exact RunStep.ite_false _ _ _ _ σ _ _ (RunStep.cond_eq_false _ σ _ _ _ _ e1 e2 h) w0

theorem notWellFormed_of_short {x : List ℕ} (h : x.length < 4) : ¬ WellFormed x := fun hw => by
  have := hw.length_eq; omega

theorem saturatingAnswer_of_not {x : List ℕ} (h : ¬ WellFormed x) : saturatingAnswer x = [0] := by
  unfold saturatingAnswer
  rw [if_neg (fun hh => h hh.1)]

/-- **The heavy path**, on a well-formed word. -/
theorem heavyTot_run {x : List ℕ} (hw : WellFormed x) (hB : 8 * x.length + 40 ≤ B) {σ : Env}
    (hb : Base x σ) (hdeg : DegOK x σ) (ha : σ.arrs "a" = List.replicate x.length 0)
    (hpos : (σ.arrs "pos").length = nw x) (hu : Untouched x σ) :
    ∃ σ' K, Run B heavyTot σ σ' K ∧
      K ≤ 200 * (x.length + 1) + 400 * ((x.length + 1) * nw x) ∧
      σ'.out = [if kuhnSize (sx x) = nw x then 1 else 0] := by
  have hxlen := wf_len hw
  have hnV := wf_nV hw
  have hg : Good (sx x) := wf_good_sx hw
  have hlen' := wf_length_sx hw
  set x' := sx x with hx'
  have hnw : nw x' = nw x := nw_sx x
  have hmw : mw x' = Vw x - nw x := by unfold mw; rw [Vw_sx, nw_sx]
  have hVw : Vw x' = Vw x := rfl
  -- the prefix sums
  obtain ⟨σ₁, r1, ⟨hb₁, hdeg₁, hf₁⟩, hfv₁, hfa₁, -, hfo₁⟩ :=
    (prefix_spec hw hB).frame.run ⟨hb, hdeg, ha⟩
  have hu₁ : Untouched x σ₁ := hu.of_run r1 frame_prefix.1 frame_prefix.2.1 frame_prefix.2.2
  have hpos₁ : (σ₁.arrs "pos").length = nw x := by rw [hfa₁ "pos" warrs_prefix]; exact hpos
  -- the cursors
  obtain ⟨σ₂, r2, ⟨hb₂, hf₂, hp₂⟩, -, -, -, -⟩ :=
    (pos_spec hw hB).frame.run ⟨hb₁, hf₁, hpos₁⟩
  have hu₂ : Untouched x σ₂ := hu₁.of_run r2 frame_pos.1 frame_pos.2.1 frame_pos.2.2
  -- the fill
  obtain ⟨σ₃, r3, ⟨hb₃, harr₃⟩, -, -, -, -⟩ := (fillPass_spec hw hB).frame.run ⟨hb₂, hf₂, hp₂⟩
  have hu₃ : Untouched x σ₃ := hu₂.of_run r3 frame_fillPass.1 frame_fillPass.2.1 frame_fillPass.2.2
  -- m := V - n; l0 := 0
  have hVB : Vw x < B := by omega
  have r4 := RunStep.assign B σ₃ "m" (.sub (.var "V") (.var "n")) (Vw x - nw x)
    (RunStep.eval_sub B σ₃ (.var "V") (.var "n") _ _
      (by rw [← hb₃.V]; exact RunStep.eval_var B σ₃ "V" (by rw [hb₃.V]; omega))
      (by rw [← hb₃.n]; exact RunStep.eval_var B σ₃ "n" (by rw [hb₃.n]; omega)) (by omega))
  set σ₄ := σ₃.setVar "m" (Vw x - nw x) with hσ₄
  have r5 := RunStep.assign B σ₄ "l0" (.lit 0) 0 (RunStep.eval_lit B 0 σ₄ (by omega))
  set σ₅ := σ₄.setVar "l0" 0 with hσ₅
  have hu₅ : Untouched x σ₅ := (hu₃.setVar "m" (by decide) _).setVar "l0" (by decide) _
  -- the search state
  have hReal : Real x' (fun _ => none) b0 σ₅ := by
    refine real_init hu₅.top ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hVw]; simp [hσ₅, hσ₄, hb₃.V]
    · rw [hnw]; simp [hσ₅, hσ₄, hb₃.n]
    · rw [hmw]; simp [hσ₅, hσ₄]
    · exact harr₃.congr (by simp [hσ₅, hσ₄])
    · rw [hmw]; exact hu₅.vis
    · rw [hmw]; exact hu₅.mu
    · rw [hmw]; exact hu₅.stkL
    · rw [hmw]; exact hu₅.stkR
    · rw [hmw]; exact hu₅.stkX
  have hI₅ : OuterInv x' σ₅ := by
    refine ⟨by rw [hnw]; simp [hσ₅], fun _ => none, b0, hReal, ?_⟩
    simp only [hσ₅, vars_setVar, ↓reduceIte]
    exact MatchInv.zero _ _ _
  have hB' : x'.length + 8 ≤ B := by rw [hlen']; omega
  obtain ⟨σ₆, K₆, r6, hI₆, hl₆, hK₆⟩ := outerLoop_run hg hB' hI₅
  have hl₅ : σ₅.vars "l0" = 0 := by simp [hσ₅]
  rw [hl₅, Nat.sub_zero, hnw] at hK₆
  obtain ⟨-, μ, b, hR₆, hM₆⟩ := hI₆
  rw [hl₆] at hM₆
  have hout₆ : σ₆.out = [] := by
    rw [r6.out_eq (by decide)]; simpa [hσ₅, hσ₄] using hu₃.out
  -- the count
  have hmB : mw x' + 1 < B := by rw [hmw]; omega
  obtain ⟨σ₇, r7, hq₇, hfv₇, -, -, hfo₇⟩ :=
    (countCom_spec (B := B) (μ := μ) (m := mw x') hmB
      (fun j l hj => by have := hM₆.hμn le_rfl j l hj; rw [hnw] at this; omega)).frame.run
      (σ := σ₆) ⟨hR₆.m, hR₆.mu⟩
  have hn₇ : σ₇.vars "n" = nw x := by
    rw [hfv₇ "n" (by simp [countCom, countBody, Com.wvars]), hR₆.n, hnw]
  have hcount : σ₇.vars "count" = kuhnSize x' := by
    rw [hq₇]
    unfold kuhnSize cnt
    rw [← size_muF_eq (hM₆.hμn le_rfl), hM₆.size_eq_kuhn]
  have hout₇ : σ₇.out = [] := by rw [hfo₇ (by decide)]; exact hout₆
  have hcB : σ₇.vars "count" < B := by
    rw [hcount]; have := Lax117284Proofs.Bipartite.Machine.kuhnSize_le x'; rw [hmw] at this; omega
  have r8 := finalC_run (B := B) (σ := σ₇) hcB (by rw [hn₇]; omega) (by omega)
  refine ⟨_, _, r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq r8)))))), ?_, ?_⟩
  · -- the cost
    have h1 := Lax117284Proofs.Bipartite.Machine.iterCost_le hg
    have h2 : x'.length + 1 = x.length + 1 := by rw [hlen']
    have h3 : iterCost x' ≤ 400 * (x.length + 1) := by omega
    have h4 : iterCost x' * nw x ≤ 400 * ((x.length + 1) * nw x) := by
      calc iterCost x' * nw x ≤ 400 * (x.length + 1) * nw x := Nat.mul_le_mul_right _ h3
        _ = 400 * ((x.length + 1) * nw x) := by ring
    rw [hmw] at *
    simp only [size_var, size_lit, size_bin, Expr.sub_def]
    omega
  · show σ₇.out ++ [if σ₇.vars "count" = σ₇.vars "n" then 1 else 0] = _
    rw [hout₇, hcount, hn₇]
    rfl

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.TotalMain` -/

section
/-!
**The total program on every word**: from the entry state of `Wrap.lean`, `totCom` halts within
`totCost x` with the output `saturatingAnswer x`, every value below `BofT x`.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteDecision Lax117284.BipartiteGraph Lax117284.BipartiteMatching Lax271696.GraphEncoding
open scoped Classical

variable {B : ℕ}

/-- What the checks keep: the header, the untouched search state, and the three arrays of the
symmetrizer still zero. -/
structure Aux (x : List ℕ) (σ : Env) : Prop where
  base : Base x σ
  unt : Untouched x σ
  deg : σ.arrs "deg" = List.replicate (nw x) 0
  a : σ.arrs "a" = List.replicate x.length 0
  pos : σ.arrs "pos" = List.replicate (nw x) 0

/-- A check keeps `Aux`. -/
theorem Aux.of_run {x : List ℕ} {σ σ' : Env} {c : Com} {K : ℕ} (h : Aux x σ) (hb : Base x σ')
    (hr : Run B c σ σ' K) (htop : "top" ∉ c.wvars)
    (harr : ∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ c.warrs) (hw : c.NoWrite)
    (h3 : ∀ a ∈ ["deg", "pos", "a"], a ∉ c.warrs) : Aux x σ' :=
  ⟨hb, h.unt.of_run hr htop harr hw, by rw [hr.frame_arr "deg" (h3 _ (by simp))]; exact h.deg,
    by rw [hr.frame_arr "a" (h3 _ (by simp))]; exact h.a,
    by rw [hr.frame_arr "pos" (h3 _ (by simp))]; exact h.pos⟩

theorem Aux.setVar {x : List ℕ} {σ : Env} (h : Aux x σ) (y : String)
    (hy : y ∉ ["len", "V", "E", "n", "top"]) (v : ℕ) : Aux x (σ.setVar y v) :=
  ⟨h.base.setVar y (by simp at hy; simp; tauto) v, h.unt.setVar y (by simp at hy; tauto) v,
    h.deg, h.a, h.pos⟩

/-- **The total program, run.** -/
theorem tot_run (x : List ℕ) :
    ∃ σ' K, Run (BofT x) totCom (lenEnv (extT x) x) σ' K ∧ K ≤ totCost x ∧
      σ'.out = saturatingAnswer x := by
  set B := BofT x with hBdef
  have hxB : ∀ v ∈ x, v < B := fun v hv => by have := le_mxE hv; unfold BofT at hBdef; omega
  have hB : 8 * x.length + 40 ≤ B := by unfold BofT at hBdef; omega
  have h0m := getD_le_mxE x 0
  have h1m := getD_le_mxE x 1
  have hnm := getD_le_mxE x (x.length - 1)
  have hVm : Vw x ≤ mxE x := h0m
  have hnm' : nw x ≤ mxE x := hnm
  have hBV : 8 * (x.length + Vw x + x.getD 1 0 + nw x) + 40 ≤ B := by
    have hB' : B = 8 * (x.length + 3 * mxE x + 1) + 40 := hBdef
    rw [hB']
    omega
  have hlB : x.length < B := by omega
  have h1B : 1 < B := by omega
  set σ₀ := lenEnv (extT x) x with hσ₀
  have h0len : σ₀.vars "len" = x.length := by simp [hσ₀, lenEnv]
  have h0top : σ₀.vars "top" = 0 := by simp [hσ₀, lenEnv, initEnv]
  have h0inp : σ₀.inp = x := rfl
  have h0out : σ₀.out = [] := rfl
  have h0arr : ∀ a, σ₀.arrs a = List.replicate (extT x a) 0 := fun a => rfl
  -- the read
  obtain ⟨σ₁, r1, ⟨-, htab₁, hlen₁⟩, hfv₁, hfa₁, -, hfo₁⟩ :=
    (readT_spec (B := B) hxB hlB).frame.run
      ⟨h0len, h0inp, by rw [h0arr, replicate_eq_arrOf]; simp [extT]⟩
  have hu₁ : Untouched x σ₁ := by
    have hv : σ₁.vars "top" = σ₀.vars "top" := hfv₁ "top" frame_readT.1
    refine ⟨by rw [hv]; exact h0top, ?_, ?_, ?_, ?_, ?_, by rw [hfo₁ frame_readT.2.2]; exact h0out⟩
    all_goals (rw [hfa₁ _ (frame_readT.2.1 _ (by simp)), h0arr]; simp [extT])
  have harrs₁ : σ₁.arrs "deg" = List.replicate (nw x) 0 ∧ σ₁.arrs "a" = List.replicate x.length 0 ∧
      σ₁.arrs "pos" = List.replicate (nw x) 0 := by
    refine ⟨?_, ?_, ?_⟩ <;> (rw [hfa₁ _ (warrs_checks _ (by simp)).1, h0arr]; simp [extT])
  have hcond4 : (Cond.lt (.var "len") (.lit 4)).evalB B σ₁ = some (decide (x.length < 4)) := by
    rw [← hlen₁]; exact evalB_condLt (evalB_var (by omega)) (evalB_lit (by omega))
  by_cases h4 : x.length < 4
  · -- too short: not well formed
    have hc : (Cond.lt (.var "len") (.lit 4)).evalB B σ₁ = some true := by
      rw [hcond4, decide_eq_true h4]
    refine ⟨_, _, r1.seq (Run.ite_true hc (write_run 0 (by omega))), ?_, ?_⟩
    · simp only [size_condLt, size_var, size_lit]; unfold totCost; omega
    · show σ₁.out ++ [0] = _
      rw [hu₁.out, saturatingAnswer_of_not (notWellFormed_of_short h4)]; rfl
  have hc4 : (Cond.lt (.var "len") (.lit 4)).evalB B σ₁ = some false := by
    rw [hcond4, decide_eq_false h4]
  -- the header
  obtain ⟨σ₂, r2, hq₂⟩ := (hdrT_spec (B := B) hxB hlB (by omega)).run (σ := σ₁) ⟨htab₁, hlen₁⟩
  have hb₂ : Base x σ₂ := by
    rw [hq₂]; exact ⟨htab₁.congr rfl, by simpa using hlen₁, by simp, by simp, by simp⟩
  have hA₂ : Aux x σ₂ := by
    rw [hq₂]
    refine ⟨?_, ?_, harrs₁.1, harrs₁.2.1, harrs₁.2.2⟩
    · rw [← hq₂]; exact hb₂
    · exact ((hu₁.setVar "V" (by decide) _).setVar "E" (by decide) _).setVar "n" (by decide) _
  -- ok := 1
  have r3 := RunStep.assign B σ₂ "ok" (.lit 1) 1 (RunStep.eval_lit B 1 σ₂ h1B)
  set σ₃ := σ₂.setVar "ok" 1 with hσ₃
  have hA₃ : Aux x σ₃ := hA₂.setVar "ok" (by simp) 1
  -- check 1
  obtain ⟨σ₄, r4, ⟨hb₄, hok₄, hiff₄⟩, hfv₄, hfa₄, -, hfo₄⟩ :=
    (chk1_spec (B := B) hBV).frame.run (σ := σ₃) ⟨hA₃.base, by simp [hσ₃]⟩
  have hA₄ : Aux x σ₄ := hA₃.of_run hb₄ r4 frame_chk1.1 frame_chk1.2.1 frame_chk1.2.2
    (fun a ha => (warrs_checks a ha).2.2.1)
  -- check 2, guarded
  obtain ⟨σ₅, K₅, r5, hK₅, hok₅, hiff₅, hA₅⟩ := guarded_run (B := B) (Q' := offw x 0 = 0 ∧
      offw x (Vw x) = 2 * x.getD 1 0 ∧ ∀ i < Vw x, offw x i ≤ offw x (i + 1))
    (Kc := 16 + 16 + ((20 + 4) * Vw x + 6)) (Aux x) h1B hok₄ hiff₄ hA₄ (fun hok => by
      have hlen : x.length = 4 + Vw x + 2 * x.getD 1 0 := (hiff₄.1 hok).2
      obtain ⟨σ', r, ⟨hb', hok', hiff'⟩, -, -, -, -⟩ :=
        (chk2_spec (B := B) hxB hB hlen).frame.run (σ := σ₄) ⟨hA₄.base, hok⟩
      exact ⟨σ', _, r, le_rfl, hok', hiff', hA₄.of_run hb' r frame_chk2.1 frame_chk2.2.1
        frame_chk2.2.2 (fun a ha => (warrs_checks a ha).2.2.2.1)⟩)
  -- check 3, guarded
  obtain ⟨σ₆, K₆, r6, hK₆, hok₆, hiff₆, hA₆⟩ := guarded_run (B := B)
    (Q' := ∀ s < 2 * x.getD 1 0, tgtw x s < Vw x)
    (Kc := 4 + ((20 + 4) * (2 * x.getD 1 0) + 6)) (Aux x) h1B hok₅ hiff₅ hA₅ (fun hok => by
      have hlen : x.length = 4 + Vw x + 2 * x.getD 1 0 := (hiff₅.1 hok).1.2
      obtain ⟨σ', r, ⟨hb', hok', hiff'⟩, -, -, -, -⟩ :=
        (chk3_spec (B := B) hxB hB hlen).frame.run (σ := σ₅) ⟨hA₅.base, hok⟩
      exact ⟨σ', _, r, le_rfl, hok', hiff', hA₅.of_run hb' r frame_chk3.1 frame_chk3.2.1
        frame_chk3.2.2 (fun a ha => (warrs_checks a ha).2.2.2.2)⟩)
  -- the degree pass, guarded: afterwards `ok = 1 ↔ WellFormed x`
  have hWF3 : σ₆.vars "ok" = 1 → WF3 x := fun hok => by
    obtain ⟨⟨⟨h1, h2⟩, h3, h4, h5⟩, h6⟩ := hiff₆.1 hok
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have hokB₆ : σ₆.vars "ok" < B := by omega
  have hdegPass : ∃ σ' K, Run B (guarded degPass) σ₆ σ' K ∧
      K ≤ 5 + (if σ₆.vars "ok" = 1 then (30 + 8) * (2 * x.getD 1 0) + 22 * Vw x + 6 else 0) ∧
      σ'.vars "ok" ≤ 1 ∧
      (σ'.vars "ok" = 1 ↔ WellFormed x) ∧ Base x σ' ∧ Untouched x σ' ∧
      σ'.arrs "a" = List.replicate x.length 0 ∧ σ'.arrs "pos" = List.replicate (nw x) 0 ∧
      (σ'.vars "ok" = 1 → DegOK x σ') := by
    by_cases hok : σ₆.vars "ok" = 1
    · have h3 := hWF3 hok
      have hcond := RunStep.cond_eq_true B σ₆ (.var "ok") (.lit 1) _ _
        (RunStep.eval_var B σ₆ "ok" hokB₆) (RunStep.eval_lit B 1 σ₆ h1B) hok
      obtain ⟨σ', r, ⟨hb', hok', hiff', hdeg', hlen'⟩, -, hfa', -, -⟩ :=
        (degPass_spec (B := B) h3 hB).frame.run (σ := σ₆) ⟨hA₆.base, hok, hA₆.deg⟩
      refine ⟨σ', _, RunStep.ite_true B _ degPass .skip σ₆ σ' _ hcond r,
        by rw [if_pos hok]; simp only [size_condEq, size_var, size_lit]; omega, hok', hiff', hb',
        hA₆.unt.of_run r frame_degPass.1 frame_degPass.2.1 frame_degPass.2.2, ?_, ?_,
        fun h => ⟨hlen', hdeg' h⟩⟩
      · rw [hfa' "a" (warrs_degPass _ (by simp))]; exact hA₆.a
      · rw [hfa' "pos" (warrs_degPass _ (by simp))]; exact hA₆.pos
    · have hcond := RunStep.cond_eq_false B σ₆ (.var "ok") (.lit 1) _ _
        (RunStep.eval_var B σ₆ "ok" hokB₆) (RunStep.eval_lit B 1 σ₆ h1B) hok
      refine ⟨σ₆, _, RunStep.ite_false B _ degPass .skip σ₆ σ₆ 1 hcond (RunStep.skip B σ₆),
        by rw [if_neg hok]; simp only [size_condEq, size_var, size_lit]; omega,
        hok₆, ⟨fun h => absurd h hok, fun hw => absurd (hiff₆.2 (wellFormed_iff.1 hw |>.elim
          (fun h3 hc => ⟨⟨⟨h3.nV, h3.len⟩, h3.off0, h3.offV, h3.mono⟩, h3.tgt_lt⟩))) hok⟩,
        hA₆.base, hA₆.unt, hA₆.a, hA₆.pos, fun h => absurd h hok⟩
  obtain ⟨σ₇, K₇, r7, hK₇, hok₇, hiff₇, hb₇, hu₇, ha₇, hpos₇, hdeg₇⟩ := hdegPass
  have hokB₇ : σ₇.vars "ok" < B := by omega
  -- the answer
  by_cases hok : σ₇.vars "ok" = 1
  · have hw : WellFormed x := hiff₇.1 hok
    have hcond := RunStep.cond_eq_true B σ₇ (.var "ok") (.lit 1) _ _
      (RunStep.eval_var B σ₇ "ok" hokB₇) (RunStep.eval_lit B 1 σ₇ h1B) hok
    obtain ⟨σ₈, K₈, r8, hK₈, hout₈⟩ := heavyTot_run hw hB hb₇ (hdeg₇ hok) ha₇
      (by rw [hpos₇]; simp) hu₇
    refine ⟨σ₈, _, r1.seq (Run.ite_false hc4 (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq
      (RunStep.ite_true B _ heavyTot _ σ₇ σ₈ _ hcond r8)))))))), ?_, ?_⟩
    · have hxlen := wf_len hw
      have hVx : Vw x ≤ x.length := by omega
      have hEx : 2 * x.getD 1 0 ≤ x.length := by omega
      simp only [size_condLt, size_condEq, size_var, size_lit]
      unfold totCost
      rw [if_pos hw]
      split_ifs at hK₅ hK₆ hK₇ <;> omega
    · rw [hout₈]
      unfold saturatingAnswer
      by_cases hs : ∃ M : (wordGraph x).Subgraph, M.IsMatching ∧
          Saturates (wordGraph x) M (leftSide (vertexCount x) (leftCount x))
      · rw [if_pos (show kuhnSize (sx x) = nw x from (kuhnSize_sx_iff hw).2 hs), if_pos ⟨hw, hs⟩]
      · rw [if_neg (show ¬ kuhnSize (sx x) = nw x from fun h => hs ((kuhnSize_sx_iff hw).1 h)),
          if_neg (fun h => hs h.2)]
  · have hnw : ¬ WellFormed x := fun hw => hok (hiff₇.2 hw)
    have hcond := RunStep.cond_eq_false B σ₇ (.var "ok") (.lit 1) _ _
      (RunStep.eval_var B σ₇ "ok" hokB₇) (RunStep.eval_lit B 1 σ₇ h1B) hok
    refine ⟨_, _, r1.seq (Run.ite_false hc4 (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq
      (RunStep.ite_false B _ heavyTot _ σ₇ _ 2 hcond (write_run 0 (by omega)))))))))), ?_, ?_⟩
    · -- the cost, by whether the checks ran
      simp only [size_condLt, size_condEq, size_var, size_lit]
      unfold totCost
      rw [if_neg hnw]
      by_cases hQ1 : nw x ≤ Vw x ∧ x.length = 4 + Vw x + 2 * x.getD 1 0
      · have hVx : Vw x ≤ x.length := by omega
        have hEx : 2 * x.getD 1 0 ≤ x.length := by omega
        split_ifs at hK₅ hK₆ hK₇ <;> omega
      · -- the flag fell at the first check: every later phase was skipped
        have h4' : σ₄.vars "ok" ≠ 1 := fun h => hQ1 (hiff₄.1 h)
        have h5' : σ₅.vars "ok" ≠ 1 := fun h => hQ1 (hiff₅.1 h).1
        have h6' : σ₆.vars "ok" ≠ 1 := fun h => hQ1 (hiff₆.1 h).1.1
        rw [if_neg h4'] at hK₅
        rw [if_neg h5'] at hK₆
        rw [if_neg h6'] at hK₇
        omega
    · show σ₇.out ++ [0] = _
      rw [hu₇.out, saturatingAnswer_of_not hnw]; rfl

end Lax117284Proofs.Bipartite.Ram2

end
