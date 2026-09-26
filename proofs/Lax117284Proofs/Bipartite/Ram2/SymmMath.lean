import Lax117284Proofs.Bipartite.Ram2.Word

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
