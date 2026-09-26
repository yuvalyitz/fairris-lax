import Lax117284Proofs.TwoSAT.Bridge
import Lax117284Proofs.TwoSAT.Correct
import Lax391470Proofs.L2ScanModel

/-!
The mathematics of what the machine computes from a scanned formula: the codes of the
literals as nodes, the edges each clause contributes, in the order the machine emits them,
and the identification of that edge list with the edge relation of the criterion.

The scan of `lax-391470` leaves the formula `F` as the list of its literals in order (`lits F`),
each with its clause number (`cn F`). The machine's graph has `N F = 2 · mxOf (lits F)` nodes,
the codes `2x` and `2x + 1` of the negative and positive literals of every variable `x` below
the bound `mxOf`, which the scan computes as one more than the largest index.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Model

open Lax429075.CNF Lax391470Proofs.L2ScanModel Lax117284.TwoSatCNF Lax117284.TwoSatImplicationGraph
open Lax117284Proofs.TwoSAT.Math Lax117284Proofs.TwoSAT.Bridge

variable (F : Formula)

/-! ### The arrays the scan leaves -/

def dflt : Literal := ⟨0, false⟩

/-- The variable of the `i`-th literal. -/
def iv (i : ℕ) : ℕ := ((lits F).getD i dflt).index

/-- The sign of the `i`-th literal, `1` for positive. -/
def sv (i : ℕ) : ℕ := if ((lits F).getD i dflt).positive then 1 else 0

/-- The clause number of the `i`-th literal. -/
def cv (i : ℕ) : ℕ := (cn F).getD i 0

/-- The number of nodes of the machine's graph. -/
def N : ℕ := 2 * mxOf (lits F)

/-- The code of the `i`-th literal. -/
theorem code_getD (i : ℕ) : code ((lits F).getD i dflt) = 2 * iv F i + sv F i := by
  unfold code node iv sv; rfl

/-- The code of the negation of the `i`-th literal. -/
theorem code_negate_getD (i : ℕ) :
    code (negate ((lits F).getD i dflt)) = 2 * iv F i + (1 - sv F i) := by
  unfold code node iv sv negate
  cases ((lits F).getD i dflt).positive <;> simp

theorem sv_le (i : ℕ) : sv F i ≤ 1 := by unfold sv; split <;> omega

/-! ### The bound on the indices -/

theorem index_lt_mxOf {L : List Literal} {l : Literal} (hl : l ∈ L) : l.index + 1 ≤ mxOf L := by
  induction L with
  | nil => cases hl
  | cons a t ih =>
    simp only [mxOf, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp hl with rfl | h
    · omega
    · have := ih h; omega

theorem code_lt_N {l : Literal} (hl : l ∈ lits F) : code l < N F := by
  have := index_lt_mxOf hl
  unfold code node N; split <;> omega

theorem code_negate_lt_N {l : Literal} (hl : l ∈ lits F) : code (negate l) < N F := by
  have := index_lt_mxOf hl
  obtain ⟨i, p⟩ := l
  simp only at this
  unfold code node N negate
  cases p <;> simp <;> omega

theorem getD_mem_lits (i : ℕ) (hi : i < (lits F).length) : (lits F).getD i dflt ∈ lits F := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

theorem iv_lt (i : ℕ) (hi : i < (lits F).length) : iv F i + 1 ≤ mxOf (lits F) :=
  index_lt_mxOf (getD_mem_lits F i hi)

theorem two_le_N : 2 ≤ N F := by
  have := mxOf_pos (lits F); unfold N; omega

/-! ### The edges -/

/-- The edges a clause contributes, in the order the machine emits them: `¬a → a` for a unit
clause, `¬a → b` and `¬b → a` for a clause of two literals. -/
def clauseEdges : Clause → List (ℕ × ℕ)
  | [a] => [(code (negate a), code a)]
  | [a, b] => [(code (negate a), code b), (code (negate b), code a)]
  | _ => []

/-- All the edges, clause by clause. -/
def edges : List (ℕ × ℕ) := F.flatMap clauseEdges

/-- The edge relation of the machine's graph. -/
def E (u v : ℕ) : Prop := (u, v) ∈ edges F

/-- Every clause has one or two literals. -/
def WidthOk : Prop := ∀ C ∈ F, 1 ≤ C.length ∧ C.length ≤ 2

theorem widthOk_iff : WidthOk F ↔ IsTwoCNF F ∧ [] ∉ F := by
  constructor
  · intro h
    refine ⟨fun C hC => (h C hC).2, fun h0 => ?_⟩
    have := (h [] h0).1; simp at this
  · rintro ⟨h2, h0⟩ C hC
    refine ⟨?_, h2 C hC⟩
    rcases C with _ | ⟨a, C⟩
    · exact absurd hC h0
    · simp

theorem length_clauseEdges_le (C : Clause) : (clauseEdges C).length ≤ C.length := by
  match C with
  | [] => simp [clauseEdges]
  | [a] => simp [clauseEdges]
  | [a, b] => simp [clauseEdges]
  | a :: b :: c :: t => simp [clauseEdges]

theorem length_edges_le : (edges F).length ≤ (lits F).length := by
  unfold edges lits
  induction F with
  | nil => simp
  | cons C t ih =>
    simp only [List.flatMap_cons, List.length_append, id]
    have := length_clauseEdges_le C
    omega

theorem mem_clauseEdges_iff (C : Clause) (hlen : C.length ≤ 2) (hne : C ≠ []) (u v : ℕ) :
    (u, v) ∈ clauseEdges C ↔
      ((u = code (negate (clauseLit C 0)) ∧ v = code (clauseLit C 1)) ∨
        (u = code (negate (clauseLit C 1)) ∧ v = code (clauseLit C 0))) := by
  match C with
  | [] => exact absurd rfl hne
  | [a] => simp [clauseEdges, clauseLit]
  | [a, b] => simp [clauseEdges, clauseLit]
  | a :: b :: c :: t => simp at hlen

/-- **The machine's edges are the edges of the criterion.** -/
theorem E_iff_edge (hw : WidthOk F) (u v : ℕ) :
    E F u v ↔ Edge F.length (xsOf F) (ssOf F) u v := by
  unfold E edges Edge
  rw [List.mem_flatMap, exists_mem_iff]
  refine exists_congr fun c => and_congr_right fun hc => ?_
  have h := hw _ (getD_mem hc)
  rw [mem_clauseEdges_iff _ h.2 (by intro e; rw [e] at h; simp at h)]
  rw [node_xs_ss, node_xs_ss, node_xs_neg, node_xs_neg, litAt_even, litAt_odd]

theorem edge_ends_lt (hw : WidthOk F) {u v : ℕ} (h : E F u v) : u < N F ∧ v < N F := by
  unfold E edges at h
  rw [List.mem_flatMap] at h
  obtain ⟨C, hC, huv⟩ := h
  have hmem : ∀ l ∈ C, l ∈ lits F := fun l hl => by
    unfold lits; rw [List.mem_flatMap]; exact ⟨C, hC, hl⟩
  match C, huv with
  | [a], huv =>
    simp [clauseEdges] at huv
    obtain ⟨rfl, rfl⟩ := huv
    exact ⟨code_negate_lt_N F (hmem a (by simp)), code_lt_N F (hmem a (by simp))⟩
  | [a, b], huv =>
    simp [clauseEdges] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨code_negate_lt_N F (hmem a (by simp)), code_lt_N F (hmem b (by simp))⟩
    · exact ⟨code_negate_lt_N F (hmem b (by simp)), code_lt_N F (hmem a (by simp))⟩
  | [], huv => simp [clauseEdges] at huv
  | a :: b :: c :: t, huv => simp [clauseEdges] at huv

/-! ### Reachability -/

/-- Reachability in the machine's graph, paths of any length. -/
def RT : ℕ → ℕ → Prop := Relation.ReflTransGen (E F)

theorem rt_iff_reach (hw : WidthOk F) {u v : ℕ} (hne : u ≠ v) :
    RT F u v ↔ Reach F.length (xsOf F) (ssOf F) u v := by
  unfold RT
  rw [Relation.reflTransGen_iff_eq_or_transGen]
  simp only [hne.symm, false_or]
  have : E F = Edge F.length (xsOf F) (ssOf F) := by
    funext a b; exact propext (E_iff_edge F hw a b)
  rw [this]

/-- The variable `x` is found contradictory by the searches. -/
def Bad (x : ℕ) : Prop := RT F (2 * x + 1) (2 * x) ∧ RT F (2 * x) (2 * x + 1)

theorem bad_iff (hw : WidthOk F) (x : ℕ) : Bad F x ↔ Contra F.length (xsOf F) (ssOf F) x := by
  simp only [Bad, Contra, node, Nat.add_zero]
  rw [rt_iff_reach F hw (by omega), rt_iff_reach F hw (by omega)]

/-- **What the machine decides is the right thing**: every clause has one or two literals and
no occurring variable is contradictory, exactly when the formula is a satisfiable 2-CNF. -/
theorem answer_iff :
    (WidthOk F ∧ ∀ x ∈ vars F, ¬ Bad F x) ↔ IsTwoCNF F ∧ Satisfiable F := by
  rw [widthOk_iff]
  constructor
  · rintro ⟨⟨h2, h0⟩, hb⟩
    refine ⟨h2, (satisfiable_iff F h2).2 ⟨h0, fun x hx => ?_⟩⟩
    by_cases hv : x ∈ vars F
    · exact hb x hv ((bad_iff F ((widthOk_iff F).2 ⟨h2, h0⟩) x).2
        ((contradictory_iff_contra h2 h0 x).1 hx))
    · exact Lax117284Proofs.TwoSAT.Correct.not_contradictory_of_not_mem_vars hv hx
  · rintro ⟨h2, hs⟩
    have h0 := not_mem_nil_of_satisfiable hs
    refine ⟨⟨h2, h0⟩, fun x _ hb => ?_⟩
    exact ((satisfiable_iff F h2).1 hs).2 x
      ((contradictory_iff_contra h2 h0 x).2 ((bad_iff F ((widthOk_iff F).2 ⟨h2, h0⟩) x).1 hb))

/-! ### The layout of the literals by clause -/

/-- The position of the first literal of clause `c`. -/
def start (c : ℕ) : ℕ := ((F.take c).flatMap id).length

theorem start_zero : start F 0 = 0 := by simp [start]

theorem start_succ (c : ℕ) (hc : c < F.length) :
    start F (c + 1) = start F c + (F.getD c []).length := by
  unfold start
  rw [List.take_add_one, List.flatMap_append, List.length_append]
  simp [List.getD_eq_getElem?_getD, hc]

theorem lits_eq (c : ℕ) (hc : c < F.length) :
    lits F = (F.take c).flatMap id ++ (F.getD c [] ++ (F.drop (c + 1)).flatMap id) := by
  unfold lits
  conv_lhs => rw [← List.take_append_drop c F]
  rw [List.flatMap_append, List.drop_eq_getElem_cons hc, List.flatMap_cons]
  simp [List.getD_eq_getElem?_getD, hc]

theorem getD_lits (c : ℕ) (hc : c < F.length) (α : ℕ) (hα : α < (F.getD c []).length) :
    (lits F).getD (start F c + α) dflt = (F.getD c []).getD α dflt := by
  rw [lits_eq F c hc]
  unfold start
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ hα]

theorem start_le (c : ℕ) (hc : c ≤ F.length) : start F c ≤ (lits F).length := by
  unfold start lits
  conv_rhs => rw [← List.take_append_drop c F]
  rw [List.flatMap_append, List.length_append]; omega

theorem start_add_le (c : ℕ) (hc : c < F.length) :
    start F c + (F.getD c []).length ≤ (lits F).length := by
  rw [← start_succ F c hc]; exact start_le F (c + 1) hc

theorem sum_ite_range (n c v : ℕ) (hc : c < n) :
    ((List.range n).map fun j => if j = c then v else 0).sum = v := by
  induction n with
  | zero => omega
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases h : c = k
    · subst h
      have : ((List.range c).map fun j => if j = c then v else 0).sum = 0 := by
        rw [List.sum_eq_zero]
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        rw [List.mem_range] at hj
        simp [show j ≠ c by omega]
      simp [this]
    · rw [ih (by omega)]
      simp [Ne.symm h]

/-- The number of literals with clause number `c` is the length of clause `c`. -/
theorem count_cv (c : ℕ) (hc : c < F.length) :
    ((List.range (lits F).length).filter fun i => cv F i = c).length =
      (F.getD c []).length := by
  have hlen := cn_length F
  have key : ∀ (L : List ℕ), ((List.range L.length).filter fun i => L.getD i 0 = c).length =
      L.count c := by
    intro L
    induction L using List.reverseRecOn with
    | nil => simp
    | append_singleton L a ih =>
      rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append,
        List.length_append, List.count_append]
      have h1 : ((List.range L.length).filter fun i => (L ++ [a]).getD i 0 = c) =
          (List.range L.length).filter fun i => L.getD i 0 = c := by
        apply List.filter_congr
        intro i hi
        rw [List.mem_range] at hi
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      have h2 : (L ++ [a]).getD L.length 0 = a := by
        rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
      rw [h1, ih]
      congr 1
      simp only [List.filter_singleton, h2]
      by_cases h : a = c
      · subst h; simp
      · simp [h]
  have : ((List.range (lits F).length).filter fun i => cv F i = c) =
      (List.range (cn F).length).filter fun i => (cn F).getD i 0 = c := by
    unfold cv; rw [hlen]
  rw [this, key]
  unfold cn
  rw [List.count_flatMap]
  have hf : ∀ j ∈ List.range F.length,
      (List.count c ∘ fun j => List.replicate (F.getD j []).length j) j =
        if j = c then (F.getD c []).length else 0 := by
    intro j _
    simp only [Function.comp, List.count_replicate]
    by_cases h : j = c
    · subst h; simp
    · simp [h]
  rw [List.map_congr_left hf, sum_ite_range _ _ _ hc]

theorem cv_lt (i : ℕ) (hi : i < (lits F).length) : cv F i < F.length := by
  unfold cv
  have hmem : (cn F).getD i 0 ∈ cn F := by
    rw [List.getD_eq_getElem _ _ (by rw [cn_length]; exact hi)]; exact List.getElem_mem _
  have hmem' : (cn F).getD i 0 ∈
      (List.range F.length).flatMap (fun j => List.replicate (F.getD j []).length j) := hmem
  rw [List.mem_flatMap] at hmem'
  obtain ⟨j, hj, hmem⟩ := hmem'
  rw [List.mem_replicate] at hmem
  rw [hmem.2]; exact List.mem_range.1 hj

end Lax117284Proofs.TwoSAT.Machine.Model
