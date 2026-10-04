import Lax117284Proofs.TwoSAT.Bridge
import Lax117284Proofs.TwoSAT.Correct
import Lax391470Proofs.L2ScanModel
import Lax808846Proofs.Lib.Basic
import Lax808846Proofs.Lib.Csr
import Lax808846Proofs.Tactic
import Lax808846Proofs.Lib.Queue
import Lax808846Proofs.Lib.Fill
import Lax391470Proofs.L2Scan
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lax117284.TwoSatRunningTime
import Lax808846Proofs.Transfer
import Lax391470Proofs.RamToTuring
import Lax391470Proofs.ReadAll
import Lax391470Proofs.RamBridge
import Lax117284.TwoSatInP

/-! ### `Lax117284Proofs.TwoSAT.Machine.Model` -/

section
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

end

/-! ### `Lax117284Proofs.TwoSAT.Machine.BuildMath` -/

section
/-!
The mathematics behind the counting-sort construction of the implication graph's CSR
representation: the edges of the first `c` clauses, how many of them leave each node, the
prefix sums of those counts, and the invariant of the fill — every row's filled stretch holds
exactly the out-neighbours emitted so far.

Nothing here mentions an environment; `Build.lean` reads these through `arrOf`.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Build

open Lax429075.CNF Lax391470Proofs.L2ScanModel Lax117284.TwoSatCNF Lax117284.TwoSatImplicationGraph
open Lax117284Proofs.TwoSAT.Machine.Model Lax808846Proofs.Reasoning.Lib

/-! ### The edges of the first `c` clauses -/

variable (F : Formula)

/-- The edges contributed by the first `c` clauses, in emission order. -/
def edgesUpTo (c : ℕ) : List (ℕ × ℕ) := (F.take c).flatMap clauseEdges

theorem edgesUpTo_zero : edgesUpTo F 0 = [] := by simp [edgesUpTo]

theorem edgesUpTo_succ (c : ℕ) (hc : c < F.length) :
    edgesUpTo F (c + 1) = edgesUpTo F c ++ clauseEdges (F.getD c []) := by
  unfold edgesUpTo
  rw [List.take_add_one, List.flatMap_append]
  simp [List.getD_eq_getElem?_getD, hc]

theorem edgesUpTo_length : edgesUpTo F F.length = edges F := by
  unfold edgesUpTo edges; rw [List.take_length]

theorem edgesUpTo_prefix (c : ℕ) : edgesUpTo F c <+: edges F :=
  ⟨(F.drop c).flatMap clauseEdges, by
    unfold edgesUpTo edges; rw [← List.flatMap_append, List.take_append_drop]⟩

theorem edgesUpTo_succ_prefix (c : ℕ) (hc : c < F.length) :
    edgesUpTo F c ++ clauseEdges (F.getD c []) <+: edges F := by
  rw [← edgesUpTo_succ F c hc]; exact edgesUpTo_prefix F (c + 1)

theorem mem_edges_of_prefix {L : List (ℕ × ℕ)} (h : L <+: edges F) {e : ℕ × ℕ} (he : e ∈ L) :
    e ∈ edges F := h.subset he

/-- The codes read off the literal arrays at the two positions of clause `c`. -/
theorem clauseEdges_unit (c : ℕ) (hc : c < F.length) (h1 : (F.getD c []).length = 1) :
    clauseEdges (F.getD c []) =
      [(2 * iv F (start F c) + (1 - sv F (start F c)), 2 * iv F (start F c) + sv F (start F c))] := by
  have h0 := getD_lits F c hc 0 (by omega)
  rw [Nat.add_zero] at h0
  rw [← code_negate_getD, ← code_getD, h0]
  generalize F.getD c [] = D at h1 ⊢
  match D, h1 with
  | [a], _ => simp [clauseEdges]

theorem clauseEdges_pair (c : ℕ) (hc : c < F.length) (h2 : (F.getD c []).length = 2) :
    clauseEdges (F.getD c []) =
      [(2 * iv F (start F c) + (1 - sv F (start F c)),
          2 * iv F (start F c + 1) + sv F (start F c + 1)),
        (2 * iv F (start F c + 1) + (1 - sv F (start F c + 1)),
          2 * iv F (start F c) + sv F (start F c))] := by
  have h0 := getD_lits F c hc 0 (by omega)
  have h1 := getD_lits F c hc 1 (by omega)
  rw [Nat.add_zero] at h0
  rw [← code_negate_getD, ← code_getD, ← code_negate_getD, ← code_getD, h0, h1]
  generalize F.getD c [] = D at h2 ⊢
  match D, h2 with
  | [a, b], _ => simp [clauseEdges]

theorem clause_length_cases (hw : WidthOk F) (c : ℕ) (hc : c < F.length) :
    (F.getD c []).length = 1 ∨ (F.getD c []).length = 2 := by
  have hmem : F.getD c [] ∈ F := by
    rw [List.getD_eq_getElem _ _ hc]; exact List.getElem_mem hc
  have := hw _ hmem
  omega

/-- The bound the codes obey: twice the variable plus two is at most the node count. -/
theorem two_iv_add_two_le (i : ℕ) : 2 * iv F i + 2 ≤ N F := by
  by_cases hi : i < (lits F).length
  · have := iv_lt F i hi; unfold N; omega
  · have h2 := two_le_N F
    have : iv F i = 0 := by
      unfold iv; rw [List.getD_eq_default _ _ (by omega)]; rfl
    omega

/-! ### Counting the edges leaving a node -/

/-- The number of edges of `L` leaving `u`. -/
def cntSrc (L : List (ℕ × ℕ)) (u : ℕ) : ℕ := (L.filter fun e => e.1 = u).length

@[simp] theorem cntSrc_nil (u : ℕ) : cntSrc [] u = 0 := rfl

theorem cntSrc_append (L M : List (ℕ × ℕ)) (u : ℕ) :
    cntSrc (L ++ M) u = cntSrc L u + cntSrc M u := by
  simp [cntSrc, List.filter_append]

theorem cntSrc_singleton (s d u : ℕ) : cntSrc [(s, d)] u = if s = u then 1 else 0 := by
  simp only [cntSrc, List.filter_singleton]
  split <;> simp_all

theorem cntSrc_cons (s d : ℕ) (L : List (ℕ × ℕ)) (u : ℕ) :
    cntSrc ((s, d) :: L) u = (if s = u then 1 else 0) + cntSrc L u := by
  rw [← List.singleton_append, cntSrc_append, cntSrc_singleton]

theorem cntSrc_le_length (L : List (ℕ × ℕ)) (u : ℕ) : cntSrc L u ≤ L.length :=
  List.length_filter_le _ _

theorem cntSrc_le_of_prefix {L M : List (ℕ × ℕ)} (h : L <+: M) (u : ℕ) :
    cntSrc L u ≤ cntSrc M u := by
  obtain ⟨R, rfl⟩ := h
  rw [cntSrc_append]; omega

theorem cntSrc_eq_zero {L : List (ℕ × ℕ)} {n : ℕ} (h : ∀ e ∈ L, e.1 < n) {u : ℕ} (hu : n ≤ u) :
    cntSrc L u = 0 := by
  unfold cntSrc
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro e he
  have := h e he
  simp; omega

/-- The out-degree of `u` in the whole graph. -/
def degF (u : ℕ) : ℕ := cntSrc (edges F) u

theorem degF_eq_zero (hw : WidthOk F) {u : ℕ} (hu : N F ≤ u) : degF F u = 0 :=
  cntSrc_eq_zero (fun e he => (edge_ends_lt F hw (u := e.1) (v := e.2) he).1) hu

theorem cntSrc_le_degF {L : List (ℕ × ℕ)} (h : L <+: edges F) (u : ℕ) :
    cntSrc L u ≤ degF F u := cntSrc_le_of_prefix h u

theorem length_le_of_prefix {L : List (ℕ × ℕ)} (h : L <+: edges F) :
    L.length ≤ (lits F).length := h.length_le.trans (length_edges_le F)

/-! ### Prefix sums -/

/-- `sumBelow f n = f 0 + ⋯ + f (n - 1)`. -/
def sumBelow (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumBelow f n + f n

@[simp] theorem sumBelow_zero (f : ℕ → ℕ) : sumBelow f 0 = 0 := rfl

@[simp] theorem sumBelow_succ (f : ℕ → ℕ) (n : ℕ) : sumBelow f (n + 1) = sumBelow f n + f n := rfl

theorem sumBelow_congr {f g : ℕ → ℕ} {n : ℕ} (h : ∀ u, u < n → f u = g u) :
    sumBelow f n = sumBelow g n := by
  induction n with
  | zero => rw [sumBelow_zero, sumBelow_zero]
  | succ n ih => rw [sumBelow_succ, sumBelow_succ, ih (fun u hu => h u (by omega)), h n (by omega)]

theorem sumBelow_add (f g : ℕ → ℕ) (n : ℕ) :
    sumBelow (fun u => f u + g u) n = sumBelow f n + sumBelow g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumBelow_succ, ih]; ring

theorem sumBelow_indicator (s n : ℕ) :
    sumBelow (fun u => if s = u then 1 else 0) n = if s < n then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sumBelow_succ, ih]
    split_ifs <;> omega

theorem sumBelow_mono (f : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) : sumBelow f a ≤ sumBelow f b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact le_rfl
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · exact (ih (by omega)).trans (by rw [sumBelow_succ]; omega)
    · have : a = b + 1 := by omega
      subst this; exact le_rfl

/-- **Every slot below the total has an owner.** -/
theorem sumBelow_owner (f : ℕ → ℕ) (n j : ℕ) (hj : j < sumBelow f n) :
    ∃ u, u < n ∧ sumBelow f u ≤ j ∧ j < sumBelow f (u + 1) := by
  induction n with
  | zero => simp at hj
  | succ n ih =>
    rcases Nat.lt_or_ge j (sumBelow f n) with h | h
    · obtain ⟨u, hu, h1, h2⟩ := ih h
      exact ⟨u, by omega, h1, h2⟩
    · exact ⟨n, by omega, h, hj⟩

/-- **The counts add up to the length** when every source is below `n`. -/
theorem sumBelow_cntSrc (L : List (ℕ × ℕ)) (n : ℕ) (h : ∀ e ∈ L, e.1 < n) :
    sumBelow (cntSrc L) n = L.length := by
  induction L with
  | nil =>
    clear h
    induction n with
    | zero => rfl
    | succ n ih => rw [sumBelow_succ, ih, cntSrc_nil, Nat.add_zero]
  | cons e L ih =>
    obtain ⟨s, d⟩ := e
    rw [sumBelow_congr (g := fun u => (if s = u then 1 else 0) + cntSrc L u)
      (fun u _ => cntSrc_cons s d L u), sumBelow_add, sumBelow_indicator,
      ih (fun e he => h e (List.mem_cons_of_mem _ he)), if_pos (h (s, d) (List.mem_cons_self))]
    simp only [List.length_cons]; omega

/-- The offsets: `S u` is the number of edges leaving nodes below `u`. -/
def S (u : ℕ) : ℕ := sumBelow (degF F) u

theorem S_zero : S F 0 = 0 := rfl

theorem S_succ (u : ℕ) : S F (u + 1) = S F u + degF F u := rfl

theorem S_le_succ (u : ℕ) : S F u ≤ S F (u + 1) := by rw [S_succ]; omega

theorem S_mono {a b : ℕ} (h : a ≤ b) : S F a ≤ S F b := sumBelow_mono _ h

theorem S_N (hw : WidthOk F) : S F (N F) = (edges F).length :=
  sumBelow_cntSrc _ _ fun e he => (edge_ends_lt F hw (u := e.1) (v := e.2) he).1

theorem S_of_ge (hw : WidthOk F) {u : ℕ} (hu : N F ≤ u) : S F u = S F (N F) := by
  induction u with
  | zero => have : N F = 0 := by omega
            rw [this]
  | succ u ih =>
    rcases Nat.lt_or_ge u (N F) with h | h
    · have : u + 1 = N F := by omega
      rw [this]
    · rw [S_succ, ih h, degF_eq_zero F hw h, Nat.add_zero]

theorem S_le_E (hw : WidthOk F) (u : ℕ) : S F u ≤ (edges F).length := by
  rcases Nat.lt_or_ge u (N F) with h | h
  · rw [← S_N F hw]; exact S_mono F h.le
  · rw [S_of_ge F hw h, S_N F hw]


theorem S_succ_le_E (hw : WidthOk F) (u : ℕ) : S F u + degF F u ≤ (edges F).length := by
  rw [← S_succ]; exact S_le_E F hw _

/-- **Rows are disjoint**: a slot of row `u` is not a slot of row `s ≠ u`. -/
theorem row_disjoint {u s j j' : ℕ} (hus : u ≠ s)
    (hj : S F u ≤ j) (hj' : j < S F (u + 1)) (hs : S F s ≤ j') (hs' : j' < S F (s + 1)) :
    j ≠ j' := by
  rcases Nat.lt_or_gt_of_ne hus with h | h
  · have := S_mono F (show u + 1 ≤ s by omega); omega
  · have := S_mono F (show s + 1 ≤ u by omega); omega

/-! ### The degree array during the first pass -/

theorem cntSrc_step2 {n : ℕ} {g : ℕ → ℕ} {L : List (ℕ × ℕ)} (hg : ∀ u, u < n → g u = cntSrc L u)
    (X Y d₁ d₂ : ℕ) :
    ∀ u, u < n → upd (upd g X (g X + 1)) Y (upd g X (g X + 1) Y + 1) u =
      cntSrc (L ++ [(X, d₁), (Y, d₂)]) u := by
  intro u hu
  rw [cntSrc_append, cntSrc_cons, cntSrc_singleton]
  have := hg u hu
  simp only [upd_apply]
  split_ifs <;> subst_vars <;> omega

theorem cntSrc_step1 {n : ℕ} {g : ℕ → ℕ} {L : List (ℕ × ℕ)} (hg : ∀ u, u < n → g u = cntSrc L u)
    (X d : ℕ) :
    ∀ u, u < n → upd g X (g X + 1) u = cntSrc (L ++ [(X, d)]) u := by
  intro u hu
  rw [cntSrc_append, cntSrc_singleton]
  have := hg u hu
  simp only [upd_apply]
  split_ifs <;> subst_vars <;> omega

/-! ### The fill invariant -/

/-- `RowState F L p t`: with the edges `L` emitted so far, `p u` is the next free slot of row
`u`, every filled slot of row `u` holds an out-neighbour of `u` in `L`, and every edge of `L`
sits in a filled slot of its row. -/
structure RowState (L : List (ℕ × ℕ)) (p t : ℕ → ℕ) : Prop where
  pos : ∀ u, u < N F → p u = S F u + cntSrc L u
  sound : ∀ u, u < N F → ∀ j, S F u ≤ j → j < p u → (u, t j) ∈ L
  complete : ∀ e ∈ L, ∃ j, S F e.1 ≤ j ∧ j < p e.1 ∧ t j = e.2

theorem rowState_nil {p t : ℕ → ℕ} (hp : ∀ u, u < N F → p u = S F u) : RowState F [] p t where
  pos u hu := by rw [hp u hu]; simp
  sound u hu j h1 h2 := by rw [hp u hu] at h2; omega
  complete e he := by simp at he

theorem RowState.p_lt (_hw : WidthOk F) {L : List (ℕ × ℕ)} {p t : ℕ → ℕ} (hR : RowState F L p t)
    {s d : ℕ} (hpre : L ++ [(s, d)] <+: edges F) (hs : s < N F) : p s < S F (s + 1) := by
  have h1 := cntSrc_le_degF F hpre s
  rw [cntSrc_append, cntSrc_singleton, if_pos rfl] at h1
  rw [hR.pos s hs, S_succ]; omega

theorem RowState.p_lt_E (hw : WidthOk F) {L : List (ℕ × ℕ)} {p t : ℕ → ℕ} (hR : RowState F L p t)
    {s d : ℕ} (hpre : L ++ [(s, d)] <+: edges F) (hs : s < N F) : p s < (edges F).length :=
  (hR.p_lt F hw hpre hs).trans_le (S_le_E F hw _)

theorem RowState.p_ge (_hw : WidthOk F) {L : List (ℕ × ℕ)} {p t : ℕ → ℕ} (hR : RowState F L p t)
    {u : ℕ} (hu : u < N F) : S F u ≤ p u := by rw [hR.pos u hu]; omega

theorem RowState.p_le (_hw : WidthOk F) {L : List (ℕ × ℕ)} {p t : ℕ → ℕ} (hR : RowState F L p t)
    (hpre : L <+: edges F) {u : ℕ} (hu : u < N F) : p u ≤ S F (u + 1) := by
  rw [hR.pos u hu, S_succ]; have := cntSrc_le_degF F hpre u; omega

/-- **Emitting one edge.** -/
theorem RowState.emit (hw : WidthOk F) {L : List (ℕ × ℕ)} {p t : ℕ → ℕ} (hR : RowState F L p t)
    {s d : ℕ} (hpre : L ++ [(s, d)] <+: edges F) (hs : s < N F) :
    RowState F (L ++ [(s, d)]) (upd p s (p s + 1)) (upd t (p s) d) := by
  have hpreL : L <+: edges F := (List.prefix_append L _).trans hpre
  have hps := hR.p_lt F hw hpre hs
  have hpsge := hR.p_ge F hw hs
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    have hpu := hR.pos u hu
    have hps' := hR.pos s hs
    rw [cntSrc_append, cntSrc_singleton, upd_apply]
    split_ifs <;> subst_vars <;> omega
  · intro u hu j h1 h2
    rw [upd_apply] at h2
    by_cases hus : u = s
    · subst hus
      rw [if_pos rfl] at h2
      rcases Nat.lt_or_ge j (p u) with hlt | hge
      · rw [upd_of_ne _ (by omega)]
        exact List.mem_append_left _ (hR.sound u hu j h1 hlt)
      · have : j = p u := by omega
        subst this
        rw [upd_self]; simp
    · rw [if_neg hus] at h2
      have hle := hR.p_le F hw hpreL hu
      have hne : j ≠ p s := row_disjoint F hus h1 (by omega) hpsge hps
      rw [upd_of_ne _ hne]
      exact List.mem_append_left _ (hR.sound u hu j h1 h2)
  · intro e he
    rw [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · obtain ⟨j, h1, h2, h3⟩ := hR.complete e he
      have heN : e.1 < N F :=
        (edge_ends_lt F hw (u := e.1) (v := e.2) (mem_edges_of_prefix F hpreL he)).1
      refine ⟨j, h1, ?_, ?_⟩
      · rw [upd_apply]
        split_ifs with h
        · rw [h] at h2; omega
        · omega
      · by_cases hes : e.1 = s
        · rw [upd_of_ne _ (by rw [hes] at h2; omega)]; exact h3
        · have hle := hR.p_le F hw hpreL heN
          rw [upd_of_ne _ (row_disjoint F hes h1 (by omega) hpsge hps)]; exact h3
    · exact ⟨p s, hpsge, by rw [upd_self]; omega, by rw [upd_self]⟩

/-- **The rows at the end.** -/
theorem RowState.done (hw : WidthOk F) {p t : ℕ → ℕ} (hR : RowState F (edges F) p t) (u v : ℕ) :
    (∃ j, S F u ≤ j ∧ j < S F (u + 1) ∧ t j = v) ↔ E F u v := by
  constructor
  · rintro ⟨j, h1, h2, rfl⟩
    rcases Nat.lt_or_ge u (N F) with hu | hu
    · have hp : p u = S F (u + 1) := by rw [hR.pos u hu, S_succ]; rfl
      exact hR.sound u hu j h1 (hp ▸ h2)
    · rw [S_succ, degF_eq_zero F hw hu] at h2; omega
  · intro h
    obtain ⟨j, h1, h2, h3⟩ := hR.complete (u, v) h
    have hu := (edge_ends_lt F hw h).1
    refine ⟨j, h1, ?_, h3⟩
    simp only at h2
    rw [hR.pos u hu] at h2; rw [S_succ]; exact h2

theorem RowState.target_lt (hw : WidthOk F) {p t : ℕ → ℕ} (hR : RowState F (edges F) p t)
    {j : ℕ} (hj : j < (edges F).length) : t j < N F := by
  rw [← S_N F hw] at hj
  obtain ⟨u, hu, h1, h2⟩ := sumBelow_owner _ _ _ hj
  have hp : p u = S F (u + 1) := by rw [hR.pos u hu, S_succ]; rfl
  exact (edge_ends_lt F hw (hR.sound u hu j h1 (hp ▸ h2))).2

end Lax117284Proofs.TwoSAT.Machine.Build

end

/-! ### `Lax117284Proofs.TwoSAT.Machine.Build` -/

section
/-!
Building the implication graph's CSR representation from the scanned formula, by counting
sort: three passes over the clauses.

* **degrees** — one pass over the clauses, incrementing `deg[src]` for every edge a clause
  contributes;
* **prefix sums** — `off[u + 1] = off[u] + deg[u]`, with `pos[u] = off[u]` the next free
  slot of each row, and the scalar `E` set to `off[N]`, the number of edges;
* **fill** — the same walk as the first pass, writing every edge `(src, dst)` at slot
  `pos[src]` of `tgt` and advancing `pos[src]`.

Each pass over the clauses keeps a running literal pointer `i`, which stands at `start F c`
at the top of the turn for clause `c`; a clause with `cnt[c] = 1` literal reads position `i`
and moves the pointer by one, a clause with two literals reads `i` and `i + 1` and moves it
by two. The unit clause `[a]` contributes the edge `¬a → a`; the clause `[a, b]` the edges
`¬a → b` and `¬b → a`, in that order (`clauseEdges`).

The specification `build_spec` says that afterwards `off`/`tgt` form a CSR structure
(`Lib.Csr`) whose row `u` lists exactly the out-neighbours of `u` in `edges F`.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Build

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax429075.CNF Lax391470Proofs.L2ScanModel Lax117284Proofs.TwoSAT.Machine.Model

/-- Collapse a chain of `setVar`/`setArr` updates: the projections, the string keys decided,
and whatever else is handed over. -/
syntax "env_simp" (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
  Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| env_simp) =>
    `(tactic| simp only [Env.setVar, Env.setArr, String.reduceEq, reduceIte])
  | `(tactic| env_simp [$ts,*]) =>
    `(tactic| simp only [Env.setVar, Env.setArr, String.reduceEq, reduceIte, $ts,*])

/-! ### The program -/

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.add (V s) (.lit 1))

/-- `2 * vr[e] + sg[e]`: the code of the literal at position `e`. -/
abbrev codeAt (e : Expr) : Expr := .add (.mul (.lit 2) (.get "vr" e)) (.get "sg" e)

/-- `2 * vr[e] + (1 - sg[e])`: the code of the negation of the literal at position `e`. -/
abbrev ncodeAt (e : Expr) : Expr := .add (.mul (.lit 2) (.get "vr" e)) (.sub (.lit 1) (.get "sg" e))

/-- `a[x] := a[x] + 1`. -/
abbrev inc (a x : String) : Com := .store a (V x) (.add (.get a (V x)) (.lit 1))

/-- The turn of the degree pass for a unit clause. -/
def degUnit : Com := .seq (.assign "na" (ncodeAt (V "i"))) (.seq (inc "deg" "na") (bump "i"))

/-- The turn of the degree pass for a clause of two literals. -/
def degPair : Com :=
  .seq (.assign "na" (ncodeAt (V "i")))
    (.seq (.assign "nb" (ncodeAt (.add (V "i") (.lit 1))))
      (.seq (inc "deg" "na") (.seq (inc "deg" "nb") (.assign "i" (.add (V "i") (.lit 2))))))

def degBody : Com := .seq (.ite (.eq (.get "cnt" (V "c")) (.lit 1)) degUnit degPair) (bump "c")

/-- Pass (a): the out-degrees. -/
def degPass : Com :=
  .seq (.assign "i" (.lit 0))
    (.seq (.assign "c" (.lit 0)) (.while (.lt (V "c") (V "C")) degBody))

/-- One turn of the prefix sums: `pos[u] := off[u]; off[u + 1] := off[u] + deg[u]`. -/
def prefBody : Com :=
  .seq (.store "pos" (V "u") (.get "off" (V "u")))
    (.seq (.store "off" (.add (V "u") (.lit 1)) (.add (.get "off" (V "u")) (.get "deg" (V "u"))))
      (bump "u"))

/-- Pass (b): the offsets, the free-slot pointers, and the edge count `E`. -/
def prefPass : Com :=
  .seq (.store "off" (.lit 0) (.lit 0))
    (.seq (.seq (.assign "u" (.lit 0)) (.while (.lt (V "u") (V "N")) prefBody))
      (.assign "E" (.get "off" (V "N"))))

/-- Emit the edge `(x, y)`: `tgt[pos[x]] := y; pos[x] := pos[x] + 1`. -/
abbrev put (x y : String) : Com := .seq (.store "tgt" (.get "pos" (V x)) (V y)) (inc "pos" x)

def fillUnit : Com :=
  .seq (.assign "ca" (codeAt (V "i")))
    (.seq (.assign "na" (ncodeAt (V "i"))) (.seq (put "na" "ca") (bump "i")))

def fillPair : Com :=
  .seq (.assign "ca" (codeAt (V "i")))
    (.seq (.assign "na" (ncodeAt (V "i")))
      (.seq (.assign "cb" (codeAt (.add (V "i") (.lit 1))))
        (.seq (.assign "nb" (ncodeAt (.add (V "i") (.lit 1))))
          (.seq (put "na" "cb") (.seq (put "nb" "ca") (.assign "i" (.add (V "i") (.lit 2))))))))

def fillBody : Com := .seq (.ite (.eq (.get "cnt" (V "c")) (.lit 1)) fillUnit fillPair) (bump "c")

/-- Pass (c): the targets. -/
def fillPass : Com :=
  .seq (.assign "i" (.lit 0))
    (.seq (.assign "c" (.lit 0)) (.while (.lt (V "c") (V "C")) fillBody))

/-- The whole construction. -/
def build : Com := .seq degPass (.seq prefPass fillPass)

/-! ### What every pass keeps -/

/-- The scalars and arrays the scan left, which no pass changes. -/
def Static (F : Formula) (σ : Env) : Prop :=
  σ.vars "k" = (lits F).length ∧ σ.vars "C" = F.length ∧ σ.vars "N" = N F ∧
    (lits F).length ≤ (σ.arrs "vr").length ∧ (lits F).length ≤ (σ.arrs "sg").length ∧
    F.length + 1 ≤ (σ.arrs "cnt").length ∧
    (∀ i, i < (lits F).length → (σ.arrs "vr").getD i 0 = iv F i) ∧
    (∀ i, i < (lits F).length → (σ.arrs "sg").getD i 0 = sv F i) ∧
    (∀ c, c < F.length → (σ.arrs "cnt").getD c 0 = (F.getD c []).length)

theorem Static.of_eq {F : Formula} {σ σ' : Env} (h : Static F σ) (hk : σ'.vars "k" = σ.vars "k")
    (hC : σ'.vars "C" = σ.vars "C") (hN : σ'.vars "N" = σ.vars "N")
    (hvr : σ'.arrs "vr" = σ.arrs "vr") (hsg : σ'.arrs "sg" = σ.arrs "sg")
    (hcnt : σ'.arrs "cnt" = σ.arrs "cnt") : Static F σ' := by
  unfold Static at h ⊢
  rw [hk, hC, hN, hvr, hsg, hcnt]; exact h

/-- The degree array holds the out-degrees in `L`. -/
def Deg (F : Formula) (L : List (ℕ × ℕ)) (σ : Env) : Prop :=
  ∃ g, σ.arrs "deg" = arrOf (N F + 1) g ∧ ∀ u, u < N F + 1 → g u = cntSrc L u

theorem Deg.of_eq {F : Formula} {L : List (ℕ × ℕ)} {σ σ' : Env} (h : Deg F L σ)
    (hd : σ'.arrs "deg" = σ.arrs "deg") : Deg F L σ' := by
  unfold Deg at h ⊢; rw [hd]; exact h

/-- The free-slot pointers and the targets, with `L` emitted. -/
def Rows (F : Formula) (L : List (ℕ × ℕ)) (σ : Env) : Prop :=
  ∃ p t, σ.arrs "pos" = arrOf (N F + 1) p ∧ σ.arrs "tgt" = arrOf (edges F).length t ∧
    RowState F L p t

/-! ### Pass (a): the degrees -/

def DegInv (F : Formula) (σ : Env) : Prop :=
  Static F σ ∧ σ.vars "c" ≤ F.length ∧ σ.vars "i" = start F (σ.vars "c") ∧
    Deg F (edgesUpTo F (σ.vars "c")) σ

variable {F : Formula}

theorem degBody_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => DegInv F σ ∧ σ.vars "c" < F.length) degBody
      (fun σ σ' => DegInv F σ' ∧ σ'.vars "c" = σ.vars "c" + 1) 50 := by
  intro σ hσ
  obtain ⟨⟨hS, hcC, hi, hD⟩, hc⟩ := hσ
  have hS' := hS
  obtain ⟨hk, hC, hN, hvrl, hsgl, hcntl, hvr, hsg, hcnt⟩ := hS'
  obtain ⟨g, hdeg, hg⟩ := hD
  have hlen := hcnt _ hc
  have hst := start_add_le F _ hc
  have hcases := clause_length_cases F hw _ hc
  have hvr0 : (σ.arrs "vr").getD (σ.vars "i") 0 = iv F (σ.vars "i") := hvr (σ.vars "i") (by omega)
  have hsg0 : (σ.arrs "sg").getD (σ.vars "i") 0 = sv F (σ.vars "i") := hsg (σ.vars "i") (by omega)
  have hiv0 := two_iv_add_two_le F (σ.vars "i")
  have hiv1 := two_iv_add_two_le F (σ.vars "i" + 1)
  have hsv0 := sv_le F (σ.vars "i")
  have hsv1 := sv_le F (σ.vars "i" + 1)
  have hdegl : (σ.arrs "deg").length = N F + 1 := by rw [hdeg, length_arrOf]
  have hgle : ∀ u, u < N F + 1 → g u ≤ (lits F).length := fun u hu => by
    rw [hg u hu]
    exact (cntSrc_le_length _ _).trans (length_le_of_prefix F (edgesUpTo_prefix F _))
  have hX : 2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")) < N F + 1 := by omega
  have hY : 2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1)) < N F + 1 := by omega
  have hd0 : (σ.arrs "deg").getD (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) 0
      ≤ (lits F).length := by
    rw [hdeg, getD_arrOf _ hX]; exact hgle _ hX
  rcases hcases with h1 | h2
  · -- a unit clause
    run_vcg
    all_goals try (env_simp [List.length_set, hvr0, hsg0]; omega)
    refine ⟨⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), ?_, ?_, ?_⟩, ?_⟩
    · env_simp; omega
    · env_simp
      rw [start_succ F _ hc]; omega
    · refine ⟨upd g (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
        (g (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1), ?_, ?_⟩
      · env_simp [hvr0, hsg0]
        rw [hdeg, getD_arrOf _ hX, set_arrOf_eq_upd]
      · env_simp
        rw [edgesUpTo_succ F _ hc, clauseEdges_unit F _ hc h1, ← hi]
        exact cntSrc_step1 hg _ _
    · env_simp
  · -- a clause of two literals
    have hvr1 : (σ.arrs "vr").getD (σ.vars "i" + 1) 0 = iv F (σ.vars "i" + 1) :=
      hvr (σ.vars "i" + 1) (by omega)
    have hsg1 : (σ.arrs "sg").getD (σ.vars "i" + 1) 0 = sv F (σ.vars "i" + 1) :=
      hsg (σ.vars "i" + 1) (by omega)
    have hd1 : ((σ.arrs "deg").set (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
          ((σ.arrs "deg").getD (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) 0 + 1)).getD
          (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1))) 0 ≤ (lits F).length + 1 := by
      rw [hdeg, getD_arrOf _ hX, set_arrOf_eq_upd, getD_arrOf _ hY]
      exact upd_le (by have := hgle _ hX; omega) (by have := hgle _ hY; omega)
    run_vcg
    all_goals try (env_simp [List.length_set, hvr0, hsg0, hvr1, hsg1]; omega)
    refine ⟨⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), ?_, ?_, ?_⟩, ?_⟩
    · env_simp; omega
    · env_simp
      rw [start_succ F _ hc]; omega
    · refine ⟨upd (upd g (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
          (g (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1))
          (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1)))
          (upd g (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
            (g (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1)
            (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1))) + 1), ?_, ?_⟩
      · env_simp [hvr0, hsg0, hvr1, hsg1]
        rw [hdeg, getD_arrOf _ hX, set_arrOf_eq_upd, getD_arrOf _ hY, set_arrOf_eq_upd]
      · env_simp
        rw [edgesUpTo_succ F _ hc, clauseEdges_pair F _ hc h2, ← hi]
        exact cntSrc_step2 hg _ _ _ _
    · env_simp

theorem degLoop_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => DegInv F (σ.setVar "c" 0))
      (.seq (.assign "c" (.lit 0)) (.while (.lt (V "c") (V "C")) degBody))
      (fun _ σ' => DegInv F σ' ∧ σ'.vars "c" = F.length) (54 * F.length + 6) :=
  Spec.forRangeZero "c" "C" (DegInv F) F.length 50 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2.1) (degBody_spec hw hB)

theorem degPass_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => Static F σ ∧ σ.arrs "deg" = List.replicate (N F + 1) 0) degPass
      (fun _ σ' => Static F σ' ∧ Deg F (edges F) σ') (54 * F.length + 8) := by
  refine (Spec.seq (Spec.assign (x := "i") (e := .lit 0) (f := fun _ => 0)
    (fun _ _ => evalB_lit (by omega))) (degLoop_spec hw hB) ?_ ?_).mono (by simp only [size_lit]; omega)
  · rintro σ σ' ⟨hS, hdeg⟩ rfl
    refine ⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), by simp,
      by simp [start_zero], fun _ => 0, ?_, ?_⟩
    · simp [hdeg, replicate_eq_arrOf]
    · simp [edgesUpTo_zero]
  · rintro σ σ' σ'' - - ⟨⟨hS, -, -, hD⟩, hc⟩
    rw [hc, edgesUpTo_length] at hD
    exact ⟨hS, hD⟩

/-! ### Pass (b): the prefix sums -/

def PInv (F : Formula) (σ : Env) : Prop :=
  Static F σ ∧ σ.vars "u" ≤ N F ∧ Deg F (edges F) σ ∧
    (∃ o, σ.arrs "off" = arrOf (N F + 1) o ∧ ∀ v, v ≤ σ.vars "u" → o v = S F v) ∧
    (∃ p, σ.arrs "pos" = arrOf (N F + 1) p ∧ ∀ v, v < σ.vars "u" → p v = S F v)

theorem prefBody_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => PInv F σ ∧ σ.vars "u" < N F) prefBody
      (fun σ σ' => PInv F σ' ∧ σ'.vars "u" = σ.vars "u" + 1) 20 := by
  intro σ hσ
  obtain ⟨⟨hS, huN, ⟨g, hdeg, hg⟩, ⟨o, hoff, ho⟩, ⟨p, hpos, hp⟩⟩, hu⟩ := hσ
  have hEk : (edges F).length ≤ (lits F).length := length_edges_le F
  have hSE := S_succ_le_E F hw (σ.vars "u")
  have hoffl : (σ.arrs "off").length = N F + 1 := by rw [hoff, length_arrOf]
  have hposl : (σ.arrs "pos").length = N F + 1 := by rw [hpos, length_arrOf]
  have hdegl : (σ.arrs "deg").length = N F + 1 := by rw [hdeg, length_arrOf]
  have hoff0 : (σ.arrs "off").getD (σ.vars "u") 0 = S F (σ.vars "u") := by
    rw [hoff, getD_arrOf _ (by omega)]; exact ho _ le_rfl
  have hdeg0 : (σ.arrs "deg").getD (σ.vars "u") 0 = degF F (σ.vars "u") := by
    rw [hdeg, getD_arrOf _ (by omega)]; exact hg _ (by omega)
  run_vcg
  all_goals try (env_simp [List.length_set, hoff0, hdeg0]; omega)
  refine ⟨⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), ?_, ?_, ?_, ?_⟩, ?_⟩
  · env_simp; omega
  · refine ⟨g, ?_, hg⟩
    env_simp; exact hdeg
  · refine ⟨upd o (σ.vars "u" + 1) (S F (σ.vars "u") + degF F (σ.vars "u")), ?_, ?_⟩
    · env_simp [hoff0, hdeg0]
      rw [hoff, set_arrOf_eq_upd]
    · env_simp
      intro v hv
      rw [upd_apply]
      split_ifs with h
      · rw [h, S_succ]
      · exact ho v (by omega)
  · refine ⟨upd p (σ.vars "u") (S F (σ.vars "u")), ?_, ?_⟩
    · env_simp [hoff0]
      rw [hpos, set_arrOf_eq_upd]
    · env_simp
      intro v hv
      rw [upd_apply]
      split_ifs with h
      · rw [h]
      · exact hp v (by omega)
  · env_simp

theorem prefLoop_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => PInv F (σ.setVar "u" 0))
      (.seq (.assign "u" (.lit 0)) (.while (.lt (V "u") (V "N")) prefBody))
      (fun _ σ' => PInv F σ' ∧ σ'.vars "u" = N F) (24 * N F + 6) :=
  Spec.forRangeZero "u" "N" (PInv F) (N F) 20 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2.2.1) (prefBody_spec hw hB)

/-- The loop and the final `E := off[N]`. -/
theorem prefTail_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => PInv F (σ.setVar "u" 0))
      (.seq (.seq (.assign "u" (.lit 0)) (.while (.lt (V "u") (V "N")) prefBody))
        (.assign "E" (.get "off" (V "N"))))
      (fun _ σ' => Static F σ' ∧ σ'.arrs "off" = arrOf (N F + 1) (S F) ∧
        (∃ p, σ'.arrs "pos" = arrOf (N F + 1) p ∧ ∀ v, v < N F → p v = S F v) ∧
        σ'.vars "E" = (edges F).length) (24 * N F + 10) := by
  have hEk : (edges F).length ≤ (lits F).length := length_edges_le F
  refine (Spec.seq (prefLoop_spec hw hB)
    (Spec.assign (P := fun σ => PInv F σ ∧ σ.vars "u" = N F) (x := "E") (e := .get "off" (V "N"))
      (f := fun σ => (σ.arrs "off").getD (σ.vars "N") 0) ?_) (fun _ _ _ h => h) ?_).mono ?_
  · rintro σ ⟨⟨hS, -, -, ⟨o, hoff, ho⟩, -⟩, hu⟩
    have hN := hS.2.2.1
    have hoN : o (N F) = S F (N F) := ho _ (by omega)
    show (Expr.get "off" (V "N")).evalB B σ = some ((σ.arrs "off").getD (σ.vars "N") 0)
    rw [hN]
    refine evalB_get (evalB_var (by omega)) ?_ ?_
    · rw [hN, hoff, getElem?_arrOf _ (by omega), getD_arrOf _ (by omega)]
    · rw [hoff, getD_arrOf _ (by omega), hoN, S_N F hw]; omega
  · rintro σ σ' σ'' - ⟨⟨hS, -, -, ⟨o, hoff, ho⟩, ⟨p, hpos, hp⟩⟩, hu⟩ rfl
    refine ⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), ?_, ?_, ?_⟩
    · simp only [arrs_setVar]
      rw [hoff]; exact arrOf_congr fun v hv => ho v (by omega)
    · exact ⟨p, by simp only [arrs_setVar]; exact hpos, fun v hv => hp v (by omega)⟩
    · env_simp
      rw [hS.2.2.1, hoff, getD_arrOf _ (by omega), ho _ (by omega), S_N F hw]
  · simp only [size_get, size_var]; omega

theorem prefPass_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => Static F σ ∧ Deg F (edges F) σ ∧
        σ.arrs "off" = List.replicate (N F + 1) 0 ∧ σ.arrs "pos" = List.replicate (N F + 1) 0)
      prefPass
      (fun _ σ' => Static F σ' ∧ σ'.arrs "off" = arrOf (N F + 1) (S F) ∧
        (∃ p, σ'.arrs "pos" = arrOf (N F + 1) p ∧ ∀ v, v < N F → p v = S F v) ∧
        σ'.vars "E" = (edges F).length) (24 * N F + 13) := by
  refine (Spec.seq (Spec.store (a := "off") (i := .lit 0) (e := .lit 0) (idx := fun _ => 0)
      (f := fun _ => 0) (fun _ _ => evalB_lit (by omega)) (fun _ _ => evalB_lit (by omega))
      (fun σ h => by rw [h.2.2.1]; simp))
    (prefTail_spec hw hB) ?_ (fun _ _ _ _ _ h => h)).mono ?_
  · rintro σ σ' ⟨hS, hD, hoff, hpos⟩ rfl
    refine ⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), by simp,
      hD.of_eq (by simp), ⟨upd (fun _ => 0) 0 0, ?_, ?_⟩, ⟨fun _ => 0, ?_, ?_⟩⟩
    · env_simp
      rw [hoff, replicate_eq_arrOf, set_arrOf_eq_upd]
    · env_simp
      intro v hv
      have : v = 0 := by omega
      subst this
      have h0 := S_zero (F := F)
      simp [h0]
    · env_simp
      rw [hpos, replicate_eq_arrOf]
    · simp
  · simp only [size_lit]; omega

/-! ### Pass (c): the fill -/

def FInv (F : Formula) (σ : Env) : Prop :=
  Static F σ ∧ σ.vars "c" ≤ F.length ∧ σ.vars "i" = start F (σ.vars "c") ∧
    σ.vars "E" = (edges F).length ∧ σ.arrs "off" = arrOf (N F + 1) (S F) ∧
    Rows F (edgesUpTo F (σ.vars "c")) σ

set_option maxHeartbeats 4000000 in
theorem fillBody_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => FInv F σ ∧ σ.vars "c" < F.length) fillBody
      (fun σ σ' => FInv F σ' ∧ σ'.vars "c" = σ.vars "c" + 1) 80 := by
  intro σ hσ
  obtain ⟨⟨hS, hcC, hi, hE, hoff, hR⟩, hc⟩ := hσ
  have hS' := hS
  obtain ⟨hk, hC, hN, hvrl, hsgl, hcntl, hvr, hsg, hcnt⟩ := hS'
  obtain ⟨p, t, hpos, htgt, hRS⟩ := hR
  have hlen := hcnt _ hc
  have hst := start_add_le F _ hc
  have hcases := clause_length_cases F hw _ hc
  have hvr0 : (σ.arrs "vr").getD (σ.vars "i") 0 = iv F (σ.vars "i") := hvr (σ.vars "i") (by omega)
  have hsg0 : (σ.arrs "sg").getD (σ.vars "i") 0 = sv F (σ.vars "i") := hsg (σ.vars "i") (by omega)
  have hiv0 := two_iv_add_two_le F (σ.vars "i")
  have hiv1 := two_iv_add_two_le F (σ.vars "i" + 1)
  have hsv0 := sv_le F (σ.vars "i")
  have hsv1 := sv_le F (σ.vars "i" + 1)
  have hEk : (edges F).length ≤ (lits F).length := length_edges_le F
  have hposl : (σ.arrs "pos").length = N F + 1 := by rw [hpos, length_arrOf]
  have htgtl : (σ.arrs "tgt").length = (edges F).length := by rw [htgt, length_arrOf]
  have hX : 2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")) < N F := by omega
  have hY : 2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1)) < N F := by omega
  have hpX : (σ.arrs "pos").getD (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) 0 =
      p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) := by
    rw [hpos, getD_arrOf _ (by omega)]
  rcases hcases with h1 | h2
  · -- a unit clause: the edge `(¬a, a)`
    have hpre : edgesUpTo F (σ.vars "c") ++
        [(2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")), 2 * iv F (σ.vars "i") + sv F (σ.vars "i"))]
        <+: edges F := by
      have := edgesUpTo_succ_prefix F _ hc
      rwa [clauseEdges_unit F _ hc h1, ← hi] at this
    have hpXE := hRS.p_lt_E F hw hpre hX
    run_vcg
    all_goals try (env_simp [List.length_set, hvr0, hsg0, hpX]; omega)
    refine ⟨⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), ?_, ?_, ?_, ?_,
      ?_⟩, ?_⟩
    · env_simp; omega
    · env_simp
      rw [start_succ F _ hc]; omega
    · env_simp; exact hE
    · env_simp; exact hoff
    · refine ⟨upd p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
          (p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1),
        upd t (p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))))
          (2 * iv F (σ.vars "i") + sv F (σ.vars "i")), ?_, ?_, ?_⟩
      · env_simp [hvr0, hsg0, hpX]
        rw [hpos, set_arrOf_eq_upd]
      · env_simp [hvr0, hsg0, hpX]
        rw [htgt, set_arrOf_eq_upd]
      · env_simp
        rw [edgesUpTo_succ F _ hc, clauseEdges_unit F _ hc h1, ← hi]
        exact hRS.emit F hw hpre hX
    · env_simp
  · -- a clause of two literals: the edges `(¬a, b)` then `(¬b, a)`
    have hvr1 : (σ.arrs "vr").getD (σ.vars "i" + 1) 0 = iv F (σ.vars "i" + 1) :=
      hvr (σ.vars "i" + 1) (by omega)
    have hsg1 : (σ.arrs "sg").getD (σ.vars "i" + 1) 0 = sv F (σ.vars "i" + 1) :=
      hsg (σ.vars "i" + 1) (by omega)
    have hpre2 : edgesUpTo F (σ.vars "c") ++
        [(2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")),
            2 * iv F (σ.vars "i" + 1) + sv F (σ.vars "i" + 1)),
          (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1)),
            2 * iv F (σ.vars "i") + sv F (σ.vars "i"))] <+: edges F := by
      have := edgesUpTo_succ_prefix F _ hc
      rwa [clauseEdges_pair F _ hc h2, ← hi] at this
    have hpre2' : (edgesUpTo F (σ.vars "c") ++
        [(2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")),
            2 * iv F (σ.vars "i" + 1) + sv F (σ.vars "i" + 1))]) ++
          [(2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1)),
            2 * iv F (σ.vars "i") + sv F (σ.vars "i"))] <+: edges F := by
      rw [List.append_assoc, List.singleton_append]; exact hpre2
    have hpre1 : edgesUpTo F (σ.vars "c") ++
        [(2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")),
            2 * iv F (σ.vars "i" + 1) + sv F (σ.vars "i" + 1))] <+: edges F :=
      (List.prefix_append _ _).trans hpre2'
    have hR1 := hRS.emit F hw hpre1 hX
    have hR2 := hR1.emit F hw hpre2' hY
    rw [List.append_assoc, List.singleton_append] at hR2
    have hpXE := hRS.p_lt_E F hw hpre1 hX
    have hpY : ((σ.arrs "pos").set (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
          (p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1)).getD
          (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1))) 0 =
        upd p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
          (p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1)
          (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1))) := by
      rw [hpos, set_arrOf_eq_upd, getD_arrOf _ (by omega)]
    have hpYE := hR1.p_lt_E F hw hpre2' hY
    run_vcg
    all_goals try (env_simp [List.length_set, hvr0, hsg0, hvr1, hsg1, hpX, hpY]; omega)
    refine ⟨⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), ?_, ?_, ?_, ?_,
      ?_⟩, ?_⟩
    · env_simp; omega
    · env_simp
      rw [start_succ F _ hc]; omega
    · env_simp; exact hE
    · env_simp; exact hoff
    · refine ⟨upd (upd p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
            (p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1))
          (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1)))
          (upd p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
            (p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1)
            (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1))) + 1),
        upd (upd t (p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))))
            (2 * iv F (σ.vars "i" + 1) + sv F (σ.vars "i" + 1)))
          (upd p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
            (p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1)
            (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1))))
          (2 * iv F (σ.vars "i") + sv F (σ.vars "i")), ?_, ?_, ?_⟩
      · env_simp [hvr0, hsg0, hvr1, hsg1, hpX, hpY]
        rw [hpos, set_arrOf_eq_upd, set_arrOf_eq_upd]
      · env_simp [hvr0, hsg0, hvr1, hsg1, hpX, hpY]
        rw [htgt, set_arrOf_eq_upd, set_arrOf_eq_upd]
      · env_simp
        rw [edgesUpTo_succ F _ hc, clauseEdges_pair F _ hc h2, ← hi]
        exact hR2
    · env_simp

theorem fillLoop_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => FInv F (σ.setVar "c" 0))
      (.seq (.assign "c" (.lit 0)) (.while (.lt (V "c") (V "C")) fillBody))
      (fun _ σ' => FInv F σ' ∧ σ'.vars "c" = F.length) (84 * F.length + 6) :=
  Spec.forRangeZero "c" "C" (FInv F) F.length 80 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2.1) (fillBody_spec hw hB)

theorem fillPass_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => Static F σ ∧ σ.vars "E" = (edges F).length ∧
        σ.arrs "off" = arrOf (N F + 1) (S F) ∧
        (∃ p, σ.arrs "pos" = arrOf (N F + 1) p ∧ ∀ v, v < N F → p v = S F v) ∧
        σ.arrs "tgt" = List.replicate (edges F).length 0)
      fillPass
      (fun _ σ' => Static F σ' ∧ σ'.vars "E" = (edges F).length ∧
        σ'.arrs "off" = arrOf (N F + 1) (S F) ∧ Rows F (edges F) σ') (84 * F.length + 8) := by
  refine (Spec.seq (Spec.assign (x := "i") (e := .lit 0) (f := fun _ => 0)
    (fun _ _ => evalB_lit (by omega))) (fillLoop_spec hw hB) ?_ ?_).mono
    (by simp only [size_lit]; omega)
  · rintro σ σ' ⟨hS, hE, hoff, ⟨p, hpos, hp⟩, htgt⟩ rfl
    refine ⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), by simp,
      by simp [start_zero], by simp [hE], by simp [hoff], p, fun _ => 0, by simp [hpos],
      by simp [htgt, replicate_eq_arrOf], ?_⟩
    env_simp
    rw [edgesUpTo_zero]; exact rowState_nil F hp
  · rintro σ σ' σ'' - - ⟨⟨hS, -, -, hE, hoff, hR⟩, hc⟩
    rw [hc, edgesUpTo_length] at hR
    exact ⟨hS, hE, hoff, hR⟩

/-! ### The whole construction -/

/-- What the earlier phases leave: the scan's scalars and arrays (`Static`, plus the clause
numbers `cl`, which the construction does not read), and the four fresh arrays. -/
def Pre (F : Formula) (σ : Env) : Prop :=
  Static F σ ∧ (lits F).length ≤ (σ.arrs "cl").length ∧
    (∀ i, i < (lits F).length → (σ.arrs "cl").getD i 0 = cv F i) ∧
    σ.arrs "deg" = List.replicate (N F + 1) 0 ∧ σ.arrs "off" = List.replicate (N F + 1) 0 ∧
    σ.arrs "pos" = List.replicate (N F + 1) 0 ∧
    σ.arrs "tgt" = List.replicate (edges F).length 0

theorem off_not_warrs_degPass : "off" ∉ degPass.warrs := by decide
theorem pos_not_warrs_degPass : "pos" ∉ degPass.warrs := by decide
theorem tgt_not_warrs_degPass : "tgt" ∉ degPass.warrs := by decide
theorem tgt_not_warrs_prefPass : "tgt" ∉ prefPass.warrs := by decide

/-- **The construction is correct**: from the scanned formula it builds the CSR
representation of the implication graph — offsets `off`, targets `tgt`, with row `u`
listing exactly the out-neighbours of `u` — and sets `E` to the number of edges, in time
linear in the size of the formula. -/
theorem build_spec {B : ℕ} (F : Formula) (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (Pre F) build
      (fun _ σ' => ∃ off tgt : ℕ → ℕ,
        Lax808846Proofs.Reasoning.Lib.Csr "off" "tgt" (N F) (edges F).length (N F) off tgt σ' ∧
        (∀ u v, (∃ j, off u ≤ j ∧ j < off (u + 1) ∧ tgt j = v) ↔ E F u v) ∧
        σ'.vars "E" = (edges F).length ∧ σ'.vars "N" = N F ∧ σ'.vars "k" = (lits F).length ∧
        σ'.vars "C" = F.length)
      (138 * ((lits F).length + N F + F.length + 1)) := by
  have h2 := ((prefPass_spec hw hB).frame).conseq
    (P' := fun σ => (Static F σ ∧ Deg F (edges F) σ ∧
        σ.arrs "off" = List.replicate (N F + 1) 0 ∧ σ.arrs "pos" = List.replicate (N F + 1) 0) ∧
      σ.arrs "tgt" = List.replicate (edges F).length 0)
    (Q' := fun _ σ' => (Static F σ' ∧ σ'.arrs "off" = arrOf (N F + 1) (S F) ∧
        (∃ p, σ'.arrs "pos" = arrOf (N F + 1) p ∧ ∀ v, v < N F → p v = S F v) ∧
        σ'.vars "E" = (edges F).length) ∧ σ'.arrs "tgt" = List.replicate (edges F).length 0)
    (fun _ h => h.1) (fun _ _ hP hQ => ⟨hQ.1, (hQ.2.2.1 "tgt" tgt_not_warrs_prefPass).trans hP.2⟩)
    le_rfl
  have h1 := ((degPass_spec hw hB).frame).conseq (P' := Pre F)
    (Q' := fun _ σ' => (Static F σ' ∧ Deg F (edges F) σ' ∧
        σ'.arrs "off" = List.replicate (N F + 1) 0 ∧ σ'.arrs "pos" = List.replicate (N F + 1) 0) ∧
      σ'.arrs "tgt" = List.replicate (edges F).length 0)
    (fun _ h => ⟨h.1, h.2.2.2.1⟩)
    (fun _ _ hP hQ => ⟨⟨hQ.1.1, hQ.1.2, (hQ.2.2.1 "off" off_not_warrs_degPass).trans hP.2.2.2.2.1,
      (hQ.2.2.1 "pos" pos_not_warrs_degPass).trans hP.2.2.2.2.2.1⟩,
      (hQ.2.2.1 "tgt" tgt_not_warrs_degPass).trans hP.2.2.2.2.2.2⟩) le_rfl
  refine (Spec.seq h1 (Spec.seq h2 (fillPass_spec hw hB)
    (R := fun _ σ'' => Static F σ'' ∧ σ''.vars "E" = (edges F).length ∧
      σ''.arrs "off" = arrOf (N F + 1) (S F) ∧ Rows F (edges F) σ'')
    ?_ (fun _ _ _ _ _ h => h)) (fun _ _ _ h => h) ?_).mono ?_
  · rintro σ σ' - ⟨⟨hS, hoff, hpos, hE⟩, htgt⟩
    exact ⟨hS, hE, hoff, hpos, htgt⟩
  · rintro σ σ' σ'' - - ⟨hS, hE, hoff, p, t, hpos, htgt, hRS⟩
    refine ⟨S F, t, ⟨hoff, htgt, fun i _ => S_le_succ F i, S_N F hw,
      fun j hj => hRS.target_lt F hw hj⟩, hRS.done F hw, hE, hS.2.2.1, hS.1, hS.2.1⟩
  · omega

end Lax117284Proofs.TwoSAT.Machine.Build

end

/-! ### `Lax117284Proofs.TwoSAT.Machine.Bfs` -/

section
/-!
Breadth-first search over a directed graph in compressed-row form, as an IMP+ command with a
proved specification: the marks array ends up as the indicator of the nodes reachable from the
source, at a cost linear in the number of nodes and slots.

The program is the search loop of `Lax271696Proofs.CC` (the connected-components driver) over a
directed structure, marking reachability instead of labelling: the marks are cleared first, the
source is marked and enqueued, and the queue is drained, each dequeued node having its whole row
scanned and every unmarked target marked and enqueued.

The invariant of the drain (`Base`) is the one of that driver with the labels replaced by marks:
the queue holds exactly the marked nodes, without repetition, all reachable from the source; the
source is marked; and every node before `head` has had its whole row looked at, so its successors
are marked. At exit `head = tail`, so the marked set is closed under the successor relation,
contains the source, and consists of reachable nodes — hence it is the reachable set.

The cost is paid out of the potential `26 · (E − scanned) + 23 · (N − head)`, where `scanned`
is the total length of the rows of the nodes already dequeued — read off the queue itself, so no
counting scalar is needed. A turn of the drain dequeues a node of row length `r`, costs at most
`26 r + 19`, and drops the potential by exactly `26 r + 23`.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Bfs

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib

/-! ### Reachability, on the offset and target functions alone -/

/-- `b` is a successor of `a`: some slot of row `a` names it. -/
def Succ (off tgt : ℕ → ℕ) (a b : ℕ) : Prop := ∃ j, off a ≤ j ∧ j < off (a + 1) ∧ tgt j = b

/-- The nodes reachable from `s`. -/
def Reach (off tgt : ℕ → ℕ) (s : ℕ) : ℕ → Prop := Relation.ReflTransGen (Succ off tgt) s

/-- The pure content of the `Csr` relation: what the offsets and the targets satisfy,
independently of any state. -/
structure CsrOk (N E : ℕ) (off tgt : ℕ → ℕ) : Prop where
  mono : ∀ i, i < N → off i ≤ off (i + 1)
  last : off N = E
  tgt_lt : ∀ p, p < E → tgt p < N

variable {B N E s : ℕ} {off tgt Vf Q : ℕ → ℕ} {head tail : ℕ}

theorem CsrOk.of_csr {σ : Env} (h : Csr "off" "tgt" N E N off tgt σ) : CsrOk N E off tgt :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem CsrOk.csr (h : CsrOk N E off tgt) {σ : Env} (ho : σ.arrs "off" = arrOf (N + 1) off)
    (ht : σ.arrs "tgt" = arrOf E tgt) : Csr "off" "tgt" N E N off tgt σ :=
  ⟨ho, ht, h.mono, h.last, h.tgt_lt⟩

theorem CsrOk.off_mono (h : CsrOk N E off tgt) {i k : ℕ} (hik : i ≤ k) (hk : k ≤ N) :
    off i ≤ off k := by
  induction k with
  | zero =>
      have : i = 0 := by omega
      subst this; exact le_rfl
  | succ k ih =>
      by_cases hik' : i ≤ k
      · exact le_trans (ih hik' (by omega)) (h.mono k (by omega))
      · have : i = k + 1 := by omega
        subst this; exact le_rfl

/-- A row of a node ends inside the target array. -/
theorem CsrOk.row_le (h : CsrOk N E off tgt) {v : ℕ} (hv : v < N) : off (v + 1) ≤ E :=
  h.last ▸ h.off_mono (by omega) le_rfl

/-- The rows tile the target array. -/
theorem CsrOk.sum_rowLen (h : CsrOk N E off tgt) :
    ∑ i ∈ Finset.range N, Csr.rowLen off i ≤ E := by
  have key : ∀ k, k ≤ N → ∑ i ∈ Finset.range k, Csr.rowLen off i = off k - off 0 := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih (by omega)]
        have h₁ : off 0 ≤ off k := h.off_mono (by omega) (by omega)
        have h₂ : off k ≤ off (k + 1) := h.mono k (by omega)
        simp only [Csr.rowLen]; omega
  rw [key N le_rfl, h.last]; omega

/-- The rows of distinct nodes together fit in the target array. -/
theorem CsrOk.sum_le (h : CsrOk N E off tgt) {Q : ℕ → ℕ} {k : ℕ} (hQ : ∀ i, i < k → Q i < N)
    (hinj : ∀ i, i < k → ∀ j, j < k → Q i = Q j → i = j) :
    ∑ i ∈ Finset.range k, Csr.rowLen off (Q i) ≤ E := by
  have himg : ∑ v ∈ (Finset.range k).image Q, Csr.rowLen off v
      = ∑ i ∈ Finset.range k, Csr.rowLen off (Q i) :=
    Finset.sum_image
      (fun i hi j hj hij => hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hij)
  rw [← himg]
  refine le_trans (Finset.sum_le_sum_of_subset ?_) h.sum_rowLen
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
  exact Finset.mem_range.2 (hQ i (Finset.mem_range.1 hi))

/-! ### What holds throughout the search -/

/-- The state of the marks and the queue, at any point of the search. -/
structure Base (off tgt : ℕ → ℕ) (N s : ℕ) (Vf Q : ℕ → ℕ) (head tail : ℕ) : Prop where
  /-- Every mark is a bit. -/
  bit : ∀ w, w < N → Vf w ≤ 1
  /-- The queue is a segment. -/
  hd : head ≤ tail
  /-- The queue holds nodes. -/
  tl : tail ≤ N
  /-- Everything on the queue is a marked node. -/
  qmem : ∀ i, i < tail → Q i < N ∧ Vf (Q i) = 1
  /-- Every marked node is on the queue. -/
  qall : ∀ w, w < N → Vf w = 1 → ∃ i, i < tail ∧ Q i = w
  /-- Nothing is on the queue twice. -/
  qinj : ∀ i, i < tail → ∀ j, j < tail → Q i = Q j → i = j
  /-- Everything on the queue is reachable. -/
  reach : ∀ i, i < tail → Reach off tgt s (Q i)
  /-- The source is marked. -/
  src : Vf s = 1
  /-- The row of a node before `head` has been looked at: its successors are marked. -/
  exp : ∀ i, i < head → ∀ j, off (Q i) ≤ j → j < off (Q i + 1) → Vf (tgt j) = 1

/-- An unmarked node is not on the queue, so there is room for one more. -/
theorem Base.tail_lt (hB : Base off tgt N s Vf Q head tail) {w : ℕ} (hw : w < N)
    (hV : Vf w = 0) : tail < N := by
  have hsub : (Finset.range tail).image Q ⊆ (Finset.range N).erase w := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
    have hi' := Finset.mem_range.1 hi
    refine Finset.mem_erase.2 ⟨fun h => ?_, Finset.mem_range.2 (hB.qmem i hi').1⟩
    have := (hB.qmem i hi').2
    rw [h, hV] at this
    exact absurd this (by omega)
  have hcard : ((Finset.range tail).image Q).card = tail := by
    rw [Finset.card_image_of_injOn (fun i hi j hj h =>
      hB.qinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) h)]
    exact Finset.card_range tail
  have := Finset.card_le_card hsub
  rw [hcard, Finset.card_erase_of_mem (Finset.mem_range.2 hw), Finset.card_range] at this
  omega

/-- Marking an unmarked reachable node and enqueuing it. -/
theorem Base.enqueue (hB : Base off tgt N s Vf Q head tail) {w : ℕ} (hw : w < N)
    (hnew : Vf w = 0) (hr : Reach off tgt s w) :
    Base off tgt N s (upd Vf w 1) (upd Q tail w) head (tail + 1) := by
  have htail : tail < N := hB.tail_lt hw hnew
  have hhd := hB.hd
  have hQne : ∀ p, p < tail → Q p ≠ w := fun p hp hpw => by
    have := (hB.qmem p hp).2
    rw [hpw, hnew] at this
    omega
  refine ⟨fun z hz => upd_le (le_refl 1) (hB.bit z hz), by omega, by omega, fun i hi => ?_,
    fun z hz hz1 => ?_, fun i hi j hj hij => ?_, fun i hi => ?_, ?_, fun i hi j hj₁ hj₂ => ?_⟩
  · by_cases hit : i = tail
    · rw [hit, upd_self, upd_self]; exact ⟨hw, rfl⟩
    · have hi' : i < tail := by omega
      rw [upd_of_ne _ hit, upd_of_ne _ (hQne i hi')]
      exact hB.qmem i hi'
  · by_cases hzw : z = w
    · exact ⟨tail, by omega, by rw [upd_self, hzw]⟩
    · rw [upd_of_ne _ hzw] at hz1
      obtain ⟨i, hi, rfl⟩ := hB.qall z hz hz1
      exact ⟨i, by omega, upd_of_ne _ (by omega)⟩
  · by_cases hit : i = tail <;> by_cases hjt : j = tail
    · omega
    · rw [hit, upd_self, upd_of_ne _ hjt] at hij
      exact absurd hij.symm (hQne j (by omega))
    · rw [hjt, upd_self, upd_of_ne _ hit] at hij
      exact absurd hij (hQne i (by omega))
    · rw [upd_of_ne _ hit, upd_of_ne _ hjt] at hij
      exact hB.qinj i (by omega) j (by omega) hij
  · by_cases hit : i = tail
    · rw [hit, upd_self]; exact hr
    · rw [upd_of_ne _ hit]; exact hB.reach i (by omega)
  · by_cases hsw : s = w
    · rw [hsw, upd_self]
    · rw [upd_of_ne _ hsw]; exact hB.src
  · have hit : i ≠ tail := by omega
    rw [upd_of_ne _ hit] at hj₁ hj₂
    by_cases htw : tgt j = w
    · rw [htw, upd_self]
    · rw [upd_of_ne _ htw]; exact hB.exp i hi j hj₁ hj₂

/-- Moving the head on, once the row of the node at the head has been looked at. -/
theorem Base.advance (hB : Base off tgt N s Vf Q head tail) (hht : head < tail)
    (hrow : ∀ j, off (Q head) ≤ j → j < off (Q head + 1) → Vf (tgt j) = 1) :
    Base off tgt N s Vf Q (head + 1) tail := by
  refine ⟨hB.bit, hht, hB.tl, hB.qmem, hB.qall, hB.qinj, hB.reach, hB.src,
    fun i hi j hj₁ hj₂ => ?_⟩
  rcases Nat.lt_or_ge i head with h | h
  · exact hB.exp i h j hj₁ hj₂
  · have : i = head := by omega
    subst this; exact hrow j hj₁ hj₂

/-- **The exit argument, one direction.** When the queue is empty, every reachable node is a
marked node: the marked set is closed under the successor relation. -/
theorem Base.reach_marked (hc : CsrOk N E off tgt) (hs : s < N)
    (hB : Base off tgt N s Vf Q tail tail) {w : ℕ} (h : Reach off tgt s w) :
    w < N ∧ Vf w = 1 := by
  induction h with
  | refl => exact ⟨hs, hB.src⟩
  | tail _ hstep ih =>
      obtain ⟨j, hj₁, hj₂, rfl⟩ := hstep
      obtain ⟨i, hi, rfl⟩ := hB.qall _ ih.1 ih.2
      have hjE : j < E := lt_of_lt_of_le hj₂ (hc.row_le ih.1)
      exact ⟨hc.tgt_lt j hjE, hB.exp i hi j hj₁ hj₂⟩

/-- And the other: a marked node is on the queue, hence reachable. -/
theorem Base.marked_reach (hB : Base off tgt N s Vf Q head tail) {w : ℕ} (hw : w < N)
    (h : Vf w = 1) : Reach off tgt s w := by
  obtain ⟨i, hi, rfl⟩ := hB.qall w hw h
  exact hB.reach i hi

open scoped Classical in
/-- **At exit the marks are the indicator of reachability.** -/
theorem Base.exit (hc : CsrOk N E off tgt) (hs : s < N)
    (hB : Base off tgt N s Vf Q tail tail) :
    arrOf N Vf = arrOf N (fun v => if Reach off tgt s v then 1 else 0) := by
  refine arrOf_congr fun w hw => ?_
  have hbit := hB.bit w hw
  by_cases hr : Reach off tgt s w
  · rw [if_pos hr]; exact (hB.reach_marked hc hs hr).2
  · rw [if_neg hr]
    rcases Nat.eq_zero_or_pos (Vf w) with h0 | hpos
    · exact h0
    · exact absurd (hB.marked_reach hw (by omega)) hr

/-- A list of length `n` is the array of its own entries. -/
theorem eq_arrOf_getD (l : List ℕ) (n : ℕ) (h : l.length = n) :
    l = arrOf n (fun i => l.getD i 0) := by
  subst h
  refine List.ext_getElem (by simp) fun k h₁ _ => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁]

/-- The state after the source has been marked and enqueued: the search's starting point. -/
theorem Base.init (hs : s < N) (Q₀ : ℕ → ℕ) :
    Base off tgt N s (upd (fun _ => 0) s 1) (upd Q₀ 0 s) 0 1 := by
  refine ⟨fun z hz => upd_le (le_refl 1) (Nat.zero_le 1), by omega, by omega, fun i hi => ?_,
    fun w hw h1 => ⟨0, by omega, ?_⟩, fun i hi j hj _ => by omega, fun i hi => ?_,
    upd_self _ _ _, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  · have : i = 0 := by omega
    subst this; simp [hs]
  · by_cases hws : w = s
    · rw [upd_self, hws]
    · rw [upd_of_ne _ hws] at h1; simp at h1
  · have : i = 0 := by omega
    subst this; rw [upd_self]; exact Relation.ReflTransGen.refl

/-! ### The program -/

/-- Clear the marks: `i := 0; while i < N do (vis[i] := 0; i := i + 1)`. -/
def clear : Com :=
  .seq (.assign "i" (.lit 0))
    (.while (.lt (.var "i") (.var "N"))
      (.seq (.store "vis" (.var "i") (.lit 0)) (.assign "i" (.add (.var "i") (.lit 1)))))

/-- Look at the slot `j`: if the node it names is unmarked, mark it and enqueue it. -/
def scanBody : Com :=
  .seq (.assign "v" (.get "tgt" (.var "j")))
    (.seq (.ite (.eq (.get "vis" (.var "v")) (.lit 0))
            (.seq (.store "vis" (.var "v") (.lit 1))
              (.seq (.store "q" (.var "tail") (.var "v"))
                (.assign "tail" (.add (.var "tail") (.lit 1)))))
            .skip)
      (.assign "j" (.add (.var "j") (.lit 1))))

/-- Take the next node off the queue and scan its whole row. The head moves *after* the scan,
so that "the nodes before `head` have been expanded" is an invariant of the scan as well. -/
def expandBody : Com :=
  .seq (.assign "u" (.get "q" (.var "head")))
    (.seq (.assign "j" (.get "off" (.var "u")))
      (.seq (.assign "jend" (.get "off" (.add (.var "u") (.lit 1))))
        (.seq (.while (.lt (.var "j") (.var "jend")) scanBody)
          (.assign "head" (.add (.var "head") (.lit 1))))))

/-- Empty the queue: the search itself. -/
def drain : Com := .while (.lt (.var "head") (.var "tail")) expandBody

/-- Mark and enqueue the source, then drain the queue. -/
def initDrain : Com :=
  .seq (.assign "head" (.lit 0))
    (.seq (.assign "tail" (.lit 0))
      (.seq (.store "q" (.var "tail") (.var "s"))
        (.seq (.assign "tail" (.add (.var "tail") (.lit 1)))
          (.seq (.store "vis" (.var "s") (.lit 1)) drain))))

/-- The whole search: clear the marks, mark and enqueue the source, drain the queue. -/
def bfs : Com := .seq clear initDrain

/-- The constant of the running time: `bfs` costs at most `Kbfs · (N + E + 1)`. -/
def Kbfs : ℕ := 40

@[simp] theorem Kbfs_eq : Kbfs = 40 := rfl

/-! ### The state of the machine -/

/-- The arrays and the two scalars the search does not move. -/
def SearchEnv (N E s : ℕ) (off tgt Vf Q : ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars "N" = N ∧ τ.vars "s" = s ∧
  τ.arrs "off" = arrOf (N + 1) off ∧ τ.arrs "tgt" = arrOf E tgt ∧
  τ.arrs "vis" = arrOf N Vf ∧ τ.arrs "q" = arrOf N Q

/-- The total length of the rows of the nodes already dequeued, read off the queue. -/
def scanned (off : ℕ → ℕ) (τ : Env) : ℕ :=
  ∑ i ∈ Finset.range (τ.vars "head"), Csr.rowLen off ((τ.arrs "q").getD i 0)

/-- The potential the search is paid out of: twenty-six per slot not yet looked at,
twenty-three per node not yet dequeued. -/
def Pot (N E : ℕ) (off : ℕ → ℕ) (τ : Env) : ℕ :=
  26 * (E - scanned off τ) + 23 * (N - τ.vars "head")

/-! ### Scanning one row -/

/-- The invariant of the row scan of the node `u` at position `head`: the position reached in
the row, the slots already looked at marked, and the queue below `head` untouched. -/
def ScanInv (N E s : ℕ) (off tgt : ℕ → ℕ) (u head : ℕ) (Q₀ : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ Vf Q, SearchEnv N E s off tgt Vf Q τ ∧ Base off tgt N s Vf Q head (τ.vars "tail") ∧
    τ.vars "head" = head ∧ head < τ.vars "tail" ∧ Q head = u ∧
    τ.vars "jend" = off (u + 1) ∧
    off u ≤ τ.vars "j" ∧ τ.vars "j" ≤ off (u + 1) ∧
    (∀ j', off u ≤ j' → j' < τ.vars "j" → Vf (tgt j') = 1) ∧
    (∀ i, i < head + 1 → Q i = Q₀ i)

/-- One slot of the row of `u`: if it names an unmarked node, that node is marked and enqueued.
The block is walked by `run_vcg`; what is left is what the two paths did. -/
theorem scanBody_run (hc : CsrOk N E off tgt) {u head : ℕ} (hu : u < N)
    (hB : N + E + 16 < B) {Q₀ : ℕ → ℕ} {τ : Env}
    (hI : ScanInv N E s off tgt u head Q₀ τ) (hjlt : τ.vars "j" < off (u + 1)) :
    ∃ τ' K, Run B scanBody τ τ' K ∧ K ≤ 22 ∧
      ScanInv N E s off tgt u head Q₀ τ' ∧ τ'.vars "j" = τ.vars "j" + 1 := by
  obtain ⟨Vf, Q, ⟨hn, hsv, hoff, htgt, hvis, hq⟩, hL, hhead, hht, hqu, hje, hj₁, hj₂, hscan,
    hq₀⟩ := hI
  have htl := hL.tl
  have hhd := hL.hd
  have hE : off (u + 1) ≤ E := hc.row_le hu
  have hjE : τ.vars "j" < E := by omega
  obtain ⟨w, hw⟩ : ∃ w, tgt (τ.vars "j") = w := ⟨_, rfl⟩
  have hwn : w < N := hw ▸ hc.tgt_lt _ hjE
  have hru : Reach off tgt s u := hqu ▸ hL.reach head hht
  have hrw : Reach off tgt s w := hru.tail ⟨τ.vars "j", hj₁, hjlt, hw⟩
  -- what the walk owes: the slot read, the mark read at what it names, and the bounds
  have hrj : (τ.arrs "tgt").getD (τ.vars "j") 0 = w := by
    rw [htgt, getD_arrOf tgt hjE, hw]
  have hrj' : (τ.arrs "tgt")[τ.vars "j"]?.getD 0 = w := by
    rw [← List.getD_eq_getElem?_getD]; exact hrj
  have hvw : (τ.setVar "v" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "v"
      = (τ.arrs "tgt").getD (τ.vars "j") 0 := by simp
  have hbr : ((τ.setVar "v" ((τ.arrs "tgt").getD (τ.vars "j") 0)).arrs "vis").getD
      ((τ.setVar "v" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "v") 0 = Vf w := by
    rw [arrs_setVar, hvw, hrj, hvis, getD_arrOf Vf hwn]
  have hjlen : τ.vars "j" < (τ.arrs "tgt").length := by rw [htgt, length_arrOf]; omega
  have hwB : (τ.arrs "tgt").getD (τ.vars "j") 0 < B := by rw [hrj]; omega
  have hwlen : (τ.arrs "tgt").getD (τ.vars "j") 0 < (τ.arrs "vis").length := by
    rw [hrj, hvis, length_arrOf]; exact hwn
  have hVwB : Vf w < B := by have := hL.bit w hwn; omega
  have hjB : τ.vars "j" + 1 < B := by omega
  have htB : τ.vars "tail" + 1 < B := by omega
  run_vcg
  · -- the node found is unmarked: it is marked and enqueued
    have hnew : Vf w = 0 := by omega
    have htail : τ.vars "tail" < N := hL.tail_lt hwn hnew
    refine ⟨⟨upd Vf w 1, upd Q (τ.vars "tail") w,
      ⟨by simp [hn], by simp [hsv], by simp [hoff], by simp [htgt],
        by simp [hvis, hrj', set_arrOf_eq_upd], by simp [hq, hrj', set_arrOf_eq_upd]⟩,
      by simpa using hL.enqueue hwn hnew hrw, by simp [hhead], by simp; omega,
      by rw [upd_of_ne _ (by omega : head ≠ τ.vars "tail")]; exact hqu,
      by simp [hje], by simp; omega, by simp; omega, ?_,
      fun i hi => by rw [upd_of_ne _ (by omega : i ≠ τ.vars "tail")]; exact hq₀ i hi⟩,
      by simp⟩
    intro j' hj₁' hj₂'
    simp at hj₂'
    by_cases hyw : tgt j' = w
    · rw [hyw, upd_self]
    · rw [upd_of_ne _ hyw]
      rcases Nat.lt_or_ge j' (τ.vars "j") with h | h
      · exact hscan j' hj₁' h
      · exact absurd (show j' = τ.vars "j" by omega) (by rintro rfl; exact hyw hw)
  · -- already marked: nothing is written
    have hVw : Vf w = 1 := by have := hL.bit w hwn; omega
    refine ⟨⟨Vf, Q, by simp [SearchEnv, hn, hsv, hoff, htgt, hvis, hq],
      by simpa using hL, by simp [hhead], by simp [hht], hqu, by simp [hje],
      by simp; omega, by simp; omega, ?_, hq₀⟩, by simp⟩
    intro j' hj₁' hj₂'
    simp at hj₂'
    rcases Nat.lt_or_ge j' (τ.vars "j") with h | h
    · exact hscan j' hj₁' h
    · rw [show j' = τ.vars "j" by omega, hw]; exact hVw
  -- what the walk deferred: the queue has room, because the node just found is unmarked
  all_goals
    (have hnew : Vf w = 0 := by omega
     have := hL.tail_lt hwn hnew
     simp [hq]
     omega)

/-- **The whole row of `u`, scanned.** The loop is the kit's row scan: twenty-six per slot. -/
theorem scan_spec (hc : CsrOk N E off tgt) {u head : ℕ} (hu : u < N)
    (hB : N + E + 16 < B) {Q₀ : ℕ → ℕ} :
    Spec B (fun τ => ScanInv N E s off tgt u head Q₀ τ ∧ τ.vars "j" = off u)
      (.while (.lt (.var "j") (.var "jend")) scanBody)
      (fun _ τ' => ScanInv N E s off tgt u head Q₀ τ' ∧ τ'.vars "j" = off (u + 1))
      (26 * Csr.rowLen off u + 4) := by
  have hE : off (u + 1) ≤ E := hc.row_le hu
  refine Csr.rowScan_spec B (26 * Csr.rowLen off u + 4) (off (u + 1)) 22 "j" "jend" scanBody
    (ScanInv N E s off tgt u head Q₀) (by omega)
    (fun σ hσ => by
      obtain ⟨-, -, -, -, -, -, -, hje, -, hjle, -, -⟩ := hσ
      exact ⟨hje, hjle⟩)
    (fun σ hσ hlt => by
      obtain ⟨σ', K', hr, hK, hI', hj'⟩ := scanBody_run hc hu hB hσ hlt
      exact ⟨σ', K', hr, hI', hj', hK⟩) (fun _ hσ => hσ.1)
    (fun σ hσ => by rw [hσ.2]; simp only [Csr.rowLen]; omega)

/-! ### Emptying the queue -/

/-- The invariant of the drain loop. -/
def DrainInv (N E s : ℕ) (off tgt : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ Vf Q, SearchEnv N E s off tgt Vf Q τ ∧
    Base off tgt N s Vf Q (τ.vars "head") (τ.vars "tail")

/-- Taking one node off the queue and scanning its row: the cost is twenty-six per slot of the
row and nineteen besides, and the scanned total grows by the row's length. -/
theorem expandBody_run (hc : CsrOk N E off tgt) (hB : N + E + 16 < B) {τ : Env}
    (hSE : SearchEnv N E s off tgt Vf Q τ)
    (hL : Base off tgt N s Vf Q (τ.vars "head") (τ.vars "tail"))
    (hht : τ.vars "head" < τ.vars "tail") :
    ∃ (τ' : Env) (K : ℕ), Run B expandBody τ τ' K ∧
      K ≤ 26 * Csr.rowLen off (Q (τ.vars "head")) + 19 ∧ DrainInv N E s off tgt τ' ∧
      τ'.vars "head" = τ.vars "head" + 1 ∧
      scanned off τ' = scanned off τ + Csr.rowLen off (Q (τ.vars "head")) := by
  obtain ⟨hn, hsv, hoff, htgt, hvis, hq⟩ := id hSE
  have htln := hL.tl
  have hheadn : τ.vars "head" < N := by omega
  obtain ⟨u, hudef⟩ : ∃ u, Q (τ.vars "head") = u := ⟨_, rfl⟩
  rw [hudef]
  have hun : u < N := hudef ▸ (hL.qmem _ hht).1
  have hcsr : Csr "off" "tgt" N E N off tgt τ := hc.csr hoff htgt
  -- what the read at the head of the queue owes
  have hru : (τ.arrs "q").getD (τ.vars "head") 0 = u := by
    rw [hq, getD_arrOf Q hheadn, hudef]
  have hru' : (τ.arrs "q")[τ.vars "head"]?.getD 0 = u := by
    rw [← List.getD_eq_getElem?_getD]; exact hru
  have hqlen : τ.vars "head" < (τ.arrs "q").length := by rw [hq, length_arrOf]; omega
  have huB : (τ.arrs "q").getD (τ.vars "head") 0 < B := by rw [hru]; omega
  -- the scan, saying what the turn owes: the invariant one node on
  have hscan : Spec B
      (fun σ => ScanInv N E s off tgt u (τ.vars "head") Q σ ∧ σ.vars "j" = off u)
      (.while (.lt (.var "j") (.var "jend")) scanBody)
      (fun _ σ' => DrainInv N E s off tgt (σ'.setVar "head" (τ.vars "head" + 1)) ∧
        σ'.vars "head" = τ.vars "head" ∧
        scanned off (σ'.setVar "head" (τ.vars "head" + 1))
          = scanned off τ + Csr.rowLen off u ∧
        σ'.vars "head" + 1 < B) (26 * Csr.rowLen off u + 4) :=
    (scan_spec hc hun hB (Q₀ := Q)).post fun _ σ' _ hQ => by
      obtain ⟨⟨Vf', Q', hSE', hL', hhead', hht', hqu', hje', hjge', hjle', hscanned, hq₀'⟩,
        hj₄⟩ := hQ
      obtain ⟨hn', hsv', hoff', htgt', hvis', hq'⟩ := id hSE'
      have htl' := hL'.tl
      refine ⟨⟨Vf', Q', by simpa [SearchEnv] using hSE', ?_⟩, hhead', ?_, by omega⟩
      · -- the search is one node further along
        have hrow : ∀ j, off (Q' (τ.vars "head")) ≤ j → j < off (Q' (τ.vars "head") + 1) →
            Vf' (tgt j) = 1 := by
          rw [hqu']
          intro j hj₁ hj₂
          exact hscanned j hj₁ (by rw [hj₄]; exact hj₂)
        simpa using hL'.advance hht' hrow
      · -- the scanned total is the sum over the dequeued nodes
        simp only [scanned, vars_setVar, arrs_setVar, if_true]
        rw [Finset.sum_range_succ]
        congr 1
        · refine Finset.sum_congr rfl fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          rw [hq', getD_arrOf Q' (by omega), hq₀' i (by omega), hq, getD_arrOf Q (by omega)]
        · rw [hq', getD_arrOf Q' (by omega), hq₀' _ (by omega), hudef]
  run_vcg [Csr.loadRow_spec B N E N "off" "tgt" "u" "j" "jend" off tgt (by decide) (by decide),
    hscan]
  · -- what the block did is what the scan handed back
    simp_all
  · -- the two offset reads: a row of the structure, and its number a word
    exact ⟨⟨by simpa using hcsr, by omega, by omega⟩, by simp [hru']; omega,
      by simp [hru']; omega⟩
  · -- the scan starts at the top of the row, in the state the reads left
    obtain ⟨-, -, -, rfl⟩ := ‹Csr.LoadRowPost "off" "tgt" "u" "j" "jend" N E N off tgt _ _›
    exact ⟨⟨Vf, Q, by simpa [SearchEnv] using hSE, by simpa using hL, by simp,
      by simpa using hht, hudef, by simp [hru'], by simp [hru'],
      (by simpa [hru'] using hc.mono u hun),
      by intro j' h₁ h₂; simp [hru'] at h₂; omega, fun i _ => rfl⟩,
      by simp [hru']⟩

open scoped Classical in
/-- **The search.** The queue is emptied, and the whole cost is paid out of the potential. The
loop is the kit's `Queue.drain_spec`; what is left here is that a turn pays for itself, and the
exit argument. -/
theorem drain_spec (hc : CsrOk N E off tgt) (hs : s < N) (hB : N + E + 16 < B) :
    Spec B (fun τ => DrainInv N E s off tgt τ ∧ τ.vars "head" = 0) drain
      (fun _ τ' => τ'.arrs "vis" = arrOf N (fun v => if Reach off tgt s v then 1 else 0) ∧
        Csr "off" "tgt" N E N off tgt τ' ∧ τ'.vars "N" = N ∧ τ'.vars "s" = s ∧
        (τ'.arrs "q").length = N)
      (26 * E + 23 * N + 4) := by
  refine (Queue.drain_spec B N N (26 * E + 23 * N + 4) "q" "head" "tail" expandBody
    (DrainInv N E s off tgt) (Pot N E off) (fun σ hσ => ?_) (by omega) (fun σ hσ hlt => ?_)
    (fun σ hσ => hσ.1) (fun σ hσ => ?_)).post (fun _ σ' _ hQ => ?_)
  · -- the invariant carries a queue: the marked nodes, in arrival order
    obtain ⟨Vf, Q, ⟨-, -, -, -, -, hq⟩, hL⟩ := hσ
    exact ⟨Q, σ.vars "head", σ.vars "tail", hq, rfl, rfl, hL.hd, hL.tl,
      fun i hi => (hL.qmem i hi).1⟩
  · -- a turn pays for itself out of the potential
    obtain ⟨Vf, Q, hSE, hL⟩ := hσ
    obtain ⟨σ', K, hrun, hK, hI', hhead', hsc'⟩ := expandBody_run hc hB hSE hL hlt
    refine ⟨σ', K, hrun, hI', ?_⟩
    obtain ⟨Vf', Q', hSE', hL'⟩ := hI'
    have hhd := hL'.hd
    have htl := hL'.tl
    have hE : scanned off σ' ≤ E := by
      have hq' := hSE'.2.2.2.2.2
      have : scanned off σ' = ∑ i ∈ Finset.range (σ'.vars "head"), Csr.rowLen off (Q' i) := by
        simp only [scanned]
        refine Finset.sum_congr rfl fun i hi => ?_
        have := Finset.mem_range.1 hi
        rw [hq', getD_arrOf Q' (by omega)]
      rw [this]
      exact hc.sum_le (fun i hi => (hL'.qmem i (by omega)).1)
        (fun i hi j hj h => hL'.qinj i (by omega) j (by omega) h)
    have hhd0 := hL.hd
    have htl0 := hL.tl
    simp only [Pot]
    omega
  · -- the potential at entry
    obtain ⟨-, h0⟩ := hσ
    simp only [Pot, scanned, h0, Finset.range_zero, Finset.sum_empty]
    omega
  · -- the exit: every node on the queue has been expanded
    obtain ⟨⟨Vf, Q, ⟨hn, hsv, hoff, htgt, hvis, hq⟩, hL⟩, hht⟩ := hQ
    rw [hht] at hL
    exact ⟨by rw [hvis]; exact hL.exit hc hs, hc.csr hoff htgt, hn, hsv,
      by rw [hq, length_arrOf]⟩

/-! ### The whole search -/

open scoped Classical in
/-- From cleared marks: the source is marked and enqueued, and the queue drained. -/
theorem initDrain_spec (hs : s < N) (hB : N + E + 16 < B) :
    Spec B
      (fun τ => Csr "off" "tgt" N E N off tgt τ ∧ τ.vars "N" = N ∧ τ.vars "s" = s ∧
        τ.arrs "vis" = arrOf N (fun _ => 0) ∧ (τ.arrs "q").length = N)
      initDrain
      (fun _ τ' => τ'.arrs "vis" = arrOf N (fun v => if Reach off tgt s v then 1 else 0) ∧
        Csr "off" "tgt" N E N off tgt τ' ∧
        τ'.vars "N" = N ∧ τ'.vars "s" = s ∧ (τ'.arrs "q").length = N)
      (26 * E + 23 * N + 18) := by
  intro τ hτ
  obtain ⟨hcsr, hn, hsv, hvis, hql⟩ := hτ
  obtain ⟨hoff, htgt, -, -, -⟩ := id hcsr
  have hc := CsrOk.of_csr hcsr
  have hdrain := drain_spec (B := B) hc hs hB
  obtain ⟨Q₀, hq⟩ : ∃ Q₀, τ.arrs "q" = arrOf N Q₀ := ⟨_, eq_arrOf_getD _ N hql⟩
  have hvl : (τ.arrs "vis").length = N := by rw [hvis, length_arrOf]
  run_vcg [hdrain]
  · exact ‹_›
  · -- the search starts with the source marked and on the queue
    refine ⟨⟨upd (fun _ => 0) s 1, upd Q₀ 0 s,
      ⟨by simp [hn], by simp [hsv], by simp [hoff], by simp [htgt],
        by simp [hvis, hsv, set_arrOf_eq_upd], by simp [hq, hsv, set_arrOf_eq_upd]⟩, ?_⟩,
      by simp⟩
    simpa using Base.init (off := off) (tgt := tgt) hs Q₀

open scoped Classical in
/-- **Breadth-first search.** From a CSR structure of `N` nodes and `E` slots and a source
`s < N`, with a marks array and a queue of length `N`, `bfs` leaves the marks array as the
indicator of the nodes reachable from `s`, at a cost of at most `Kbfs · (N + E + 1)`. -/
theorem bfs_spec {B : ℕ} (N E s : ℕ) (off tgt : ℕ → ℕ) (hs : s < N) (hB : N + E + 16 < B) :
    Spec B
      (fun σ => Csr "off" "tgt" N E N off tgt σ ∧
        σ.vars "N" = N ∧ σ.vars "s" = s ∧ (σ.arrs "vis").length = N ∧ (σ.arrs "q").length = N)
      bfs
      (fun _ σ' => σ'.arrs "vis" = arrOf N (fun v => if Reach off tgt s v then 1 else 0) ∧
        Csr "off" "tgt" N E N off tgt σ' ∧
        σ'.vars "N" = N ∧ σ'.vars "s" = s ∧ (σ'.arrs "q").length = N)
      (Kbfs * (N + E + 1)) := by
  have hclear : Spec B (fun σ => (∃ g, σ.arrs "vis" = arrOf N g) ∧ σ.vars "N" = N) clear
      (fun _ σ' => (∃ g, σ'.arrs "vis" = arrOf N g ∧ ∀ j, j < N → g j = 0) ∧ σ'.vars "i" = N)
      (11 * N + 6) :=
    Fill.loop_spec B N "vis" "i" "N" (.lit 0) (fun _ => 0) (by decide) (by omega)
      (fun _ _ _ _ => evalB_lit (by omega))
  refine ((hclear.frame.pre (P' := fun σ => Csr "off" "tgt" N E N off tgt σ ∧
      σ.vars "N" = N ∧ σ.vars "s" = s ∧ (σ.arrs "vis").length = N ∧ (σ.arrs "q").length = N)
      (fun σ hσ => ⟨⟨_, eq_arrOf_getD _ N hσ.2.2.2.1⟩, hσ.2.1⟩)).seq
    (initDrain_spec (off := off) (tgt := tgt) hs hB) ?_ ?_).mono ?_
  · -- the clearing lands in the search's precondition
    rintro σ σ' ⟨hcsr, hn, hsv, hvl, hql⟩ ⟨⟨⟨g, hg, hg0⟩, -⟩, hvars, harrs, -, -⟩
    have hoff : σ'.arrs "off" = σ.arrs "off" := harrs "off" (by decide)
    have htgt : σ'.arrs "tgt" = σ.arrs "tgt" := harrs "tgt" (by decide)
    refine ⟨hcsr.of_eq hoff htgt, by rw [hvars "N" (by decide), hn],
      by rw [hvars "s" (by decide), hsv], ?_, by rw [harrs "q" (by decide), hql]⟩
    rw [hg]
    exact arrOf_congr fun i hi => hg0 i hi
  · exact fun _ _ _ _ _ hq => hq
  · rw [Kbfs_eq]; omega

end Lax117284Proofs.TwoSAT.Machine.Bfs

end

/-! ### `Lax117284Proofs.TwoSAT.Machine.Scan` -/

section
/-!
The first phase of the program: the word is in the array `a` with its length in `L`, and the
scan of `lax-391470` reads the formula off its bits into the arrays `vr`, `sg`, `cl`, leaving
the phase of the scan in `ph` (`4` for an accepted encoding), the numbers of literals and
clauses in `k` and `C`, and one more than the largest index in `mx`.

Everything here is the verified scanner of `lax-391470`, applied; what is added is the reading
of its invariant into the facts the later phases consume.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Scan

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax429075.CNF Lax391470Proofs.CnfScan Lax391470Proofs.L2ScanModel Lax391470Proofs.L2Scan
open Lax391470Proofs.Bits Lax117284Proofs.TwoSAT.Machine.Model

/-- The state of the scan on the bits of a word. -/
def st (y : List ℕ) : St := run init (bitsOf y)

/-- The formula a word scans to: the clauses completed. -/
def formulaOf (y : List ℕ) : Formula := (st y).done

/-- The word is accepted by the scan. -/
def Accepted (y : List ℕ) : Prop := (st y).ph = 4

/-- The scan, after the word has been read: the index bound starts at `1`. -/
def scanPart : Com := .seq (.assign "mx" (.lit 1)) scanLoop

/-- What the reader leaves and the scan needs. -/
structure ReadPost (y : List ℕ) (ext : String → ℕ) (σ : Env) : Prop where
  L : σ.vars "L" = y.length
  a : σ.arrs "a" = y
  out : σ.out = []
  zero : ∀ x, x ∉ ["L", "rt", "rv", "len"] → σ.vars x = 0
  arr : ∀ b, b ≠ "a" → σ.arrs b = List.replicate (ext b) 0

/-- What the scan leaves, in terms of the state of the abstract scan. -/
structure ScanPost (y : List ℕ) (ext : String → ℕ) (σ : Env) : Prop where
  ph : σ.vars "ph" = (st y).ph
  C : σ.vars "C" = (st y).done.length
  k : σ.vars "k" = (flat (st y)).length
  mx : σ.vars "mx" = mxOf (flat (st y))
  vr : (σ.arrs "vr").take (flat (st y)).length = (flat (st y)).map Literal.index
  sg : (σ.arrs "sg").take (flat (st y)).length =
    (flat (st y)).map fun l => if l.positive then 1 else 0
  cl : (σ.arrs "cl").take (flat (st y)).length = nums (st y)
  lvr : (σ.arrs "vr").length = y.length
  lsg : (σ.arrs "sg").length = y.length
  lcl : (σ.arrs "cl").length = y.length
  out : σ.out = []
  arr : ∀ b, b ∉ ["a", "vr", "sg", "cl"] → σ.arrs b = List.replicate (ext b) 0

lemma warrs_scan : scanLoop.warrs = ["vr", "sg", "sg", "cl"] := by
  simp [scanLoop, scanBody, dispatch, phase3, Com.warrs]

variable {B : ℕ} {y : List ℕ} {ext : String → ℕ}

/-- **The scan.** -/
theorem scanPart_spec (hB : y.length + 8 < B) (hyB : ∀ v ∈ y, v < B)
    (hext : ext "vr" = y.length ∧ ext "sg" = y.length ∧ ext "cl" = y.length) :
    Spec B (ReadPost y ext) scanPart (fun _ σ' => ScanPost y ext σ') (2 + (64 * y.length + 6)) := by
  intro σ1 h1
  have r2 : Run B (.assign "mx" (.lit 1)) σ1 (σ1.setVar "mx" 1) (1 + (Expr.lit 1).size) :=
    Run.assign (evalB_lit (by omega))
  obtain ⟨σ3, r3, ⟨I3, p3⟩, -, fa3, -, -⟩ := (scanLoop_spec (B := B) (y := y) hB hyB).frame
    (σ1.setVar "mx" 1) (by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [Env.setVar]
    all_goals try simp [stAt, bitsOf, init, flat, lits, nums, cn, mxOf]
    · exact h1.zero "ph" (by decide)
    · exact h1.zero "n" (by decide)
    · exact h1.zero "C" (by decide)
    · exact h1.zero "k" (by decide)
    · exact h1.a
    · exact h1.L
    · rw [h1.arr "vr" (by decide)]; simp [hext.1]
    · rw [h1.arr "sg" (by decide)]; simp [hext.2.1]
    · rw [h1.arr "cl" (by decide)]; simp [hext.2.2]
    · exact h1.out)
  obtain ⟨hR, -, -, -, lvr, lsg, lcl, out3⟩ := I3
  have hst : stAt y (σ3.vars "p") = st y := by
    rw [p3]; unfold stAt st; rw [List.take_length]
  rw [hst] at hR
  refine ⟨σ3, (r2.seq r3).mono (by simp), ?_⟩
  refine ⟨hR.ph, hR.C, hR.k, hR.mx, hR.vr, hR.sg, hR.cl, lvr, lsg, lcl, out3, ?_⟩
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
    rw [fa3 b (by rw [warrs_scan]; simp; tauto)]
    simp only [Env.setVar]
    exact h1.arr b hb.1

/-! ### Reading the result of an accepted scan -/

lemma getD_of_take (l : List ℕ) (K i : ℕ) (hi : i < K) : l.getD i 0 = (l.take K).getD i 0 := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma getD_map {α : Type} (l : List α) (f : α → ℕ) (d : α) (i : ℕ) (hi : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]

theorem cur_nil (h : Accepted y) : (st y).cur = [] :=
  (run_inv (bitsOf y) (by unfold Accepted st at *; omega)).1 (Or.inr h)

theorem flat_eq (h : Accepted y) : flat (st y) = lits (formulaOf y) := by
  simp [flat, cur_nil h, formulaOf]

theorem nums_eq (h : Accepted y) : nums (st y) = cn (formulaOf y) := by
  simp [nums, cur_nil h, formulaOf]

/-- The sizes the scan produces are bounded by the length of the word. -/
theorem sizes_le (h : Accepted y) :
    (lits (formulaOf y)).length ≤ y.length ∧ (formulaOf y).length ≤ y.length ∧
      mxOf (lits (formulaOf y)) ≤ y.length + 1 := by
  have hs : Lax391470Proofs.L2ScanModel.size (st y) ≤ (bitsOf y).length := size_run (bitsOf y)
  have hl : (bitsOf y).length = y.length := by simp [bitsOf]
  simp only [Lax391470Proofs.L2ScanModel.size, hl, flat_eq h] at hs
  unfold formulaOf at hs ⊢
  omega

/-- **The facts an accepted scan leaves**, in terms of the formula. -/
structure Facts (F : Formula) (y : List ℕ) (ext : String → ℕ) (σ : Env) : Prop where
  C : σ.vars "C" = F.length
  k : σ.vars "k" = (lits F).length
  mx : σ.vars "mx" = mxOf (lits F)
  vr : ∀ i < (lits F).length, (σ.arrs "vr").getD i 0 = iv F i
  sg : ∀ i < (lits F).length, (σ.arrs "sg").getD i 0 = sv F i
  cl : ∀ i < (lits F).length, (σ.arrs "cl").getD i 0 = cv F i
  lvr : (σ.arrs "vr").length = y.length
  lsg : (σ.arrs "sg").length = y.length
  lcl : (σ.arrs "cl").length = y.length
  out : σ.out = []
  arr : ∀ b, b ∉ ["a", "vr", "sg", "cl"] → σ.arrs b = List.replicate (ext b) 0
  hk : (lits F).length ≤ y.length
  hC : F.length ≤ y.length
  hmx : mxOf (lits F) ≤ y.length + 1

theorem ScanPost.facts {σ : Env} (hσ : ScanPost y ext σ) (h : Accepted y) :
    Facts (formulaOf y) y ext σ := by
  have e1 := hσ.vr; have e2 := hσ.sg; have e3 := hσ.cl
  rw [flat_eq h] at e1 e2 e3
  rw [nums_eq h] at e3
  have hk := hσ.k; rw [flat_eq h] at hk
  have hmx := hσ.mx; rw [flat_eq h] at hmx
  obtain ⟨s1, s2, s3⟩ := sizes_le h
  refine ⟨hσ.C, hk, hmx, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, hσ.lvr, hσ.lsg,
    hσ.lcl, hσ.out, hσ.arr, s1, s2, s3⟩
  · rw [getD_of_take _ _ _ hi, e1, getD_map _ _ dflt _ hi]; rfl
  · rw [getD_of_take _ _ _ hi, e2, getD_map _ _ dflt _ hi]; rfl
  · rw [getD_of_take _ _ _ hi, e3]; rfl

end Lax117284Proofs.TwoSAT.Machine.Scan

end

/-! ### `Lax117284Proofs.TwoSAT.Machine.Width` -/

section
/-!
The width check: one pass over the literals counts, for every clause, how many literals it has
(`cnt`) and marks every variable that occurs (`occ`); one pass over the clauses then sets `ok`
to `0` if some clause has no literal or more than two.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Width

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax429075.CNF Lax391470Proofs.L2ScanModel Lax117284.TwoSatCNF
open Lax117284Proofs.TwoSAT.Machine.Model Lax117284Proofs.TwoSAT.Machine.Scan
open scoped Classical

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.add (V s) (.lit 1))

/-- One literal: count it for its clause and mark its variable. -/
def countBody : Com :=
  .seq (.assign "cc" (.get "cl" (V "i")))
    (.seq (.store "cnt" (V "cc") (.add (.get "cnt" (V "cc")) (.lit 1)))
      (.seq (.assign "x" (.get "vr" (V "i")))
        (.seq (.store "occ" (V "x") (.lit 1)) (bump "i"))))

def countLoop : Com := .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "k")) countBody)

/-- One clause: a count of `0` or more than `2` clears `ok`. -/
def checkBody : Com :=
  .seq (.assign "t" (.get "cnt" (V "cc")))
    (.seq (.ite (.eq (V "t") (.lit 0)) (.assign "ok" (.lit 0))
      (.ite (.lt (.lit 2) (V "t")) (.assign "ok" (.lit 0)) .skip))
      (bump "cc"))

def checkLoop : Com :=
  .seq (.assign "ok" (.lit 1))
    (.seq (.assign "cc" (.lit 0)) (.while (.lt (V "cc") (V "C")) checkBody))

/-- The width check. -/
def width : Com := .seq countLoop checkLoop

/-! ### The mathematics of the counts -/

variable (F : Formula)

/-- The number of literals among the first `i` with clause number `c`. -/
def cntUpTo (i c : ℕ) : ℕ := ((List.range i).filter fun j => cv F j = c).length

theorem cntUpTo_succ (i c : ℕ) :
    cntUpTo F (i + 1) c = cntUpTo F i c + if cv F i = c then 1 else 0 := by
  unfold cntUpTo
  rw [List.range_succ, List.filter_append, List.length_append, List.filter_singleton]
  split <;> simp_all

theorem cntUpTo_le (i c : ℕ) : cntUpTo F i c ≤ i := by
  unfold cntUpTo
  exact (List.length_filter_le _ _).trans (by simp)

theorem cntUpTo_zero (c : ℕ) : cntUpTo F 0 c = 0 := by simp [cntUpTo]

/-- The final counts: the length of each clause. -/
def cntF (c : ℕ) : ℕ := if c < F.length then (F.getD c []).length else 0

theorem cntUpTo_length (c : ℕ) : cntUpTo F (lits F).length c = cntF F c := by
  unfold cntF
  split
  · exact count_cv F c ‹_›
  · unfold cntUpTo
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro j hj
    rw [List.mem_range] at hj
    have := cv_lt F j hj
    simp; omega

/-- The variables among the first `i` literals. -/
def occUpTo (i x : ℕ) : ℕ := if ∃ j < i, iv F j = x then 1 else 0

theorem occUpTo_zero (x : ℕ) : occUpTo F 0 x = 0 := by
  unfold occUpTo; rw [if_neg]; rintro ⟨j, hj, -⟩; omega

theorem mem_vars_iff (x : ℕ) : x ∈ vars F ↔ ∃ j < (lits F).length, iv F j = x := by
  unfold vars literals
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hl
    exact ⟨j, hj, by unfold iv lits; rw [List.getD_eq_getElem _ _ hj]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, getD_mem_lits F j hj, rfl⟩

/-- The final marks: the indicator of the variables. -/
def occF (x : ℕ) : ℕ := if x ∈ vars F then 1 else 0

theorem occUpTo_length (x : ℕ) : occUpTo F (lits F).length x = occF F x := by
  unfold occUpTo occF
  by_cases h : x ∈ vars F
  · rw [if_pos h, if_pos ((mem_vars_iff F x).1 h)]
  · rw [if_neg h, if_neg (fun h' => h ((mem_vars_iff F x).2 h'))]

theorem widthOk_iff_cnt : WidthOk F ↔ ∀ c < F.length, 1 ≤ cntF F c ∧ cntF F c ≤ 2 := by
  unfold WidthOk
  rw [Lax117284Proofs.TwoSAT.Bridge.forall_mem_iff]
  refine forall_congr' fun c => imp_congr_right fun hc => ?_
  unfold cntF; rw [if_pos hc]

/-! ### The counting pass -/

variable {B : ℕ} {y : List ℕ} {ext : String → ℕ}

/-- The invariant of the counting pass. -/
structure CountInv (F : Formula) (y : List ℕ) (σ : Env) : Prop where
  k : σ.vars "k" = (lits F).length
  i : σ.vars "i" ≤ (lits F).length
  vr : ∀ j < (lits F).length, (σ.arrs "vr").getD j 0 = iv F j
  cl : ∀ j < (lits F).length, (σ.arrs "cl").getD j 0 = cv F j
  lvr : (σ.arrs "vr").length = y.length
  lcl : (σ.arrs "cl").length = y.length
  cnt : σ.arrs "cnt" = arrOf (y.length + 1) (cntUpTo F (σ.vars "i"))
  occ : σ.arrs "occ" = arrOf (y.length + 2) (occUpTo F (σ.vars "i"))
  hk : (lits F).length ≤ y.length
  hC : F.length ≤ y.length
  hmx : mxOf (lits F) ≤ y.length + 1

theorem countBody_flat :
    Spec B (fun σ => CountInv F y σ ∧ σ.vars "i" < (lits F).length ∧
        σ.vars "i" < (σ.arrs "cl").length ∧ (σ.arrs "cl").getD (σ.vars "i") 0 < B ∧
        (σ.arrs "cl").getD (σ.vars "i") 0 < (σ.arrs "cnt").length ∧
        (σ.arrs "cnt").getD ((σ.arrs "cl").getD (σ.vars "i") 0) 0 + 1 < B ∧
        σ.vars "i" < (σ.arrs "vr").length ∧ (σ.arrs "vr").getD (σ.vars "i") 0 < B ∧
        (σ.arrs "vr").getD (σ.vars "i") 0 < (σ.arrs "occ").length ∧ σ.vars "i" + 1 < B ∧
        σ.vars "i" < B ∧ 1 < B) countBody
      (fun σ σ' => CountInv F y σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  run_vcg
  all_goals try (simp only [Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte]; first | omega | assumption)
  have hI : CountInv F y σ := ‹_›
  have hi : σ.vars "i" < (lits F).length := ‹_›
  have hcl := hI.cl _ hi
  have hvr := hI.vr _ hi
  have hcv := cv_lt F _ hi
  have hiv := iv_lt F _ hi
  have hC := hI.hC
  have hmx := hI.hmx
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.hk, hI.hC, hI.hmx⟩, ?_⟩
  all_goals try simp only [Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte]
  · exact hI.k
  · omega
  · exact hI.vr
  · exact hI.cl
  · exact hI.lvr
  · exact hI.lcl
  · rw [hcl, hI.cnt, set_arrOf_eq_upd]
    apply arrOf_congr
    intro c hc
    rw [cntUpTo_succ, upd_apply, getD_arrOf _ (by omega)]
    by_cases h : c = cv F (σ.vars "i")
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), Nat.add_zero]
  · rw [hvr, hI.occ, set_arrOf_eq_upd]
    apply arrOf_congr
    intro x hx
    rw [upd_apply]
    unfold occUpTo
    by_cases hxe : x = iv F (σ.vars "i")
    · rw [if_pos hxe, if_pos ⟨σ.vars "i", by omega, hxe.symm⟩]
    · rw [if_neg hxe]
      by_cases h : ∃ j < σ.vars "i", iv F j = x
      · have h' : ∃ j < σ.vars "i" + 1, iv F j = x := by
          obtain ⟨j, hj, hjx⟩ := h; exact ⟨j, by omega, hjx⟩
        rw [if_pos h, if_pos h']
      · have h' : ¬ ∃ j < σ.vars "i" + 1, iv F j = x := by
          rintro ⟨j, hj, hjx⟩
          rcases Nat.lt_or_ge j (σ.vars "i") with h' | h'
          · exact h ⟨j, h', hjx⟩
          · exact hxe (by rw [← hjx]; congr 1; omega)
        rw [if_neg h, if_neg h']

theorem countBody_spec (hB : 2 * y.length + 8 < B) :
    Spec B (fun σ => CountInv F y σ ∧ σ.vars "i" < (lits F).length) countBody
      (fun σ σ' => CountInv F y σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  refine Spec.pre (countBody_flat F) ?_
  rintro σ ⟨hI, hi⟩
  have hcl := hI.cl _ hi
  have hvr := hI.vr _ hi
  have hcv := cv_lt F _ hi
  have hiv := iv_lt F _ hi
  have hC := hI.hC
  have hmx := hI.hmx
  have hk := hI.hk
  have hcnt : (σ.arrs "cnt").getD (cv F (σ.vars "i")) 0 ≤ σ.vars "i" := by
    rw [hI.cnt, getD_arrOf _ (by omega)]; exact cntUpTo_le F _ _
  refine ⟨hI, hi, by rw [hI.lcl]; omega, by rw [hcl]; omega,
    by rw [hcl, hI.cnt, length_arrOf]; omega, by rw [hcl]; omega, by rw [hI.lvr]; omega,
    by rw [hvr]; omega, by rw [hvr, hI.occ, length_arrOf]; omega, by omega, by omega, by omega⟩

/-- **The counting pass.** -/
theorem countLoop_spec (hB : 2 * y.length + 8 < B) (hk : (lits F).length ≤ y.length) :
    Spec B (fun σ => CountInv F y (σ.setVar "i" 0)) countLoop
      (fun _ σ' => CountInv F y σ' ∧ σ'.vars "i" = (lits F).length) (44 * (lits F).length + 6) :=
  Spec.forRangeZero "i" "k" (CountInv F y) (lits F).length 40 (by omega)
    (fun _ h => h.i) (fun _ h => h.k) (countBody_spec F hB)

/-! ### The checking pass -/

/-- The invariant of the checking pass. -/
structure CheckInv (F : Formula) (y : List ℕ) (σ : Env) : Prop where
  C : σ.vars "C" = F.length
  cc : σ.vars "cc" ≤ F.length
  cnt : σ.arrs "cnt" = arrOf (y.length + 1) (cntF F)
  ok : σ.vars "ok" = 1 ↔ ∀ c < σ.vars "cc", 1 ≤ cntF F c ∧ cntF F c ≤ 2
  ok1 : σ.vars "ok" ≤ 1
  hC : F.length ≤ y.length
  hk : (lits F).length ≤ y.length

theorem checkBody_flat :
    Spec B (fun σ => CheckInv F y σ ∧ σ.vars "cc" < F.length ∧
        σ.vars "cc" < (σ.arrs "cnt").length ∧ (σ.arrs "cnt").getD (σ.vars "cc") 0 < B ∧
        σ.vars "cc" + 1 < B ∧ σ.vars "cc" < B ∧ 2 < B ∧
        (σ.arrs "cnt").getD (σ.vars "cc") 0 = cntF F (σ.vars "cc")) checkBody
      (fun σ σ' => CheckInv F y σ' ∧ σ'.vars "cc" = σ.vars "cc" + 1) 30 := by
  run_vcg
  all_goals try (simp only [Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte]; first | omega | assumption)
  all_goals (
    have hI : CheckInv F y σ := ‹_›
    have hlt : σ.vars "cc" < F.length := ‹_›
    have ht : (σ.arrs "cnt").getD (σ.vars "cc") 0 = cntF F (σ.vars "cc") := ‹_›
    have hok := hI.ok
    have hok1 := hI.ok1
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, hI.hC, hI.hk⟩, ?_⟩
    all_goals try simp only [Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte] at *)
  · exact hI.C
  · omega
  · exact hI.cnt
  · -- the count is zero: the answer is no
    rw [ht] at *
    constructor
    · intro h; omega
    · intro h; have := (h (σ.vars "cc") (by omega)).1; omega
  · omega
  · exact hI.C
  · omega
  · exact hI.cnt
  · -- the count is more than two: the answer is no
    rw [ht] at *
    constructor
    · intro h; omega
    · intro h; have := (h (σ.vars "cc") (by omega)).2; omega
  · omega
  · exact hI.C
  · omega
  · exact hI.cnt
  · -- the count is one or two: the answer stands
    rw [ht] at *
    rw [hok]
    constructor
    · intro h c hc
      rcases Nat.lt_or_ge c (σ.vars "cc") with h' | h'
      · exact h c h'
      · have : c = σ.vars "cc" := by omega
        subst this; omega
    · intro h c hc; exact h c (by omega)
  · exact hok1

theorem checkBody_spec (hB : y.length + 8 < B) :
    Spec B (fun σ => CheckInv F y σ ∧ σ.vars "cc" < F.length) checkBody
      (fun σ σ' => CheckInv F y σ' ∧ σ'.vars "cc" = σ.vars "cc" + 1) 30 := by
  refine Spec.pre (checkBody_flat F) ?_
  rintro σ ⟨hI, hlt⟩
  have hC := hI.hC
  have ht : (σ.arrs "cnt").getD (σ.vars "cc") 0 = cntF F (σ.vars "cc") := by
    rw [hI.cnt, getD_arrOf _ (by omega)]
  have hle : cntF F (σ.vars "cc") ≤ y.length := by
    unfold cntF; rw [if_pos hlt]
    have := start_add_le F _ hlt
    have := hI.hk
    omega
  refine ⟨hI, hlt, by rw [hI.cnt, length_arrOf]; omega, by rw [ht]; omega, by omega, by omega,
    by omega, ht⟩

/-- **The checking pass.** -/
theorem checkLoop_spec (hB : y.length + 8 < B) (hC : F.length ≤ y.length) :
    Spec B (fun σ => CheckInv F y ((σ.setVar "ok" 1).setVar "cc" 0)) checkLoop
      (fun _ σ' => CheckInv F y σ' ∧ σ'.vars "cc" = F.length) (2 + (34 * F.length + 6)) := by
  refine Spec.of_exists fun σ hσ => ?_
  have r1 : Run B (.assign "ok" (.lit 1)) σ (σ.setVar "ok" 1) 2 :=
    Run.assign (evalB_lit (by omega))
  obtain ⟨σ', r2, h2⟩ := (Spec.forRangeZero "cc" "C" (CheckInv F y) F.length 30 (by omega)
    (fun _ h => h.cc) (fun _ h => h.C) (checkBody_spec F hB)).run hσ
  exact ⟨σ', _, r1.seq r2, le_rfl, h2⟩

/-! ### The whole width check -/

/-- What the width check leaves. -/
structure WidthPost (F : Formula) (y : List ℕ) (σ : Env) : Prop where
  cnt : σ.arrs "cnt" = arrOf (y.length + 1) (cntF F)
  occ : σ.arrs "occ" = arrOf (y.length + 2) (occF F)
  ok : σ.vars "ok" = 1 ↔ WidthOk F
  ok1 : σ.vars "ok" ≤ 1
  k : σ.vars "k" = (lits F).length
  C : σ.vars "C" = F.length

lemma wvars_countLoop : countLoop.wvars = ["i", "cc", "x", "i"] := by
  simp [countLoop, countBody, Com.wvars]
lemma wvars_checkLoop : checkLoop.wvars = ["ok", "cc", "t", "ok", "ok", "cc"] := by
  simp [checkLoop, checkBody, Com.wvars]
lemma warrs_checkLoop : checkLoop.warrs = [] := by
  simp [checkLoop, checkBody, Com.warrs]

/-- **The width check**: from the facts of an accepted scan, with fresh `cnt` and `occ`. -/
theorem width_spec (hB : 2 * y.length + 8 < B)
    (hext : ext "cnt" = y.length + 1 ∧ ext "occ" = y.length + 2) :
    Spec B (Facts F y ext) width (fun _ σ' => WidthPost F y σ')
      ((44 * (lits F).length + 6) + (2 + (34 * F.length + 6))) := by
  intro σ hF
  have hk := hF.hk
  have hC := hF.hC
  -- the counting pass
  obtain ⟨σ1, r1, ⟨hI1, hi1⟩, fv1, fa1, -, -⟩ :=
    (countLoop_spec F hB hk).frame.run (σ := σ) (by
      refine ⟨by simp [hF.k], by simp, ?_, ?_, by simp [hF.lvr], by simp [hF.lcl], ?_, ?_,
        hk, hC, hF.hmx⟩
      · intro j hj; simp only [Env.setVar]; exact hF.vr j hj
      · intro j hj; simp only [Env.setVar]; exact hF.cl j hj
      · simp only [Env.setVar, String.reduceEq, ↓reduceIte]
        rw [hF.arr "cnt" (by decide), hext.1, replicate_eq_arrOf]
        exact arrOf_congr fun c _ => (cntUpTo_zero F c).symm
      · simp only [Env.setVar, String.reduceEq, ↓reduceIte]
        rw [hF.arr "occ" (by decide), hext.2, replicate_eq_arrOf]
        exact arrOf_congr fun x _ => (occUpTo_zero F x).symm)
  have hC1 : σ1.vars "C" = F.length := by
    rw [fv1 "C" (by rw [wvars_countLoop]; decide)]; exact hF.C
  have hcnt1 : σ1.arrs "cnt" = arrOf (y.length + 1) (cntF F) := by
    rw [hI1.cnt, hi1]; exact arrOf_congr fun c _ => cntUpTo_length F c
  have hocc1 : σ1.arrs "occ" = arrOf (y.length + 2) (occF F) := by
    rw [hI1.occ, hi1]; exact arrOf_congr fun x _ => occUpTo_length F x
  -- the checking pass
  have hB' : y.length + 8 < B := by omega
  obtain ⟨σ2, r2, ⟨hI2, hcc2⟩, fv2, fa2, -, -⟩ :=
    (checkLoop_spec F hB' hC).frame.run (σ := σ1) (by
      refine ⟨by simp [hC1], by simp, by simp [hcnt1], ?_, by simp, hC, hk⟩
      simp only [Env.setVar, String.reduceEq, ↓reduceIte]
      first
        | trivial
        | exact ⟨fun _ c hc => absurd hc (by omega), fun _ => trivial⟩
        | exact ⟨fun _ c hc => absurd hc (by omega), fun _ => rfl⟩)
  refine ⟨σ2, r1.seq r2, ?_⟩
  refine ⟨?_, ?_, ?_, hI2.ok1, ?_, hI2.C⟩
  · exact hI2.cnt
  · rw [fa2 "occ" (by rw [warrs_checkLoop]; decide)]; exact hocc1
  · rw [hI2.ok, hcc2, widthOk_iff_cnt]
  · rw [fv2 "k" (by rw [wvars_checkLoop]; decide), fv1 "k" (by rw [wvars_countLoop]; decide)]
    exact hF.k

end Lax117284Proofs.TwoSAT.Machine.Width

end

/-! ### `Lax117284Proofs.TwoSAT.Machine.Driver` -/

section
/-!
The driver: for every variable `x` below the index bound that occurs, a search from the
positive literal `2x + 1`; if it reaches the negative literal `2x`, a search from `2x`; if
that reaches `2x + 1`, the variable is contradictory and the answer is `0`.

The cost is paid out of a potential that charges every variable a constant and every
*occurring* variable two searches, so that the loop costs `O(mx + v · (N + E))` where `v` is the
number of variables that occur — the bound the concept states.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Driver

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax429075.CNF Lax391470Proofs.L2ScanModel Lax117284.TwoSatCNF
open Lax117284Proofs.TwoSAT.Machine.Model Lax117284Proofs.TwoSAT.Machine.Width Lax117284Proofs.TwoSAT.Machine.Bfs
open scoped Classical

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.add (V s) (.lit 1))

/-- The second search, from the negative literal, and the verdict. -/
def secondCom : Com :=
  .seq (.assign "s" (.mul (.lit 2) (V "x")))
    (.seq bfs
      (.seq (.assign "r" (.get "vis" (.add (.mul (.lit 2) (V "x")) (.lit 1))))
        (.ite (.eq (V "r") (.lit 1)) (.assign "ans" (.lit 0)) .skip)))

/-- The searches of one occurring variable. -/
def searchesCom : Com :=
  .seq (.assign "s" (.add (.mul (.lit 2) (V "x")) (.lit 1)))
    (.seq bfs
      (.seq (.assign "r" (.get "vis" (.mul (.lit 2) (V "x"))))
        (.ite (.eq (V "r") (.lit 1)) secondCom .skip)))

/-- One variable: the searches if it occurs, then on to the next. -/
def varBody : Com :=
  .seq (.assign "o" (.get "occ" (V "x")))
    (.seq (.ite (.eq (V "o") (.lit 1)) searchesCom .skip) (bump "x"))

/-- The driver: every variable below the bound, then the answer. -/
def driver : Com :=
  .seq (.assign "ans" (.lit 1))
    (.seq (.assign "x" (.lit 0)) (.seq (.while (.lt (V "x") (V "mx")) varBody) (.write (V "ans"))))

/-! ### The invariant -/

variable (F : Formula) (y : List ℕ) (off tgt : ℕ → ℕ)

/-- The graph in memory is the implication graph. -/
def Graph (σ : Env) : Prop :=
  Csr "off" "tgt" (N F) (edges F).length (N F) off tgt σ ∧
    ∀ u v, Succ off tgt u v ↔ E F u v

/-- Reachability in the stored graph is reachability in the implication graph. -/
theorem reach_iff (h : ∀ u v, Succ off tgt u v ↔ E F u v) (s v : ℕ) :
    Reach off tgt s v ↔ RT F s v := by
  have : Succ off tgt = E F := by funext a b; exact propext (h a b)
  unfold Reach RT; rw [this]

/-- The invariant of the loop over the variables. -/
structure Core (σ : Env) : Prop where
  graph : Graph F off tgt σ
  hN : σ.vars "N" = N F
  mx : σ.vars "mx" = mxOf (lits F)
  x : σ.vars "x" ≤ mxOf (lits F)
  occ : σ.arrs "occ" = arrOf (y.length + 2) (occF F)
  lvis : (σ.arrs "vis").length = N F
  lq : (σ.arrs "q").length = N F
  hmx : mxOf (lits F) ≤ y.length + 1
  out : σ.out = []

/-- The invariant of the loop: the core, and the answer so far. -/
structure Inv (σ : Env) : Prop where
  core : Core F y off tgt σ
  ans1 : σ.vars "ans" ≤ 1
  ans : σ.vars "ans" = 1 ↔ ∀ x' < σ.vars "x", x' ∈ vars F → ¬ Bad F x'

/-- The cost of one search. -/
def Ks : ℕ := Kbfs * (N F + (edges F).length + 1)

/-- The potential: a constant per variable left, and two searches per occurring variable
left. -/
def Pot (σ : Env) : ℕ :=
  60 * (mxOf (lits F) - σ.vars "x") +
    (2 * Ks F + 40) * ((Finset.Ico (σ.vars "x") (mxOf (lits F))).filter (· ∈ vars F)).card

theorem pot_zero_le : ∀ σ, σ.vars "x" = 0 →
    Pot F σ ≤ 60 * mxOf (lits F) + (2 * Ks F + 40) * varCount F := by
  intro σ hx
  unfold Pot; rw [hx]
  refine Nat.add_le_add (by simp) (Nat.mul_le_mul_left _ ?_)
  unfold varCount
  apply Finset.card_le_card
  intro x hx; simp only [Finset.mem_filter] at hx; exact hx.2

theorem pot_step (σ : Env) (hlt : σ.vars "x" < mxOf (lits F)) :
    Pot F σ = 60 + (if σ.vars "x" ∈ vars F then 2 * Ks F + 40 else 0) +
      (60 * (mxOf (lits F) - (σ.vars "x" + 1)) +
        (2 * Ks F + 40) * ((Finset.Ico (σ.vars "x" + 1) (mxOf (lits F))).filter (· ∈ vars F)).card) := by
  unfold Pot
  have hsplit : Finset.Ico (σ.vars "x") (mxOf (lits F)) =
      insert (σ.vars "x") (Finset.Ico (σ.vars "x" + 1) (mxOf (lits F))) := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [hsplit, Finset.filter_insert]
  split
  · rw [Finset.card_insert_of_notMem (by simp)]
    have : mxOf (lits F) - σ.vars "x" = (mxOf (lits F) - (σ.vars "x" + 1)) + 1 := by omega
    rw [this]; ring
  · have : mxOf (lits F) - σ.vars "x" = (mxOf (lits F) - (σ.vars "x" + 1)) + 1 := by omega
    rw [this]; ring

/-! ### The searches -/

variable {B : ℕ}

lemma bfs_noWrite : bfs.NoWrite := by
  simp [bfs, clear, initDrain, drain, expandBody, scanBody, Com.NoWrite]

lemma mem_wvars_bfs {z : String} (hz : z ∈ bfs.wvars) :
    z ∈ ["i", "head", "tail", "u", "j", "jend", "v"] := by
  simp only [bfs, clear, initDrain, drain, expandBody, scanBody, Com.wvars, List.mem_append,
    List.mem_cons, List.not_mem_nil] at hz ⊢
  tauto

lemma mem_warrs_bfs {a : String} (ha : a ∈ bfs.warrs) : a ∈ ["vis", "q"] := by
  simp only [bfs, clear, initDrain, drain, expandBody, scanBody, Com.warrs, List.mem_append,
    List.mem_cons, List.not_mem_nil] at ha ⊢
  tauto

/-- The search from whatever `s` holds, relationally. -/
theorem bfsAny_spec (hB : N F + (edges F).length + 16 < B) :
    Spec B (fun σ => Graph F off tgt σ ∧ σ.vars "N" = N F ∧ σ.vars "s" < N F ∧
        (σ.arrs "vis").length = N F ∧ (σ.arrs "q").length = N F)
      bfs
      (fun σ σ' => σ'.arrs "vis" = arrOf (N F) (fun v => if RT F (σ.vars "s") v then 1 else 0) ∧
        Graph F off tgt σ' ∧ σ'.vars "N" = N F ∧ σ'.vars "s" = σ.vars "s" ∧
        (σ'.arrs "q").length = N F ∧ (σ'.arrs "vis").length = N F ∧
        (∀ z, z ∉ bfs.wvars → σ'.vars z = σ.vars z) ∧
        (∀ a, a ∉ bfs.warrs → σ'.arrs a = σ.arrs a) ∧ σ'.out = σ.out)
      (Ks F) := by
  intro σ hσ
  obtain ⟨σ', hr, ⟨hvis, hcsr, hN, hs, hq⟩, fv, fa, -, hout⟩ :=
    (bfs_spec (B := B) (N F) (edges F).length (σ.vars "s") off tgt hσ.2.2.1 hB).frame.run
      ⟨hσ.1.1, hσ.2.1, rfl, hσ.2.2.2.1, hσ.2.2.2.2⟩
  refine ⟨σ', hr, ?_, ⟨hcsr, hσ.1.2⟩, hN, hs, hq, by rw [hvis]; simp, fv, fa,
    hout bfs_noWrite⟩
  rw [hvis]
  exact arrOf_congr fun v _ => by rw [reach_iff F off tgt hσ.1.2]

/-- What the searches of one variable leave. -/
def SPost (σ σ' : Env) : Prop :=
  Core F y off tgt σ' ∧ σ'.vars "x" = σ.vars "x" ∧ σ'.vars "ans" ≤ 1 ∧
    (σ'.vars "ans" = 1 ↔ σ.vars "ans" = 1 ∧ ¬ Bad F (σ.vars "x"))

theorem core_of_bfs {σ σ' : Env} (hc : Core F y off tgt σ) (s : ℕ)
    (h : σ'.arrs "vis" = arrOf (N F) (fun v => if RT F s v then 1 else 0) ∧
      Graph F off tgt σ' ∧ σ'.vars "N" = N F ∧ σ'.vars "s" = s ∧
      (σ'.arrs "q").length = N F ∧ (σ'.arrs "vis").length = N F ∧
      (∀ z, z ∉ bfs.wvars → σ'.vars z = σ.vars z) ∧
      (∀ a, a ∉ bfs.warrs → σ'.arrs a = σ.arrs a) ∧ σ'.out = σ.out) :
    Core F y off tgt σ' ∧ σ'.vars "x" = σ.vars "x" ∧ σ'.vars "ans" = σ.vars "ans" ∧
      σ'.vars "mx" = σ.vars "mx" := by
  obtain ⟨-, hg, hN, -, hq, hvis, fv, fa, hout⟩ := h
  have hx : σ'.vars "x" = σ.vars "x" :=
    fv "x" (fun hm => by have := mem_wvars_bfs hm; simp at this)
  have hans : σ'.vars "ans" = σ.vars "ans" :=
    fv "ans" (fun hm => by have := mem_wvars_bfs hm; simp at this)
  have hmx : σ'.vars "mx" = σ.vars "mx" :=
    fv "mx" (fun hm => by have := mem_wvars_bfs hm; simp at this)
  refine ⟨⟨hg, hN, by rw [hmx]; exact hc.mx, by rw [hx]; exact hc.x, ?_, hvis, hq, hc.hmx,
    by rw [hout]; exact hc.out⟩, hx, hans, hmx⟩
  rw [fa "occ" (fun hm => by have := mem_warrs_bfs hm; simp at this)]
  exact hc.occ

theorem two_mul_lt {x : ℕ} (hx : x < mxOf (lits F)) : 2 * x + 1 < N F := by
  unfold N; omega

theorem vis_read (s v : ℕ) (hv : v < N F) {σ : Env}
    (h : σ.arrs "vis" = arrOf (N F) (fun v => if RT F s v then 1 else 0)) :
    (σ.arrs "vis").getD v 0 = if RT F s v then 1 else 0 := by
  rw [h, getD_arrOf _ hv]

variable {F y off tgt} in
theorem Core.setVar {σ : Env} (hc : Core F y off tgt σ) (z : String)
    (hz : z ≠ "N" ∧ z ≠ "mx" ∧ z ≠ "x") (v : ℕ) : Core F y off tgt (σ.setVar z v) := by
  obtain ⟨hz1, hz2, hz3⟩ := hz
  refine ⟨⟨?_, hc.graph.2⟩, ?_, ?_, ?_, ?_, ?_, ?_, hc.hmx, ?_⟩
  · simpa using hc.graph.1
  · simp [hz1.symm]; exact hc.hN
  · simp [hz2.symm]; exact hc.mx
  · simp [hz3.symm]; exact hc.x
  · simpa using hc.occ
  · simpa using hc.lvis
  · simpa using hc.lq
  · simpa using hc.out

/-! #### The atomic steps -/

theorem assign_s1_run {σ : Env} (hxB : 2 * σ.vars "x" + 1 < B) (h2B : 2 < B) :
    Run B (.assign "s" (.add (.mul (.lit 2) (V "x")) (.lit 1))) σ
      (σ.setVar "s" (2 * σ.vars "x" + 1)) 6 := by
  have e1 : (Expr.mul (.lit 2) (V "x")).evalB B σ = some (2 * σ.vars "x") := by
    have := evalB_bin (op := .mul) (evalB_lit (B := B) (σ := σ) (n := 2) (by omega))
      (evalB_var (x := "x") (by omega)) (by show 2 * σ.vars "x" < B; omega)
    simpa [Bop.apply] using this
  have e2 : (Expr.add (.mul (.lit 2) (V "x")) (.lit 1)).evalB B σ =
      some (2 * σ.vars "x" + 1) := by
    have := evalB_bin (op := .add) e1 (evalB_lit (B := B) (σ := σ) (n := 1) (by omega))
      (by show 2 * σ.vars "x" + 1 < B; omega)
    simpa [Bop.apply] using this
  exact (Run.assign e2).mono (by simp)

theorem assign_s0_run {σ : Env} (hxB : 2 * σ.vars "x" + 1 < B) (h2B : 2 < B) :
    Run B (.assign "s" (.mul (.lit 2) (V "x"))) σ (σ.setVar "s" (2 * σ.vars "x")) 4 := by
  have e1 : (Expr.mul (.lit 2) (V "x")).evalB B σ = some (2 * σ.vars "x") := by
    have := evalB_bin (op := .mul) (evalB_lit (B := B) (σ := σ) (n := 2) (by omega))
      (evalB_var (x := "x") (by omega)) (by show 2 * σ.vars "x" < B; omega)
    simpa [Bop.apply] using this
  exact (Run.assign e1).mono (by simp)

theorem read_r_run {σ : Env} {e : Expr} {idx : ℕ} (he : e.evalB B σ = some idx)
    (hidx : idx < (σ.arrs "vis").length) (hv : (σ.arrs "vis").getD idx 0 < B) :
    Run B (.assign "r" (.get "vis" e)) σ (σ.setVar "r" ((σ.arrs "vis").getD idx 0))
      (e.size + 2) := by
  refine (Run.assign (evalB_get he ?_ hv)).mono (by simp; omega)
  rw [List.getD_eq_getElem _ _ hidx, List.getElem?_eq_getElem hidx]

theorem cond_r_true {σ : Env} (hr : σ.vars "r" = 1) (h1 : 1 < B) :
    (Cond.eq (V "r") (.lit 1)).evalB B σ = some true := by
  rw [evalB_condEq (evalB_var (by omega)) (evalB_lit h1), hr]; rfl

theorem cond_r_false {σ : Env} (hr : σ.vars "r" = 0) (h1 : 1 < B) :
    (Cond.eq (V "r") (.lit 1)).evalB B σ = some false := by
  rw [evalB_condEq (evalB_var (by omega)) (evalB_lit h1), hr]; rfl

/-- **The searches of one occurring variable.** -/
theorem searches_spec (hB : N F + (edges F).length + 16 < B) :
    Spec B (fun σ => Core F y off tgt σ ∧ σ.vars "x" < mxOf (lits F) ∧ σ.vars "ans" ≤ 1)
      searchesCom (SPost F y off tgt) (2 * Ks F + 40) := by
  intro σ ⟨hc, hlt, hans⟩
  have hNB : N F < B := by omega
  have h1B : 1 < B := by omega
  have h2x : 2 * σ.vars "x" + 1 < N F := two_mul_lt F hlt
  set x := σ.vars "x" with hxdef
  -- s := 2x + 1
  have h2B : 2 < B := by omega
  have r1 := assign_s1_run (B := B) (σ := σ) (by omega) h2B
  set σ1 := σ.setVar "s" (2 * x + 1) with hσ1
  have hc1 : Core F y off tgt σ1 := hc.setVar "s" (by decide) _
  have hs1 : σ1.vars "s" = 2 * x + 1 := by rw [hσ1]; simp
  -- the first search
  obtain ⟨σ2, r2, h2⟩ := (bfsAny_spec F off tgt hB).run (σ := σ1)
    ⟨hc1.graph, hc1.hN, by rw [hs1]; exact h2x, hc1.lvis, hc1.lq⟩
  rw [hs1] at h2
  obtain ⟨hc2, hx2, hans2, -⟩ := core_of_bfs F y off tgt hc1 _ h2
  have hx2' : σ2.vars "x" = x := by rw [hx2, hσ1]; simp [← hxdef]
  have hans2' : σ2.vars "ans" = σ.vars "ans" := by rw [hans2, hσ1]; simp
  have hvis2 := h2.1
  -- r := vis[2x]
  have hv1 : (σ2.arrs "vis").getD (2 * x) 0 = if RT F (2 * x + 1) (2 * x) then 1 else 0 :=
    vis_read F (2 * x + 1) (2 * x) (by omega) hvis2
  have r3 := read_r_run (B := B) (σ := σ2) (e := .mul (.lit 2) (V "x")) (idx := 2 * x)
    (by
      have := evalB_bin (op := .mul) (evalB_lit (B := B) (σ := σ2) (n := 2) (by omega))
        (evalB_var (x := "x") (by rw [hx2']; omega)) (by rw [hx2']; show 2 * x < B; omega)
      simpa [Bop.apply, hx2'] using this)
    (by rw [hc2.lvis]; omega) (by rw [hv1]; split <;> omega)
  set σ3 := σ2.setVar "r" ((σ2.arrs "vis").getD (2 * x) 0) with hσ3
  have hc3 : Core F y off tgt σ3 := hc2.setVar "r" (by decide) _
  have hx3 : σ3.vars "x" = x := by simp [hσ3, hx2']
  have hans3 : σ3.vars "ans" = σ.vars "ans" := by simp [hσ3, hans2']
  have hr3 : σ3.vars "r" = if RT F (2 * x + 1) (2 * x) then 1 else 0 := by
    rw [hσ3]; simp only [vars_setVar, String.reduceEq, ↓reduceIte]; exact hv1
  by_cases hA : RT F (2 * x + 1) (2 * x)
  · -- the negative literal is reached: the second search
    have hr3' : σ3.vars "r" = 1 := by rw [hr3, if_pos hA]
    have r4 := assign_s0_run (B := B) (σ := σ3) (by rw [hx3]; omega) h2B
    set σ4 := σ3.setVar "s" (2 * σ3.vars "x") with hσ4
    have hc4 : Core F y off tgt σ4 := hc3.setVar "s" (by decide) _
    have hs4 : σ4.vars "s" = 2 * x := by rw [hσ4]; simp [hx3]
    obtain ⟨σ5, r5, h5⟩ := (bfsAny_spec F off tgt hB).run (σ := σ4)
      ⟨hc4.graph, hc4.hN, by rw [hs4]; omega, hc4.lvis, hc4.lq⟩
    rw [hs4] at h5
    obtain ⟨hc5, hx5, hans5, -⟩ := core_of_bfs F y off tgt hc4 _ h5
    have hx5' : σ5.vars "x" = x := by rw [hx5, hσ4]; simp [hx3]
    have hans5' : σ5.vars "ans" = σ.vars "ans" := by rw [hans5, hσ4]; simp [hans3]
    have hv2 : (σ5.arrs "vis").getD (2 * x + 1) 0 =
        if RT F (2 * x) (2 * x + 1) then 1 else 0 :=
      vis_read F (2 * x) (2 * x + 1) (by omega) h5.1
    have r6 := read_r_run (B := B) (σ := σ5) (e := .add (.mul (.lit 2) (V "x")) (.lit 1))
      (idx := 2 * x + 1)
      (by
        have e1 := evalB_bin (op := .mul) (evalB_lit (B := B) (σ := σ5) (n := 2) (by omega))
          (evalB_var (x := "x") (by rw [hx5']; omega)) (by rw [hx5']; show 2 * x < B; omega)
        have := evalB_bin (op := .add) e1 (evalB_lit (B := B) (σ := σ5) (n := 1) (by omega))
          (by rw [hx5']; show 2 * x + 1 < B; omega)
        simpa [Bop.apply, hx5'] using this)
      (by rw [hc5.lvis]; omega) (by rw [hv2]; split <;> omega)
    set σ6 := σ5.setVar "r" ((σ5.arrs "vis").getD (2 * x + 1) 0) with hσ6
    have hc6 : Core F y off tgt σ6 := hc5.setVar "r" (by decide) _
    have hx6 : σ6.vars "x" = x := by simp [hσ6, hx5']
    have hans6 : σ6.vars "ans" = σ.vars "ans" := by simp [hσ6, hans5']
    have hr6 : σ6.vars "r" = if RT F (2 * x) (2 * x + 1) then 1 else 0 := by
      rw [hσ6]; simp only [vars_setVar, String.reduceEq, ↓reduceIte]; exact hv2
    by_cases hA2 : RT F (2 * x) (2 * x + 1)
    · -- contradictory: the answer is no
      have hr6' : σ6.vars "r" = 1 := by rw [hr6, if_pos hA2]
      have r7 : Run B (.assign "ans" (.lit 0)) σ6 (σ6.setVar "ans" 0) 2 :=
        Run.assign (evalB_lit (by omega))
      have run : Run B searchesCom σ (σ6.setVar "ans" 0)
          (6 + (Ks F + (5 + (1 + 3 + (4 + (Ks F + (7 + (1 + 3 + 2)))))))) := by
        refine r1.seq (r2.seq (r3.seq (Run.ite_true (cond_r_true hr3' h1B)
          (r4.seq (r5.seq (r6.seq (Run.ite_true (cond_r_true hr6' h1B) r7)))))))
      refine ⟨_, run.mono (by omega), hc6.setVar "ans" (by decide) _,
        by simp only [vars_setVar, String.reduceEq, ↓reduceIte]; exact hx6, by simp, ?_⟩
      simp only [vars_setVar, String.reduceEq, ↓reduceIte]
      constructor
      · intro h; omega
      · rintro ⟨-, hb⟩; exact absurd ⟨hA, hA2⟩ hb
    · -- not contradictory
      have hr6' : σ6.vars "r" = 0 := by rw [hr6, if_neg hA2]
      have run : Run B searchesCom σ σ6
          (6 + (Ks F + (5 + (1 + 3 + (4 + (Ks F + (7 + (1 + 3 + 1)))))))) := by
        refine r1.seq (r2.seq (r3.seq (Run.ite_true (cond_r_true hr3' h1B)
          (r4.seq (r5.seq (r6.seq (Run.ite_false (cond_r_false hr6' h1B) Run.skip)))))))
      refine ⟨_, run.mono (by omega), hc6, hx6, by rw [hans6]; exact hans, ?_⟩
      rw [hans6]
      constructor
      · intro h; exact ⟨h, fun hb => hA2 hb.2⟩
      · exact fun h => h.1
  · -- the negative literal is not reached
    have hr3' : σ3.vars "r" = 0 := by rw [hr3, if_neg hA]
    have run : Run B searchesCom σ σ3 (6 + (Ks F + (5 + (1 + 3 + 1)))) :=
      r1.seq (r2.seq (r3.seq (Run.ite_false (cond_r_false hr3' h1B) Run.skip)))
    refine ⟨_, run.mono (by omega), hc3, hx3, by rw [hans3]; exact hans, ?_⟩
    rw [hans3]
    constructor
    · intro h; exact ⟨h, fun hb => hA hb.1⟩
    · exact fun h => h.1

/-! ### One variable -/

variable {F y off tgt} in
theorem Core.bumpX {σ : Env} (hc : Core F y off tgt σ) (h : σ.vars "x" + 1 ≤ mxOf (lits F)) :
    Core F y off tgt (σ.setVar "x" (σ.vars "x" + 1)) := by
  refine ⟨⟨?_, hc.graph.2⟩, ?_, ?_, ?_, ?_, ?_, ?_, hc.hmx, ?_⟩
  · simpa using hc.graph.1
  · simp; exact hc.hN
  · simp; exact hc.mx
  · simp; exact h
  · simpa using hc.occ
  · simpa using hc.lvis
  · simpa using hc.lq
  · simpa using hc.out

theorem mem_vars_lt {x : ℕ} (hx : x ∈ vars F) : x < mxOf (lits F) := by
  obtain ⟨j, hj, rfl⟩ := (mem_vars_iff F x).1 hx
  have := iv_lt F j hj; omega

/-- **One variable.** The cost is a constant, plus two searches if the variable occurs. -/
theorem varBody_run (hB : N F + (edges F).length + 16 < B) (hyB : 2 * y.length + 8 < B)
    {σ : Env} (hI : Inv F y off tgt σ) (hlt : σ.vars "x" < mxOf (lits F)) :
    ∃ σ' K, Run B varBody σ σ' K ∧ Inv F y off tgt σ' ∧ σ'.vars "x" = σ.vars "x" + 1 ∧
      K ≤ 12 + (if σ.vars "x" ∈ vars F then 2 * Ks F + 40 else 0) := by
  have hc := hI.core
  have hmx := hc.hmx
  have hxB : σ.vars "x" < B := by omega
  have h1B : 1 < B := by omega
  -- o := occ[x]
  have hocc : (σ.arrs "occ")[σ.vars "x"]? = some (occF F (σ.vars "x")) := by
    rw [hc.occ, getElem?_arrOf _ (by omega)]
  have hoccB : occF F (σ.vars "x") < B := by unfold occF; split <;> omega
  have r1 : Run B (.assign "o" (.get "occ" (V "x"))) σ (σ.setVar "o" (occF F (σ.vars "x"))) 3 :=
    (Run.assign (evalB_get (evalB_var hxB) hocc hoccB)).mono (by simp)
  set σ1 := σ.setVar "o" (occF F (σ.vars "x")) with hσ1
  have hc1 : Core F y off tgt σ1 := hc.setVar "o" (by decide) _
  have hx1 : σ1.vars "x" = σ.vars "x" := by simp [hσ1]
  have hans1 : σ1.vars "ans" = σ.vars "ans" := by simp [hσ1]
  have ho1 : σ1.vars "o" = occF F (σ.vars "x") := by simp [hσ1]
  have hcond : (Cond.eq (V "o") (.lit 1)).evalB B σ1 = some (occF F (σ.vars "x") == 1) := by
    rw [evalB_condEq (evalB_var (by rw [ho1]; exact hoccB)) (evalB_lit h1B), ho1]
  -- the bump, from any state with the right `x`
  have bump_run : ∀ τ : Env, τ.vars "x" = σ.vars "x" →
      Run B (bump "x") τ (τ.setVar "x" (σ.vars "x" + 1)) 4 := by
    intro τ hτ
    have := evalB_bin (op := .add) (evalB_var (B := B) (x := "x") (σ := τ) (by omega))
      (evalB_lit (B := B) (n := 1) (by omega)) (by rw [hτ]; show σ.vars "x" + 1 < B; omega)
    rw [hτ] at this
    exact (Run.assign (by simpa [Bop.apply] using this)).mono (by simp)
  by_cases hv : σ.vars "x" ∈ vars F
  · -- the variable occurs: the searches
    have hocc1 : occF F (σ.vars "x") = 1 := by unfold occF; rw [if_pos hv]
    rw [hocc1] at hcond
    obtain ⟨σ2, r2, hc2, hx2, hans2, hiff⟩ := (searches_spec F y off tgt hB).run (σ := σ1)
      ⟨hc1, by rw [hx1]; exact hlt, by rw [hans1]; exact hI.ans1⟩
    rw [hx1] at hx2 hiff; rw [hans1] at hiff
    have r3 := bump_run σ2 hx2
    refine ⟨_, _, r1.seq ((Run.ite_true hcond r2).seq r3), ?_, by simp, by rw [if_pos hv]; simp; omega⟩
    have hcb := hc2.bumpX (by rw [hx2]; omega)
    rw [hx2] at hcb
    refine ⟨hcb, by simp; exact hans2, ?_⟩
    simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hiff, hI.ans]
    constructor
    · rintro ⟨h1, h2⟩ x' hx' hx'v
      rcases Nat.lt_or_ge x' (σ.vars "x") with h | h
      · exact h1 x' h hx'v
      · have : x' = σ.vars "x" := by omega
        subst this; exact h2
    · intro h
      exact ⟨fun x' hx' hx'v => h x' (by omega) hx'v, h _ (by omega) hv⟩
  · -- the variable does not occur
    have hocc0 : occF F (σ.vars "x") = 0 := by unfold occF; rw [if_neg hv]
    rw [hocc0] at hcond
    have r3 := bump_run σ1 hx1
    refine ⟨_, _, r1.seq ((Run.ite_false hcond Run.skip).seq r3), ?_, by simp, by rw [if_neg hv]; simp⟩
    have hcb := hc1.bumpX (by rw [hx1]; omega)
    rw [hx1] at hcb
    refine ⟨hcb, by simp; rw [hans1]; exact hI.ans1, ?_⟩
    simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hans1, hI.ans]
    constructor
    · intro h1 x' hx' hx'v
      rcases Nat.lt_or_ge x' (σ.vars "x") with h | h
      · exact h1 x' h hx'v
      · have : x' = σ.vars "x" := by omega
        subst this; exact absurd hx'v hv
    · intro h x' hx' hx'v; exact h x' (by omega) hx'v

/-! ### The loop -/

/-- The cost of the loop over the variables. -/
def Kloop : ℕ := 60 * mxOf (lits F) + (2 * Ks F + 40) * varCount F + 4

/-- **The loop over the variables**, paid out of the potential. -/
theorem loop_spec (hB : N F + (edges F).length + 16 < B) (hyB : 2 * y.length + 8 < B) :
    Spec B (fun σ => Inv F y off tgt σ ∧ σ.vars "x" = 0) (.while (.lt (V "x") (V "mx")) varBody)
      (fun _ σ' => Inv F y off tgt σ' ∧ σ'.vars "x" = mxOf (lits F)) (Kloop F) := by
  refine (Spec.while_potential (Inv F y off tgt) (Pot F) ?_ ?_ (fun _ h => h.1) ?_).post ?_
  · intro σ hI
    have := hI.core.x; have := hI.core.hmx; have := hI.core.mx
    exact evalB_condLt_vars (by omega) (by omega)
  · intro σ hI hcond
    have hlt : σ.vars "x" < mxOf (lits F) := by
      have := lt_of_condLt_true hcond; rw [hI.core.mx] at this; exact this
    obtain ⟨σ', K, hr, hI', hx', hK⟩ := varBody_run F y off tgt hB hyB hI hlt
    refine ⟨σ', K, hr, hI', ?_⟩
    rw [pot_step F σ hlt]
    unfold Pot
    rw [hx']
    simp only [size_condLt, size_var]
    split_ifs at hK ⊢ <;> omega
  · intro σ ⟨hI, hx⟩
    have := pot_zero_le F σ hx
    simp only [size_condLt, size_var]
    unfold Kloop; omega
  · intro σ σ' _ ⟨hI', hfalse⟩
    have := le_of_condLt_false hfalse
    rw [hI'.core.mx] at this
    exact ⟨hI', by have := hI'.core.x; omega⟩

/-- **The driver**: from a core state, the answer is written. -/
theorem driver_spec (hB : N F + (edges F).length + 16 < B) (hyB : 2 * y.length + 8 < B) :
    Spec B (Core F y off tgt) driver
      (fun _ σ' => σ'.out = [if ∀ x ∈ vars F, ¬ Bad F x then 1 else 0]) (2 + 2 + Kloop F + 2) := by
  intro σ hc
  unfold driver
  have h1B : 1 < B := by omega
  have r1 : Run B (.assign "ans" (.lit 1)) σ (σ.setVar "ans" 1) 2 :=
    Run.assign (evalB_lit h1B)
  have r2 : Run B (.assign "x" (.lit 0)) (σ.setVar "ans" 1) ((σ.setVar "ans" 1).setVar "x" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  have hI : Inv F y off tgt ((σ.setVar "ans" 1).setVar "x" 0) := by
    refine ⟨?_, by simp, ?_⟩
    · have := (hc.setVar "ans" (by decide) 1)
      refine ⟨⟨?_, this.graph.2⟩, ?_, ?_, ?_, ?_, ?_, ?_, hc.hmx, ?_⟩
      · simpa using this.graph.1
      · simp; exact this.hN
      · simp; exact this.mx
      · simp
      · simpa using this.occ
      · simpa using this.lvis
      · simpa using this.lq
      · simpa using this.out
    · simp
  obtain ⟨σ3, r3, hI3, hx3⟩ := (loop_spec F y off tgt hB hyB).run ⟨hI, by simp⟩
  have hansB : σ3.vars "ans" < B := by have := hI3.ans1; omega
  have r4 : Run B (.write (V "ans")) σ3 { σ3 with out := σ3.out ++ [σ3.vars "ans"] } 2 :=
    Run.write (evalB_var hansB)
  refine ⟨_, (r1.seq (r2.seq (r3.seq r4))).mono (by omega), ?_⟩
  show σ3.out ++ [σ3.vars "ans"] = _
  rw [hI3.core.out]
  have hiff : σ3.vars "ans" = 1 ↔ ∀ x ∈ vars F, ¬ Bad F x := by
    rw [hI3.ans, hx3]
    exact ⟨fun h x hx => h x (mem_vars_lt F hx) hx, fun h x _ hx => h x hx⟩
  have hans1 := hI3.ans1
  rw [List.nil_append]
  split
  · rw [hiff.2 ‹_›]
  · have h1 : σ3.vars "ans" ≠ 1 := fun h => ‹¬ _› (hiff.1 h)
    have h0 : σ3.vars "ans" = 0 := by omega
    rw [h0]

end Lax117284Proofs.TwoSAT.Machine.Driver

end

/-! ### `Lax117284Proofs.TwoSAT.Machine.Language` -/

section
/-!
Membership in 2-SAT, in the terms of the machine: the scan accepts the bits, every clause has
one or two literals, and no occurring variable is contradictory.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Language

open Lax429075.CNF Lax429075.Encoding Lax434930.PolynomialTime Lax117284.TwoSatCNF
open Lax391470Proofs.CnfScan Lax117284Proofs.TwoSAT.Machine.Scan Lax117284Proofs.TwoSAT.Machine.Model

/-- The concept's bits are the scanner's. -/
theorem bitsOf_eq (x : List ℕ) :
    Lax117284.TwoSatRunningTime.bitsOf x = Lax391470Proofs.Bits.bitsOf x := rfl

/-- **The bits of a word are in 2-SAT** exactly when the scan accepts them as a satisfiable
2-CNF formula. -/
theorem mem_twoSAT_iff (y : List ℕ) :
    Lax391470Proofs.Bits.bitsOf y ∈ TwoSAT ↔
      Accepted y ∧ IsTwoCNF (formulaOf y) ∧ Satisfiable (formulaOf y) := by
  constructor
  · rintro ⟨F, hF, h2, hs⟩
    have h := accept_complete F
    rw [hF] at h
    have hF' : formulaOf y = F := h.2
    exact ⟨h.1, hF' ▸ h2, hF' ▸ hs⟩
  · rintro ⟨hacc, h2, hs⟩
    exact ⟨formulaOf y, accept_sound hacc, h2, hs⟩

/-- The same, in the machine's terms. -/
theorem mem_twoSAT_iff' (y : List ℕ) :
    Lax391470Proofs.Bits.bitsOf y ∈ TwoSAT ↔
      Accepted y ∧ WidthOk (formulaOf y) ∧ ∀ x ∈ vars (formulaOf y), ¬ Bad (formulaOf y) x := by
  rw [mem_twoSAT_iff, ← answer_iff]

/-- The concept's count of variables is the scanned formula's. -/
theorem wordVarCount_eq (y : List ℕ) (h : Accepted y) :
    Lax117284.TwoSatRunningTime.wordVarCount y = varCount (formulaOf y) := by
  unfold Lax117284.TwoSatRunningTime.wordVarCount
  have h' : (run init (Lax391470Proofs.Bits.bitsOf y)).ph = 4 := h
  rw [bitsOf_eq, decodeCNF_eq, if_pos h']; rfl

theorem wordVarCount_eq_zero (y : List ℕ) (h : ¬ Accepted y) :
    Lax117284.TwoSatRunningTime.wordVarCount y = 0 := by
  unfold Lax117284.TwoSatRunningTime.wordVarCount
  have h' : ¬ (run init (Lax391470Proofs.Bits.bitsOf y)).ph = 4 := h
  rw [bitsOf_eq, decodeCNF_eq, if_neg h']; rfl

end Lax117284Proofs.TwoSAT.Machine.Language

end

/-! ### `Lax117284Proofs.TwoSAT.Machine.Main` -/

section
/-!
The whole program, after the word has been read into `a` with its length in `L`: the scan, and
then either the answer `0` — the bits are no encoding of a formula, or a clause has no literal
or more than two — or the graph and the searches.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Main

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax429075.CNF Lax391470Proofs.L2ScanModel Lax391470Proofs.L2Scan Lax117284.TwoSatCNF
open Lax117284Proofs.TwoSAT.Machine.Model Lax117284Proofs.TwoSAT.Machine.Scan Lax117284Proofs.TwoSAT.Machine.Width
open Lax117284Proofs.TwoSAT.Machine.Driver Lax117284Proofs.TwoSAT.Machine.Language
open scoped Classical

abbrev V (s : String) : Expr := .var s

/-- The answer `0`. -/
def reject : Com := .write (.lit 0)

/-- The accepting path: the number of nodes, the graph, the searches. -/
def accept : Com :=
  .seq (.assign "N" (.mul (.lit 2) (V "mx")))
    (.seq (.assign "x" (.lit 0)) (.seq Build.build driver))

/-- After the scan: reject unless it accepted; the width check; reject unless it passed. -/
def afterScan : Com :=
  .ite (.eq (V "ph") (.lit 4))
    (.seq width (.ite (.eq (V "ok") (.lit 1)) accept reject))
    reject

/-- The program after the word has been read. -/
def body : Com := .seq scanPart afterScan

/-- The array lengths, as functions of the word. -/
def ext (y : List ℕ) : String → ℕ := fun a =>
  if a = "cnt" then y.length + 1
  else if a = "occ" then y.length + 2
  else if a = "deg" ∨ a = "off" ∨ a = "pos" then N (formulaOf y) + 1
  else if a = "tgt" then (edges (formulaOf y)).length
  else if a = "vis" ∨ a = "q" then N (formulaOf y)
  else y.length

/-- The cost of the accepting path, on the formula. -/
def Kacc (F : Formula) : ℕ :=
  (44 * (lits F).length + 6) + (2 + (34 * F.length + 6)) + 4 + 4 + 2 +
    138 * ((lits F).length + N F + F.length + 1) + (2 + 2 + Kloop F + 2)

/-- The cost of the program after the read. -/
noncomputable def Kbody (y : List ℕ) : ℕ :=
  (2 + (64 * y.length + 6)) + 4 + (if Accepted y then 4 + Kacc (formulaOf y) else 2)

/-! ### Frame facts -/

lemma width_noWrite : width.NoWrite := by
  simp [width, countLoop, countBody, checkLoop, checkBody, Com.NoWrite]

lemma build_noWrite : Build.build.NoWrite := by
  simp [Build.build, Build.degPass, Build.degBody, Build.degUnit, Build.degPair, Build.prefPass,
    Build.prefBody, Build.fillPass, Build.fillBody, Build.fillUnit, Build.fillPair, Com.NoWrite]

lemma mem_wvars_width {z : String} (hz : z ∈ width.wvars) : z ∈ ["i", "cc", "x", "t", "ok"] := by
  simp only [width, countLoop, countBody, checkLoop, checkBody, Com.wvars, List.mem_append,
    List.mem_cons, List.not_mem_nil] at hz ⊢
  tauto

lemma mem_warrs_width {a : String} (ha : a ∈ width.warrs) : a ∈ ["cnt", "occ"] := by
  simp only [width, countLoop, countBody, checkLoop, checkBody, Com.warrs, List.mem_append,
    List.mem_cons, List.not_mem_nil] at ha ⊢
  tauto

lemma mem_warrs_build {a : String} (ha : a ∈ Build.build.warrs) :
    a ∈ ["deg", "off", "pos", "tgt"] := by
  simp only [Build.build, Build.degPass, Build.degBody, Build.degUnit, Build.degPair,
    Build.prefPass, Build.prefBody, Build.fillPass, Build.fillBody, Build.fillUnit,
    Build.fillPair, Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil] at ha ⊢
  tauto

lemma mx_not_wvars_build : "mx" ∉ Build.build.wvars := by decide

/-! ### The whole program -/

variable {B : ℕ} {y : List ℕ}

theorem ph_le (y : List ℕ) : (st y).ph ≤ 5 := ph_run_le _

/-- **The program after the read** writes the answer. -/
theorem body_spec (hB : 5 * y.length + 24 < B) (hyB : ∀ v ∈ y, v < B) :
    Spec B (ReadPost y (ext y)) body
      (fun _ σ' => σ'.out = [if Lax391470Proofs.Bits.bitsOf y ∈ TwoSAT then 1 else 0])
      (Kbody y) := by
  intro σ h0
  have h4B : 4 < B := by omega
  have h1B : 1 < B := by omega
  -- the scan
  obtain ⟨σ1, r1, hS⟩ := (scanPart_spec (B := B) (ext := ext y) (by omega) hyB
    (by simp [ext])).run h0
  have hph : σ1.vars "ph" = (st y).ph := hS.ph
  have hphB : σ1.vars "ph" < B := by rw [hph]; have := ph_le y; omega
  have hcond : (Cond.eq (V "ph") (.lit 4)).evalB B σ1 = some ((st y).ph == 4) := by
    rw [evalB_condEq (evalB_var hphB) (evalB_lit h4B), hph]
  by_cases hacc : Accepted y
  · -- accepted: the width check
    have hF := hS.facts hacc
    set F := formulaOf y with hFdef
    have hcond' : (Cond.eq (V "ph") (.lit 4)).evalB B σ1 = some true := by
      rw [hcond]; have : (st y).ph = 4 := hacc; rw [this]; rfl
    have hk := hF.hk; have hC := hF.hC; have hmx := hF.hmx
    have hN : N F = 2 * mxOf (lits F) := rfl
    have hE := length_edges_le F
    obtain ⟨σ2, r2, hW, fv2, fa2, -, hout2⟩ := (width_spec (B := B) (ext := ext y) F (by omega)
      (by simp [ext])).frame.run hF
    have hout2' : σ2.out = [] := by rw [hout2 width_noWrite]; exact hF.out
    have hokB : σ2.vars "ok" < B := by have := hW.ok1; omega
    have hcondok : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some (σ2.vars "ok" == 1) :=
      evalB_condEq (evalB_var hokB) (evalB_lit h1B)
    have hfv2 : ∀ z, z ∉ ["i", "cc", "x", "t", "ok"] → σ2.vars z = σ1.vars z :=
      fun z hz => fv2 z fun hm => hz (mem_wvars_width hm)
    have hfa2 : ∀ a, a ∉ ["cnt", "occ"] → σ2.arrs a = σ1.arrs a :=
      fun a ha => fa2 a fun hm => ha (mem_warrs_width hm)
    by_cases hw : WidthOk F
    · -- the graph and the searches
      have hok1 : σ2.vars "ok" = 1 := hW.ok.2 hw
      have hcondok' : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some true := by
        rw [hcondok, hok1]; rfl
      have hmx2 : σ2.vars "mx" = mxOf (lits F) := by rw [hfv2 "mx" (by decide)]; exact hF.mx
      -- N := 2 * mx
      have rN : Run B (.assign "N" (.mul (.lit 2) (V "mx"))) σ2 (σ2.setVar "N" (N F)) 4 := by
        have := evalB_bin (op := .mul) (evalB_lit (B := B) (σ := σ2) (n := 2) (by omega))
          (evalB_var (x := "mx") (by rw [hmx2]; omega)) (by rw [hmx2]; show 2 * mxOf (lits F) < B; omega)
        rw [hmx2] at this
        exact (Run.assign (by simpa [Bop.apply, N] using this)).mono (by simp)
      set σ3 := σ2.setVar "N" (N F) with hσ3
      have rX : Run B (.assign "x" (.lit 0)) σ3 (σ3.setVar "x" 0) 2 := Run.assign (evalB_lit (by omega))
      set σ4 := σ3.setVar "x" 0 with hσ4
      -- what the construction needs
      have hvr4 : σ4.arrs "vr" = σ1.arrs "vr" := by
        simp only [hσ4, hσ3, arrs_setVar]; exact hfa2 "vr" (by decide)
      have hsg4 : σ4.arrs "sg" = σ1.arrs "sg" := by
        simp only [hσ4, hσ3, arrs_setVar]; exact hfa2 "sg" (by decide)
      have hcl4 : σ4.arrs "cl" = σ1.arrs "cl" := by
        simp only [hσ4, hσ3, arrs_setVar]; exact hfa2 "cl" (by decide)
      have hcnt4 : σ4.arrs "cnt" = arrOf (y.length + 1) (cntF F) := by
        simp only [hσ4, hσ3, arrs_setVar]; exact hW.cnt
      have hfresh : ∀ a, a ∉ ["a", "vr", "sg", "cl", "cnt", "occ"] →
          σ4.arrs a = List.replicate (ext y a) 0 := by
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
        simp only [hσ4, hσ3, arrs_setVar]
        rw [hfa2 a (by simp; tauto)]
        exact hF.arr a (by simp; tauto)
      have hpre : Build.Pre F σ4 := by
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [hσ4, hσ3, vars_setVar, String.reduceEq, ↓reduceIte]; exact hW.k
        · simp only [hσ4, hσ3, vars_setVar, String.reduceEq, ↓reduceIte]; exact hW.C
        · simp only [hσ4, hσ3, vars_setVar, String.reduceEq, ↓reduceIte]
        · rw [hvr4, hF.lvr]; exact hk
        · rw [hsg4, hF.lsg]; exact hk
        · rw [hcnt4, length_arrOf]; omega
        · intro i hi; rw [hvr4]; exact hF.vr i hi
        · intro i hi; rw [hsg4]; exact hF.sg i hi
        · intro c hc; rw [hcnt4, getD_arrOf _ (by omega)]; unfold cntF; rw [if_pos hc]
        · rw [hcl4, hF.lcl]; exact hk
        · intro i hi; rw [hcl4]; exact hF.cl i hi
        · rw [hfresh "deg" (by decide)]; simp [ext, ← hFdef]
        · rw [hfresh "off" (by decide)]; simp [ext, ← hFdef]
        · rw [hfresh "pos" (by decide)]; simp [ext, ← hFdef]
        · rw [hfresh "tgt" (by decide)]; simp [ext, ← hFdef]
      obtain ⟨σ5, r5, ⟨off, tgt, hcsr, hrows, hE5, hN5, -, -⟩, fv5, fa5, -, hout5⟩ :=
        (Build.build_spec (B := B) F hw (by omega)).frame.run hpre
      have hfa5 : ∀ a, a ∉ ["deg", "off", "pos", "tgt"] → σ5.arrs a = σ4.arrs a :=
        fun a ha => fa5 a fun hm => ha (mem_warrs_build hm)
      -- what the driver needs
      have hcore : Core F y off tgt σ5 := by
        refine ⟨⟨hcsr, hrows⟩, hN5, ?_, ?_, ?_, ?_, ?_, hmx, ?_⟩
        · rw [fv5 "mx" mx_not_wvars_build]
          simp only [hσ4, hσ3, vars_setVar, String.reduceEq, ↓reduceIte]; exact hmx2
        · rw [fv5 "x" (by decide)]
          simp only [hσ4, vars_setVar, ↓reduceIte]; omega
        · rw [hfa5 "occ" (by decide)]
          simp only [hσ4, hσ3, arrs_setVar]; exact hW.occ
        · rw [hfa5 "vis" (by decide), hfresh "vis" (by decide)]; simp [ext, ← hFdef]
        · rw [hfa5 "q" (by decide), hfresh "q" (by decide)]; simp [ext, ← hFdef]
        · rw [hout5 build_noWrite]; simp only [hσ4, hσ3, out_setVar]; exact hout2'
      obtain ⟨σ6, r6, hout6⟩ := (driver_spec (B := B) F y off tgt (by omega) (by omega)).run hcore
      refine ⟨σ6, ?_, ?_⟩
      · have run := r1.seq (Run.ite_true (d := reject) hcond' (r2.seq
          (Run.ite_true (d := reject) hcondok' (rN.seq (rX.seq (r5.seq r6))))))
        refine run.mono ?_
        unfold Kbody Kacc
        rw [if_pos hacc]
        simp only [size_condEq, size_var, size_lit]
        try simp only [← hFdef]
        try rw [hmx2]
        omega
      · show σ6.out = _
        rw [hout6, mem_twoSAT_iff', ← hFdef]
        simp only [hacc, hw, true_and]
    · -- a clause of the wrong width
      have hok0 : σ2.vars "ok" ≠ 1 := fun h => hw (hW.ok.1 h)
      have hcondok' : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some false := by
        rw [hcondok]; exact congrArg some (beq_eq_false_iff_ne.mpr hok0)
      have r3 : Run B reject σ2 { σ2 with out := σ2.out ++ [0] } 2 := Run.write (evalB_lit (by omega))
      refine ⟨{ σ2 with out := σ2.out ++ [0] }, ?_, ?_⟩
      · have run := r1.seq (Run.ite_true (d := reject) hcond'
          (r2.seq (Run.ite_false (c := accept) hcondok' r3)))
        refine run.mono ?_
        unfold Kbody Kacc
        rw [if_pos hacc]
        simp only [size_condEq, size_var, size_lit]
        try simp only [← hFdef]
        omega
      · show σ2.out ++ [0] = _
        rw [hout2', mem_twoSAT_iff', ← hFdef]
        simp [hw]
  · -- not the encoding of a formula
    have hcond' : (Cond.eq (V "ph") (.lit 4)).evalB B σ1 = some false := by
      rw [hcond]; exact congrArg some (beq_eq_false_iff_ne.mpr hacc)
    have r3 : Run B reject σ1 { σ1 with out := σ1.out ++ [0] } 2 := Run.write (evalB_lit (by omega))
    refine ⟨{ σ1 with out := σ1.out ++ [0] }, ?_, ?_⟩
    · have run := r1.seq (Run.ite_false
        (c := .seq width (.ite (.eq (V "ok") (.lit 1)) accept reject)) hcond' r3)
      refine run.mono ?_
      unfold Kbody
      rw [if_neg hacc]
      simp only [size_condEq, size_var, size_lit]
      omega
    · show σ1.out ++ [0] = _
      rw [hS.out, mem_twoSAT_iff']
      simp [hacc]

end Lax117284Proofs.TwoSAT.Machine.Main

end

/-! ### `Lax117284Proofs.TwoSAT.Machine.Wrap` -/

section
/-!
A machine program that knows how long its input is.

IMP+ has no way to ask how long the input tape is: a `read` from an exhausted tape is stuck, and
the concept's words are *arbitrary* lists (a table shorter than the header claims reads as zeros).
The machine, though, has `inputLength`. So the machine program here is one instruction longer than
the compiled IMP+ one: `inputLength` into the cell of the scalar `"len"`, then the compiled code,
laid out at address `1`, then `halt`. The IMP+ program is proved against the environment in which
`"len"` already holds the input length; `wrap_runsTo` is the simulation theorem for that entry
state, obtained from `compile_correct` (which starts from *any* state representing the
environment, with the code laid out at the program counter).
-/

namespace Lax117284Proofs.TwoSAT.Machine.Wrap

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Simulation
open Lax808846Proofs.Machine

variable {x : List ℕ}

/-- The machine program: the input length into `"len"`, the compiled code, `halt`. -/
def wrapProgram (L : Layout) (c : Com) : Program :=
  Instr.inputLength (L.varAddr "len") :: (compile L c 1 ++ [Instr.halt])

/-- The environment the IMP+ program starts in: all zero, arrays as declared, and `"len"` holding
the length of the input. -/
def lenEnv (ext : String → ℕ) (x : List ℕ) : Env := (initEnv ext x).setVar "len" x.length

/-- The machine state after the first instruction. -/
def wrapState (L : Layout) (w : ℕ) (x : List ℕ) : State :=
  ⟨1, setCell w (initState x).mem (L.varAddr "len") x.length, x, x, []⟩

theorem wrap_step (L : Layout) (c : Com) (w : ℕ) (x : List ℕ) :
    run w (wrapProgram L c) 1 (initState x) = some (wrapState L w x) := by
  rw [run_one (ins := Instr.inputLength (L.varAddr "len")) (by simp [wrapProgram, initState]),
    effect_inputLength]
  rfl

theorem represents_wrapState {L : Layout} {B w : ℕ} (hfit : L.FitsWords B w)
    (hlen : "len" ∈ L.scalars) (hxB : x.length < B) (ext : String → ℕ) :
    Represents L (lenEnv ext x) (wrapState L w x) where
  vars y hy := by
    have hyw := L.varAddr_lt_two_pow hfit hy
    have hlw := L.varAddr_lt_two_pow hfit hlen
    have hxw : x.length < 2 ^ w := lt_of_lt_of_le hxB hfit.bound
    show setCell w (initState x).mem (L.varAddr "len") x.length (L.varAddr y) =
      (lenEnv ext x).vars y
    by_cases hyl : y = "len"
    · subst hyl
      rw [setCell_self _ hlw hxw]
      simp [lenEnv]
    · rw [setCell_of_ne _ _ hlw (fun h => hyl (varAddr_inj L hy hlen h))]
      simp [lenEnv, hyl, initState, initEnv]
  arrs a ha i hi := by
    have hlw := L.varAddr_lt_two_pow hfit hlen
    show setCell w (initState x).mem (L.varAddr "len") x.length (L.arrAddr a i) =
      ((lenEnv ext x).arrs a).getD i 0
    rw [setCell_of_ne _ _ hlw (fun h => varAddr_ne_arrAddr L hlen (a := a) i h.symm)]
    have : (lenEnv ext x).arrs a = List.replicate (ext a) 0 := rfl
    rw [this]
    show (0 : ℕ) = _
    rw [List.getD_eq_getElem?_getD]
    rcases h : (List.replicate (ext a) (0 : ℕ))[i]? with _ | u
    · rfl
    · have := List.mem_of_getElem? h
      simp only [List.mem_replicate] at this
      rw [this.2]; rfl
  inp := rfl
  out := rfl

theorem wrap_fits (L : Layout) (c : Com) :
    Fits (wrapProgram L c) 1 (compile L c 1) := by
  intro i hi
  show (Instr.inputLength (L.varAddr "len") :: (compile L c 1 ++ [Instr.halt]))[1 + i]? = _
  rw [Nat.add_comm, List.getElem?_cons_succ, List.getElem?_append_left hi]

/-- **The simulation theorem for the wrapped program.** -/
theorem wrap_runsTo {L : Layout} {B w : ℕ} {c : Com} {ext : String → ℕ} {x : List ℕ}
    {σ' : Env} {k : ℕ} (hfit : L.FitsWords B w) (hok : Com.Ok L c)
    (hlen : "len" ∈ L.scalars) (hx : ∀ v ∈ x, v < B) (hxl : x.length < B)
    (hbs : BigStepB B c (lenEnv ext x) σ' k) :
    ∃ t ≤ L.const * k + 2, RunsTo w (wrapProgram L c) x σ'.out t := by
  have hinp : (lenEnv ext x).InpBounded B := fun v hv => hx v hv
  obtain ⟨t, s', ht, hr, hpc, hrep⟩ :=
    compile_correct hfit hbs hok hinp 1 (wrapState L w x) rfl
      (represents_wrapState hfit hlen hxl ext) (wrap_fits L c)
  have hhalt : (wrapProgram L c)[s'.pc]? = some Instr.halt := by
    rw [hpc, wrapProgram, Nat.add_comm 1, List.getElem?_cons_succ, ← compile_length L c 1,
      List.getElem?_append_right (by omega)]
    simp
  refine ⟨1 + t + 1, by omega, 1 + t, s', run_trans (wrap_step L c w x) hr, ?_, ?_, ?_⟩
  · rw [step_eq, hhalt]; rfl
  · rw [← hrep.out]
  · rw [terminalCost_of_getElem? hhalt]

end Lax117284Proofs.TwoSAT.Machine.Wrap

end

/-! ### `Lax117284Proofs.TwoSAT.Machine.ToP` -/

section
/-!
From a polynomial-time word RAM computation of the decision, on the zeros and ones of the
word, to membership of 2-SAT in the class P: the RAM/Turing equivalence of `lax-759944` and the
two fixed translations of `lax-391470` give a polynomial-time Turing machine on the binary word
itself, and a machine writing the one bit of the answer is a machine for the class.
-/

namespace Lax117284Proofs.TwoSAT.Machine.ToP

open Lax434930.PolynomialTime Lax117284.TwoSatCNF Lax759944.RamPolytime
open Lax391470Proofs.Bits
open scoped Classical

/-- The decision, as a map of binary words. -/
noncomputable def dec (w : Word) : Word := [decide (w ∈ TwoSAT)]

/-- The decision on the zeros and ones of a word: what the machine computes. -/
noncomputable def decBits (y : List ℕ) : List ℕ := natBits (dec (bitsOf y))

theorem decBits_natBits (w : Word) : decBits (natBits w) = natBits (dec w) := by
  unfold decBits; rw [bitsOf_natBits]

theorem decBits_eq (y : List ℕ) : decBits y = if bitsOf y ∈ TwoSAT then [1] else [0] := by
  unfold decBits dec natBits
  split <;> simp_all

/-- **2-SAT is in P once the decision is a polynomial-time RAM computation on bits.** -/
theorem mem_P_of_ram (h : RamPolytime decBits) : TwoSAT ∈ P := by
  obtain ⟨c⟩ := Lax391470Proofs.RamToTuring.polyTime_of_ram h decBits_natBits
  refine ⟨fun w => decide (w ∈ TwoSAT), fun w => by simp, ⟨?_⟩⟩
  exact
    { tm := c.tm
      inputAlphabet := c.inputAlphabet
      outputAlphabet := c.outputAlphabet
      time := c.time
      outputsFun := fun w => c.outputsFun w }

end Lax117284Proofs.TwoSAT.Machine.ToP

end

/-! ### `Lax117284Proofs.TwoSAT.Machine.Final` -/

section
/-!
The program on the word RAM: the layout, the two entry points — the raw word with its length
supplied by the machine, and the length-prefixed word of the polynomial-time predicate — and
the concept's running-time statement.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax429075.CNF Lax391470Proofs.L2ScanModel Lax117284.TwoSatCNF
open Lax117284Proofs.TwoSAT.Machine.Model Lax117284Proofs.TwoSAT.Machine.Scan Lax117284Proofs.TwoSAT.Machine.Width
open Lax117284Proofs.TwoSAT.Machine.Driver Lax117284Proofs.TwoSAT.Machine.Language Lax117284Proofs.TwoSAT.Machine.Main
open Lax117284Proofs.TwoSAT.Machine.Wrap Lax391470Proofs.ReadAll
open scoped Classical

/-- The layout: every scalar and every array the program mentions. -/
def layout : Layout :=
  ⟨["L", "rt", "rv", "len", "mx", "ph", "n", "C", "k", "p", "c", "i", "cc", "x", "t", "ok",
    "N", "E", "na", "nb", "ca", "cb", "u", "s", "head", "tail", "v", "j", "jend", "r", "o", "ans"],
   ["a", "vr", "sg", "cl", "cnt", "occ", "deg", "off", "pos", "tgt", "vis", "q"], 12⟩

/-- The program on the raw word: the machine has put its length into `len`. -/
def mainRaw : Com := .seq (.assign "L" (.var "len")) (.seq readLoop body)

/-- The program on the length-prefixed word. -/
def mainPre : Com := .seq readAll body

theorem body_ok : Com.Ok layout body := by
  simp [body, scanPart, Lax391470Proofs.L2Scan.scanLoop, Lax391470Proofs.L2Scan.scanBody,
    Lax391470Proofs.L2Scan.dispatch, Lax391470Proofs.L2Scan.phase3, afterScan, accept, reject,
    width, countLoop, countBody, checkLoop, checkBody, Build.build, Build.degPass, Build.degBody,
    Build.degUnit, Build.degPair, Build.prefPass, Build.prefBody, Build.fillPass, Build.fillBody,
    Build.fillUnit, Build.fillPair, driver, varBody, searchesCom, secondCom, Bfs.bfs, Bfs.clear,
    Bfs.initDrain, Bfs.drain, Bfs.expandBody, Bfs.scanBody, layout, Com.Ok, Cond.Ok, condExpr,
    Expr.Ok]

theorem mainRaw_ok : Com.Ok layout mainRaw := by
  refine ⟨?_, ?_, body_ok⟩
  · simp [layout, Com.Ok, Expr.Ok]
  · simp [readLoop, readBody, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem mainPre_ok : Com.Ok layout mainPre := by
  refine ⟨?_, body_ok⟩
  simp [readAll, readLoop, readBody, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

/-! ### Reading the raw word -/

/-- The value bound on a word of zeros and ones. -/
def Bd (y : List ℕ) : ℕ := 5 * y.length + 25

/-- The cost of the program on the raw word. -/
noncomputable def KRaw (y : List ℕ) : ℕ := 2 + (12 * y.length + 10) + Kbody y

lemma wvars_readLoop : readLoop.wvars = ["rt", "rv", "rt"] := by
  simp [readLoop, readBody, Com.wvars]
lemma warrs_readLoop : readLoop.warrs = ["a"] := by
  simp [readLoop, readBody, Com.warrs]

/-- After the read loop, the array `a` is the word. -/
theorem a_eq_of_rinv {y : List ℕ} {σ : Env} (h : RInv y σ) (ht : σ.vars "rt" = y.length) :
    σ.arrs "a" = y := by
  obtain ⟨-, -, hlen, hcell, -, -⟩ := h
  refine List.ext_getElem hlen fun i h1 h2 => ?_
  have := hcell i (by rw [ht]; exact h2)
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some,
    Option.getD_some] at this

/-- **The program on the raw word.** -/
theorem mainRaw_run (y : List ℕ) (hy1 : ∀ v ∈ y, v ≤ 1) :
    ∃ σ', Run (Bd y) mainRaw (lenEnv (ext y) y) σ' (KRaw y) ∧
      σ'.out = [if Lax391470Proofs.Bits.bitsOf y ∈ TwoSAT then 1 else 0] := by
  have hB : 5 * y.length + 24 < Bd y := by unfold Bd; omega
  have hyB : ∀ v ∈ y, v < Bd y := fun v hv => by have := hy1 v hv; unfold Bd; omega
  set σ0 := lenEnv (ext y) y with hσ0
  have hlen0 : σ0.vars "len" = y.length := by simp [hσ0, lenEnv]
  -- L := len
  have r0 : Run (Bd y) (.assign "L" (.var "len")) σ0 (σ0.setVar "L" y.length) 2 := by
    have := Run.assign (B := Bd y) (σ := σ0) (x := "L") (e := .var "len")
      (evalB_var (by rw [hlen0]; unfold Bd; omega))
    rw [hlen0] at this
    exact this.mono (by simp)
  set σ1 := σ0.setVar "L" y.length with hσ1
  -- the read loop
  obtain ⟨σ2, r2, ⟨hI2, ht2⟩, fv2, fa2, -, -⟩ :=
    (readLoop_spec (B := Bd y) (y := y) hyB (by unfold Bd; omega)).frame.run (σ := σ1) (by
      refine ⟨by simp [hσ1], by simp, ?_, fun i hi => by simp at hi, by simp [hσ1, hσ0, lenEnv, initEnv],
        by simp [hσ1, hσ0, lenEnv, initEnv]⟩
      simp [hσ1, hσ0, lenEnv, initEnv, ext])
  have hpost : ReadPost y (ext y) σ2 := by
    refine ⟨hI2.1, a_eq_of_rinv hI2 ht2, hI2.2.2.2.2.2, ?_, ?_⟩
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      rw [fv2 z (by rw [wvars_readLoop]; simp; tauto)]
      simp [hσ1, hσ0, lenEnv, initEnv, hz.1, hz.2.2.2]
    · intro b hb
      rw [fa2 b (by rw [warrs_readLoop]; simp [hb])]
      simp [hσ1, hσ0, lenEnv, initEnv]
  obtain ⟨σ3, r3, hout⟩ := (body_spec (B := Bd y) hB hyB).run hpost
  exact ⟨σ3, (r0.seq (r2.seq r3)).mono (by unfold KRaw; omega), hout⟩

/-! ### The cost, against the concept's bound -/

theorem varCount_le (F : Formula) : varCount F ≤ (lits F).length := by
  unfold varCount vars literals
  exact (List.toFinset_card_le _).trans (by rw [List.length_map]; rfl)

/-- The constant of the running time. -/
def c0 : ℕ := 8000

theorem KRaw_le (y : List ℕ) :
    10 * KRaw y + 2 ≤ c0 * (y.length + 1) * (Lax117284.TwoSatRunningTime.wordVarCount y + 1) := by
  unfold KRaw Kbody c0
  by_cases hacc : Accepted y
  · rw [if_pos hacc, wordVarCount_eq y hacc]
    set F := formulaOf y with hF
    obtain ⟨hk, hC, hmx⟩ := sizes_le hacc
    rw [← hF] at hk hC hmx
    have hE := length_edges_le F
    have hN : N F = 2 * mxOf (lits F) := rfl
    have hv := varCount_le F
    unfold Kacc Kloop Ks
    simp only [Bfs.Kbfs_eq]
    set v := varCount F with hvdef
    set L := y.length with hL
    have h1 : (2 * (40 * (N F + (edges F).length + 1)) + 40) * v ≤ (240 * L + 280) * v :=
      Nat.mul_le_mul_right v (by omega)
    have h2 : (240 * L + 280) * v = 240 * (L * v) + 280 * v := by ring
    have h3 : 8000 * (L + 1) * (v + 1) = 8000 * (L * v) + 8000 * L + 8000 * v + 8000 := by ring
    have h4 : L * v ≥ 0 := Nat.zero_le _
    have h5 : v ≤ L := by omega
    have h6 : v ≤ L * v + v := by omega
    rw [h3]
    omega
  · rw [if_neg hacc, wordVarCount_eq_zero y hacc]
    nlinarith

/-! ### The concept's statement -/

theorem fits (w : ℕ) (x : List ℕ) (h : c0 * (x.length + 1) ≤ 2 ^ w) :
    layout.FitsWords (Bd x) w := by
  refine fitsWords_of_max_le (by unfold Bd; omega) ?_
  simp only [Layout.span, layout, List.length_cons, List.length_nil, max_le_iff]
  unfold Bd; unfold c0 at h
  omega

/--
---
conclusion: Lax117284.TwoSatRunningTime.decides
---
The program reads the word, scans it with the verified scanner of `lax-391470`, checks the
width of every clause, builds the implication graph in compressed sparse row form by a counting
sort, and searches from both literals of every occurring variable; the searches are paid out of a
potential that charges a constant to every variable and two searches to every occurring one,
which gives the factor `v + 1`. The constant is `8000`.
-/
theorem decides : ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog
      {x | (∀ v ∈ x, v ≤ 1) ∧ c * (x.length + 1) ≤ 2 ^ w}
      (fun x => if Lax117284.TwoSatRunningTime.bitsOf x ∈ TwoSAT then [1] else [0])
      (fun x => c * (x.length + 1) * (Lax117284.TwoSatRunningTime.wordVarCount x + 1)) := by
  refine ⟨wrapProgram layout mainRaw, c0, fun w x ⟨hx1, hfit⟩ => ?_⟩
  obtain ⟨σ', ⟨k, hk, hbs⟩, hout⟩ := mainRaw_run x hx1
  obtain ⟨t, ht, hrun⟩ := wrap_runsTo (fits w x hfit) mainRaw_ok (by simp [layout])
    (fun v hv => by have := hx1 v hv; unfold Bd; omega) (by unfold Bd; omega) hbs
  refine ⟨t, ?_, ?_⟩
  · show t ≤ c0 * (x.length + 1) * (Lax117284.TwoSatRunningTime.wordVarCount x + 1)
    have := KRaw_le x
    simp only [Layout.const] at ht
    omega
  · rw [hout] at hrun
    have e : (if Lax117284.TwoSatRunningTime.bitsOf x ∈ TwoSAT then [1] else [0]) =
        [if Lax391470Proofs.Bits.bitsOf x ∈ TwoSAT then 1 else 0] := by
      rw [bitsOf_eq]; split <;> rfl
    show RunsTo w (wrapProgram layout mainRaw) x
      (if Lax117284.TwoSatRunningTime.bitsOf x ∈ TwoSAT then [1] else [0]) t
    rw [e]; exact hrun

end Lax117284Proofs.TwoSAT.Machine.Final

end

/-! ### `Lax117284Proofs.TwoSAT.Machine.FinalP` -/

section
/-!
2-SAT is in P: the program on the length-prefixed word is a polynomial-time word RAM
computation of the decision on the zeros and ones of the word, in the sense of `lax-759944`,
and `ToP.lean` carries that to the class.
-/

namespace Lax117284Proofs.TwoSAT.Machine.FinalP

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax429075.CNF Lax117284.TwoSatCNF Lax117284Proofs.TwoSAT.Machine.Scan Lax117284Proofs.TwoSAT.Machine.Main
open Lax117284Proofs.TwoSAT.Machine.Final Lax117284Proofs.TwoSAT.Machine.Language Lax117284Proofs.TwoSAT.Machine.ToP
open Lax391470Proofs.ReadAll Lax391470Proofs.Bits
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax391470Proofs.BitSize
open scoped Classical

/-- The largest entry of a word. -/
def Mx (y : List ℕ) : ℕ := y.foldr max 0

lemma le_Mx {y : List ℕ} {v : ℕ} (hv : v ∈ y) : v ≤ Mx y := by
  induction y with
  | nil => cases hv
  | cons a t ih =>
    simp only [Mx, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp hv with rfl | h
    · omega
    · have := ih h; omega

lemma Mx_mem_or_zero (y : List ℕ) : Mx y ∈ y ∨ Mx y = 0 := by
  induction y with
  | nil => right; rfl
  | cons a t ih =>
    simp only [Mx, List.foldr_cons] at ih ⊢
    rcases Nat.le_total a (List.foldr max 0 t) with h | h
    · rw [Nat.max_eq_right h]
      rcases ih with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · right; exact h'
    · rw [Nat.max_eq_left h]; exact Or.inl List.mem_cons_self

/-- The value bound on an arbitrary word. -/
def Bd2 (y : List ℕ) : ℕ := 5 * y.length + 25 + Mx y

/-- The cost of the program on the length-prefixed word. -/
noncomputable def KPre (y : List ℕ) : ℕ := (12 * y.length + 10) + Kbody y

lemma wvars_readAll : readAll.wvars = ["L", "rt", "rv", "rt"] := by
  simp [readAll, readLoop, readBody, Com.wvars]
lemma warrs_readAll : readAll.warrs = ["a"] := by
  simp [readAll, readLoop, readBody, Com.warrs]

/-- **The program on the length-prefixed word.** -/
theorem mainPre_run (y : List ℕ) :
    ∃ σ', Run (Bd2 y) mainPre (initEnv (ext y) (y.length :: y)) σ' (KPre y) ∧
      σ'.out = decBits y := by
  have hB : 5 * y.length + 24 < Bd2 y := by unfold Bd2; omega
  have hyB : ∀ v ∈ y, v < Bd2 y := fun v hv => by have := le_Mx hv; unfold Bd2; omega
  set σ0 := initEnv (ext y) (y.length :: y) with hσ0
  obtain ⟨σ1, r1, ⟨hL1, ha1, hout1, -⟩, fv1, fa1, -, -⟩ :=
    (readAll_spec (B := Bd2 y) (y := y) hyB (by unfold Bd2; omega)).frame.run (σ := σ0)
      ⟨rfl, rfl, by simp [hσ0, initEnv, ext]⟩
  have hpost : ReadPost y (ext y) σ1 := by
    refine ⟨hL1, ha1, hout1, ?_, ?_⟩
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      rw [fv1 z (by rw [wvars_readAll]; simp; tauto)]
      rfl
    · intro b hb
      rw [fa1 b (by rw [warrs_readAll]; simp [hb])]
      rfl
  obtain ⟨σ2, r2, hout⟩ := (body_spec (B := Bd2 y) hB hyB).run hpost
  refine ⟨σ2, (r1.seq r2).mono (by unfold KPre; omega), ?_⟩
  rw [hout, decBits_eq]
  split <;> rfl

/-! ### The machine program -/

/-- The physical inputs: a word preceded by its length. -/
def Shape : Set (List ℕ) := {y | y ≠ [] ∧ y.headD 0 = y.tail.length}

lemma shape_eq {y : List ℕ} (h : y ∈ Shape) : y = y.tail.length :: y.tail := by
  obtain ⟨hne, hh⟩ := h
  rcases y with _ | ⟨a, t⟩
  · exact absurd rfl hne
  · simp only [List.headD_cons, List.tail_cons] at hh ⊢
    rw [hh]

theorem solves : Solves layout mainPre Shape (fun x => decBits x.tail)
    (fun x => Bd2 x.tail) (fun x => KPre x.tail) where
  ok := mainPre_ok
  inp := by
    intro x hx v hv
    rw [shape_eq hx] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · unfold Bd2; omega
    · have := le_Mx hv'; unfold Bd2; omega
  run := by
    intro x hx
    obtain ⟨σ', hrun, hout⟩ := mainPre_run x.tail
    rw [← shape_eq hx] at hrun
    exact ⟨_, σ', hrun, hout⟩

def prog : Program := compileProgram layout mainPre

theorem prog_runs (w : ℕ) (x : List ℕ) (hfit : 56 + 12 * Bd2 x ≤ 2 ^ w) :
    ∃ t ≤ 10 * KPre x + 1, RunsTo w prog (x.length :: x) (decBits x) t := by
  have hs : Solves layout mainPre {z | z = x.length :: x} (fun z => decBits z.tail)
      (fun z => Bd2 z.tail) (fun z => KPre z.tail) :=
    ⟨solves.ok, fun z hz => solves.inp z (by rw [hz]; exact ⟨by simp, by simp⟩),
      fun z hz => solves.run z (by rw [hz]; exact ⟨by simp, by simp⟩)⟩
  have h := computesInTime_of_solves (w := w) (T := fun z => 10 * KPre z.tail + 1) hs
    (fun z hz => by
      rw [hz]; simp only [List.tail_cons]
      refine fitsWords_of_max_le (by unfold Bd2; omega) ?_
      simp only [Layout.span, layout, List.length_cons, List.length_nil, max_le_iff]
      omega)
    (fun z hz => by simp [Layout.const])
  obtain ⟨t, ht, hrun⟩ := h (x.length :: x) rfl
  exact ⟨t, by simpa using ht, by simpa [prog] using hrun⟩

/-! ### Fitting into a word, and the polynomial -/

/-- The constant of the fitting condition. -/
def cfit : ℕ := 900

lemma fit_of (w : ℕ) (x : List ℕ)
    (h : ∀ v ∈ (x.length :: x), cfit * ((x.length + 1) + v + 1) ^ 2 ≤ 2 ^ w) :
    56 + 12 * Bd2 x ≤ 2 ^ w := by
  obtain ⟨v, hv, hT⟩ : ∃ v ∈ (x.length :: x), x.length + Mx x + 2 ≤ (x.length + 1) + v + 1 := by
    rcases Mx_mem_or_zero x with hm | hm
    · exact ⟨Mx x, List.mem_cons_of_mem _ hm, by omega⟩
    · exact ⟨x.length, List.mem_cons_self, by omega⟩
  have hpow := Nat.pow_le_pow_left hT 2
  have hc := Nat.mul_le_mul_left cfit hpow
  refine le_trans ?_ (le_trans hc (h v hv))
  set T := x.length + Mx x + 2 with hTdef
  have hTT : T ≤ T * T := Nat.le_mul_of_pos_left _ (by omega)
  have e : cfit * T ^ 2 = 900 * (T * T) := by unfold cfit; ring
  rw [e]
  unfold Bd2
  omega

/-- The scale of the time bound. -/
def sc : ℕ := 8000

lemma KPre_le (x : List ℕ) : 10 * KPre x + 1 ≤ sc * (bitSize x + 1) ^ 2 := by
  have hlen := length_le_bitSize x
  have h1 := KRaw_le x
  have hv : Lax117284.TwoSatRunningTime.wordVarCount x ≤ x.length := by
    unfold Lax117284.TwoSatRunningTime.wordVarCount
    rw [bitsOf_eq, Lax391470Proofs.CnfScan.decodeCNF_eq]
    split
    · next h =>
      have := varCount_le (formulaOf x)
      have := (sizes_le (y := x) h).1
      show varCount (formulaOf x) ≤ x.length
      omega
    · simp
  have hK : KPre x ≤ KRaw x := by unfold KPre KRaw; omega
  have h2 : c0 * (x.length + 1) * (Lax117284.TwoSatRunningTime.wordVarCount x + 1) ≤
      c0 * (bitSize x + 1) * (bitSize x + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e : sc * (bitSize x + 1) ^ 2 = c0 * (bitSize x + 1) * (bitSize x + 1) := by
    unfold sc c0; ring
  rw [e]
  calc 10 * KPre x + 1 ≤ 10 * KRaw x + 2 := by omega
    _ ≤ c0 * (x.length + 1) * (Lax117284.TwoSatRunningTime.wordVarCount x + 1) := h1
    _ ≤ c0 * (bitSize x + 1) * (bitSize x + 1) := h2

/-- **The decision is a polynomial-time word RAM computation on the bits.** -/
theorem ramPolytime_decBits : RamPolytime decBits := by
  have hK : cfit * 4 ^ 2 ≤ 2 ^ (16 * cfit).size := by
    have := Nat.lt_size_self (16 * cfit)
    omega
  refine Lax391470Proofs.RamBridge.ramPolytime_of_poly (c := cfit) (d := 2)
    (K := (16 * cfit).size) (prog := prog)
    (Polynomial.C sc * (Polynomial.X + Polynomial.C 1) ^ 2)
    (by omega) hK ?_ ?_
  · intro x v hv
    have h1 : v ≤ 1 := by
      rw [decBits_eq] at hv
      split at hv <;> simp at hv <;> omega
    have h2 : 2 ≤ 2 ^ (2 * bitSize x + (16 * cfit).size) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by omega)
        (show 1 ≤ 2 * bitSize x + (16 * cfit).size by
          have : 0 < 16 * cfit := by unfold cfit; omega
          have := Nat.size_pos.mpr this
          omega))
    omega
  · intro w x hfits
    obtain ⟨t, ht, hrun⟩ := prog_runs w x (fit_of w x hfits)
    refine ⟨t, ?_, hrun⟩
    have := KPre_le x
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    omega

/--
---
conclusion: Lax117284.TwoSatInP.twoSAT_mem_P
---
The program on the length-prefixed word is a polynomial-time word RAM computation of the
decision on the zeros and ones of the word, with all values polynomially bounded; the RAM/Turing
equivalence of `lax-759944` and the two translations of `lax-391470` give a polynomial-time Turing
machine on the binary word, and a machine writing the one bit of the answer is a machine for the
class.
-/
theorem twoSAT_mem_P : TwoSAT ∈ Lax434930.PolynomialTime.P :=
  mem_P_of_ram ramPolytime_decBits

end Lax117284Proofs.TwoSAT.Machine.FinalP

end
