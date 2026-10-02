import Lax117284Proofs.TwoSAT.Machine.Model
import Lax808846Proofs.Lib.Basic

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
  | zero => rfl
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
