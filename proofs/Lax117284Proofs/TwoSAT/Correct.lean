import Lax117284.TwoSatCorrectness
import Lax117284Proofs.TwoSAT.Bridge

/-!
Correctness of the algorithm `Lax117284.TwoSatAlgorithm.decide`.

The width check accepts exactly the 2-CNF formulas without an empty clause (`widthOk_iff`). The
search from a node computes exactly the literals reachable from it (`mem_reachable_iff`): every
literal the iterates collect is reachable, the iterates form a chain inside the finite set of
nodes and so are stationary after as many rounds as there are nodes, and a set closed under
expansion contains everything reachable from its members, since every edge from any literal
ends in a node. A variable that does not occur has no edge at either of its literals and so is
never contradictory (`not_contradictory_of_not_mem_vars`). Together with the criterion
`Bridge.satisfiable_iff` this gives `decide_iff`.
-/

namespace Lax117284Proofs.TwoSAT.Correct

open Lax429075.CNF Lax117284.TwoSatCNF Lax117284.TwoSatImplicationGraph Lax117284.TwoSatAlgorithm

/-! ### The width check -/

theorem widthOk_iff (F : Formula) : widthOk F = true ↔ IsTwoCNF F ∧ [] ∉ F := by
  unfold widthOk IsTwoCNF
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨fun C hC => (h C hC).2, fun hnil => ?_⟩
    have := (h [] hnil).1
    simp at this
  · rintro ⟨h2, h0⟩ C hC
    refine ⟨?_, h2 C hC⟩
    have : C ≠ [] := fun h => h0 (h ▸ hC)
    have := List.length_pos_of_ne_nil this
    omega

/-! ### Variables and nodes -/

theorem mem_vars {F : Formula} {x : ℕ} : x ∈ vars F ↔ ∃ l ∈ literals F, l.index = x := by
  simp [vars]

theorem mem_dedup_iff {F : Formula} {x : ℕ} :
    x ∈ ((literals F).map Literal.index).dedup ↔ x ∈ vars F := by
  simp [vars]

theorem mem_literals_of_mem {F : Formula} {C : Clause} {l : Literal} (hC : C ∈ F) (hl : l ∈ C) :
    l ∈ literals F := by
  simp only [literals, List.mem_flatMap, id]
  exact ⟨C, hC, hl⟩

theorem lt_foldr (L : List Literal) :
    ∀ l ∈ L, l.index < L.foldr (fun l n => max (l.index + 1) n) 0 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    intro l hl
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hl with rfl | hl
    · omega
    · have := ih l hl
      omega

theorem index_lt_indexBound {F : Formula} {l : Literal} (hl : l ∈ literals F) :
    l.index < indexBound F := lt_foldr _ l hl

theorem vars_lt {F : Formula} {x : ℕ} (hx : x ∈ vars F) : x < indexBound F := by
  obtain ⟨l, hl, rfl⟩ := mem_vars.1 hx
  exact index_lt_indexBound hl

theorem mem_nodes {F : Formula} {l : Literal} : l ∈ nodes F ↔ l.index < indexBound F := by
  unfold nodes
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true,
    Prod.exists]
  constructor
  · rintro ⟨i, p, hi, rfl⟩
    exact hi
  · intro h
    exact ⟨l.index, l.positive, h, rfl⟩

theorem pos_mem_nodes {F : Formula} {x : ℕ} (hx : x ∈ vars F) : pos x ∈ nodes F :=
  mem_nodes.2 (vars_lt hx)

theorem neg_mem_nodes {F : Formula} {x : ℕ} (hx : x ∈ vars F) : neg x ∈ nodes F :=
  mem_nodes.2 (vars_lt hx)

/-! ### Edges stay among the occurring variables -/

theorem implies_mem_clause {F : Formula} {a b : Literal} (h : Implies F a b) :
    ∃ C ∈ F, negate a ∈ C ∧ b ∈ C := by
  obtain ⟨C, hC, h | h | h⟩ := h
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, hC, by simp [Bridge.negate_negate], by simp⟩
  · subst h
    exact ⟨_, hC, by simp, by simp⟩
  · subst h
    exact ⟨_, hC, by simp, by simp⟩

theorem implies_mem_vars {F : Formula} {a b : Literal} (h : Implies F a b) :
    a.index ∈ vars F ∧ b.index ∈ vars F := by
  obtain ⟨C, hC, ha, hb⟩ := implies_mem_clause h
  exact ⟨mem_vars.2 ⟨negate a, mem_literals_of_mem hC ha, rfl⟩,
    mem_vars.2 ⟨b, mem_literals_of_mem hC hb, rfl⟩⟩

theorem implies_lt {F : Formula} {a b : Literal} (h : Implies F a b) :
    a.index < indexBound F ∧ b.index < indexBound F :=
  ⟨vars_lt (implies_mem_vars h).1, vars_lt (implies_mem_vars h).2⟩

theorem mem_successors {F : Formula} {a b : Literal} :
    b ∈ successors F a ↔ b ∈ nodes F ∧ Implies F a b := by
  unfold successors
  exact Finset.mem_filter

theorem mem_expand {F : Formula} {S : Finset Literal} {b : Literal} :
    b ∈ expand F S ↔ b ∈ S ∨ ∃ a ∈ S, b ∈ successors F a := by
  unfold expand
  simp [Finset.mem_union, Finset.mem_biUnion]

/-! ### The iterates of the search -/

/-- The set after `k` rounds of expansion from `s`. -/
def iter (F : Formula) (s : Literal) (k : ℕ) : Finset Literal := (expand F)^[k] {s}

theorem iter_zero (F : Formula) (s : Literal) : iter F s 0 = {s} := rfl

theorem iter_succ (F : Formula) (s : Literal) (k : ℕ) :
    iter F s (k + 1) = expand F (iter F s k) := Function.iterate_succ_apply' _ _ _

theorem reachable_eq_iter (F : Formula) (s : Literal) :
    reachable F s = iter F s (nodes F).card := rfl

theorem subset_expand (F : Formula) (S : Finset Literal) : S ⊆ expand F S :=
  Finset.subset_union_left

theorem iter_subset_succ (F : Formula) (s : Literal) (k : ℕ) : iter F s k ⊆ iter F s (k + 1) := by
  rw [iter_succ]
  exact subset_expand F _

theorem mem_iter_self (F : Formula) (s : Literal) : ∀ k, s ∈ iter F s k := by
  intro k
  induction k with
  | zero => simp [iter_zero]
  | succ k ih => exact iter_subset_succ F s k ih

theorem expand_subset_nodes {F : Formula} {S : Finset Literal} (hS : S ⊆ nodes F) :
    expand F S ⊆ nodes F := by
  unfold expand
  refine Finset.union_subset hS (Finset.biUnion_subset.2 fun a _ => ?_)
  unfold successors
  exact Finset.filter_subset _ _

theorem iter_subset_nodes {F : Formula} {s : Literal} (hs : s ∈ nodes F) :
    ∀ k, iter F s k ⊆ nodes F := by
  intro k
  induction k with
  | zero =>
    rw [iter_zero]
    exact Finset.singleton_subset_iff.2 hs
  | succ k ih =>
    rw [iter_succ]
    exact expand_subset_nodes ih

theorem reaches_of_mem_iter {F : Formula} {s : Literal} :
    ∀ k, ∀ b ∈ iter F s k, Reaches F s b := by
  intro k
  induction k with
  | zero =>
    intro b hb
    rw [iter_zero, Finset.mem_singleton] at hb
    rw [hb]
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro b hb
    rw [iter_succ, mem_expand] at hb
    rcases hb with hb | ⟨a, ha, hab⟩
    · exact ih b hb
    · exact (ih a ha).tail (mem_successors.1 hab).2

/-- A fixed point of expansion stays fixed. -/
theorem iter_stable {F : Formula} {s : Literal} {k : ℕ} (h : iter F s k = iter F s (k + 1)) :
    ∀ d, iter F s (k + d) = iter F s k := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc, iter_succ, ih, ← iter_succ, ← h]

/-- Until the chain becomes stationary, the `k`-th iterate has more than `k` elements. -/
theorem iter_card (F : Formula) (s : Literal) :
    ∀ k, (∃ j < k, iter F s j = iter F s (j + 1)) ∨ k + 1 ≤ (iter F s k).card := by
  intro k
  induction k with
  | zero =>
    right
    simp [iter_zero]
  | succ k ih =>
    rcases ih with ⟨j, hj, hfix⟩ | hcard
    · exact Or.inl ⟨j, by omega, hfix⟩
    · by_cases hfix : iter F s k = iter F s (k + 1)
      · exact Or.inl ⟨k, by omega, hfix⟩
      · right
        have hlt : (iter F s k).card < (iter F s (k + 1)).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨iter_subset_succ F s k, hfix⟩)
        omega

/-- After as many rounds as there are nodes, the search is stationary. -/
theorem expand_reachable {F : Formula} {s : Literal} (hs : s ∈ nodes F) :
    expand F (reachable F s) = reachable F s := by
  rw [reachable_eq_iter, ← iter_succ]
  set N := (nodes F).card with hN
  rcases iter_card F s (N + 1) with ⟨j, hj, hfix⟩ | hcard
  · have h1 := iter_stable hfix (N - j)
    have h2 := iter_stable hfix (N + 1 - j)
    have e1 : j + (N - j) = N := by omega
    have e2 : j + (N + 1 - j) = N + 1 := by omega
    rw [e1] at h1
    rw [e2] at h2
    rw [h1, h2]
  · have := Finset.card_le_card (iter_subset_nodes hs (N + 1))
    omega

/-- A set closed under expansion contains everything reachable from its members. -/
theorem mem_of_reaches {F : Formula} {S : Finset Literal} (hfix : expand F S = S) {s b : Literal}
    (hs : s ∈ S) (h : Reaches F s b) : b ∈ S := by
  induction h with
  | refl => exact hs
  | tail _ hab ih =>
    have : _ ∈ expand F S :=
      mem_expand.2 (Or.inr ⟨_, ih, mem_successors.2 ⟨mem_nodes.2 (implies_lt hab).2, hab⟩⟩)
    rwa [hfix] at this

/-- **The search computes reachability.** -/
theorem mem_reachable_iff {F : Formula} {s : Literal} (hs : s ∈ nodes F) (b : Literal) :
    b ∈ reachable F s ↔ Reaches F s b := by
  constructor
  · intro hb
    exact reaches_of_mem_iter _ b hb
  · intro h
    exact mem_of_reaches (expand_reachable hs) (mem_iter_self F s _) h

/-! ### Variables that do not occur -/

theorem pos_ne_neg (x : ℕ) : pos x ≠ neg x := by
  simp [pos, neg]

/-- A variable that does not occur has no edge at its positive literal, so is not
contradictory. -/
theorem not_contradictory_of_not_mem_vars {F : Formula} {x : ℕ} (hx : x ∉ vars F) :
    ¬ Contradictory F x := by
  rintro ⟨h1, _⟩
  rcases Relation.ReflTransGen.cases_head h1 with h | ⟨c, hc, _⟩
  · exact pos_ne_neg x h
  · exact hx (implies_mem_vars hc).1

/-- On an occurring variable the Boolean test is the notion. -/
theorem contradictory_eq {F : Formula} {x : ℕ} (hx : x ∈ vars F) :
    contradictory F x = true ↔ Contradictory F x := by
  unfold contradictory Contradictory
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [mem_reachable_iff (pos_mem_nodes hx), mem_reachable_iff (neg_mem_nodes hx)]

/-! ### Correctness -/

/--
---
conclusion: Lax117284.TwoSatCorrectness.decide_iff
---
The width check accepts exactly the 2-CNF formulas without an empty clause; for an occurring
variable the search computes reachability in the implication graph, since the iterates are a
chain in the finite set of nodes and every edge ends in a node; a variable that does not occur
is never contradictory. The criterion `Bridge.satisfiable_iff` finishes the proof.
-/
theorem decide_iff (F : Formula) : decide F = true ↔ IsTwoCNF F ∧ Satisfiable F := by
  unfold Lax117284.TwoSatAlgorithm.decide
  rw [Bool.and_eq_true, widthOk_iff, List.all_eq_true]
  constructor
  · rintro ⟨⟨h2, h0⟩, hall⟩
    refine ⟨h2, (Bridge.satisfiable_iff F h2).2 ⟨h0, fun x => ?_⟩⟩
    by_cases hx : x ∈ vars F
    · have := hall x (mem_dedup_iff.2 hx)
      rw [Bool.not_eq_eq_eq_not, Bool.not_true] at this
      rw [← contradictory_eq hx, this]
      exact Bool.false_ne_true
    · exact not_contradictory_of_not_mem_vars hx
  · rintro ⟨h2, hsat⟩
    obtain ⟨h0, hx⟩ := (Bridge.satisfiable_iff F h2).1 hsat
    refine ⟨⟨h2, h0⟩, fun x hxd => ?_⟩
    have hxv := mem_dedup_iff.1 hxd
    have hnot : ¬ contradictory F x = true := fun hc => hx x ((contradictory_eq hxv).1 hc)
    rw [Bool.not_eq_eq_eq_not, Bool.not_true]
    exact Bool.eq_false_iff.2 hnot

end Lax117284Proofs.TwoSAT.Correct
