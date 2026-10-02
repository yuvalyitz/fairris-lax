import Lax117284.TwoSatCriterion
import Lax117284Proofs.TwoSAT.Math.Criterion
import Mathlib.Data.Finset.Lattice.Fold

/-!
The bridge between the formulas of `lax-429075` and the occurrence functions of
`Lax117284Proofs.TwoSAT.Math`, and the criterion of Aspvall, Plass and Tarjan for those formulas.

A 2-CNF formula `F` without an empty clause is read as `m = F.length` clauses given by two
functions on the occurrences `0, …, 2m-1`: the occurrence `2c + α` is the literal `α` of the
clause `c`; a unit clause `[a]` supplies `a` for both `α = 0` and `α = 1`, so that its two edges
coincide. Outside `[0, 2m)` the occurrence is the dummy literal `⟨0, false⟩`, with variable `0`
and sign `0`.

Under this reading satisfiability is `Sat2` (`satisfiable_iff_sat2`), the edges of the
implication graph are the edges `Edge` on the codes `2x + s` of the literals
(`implies_iff_edge`), and a contradictory variable is `Contra` (`contradictory_iff_contra`). The
criterion `satisfiable_iff` then follows from `Math.sat2_iff_no_contra`.
-/

namespace Lax117284Proofs.TwoSAT.Bridge

open Lax429075.CNF Lax117284.TwoSatCNF Lax117284.TwoSatImplicationGraph Lax117284Proofs.TwoSAT.Math

/-! ### The occurrence functions -/

/-- The literal `α` of a clause of one or two literals; a unit clause supplies its literal for
both `α`, and any other clause supplies the dummy `⟨0, false⟩`. -/
def clauseLit (C : Clause) (α : ℕ) : Literal :=
  match C with
  | [a] => a
  | [a, b] => if α = 0 then a else b
  | _ => ⟨0, false⟩

/-- The literal at occurrence `i`: literal `i % 2` of clause `i / 2`. -/
def litAt (F : Formula) (i : ℕ) : Literal := clauseLit (F.getD (i / 2) []) (i % 2)

/-- The variable of occurrence `i`. -/
def xsOf (F : Formula) (i : ℕ) : ℕ := (litAt F i).index

/-- The sign of occurrence `i`: `1` for a positive literal, `0` for a negative one. -/
def ssOf (F : Formula) (i : ℕ) : ℕ := if (litAt F i).positive then 1 else 0

theorem ssOf_le (F : Formula) : ∀ i < 2 * F.length, ssOf F i ≤ 1 := by
  intro i _
  unfold ssOf
  split <;> omega



theorem litAt_even (F : Formula) (c : ℕ) : litAt F (2 * c) = clauseLit (F.getD c []) 0 := by
  have h1 : 2 * c / 2 = c := by omega
  have h2 : 2 * c % 2 = 0 := by omega
  simp only [litAt, h1, h2]

theorem litAt_odd (F : Formula) (c : ℕ) :
    litAt F (2 * c + 1) = clauseLit (F.getD c []) 1 := by
  have h1 : (2 * c + 1) / 2 = c := by omega
  have h2 : (2 * c + 1) % 2 = 1 := by omega
  simp only [litAt, h1, h2]

/-! ### Clauses by position -/

theorem getD_mem {F : Formula} {c : ℕ} (hc : c < F.length) : F.getD c [] ∈ F := by
  simp [List.getD_eq_getElem?_getD, hc]

theorem forall_mem_iff (F : Formula) (P : Clause → Prop) :
    (∀ C ∈ F, P C) ↔ ∀ c < F.length, P (F.getD c []) := by
  constructor
  · intro h c hc
    exact h _ (getD_mem hc)
  · intro h C hC
    obtain ⟨c, hc, rfl⟩ := List.mem_iff_getElem.1 hC
    have := h c hc
    simpa [List.getD_eq_getElem?_getD, hc] using this

theorem exists_mem_iff (F : Formula) (P : Clause → Prop) :
    (∃ C ∈ F, P C) ↔ ∃ c < F.length, P (F.getD c []) := by
  constructor
  · rintro ⟨C, hC, hP⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_iff_getElem.1 hC
    refine ⟨c, hc, ?_⟩
    simpa [List.getD_eq_getElem?_getD, hc] using hP
  · rintro ⟨c, hc, hP⟩
    exact ⟨_, getD_mem hc, hP⟩

theorem getD_ne_nil {F : Formula} (h0 : [] ∉ F) {c : ℕ} (hc : c < F.length) :
    F.getD c [] ≠ [] := fun h => h0 (h ▸ getD_mem hc)

/-! ### Satisfiability -/

theorem literal_eval_iff (l : Literal) (ρ : ℕ → Bool) :
    l.eval ρ = true ↔ ρ l.index = l.positive := by
  unfold Literal.eval
  cases l.positive <;> simp

theorem holds_iff (F : Formula) (ρ : ℕ → Bool) (i : ℕ) :
    Holds ρ (xsOf F) (ssOf F) i ↔ (litAt F i).eval ρ = true := by
  rw [literal_eval_iff]
  unfold Holds xsOf ssOf
  cases (litAt F i).positive <;> simp

theorem clause_sat (C : Clause) (hlen : C.length ≤ 2) (hne : C ≠ []) (ρ : ℕ → Bool) :
    (∃ l ∈ C, l.eval ρ = true) ↔
      (clauseLit C 0).eval ρ = true ∨ (clauseLit C 1).eval ρ = true := by
  match C with
  | [] => exact absurd rfl hne
  | [u] => simp [clauseLit]
  | [u, v] => simp [clauseLit]
  | _ :: _ :: _ :: _ => simp at hlen

theorem eval_eq_true_iff (F : Formula) (ρ : ℕ → Bool) :
    eval F ρ = true ↔ ∀ C ∈ F, ∃ l ∈ C, l.eval ρ = true := by
  simp [eval, List.all_eq_true, List.any_eq_true]

/-- A formula with an empty clause is not satisfiable. -/
theorem not_mem_nil_of_satisfiable {F : Formula} (h : Satisfiable F) : [] ∉ F := by
  obtain ⟨ρ, hρ⟩ := h
  intro hmem
  have := (eval_eq_true_iff F ρ).1 hρ [] hmem
  simp at this

/-- **Satisfiability is `Sat2`.** -/
theorem satisfiable_iff_sat2 {F : Formula} (h2 : IsTwoCNF F) (h0 : [] ∉ F) :
    Satisfiable F ↔ Sat2 F.length (xsOf F) (ssOf F) := by
  unfold Satisfiable Sat2
  apply exists_congr
  intro ρ
  rw [eval_eq_true_iff, forall_mem_iff]
  unfold SatBy
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro hc
  rw [holds_iff, holds_iff, litAt_even, litAt_odd]
  exact clause_sat _ (h2 _ (getD_mem hc)) (getD_ne_nil h0 hc) ρ

/-! ### Literals as nodes -/

/-- The node of a literal: `2x + 1` for the variable `x`, `2x` for its negation. -/
def code (l : Literal) : ℕ := node l.index (if l.positive then 1 else 0)

/-- The literal of a node. -/
def decode (n : ℕ) : Literal := ⟨n / 2, decide (n % 2 = 1)⟩

theorem code_decode (n : ℕ) : code (decode n) = n := by
  unfold code decode node
  by_cases h : n % 2 = 1
  · simp only [h, decide_true, if_true]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    omega

theorem decode_code (l : Literal) : decode (code l) = l := by
  obtain ⟨i, p⟩ := l
  cases p
  · simp [code, decode, node]
  · simp [code, decode, node]
    omega

theorem code_inj {a b : Literal} : code a = code b ↔ a = b := by
  constructor
  · intro h
    rw [← decode_code a, ← decode_code b, h]
  · rintro rfl
    rfl

theorem negate_negate (l : Literal) : negate (negate l) = l := by
  simp [negate]

theorem code_pos (x : ℕ) : code (pos x) = node x 1 := by
  simp [code, pos]

theorem code_neg (x : ℕ) : code (neg x) = node x 0 := by
  simp [code, neg]

theorem node_xs_ss (F : Formula) (i : ℕ) : node (xsOf F i) (ssOf F i) = code (litAt F i) := rfl

theorem node_xs_neg (F : Formula) (i : ℕ) :
    node (xsOf F i) (1 - ssOf F i) = code (negate (litAt F i)) := by
  unfold xsOf ssOf code negate
  cases (litAt F i).positive <;> simp

/-! ### Edges -/

theorem clause_implies (C : Clause) (hlen : C.length ≤ 2) (hne : C ≠ []) (a b : Literal) :
    ((C = [b] ∧ a = negate b) ∨ C = [negate a, b] ∨ C = [b, negate a]) ↔
      ((a = negate (clauseLit C 0) ∧ b = clauseLit C 1) ∨
        (a = negate (clauseLit C 1) ∧ b = clauseLit C 0)) := by
  match C with
  | [] => exact absurd rfl hne
  | [u] =>
    simp only [clauseLit, List.cons.injEq, reduceCtorEq, and_true, and_false, or_false, or_self]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | [u, v] =>
    simp only [clauseLit, List.cons.injEq, reduceCtorEq, and_true, and_false, false_and,
      false_or, if_true, one_ne_zero, if_false]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact Or.inl ⟨(negate_negate a).symm, rfl⟩
      · exact Or.inr ⟨(negate_negate a).symm, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact Or.inl ⟨(negate_negate u).symm, rfl⟩
      · exact Or.inr ⟨rfl, (negate_negate v).symm⟩
  | _ :: _ :: _ :: _ => simp at hlen

theorem implies_iff' {F : Formula} (h2 : IsTwoCNF F) (h0 : [] ∉ F) (a b : Literal) :
    Implies F a b ↔ ∃ c < F.length,
      (a = negate (litAt F (2 * c)) ∧ b = litAt F (2 * c + 1)) ∨
        (a = negate (litAt F (2 * c + 1)) ∧ b = litAt F (2 * c)) := by
  unfold Implies
  rw [exists_mem_iff]
  apply exists_congr
  intro c
  apply and_congr_right
  intro hc
  rw [clause_implies _ (h2 _ (getD_mem hc)) (getD_ne_nil h0 hc), litAt_even, litAt_odd]

/-- **Edges are `Edge`.** -/
theorem implies_iff_edge {F : Formula} (h2 : IsTwoCNF F) (h0 : [] ∉ F) (a b : Literal) :
    Implies F a b ↔ Edge F.length (xsOf F) (ssOf F) (code a) (code b) := by
  rw [implies_iff' h2 h0]
  unfold Edge
  apply exists_congr
  intro c
  apply and_congr_right
  intro _
  rw [node_xs_ss, node_xs_ss, node_xs_neg, node_xs_neg, code_inj, code_inj, code_inj, code_inj]

/-! ### Paths -/

theorem transGen_iff {F : Formula} (h2 : IsTwoCNF F) (h0 : [] ∉ F) (a b : Literal) :
    Relation.TransGen (Implies F) a b ↔ Reach F.length (xsOf F) (ssOf F) (code a) (code b) := by
  constructor
  · intro h
    exact Relation.TransGen.lift code
      (by intro u v huv; exact (implies_iff_edge h2 h0 u v).1 huv) _ _ h
  · intro h
    have := Relation.TransGen.lift decode (r := Edge F.length (xsOf F) (ssOf F))
      (p := Implies F) (by
        intro u v huv
        exact (implies_iff_edge h2 h0 (decode u) (decode v)).2
          (by rwa [code_decode, code_decode])) _ _ h
    have this' : Relation.TransGen (Implies F) (decode (code a)) (decode (code b)) := this
    rwa [decode_code, decode_code] at this'

/-- **Contradictory variables are `Contra`.** -/
theorem contradictory_iff_contra {F : Formula} (h2 : IsTwoCNF F) (h0 : [] ∉ F) (x : ℕ) :
    Contradictory F x ↔ Contra F.length (xsOf F) (ssOf F) x := by
  unfold Contradictory Contra Reaches
  have hne : neg x ≠ pos x := by simp [neg, pos]
  rw [Relation.reflTransGen_iff_eq_or_transGen, Relation.reflTransGen_iff_eq_or_transGen]
  simp only [hne, hne.symm, false_or]
  rw [transGen_iff h2 h0, transGen_iff h2 h0, code_pos, code_neg]

/-! ### The criterion -/

/-- A bound on the variables of the occurrences. -/
def bound (F : Formula) : ℕ := (Finset.range (2 * F.length)).sup (xsOf F) + 1

theorem xsOf_lt_bound (F : Formula) : ∀ i < 2 * F.length, xsOf F i < bound F := by
  intro i hi
  have := Finset.le_sup (f := xsOf F) (Finset.mem_range.2 hi)
  unfold bound
  omega

/--
---
conclusion: Lax117284.TwoSatCriterion.satisfiable_iff
---
The formula is read as occurrence functions, under which satisfiability is `Sat2`, edges are
`Edge` and contradictory variables are `Contra`; the criterion is then `Math.sat2_iff_no_contra`,
with the direction from a satisfying assignment holding for every variable by
`Math.not_contra_of_sat`. A formula with an empty clause is unsatisfiable outright.
-/
theorem satisfiable_iff (F : Formula) (h : IsTwoCNF F) :
    Satisfiable F ↔ [] ∉ F ∧ ∀ x : ℕ, ¬ Contradictory F x := by
  constructor
  · intro hsat
    have h0 : [] ∉ F := not_mem_nil_of_satisfiable hsat
    refine ⟨h0, fun x => ?_⟩
    rw [contradictory_iff_contra h h0]
    obtain ⟨A, hA⟩ := (satisfiable_iff_sat2 h h0).1 hsat
    exact not_contra_of_sat hA (ssOf_le F) x
  · rintro ⟨h0, hx⟩
    rw [satisfiable_iff_sat2 h h0,
      sat2_iff_no_contra (bound F) _ _ _ (xsOf_lt_bound F) (ssOf_le F)]
    intro x _
    rw [← contradictory_iff_contra h h0]
    exact hx x

end Lax117284Proofs.TwoSAT.Bridge
