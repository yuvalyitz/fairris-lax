import Lax117284.Problems

/-!
---
title: Satisfiability of Bounded Occurrence
type: definition
---
A *[2,3]-bounded 3-SAT formula* is a conjunction of clauses of two and of three literals in
which every literal occurs at most twice — so every variable occurs at most twice
positively and at most twice negatively, and hence in at most four clauses. Deciding
whether such a formula is satisfiable is NP-hard.

# Formalization Notes

The two widths are separate families of clauses rather than one family with a width
condition, because the construction that consumes such a formula treats the two widths
differently: the clauses of three literals receive a gadget of their own.

The language contains only formulas with at most as many variables as positions. A formula
in which every variable occurs is of this kind, so nothing is excluded that a formula of the
paper is; but the number of variables is written in binary, so a word may name exponentially
many variables without mentioning any, and a reduction that writes a client for each of them
could not run in polynomial time.

The occurrence bound is a condition on the formula and not extra data: an *occurrence* is a
position inside a clause, and every literal is required to occupy at most two of them. A
reduction that needs to distinguish the two occurrences of a literal obtains a numbering of
them from this bound.
-/

namespace Lax117284.BoundedSat

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

/-- A **[2,3]-bounded 3-SAT formula** over `vars` variables: `twoClauses` clauses of two
literals and `threeClauses` clauses of three literals, in which every literal — a variable
together with a sign — occupies at most two of the positions of the formula. -/
structure Formula where
  /-- The number of variables. -/
  vars : ℕ
  /-- The number of clauses of two literals. -/
  twoClauses : ℕ
  /-- The number of clauses of three literals. -/
  threeClauses : ℕ
  /-- The literals of the clauses of two literals. -/
  aLit : Fin twoClauses → Fin 2 → Fin vars × Bool
  /-- The literals of the clauses of three literals. -/
  bLit : Fin threeClauses → Fin 3 → Fin vars × Bool
  /-- Every literal occurs at most twice in the formula. -/
  occ_le_two : ∀ l : Fin vars × Bool,
    (Finset.univ.filter fun o : (Fin twoClauses × Fin 2) ⊕ (Fin threeClauses × Fin 3) =>
      Sum.elim (fun q => aLit q.1 q.2) (fun q => bLit q.1 q.2) o = l).card ≤ 2

namespace Formula

variable (φ : Formula)

/-- A **position** of the formula: a literal slot in one of the clauses. -/
abbrev Occ := (Fin φ.twoClauses × Fin 2) ⊕ (Fin φ.threeClauses × Fin 3)

/-- The literal occupying a position. -/
def litAt (o : φ.Occ) : Fin φ.vars × Bool :=
  Sum.elim (fun q => φ.aLit q.1 q.2) (fun q => φ.bLit q.1 q.2) o

/-- An assignment of a truth value to every variable. -/
abbrev Assignment := Fin φ.vars → Bool

/-- The assignment `a` satisfies `φ`: every clause, of either width, has a literal that
holds. -/
def Satisfies (a : φ.Assignment) : Prop :=
  (∀ c, ∃ α, a (φ.aLit c α).1 = (φ.aLit c α).2) ∧
  (∀ c, ∃ α, a (φ.bLit c α).1 = (φ.bLit c α).2)

/-- **The question of [2,3]-bounded 3-SAT**: is there a satisfying assignment? -/
def Satisfiable : Prop := ∃ a : φ.Assignment, φ.Satisfies a

end Formula

/-- The literal occupying the occurrence slot `o`, read off unnumbered indices: the two
slots of every clause of two literals come first, then the three slots of every clause of
three literals. Outside the formula the value is the positive literal of the variable `0`.
It is in this form that a construction reads a formula. -/
def litOfSlot (φ : Formula) (o : ℕ) : ℕ × Bool :=
  if o < 2 * φ.twoClauses then
    if hj : o / 2 < φ.twoClauses then
      ((φ.aLit ⟨o / 2, hj⟩ ⟨o % 2, by omega⟩).1, (φ.aLit ⟨o / 2, hj⟩ ⟨o % 2, by omega⟩).2)
    else (0, true)
  else
    if hj : (o - 2 * φ.twoClauses) / 3 < φ.threeClauses then
      ((φ.bLit ⟨(o - 2 * φ.twoClauses) / 3, hj⟩ ⟨(o - 2 * φ.twoClauses) % 3, by omega⟩).1,
        (φ.bLit ⟨(o - 2 * φ.twoClauses) / 3, hj⟩ ⟨(o - 2 * φ.twoClauses) % 3, by omega⟩).2)
    else (0, true)

/-- Which of the occurrences of its own literal the slot `o` is: the number of earlier
slots carrying the same literal. Under the occurrence bound this is `0` or `1`. -/
def slotRank (φ : Formula) (o : ℕ) : ℕ :=
  (List.range o).countP fun o' => litOfSlot φ o' == litOfSlot φ o

/-- The number of occurrence slots of the formula. -/
def slots (φ : Formula) : ℕ := 2 * φ.twoClauses + 3 * φ.threeClauses

/-- A [2,3]-bounded 3-SAT formula as a binary word: the number of variables, the two
numbers of clauses, and then the variable and the sign of every literal of every clause,
the clauses of two literals first. -/
def encodeFormula (φ : Formula) : Word :=
  Problems.encodeNat φ.vars ++ Problems.encodeNat φ.twoClauses ++
    Problems.encodeNat φ.threeClauses ++
    ((List.finRange φ.twoClauses).flatMap fun c =>
      (List.finRange 2).flatMap fun α =>
        Problems.encodeNat (φ.aLit c α).1 ++ [(φ.aLit c α).2]) ++
    (List.finRange φ.threeClauses).flatMap fun c =>
      (List.finRange 3).flatMap fun α =>
        Problems.encodeNat (φ.bLit c α).1 ++ [(φ.bLit c α).2]

/-- **[2,3]-bounded 3-SAT**, as a language: the satisfiable formulas that have no more
variables than positions, which every formula in which each variable occurs does. -/
def BoundedSat : Language :=
  {w | ∃ φ : Formula, encodeFormula φ = w ∧ φ.vars ≤ slots φ ∧ φ.Satisfiable}

/-- **[2,3]-bounded 3-SAT is NP-hard.** -/
axiom boundedSat_npHard : Problems.NPHard BoundedSat

end Lax117284.BoundedSat
