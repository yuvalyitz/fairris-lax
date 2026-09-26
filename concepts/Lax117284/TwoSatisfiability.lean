import Lax117284.Problems

/-!
---
title: Two-satisfiability
type: definition
---
A *2-CNF formula* over $n$ variables is a finite conjunction of clauses, each clause a
disjunction of two literals, a literal being a variable or a negated variable. The formula
is *satisfiable* if some assignment of truth values to the variables makes at least one
literal of every clause true. The language 2-SAT consists of the encodings of the
satisfiable 2-CNF formulas; it is decidable in linear time.

# Formalization notes

A clause is a pair of literals and not a set of at most two of them. The distinction is the
one that matters here: what breaks the tractability of 2-SAT is a clause with three
literals, so the width has to be part of the definition rather than a side condition. A
clause repeating its literal is allowed and expresses a unit clause.

A literal is a variable together with a sign, `true` standing for the variable and `false`
for its negation, so that a literal holds under an assignment exactly when the assignment
agrees with the sign.

The numbers of an encoded formula are written with the numeral code of the scheduling
languages, so that all words of this submission are read the same way.
-/

namespace Lax117284.TwoSatisfiability

open Lax434930.PolynomialTime

/-- A **2-CNF formula**: `clauses` clauses over `vars` variables, each clause a pair of
literals, a literal being a variable together with a sign. -/
structure Formula where
  /-- The number of variables. -/
  vars : ℕ
  /-- The number of clauses. -/
  clauses : ℕ
  /-- The two literals of each clause. -/
  lit : Fin clauses → Fin 2 → Fin vars × Bool

namespace Formula

variable (φ : Formula)

/-- An assignment of a truth value to every variable. -/
abbrev Assignment := Fin φ.vars → Bool

/-- The assignment `a` satisfies `φ`: every clause has a literal that holds. -/
def Satisfies (a : φ.Assignment) : Prop :=
  ∀ c, ∃ α, a (φ.lit c α).1 = (φ.lit c α).2

/-- **The question of 2-satisfiability**: is there a satisfying assignment? -/
def Satisfiable : Prop := ∃ a : φ.Assignment, φ.Satisfies a

end Formula

/-- An unsatisfiable formula: one variable, required by one clause to be true and by
another to be false. It is the image a reduction into 2-SAT gives the words it must
reject. -/
def unsatisfiable : Formula where
  vars := 1
  clauses := 2
  lit c _ := (0, decide (c = 0))

/-- **The rejected formula is unsatisfiable.** -/
axiom not_satisfiable_unsatisfiable : ¬ unsatisfiable.Satisfiable

/-- A 2-CNF formula as a binary word: the number of variables, the number of clauses, and
then the variable and the sign of both literals of every clause. -/
def encodeFormula (φ : Formula) : Word :=
  Problems.encodeNat φ.vars ++ Problems.encodeNat φ.clauses ++
    (List.finRange φ.clauses).flatMap fun c =>
      (List.finRange 2).flatMap fun α =>
        Problems.encodeNat (φ.lit c α).1 ++ [(φ.lit c α).2]

/-- **2-SAT**, as a language. -/
def TwoSat : Language := {w | ∃ φ : Formula, encodeFormula φ = w ∧ φ.Satisfiable}

/-- **2-SAT is solvable in polynomial time**, indeed in linear time. -/
axiom twoSat_mem_P : TwoSat ∈ P

end Lax117284.TwoSatisfiability
