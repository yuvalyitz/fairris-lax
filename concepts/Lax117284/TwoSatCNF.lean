import Lax429075.Satisfiability
import Mathlib.Data.Finset.Card

/-!
---
title: 2-CNF formulas and the language 2-SAT
type: definition
---
A CNF formula is in *2-CNF* when every clause has at most two literals. The language 2-SAT
consists of the binary encodings of the satisfiable 2-CNF formulas: it is the language SAT of
`lax-429075`, restricted to the encodings of formulas in 2-CNF.

# Formalization notes

Nothing about formulas, literals, satisfiability or encodings is defined here. A formula is a
formula of `lax-429075` — a list of clauses, a clause a list of literals, a literal a variable
index with a sign — its satisfiability is that submission's `Satisfiable`, and its binary word is
that submission's `encodeCNF`. The only new notion is the width condition, so that 2-SAT is
literally a subset of SAT, with membership in the two languages witnessed by the same formula.

A clause is allowed to have fewer than two literals. A unit clause is a clause of one literal;
the empty clause is a clause no assignment satisfies, so a formula containing one is not
satisfiable. Both are handled by the algorithm, and the classical results hold for them: the
restriction to clauses of exactly two literals is a convenience that this development does not
need.

The variables of a formula are the indices its literals mention, however large; a formula on
the single variable `1000` has one variable. The count of distinct variables is what the running
time of the algorithm is measured by, besides the length of the word.
-/

namespace Lax117284.TwoSatCNF

open Lax429075.CNF Lax429075.Encoding Lax429075.Satisfiability Lax434930.PolynomialTime

/-- A CNF formula is in **2-CNF** when every clause has at most two literals. -/
def IsTwoCNF (F : Formula) : Prop := ∀ C ∈ F, C.length ≤ 2

/-- The literals of a formula, in order of occurrence. -/
def literals (F : Formula) : List Literal := F.flatMap id

/-- The variables a formula mentions. -/
def vars (F : Formula) : Finset ℕ := ((literals F).map Literal.index).toFinset

/-- The number of distinct variables of a formula. -/
def varCount (F : Formula) : ℕ := (vars F).card

/-- **2-SAT**: the encodings of the satisfiable formulas in 2-CNF. It is `SAT` restricted to
the encodings of 2-CNF formulas. -/
def TwoSAT : Language := {w | ∃ F : Formula, encodeCNF F = w ∧ IsTwoCNF F ∧ Satisfiable F}

end Lax117284.TwoSatCNF
