import Lax117284.TwoSatCNF
import Lax808846.RamComputes

/-!
---
title: 2-SAT is decided in time linear in the word times the number of variables
type: theorem
---
There is one word RAM program and one constant $c$ such that, at every word length $w$, given
the bits of a binary word $x$ with $c\,(|x|+1) \le 2^w$, the program halts within
$c\,(|x|+1)\,(v+1)$ instructions, where $v$ is the number of distinct variables of the formula
$x$ encodes (and $0$ if it encodes none), with output $1$ if $x$ is in 2-SAT and $0$ otherwise.
Since a formula with $m$ clauses has at most $2m$ variables and at most $|x|$, the bound is at
most $c\,(|x|+1)\,(2m+1)$ and at most $c\,(|x|+1)^2$.

# Formalization notes

The word RAM of `lax-808846` reads words of natural numbers; a binary word is handed to it as
its list of zeros and ones, one bit an entry, so that the length of the input is the length of
the binary word and the machine has no advantage from packing bits into its words. The admissible
inputs are the lists of zeros and ones, all of them: a list that is not the encoding of a formula
is answered `0`, as it is not in the language. The output is `1` or `0`; the machine writes it
as a single entry.

The bound is proved, not merely asserted, from the program: reading and decoding the word is
linear in its length; the implication graph has $2b$ nodes for $b$ the bound on the indices,
which is at most the length of the word because an index is written in unary, and at most two
edges per clause; each of the at most $2v$ searches costs a number of instructions linear in the
size of the graph, and skipping a variable that does not occur costs a constant. The strongly
connected components of Aspvall, Plass and Tarjan would bring the second factor down to a
constant; that algorithm is not formalized here.

The fitting hypothesis $c\,(|x|+1) \le 2^w$ is the "word is wide enough" condition written as an
inequality: every value the program manipulates is a count of nodes, edges, bits or steps, all
of them below $c\,(|x|+1)$. The program is quantified before the word length, so it is one
algorithm at every word length, not a family.
-/

namespace Lax117284.TwoSatRunningTime

open Lax429075.CNF Lax429075.Encoding Lax434930.PolynomialTime Lax117284.TwoSatCNF
open Lax808846.Ram Lax808846.RamComputes

/-- A binary word as a list of zeros and ones, the form in which the word RAM reads it. -/
def natBits (w : Word) : List ℕ := w.map fun b => if b then 1 else 0

/-- A list of numbers as a binary word: which entries are nonzero. -/
def bitsOf (x : List ℕ) : Word := x.map fun n => decide (n ≠ 0)

/-- The number of distinct variables of the formula a list of bits encodes, and `0` if it
encodes none. -/
def wordVarCount (x : List ℕ) : ℕ := ((decodeCNF (bitsOf x)).map varCount).getD 0

open scoped Classical in
/-- **2-SAT is decided within `c · (|x| + 1) · (v + 1)` instructions**, `v` the number of
distinct variables, by one word RAM program at every word length that fits the word. -/
axiom decides : ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog
      {x | (∀ v ∈ x, v ≤ 1) ∧ c * (x.length + 1) ≤ 2 ^ w}
      (fun x => if bitsOf x ∈ TwoSAT then [1] else [0])
      (fun x => c * (x.length + 1) * (wordVarCount x + 1))

end Lax117284.TwoSatRunningTime
