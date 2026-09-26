import Lax117284.BipartiteKuhnTime
import Lax759944.RamPolytime

/-!
---
title: Saturating and perfect matchings, decided in the same time
type: corollary
---
Whether a bipartite graph split at $n$ has a matching saturating its left side, and whether it
has a perfect matching, are decided within the same bound $c\,(n+1)\,(|x|+1)$. The saturating
question is also decided *on every word*, well formed or not, in the same time and in the sense
of polynomial time on the word RAM of [lax-759944](https://laxarchive.org/lax-759944/), which is
the form another submission can compose with its own reductions.

# Formalization notes

Both are comparisons of the matching number with a number the word carries: a matching
saturating the left side exists exactly when the matching number is $n$, since a matching of a
graph split at $n$ has at most one edge at each left vertex, and a perfect matching exists exactly
when twice the matching number is the number of vertices. The programs compute the matching
number and compare.

The total statements need a notion of a *well-formed* word that a program can check in linear
time: the counts, the offsets, the targets and the split are as the encoding demands, and every
listed edge crosses the split. Symmetry of the adjacency lists is *not* demanded, because the
graph a word denotes (`wordGraph`) is the symmetric closure of its lists, so the program may
symmetrize the lists itself in linear time; every word encoding a bipartite graph is well formed.
On a well-formed word the answer is that of `decides_saturating`; on any other word it is `0`.
The word `saturatingAnswer` is the function the total program computes, and
`ramPolytime_saturating` states it in the archive's polynomial-time form on a length-prefixed
input, at every word length in which the word fits.
-/

namespace Lax117284.BipartiteDecision

open Lax808846.Ram Lax808846.RamComputes Lax117284.BipartiteGraph Lax117284.BipartiteMatching
open Lax271696.GraphEncoding

/-- The admissible words: encodings of bipartite graphs split at their last entry, fitting the
word length. -/
def Dom (c w : ℕ) : Set (List ℕ) :=
  {x | (∃ (V : ℕ) (G : SimpleGraph (Fin V)) (n : ℕ), EncodesBipartite x V G n) ∧
    c * (x.length + 1) ≤ 2 ^ w}

open scoped Classical in
/-- **A matching saturating the left side is decided within `c · (n + 1) · (|x| + 1)`
instructions.** -/
axiom decides_saturating : ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog (Dom c w)
      (fun x => if ∃ M : (wordGraph x).Subgraph, M.IsMatching ∧
          Saturates (wordGraph x) M (leftSide (vertexCount x) (leftCount x)) then [1] else [0])
      (fun x => c * (leftCount x + 1) * (x.length + 1))

open scoped Classical in
/-- **A perfect matching is decided within `c · (n + 1) · (|x| + 1)` instructions.** -/
axiom decides_perfect : ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog (Dom c w)
      (fun x => if ∃ M : (wordGraph x).Subgraph, M.IsPerfectMatching then [1] else [0])
      (fun x => c * (leftCount x + 1) * (x.length + 1))

/-- **A well-formed bipartite word**: at least as many vertices as left vertices, the length of
a compressed sparse row block plus the split, offsets starting at `0`, ending at twice the edge
count and nondecreasing, every target a vertex, and every listed edge crossing the split. -/
structure WellFormed (x : List ℕ) : Prop where
  /-- The left vertices are among the vertices. -/
  left_le : leftCount x ≤ vertexCount x
  /-- The compressed sparse row block, then the split. -/
  length_eq : x.length = 4 + vertexCount x + 2 * edgeCount x
  /-- The first offset is `0`. -/
  offset_zero : offset x 0 = 0
  /-- The last offset is twice the edge count. -/
  offset_last : offset x (vertexCount x) = 2 * edgeCount x
  /-- The offsets are nondecreasing. -/
  offset_mono : ∀ i < vertexCount x, offset x i ≤ offset x (i + 1)
  /-- Every target is a vertex. -/
  target_lt : ∀ j < 2 * edgeCount x, target x j < vertexCount x
  /-- Every listed edge crosses the split. -/
  crosses : ∀ u < vertexCount x, ∀ j, offset x u ≤ j → j < offset x (u + 1) →
    (u < leftCount x ↔ leftCount x ≤ target x j)

open scoped Classical in
/-- The answer of the total program: `1` on a well-formed word whose graph has a matching
saturating its left side, `0` on every other word. -/
noncomputable def saturatingAnswer (x : List ℕ) : List ℕ :=
  if WellFormed x ∧ ∃ M : (wordGraph x).Subgraph, M.IsMatching ∧
      Saturates (wordGraph x) M (leftSide (vertexCount x) (leftCount x)) then [1] else [0]

/-- **On every word whose length and entries fit the word length, a matching saturating the
left side is decided within `c · (n + 1) · (|x| + 1)` instructions**, `n` the last entry of the
word, well-formedness included. The entries must fit: the machine holds every entry modulo
`2 ^ w`, so a word with an entry beyond a word is indistinguishable from the well-formed word it
reduces to, and no program could answer both. -/
axiom decides_saturating_all : ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog {x | c * (x.length + 1) ≤ 2 ^ w ∧ ∀ v ∈ x, c * (v + 1) ≤ 2 ^ w}
      saturatingAnswer (fun x => c * (leftCount x + 1) * (x.length + 1))

/-- **The same, as polynomial time on the word RAM** in the sense of `lax-759944`: one program
reads the length-prefixed word and writes `saturatingAnswer` within a polynomial in the bit size
of the word, at every word length in which the word fits. -/
axiom ramPolytime_saturating : Lax759944.RamPolytime.RamPolytime saturatingAnswer

end Lax117284.BipartiteDecision
