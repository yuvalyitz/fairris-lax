import Lax117284.BipartiteGraph
import Lax117284.BipartiteMatching
import Lax808846.RamComputes

/-!
---
title: The matching number of a bipartite graph in time O(n · |x|)
type: theorem
---
There is one word RAM program and one constant $c$ such that, at every word length $w$, given a
bipartite graph split at $n$ as a word $x$ with $c\,(|x|+1) \le 2^w$, the program halts within
$c\,(n+1)\,(|x|+1)$ instructions with the matching number of the graph as its single output
entry. Since the word has length $3 + V + 2E + 1$ for $V$ vertices and $E$ edges, this is Kuhn's
bound $O(|L| \cdot (|V| + |E|))$, hence $O(|V| \cdot |E|)$ on graphs without isolated vertices.

# Formalization notes

The program runs one augmenting search per left vertex, in the order of the word. A search
marks each right vertex at most once, scans the adjacency list of each left vertex it reaches at
most once, and clears its marks before the next search; so a search costs a number of
instructions linear in the length of the word, and the $n$ searches cost $c\,n\,(|x|+1)$. The
matching itself is left in memory; the output is its size, which is a function of the graph
alone, whereas which maximum matching is found depends on the order of the lists.

The admissible inputs are the encodings of bipartite graphs split at their last entry that fit
the word length. Every value the program manipulates — a vertex, an offset into the word, a
counter, a step count — is below $c\,(|x|+1)$, so the one fitting condition on the word suffices.
The program is quantified before the word length: it is one algorithm, uniform in $w$.
-/

namespace Lax117284.BipartiteKuhnTime

open Lax808846.Ram Lax808846.RamComputes Lax117284.BipartiteGraph Lax117284.BipartiteMatching

open scoped Classical in
/-- **The matching number is computed within `c · (n + 1) · (|x| + 1)` instructions** by one
word RAM program at every word length that fits the word. -/
axiom computes : ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog
      {x | (∃ (V : ℕ) (G : SimpleGraph (Fin V)) (n : ℕ), EncodesBipartite x V G n) ∧
        c * (x.length + 1) ≤ 2 ^ w}
      (fun x => [matchingNumber (wordGraph x)])
      (fun x => c * (leftCount x + 1) * (x.length + 1))

end Lax117284.BipartiteKuhnTime
