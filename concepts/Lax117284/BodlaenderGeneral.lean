import Lax117284.GraphWords
import Lax808846.Ram

/-!
---
title: Nice Tree Decompositions of Small Width Are Found in Fixed-Parameter Time
type: theorem
---
**Bodlaender's theorem.** For every constant $k$ one can decide in linear time whether a graph
has treewidth at most $k$, and if so construct a tree decomposition of width at most $k$; the
dependence on $k$ is $2^{O(k^3)}$. Kloks' construction turns a tree decomposition into a nice
one of the same width in time linear in its size, so the same holds for nice decompositions.

H. L. Bodlaender, *"A linear-time algorithm for finding tree-decompositions of small
treewidth"*, SIAM Journal on Computing 25 (1996) 1305–1317; T. Kloks, *"Treewidth: Computations
and Approximations"*, Lecture Notes in Computer Science 842, Springer 1994. A simplified
presentation of the whole algorithm is E. Althaus and S. Ziegler, *"Optimal tree decompositions
revisited: a simpler linear-time FPT algorithm"*, arXiv:1912.09144 (2020).

The formalized algorithm uses the improvement step of Bodlaender and Kloks in a
vertex-by-vertex construction. It extends a decomposition to include the next vertex,
then reduces its width using `BodlaenderKloks.improveDecomposition`. Its verified bound
is fixed-parameter time with polynomial dependence on the encoded input length, as
stated below.

# Formalization Notes

The input is the word of the graph (see `GraphWords`) followed by the bound `k`. The output is
either `[0]`, admissible only when the graph has no tree decomposition of width at most `k` (in
the archive's sense), or `1` followed by the word of a nice tree decomposition of width at most
`k`. The output is a relation and not a function, since a graph has many decompositions: the
program may produce any one of them.

The bound is `c * 2 ^ (c * k ^ 3) * (|g| + 2) ^ c`: the paper's is linear in the number of
vertices, while the input has length quadratic in it, and the statement is polynomial in the
length of the word, which is what a consumer needs. The guard on the word length is what makes
the statement true: the program's tables have size `2 ^ (c * k ^ 3)` times a polynomial in the
length of the word, so a machine of too small a word length cannot hold them; the hypothesis is
an explicit inequality against `2 ^ W`, checkable from the input alone, and it ranges over the
entries of the word so that every entry, and every number the output contains (node numbers are
bounded by the running time), is a word. Nothing is claimed for word lengths that violate it.

The program and the constant are quantified before the word length, the graph and the bound,
so one program serves them all.
-/

namespace Lax117284.BodlaenderGeneral

open Lax808846.Ram Lax117284.GraphWords

open Classical in
/-- **Bodlaender's theorem with Kloks' niceness, on a word RAM.** One program and one constant
serve every word length `W`, every graph `G` on `n` vertices and every bound `k`, provided the
word — the graph followed by `k` — fits with room for `c * 2 ^ (c * k ^ 3)` times a polynomial
in its length. On such a word the program halts within `c * 2 ^ (c * k ^ 3) * (|g| + 2) ^ c`
instructions, writing `[0]` if the graph has no tree decomposition of width at most `k`, and `1`
followed by the word of a nice tree decomposition of width at most `k` otherwise. -/
axiom niceDecomposition_computable :
    ∃ (prog : Program) (c : ℕ), ∀ (W k n : ℕ) (G : SimpleGraph (Fin n)) (g : List ℕ),
      EncodesGraph g G →
      (∀ v ∈ g ++ [k], c * 2 ^ (c * k ^ 3) * ((g ++ [k]).length + v + 1) ^ c ≤ 2 ^ W) →
      ∃ (out : List ℕ) (t : ℕ), t ≤ c * 2 ^ (c * k ^ 3) * (g.length + 2) ^ c ∧
        RunsTo W prog (g ++ [k]) out t ∧
        (out = [0] ∧ ¬ Lax228581.Treewidth.HasTreewidthAtMost G k ∨
          ∃ D, out = 1 :: D ∧ NiceDecomposition G k D)

end Lax117284.BodlaenderGeneral
