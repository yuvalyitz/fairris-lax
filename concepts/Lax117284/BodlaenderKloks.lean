import Lax117284.GraphWords
import Lax808846.Ram

/-!
---
title: Optimal tree decompositions from a given one
type: theorem
---
**The theorem of Bodlaender and Kloks.** For all $k$ and $\ell$ there is a linear-time
algorithm that, given a graph together with a tree decomposition of width at most $\ell$,
decides whether the treewidth of the graph is at most $k$ and, if so, finds a tree
decomposition of width at most $k$. The dependence on $\ell$ is $2^{O(\ell^3)}$.

H. L. Bodlaender and T. Kloks, *"Efficient and constructive algorithms for the pathwidth and
treewidth of graphs"*, Journal of Algorithms 21 (1996) 358–402. A simpler presentation, which
this module follows, is E. Althaus and S. Ziegler, *"Optimal tree decompositions revisited:
a simpler linear-time FPT algorithm"*, arXiv:1912.09144 (2020), §3; the statement is Theorem
2.10 of H. L. Bodlaender, *"A linear-time algorithm for finding tree-decompositions of small
treewidth"*, SIAM Journal on Computing 25 (1996) 1305–1317, where it is used as a black box.

This is the *second stage* of Bodlaender's algorithm, `BodlaenderGeneral.niceDecomposition_computable`
being the first: the latter builds the decomposition of width at most $2k+1$ this one
consumes.

# Formalization notes

The input is one word: the graph (see `GraphWords`), the two numbers `k` and `l`, and the word
of a nice tree decomposition of width at most `l`. The graph word states its own length, so the
three parts are told apart. The given decomposition is nice; Althaus and Ziegler assume it and
the conversion of an arbitrary decomposition into a nice one of the same width takes time
$O(\ell^2(|V(T)| + |V|))$ (Kloks), so nothing is lost.

The output is either `[0]`, admissible only when the graph has no tree decomposition of width
at most `k`, or `1` followed by the word of a nice tree decomposition of width at most `k`. It
is a relation rather than a function: a graph has many decompositions, and the program may
produce any one of them. The output is nice, where the theorem produces an arbitrary
decomposition, because the conversion is one more linear-time pass and every consumer wants
the nice form.

The bound is `c * 2 ^ (c * l ^ 3) * (|input| + 2) ^ c`. The paper's is linear in the number of
vertices; on a word RAM given the adjacency matrix the input has length quadratic in the number
of vertices, and the statement is polynomial in it, which is all a consumer needs. The
condition on the word length is an explicit inequality against `2 ^ W`, on every entry of the
input: the tables of the algorithm have size `2 ^ (c * l ^ 3)` times a polynomial in the length,
so a machine of too small a word length cannot hold them.

The program and the constant are quantified before the word length, the graph and the two
bounds, so one program serves all of them.
-/

namespace Lax117284.BodlaenderKloks

open Lax808846.Ram Lax117284.GraphWords

open Classical in
/-- **The theorem of Bodlaender and Kloks, on a word RAM.** One program and one constant serve
every word length `W`, every graph `G`, every bound `k` and every nice tree decomposition `D` of
`G` of width at most `l`, provided the input `g ++ [k, l] ++ D` fits with room for
`c * 2 ^ (c * l ^ 3)` times a polynomial in its length. On such an input the program halts
within `c * 2 ^ (c * l ^ 3) * (|input| + 2) ^ c` instructions, writing `[0]` if the graph has no
tree decomposition of width at most `k`, and `1` followed by the word of a nice tree
decomposition of width at most `k` otherwise. -/
axiom improveDecomposition :
    ∃ (prog : Program) (c : ℕ), ∀ (W k l : ℕ) (n : ℕ) (G : SimpleGraph (Fin n)) (g D : List ℕ),
      EncodesGraph g G → NiceDecomposition G l D →
      (∀ v ∈ g ++ [k, l] ++ D,
        c * 2 ^ (c * l ^ 3) * ((g ++ [k, l] ++ D).length + v + 1) ^ c ≤ 2 ^ W) →
      ∃ (out : List ℕ) (t : ℕ), t ≤ c * 2 ^ (c * l ^ 3) * ((g ++ [k, l] ++ D).length + 2) ^ c ∧
        RunsTo W prog (g ++ [k, l] ++ D) out t ∧
        (out = [0] ∧ ¬ Lax228581.Treewidth.HasTreewidthAtMost G k ∨
          ∃ D', out = 1 :: D' ∧ NiceDecomposition G k D')

end Lax117284.BodlaenderKloks
