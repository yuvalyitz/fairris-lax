import Lax271696.GraphEncoding
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
---
title: Bipartite graphs with a fixed bipartition, and their encoding
type: definition
---
A bipartite graph is a simple graph whose vertices split into two sides such that every edge
joins the two sides. A graph on the vertices $0, \ldots, V-1$ is *split at* $n$ when the first
$n$ vertices form one side, the *left side*, and the remaining $V - n$ vertices the other, the
*right side*; this is Mathlib's `IsBipartiteWith` for these two sets, and it makes the graph
bipartite in Mathlib's sense.

Such a graph is handed to the word RAM as the compressed sparse row encoding of `lax-271696`
followed by one entry, the number $n$ of left vertices. The bipartition is part of the input, as
it is in the usual statement of the bipartite matching problem.

# Formalization notes

The graph is a Mathlib `SimpleGraph` on `Fin V`, and both its encoding and the number of
vertices come from the archive: `EncodesGraph g V G` of `lax-271696` says that the word `g` is a
compressed sparse row encoding of `G`. The word of an instance is `g ++ [n]`. The block `g` is
self-delimiting — its header fixes its length — so the split of the word into the block and the
appended entry is determined by the word, as in the parameterized instances of the same
submission, and the graph block sits at the same offsets as in every statement built on that
encoding.

The word is required to encode a graph that genuinely is split at `n`: an edge inside a side is
not an input the theorems below speak about. The adjacency lists of the right vertices are
present in the word, as the encoding lists every edge from both ends; the algorithm reads only the
left rows, and pays for the length of the whole word only in the linear factor of its bound.

`wordGraph x` is the graph a word denotes, read off its block: two vertices are adjacent when
either lists the other. On an encoding of `G` it is `G`. It is what makes the output of the
machine a function of the word, as `ComputesInTime` requires, and `leftCount x` is the last
entry of the word.
-/

namespace Lax117284.BipartiteGraph

open Lax271696.GraphEncoding

/-- The left side of a graph on `Fin V` split at `n`: the vertices below `n`. -/
def leftSide (V n : ℕ) : Set (Fin V) := {v | (v : ℕ) < n}

/-- The right side: the vertices from `n` on. -/
def rightSide (V n : ℕ) : Set (Fin V) := {v | n ≤ (v : ℕ)}

/-- **A graph split at `n`**: bipartite with the first `n` vertices on the left and the rest on
the right. -/
def SplitAt {V : ℕ} (G : SimpleGraph (Fin V)) (n : ℕ) : Prop :=
  G.IsBipartiteWith (leftSide V n) (rightSide V n)

/-- **The word `x` presents the bipartite graph `G` on `V` vertices split at `n`**: a compressed
sparse row block encoding `G`, followed by the single entry `n`, with `n ≤ V`. -/
def EncodesBipartite (x : List ℕ) (V : ℕ) (G : SimpleGraph (Fin V)) (n : ℕ) : Prop :=
  ∃ g : List ℕ, x = g ++ [n] ∧ EncodesGraph g V G ∧ n ≤ V ∧ SplitAt G n

/-- The number of left vertices a word declares: its last entry. -/
def leftCount (x : List ℕ) : ℕ := x.getLastD 0

/-- Vertex `u` lists vertex `v` in its block. -/
def Lists (x : List ℕ) (u v : ℕ) : Prop :=
  ∃ j, offset x u ≤ j ∧ j < offset x (u + 1) ∧ target x j = v

/-- The graph a word denotes: two distinct vertices are adjacent when either lists the other. -/
def wordGraph (x : List ℕ) : SimpleGraph (Fin (vertexCount x)) :=
  SimpleGraph.fromRel fun u v : Fin (vertexCount x) => Lists x u v

end Lax117284.BipartiteGraph
