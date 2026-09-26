import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Sort

/-!
---
title: Kuhn's algorithm
type: definition
---
Kuhn's algorithm builds a matching of a bipartite graph one left vertex at a time. To place a
left vertex $l$ it searches for an *augmenting path*: among the neighbours of $l$ not yet
visited on this search, it takes one that is either free, in which case $l$ takes it, or held by
some left vertex $l'$, in which case $l'$ is displaced and re-placed by the same search, among
the neighbours not yet visited; if $l'$ can be re-placed, $l$ takes the neighbour, and otherwise
the next neighbour is tried. A left vertex whose search fails stays unmatched, and the algorithm
goes on to the next left vertex. The output is the matching after every left vertex has been
tried.

# Formalization notes

The graph is a relation `adj : L → R → Prop` between the left and the right vertices, both finite
types; the bipartite graph split at `n` of this submission gives such a relation between
`Fin n` and `Fin (V - n)`. A matching is kept as `μ : R → Option L`, the left vertex each right
vertex currently holds, which is the form the machine keeps it in.

`tryAugment` is the search from one left vertex. It is written as a recursion on a fuel, spent
once per displaced left vertex; the number of right vertices plus one is always enough, as each
descent visits a fresh right vertex. `step` tries one candidate neighbour and passes a success
through unchanged, so that the fold over the candidates stops at the first success. `runAll`
tries every left vertex in turn from an empty visited set, keeping the matching it has when a
search fails. The machine implements the recursion with an explicit stack of frames, one per
displaced vertex, and tries left vertices and neighbours in the order of the word; the order is
immaterial to what is proved about the result.
-/

namespace Lax117284.BipartiteKuhn

variable {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- The neighbours of a left vertex. -/
noncomputable def nbrs (adj : L → R → Prop) [DecidableRel adj] (l : L) : Finset R :=
  Finset.univ.filter fun r => adj l r

/-- A matching respects the graph: every right vertex's match is one of its neighbours. -/
def Respects (adj : L → R → Prop) (μ : R → Option L) : Prop :=
  ∀ r l, μ r = some l → adj l r

/-- A matching is injective: no two right vertices hold the same left vertex. -/
def InjOnSupport (μ : R → Option L) : Prop :=
  ∀ r r' l, μ r = some l → μ r' = some l → r = r'

/-- The left vertex `l` holds some right vertex. -/
def Matched (μ : R → Option L) (l : L) : Prop := ∃ r, μ r = some l

/-- The number of matched pairs. -/
noncomputable def size (μ : R → Option L) : ℕ :=
  (Finset.univ.filter fun r => (μ r).isSome).card

/-- One candidate `r` of the search for `l`: a success already found passes through; a free `r`
is taken; an `r` held by `l'` is taken if `l'` can be re-placed by `tryFrom`, from the matching
with `r` cleared and `r` marked visited. -/
noncomputable def step (adj : L → R → Prop) [DecidableRel adj] (μ : R → Option L) (l : L)
    (tryFrom : (R → Option L) → Finset R → L → Option (R → Option L))
    (acc : Option (R → Option L) × Finset R) (r : R) :
    Option (R → Option L) × Finset R :=
  match acc.1 with
  | some _ => acc
  | none =>
    let visited' := insert r acc.2
    match μ r with
    | none => (some (Function.update μ r (some l)), visited')
    | some l' =>
      match tryFrom (Function.update μ r none) visited' l' with
      | some μ' => (some (Function.update μ' r (some l)), visited')
      | none => (none, visited')

/-- **The augmenting search from `l`**: try the unvisited neighbours of `l` in turn, with `fuel`
descents allowed. -/
noncomputable def tryAugment (adj : L → R → Prop) [DecidableRel adj] (fuel : ℕ)
    (μ : R → Option L) (visited : Finset R) (l : L) :
    Option (R → Option L) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    (((nbrs adj l) \ visited).toList.foldl (step adj μ l (tryAugment adj fuel))
      (none, visited)).1

/-- **Try every left vertex in turn**, from an empty visited set, keeping the matching when a
search fails. -/
noncomputable def runAll (adj : L → R → Prop) [DecidableRel adj] (fuel : ℕ) :
    List L → (R → Option L) → (R → Option L)
  | [], μ => μ
  | l :: ls, μ =>
    match tryAugment adj fuel μ ∅ l with
    | some μ' => runAll adj fuel ls μ'
    | none => runAll adj fuel ls μ

/-- **Kuhn's algorithm**: every left vertex, from the empty matching, with fuel enough for any
search. -/
noncomputable def kuhn (adj : L → R → Prop) [DecidableRel adj] : R → Option L :=
  runAll adj (Fintype.card R + 1) Finset.univ.toList (fun _ => none)

end Lax117284.BipartiteKuhn
