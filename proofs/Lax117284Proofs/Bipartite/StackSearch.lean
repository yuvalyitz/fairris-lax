import Lax117284Proofs.Bipartite.Matching

/-!
The data of an iterative reformulation of `Matching.tryAugment`'s augmenting-path search, using
an explicit stack in place of Lean's own recursion. IMP+ (the word RAM's structured
while-language) has no recursion construct, only `while`, so this reformulation is the bridge
between the clean recursive correctness proof of `Matching.lean` and an actual machine
program.

A **frame** `⟨l, r, rest⟩` records that left vertex `l` is being placed by trying right
vertex `r`, with `rest` the further candidates to fall back on if `r`'s branch fails. The
**stack** (a list of frames, head = top = most recently pushed) is the augmenting path under
construction: the bottom frame is the left vertex the whole search started from, and each
frame's `r`, if that vertex turns out to be occupied, is why the next frame down was pushed to
try to re-place its occupant.
-/

namespace Lax117284Proofs.Bipartite.StackSearch

set_option genInjectivity false
set_option genSizeOfSpec false

/-- A stack frame: `l` is being placed, `r` is the candidate being tried now, `rest` are the
further candidates to try if `r`'s branch fails. -/
structure Frame (L R : Type*) where
  /-- The left vertex being placed. -/
  l : L
  /-- The right vertex currently being tried for `l`. -/
  r : R
  /-- The further candidates for `l`, to fall back on if `r` fails. -/
  rest : List R

end Lax117284Proofs.Bipartite.StackSearch
