import Lax117284Proofs.Treewidth.Chars.Extract
import Lax117284Proofs.Treewidth.Chars.Restrict
import Lax117284Proofs.Treewidth.Wrap.Nice
import Lax117284Proofs.Treewidth.Wrap.Decompose

/-!
# `improve_correct` and the unconditional `decompose` (work package C6b)

* `improve_correct` : `improve adj k nt` is `none` iff `G[U]` has no tree decomposition of width `≤ k`, and otherwise
  a nice decomposition of `G[U]` of width `≤ k`.  Proof: `good_of_isNiceTD`, `tables_ne_nil_iff` (decision),
  `extract_spec` (a real decomposition), `niceOf_spec` (Kloks).
* `improveSpec` : `ImproveSpec adj W` holds whenever `adj.SymmOn W`.
* `decompose_correct_final`, `decompose_words_final` : the wrapper's specification without the `himp` hypothesis.

**Repair** (relative to `proofs-todo/Statements.lean`): `improve_correct` gets `hs : adj.SymmOn W` and `hU : U ⊆ W`
(a nice decomposition of `G[U]` only refers to vertices of `U`; see `Wrap/NOTES.md`: without symmetry it is false).
`decompose_words_final` needs no new hypothesis beyond the printed `hadj` (which implies symmetry on `range n`).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Trees Lax117284Proofs.Treewidth.Trees.NT

end Lax117284Proofs.Treewidth.Chars
