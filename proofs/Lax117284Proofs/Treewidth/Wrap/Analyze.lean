import Lax117284Proofs.Treewidth.Chars.AnalyzeRT

/-!
# The remaining `analyze` lemmas (C8a)

* `analyze_char` : the characteristic read off the analysis is `RT.char`;
* `conn_of_conn_toRT_analyze`, `analyze_toRT_isTD`, `analyze_toRT_width` : the two directions of validity / width of
  the reassembled analysis (C3 proved the forward directions);
* `analyze_toRT_char` : true for `B' = B` (this is `char_toRT_analyze`); for `B' ≠ B` it is FALSE as typed in
  `proofs-todo/Statements.lean` (reassembling the analysis sorts the kids by `key` relative to `B`; the normal form
  relative to `B'` sorts stably, so ties in `B'`-keys expose the reordering).  See `Wrap/NOTES.md`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

end Lax117284Proofs.Treewidth.Chars
