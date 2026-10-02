import Lax117284Proofs.Treewidth.Size.RealF
import Lax117284Proofs.Treewidth.Size.PlanSize

/-!
# Size bounds (WP P1): the statements in the shape of `proofs-todo/Machine.lean`

* `joinC_length_le_64` / `introC_length_le_64` : the typed `2^(64 (|B| + kmax + 2)^3)` bounds;
* `tables_length_le_C0`, `tables_pre_le_C0` : with the constant `C0 = 30000` of `Machine.lean` (`≤ 2^(C0 (k+2)^3)`), for
  the tables themselves and for the lists *before* `dedup` in `forgetTable`/`introTable`/`joinTable`;
* `extract_size_le` : `Machine.lean`'s statement with the extra hypothesis `nt.toRT.Width (k + 1)` (bags of at most
  `k + 2` vertices); the constant `4 * (k + 3)` is kept (the proof gives `2 * k + 8`).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- `Machine.lean`'s `C0`. -/
def sizeC0 : ℕ := 30000

end Lax117284Proofs.Treewidth.Chars
