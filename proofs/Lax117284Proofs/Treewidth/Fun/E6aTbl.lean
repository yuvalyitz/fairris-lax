import Lax117284Proofs.Treewidth.Fun.E5Inst
import Lax117284Proofs.Treewidth.Fun.E6aTop

/-!
# WP E6a (6): the assembly interface and a worked union table E1 + E2 + E3 + E5 + E6a

**How the assembler references the table.**  `E6a.e6aTbl : ℕ → Option Tm` (ids `640 … 654`, all `≥ 128`).  Let `T` be the
assembled table (`layerΔ Lib.Δ 128 T` the assembled Δ).  If `E6a.e6aTbl ⊑ T` then `E6a.e6aΔ ⊑ layerΔ Lib.Δ 128 T`
(`ext_asm`) and every theorem of E6a (stated for an arbitrary `Δ'` with `hΔ : e6aΔ ⊑ Δ'`) applies to `Δ' := layerΔ Lib.Δ 128 T`.
Disjointness with another table is `e6aTbl_range` (`640 ≤ f < 655`).  The E6a functions call **only** the library
(no E1–E5 function), so no `Ext5/ExtJ/ExtIP`-style hypotheses are needed.

The worked example is `asm6Tbl = asm5Tbl ∪ e6aTbl` (`asm5Tbl` of `E5Inst` = E1 ∪ E2 ∪ E3 ∪ E5).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6a

theorem e6aTbl_range {f : ℕ} {b : Tm} (h : e6aTbl f = some b) : 640 ≤ f ∧ f < 655 := e6aTbl_lt h

/-- **assembly**: `e6aTbl ⊑ T` implies `e6aΔ ⊑ layerΔ Lib.Δ 128 T` -/
theorem ext_asm (T : ℕ → Option Tm) (h : e6aTbl ⊑ T) : e6aΔ ⊑ layerΔ Lib.Δ 128 T := Ext.layer_mono h

/-- the union of the E1 + E2 + E3 + E5 table and the E6a table -/
def asm6Tbl : ℕ → Option Tm := orElseΔ E5Inst.asm5Tbl e6aTbl

def asm6Δ : ℕ → Option Tm := layerΔ Lib.Δ 128 asm6Tbl

open Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees ToVal

end E6a
end Lax117284Proofs.Treewidth.Fun
