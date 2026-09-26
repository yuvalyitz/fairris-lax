import Lax117284Proofs.Machine.IlpMain
import Lax117284Proofs.Machine.ClMainOk

/-!
The layout of the solver.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax117284Proofs.Machine.ClMain (cS cA cD com_ok)

/-- The arrays of the solver. -/
def ilpArrs : List String := ["z", "dg", "hl", "kd", "rkA", "sg", "S", "wv", "es", "xv"]

/-- The layout of the solver: the scalars it mentions, its ten arrays, twelve temporaries. -/
def layoutI : Layout := ⟨(cS ilpCom).dedup, ilpArrs, 12⟩

theorem ilp_arrays : ∀ a ∈ cA ilpCom, a ∈ ilpArrs := by decide +kernel

theorem ilp_depth : cD ilpCom ≤ 12 := by decide +kernel

set_option maxRecDepth 100000 in
theorem layoutI_ok : Com.Ok layoutI ilpCom :=
  com_ok layoutI ilpCom (fun y h => List.mem_dedup.mpr h) ilp_arrays ilp_depth

end Lax117284Proofs.Machine.Ilp
