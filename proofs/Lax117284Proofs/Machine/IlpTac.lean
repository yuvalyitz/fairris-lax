import Lax808846Proofs.Tactic

/-!
Small tactics for the proofs of the machine layer.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lean Elab Tactic Meta in
/-- Clear every hypothesis that is a `Run` (the derivations that `run_vcg` leaves behind). -/
elab "clear_runs" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut g := g
    let ids := (← getLCtx).foldl (init := ([] : List FVarId)) fun acc d =>
      if d.isImplementationDetail then acc else
      if d.type.isAppOf ``Lax808846Proofs.Reasoning.Run then d.fvarId :: acc else acc
    for id in ids do
      try g ← g.clear id catch _ => pure ()
    replaceMainGoal [g]

end Lax117284Proofs.Machine.Ilp
