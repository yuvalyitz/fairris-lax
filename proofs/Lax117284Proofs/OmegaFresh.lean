import Lean

/-!
`omega_fresh`: `omega` after clearing every hypothesis that talks about a machine state.

The proofs of the word RAM programs thread a growing list of facts about the states
(`σ₁.vars "x" = …`, one per variable and step) through the proof. `omega` reads all of them as
equations between atoms, though none of them concerns the arithmetic goal, and it slows down with
every step. The tactic hands `omega` only the arithmetic. If clearing loses a fact that was
needed, it falls back on plain `omega`.
-/

namespace Lax117284Proofs

open Lean Elab Tactic Meta

/-- The head constants of the hypotheses `omega_fresh` clears. -/
def stateConsts : List Name :=
  [`Lax808846Proofs.Imp.Env.vars, `Lax808846Proofs.Imp.Env.arrs, `Lax808846Proofs.Imp.Env.out,
    `Lax808846Proofs.Imp.Env.setVar]

/-- Clear the hypotheses mentioning a machine state, then run `omega`. -/
elab "omega_clear" : tactic => do
  let g ← getMainGoal
  let g ← g.withContext do
    let mut g := g
    for d in (← getLCtx).decls.toList.reverse do
      match d with
      | none => pure ()
      | some d =>
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        let hit := (ty.find? fun e => match e.getAppFn.constName? with
          | some n => stateConsts.contains n
          | none => false).isSome
        if hit then g ← g.tryClear d.fvarId
    pure g
  replaceMainGoal [g]
  evalTactic (← `(tactic| omega))

/-- `omega` on the arithmetic alone, or plain `omega` when that does not suffice. -/
macro "omega_fresh" : tactic => `(tactic| first | omega_clear | omega)

end Lax117284Proofs
