import Lax117284Proofs.Treewidth.Fun.Meta
import Lax117284Proofs.Treewidth.Fun.ToVal

/-!
# The `ev_*` tactic kit

Goals of the form `EvLe Δ B ρ t v c` (term `t` evaluates to `v` within cost `c`) are discharged by

* `ev_start` : replaces the cost bound `c` by a metavariable (the exact cost, assembled bottom-up) and leaves
  the side goal `?c ≤ c` **last** (close it with `omega`/`nlinarith` after everything else);
* `ev_step`  : one construct — `lit var add sub mul lt eq cons fst snd isNat(T/F) ite(T/F) letE`, and argument lists;
* `ev_run`   : `repeat' ev_step`, leaving only side goals (`n < B`, `ρ[i]? = some v`, `n ≠ 0`, …);
* `ev_side`  : closes the standard side goals (`rfl`, `simp`, `omega`, `decide`);
* `ev_call h`, `ev_callv h` : a call of a function whose behaviour is a `Runs` fact `h`.

`ite` needs the branch: `ev_iteT` / `ev_iteF`.
-/

namespace Lax117284Proofs.Treewidth.Fun

syntax "ev_start" : tactic
macro_rules
  | `(tactic| ev_start) => `(tactic| apply EvLe.mono)

open Lean Meta Elab Tactic in
/-- succeeds iff the main goal is a proposition that is not itself an `EvLe`/`EvLL` goal. -/
elab "ev_is_side" : tactic => do
  let g ← getMainGoal
  let ty ← g.getType
  unless (← isProp ty) do throwError "ev_side: not a proposition"
  let ty ← whnfR ty
  if ty.getAppFn.isConstOf ``EvLe || ty.getAppFn.isConstOf ``EvLL then
    throwError "ev_side: an evaluation goal"

syntax "ev_side" : tactic
macro_rules
  | `(tactic| ev_side) => `(tactic| (ev_is_side; first | rfl | (simp; done) | omega | decide | (simp [*]; done) | (simp_all; done)))

syntax "ev_step" : tactic
syntax "ev_sub" : tactic
macro_rules
  | `(tactic| ev_step) => `(tactic| first
    | apply EvLe.lit
    | apply EvLe.var
    | apply EvLe.add
    | apply EvLe.sub
    | apply EvLe.mul
    | apply EvLe.lt
    | apply EvLe.eq
    | apply EvLe.cons
    | apply EvLe.fst
    | apply EvLe.snd
    | (apply EvLe.isNatT; (case ha => ev_sub))
    | (apply EvLe.isNatF; (case ha => ev_sub))
    | (apply EvLe.iteT; (case hc => ev_sub); (case hn => ev_side))
    | (apply EvLe.iteF; (case hc => ev_sub); (case hn => ev_side))
    | apply EvLe.letE
    | apply EvLL.cons
    | (apply Runs.evle ?hargs ?hrun; (case hargs => ev_sub); (case hrun => assumption))
    | (apply Runs.evle_v ?hft ?hargs ?hrun; (case hft => ev_sub); (case hargs => ev_sub); (case hrun => assumption))
    | exact EvLL.nil)
  | `(tactic| ev_sub) => `(tactic| ((all_goals (repeat' ev_step)); (all_goals try ev_side); (all_goals try ev_side); done))

/-- solve as much as possible, leaving the stuck goals (side conditions or evaluation goals). -/
syntax "ev_run" : tactic
macro_rules
  | `(tactic| ev_run) => `(tactic| ((all_goals (repeat' ev_step)); (all_goals try ev_side); (all_goals try ev_side)))

/-- choose the branch explicitly. -/
syntax "ev_iteT" : tactic
macro_rules
  | `(tactic| ev_iteT) => `(tactic| apply EvLe.iteT)
syntax "ev_iteF" : tactic
macro_rules
  | `(tactic| ev_iteF) => `(tactic| apply EvLe.iteF)

syntax "ev_call " term : tactic
macro_rules
  | `(tactic| ev_call $h) => `(tactic| apply Runs.evle _ $h)
syntax "ev_callv " term : tactic
macro_rules
  | `(tactic| ev_callv $h) => `(tactic| apply Runs.evle_v _ _ $h)

end Lax117284Proofs.Treewidth.Fun
