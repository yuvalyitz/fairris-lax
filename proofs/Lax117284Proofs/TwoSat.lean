import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Common

/-!
# Literals

Theorem 7 reduces from 2-3-SAT, whose clauses are made of literals: a variable together with a
sign. The variables of the reduction are naturally indexed by `Fin nv`, which is why this is a
small definition of its own.
-/


namespace Lax117284Proofs.Model

namespace TwoSat

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- A literal: a variable together with a sign. `pos = false` is the negated literal. -/
structure Lit (V : Type) where
  /-- The variable the literal refers to. -/
  var : V
  /-- `true` for `x`, `false` for `¬x`. -/
  pos : Bool

/-- The assignment `a` makes the literal true. -/
def Lit.Holds {V : Type} (a : V → Bool) (l : Lit V) : Prop := a l.var = l.pos

instance {V : Type} (a : V → Bool) (l : Lit V) : Decidable (l.Holds a) := by
  unfold Lit.Holds; infer_instance

end TwoSat

end Lax117284Proofs.Model
