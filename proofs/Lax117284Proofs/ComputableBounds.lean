import Lax117284Proofs.FptBridge

/-! Computability of the arithmetic expressions used in the scheduling time bounds. -/

namespace Lax117284Proofs.ComputableBounds

macro "bound_computable" : tactic => `(tactic|
  repeat' first
  | exact Computable.id
  | exact Computable.const _
  | with_reducible apply Lax117284Proofs.FptBridge.computable_pow₂
  | with_reducible apply Primrec.nat_add.to_comp.comp
  | with_reducible apply Primrec.nat_mul.to_comp.comp
  | with_reducible apply Primrec.nat_sub.to_comp.comp)

end Lax117284Proofs.ComputableBounds
