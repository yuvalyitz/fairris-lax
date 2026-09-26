import Lax117284Proofs.Theorem10_Decide
import Lax117284Proofs.Bridge

/-!
Theorem 2's tractability half, carried down to a single decidable statement about the
numbered instance: with unit processing times, a `k`-fair schedule exists exactly when
either `k` exceeds the day count and there are no clients to serve, or `k` is within range
and Kuhn's algorithm finds a matching saturating every job vertex of the finite graph of
`Theorem10_Decide`.
-/

namespace Lax117284Proofs.Theorem2Decide

open Lax117284.Scheduling
open scoped Classical

theorem clients_eq_zero_iff (I : Instance) : I.clients = 0 ↔ IsEmpty (Fin I.clients) := by
  rw [← Fintype.card_eq_zero_iff, Fintype.card_fin]

end Lax117284Proofs.Theorem2Decide
