import Lax117284Proofs.D3Rank
import Lax117284Proofs.D3Congr
import Lax117284Proofs.D3Prog

/-!
The client at a position of the order depends on the due dates only through their values on the
clients, and the states reachable in the dynamic program on a fixed number of days, on the numbers
of a stream in the array's own order, are the ones on the instance's order.
-/

namespace Lax117284Proofs.D3Link

open Lax117284Proofs.D3Rank Lax117284Proofs.D3DP Lax117284Proofs.D3Congr Lax117284Proofs.D3Prog

variable {dd1 dd2 : ℕ → ℕ} {n : ℕ}

/-- **The rank of a client below `n` depends on the due dates only below `n`.** -/
theorem rk_congr (h : ∀ j < n, dd1 j = dd2 j) : ∀ j < n, rk dd1 n j = rk dd2 n j := by
  intro j hj
  unfold rk
  refine List.countP_congr fun j' hj' => ?_
  have hj'' := List.mem_range.1 hj'
  simp only [decide_eq_true_eq]
  unfold Lt2
  rw [h j' hj'', h j hj]

/-- **The client at a position below `n` depends on the due dates only below `n`.** -/
theorem ordOf_congr {c : ℕ} (hc : c < n) (h : ∀ j < n, dd1 j = dd2 j) :
    ordOf dd1 n c = ordOf dd2 n c := by
  have ha := ordOf_spec (dd := dd2) hc
  have hrk : rk dd1 n (ordOf dd2 n c) = c := (rk_congr h _ ha.1).trans ha.2
  have h1 := ordOf_spec (dd := dd1) hc
  exact rk_injOn (dd := dd1) h1.1 ha.1 (h1.2.trans hrk.symm)

/-- **With a positive number of days, the reachable states in the dynamic program on the
array's own order agree with the ones on the instance's order, provided the order matches on
every client.** -/
theorem reach_eq {m k : ℕ} {q1 q2 : ℕ → ℕ → ℕ} {e1 e2 : ℕ → ℕ}
    (hq : ∀ i < m, ∀ c < n, q1 i c = q2 i c) (he : ∀ c < n, e1 c = e2 c) :
    Reach m k q1 e1 n = Reach m k q2 e2 n :=
  D3Congr.reach_congr hq he n le_rfl

end Lax117284Proofs.D3Link
