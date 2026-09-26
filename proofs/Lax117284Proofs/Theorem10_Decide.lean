import Lax117284Proofs.Theorem10_Matching

/-!
The case `k > m` of Theorem 10's parameter.
-/

namespace Lax117284Proofs.Model.Instance

variable {I : Instance}

open scoped Classical

/-- **The other case of the parameter, `k > m`.** Theorem 10 itself only speaks for
`k ≤ m`; above that threshold no client can be served often enough unless there is no client
to serve, since a client is served on at most `m` days (`served_le_numDays`). -/
theorem hasKFairSchedule_iff_isEmpty_client_of_lt {I : Instance} {k : ℕ}
    (hk : I.numDays < k) : I.HasKFairSchedule k ↔ IsEmpty I.Client := by
  constructor
  · rintro ⟨σ, -, hfair⟩
    refine ⟨fun j => ?_⟩
    have hk' : k ≤ served σ j := hfair j
    have hle := served_le_numDays σ j
    omega
  · intro he
    refine ⟨fun _ => ∅, ?_, ?_⟩
    · intro i j hj
      simp at hj
    · intro j
      exact (he.false j).elim

end Lax117284Proofs.Model.Instance
