import Lax117284Proofs.D3Tab

/-!
The reachable states depend on the processing times and due dates only through their values on
the clients that have been served and the days there are: two choices of these functions that
agree there give the same sets.
-/

namespace Lax117284Proofs.D3Congr

open Lax117284Proofs.D3DP Lax117284Proofs.D3Tab

variable {m k n : ℕ}

/-- **The reachable states after `c` clients agree for functions that agree below `c`.** -/
theorem reach_congr {q1 q2 : ℕ → ℕ → ℕ} {e1 e2 : ℕ → ℕ}
    (hq : ∀ i < m, ∀ c < n, q1 i c = q2 i c) (he : ∀ c < n, e1 c = e2 c) :
    ∀ c ≤ n, Reach m k q1 e1 c = Reach m k q2 e2 c
  | 0, _ => rfl
  | c + 1, hc => by
    have ih : Reach m k q1 e1 c = Reach m k q2 e2 c := reach_congr hq he c (by omega)
    have hfeas : ∀ v : Vec m, (∀ x, v x ≤ c) → ∀ i : Fin m,
        feas m q1 e1 c v i = feas m q2 e2 c v i := by
      intro v hv i
      unfold feas fv
      rw [hq i i.isLt c (by omega), he c (by omega)]
      by_cases h0 : v i = 0
      · simp [h0]
      · have hlt : v i - 1 < n := by have := hv i; omega
        rw [he _ hlt]
    ext v'
    simp only [Reach]
    constructor
    · rintro ⟨v, hv, S, hS, hf, rfl⟩
      have hb := reach_le (m := m) (k := k) (q := q1) (e := e1) c v hv
      refine ⟨v, ih ▸ hv, S, hS, fun i hi => ?_, rfl⟩
      rw [← hfeas v hb i]; exact hf i hi
    · rintro ⟨v, hv, S, hS, hf, rfl⟩
      have hb := reach_le (m := m) (k := k) (q := q2) (e := e2) c v hv
      refine ⟨v, ih ▸ hv, S, hS, fun i hi => ?_, rfl⟩
      rw [hfeas v hb i]; exact hf i hi

end Lax117284Proofs.D3Congr
