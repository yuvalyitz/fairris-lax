import Lax117284Proofs.Machine.TwViol

/-!
The conflict read off the instance word is the conflict of the instance, so the count of violations
of the machine is the count `violE` of the mathematics.
-/

namespace Lax117284Proofs.Machine.TwCf

open Lax117284.Scheduling Lax117284.InstanceEncoding
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.TwViol Lax117284Proofs.TwDigits
  Lax117284Proofs.TwMask

variable {I : Instance} {y X : List ℕ}

lemma cfN_iff (hy : EncodesInstance y I) (hXy : ∀ j < y.length, X.getD j 0 = y.getD j 0)
    {d u v : ℕ} (hd : d < I.days) (hu : u < I.clients) (hv : v < I.clients) :
    cfN X I.clients I.days d u v ↔ I.ConflictAt d u v := by
  have hlen := hy.length_eq
  have hp : ∀ u, u < I.clients → X.getD (2 + d * I.clients + u) 0 = I.pAt d u := by
    intro u hu
    have h1 : 2 + d * I.clients + u < y.length := by
      have : d * I.clients + I.clients ≤ I.days * I.clients := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hd
      have : I.days * I.clients ≤ 2 * I.days * I.clients := by nlinarith
      omega
    rw [hXy _ h1]
    have := hy.proc_eq ⟨d, hd⟩ ⟨u, hu⟩
    simp only [proc, hy.clientCount_eq] at this
    rw [this]; simp [Instance.pAt, hd, hu]
  have hq : ∀ u, u < I.clients →
      X.getD (2 + I.days * I.clients + d * I.clients + u) 0 = I.dAt d u := by
    intro u hu
    have h1 : 2 + I.days * I.clients + d * I.clients + u < y.length := by
      have : d * I.clients + I.clients ≤ I.days * I.clients := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hd
      have : I.days * I.clients + I.days * I.clients = 2 * I.days * I.clients := by ring
      omega
    rw [hXy _ h1]
    have := hy.due_eq ⟨d, hd⟩ ⟨u, hu⟩
    simp only [due, hy.clientCount_eq, hy.dayCount_eq] at this
    rw [this]; simp [Instance.dAt, hd, hu]
  unfold cfN Instance.ConflictAt
  rw [hp u hu, hp v hv, hq u hu, hq v hv]
  exact and_comm

/-- **The count of the machine is the count of the mathematics.** -/
theorem violN_eq_violE (hy : EncodesInstance y I) (hXy : ∀ j < y.length, X.getD j 0 = y.getD j 0)
    (kk : ℕ) (bl : List ℕ) (hbl : ∀ t < bl.length, bl[t]! < I.clients) (e : ℕ) :
    violN X I.clients I.days kk bl e = violE I kk bl e := by
  unfold violN violE
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  congr 1
  refine Finset.sum_congr rfl fun t2 ht2 => ?_
  have ht2' : t2 < bl.length := lt_trans (Finset.mem_range.1 ht2) ht'
  unfold cfDayN cfDay
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' := Finset.mem_range.1 hd
  have := cfN_iff hy hXy (d := d) (u := bl[t]!) (v := bl[t2]!) hd' (hbl t ht') (hbl t2 ht2')
  rw [if_congr (and_congr Iff.rfl (and_congr Iff.rfl this)) rfl rfl]

end Lax117284Proofs.Machine.TwCf
