import Lax117284Proofs.Machine.D3AcceptDefs

/-!
Day-independent due dates with zero days: with no days at all every schedule is vacuously
feasible and serves every client on zero days, so a `k`-fair schedule exists exactly when the
parameter is zero or there is no client. The dynamic-program class of `D3AcceptDefs` at zero days
is therefore this simple numeric condition, with no dynamic program needed to decide it.
-/

namespace Lax117284Proofs.Machine.D3Accept

open Lax117284.Scheduling Lax117284Proofs.Machine.InstSem

/-- **With no days, a `k`-fair schedule exists exactly when the parameter is zero or there is no
client.** The unique schedule of an instance with no days serves every client on zero days. -/
theorem hasKFair_zero_days {I : Instance} (hd : I.days = 0) (k : ℕ) :
    I.HasKFairSchedule k ↔ k = 0 ∨ I.clients = 0 := by
  have hIE : IsEmpty (Fin I.days) := by rw [hd]; infer_instance
  have huniv : (Finset.univ : Finset (Fin I.days)) = ∅ := Finset.univ_eq_empty
  have hserved : ∀ σ : I.Schedule, ∀ j, I.served σ j = 0 := by
    intro σ j
    unfold Instance.served
    rw [huniv]; simp
  set σ0 : I.Schedule := fun i => (hIE.false i).elim
  have hfeas : I.Feasible σ0 := fun i => (hIE.false i).elim
  unfold Instance.HasKFairSchedule Instance.HasFairSchedule Instance.Fair
  constructor
  · rintro ⟨σ, -, hfair⟩
    rcases Nat.eq_zero_or_pos I.clients with hc | hc
    · exact Or.inr hc
    · refine Or.inl ?_
      have hj : Fin I.clients := ⟨0, hc⟩
      have hle : k ≤ I.served σ hj := hfair hj
      rw [hserved σ hj] at hle
      omega
  · intro hor
    refine ⟨σ0, hfeas, fun j => ?_⟩
    show k ≤ I.served σ0 j
    rw [hserved σ0 j]
    rcases hor with hk | hc
    · omega
    · exact absurd (hc ▸ j.isLt) (Nat.not_lt_zero j.1)

/-- **The dynamic-program class at zero days is the simple numeric condition**: the day count is
zero and either the parameter is zero or there is no client. -/
theorem decideOk_zero_iff (arr : List ℕ) :
    decideOk arr 0 ↔ arr.getD 1 0 = 0 ∧ (paramOf arr = 0 ∨ arr.getD 0 0 = 0) := by
  unfold decideOk
  constructor
  · rintro ⟨hv, -, hm, hk⟩
    exact ⟨hm, (hasKFair_zero_days (hm : (instOf arr hv).days = 0) (paramOf arr)).1 hk⟩
  · rintro ⟨hm, hdisj⟩
    have hv : Valid arr := fun t ht => by rw [hm] at ht; simp at ht
    exact ⟨hv, fun t ht => by rw [hm] at ht; simp at ht, hm,
      (hasKFair_zero_days (hm : (instOf arr hv).days = 0) (paramOf arr)).2 hdisj⟩

end Lax117284Proofs.Machine.D3Accept
