import Mathlib.Tactic
import Lax117284.Scheduling

/-!
An instance with no day: a schedule is the empty family, so it has a `k`-fair schedule exactly when
there is no client or `k = 0`.
-/

namespace Lax117284Proofs.Machine.TwMain

open Lax117284.Scheduling

theorem hasK_days_zero (I : Instance) (hd : I.days = 0) (k : ℕ) :
    I.HasKFairSchedule k ↔ I.clients = 0 ∨ k = 0 := by
  have : IsEmpty (Fin I.days) := ⟨fun i => by have := i.2; omega⟩
  constructor
  · rintro ⟨σ, -, hf⟩
    by_cases hn : I.clients = 0
    · exact Or.inl hn
    · right
      have h : k ≤ Instance.served σ ⟨0, by omega⟩ := hf ⟨0, by omega⟩
      have h0 : Instance.served σ ⟨0, by omega⟩ = 0 := by
        simp [Instance.served]
      omega
  · rintro (hn | hk)
    · have : IsEmpty (Fin I.clients) := ⟨fun j => by have := j.2; omega⟩
      exact ⟨fun _ => ∅, fun i => isEmptyElim i, fun j => isEmptyElim j⟩
    · subst hk
      exact ⟨fun _ => ∅, fun i => isEmptyElim i, fun j => Nat.zero_le _⟩

end Lax117284Proofs.Machine.TwMain
