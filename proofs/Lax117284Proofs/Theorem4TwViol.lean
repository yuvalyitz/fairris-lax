import Lax117284Proofs.Theorem4TwDP

/-!
# Counting the Violations of a Restriction

The dynamic program decides whether a restriction is feasible and fair by counting: `violE` is the
number of clients served fewer than `kk` times plus the number of triples of a day and two
clients of the bag that are both served on that day and conflict. It is zero exactly when
`feasE` and `fairE` hold, and it is a sum of terms, so the machine can accumulate it in one scalar
through three nested loops.
-/

namespace Lax117284Proofs.TwViol

open Lax117284Proofs.TwDigits Lax117284Proofs.TwMask Lax117284Proofs.TwDP

variable (I : Lax117284.Scheduling.Instance) (kk : ℕ)

/-- The number of days on which both digits `a` and `a'` have the day and the clients `u`, `u'`
conflict on it. -/
def cfDay (u u' a a' : ℕ) : ℕ :=
  ∑ d ∈ Finset.range I.days, if a.testBit d = true ∧ a'.testBit d = true ∧ I.ConflictAt d u u'
    then 1 else 0

/-- **The number of violations of a restriction.** -/
def violE (bl : List ℕ) (e : ℕ) : ℕ :=
  ∑ t ∈ Finset.range bl.length,
    ((if kk ≤ popc I.days (dg (2 ^ I.days) e t) then 0 else 1) +
      ∑ t' ∈ Finset.range t,
        cfDay I bl[t]! bl[t']! (dg (2 ^ I.days) e t) (dg (2 ^ I.days) e t'))

lemma cfDay_eq_zero {u u' a a' : ℕ} :
    cfDay I u u' a a' = 0 ↔
      ∀ d < I.days, a.testBit d = true → a'.testBit d = true → ¬ I.ConflictAt d u u' := by
  unfold cfDay
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h d hd h1 h2 h3
    have := h d (Finset.mem_range.2 hd)
    simp [h1, h2, h3] at this
  · intro h d hd
    have hd' := Finset.mem_range.1 hd
    by_cases hc : a.testBit d = true ∧ a'.testBit d = true ∧ I.ConflictAt d u u'
    · exact absurd hc.2.2 (h d hd' hc.1 hc.2.1)
    · simp [hc]

/-- **The count is zero exactly when the restriction is feasible and fair.** -/
lemma violE_eq_zero (bl : List ℕ) (e : ℕ) :
    violE I kk bl e = 0 ↔ feasE I bl e ∧ fairE I kk bl e := by
  unfold violE feasE fairE
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h
    have h' : ∀ t < bl.length, (if kk ≤ popc I.days (dg (2 ^ I.days) e t) then 0 else 1) = 0 ∧
        ∑ t' ∈ Finset.range t, cfDay I bl[t]! bl[t']! (dg (2 ^ I.days) e t)
          (dg (2 ^ I.days) e t') = 0 := by
      intro t ht
      have := h t (Finset.mem_range.2 ht)
      omega
    refine ⟨fun d hd t ht t' ht' hb hb' => ?_, fun t ht => ?_⟩
    · have h2 := (h' t ht).2
      rw [Finset.sum_eq_zero_iff] at h2
      have h3 := h2 t' (Finset.mem_range.2 ht')
      exact (cfDay_eq_zero I).1 h3 d hd hb hb'
    · have := (h' t ht).1
      by_cases hh : kk ≤ popc I.days (dg (2 ^ I.days) e t)
      · exact hh
      · rw [if_neg hh] at this; omega
  · rintro ⟨hF, hR⟩ t ht
    have ht' := Finset.mem_range.1 ht
    have h1 : (if kk ≤ popc I.days (dg (2 ^ I.days) e t) then 0 else 1) = 0 := by
      rw [if_pos (hR t ht')]
    have h2 : ∑ t' ∈ Finset.range t, cfDay I bl[t]! bl[t']! (dg (2 ^ I.days) e t)
        (dg (2 ^ I.days) e t') = 0 := by
      rw [Finset.sum_eq_zero_iff]
      intro t' ht''
      exact (cfDay_eq_zero I).2 fun d hd hb hb' => hF d hd t ht' t' (Finset.mem_range.1 ht'')
        hb hb'
    rw [h1, h2]; rfl

/-- A fold that adds a term at every step is the sum. -/
lemma foldl_add_range (f : ℕ → ℕ) (a₀ : ℕ) :
    ∀ N, (List.range N).foldl (fun a j => a + f j) a₀ = a₀ + ∑ j ∈ Finset.range N, f j
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_add_range f a₀ N, Finset.sum_range_succ]
    simp; ring

end Lax117284Proofs.TwViol
