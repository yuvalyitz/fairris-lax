import Lax117284Proofs.IlpClients.Decode
import Lax117284Proofs.IlpClients.Adjugate

/-!
# Completeness of Alg F

If the integer program of the family is feasible, some certificate of the search space decodes to a
solution.  First `sol_of_feasible` normalises a solution (zero columns to `0`, shifting lemma with
the kernel bound `Kn n`), then the block structure of the large columns is used to build the
integer left inverse `H` (from `Adjugate.lean`) and to show that the decoding of the certificate
reproduces the normalised solution.
-/

namespace Lax117284Proofs.IlpClients

open Finset
open Classical

noncomputable section

theorem Kn_pos (n : ℕ) : 0 < Kn n := Nat.succ_pos _

/-- Zero columns of the matrix are zero in every row. -/
theorem coef_dead {n c : ℕ} (hc : c < nN n) (hd : ¬ isLive n c) (r : ℕ) : coef n r c = 0 := by
  have h1 : c < nV n := by
    by_contra h
    exact hd ⟨hc, Or.inl (not_lt.mp h)⟩
  have h2 : ¬ indepB n (c / nZ n) (c % nZ n) = true := fun h => hd ⟨hc, Or.inr ⟨h1, h⟩⟩
  unfold coef
  rw [if_pos h1, if_neg h2]

/-- A normalised solution: zero on the dead columns, all its large columns independent. -/
structure Sol (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) (Y : ℕ → ℕ) : Prop where
  row : ∀ r < nM n, ∑ c ∈ range (nN n), coef n r c * Y c = rhs n cnt B r
  dead : ∀ c, ¬ isLive n c → Y c = 0
  indep : ¬ Dep (Amat n) {c : Fin (nN n) | Kn n ≤ Y c.val}

/-- **Normalisation** (the shifting lemma with the kernel bound `Kn n`). -/
theorem sol_of_feasible {n : ℕ} {cnt : ℕ → ℕ} {B : ℕ}
    (h : ∃ y : ℕ → ℕ, ∀ r < nM n, ∑ c ∈ range (nN n), coef n r c * y c = rhs n cnt B r) :
    ∃ Y : ℕ → ℕ, Sol n cnt B Y := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨z', hz', hnd⟩ := shift (kernelBound_family n) (fun c : Fin (nN n) => y c.val)
  let Y : ℕ → ℕ := fun c => if h : c < nN n then (if isLive n c then z' ⟨c, h⟩ else 0) else 0
  refine ⟨Y, ⟨?_, ?_, ?_⟩⟩
  · intro r hr
    have h1 : ∑ c ∈ range (nN n), coef n r c * Y c =
        ∑ c : Fin (nN n), Amat n ⟨r, hr⟩ c * z' c := by
      rw [← Fin.sum_univ_eq_sum_range (fun c => coef n r c * Y c)]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hl : isLive n c.val
      · simp [Y, hl, Amat]
      · simp [coef_dead c.isLt hl r, Amat]
    rw [h1, hz' ⟨r, hr⟩, ← hy r hr, ← Fin.sum_univ_eq_sum_range (fun c => coef n r c * y c)]
    rfl
  · intro c hc
    by_cases h : c < nN n
    · simp [Y, h, hc]
    · simp [Y, h]
  · intro hd
    apply hnd
    refine hd.mono ?_
    intro c hc
    simp only [Set.mem_setOf_eq] at hc ⊢
    by_cases hl : isLive n c.val
    · simpa [Y, hl, c.isLt] using hc
    · simp [Y, hl] at hc
      exact absurd hc (by have := Kn_pos n; omega)

section Facts

variable {n : ℕ} {cnt : ℕ → ℕ} {B : ℕ} {Y : ℕ → ℕ} (hY : Sol n cnt B Y)

/-- The digits of the certificate built from `Y`. -/
def dY (n : ℕ) (Y : ℕ → ℕ) : ℕ → ℕ := fun c => min (Y c) (Kn n)

include hY in
/-- The large columns are exactly the columns below `nN n` where `Y` is at least `Kn n`. -/
theorem mem_Lset {c : ℕ} : c ∈ Lset n (dY n Y) ↔ c < nN n ∧ Kn n ≤ Y c := by
  unfold Lset dY
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hc, -, hd⟩
    exact ⟨hc, by omega⟩
  · rintro ⟨hc, hK⟩
    refine ⟨hc, ⟨hc, ?_⟩, by omega⟩
    by_contra hl
    have := hY.dead c (fun h => hl h.2)
    have := Kn_pos n
    omega

end Facts

end

end Lax117284Proofs.IlpClients
