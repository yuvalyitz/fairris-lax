import Lax117284Proofs.IlpClients.Complete

/-!
# Independent Column Sets of the Family

An independent set `L` of columns of `Amat n` consists of one *base* column per type occurring in it
(the least column of the type, `IsB`), plus *extras* (the other columns, slacks included), and there
are at most `n` extras (`indep_extras_le`): the difference vectors of the extras are independent
vectors of `{0,±1}^n`.  No zero column is in an independent set (`no_zero_column`).
-/

namespace Lax117284Proofs.IlpClients

open Finset



/-- The large columns: the live columns with digit `K`. -/
theorem mem_Lset_iff (n : ℕ) (d : ℕ → ℕ) (c : ℕ) :
    c ∈ Lset n d ↔ isLive n c ∧ d c = Kn n := by
  unfold Lset
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨h.1.1, h⟩⟩

/-- **The base of a type is its first large column**: `c` is a base if it is a large typed column
and no earlier large column has the same type. -/
theorem isBase_iff (n : ℕ) (d : ℕ → ℕ) (c : ℕ) :
    isBase n d c ↔ c ∈ Lset n d ∧ tyOf n c ≠ none ∧
      ∀ c' < c, c' ∈ Lset n d → tyOf n c' ≠ tyOf n c := by
  unfold isBase
  constructor
  · rintro ⟨hc, hτ, hbs⟩
    refine ⟨hc, hτ, fun c' hlt hc' h => ?_⟩
    have := (isB_iff (tyOf n) (Lset n d) hc).mp ⟨hτ, hbs⟩
    exact absurd (this.2 c' hc' h) (not_le.mpr hlt)
  · rintro ⟨hc, hτ, h⟩
    refine ⟨hc, hτ, ?_⟩
    have := (isB_iff (tyOf n) (Lset n d) hc).mpr ⟨hτ, fun c' hc' h' => by
      by_contra hlt
      exact h c' (not_le.mp hlt) hc' h'⟩
    exact this.2

end Lax117284Proofs.IlpClients
