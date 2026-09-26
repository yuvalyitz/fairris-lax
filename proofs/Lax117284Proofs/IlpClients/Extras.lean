import Lax117284Proofs.IlpClients.Complete

/-!
# Independent column sets of the family

An independent set `L` of columns of `Amat n` consists of one *base* column per type occurring in it
(the least column of the type, `IsB`), plus *extras* (the other columns, slacks included), and there
are at most `n` extras (`indep_extras_le`): the difference vectors of the extras are independent
vectors of `{0,±1}^n`.  No zero column is in an independent set (`no_zero_column`).
-/

namespace Lax117284Proofs.IlpClients

open Finset

/-- **An independent set of columns has at most `n` extras.** -/
theorem indep_extras_le (n : ℕ) (L : Finset ℕ) (hL : L ⊆ range (nN n))
    (hind : ¬ Dep (Amat n) {c : Fin (nN n) | c.val ∈ L}) :
    (L.filter (fun c => ¬ IsB (tyOf n) L c)).card ≤ n := by
  classical
  set E := L.filter (fun c => ¬ IsB (tyOf n) L c) with hE
  have hEL : E ⊆ L := Finset.filter_subset _ _
  have hind' : ∀ α : ↥E → ℤ,
      (∀ j : Fin n, ∑ c : ↥E, Dm (tyOf n) (ucol n) L j c * α c = 0) → α = 0 := by
    intro α hα
    by_contra hne
    obtain ⟨c0, hc0⟩ : ∃ c0, α c0 ≠ 0 := by
      by_contra h
      exact hne (funext fun c => by by_contra h'; exact h ⟨c, h'⟩)
    let α' : ℕ → ℤ := fun c => if h : c ∈ E then α ⟨c, h⟩ else 0
    have hk : ∀ j, ∑ c ∈ L, Dm (tyOf n) (ucol n) L j c * α' c = 0 := by
      intro j
      rw [← Finset.sum_subset hEL (fun c _ hc => by simp [α', hc])]
      rw [← Finset.sum_coe_sort E]
      simpa [α'] using hα j
    have hnb : ∀ c, α' c ≠ 0 → ¬ (tyOf n c ≠ none ∧ bs (tyOf n) L c = c) := by
      intro c hc hb
      have hcE : c ∈ E := by
        by_contra h; exact hc (by simp [α', h])
      exact (Finset.mem_filter.mp hcE).2 ⟨hb.1, hb.2⟩
    have hc0' : α' c0.val ≠ 0 := by simpa [α'] using hc0
    obtain ⟨hbk, hne0⟩ := lift_nonzero (tyOf n) (ucol n) L α' hk hnb (hEL c0.2) hc0'
    exact hind (dep_of_bker n L hL (lift (tyOf n) L α') (fun c hc => by simp [lift, hc]) hbk
      (hEL c0.2) hne0)
  obtain ⟨hcard, -⟩ := exists_left_inverse (fun j (c : ↥E) => Dm (tyOf n) (ucol n) L j c)
    (fun j c => by simpa using Dm_abs_le (tyOf n) (ucol n) (ucol_01 n) L j c) hind'
  simpa using hcard

/-- **No zero column in an independent set**: a zero column is a dependence by itself. -/
theorem no_zero_column (n : ℕ) {c : ℕ} (hc : c < nN n) (hd : ¬ (nV n ≤ c ∨ liveP n c))
    (T : Set (Fin (nN n))) (hcT : (⟨c, hc⟩ : Fin (nN n)) ∈ T) : Dep (Amat n) T := by
  refine ⟨fun c' => if c' = ⟨c, hc⟩ then 1 else 0, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h ⟨c, hc⟩
    simp at this
  · intro c' hc'
    have : c' ≠ ⟨c, hc⟩ := fun h => hc' (h ▸ hcT)
    simp [this]
  · intro i
    have hl : ¬ (nV n ≤ c ∨ liveP n c) := hd
    have hdead : ∀ r, coef n r c = 0 := fun r => by
      have := coef_dead (n := n) (c := c) hc (fun h => hl h.2) r
      exact this
    rw [Finset.sum_eq_single (⟨c, hc⟩ : Fin (nN n))]
    · simp [Amat, hdead]
    · intro c' _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h

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
