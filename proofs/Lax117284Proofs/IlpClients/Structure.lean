import Lax117284Proofs.IlpClients.Family
import Lax117284Proofs.IlpClients.Block

/-!
# The Block Structure of the Family

The matrix `Amat n` of the family is an instance of the abstract block system of `Block.lean`:
the column `c` has the type `tyOf n c` (the type of a live pair, none for zero columns and slacks)
and the client vector `ucol n c` (the client rows of the column).  Hence
* independent column sets consist of at most one base column per type and at most `n` extra columns,
* `kernelBound_family n : KernelBound (Amat n) ((n+1)^(n+1)+1)`.
-/

namespace Lax117284Proofs.IlpClients

open Finset

/-- The constraint matrix of the integer program of `n` clients. -/
def Amat (n : ℕ) : Fin (nM n) → Fin (nN n) → ℕ := fun r c => coef n r c

/-- The kernel bound of the family. -/
def Kn (n : ℕ) : ℕ := (n + 1) ^ (n + 1) + 1


/-- The pair column `c` is live: `c` is a pair whose subset is independent for its type. -/
def liveP (n c : ℕ) : Prop := c < nV n ∧ indepB n (c / nZ n) (c % nZ n) = true

instance (n : ℕ) : DecidablePred (liveP n) := fun c => by unfold liveP; infer_instance

/-- The type of a column: the type of a live pair; none for zero columns and slacks. -/
def tyOf (n c : ℕ) : Option ℕ := if liveP n c then some (c / nZ n) else none

/-- The client part of a column (its entries in the client rows). -/
def ucol (n c : ℕ) (j : Fin n) : ℤ := (coef n (nT n + j.val) c : ℤ)

theorem coef_le_one (n r c : ℕ) : coef n r c ≤ 1 := by
  unfold coef
  split_ifs <;> omega

theorem ucol_01 (n c : ℕ) (j : Fin n) : 0 ≤ ucol n c j ∧ ucol n c j ≤ 1 := by
  unfold ucol
  have := coef_le_one n (nT n + j.val) c
  constructor <;> omega

theorem tyOf_some {n c t : ℕ} (h : tyOf n c = some t) : c < nV n ∧ t = c / nZ n ∧ t < nT n := by
  unfold tyOf at h
  split_ifs at h with hl
  · have hc := hl.1
    have ht : t = c / nZ n := (Option.some.inj h).symm
    refine ⟨hc, ht, ?_⟩
    rw [ht]
    apply Nat.div_lt_of_lt_mul
    rw [mul_comm]; exact hc

theorem coef_type_row (n r c : ℕ) (hr : r < nT n) :
    coef n r c = if tyOf n c = some r then 1 else 0 := by
  unfold coef tyOf
  by_cases hc : c < nV n
  · by_cases hi : indepB n (c / nZ n) (c % nZ n) = true
    · have hl : liveP n c := ⟨hc, hi⟩
      simp only [if_pos hc, if_pos hi, if_pos hl, if_pos hr, Option.some.injEq]
    · have hl : ¬ liveP n c := fun h => hi h.2
      simp only [if_pos hc, if_neg hi, if_neg hl]
      simp
  · have hl : ¬ liveP n c := fun h => hc h.1
    simp only [if_neg hc, if_neg hl]
    have : ¬ (nT n ≤ r ∧ c - nV n = r - nT n) := fun h => by omega
    simp [this]

section Kernel

variable (n : ℕ)

theorem sum_range_eq_sum_of_support (S : Finset ℕ) (hS : S ⊆ range (nN n)) (f : ℕ → ℤ)
    (hf : ∀ c, c ∉ S → f c = 0) : ∑ c ∈ range (nN n), f c = ∑ c ∈ S, f c := by
  symm
  exact Finset.sum_subset hS fun c _ hc => hf c hc

theorem sum_row_type (S : Finset ℕ) (hS : S ⊆ range (nN n)) (v : ℕ → ℤ)
    (hv : ∀ c, c ∉ S → v c = 0) (r : ℕ) (hr : r < nT n) :
    ∑ c ∈ range (nN n), (coef n r c : ℤ) * v c =
      ∑ c ∈ S.filter (fun c => tyOf n c = some r), v c := by
  rw [sum_range_eq_sum_of_support n S hS _ (fun c hc => by simp [hv c hc]), Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [coef_type_row n r c hr]
  split_ifs <;> simp

theorem sum_row_client (S : Finset ℕ) (hS : S ⊆ range (nN n)) (v : ℕ → ℤ)
    (hv : ∀ c, c ∉ S → v c = 0) (j : Fin n) :
    ∑ c ∈ range (nN n), (coef n (nT n + j.val) c : ℤ) * v c = ∑ c ∈ S, v c * ucol n c j := by
  rw [sum_range_eq_sum_of_support n S hS _ (fun c hc => by simp [hv c hc])]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [ucol]; ring

/-- **The kernel of the matrix, as the kernel of the block system.** -/
theorem ker_iff_bker (S : Finset ℕ) (hS : S ⊆ range (nN n)) (v : ℕ → ℤ)
    (hv : ∀ c, c ∉ S → v c = 0) :
    (∀ r < nM n, ∑ c ∈ range (nN n), (coef n r c : ℤ) * v c = 0) ↔ BKer (tyOf n) (ucol n) S v := by
  constructor
  · intro h
    refine ⟨fun t => ?_, fun j => ?_⟩
    · by_cases ht : t < nT n
      · rw [← sum_row_type n S hS v hv t ht]
        exact h t (by unfold nM; omega)
      · apply Finset.sum_eq_zero
        intro c hc
        exfalso
        have := (tyOf_some (Finset.mem_filter.mp hc).2).2.2
        exact ht this
    · rw [← sum_row_client n S hS v hv j]
      exact h (nT n + j.val) (by unfold nM; omega)
  · intro h r hr
    by_cases hrT : r < nT n
    · rw [sum_row_type n S hS v hv r hrT]
      exact h.1 r
    · have hj : r - nT n < n := by unfold nM at hr; omega
      have := h.2 ⟨r - nT n, hj⟩
      rw [← sum_row_client n S hS v hv ⟨r - nT n, hj⟩] at this
      simpa [Nat.add_sub_cancel' (not_lt.mp hrT)] using this

end Kernel

/-- **A nonzero kernel vector of the block system is a dependence of the columns.** -/
theorem dep_of_bker (n : ℕ) (S : Finset ℕ) (hSr : S ⊆ range (nN n)) (v : ℕ → ℤ)
    (hv : ∀ c, c ∉ S → v c = 0) (hbk : BKer (tyOf n) (ucol n) S v) {c0 : ℕ} (hc0 : c0 ∈ S)
    (hne : v c0 ≠ 0) : Dep (Amat n) {c : Fin (nN n) | c.val ∈ S} := by
  have hker := (ker_iff_bker n S hSr v hv).mpr hbk
  refine ⟨fun c => v c.val, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h ⟨c0, by simpa using hSr hc0⟩
    exact hne (by simpa using this)
  · intro c hc
    exact hv _ hc
  · intro i
    have := hker i.val i.isLt
    rw [← Fin.sum_univ_eq_sum_range (fun c => (coef n i.val c : ℤ) * v c)] at this
    simpa [Amat] using this

/-- **`kernelBound_family`**: every dependent set of columns of `Amat n` carries a nonzero kernel
vector with all entries of absolute value at most `(n+1)^(n+1) < Kn n`. -/
theorem kernelBound_family (n : ℕ) : KernelBound (Amat n) (Kn n) := by
  classical
  intro T ⟨v, hv0, hvT, hvk⟩
  let vh : ℕ → ℤ := fun c => if h : c < nN n then v ⟨c, h⟩ else 0
  let S : Finset ℕ := (Finset.univ.filter (fun c : Fin (nN n) => v c ≠ 0)).map
    ⟨Fin.val, Fin.val_injective⟩
  have hSr : S ⊆ range (nN n) := by
    intro c hc
    obtain ⟨c', -, rfl⟩ := Finset.mem_map.mp hc
    simpa using c'.isLt
  have hSiff : ∀ c, c ∈ S ↔ vh c ≠ 0 := by
    intro c
    constructor
    · intro hc
      obtain ⟨c', hc', rfl⟩ := Finset.mem_map.mp hc
      simpa [vh] using (Finset.mem_filter.mp hc').2
    · intro hc
      have hlt : c < nN n := by
        by_contra h; exact hc (by simp [vh, h])
      refine Finset.mem_map.mpr ⟨⟨c, hlt⟩, ?_, rfl⟩
      simpa [vh, hlt] using hc
  have hvh0 : ∀ c, c ∉ S → vh c = 0 := fun c hc => by
    by_contra h; exact hc ((hSiff c).mpr h)
  have hker : ∀ r < nM n, ∑ c ∈ range (nN n), (coef n r c : ℤ) * vh c = 0 := by
    intro r hr
    have := hvk ⟨r, hr⟩
    rw [← Fin.sum_univ_eq_sum_range (fun c => (coef n r c : ℤ) * vh c)]
    simpa [vh, Amat] using this
  have hbk := (ker_iff_bker n S hSr vh hvh0).mp hker
  have hne : S.Nonempty := by
    by_contra h
    apply hv0
    funext c
    have : ¬ (v c ≠ 0) := fun hc => h ⟨c.val, (hSiff c.val).mpr (by simpa [vh] using hc)⟩
    simpa using this
  obtain ⟨v', ⟨c0, hc0S, hc0⟩, hv'S, hbk', hbd, -⟩ :=
    block_small (tyOf n) (ucol n) (ucol_01 n) S vh hSiff hne hbk
  have hv'0 : ∀ c, c ∉ S → v' c = 0 := fun c hc => by
    by_contra h; exact hc (hv'S c h)
  have hker' := (ker_iff_bker n S hSr v' hv'0).mpr hbk'
  refine ⟨fun c => v' c.val, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h ⟨c0, by simpa using hSr hc0S⟩
    exact hc0 (by simpa using this)
  · intro c hc
    by_contra h
    have h1 : c.val ∈ S := hv'S _ h
    have h2 : vh c.val ≠ 0 := (hSiff _).mp h1
    have h3 : v c ≠ 0 := by simpa [vh] using h2
    exact hc (by by_contra hcT; exact h3 (hvT c hcT))
  · intro i
    have := hker' i.val i.isLt
    rw [← Fin.sum_univ_eq_sum_range (fun c => (coef n i.val c : ℤ) * v' c)] at this
    simpa [Amat] using this
  · intro c
    have := hbd c.val
    have h2 : |v' c.val| < ((Kn n : ℕ) : ℤ) := by
      unfold Kn; push_cast at this ⊢; linarith
    exact h2


end Lax117284Proofs.IlpClients
