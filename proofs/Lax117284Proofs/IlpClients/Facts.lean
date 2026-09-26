import Lax117284Proofs.IlpClients.Complete

/-!
# The rows of a normalised solution, seen through the large columns

For a normalised solution `Y` (`Sol`), the certificate digits are `dY n Y c = min (Y c) (Kn n)`.
The quantities of the decoding (`sigma`, `cp`, `Sj`) are computed here in terms of `Y` and of the
block structure of the large set `L = Lset n (dY n Y)`:

* `sigma_add`, `cp_eq`: the type rows,
* `client_row`, `Sj_eq`, `B_sub_Sj`: the client rows; `B - Sj j` is `∑_{c ∈ extras} Dm j c * Y c`.
-/

namespace Lax117284Proofs.IlpClients

open Finset
open Classical

noncomputable section

section Facts

variable {n : ℕ} {cnt : ℕ → ℕ} {B : ℕ} {Y : ℕ → ℕ} (hY : Sol n cnt B Y)

theorem dY_lt_iff {c : ℕ} : dY n Y c < Kn n ↔ Y c < Kn n := by
  unfold dY; omega

theorem dY_eq {c : ℕ} (h : Y c < Kn n) : dY n Y c = Y c := by
  unfold dY; omega

include hY in
theorem Lset_eq : Lset n (dY n Y) = (range (nN n)).filter (fun c => Kn n ≤ Y c) := by
  ext c
  simp only [mem_Lset hY, Finset.mem_filter, Finset.mem_range]

include hY in
/-- **The type rows.** -/
theorem sigma_add (t : ℕ) (ht : t < nT n) :
    sigma n (dY n Y) t + ∑ c ∈ (Lset n (dY n Y)).filter (fun c => tyOf n c = some t), Y c =
      cnt t := by
  have hrow := hY.row t (by unfold nM; omega)
  rw [rhs, if_pos ht] at hrow
  have hL : (Lset n (dY n Y)).filter (fun c => tyOf n c = some t) =
      (range (nN n)).filter (fun c => tyOf n c = some t ∧ Kn n ≤ Y c) := by
    ext c
    simp only [Finset.mem_filter, mem_Lset hY, Finset.mem_range]
    tauto
  rw [hL, Finset.sum_filter]
  unfold sigma
  rw [← hrow, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [coef_type_row n t c ht]
  by_cases h1 : tyOf n c = some t
  · by_cases h2 : Y c < Kn n
    · have h3 : ¬ Kn n ≤ Y c := by omega
      simp [h1, h2, dY_eq h2, h3]
    · have h3 : Kn n ≤ Y c := by omega
      have h4 : ¬ dY n Y c < Kn n := fun h => h2 (dY_lt_iff.mp h)
      simp [h1, h3, h4]
  · simp [h1]

include hY in
theorem cp_eq (t : ℕ) (ht : t < nT n) :
    cp n cnt (dY n Y) t = ∑ c ∈ (Lset n (dY n Y)).filter (fun c => tyOf n c = some t), Y c := by
  have := sigma_add hY t ht
  unfold cp
  omega

include hY in
/-- **The client rows.** -/
theorem client_row (j : Fin n) :
    (B : ℤ) = ∑ c ∈ range (nN n), (if Y c < Kn n then (Y c : ℤ) * ucol n c j else 0) +
      ∑ c ∈ Lset n (dY n Y), (Y c : ℤ) * ucol n c j := by
  have hrow := hY.row (nT n + j.val) (by unfold nM; omega)
  have hnt : ¬ (nT n + j.val < nT n) := by omega
  rw [rhs, if_neg hnt] at hrow
  have hrow' := congrArg (Nat.cast (R := ℤ)) hrow
  push_cast at hrow'
  rw [← hrow', Lset_eq hY, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold ucol
  by_cases h : Y c < Kn n
  · have : ¬ Kn n ≤ Y c := by omega
    simp [h, this]; ring
  · have : Kn n ≤ Y c := by omega
    simp [h, this]; ring

include hY in
theorem isBase_filter :
    (range (nN n)).filter (isBase n (dY n Y)) =
      (Lset n (dY n Y)).filter (IsB (tyOf n) (Lset n (dY n Y))) := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_range, isBase, IsB]
  constructor
  · rintro ⟨-, h1, h2, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨((mem_Lset hY).mp h1).1, h1, h2, h3⟩

include hY in
theorem Ext_eq :
    Ext n (dY n Y) = (Lset n (dY n Y)).filter (fun c => ¬ IsB (tyOf n) (Lset n (dY n Y)) c) := by
  ext c
  constructor
  · intro hc
    have hc' := Finset.mem_filter.mp hc
    have h1 : c ∈ Lset n (dY n Y) := hc'.2.1
    refine Finset.mem_filter.mpr ⟨h1, fun h => hc'.2.2 ⟨h1, h⟩⟩
  · intro hc
    have hc' := Finset.mem_filter.mp hc
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((mem_Lset hY).mp hc'.1).1,
      hc'.1, fun h => hc'.2 h.2⟩

include hY in
/-- The value of `Sj`, in terms of the block structure of `L`. -/
theorem Sj_eq (j : Fin n) :
    (Sj n cnt (dY n Y) j.val : ℤ) =
      ∑ c ∈ range (nN n), (if Y c < Kn n then (Y c : ℤ) * ucol n c j else 0) +
      ∑ c ∈ (Lset n (dY n Y)).filter (fun c => tyOf n c ≠ none),
        (Y c : ℤ) * ucol n (bs (tyOf n) (Lset n (dY n Y)) c) j := by
  unfold Sj
  push_cast
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : Y c < Kn n
    · simp [dY_eq h, h, ucol]
    · have h' : ¬ dY n Y c < Kn n := fun h' => h (dY_lt_iff.mp h')
      simp [h, h']
  · -- the bases
    set L := Lset n (dY n Y) with hL
    rw [← Finset.sum_filter, isBase_filter hY]
    have hb : ∀ b ∈ L.filter (IsB (tyOf n) L),
        ((cp n cnt (dY n Y) (tyIdx n b) : ℕ) : ℤ) * (coef n (nT n + j.val) b : ℤ) =
          (∑ c ∈ L.filter (fun c => tyOf n c ≠ none),
            if bs (tyOf n) L c = b then (Y c : ℤ) else 0) * ucol n b j := by
      intro b hbm
      have hbm' := Finset.mem_filter.mp hbm
      obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hbm'.2.1
      have hti : tyIdx n b = t := by simp [tyIdx, ht]
      have htT : t < nT n := (tyOf_some ht).2.2
      rw [hti, cp_eq hY t htT]
      unfold ucol
      congr 1
      rw [← Finset.sum_filter, Finset.filter_filter]
      have hfe := filter_bs_eq (tyOf n) L hbm'.1 hbm'.2
      rw [hfe, ht]
      push_cast
      rfl
    rw [Finset.sum_congr rfl hb]
    exact sum_regroup (tyOf n) L (fun c => (Y c : ℤ)) (fun b => ucol n b j)

include hY in
/-- **The right-hand side of the difference system.** -/
theorem B_sub_Sj (j : Fin n) :
    (B : ℤ) - (Sj n cnt (dY n Y) j.val : ℤ) =
      ∑ c ∈ Ext n (dY n Y), Dm (tyOf n) (ucol n) (Lset n (dY n Y)) j c * (Y c : ℤ) := by
  rw [client_row hY j, Sj_eq hY j, Ext_eq hY]
  rw [sum_filter_nonbase (tyOf n) (Lset n (dY n Y)) _ (fun c hc => by
    rw [Dm_base (tyOf n) (ucol n) _ hc.1 hc.2 j]; ring)]
  rw [sum_Dm]
  ring

end Facts

end

end Lax117284Proofs.IlpClients
