import Lax117284Proofs.IlpClients.Cert

/-!
# Completeness of Alg F: Assembling the Pieces

For a normalised solution `Y` and the integer left inverse `(H, δ)` of the difference matrix of its
extras, the certificate `certOf n Y H δ` passes every guard of `decode` and decodes to `Y` itself.
-/

namespace Lax117284Proofs.IlpClients

open Finset
open Classical

noncomputable section

section Assemble

variable {n : ℕ} {cnt : ℕ → ℕ} {B : ℕ} {Y : ℕ → ℕ} (hY : Sol n cnt B Y)
  {H : ↥(Ext n (dY n Y)) → Fin n → ℤ} {δ : ℕ}

/-- `P_i - Q_i`, in the integers. -/
theorem PQ_int {c : ℕ} (hc : c ∈ Ext n (dY n Y)) :
    (Pi n cnt B (certOf n Y H δ) (rk n (dY n Y) c) : ℤ) -
      (Qi n cnt B (certOf n Y H δ) (rk n (dY n Y) c) : ℤ) =
      ∑ j : Fin n, H ⟨c, hc⟩ j * ((B : ℤ) - (Sj n cnt (dY n Y) j.val : ℤ)) := by
  unfold Pi Qi
  simp only [certOf]
  push_cast
  rw [← Finset.sum_sub_distrib]
  rw [← Fin.sum_univ_eq_sum_range (fun j => (HpOf n Y H (rk n (dY n Y) c) j : ℤ) * B +
      (HnOf n Y H (rk n (dY n Y) c) j : ℤ) * (Sj n cnt (dY n Y) j : ℤ) -
      ((HpOf n Y H (rk n (dY n Y) c) j : ℤ) * (Sj n cnt (dY n Y) j : ℤ) +
      (HnOf n Y H (rk n (dY n Y) c) j : ℤ) * B)) n]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (HpOf n Y H (rk n (dY n Y) c) j.val : ℤ) -
      (HnOf n Y H (rk n (dY n Y) c) j.val : ℤ) = H ⟨c, hc⟩ j := by
    rw [HpOf_rk hc, HnOf_rk hc, Int.toNat_sub_toNat_neg]
    simp [HcOf, hc, j.isLt]
  rw [← h1]
  ring

include hY in
/-- **The key identity**: `H (B - S) = δ Y` on the extras. -/
theorem key_identity
    (hHD : ∀ i i', ∑ j, H i j * Dmat n Y j i' = if i = i' then (δ : ℤ) else 0)
    {c : ℕ} (hc : c ∈ Ext n (dY n Y)) :
    ∑ j : Fin n, H ⟨c, hc⟩ j * ((B : ℤ) - (Sj n cnt (dY n Y) j.val : ℤ)) = δ * Y c := by
  have h1 : ∀ j : Fin n, ((B : ℤ) - (Sj n cnt (dY n Y) j.val : ℤ)) =
      ∑ c' : ↥(Ext n (dY n Y)), Dmat n Y j c' * (Y c' : ℤ) := by
    intro j
    rw [B_sub_Sj hY j]
    rw [← Finset.sum_coe_sort (Ext n (dY n Y)) (fun c' => Dm (tyOf n) (ucol n) (Lset n (dY n Y)) j c' * (Y c' : ℤ))]
    rfl
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ c' : ↥(Ext n (dY n Y)), ∑ j : Fin n, H ⟨c, hc⟩ j * (Dmat n Y j c' * (Y c' : ℤ)) =
      (if (⟨c, hc⟩ : ↥(Ext n (dY n Y))) = c' then (δ : ℤ) else 0) * (Y c' : ℤ) := by
    intro c'
    rw [← hHD ⟨c, hc⟩ c', Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl (fun c' _ => h2 c')]
  rw [Finset.sum_eq_single (⟨c, hc⟩ : ↥(Ext n (dY n Y)))]
  · simp
  · intro c' _ hne
    simp [Ne.symm hne]
  · intro h; exact absurd (Finset.mem_univ _) h

include hY in
/-- The value of an extra, and the guards at an extra. -/
theorem extra_value
    (hHD : ∀ i i', ∑ j, H i j * Dmat n Y j i' = if i = i' then (δ : ℤ) else 0)
    (hδ1 : 1 ≤ δ) {c : ℕ} (hc : c ∈ Ext n (dY n Y)) :
    Qi n cnt B (certOf n Y H δ) (rk n (dY n Y) c) ≤ Pi n cnt B (certOf n Y H δ) (rk n (dY n Y) c) ∧
    δ ∣ Pi n cnt B (certOf n Y H δ) (rk n (dY n Y) c) -
      Qi n cnt B (certOf n Y H δ) (rk n (dY n Y) c) ∧
    wcol n cnt B (certOf n Y H δ) c = Y c := by
  have h1 := PQ_int (cnt := cnt) (B := B) (H := H) (δ := δ) hc
  rw [key_identity hY hHD hc] at h1
  set P := Pi n cnt B (certOf n Y H δ) (rk n (dY n Y) c) with hP
  set Q := Qi n cnt B (certOf n Y H δ) (rk n (dY n Y) c) with hQ
  have hle : Q ≤ P := by
    have : (0 : ℤ) ≤ (δ : ℤ) * Y c := by positivity
    have h2 : (Q : ℤ) ≤ P := by linarith
    exact_mod_cast h2
  have h3 : P - Q = δ * Y c := by
    have : ((P - Q : ℕ) : ℤ) = ((δ * Y c : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hle]; exact h1
    exact_mod_cast this
  refine ⟨hle, ⟨Y c, h3⟩, ?_⟩
  unfold wcol
  show (P - Q) / δ = Y c
  rw [h3]
  exact Nat.mul_div_cancel_left _ (by omega)

/-- A type with a large column has a base column. -/
theorem base_of_hasL {t : ℕ} (h : hasL n (dY n Y) t) :
    ∃ b ∈ Lset n (dY n Y), IsB (tyOf n) (Lset n (dY n Y)) b ∧ tyOf n b = some t := by
  obtain ⟨c, hcL, hct⟩ := h
  have hτ : tyOf n c ≠ none := by rw [hct]; simp
  have := bs_isB (tyOf n) (Lset n (dY n Y)) hcL hτ
  refine ⟨bs (tyOf n) (Lset n (dY n Y)) c, this.1, this.2, ?_⟩
  rw [(bs_spec (tyOf n) (Lset n (dY n Y)) hcL).2.1, hct]

include hY in
/-- **The demand of a type** is the value of its base plus the values of its extras. -/
theorem cp_split {t b : ℕ} (ht : t < nT n) (hbL : b ∈ Lset n (dY n Y))
    (hbB : IsB (tyOf n) (Lset n (dY n Y)) b) (hbt : tyOf n b = some t) :
    (cp n cnt (dY n Y) t : ℤ) = (Y b : ℤ) +
      ∑ c ∈ (Ext n (dY n Y)).filter (fun c => tyOf n c = some t), (Y c : ℤ) := by
  have h1 := cp_eq (cnt := cnt) (B := B) hY t ht
  have h2 : (cp n cnt (dY n Y) t : ℤ) =
      ∑ c ∈ (Lset n (dY n Y)).filter (fun c => tyOf n c = some t), (Y c : ℤ) := by
    rw [h1]; push_cast; rfl
  rw [h2]
  have h3 : (Lset n (dY n Y)).filter (fun c => tyOf n c = some t) =
      (Lset n (dY n Y)).filter (fun c => tyOf n c = tyOf n b) := by
    ext c; simp [hbt]
  rw [h3, sum_type_eq (tyOf n) (Lset n (dY n Y)) hbL hbB (fun c => (Y c : ℤ))]
  congr 1
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  rw [Ext_eq hY]
  ext c
  simp only [Finset.mem_filter, hbt]
  tauto

include hY in
theorem extraSum_eq
    (hHD : ∀ i i', ∑ j, H i j * Dmat n Y j i' = if i = i' then (δ : ℤ) else 0)
    (hδ1 : 1 ≤ δ) (t : ℕ) :
    extraSum n cnt B (certOf n Y H δ) t =
      ∑ c ∈ (Ext n (dY n Y)).filter (fun c => tyOf n c = some t), Y c := by
  unfold extraSum
  rw [← Finset.sum_filter]
  have : (range (nN n)).filter (fun c => isExtra n (certOf n Y H δ).d c ∧ tyOf n c = some t) =
      (Ext n (dY n Y)).filter (fun c => tyOf n c = some t) := by
    ext c
    rw [Finset.mem_filter, Finset.mem_filter]
    unfold Ext
    rw [Finset.mem_filter]
    show _ ↔ (_ ∧ isExtra n (dY n Y) c) ∧ _
    tauto
  rw [this]
  refine Finset.sum_congr rfl fun c hc => ?_
  exact (extra_value hY hHD hδ1 (Finset.mem_filter.mp hc).1).2.2

include hY in
/-- **All guards hold.** -/
theorem guards_hold (hcard : (Ext n (dY n Y)).card ≤ n)
    (hHD : ∀ i i', ∑ j, H i j * Dmat n Y j i' = if i = i' then (δ : ℤ) else 0)
    (hδ1 : 1 ≤ δ) : Guards n cnt B (certOf n Y H δ) := by
  refine ⟨?_, hcard, ?_, ?_⟩
  · intro t ht
    have h := sigma_add hY t ht
    refine ⟨fun _ => ?_, fun hn => ?_⟩
    · show sigma n (dY n Y) t ≤ cnt t
      omega
    show sigma n (dY n Y) t = cnt t
    have : ∑ c ∈ (Lset n (dY n Y)).filter (fun c => tyOf n c = some t), Y c = 0 :=
      Finset.sum_eq_zero fun c hc => by
        exfalso
        exact hn ⟨c, (Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2⟩
    omega
  · intro c hc
    have := extra_value hY hHD hδ1 hc
    exact ⟨this.1, this.2.1⟩
  · intro t ht hL
    obtain ⟨b, hbL, hbB, hbt⟩ := base_of_hasL hL
    have h := cp_split hY ht hbL hbB hbt
    rw [extraSum_eq hY hHD hδ1 t]
    have h2 : ((∑ c ∈ (Ext n (dY n Y)).filter (fun c => tyOf n c = some t), Y c : ℕ) : ℤ) ≤
        (cp n cnt (dY n Y) t : ℤ) := by
      push_cast
      rw [h]
      have := Int.natCast_nonneg (Y b)
      linarith
    exact_mod_cast h2

include hY in
/-- **The decoding reproduces `Y`.** -/
theorem xval_eq
    (hHD : ∀ i i', ∑ j, H i j * Dmat n Y j i' = if i = i' then (δ : ℤ) else 0)
    (hδ1 : 1 ≤ δ) (c : ℕ) : xval n cnt B (certOf n Y H δ) c = Y c := by
  unfold xval
  by_cases h1 : isLive n c ∧ (certOf n Y H δ).d c < Kn n
  · rw [if_pos h1]
    have : dY n Y c < Kn n := h1.2
    exact dY_eq (dY_lt_iff.mp this)
  · rw [if_neg h1]
    by_cases h2 : isExtra n (certOf n Y H δ).d c
    · rw [if_pos h2]
      have hcE : c ∈ Ext n (dY n Y) := by
        refine Finset.mem_filter.mpr ⟨?_, h2⟩
        exact Finset.mem_range.mpr (((mem_Lset hY).mp h2.1).1)
      exact (extra_value hY hHD hδ1 hcE).2.2
    · rw [if_neg h2]
      by_cases h3 : isBase n (certOf n Y H δ).d c
      · rw [if_pos h3]
        obtain ⟨hcL, hτ, hbs⟩ := h3
        obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hτ
        have hti : tyIdx n c = t := by simp [tyIdx, ht]
        have htT : t < nT n := (tyOf_some ht).2.2
        rw [hti]
        have h := cp_split hY htT hcL ⟨hτ, hbs⟩ ht
        rw [extraSum_eq hY hHD hδ1 t]
        show cp n cnt (dY n Y) t - _ = Y c
        have h' : cp n cnt (dY n Y) t = Y c +
            ∑ c ∈ (Ext n (dY n Y)).filter (fun c => tyOf n c = some t), Y c := by
          exact_mod_cast h
        omega
      · rw [if_neg h3]
        symm
        by_contra hne
        have hnL : c ∉ Lset n (dY n Y) := fun hL => h2 ⟨hL, h3⟩
        by_cases hl : isLive n c
        · have hlt : Y c < Kn n := by
            by_contra hge
            exact hnL ((mem_Lset hY).mpr ⟨hl.1, by omega⟩)
          exact h1 ⟨hl, dY_lt_iff.mpr hlt⟩
        · exact hne (hY.dead c hl)

end Assemble

end

end Lax117284Proofs.IlpClients
