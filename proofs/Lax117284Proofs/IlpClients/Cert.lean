import Lax117284Proofs.IlpClients.Facts

/-!
# The Certificate of a Normalised Solution

Given a normalised solution `Y` (`Sol`), the extras of the large set `L` have a difference matrix
`Dmat` (`n × |Ext|`, entries `0/±1`) whose columns are independent (a nonzero relation would lift to
a dependence among the large columns, `Dmat_indep`).  By `exists_left_inverse` it has an integer
left inverse `H` with entries `≤ n!` and denominator `δ ≤ n!`; `certOf` packages the digits
`min (Y c) K`, `H = Hp - Hn` (indexed by the rank of the extra) and `δ`.
-/

namespace Lax117284Proofs.IlpClients

open Finset
open Classical

noncomputable section

section Rank

variable {n : ℕ} {d : ℕ → ℕ}

theorem rk_lt_of_lt {c c' : ℕ} (hc : isExtra n d c) (hlt : c < c') : rk n d c < rk n d c' := by
  unfold rk
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨c, ?_, ?_⟩
    · simp [hlt, hc]
    · simp
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨hx.1.trans hlt, hx.2⟩

theorem rk_inj {c c' : ℕ} (hc : isExtra n d c) (hc' : isExtra n d c') (h : rk n d c = rk n d c') :
    c = c' := by
  rcases lt_trichotomy c c' with hlt | heq | hgt
  · exact absurd h (rk_lt_of_lt hc hlt).ne
  · exact heq
  · exact absurd h (rk_lt_of_lt hc' hgt).ne'

end Rank

section Cert

variable {n : ℕ} {cnt : ℕ → ℕ} {B : ℕ} {Y : ℕ → ℕ} (hY : Sol n cnt B Y)

/-- The difference matrix of the extras. -/
def Dmat (n : ℕ) (Y : ℕ → ℕ) : Fin n → ↥(Ext n (dY n Y)) → ℤ :=
  fun j c => Dm (tyOf n) (ucol n) (Lset n (dY n Y)) j c

theorem Ext_subset_Lset (n : ℕ) (d : ℕ → ℕ) : Ext n d ⊆ Lset n d := by
  intro c hc
  exact (Finset.mem_filter.mp hc).2.1

theorem Lset_subset_range (n : ℕ) (d : ℕ → ℕ) : Lset n d ⊆ range (nN n) :=
  Finset.filter_subset _ _

include hY in
theorem Dmat_indep :
    ∀ α : ↥(Ext n (dY n Y)) → ℤ, (∀ j : Fin n, ∑ c, Dmat n Y j c * α c = 0) → α = 0 := by
  intro α hα
  by_contra hne
  obtain ⟨c0, hc0⟩ : ∃ c0, α c0 ≠ 0 := by
    by_contra h
    exact hne (funext fun c => by by_contra h'; exact h ⟨c, h'⟩)
  set L := Lset n (dY n Y) with hL
  let α' : ℕ → ℤ := fun c => if h : c ∈ Ext n (dY n Y) then α ⟨c, h⟩ else 0
  have hExtL : Ext n (dY n Y) ⊆ L := Ext_subset_Lset n _
  have hk : ∀ j, ∑ c ∈ L, Dm (tyOf n) (ucol n) L j c * α' c = 0 := by
    intro j
    rw [← Finset.sum_subset hExtL (fun c _ hc => by simp [α', hc])]
    rw [← Finset.sum_coe_sort (Ext n (dY n Y))]
    have := hα j
    simp only [Dmat] at this
    simpa [α'] using this
  have hnb : ∀ c, α' c ≠ 0 → ¬ (tyOf n c ≠ none ∧ bs (tyOf n) L c = c) := by
    intro c hc hb
    have hcE : c ∈ Ext n (dY n Y) := by
      by_contra h; exact hc (by simp [α', h])
    rw [Ext_eq hY] at hcE
    exact (Finset.mem_filter.mp hcE).2 ⟨hb.1, hb.2⟩
  have hc0' : α' c0.val ≠ 0 := by simpa [α'] using hc0
  obtain ⟨hbk, hne0⟩ := lift_nonzero (tyOf n) (ucol n) L α' hk hnb (hExtL c0.2) hc0'
  have hdep := dep_of_bker n L (Lset_subset_range n _) (lift (tyOf n) L α')
    (fun c hc => by simp [lift, hc]) hbk (hExtL c0.2) hne0
  apply hY.indep
  convert hdep using 1
  ext c
  simp only [Set.mem_setOf_eq]
  exact ⟨fun h => (mem_Lset hY).mpr ⟨c.isLt, h⟩, fun h => ((mem_Lset hY).mp h).2⟩

theorem Dmat_abs_le (j : Fin n) (c : ↥(Ext n (dY n Y))) : |Dmat n Y j c| ≤ 1 := by
  have := Dm_abs_le (tyOf n) (ucol n) (ucol_01 n) (Lset n (dY n Y)) j c
  simpa [Dmat] using this

end Cert

section Build

variable {n : ℕ} {cnt : ℕ → ℕ} {B : ℕ} {Y : ℕ → ℕ}

/-- The integer left inverse `H`, as a matrix indexed by columns and clients (zero elsewhere). -/
def HcOf (n : ℕ) (Y : ℕ → ℕ) (H : ↥(Ext n (dY n Y)) → Fin n → ℤ) (c j : ℕ) : ℤ :=
  if h : c ∈ Ext n (dY n Y) then (if hj : j < n then H ⟨c, h⟩ ⟨j, hj⟩ else 0) else 0

/-- The positive part of `H`, indexed by the rank of the extra. -/
def HpOf (n : ℕ) (Y : ℕ → ℕ) (H : ↥(Ext n (dY n Y)) → Fin n → ℤ) (i j : ℕ) : ℕ :=
  if h : ∃ c ∈ Ext n (dY n Y), rk n (dY n Y) c = i then
    (HcOf n Y H (Classical.choose h) j).toNat else 0

/-- The negative part of `H`, indexed by the rank of the extra. -/
def HnOf (n : ℕ) (Y : ℕ → ℕ) (H : ↥(Ext n (dY n Y)) → Fin n → ℤ) (i j : ℕ) : ℕ :=
  if h : ∃ c ∈ Ext n (dY n Y), rk n (dY n Y) c = i then
    (-(HcOf n Y H (Classical.choose h) j)).toNat else 0

/-- The certificate of a normalised solution. -/
def certOf (n : ℕ) (Y : ℕ → ℕ) (H : ↥(Ext n (dY n Y)) → Fin n → ℤ) (δ : ℕ) : Cert :=
  ⟨dY n Y, HpOf n Y H, HnOf n Y H, δ⟩

theorem isExtra_of_mem_Ext {d : ℕ → ℕ} {c : ℕ} (h : c ∈ Ext n d) : isExtra n d c :=
  (Finset.mem_filter.mp h).2

theorem choose_rk {H : ↥(Ext n (dY n Y)) → Fin n → ℤ} {c : ℕ} (hc : c ∈ Ext n (dY n Y)) :
    Classical.choose (⟨c, hc, rfl⟩ : ∃ c' ∈ Ext n (dY n Y), rk n (dY n Y) c' = rk n (dY n Y) c) =
      c := by
  have hspec := Classical.choose_spec
    (⟨c, hc, rfl⟩ : ∃ c' ∈ Ext n (dY n Y), rk n (dY n Y) c' = rk n (dY n Y) c)
  exact rk_inj (isExtra_of_mem_Ext hspec.1) (isExtra_of_mem_Ext hc) hspec.2

theorem HpOf_rk {H : ↥(Ext n (dY n Y)) → Fin n → ℤ} {c : ℕ} (hc : c ∈ Ext n (dY n Y)) (j : ℕ) :
    HpOf n Y H (rk n (dY n Y) c) j = (HcOf n Y H c j).toNat := by
  have h : ∃ c' ∈ Ext n (dY n Y), rk n (dY n Y) c' = rk n (dY n Y) c := ⟨c, hc, rfl⟩
  unfold HpOf
  rw [dif_pos h]
  rw [choose_rk (H := H) hc]

theorem HnOf_rk {H : ↥(Ext n (dY n Y)) → Fin n → ℤ} {c : ℕ} (hc : c ∈ Ext n (dY n Y)) (j : ℕ) :
    HnOf n Y H (rk n (dY n Y) c) j = (-(HcOf n Y H c j)).toNat := by
  have h : ∃ c' ∈ Ext n (dY n Y), rk n (dY n Y) c' = rk n (dY n Y) c := ⟨c, hc, rfl⟩
  unfold HnOf
  rw [dif_pos h]
  rw [choose_rk (H := H) hc]

theorem HcOf_abs_le {H : ↥(Ext n (dY n Y)) → Fin n → ℤ} {b : ℤ} (hH : ∀ i j, |H i j| ≤ b)
    (hb : 0 ≤ b) (c j : ℕ) : |HcOf n Y H c j| ≤ b := by
  unfold HcOf
  split_ifs
  · exact hH _ _
  · simpa using hb
  · simpa using hb

theorem toNat_le_of_abs {x b : ℤ} (h : |x| ≤ b) : (x.toNat : ℤ) ≤ b := by
  have : (x.toNat : ℤ) ≤ |x| := by
    rcases le_or_gt 0 x with hx | hx
    · rw [Int.toNat_of_nonneg hx, abs_of_nonneg hx]
    · rw [Int.toNat_of_nonpos hx.le]; simp
  linarith

theorem inBox_certOf {H : ↥(Ext n (dY n Y)) → Fin n → ℤ} {δ : ℕ}
    (hδ1 : 1 ≤ δ) (hδn : δ ≤ n.factorial) (hH : ∀ i j, |H i j| ≤ (n.factorial : ℤ)) :
    InBox n (certOf n Y H δ) := by
  refine ⟨fun c _ => ?_, fun i _ j _ => ?_, hδ1, hδn⟩
  · exact min_le_right _ _
  · have hb : (0 : ℤ) ≤ n.factorial := by positivity
    have hHc := HcOf_abs_le (Y := Y) hH hb
    constructor
    · show HpOf n Y H i j ≤ n.factorial
      unfold HpOf
      split_ifs with h
      · have := toNat_le_of_abs (hHc (Classical.choose h) j)
        exact_mod_cast this
      · exact Nat.zero_le _
    · show HnOf n Y H i j ≤ n.factorial
      unfold HnOf
      split_ifs with h
      · have := toNat_le_of_abs (b := (n.factorial : ℤ)) (by
          rw [abs_neg]; exact hHc (Classical.choose h) j)
        exact_mod_cast this
      · exact Nat.zero_le _

end Build

end

end Lax117284Proofs.IlpClients
