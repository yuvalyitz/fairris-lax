import Lax117284Proofs.Treewidth.Fun.E3D
import Lax117284Proofs.Treewidth.Fun.E3Arith

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# WP E3 (assembly, part 3): the `Runs` theorem for `CT.introC` with the closed-form cost

`introCCost W s = 10^16 · W^15 · 2^(128 s³)` with `W = U + 1` (`U ≥` all sizes and naturals of the input) and
`s = |B| + kmax + 2`: polynomial in the size times `2^{O((|B|+kmax+2)^3)}`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E3C

open ToVal Lax117284Proofs.Treewidth.Chars CT

/-- the closed-form cost bound of `introC` -/
def introCCost (W s : ℕ) : ℕ := 10 ^ 16 * W ^ 15 * 2 ^ (128 * s ^ 3)

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem introC_runs_wf (kmax v : ℕ) (N : Finset ℕ) (t : CT) (Bs : Finset ℕ) (hw : t.Wf Bs kmax)
    (U : ℕ) (hU : sz t ≤ U) (hM : mx t ≤ U) (hv : v ≤ U) (hN : N.card ≤ U) (hk : kmax ≤ U)
    (hnorm : ∀ (c : CT) (s : ℕ), sz c ≤ s → 14000 * (s + 1) ^ 5 < B →
      Runs Δ' B fNormId [toVal c] (toVal (norm c)) (6200 * (s + 1) ^ 5))
    (hnsz : ∀ c : CT, sz (norm c) ≤ sz c)
    (hB : introCCost (U + 1) (Bs.card + kmax + 2) < B) :
    Runs Δ' B fIntroC [toVal kmax, toVal v, toVal N, toVal t] (toVal (introC kmax v N t))
      (introCCost (U + 1) (Bs.card + kmax + 2)) := by
  have hbU : Bs.card ≤ U := by
    have h1 := card_verts_le_sz t
    rw [hw.verts_eq] at h1
    omega
  have hX1 : 1 ≤ 2 ^ (64 * (Bs.card + kmax + 2) ^ 3) := Nat.one_le_two_pow
  have hW1 : 1 ≤ U + 1 := by omega
  have hcount : count t ≤ runBound Bs.card := hw.count_le
  have hcU : count t ≤ U := le_trans (count_le_sz t) hU
  obtain ⟨hMW, hSnW⟩ := Sn_le Bs.card kmax (U + 1) (by omega) (by omega)
  have hGX := Gp_le Bs.card kmax
  have hΩX : 2 ^ Bs.card + 1 ≤ 2 * 2 ^ (64 * (Bs.card + kmax + 2) ^ 3) := by
    have h1 : 2 ^ Bs.card ≤ 2 ^ (64 * (Bs.card + kmax + 2) ^ 3) := Nat.pow_le_pow_right (by norm_num) (by
      have : Bs.card ≤ (Bs.card + kmax + 2) ^ 3 := by
        have : Bs.card ≤ Bs.card + kmax + 2 := by omega
        calc Bs.card ≤ Bs.card + kmax + 2 := this
          _ = (Bs.card + kmax + 2) ^ 1 := (pow_one _).symm
          _ ≤ (Bs.card + kmax + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega)
    omega
  have hcost := final_arith (U + 1) (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) (runBound Bs.card) (Gp Bs.card kmax)
    (2 ^ Bs.card + 1) ((2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10)) (count t)
    hW1 hX1 hGX hΩX hMW hSnW (by omega)
  have e : introCCost (U + 1) (Bs.card + kmax + 2) = 10 ^ 16 * (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 := by
    unfold introCCost
    rw [← pow_mul, show 64 * (Bs.card + kmax + 2) ^ 3 * 2 = 128 * (Bs.card + kmax + 2) ^ 3 by ring]
  rw [e] at hB ⊢
  have hBfit : 10 * U + 600 < B := by
    have : 10 * U + 600 ≤ 10 ^ 16 * (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 := by
      have h1 : 1 ≤ (U + 1) ^ 15 := Nat.one_le_pow _ _ hW1
      have h2 : U + 1 ≤ (U + 1) ^ 15 := by
        calc U + 1 = (U + 1) ^ 1 := (pow_one _).symm
          _ ≤ (U + 1) ^ 15 := Nat.pow_le_pow_right hW1 (by norm_num)
      have h3 : 1 ≤ (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 := Nat.one_le_pow _ _ hX1
      have h4 : (U + 1) ^ 15 ≤ (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 :=
        Nat.le_mul_of_pos_right _ (by omega)
      have h5 : 10 ^ 16 * (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 =
          10 ^ 16 * ((U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2) := by rw [mul_assoc]
      rw [h5]; omega
    omega
  have hBn : 14000 * (((2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10)) + 1) ^ 5 < B := by
    have h1 : (((2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10)) + 1) ^ 5 ≤ (209 * (U + 1) ^ 3) ^ 5 := by
      apply Nat.pow_le_pow_left
      generalize (2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10) = Sn at hSnW ⊢
      have := Nat.one_le_pow 3 (U + 1) hW1
      omega
    have h2 : (209 * (U + 1) ^ 3) ^ 5 = 209 ^ 5 * (U + 1) ^ 15 := by
      rw [mul_pow, ← pow_mul]
    have h3 : 14000 * (209 ^ 5 * (U + 1) ^ 15) ≤ 10 ^ 16 * (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 := by
      have : 1 ≤ (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 := Nat.one_le_pow _ _ hX1
      have h4 : (U + 1) ^ 15 ≤ (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 :=
        Nat.le_mul_of_pos_right _ (by omega)
      have h5 : 10 ^ 16 * (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 =
          10 ^ 16 * ((U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2) := by rw [mul_assoc]
      rw [h5]; norm_num; omega
    calc 14000 * (((2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10)) + 1) ^ 5
        ≤ 14000 * (209 * (U + 1) ^ 3) ^ 5 := Nat.mul_le_mul_left _ h1
      _ = 14000 * (209 ^ 5 * (U + 1) ^ 15) := by rw [h2]
      _ < B := lt_of_le_of_lt h3 hB
  have hszx : ∀ x ∈ introPlans v N t, sz x.2.2 ≤ (2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10) := by
    intro x hx
    rw [sz_ct_eq]
    exact introPlans_vsz_le v N hw x hx
  have hmain := introC_runs hΔ B U (1000 * (U + 1) * (U + 1)) (1000 * (U + 1) * (U + 1) * (3 * runBound Bs.card))
    (Gp Bs.card kmax) (2 ^ Bs.card + 1) (1000 * ((U + 1) * (2 ^ Bs.card + 1)))
    (100 * (1000 * (U + 1) * (U + 1) * (3 * runBound Bs.card) * Gp Bs.card kmax) +
      4 * (1000 * ((U + 1) * (2 ^ Bs.card + 1)) * (U + 1) * Gp Bs.card kmax) +
      500 * ((U + 1) * Gp Bs.card kmax) + 1000 * (U + 1))
    (6200 * (((2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10)) + 1) ^ 5)
    ((2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10)) Bs kmax (runBound Bs.card) v N
    le_rfl le_rfl le_rfl le_rfl hv hN
    (fun ν hg hm hc => hG_of_good Bs kmax v N ν (runBound Bs.card) rfl hg hm hc)
    (fun ν hg => hΩ_of_good Bs N ν hg) (by omega) t hU hM hw.good hw.bounded hcount
    (fun x hx => hnorm x.2.2 _ (hszx x hx) hBn)
    (fun x hx => le_trans (hnsz _) (hszx x hx))
  refine hmain.mono ?_
  exact hcost

end proofs
end E3C
end Lax117284Proofs.Treewidth.Fun
