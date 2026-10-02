import Lax117284Proofs.Treewidth.Fun.E3C3
import Lax117284Proofs.Treewidth.Size.Plans

/-!
# WP E3 (assembly, part 1): discharging the length hypotheses of `introPlans_runs` with the bounds of P1

For a well-formed characteristic `t` (`Wf Bs kmax t`), with `b = |Bs|` and `M = runBound b`:

* `AM = (4·kmax+3)·(4·kmax+4)^(2M) + (2^b+1)^(b+2)·(4·kmax+3)`,
* `G = M·AM + 1`, `Ω = 2^b + 1`,

and every sub-run-tree `ν` (`Good Bs ν`, `maxEntry ν ≤ kmax`, `count ν ≤ M`) satisfies the hypotheses `hG`, `hΩ` of
`introPlans_runs` (`wtopPlans`, `allChains`, `attachPlans`, `introPlans` have fewer than `G` elements,
`chainCands` fewer than `Ω`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E3C

open ToVal Lax117284Proofs.Treewidth.Chars CT

/-- `A_M` of `introPlans_length_le_aux` -/
def AM (b kmax : ℕ) : ℕ :=
  (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * runBound b) + (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3)

/-- the uniform length bound -/
def Gp (b kmax : ℕ) : ℕ := runBound b * AM b kmax + 1

theorem runBound_pos (b : ℕ) : 1 ≤ runBound b := by unfold runBound; nlinarith

theorem hG_of_good (Bs : Finset ℕ) (kmax v : ℕ) (N : Finset ℕ) (ν : CT) (M : ℕ) (hM : M = runBound Bs.card)
    (hg : Good Bs ν) (hm : maxEntry ν ≤ kmax) (hc : count ν ≤ M) :
    (wtopPlans v ν).length + 1 ≤ Gp Bs.card kmax ∧ (allChains ν.S N).length + 1 ≤ Gp Bs.card kmax ∧
      (attachPlans v N ν).length ≤ Gp Bs.card kmax ∧ (introPlans v N ν).length ≤ Gp Bs.card kmax := by
  subst hM
  set b := Bs.card with hb
  have hM1 := runBound_pos b
  have hAM : (2 ^ b + 1) ^ (b + 2) ≤ AM b kmax := by
    unfold AM
    have : (2 ^ b + 1) ^ (b + 2) ≤ (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hAM2 : (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3) ≤ AM b kmax := by unfold AM; omega
  have hMA : AM b kmax ≤ runBound b * AM b kmax := Nat.le_mul_of_pos_left _ hM1
  have hbS : ∀ S : Finset ℕ, S ⊆ Bs → S.card ≤ b := fun S h => Finset.card_le_card h
  cases ν with
  | node S y ks =>
    have hS : S.card ≤ b := hbS S hg.label_sub
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h1 := wtopPlans_length_le v kmax Bs hg hm
      have h2 : (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * count (node S y ks) - 1) ≤
          (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * runBound b) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      have h3 : (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * runBound b) ≤ AM b kmax := by unfold AM; omega
      unfold Gp; omega
    · have h1 := allChains_length_le (S := S) N hS
      show (allChains S N).length + 1 ≤ Gp b kmax
      unfold Gp; omega
    · have h1 := attachPlans_length_le v kmax Bs N hg hm (b := b) (t := node S y ks) hS
      unfold Gp; omega
    · have h1 := introPlans_length_le_aux v kmax Bs N (runBound b) b hbS (node S y ks) hg hm hc
      have h2 : count (node S y ks) * ((4 * kmax + 3) * (4 * kmax + 4) ^ (2 * runBound b) +
          (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3)) ≤ runBound b * AM b kmax :=
        Nat.mul_le_mul_right _ hc
      unfold Gp; unfold AM at h2 ⊢; omega

/-- `M · A_M ≤ 2^(64 (b+kmax+2)^3)` (the computation inside `introPlans_length_le`) -/
theorem M_AM_le (b kmax : ℕ) : runBound b * AM b kmax ≤ 2 ^ (64 * (b + kmax + 2) ^ 3) := by
  unfold AM
  set M := runBound b with hM
  have hM1 : M ≤ 2 ^ (2 * b + 2) := by
    rw [hM]; unfold runBound
    have h1 : (b + 1) ≤ 2 ^ b := succ_le_two_pow b
    have h2 : (2 * b + 2) * (2 * b + 2) = 4 * ((b + 1) * (b + 1)) := by ring
    have h3 : (b + 1) * (b + 1) ≤ 2 ^ b * 2 ^ b := Nat.mul_le_mul h1 h1
    have h4 : 2 ^ (2 * b + 2) = 4 * (2 ^ b * 2 ^ b) := by
      rw [show 2 * b + 2 = b + b + 2 by ring, pow_add, pow_add]; ring
    rw [h2, h4]
    omega
  have hK : (4 * kmax + 4) ^ (2 * M) ≤ 2 ^ ((kmax + 2) * (2 * M)) := by
    rw [pow_mul 2 (kmax + 2) (2 * M)]
    exact Nat.pow_le_pow_left (four_mul_le kmax) _
  have hC : (2 ^ b + 1) ^ (b + 2) ≤ 2 ^ ((b + 1) * (b + 2)) := by
    have : 2 ^ b + 1 ≤ 2 ^ (b + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := b); omega
    calc (2 ^ b + 1) ^ (b + 2) ≤ (2 ^ (b + 1)) ^ (b + 2) := Nat.pow_le_pow_left this _
      _ = _ := by rw [← pow_mul]
  have h34 : 4 * kmax + 3 ≤ 2 ^ (kmax + 2) := le_trans (by omega) (four_mul_le kmax)
  set E1 := (kmax + 2) * (2 * M)
  set E2 := (b + 1) * (b + 2)
  have hA : (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * M) + (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3) ≤
      2 ^ (kmax + 2) * 2 ^ (E1 + E2 + 1) := by
    have a1 : (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * M) ≤ 2 ^ (kmax + 2) * 2 ^ E1 := Nat.mul_le_mul h34 hK
    have a2 : (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3) ≤ 2 ^ E2 * 2 ^ (kmax + 2) := Nat.mul_le_mul hC h34
    have b1 : 2 ^ E1 ≤ 2 ^ (E1 + E2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have b2 : 2 ^ E2 ≤ 2 ^ (E1 + E2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ (E1 + E2 + 1) = 2 * 2 ^ (E1 + E2) := by rw [pow_succ]; ring
    rw [this]
    nlinarith [Nat.mul_le_mul_left (2 ^ (kmax + 2)) b1, Nat.mul_le_mul_left (2 ^ (kmax + 2)) b2]
  calc M * ((4 * kmax + 3) * (4 * kmax + 4) ^ (2 * M) + (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3))
      ≤ 2 ^ (2 * b + 2) * (2 ^ (kmax + 2) * 2 ^ (E1 + E2 + 1)) := Nat.mul_le_mul hM1 hA
    _ = 2 ^ ((2 * b + 2) + (kmax + 2) + (E1 + E2 + 1)) := by rw [← pow_add, ← pow_add]; congr 1; omega
    _ ≤ 2 ^ (64 * (b + kmax + 2) ^ 3) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have := intro_exponent_le b kmax
      omega

theorem Gp_le (b kmax : ℕ) : Gp b kmax ≤ 2 * 2 ^ (64 * (b + kmax + 2) ^ 3) := by
  have h1 := M_AM_le b kmax
  have h2 : 1 ≤ 2 ^ (64 * (b + kmax + 2) ^ 3) := Nat.one_le_two_pow
  unfold Gp; omega

theorem Sn_le (b kmax W : ℕ) (hb : b + 1 ≤ W) (hk : kmax + 1 ≤ W) :
    runBound b ≤ 4 * W ^ 2 ∧
      (2 * runBound b + b + 4) * (2 * b + 4 * kmax + 10) ≤ 208 * W ^ 3 := by
  have hW1 : 1 ≤ W := by omega
  have hM : runBound b ≤ 4 * W ^ 2 := by
    unfold runBound
    have : 2 * b + 2 ≤ 2 * W := by omega
    have h2 := Nat.mul_le_mul this this
    nlinarith
  refine ⟨hM, ?_⟩
  have h1 : 2 * runBound b + b + 4 ≤ 13 * W ^ 2 := by
    have : W ≤ W ^ 2 := by nlinarith
    have : 1 ≤ W ^ 2 := Nat.one_le_pow _ _ hW1
    omega
  have h2 : 2 * b + 4 * kmax + 10 ≤ 16 * W := by omega
  calc (2 * runBound b + b + 4) * (2 * b + 4 * kmax + 10) ≤ (13 * W ^ 2) * (16 * W) := Nat.mul_le_mul h1 h2
    _ = 208 * W ^ 3 := by ring

theorem hΩ_of_good (Bs : Finset ℕ) (N : Finset ℕ) (ν : CT) (hg : Good Bs ν) :
    (chainCands ν.S N).length + 1 ≤ 2 ^ Bs.card + 1 := by
  cases ν with
  | node S y ks =>
    have hS : S.card ≤ Bs.card := Finset.card_le_card hg.label_sub
    show (chainCands S N).length + 1 ≤ 2 ^ Bs.card + 1
    have : (chainCands S N).length = 2 ^ (S \ N).card := by simp [chainCands, List.length_sublists]
    rw [this]
    have h2 : (S \ N).card ≤ Bs.card := le_trans (Finset.card_le_card Finset.sdiff_subset) hS
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h2
    omega

end E3C
end Lax117284Proofs.Treewidth.Fun
