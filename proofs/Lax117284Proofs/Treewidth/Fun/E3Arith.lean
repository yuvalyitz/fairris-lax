import Mathlib.Tactic

/-!
# WP E3 (assembly, part 2): the pure arithmetic of the final cost bound
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E3C

theorem final_arith (W X M G Ω Sn c : ℕ) (hW : 1 ≤ W) (hX : 1 ≤ X)
    (hG : G ≤ 2 * X) (hΩ : Ω ≤ 2 * X) (hM : M ≤ 4 * W ^ 2) (hSn : Sn ≤ 208 * W ^ 3) (hc : 3 * c - 1 ≤ 3 * W) :
    (100 * (1000 * W * W * (3 * M) * G) + 4 * (1000 * (W * Ω) * W * G) + 500 * (W * G) + 1000 * W) * (3 * c - 1) +
      (G * (6200 * (Sn + 1) ^ 5 + 40 * Sn + 80) + 100) ≤ 10 ^ 16 * W ^ 15 * X ^ 2 := by
  have hW2 : W ≤ W ^ 4 := by
    calc W = W ^ 1 := (pow_one W).symm
      _ ≤ W ^ 4 := Nat.pow_le_pow_right hW (by norm_num)
  have hW4 : W * W = W ^ 2 := by ring
  have hW2' : W ^ 2 ≤ W ^ 4 := Nat.pow_le_pow_right hW (by norm_num)
  have hX2 : X ≤ X ^ 2 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 2 := Nat.pow_le_pow_right hX (by norm_num)
  -- the pieces of Q₀
  have a1 : 100 * (1000 * W * W * (3 * M) * G) ≤ 2400000 * (W ^ 4 * X) := by
    have : W * W * M * G ≤ W * W * (4 * W ^ 2) * (2 * X) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) hG
    nlinarith
  have a2 : 4 * (1000 * (W * Ω) * W * G) ≤ 16000 * (W ^ 2 * X ^ 2) := by
    have : W * Ω * W * G ≤ W * (2 * X) * W * (2 * X) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hΩ) le_rfl) hG
    nlinarith
  have a3 : 500 * (W * G) ≤ 1000 * (W * X) := by nlinarith
  have hWX : W * X ≤ W ^ 4 * X ^ 2 := Nat.mul_le_mul hW2 hX2
  have hW4X : W ^ 4 * X ≤ W ^ 4 * X ^ 2 := Nat.mul_le_mul_left _ hX2
  have hW2X : W ^ 2 * X ^ 2 ≤ W ^ 4 * X ^ 2 := Nat.mul_le_mul_right _ hW2'
  have hQ₀ : 100 * (1000 * W * W * (3 * M) * G) + 4 * (1000 * (W * Ω) * W * G) + 500 * (W * G) + 1000 * W ≤
      3000000 * (W ^ 4 * X ^ 2) := by
    have : W ≤ W ^ 4 * X ^ 2 := le_trans hW2 (Nat.le_mul_of_pos_right _ (by positivity))
    omega
  have hQc3 : (100 * (1000 * W * W * (3 * M) * G) + 4 * (1000 * (W * Ω) * W * G) + 500 * (W * G) + 1000 * W) * (3 * c - 1) ≤
      3000000 * (W ^ 4 * X ^ 2) * (3 * W) := Nat.mul_le_mul hQ₀ hc
  have hW5 : W ^ 4 * W = W ^ 5 := by ring
  have hW5' : W ^ 5 ≤ W ^ 15 := Nat.pow_le_pow_right hW (by norm_num)
  have b1 : (Sn + 1) ^ 5 ≤ (209 * W ^ 3) ^ 5 := Nat.pow_le_pow_left (by nlinarith [Nat.one_le_pow 3 W hW]) 5
  have b2 : (209 * W ^ 3) ^ 5 = 209 ^ 5 * W ^ 15 := by ring
  have hW3 : W ^ 3 ≤ W ^ 15 := Nat.pow_le_pow_right hW (by norm_num)
  have hW0 : 1 ≤ W ^ 15 := Nat.one_le_pow _ _ hW
  have c1 : 6200 * (Sn + 1) ^ 5 + 40 * Sn + 80 ≤ 3000000000000000 * W ^ 15 := by
    have : 6200 * (Sn + 1) ^ 5 ≤ 6200 * (209 ^ 5 * W ^ 15) := by rw [← b2]; exact Nat.mul_le_mul_left _ b1
    nlinarith
  have c2 : G * (6200 * (Sn + 1) ^ 5 + 40 * Sn + 80) ≤ 2 * X * (3000000000000000 * W ^ 15) := Nat.mul_le_mul hG c1
  have hXX : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ hX
  have e1 : 3000000 * (W ^ 4 * X ^ 2) * (3 * W) = 9000000 * (W ^ 5 * X ^ 2) := by ring
  have e2 : 2 * X * (3000000000000000 * W ^ 15) = 6000000000000000 * (W ^ 15 * X) := by ring
  have f1 : W ^ 5 * X ^ 2 ≤ W ^ 15 * X ^ 2 := Nat.mul_le_mul_right _ hW5'
  have f2 : W ^ 15 * X ≤ W ^ 15 * X ^ 2 := Nat.mul_le_mul_left _ hX2
  have f3 : 1 ≤ W ^ 15 * X ^ 2 := le_trans hW0 (Nat.le_mul_of_pos_right _ (by positivity))
  have e3 : 10 ^ 16 * W ^ 15 * X ^ 2 = 10 ^ 16 * (W ^ 15 * X ^ 2) := by ring
  rw [e3]
  omega

end E3C
end Lax117284Proofs.Treewidth.Fun
