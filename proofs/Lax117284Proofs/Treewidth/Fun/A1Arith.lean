import Lax117284Proofs.Treewidth.Fun.A1Main

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# WP A1 (5): the arithmetic of the total cost

All constants are treated symbolically: `C = 2^E` with `E` an arbitrary natural `≥ 829723`; nothing is ever evaluated.

* `cIC_le`    : `cIC M k ≤ 2^33 · (M+2)^62 · 2^(103680 (k+2)^3)`;
* `cMain_le`  : for `M = 8 (|x|+1)²`, `|x| = n² + 2`: `cMain n |x| M k + 3 ≤ K x` with `K x = C · 2^(C k³) · (|x|+1)^C`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace A1

/-- `2^(a e) ≤ 2^(b e)` for `a ≤ b` -/
theorem pw_mono (a b e : ℕ) (h : a ≤ b) : 2 ^ (a * e) ≤ 2 ^ (b * e) :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h)

theorem cIC_le (M k : ℕ) : cIC M k ≤ 2 ^ 33 * ((M + 2) ^ 62 * 2 ^ (103680 * (k + 2) ^ 3)) := by
  have hcn : E4.cnode M k = (M + 1) ^ 15 * 2 ^ (4000 * (k + 2) ^ 3) := rfl
  have hwx := E6b.cost_closed M k M
  have he8 := E4.Y_ge k
  obtain ⟨e, he⟩ : ∃ e, e = (k + 2) ^ 3 := ⟨_, rfl⟩
  rw [← he] at hcn hwx he8 ⊢
  obtain ⟨P, hP⟩ : ∃ P, P = M + 2 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 2 ^ (103680 * e) := ⟨_, rfl⟩
  rw [← hP, ← hZ]
  have hP2 : 2 ≤ P := by omega
  have hP1 : 1 ≤ P := by omega
  have hZ1 : 1 ≤ Z := by rw [hZ]; exact Nat.one_le_two_pow
  have hMP : M + 1 ≤ P := by omega
  have hMP' : M ≤ P := by omega
  -- Y = 2^e and its powers
  have hYe : e < 2 ^ e := Nat.lt_two_pow_self
  have hk2 : (k + 2) ^ 2 ≤ e := by
    rw [he]; exact Nat.pow_le_pow_right (by omega) (by norm_num)
  have hY1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hY3 : (2 ^ e) ^ 3 ≤ Z := by
    rw [hZ, ← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hY5 : (2 ^ e) ^ 5 ≤ Z := by
    rw [hZ, ← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4000 : 2 ^ (4000 * e) ≤ Z := by rw [hZ]; exact pw_mono 4000 103680 e (by norm_num)
  -- the size bound S
  have hS : sBnd k M ≤ 12 * (2 ^ e * P) := by
    unfold sBnd
    have h1 : (2 * k + 8) * (2 * k + 6) ≤ 12 * (k + 2) ^ 2 := by nlinarith [Nat.zero_le k]
    calc (2 * k + 8) * (2 * k + 6) * M ≤ (12 * (k + 2) ^ 2) * P := Nat.mul_le_mul h1 hMP'
      _ ≤ (12 * 2 ^ e) * P := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ = 12 * (2 ^ e * P) := by ring
  have hYP : 1 ≤ 2 ^ e * P := Nat.mul_le_mul hY1 hP1
  have hS1 : 2 * sBnd k M + 1 ≤ 25 * (2 ^ e * P) := by omega
  have hS2 : sBnd k M + 2 ≤ 14 * (2 ^ e * P) := by omega
  have hP62 : ∀ j, j ≤ 62 → P ^ j ≤ P ^ 62 := fun j hj => Nat.pow_le_pow_right hP1 hj
  -- T1
  have hT1 : M * E4.cnode M k ≤ P ^ 62 * Z := by
    rw [hcn]
    calc M * ((M + 1) ^ 15 * 2 ^ (4000 * e)) ≤ P * (P ^ 15 * Z) :=
          Nat.mul_le_mul hMP' (Nat.mul_le_mul (Nat.pow_le_pow_left hMP 15) h4000)
      _ = P ^ 16 * Z := by ring
      _ ≤ P ^ 62 * Z := Nat.mul_le_mul_right _ (hP62 16 (by norm_num))
  -- T2
  have hT2 : M ^ 2 * E6b.Wx M k ≤ P ^ 62 * Z := by
    rw [hwx, hZ]
    calc M ^ 2 * (M + 1) ^ 60 * 2 ^ (103680 * e) ≤ P ^ 2 * P ^ 60 * 2 ^ (103680 * e) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.pow_le_pow_left hMP' 2) (Nat.pow_le_pow_left hMP 60))
      _ = P ^ 62 * 2 ^ (103680 * e) := by rw [← pow_add]
  -- T4
  have hT4 : 400 * (2 * sBnd k M + 1) ^ 3 ≤ 6250000 * (P ^ 62 * Z) := by
    calc 400 * (2 * sBnd k M + 1) ^ 3 ≤ 400 * (25 * (2 ^ e * P)) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hS1 3)
      _ = 6250000 * (((2 ^ e) ^ 3) * P ^ 3) := by ring
      _ ≤ 6250000 * (Z * P ^ 62) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hY3 (hP62 3 (by norm_num)))
      _ = 6250000 * (P ^ 62 * Z) := by ring
  -- T6
  have hT6 : 8000 * (sBnd k M + 2) ^ 5 ≤ 4302592000 * (P ^ 62 * Z) := by
    calc 8000 * (sBnd k M + 2) ^ 5 ≤ 8000 * (14 * (2 ^ e * P)) ^ 5 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hS2 5)
      _ = 4302592000 * (((2 ^ e) ^ 5) * P ^ 5) := by ring
      _ ≤ 4302592000 * (Z * P ^ 62) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hY5 (hP62 5 (by norm_num)))
      _ = 4302592000 * (P ^ 62 * Z) := by ring
  have hW : 1 ≤ P ^ 62 * Z := Nat.mul_le_mul (Nat.one_le_pow _ _ hP1) hZ1
  unfold cIC
  omega


theorem cRound_le (M k : ℕ) : cRound M k ≤ 2 ^ 34 * ((M + 2) ^ 62 * 2 ^ (103680 * (k + 2) ^ 3)) := by
  have h := cIC_le M k
  have hP1 : 1 ≤ M + 2 := by omega
  have hZ1 : 1 ≤ 2 ^ (103680 * (k + 2) ^ 3) := Nat.one_le_two_pow
  have hP62 : M + 2 ≤ (M + 2) ^ 62 := Nat.le_self_pow (by norm_num) _
  have hW : (M + 2) ^ 62 ≤ (M + 2) ^ 62 * 2 ^ (103680 * (k + 2) ^ 3) := Nat.le_mul_of_pos_right _ hZ1
  unfold cRound
  omega

/-- the polynomial part: `n · R + …` in terms of `Q = |x| + 1` -/
theorem poly_part (n xlen k : ℕ) (hn : n ≤ xlen) :
    cMain n xlen (8 * ((xlen + 1) * (xlen + 1))) k + 3 ≤
      2 ^ 283 * ((xlen + 1) ^ 125 * 2 ^ (103680 * (k + 2) ^ 3)) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = xlen + 1 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 2 ^ (103680 * (k + 2) ^ 3) := ⟨_, rfl⟩
  have hZ1 : 1 ≤ Z := by rw [hZ]; exact Nat.one_le_two_pow
  have hR := cRound_le (8 * (Q * Q)) k
  rw [← hZ] at hR
  have hM : 8 * ((xlen + 1) * (xlen + 1)) = 8 * (Q * Q) := by rw [hQ]
  rw [hM, ← hZ, ← hQ]
  have hQ1 : 1 ≤ Q := by omega
  have hP : 8 * (Q * Q) + 2 ≤ 16 * Q ^ 2 := by nlinarith
  have hP62 : (8 * (Q * Q) + 2) ^ 62 ≤ 2 ^ 248 * Q ^ 124 := by
    calc (8 * (Q * Q) + 2) ^ 62 ≤ (16 * Q ^ 2) ^ 62 := Nat.pow_le_pow_left hP 62
      _ = 2 ^ 248 * Q ^ 124 := by
          rw [mul_pow, ← pow_mul]
          have : (16 : ℕ) = 2 ^ 4 := by norm_num
          rw [this, ← pow_mul]
  have hR2 : cRound (8 * (Q * Q)) k ≤ 2 ^ 34 * ((2 ^ 248 * Q ^ 124) * Z) :=
    le_trans hR (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hP62))
  have hnQ : n ≤ Q := by omega
  have hnR : n * cRound (8 * (Q * Q)) k ≤ 2 ^ 282 * (Q ^ 125 * Z) := by
    calc n * cRound (8 * (Q * Q)) k ≤ Q * (2 ^ 34 * ((2 ^ 248 * Q ^ 124) * Z)) := Nat.mul_le_mul hnQ hR2
      _ = (2 ^ 34 * 2 ^ 248) * (Q ^ 125 * Z) := by
          generalize 2 ^ 34 = a; generalize 2 ^ 248 = b; ring
      _ = 2 ^ 282 * (Q ^ 125 * Z) := by rw [← pow_add]
  have hQ4 : Q ^ 4 ≤ Q ^ 125 := Nat.pow_le_pow_right hQ1 (by norm_num)
  have hQ4' : Q ≤ Q ^ 4 := Nat.le_self_pow (by norm_num) _
  have hn2 : (n + 2) * (n + 2) ≤ 4 * (Q * Q) := by nlinarith
  have hsq : ((n + 2) * (n + 2)) ^ 2 ≤ 16 * Q ^ 4 := by
    calc ((n + 2) * (n + 2)) ^ 2 ≤ (4 * (Q * Q)) ^ 2 := Nat.pow_le_pow_left hn2 2
      _ = 16 * Q ^ 4 := by ring
  have hQZ : Q ^ 4 ≤ Q ^ 125 * Z := le_trans hQ4 (Nat.le_mul_of_pos_right _ hZ1)
  have hQZ' : Q ≤ Q ^ 125 * Z := le_trans hQ4' hQZ
  unfold cMain
  omega

/-- the exponent comparison `(k+2)³ ≤ 8 + 27 k³` -/
theorem cube_le (k : ℕ) : (k + 2) ^ 3 ≤ 8 + 27 * k ^ 3 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  · have h1 : k + 2 ≤ 3 * k := by omega
    have h2 : (k + 2) ^ 3 ≤ (3 * k) ^ 3 := Nat.pow_le_pow_left h1 3
    have h3 : (3 * k) ^ 3 = 27 * k ^ 3 := by ring
    omega

/-- **the total cost is within `K x`**: `C = 2^E`, `E ≥ 829723` -/
theorem cMain_le (E n xlen k : ℕ) (hE : 829723 ≤ E) (hn : n ≤ xlen) :
    cMain n xlen (8 * ((xlen + 1) * (xlen + 1))) k + 3 ≤ 2 ^ E * 2 ^ (2 ^ E * k ^ 3) * (xlen + 1) ^ (2 ^ E) := by
  have h1 := poly_part n xlen k hn
  obtain ⟨C, hC⟩ : ∃ C, C = 2 ^ E := ⟨_, rfl⟩
  rw [← hC]
  have hC1 : 2799360 ≤ C := by
    rw [hC]
    calc 2799360 ≤ 2 ^ 22 := by norm_num
      _ ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hC2 : 125 ≤ C := by omega
  have hC3 : 2 ^ (283 + 829440) ≤ C := by
    rw [hC]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcube := cube_le k
  have hZ : 2 ^ (103680 * (k + 2) ^ 3) ≤ 2 ^ 829440 * 2 ^ (C * k ^ 3) := by
    rw [← pow_add]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have : 2799360 * k ^ 3 ≤ C * k ^ 3 := Nat.mul_le_mul_right _ hC1
    omega
  have hQ : (xlen + 1) ^ 125 ≤ (xlen + 1) ^ C := Nat.pow_le_pow_right (by omega) hC2
  calc cMain n xlen (8 * ((xlen + 1) * (xlen + 1))) k + 3
      ≤ 2 ^ 283 * ((xlen + 1) ^ 125 * 2 ^ (103680 * (k + 2) ^ 3)) := h1
    _ ≤ 2 ^ 283 * ((xlen + 1) ^ C * (2 ^ 829440 * 2 ^ (C * k ^ 3))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hQ hZ)
    _ = (2 ^ 283 * 2 ^ 829440) * (2 ^ (C * k ^ 3) * (xlen + 1) ^ C) := by
        generalize 2 ^ 283 = a; generalize 2 ^ 829440 = b
        generalize 2 ^ (C * k ^ 3) = c; generalize (xlen + 1) ^ C = d
        ring
    _ = 2 ^ (283 + 829440) * (2 ^ (C * k ^ 3) * (xlen + 1) ^ C) := by rw [pow_add]
    _ ≤ C * (2 ^ (C * k ^ 3) * (xlen + 1) ^ C) := Nat.mul_le_mul_right _ hC3
    _ = C * 2 ^ (C * k ^ 3) * (xlen + 1) ^ C := by rw [mul_assoc]

end A1
end Lax117284Proofs.Treewidth.Fun
