import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lax117284Proofs.Treewidth.Fun.E4Steps

set_option linter.unusedSectionVars false

/-!
# WP E4 (2): the arithmetic of the per-node cost bound

`cnode M k = (M+1)^15 · 2^(4000 (k+2)^3)`.  With `Y = (k+2)^3 ≥ 8` every polynomial factor `128 Y + 1`, every numeral
constant and every quantity `L = 2^(a Y)` is a power of two, so each node bound is a chain of `2^_ ≤ 2^_`.
All lemmas are stated for an abstract `Y ≥ 8` (the exponent shapes are the ones the P1 bounds have).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E4

theorem pw_le {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

theorem lin_two_pow (Y : ℕ) (hY : 1 ≤ Y) : 128 * Y + 1 ≤ 2 ^ (9 * Y) := by
  have h1 : Y < 2 ^ Y := Nat.lt_two_pow_self
  have h2 : 128 * Y + 1 ≤ 2 ^ 8 * 2 ^ Y := by omega
  calc 128 * Y + 1 ≤ 2 ^ 8 * 2 ^ Y := h2
    _ = 2 ^ (8 + Y) := by rw [pow_add]
    _ ≤ 2 ^ (9 * Y) := pw_le (by omega)

theorem sq_two_pow (a : ℕ) : (2 ^ a + 1) ^ 2 ≤ 2 ^ (2 * a + 2) := by
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h2 : 2 ^ a + 1 ≤ 2 * 2 ^ a := by omega
  calc (2 ^ a + 1) ^ 2 ≤ (2 * 2 ^ a) ^ 2 := Nat.pow_le_pow_left h2 2
    _ = 2 ^ (2 * a + 2) := by ring

theorem const_two_pow (c e : ℕ) (h : c ≤ 2 ^ e) (n : ℕ) : c ≤ 2 ^ (e + n) := by
  calc c ≤ 2 ^ e := h
    _ ≤ 2 ^ (e + n) := pw_le (by omega)

/-- the bound on the cost of the per-node work -/
def cnode (M k : ℕ) : ℕ := (M + 1) ^ 15 * 2 ^ (4000 * (k + 2) ^ 3)

theorem Q_ge (M : ℕ) : 1 ≤ (M + 1) ^ 15 := Nat.one_le_pow _ _ (by omega)

/-- `t ≤ 2^e` with `e ≤ 3990 Y` gives `t ≤ Q · R` (the common ceiling `Q = (M+1)^15`, `R = 2^(3990 Y)`) -/
theorem to_ceiling {t e Y : ℕ} (M : ℕ) (h : t ≤ 2 ^ e) (he : e ≤ 3990 * Y) :
    t ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) :=
  le_trans (le_trans h (pw_le he)) (Nat.le_mul_of_pos_left _ (Q_ge M))

theorem ceiling_sum {Y M : ℕ} (hY : 1 ≤ Y) {S : ℕ} (hS : S ≤ 8 * ((M + 1) ^ 15 * 2 ^ (3990 * Y))) :
    S ≤ (M + 1) ^ 15 * 2 ^ (4000 * Y) := by
  have h1 : 8 * ((M + 1) ^ 15 * 2 ^ (3990 * Y)) = (M + 1) ^ 15 * 2 ^ (3990 * Y + 3) := by rw [pow_add]; ring
  have h2 : 2 ^ (3990 * Y + 3) ≤ 2 ^ (4000 * Y) := pw_le (by omega)
  calc S ≤ 8 * ((M + 1) ^ 15 * 2 ^ (3990 * Y)) := hS
    _ = (M + 1) ^ 15 * 2 ^ (3990 * Y + 3) := h1
    _ ≤ (M + 1) ^ 15 * 2 ^ (4000 * Y) := Nat.mul_le_mul_left _ h2

theorem const_le_ceiling (M Y c e : ℕ) (hc : c ≤ 2 ^ e) (he : e ≤ 3990 * Y) :
    c ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := to_ceiling M hc he

/-! ### forget node -/

theorem forget_node (Y M : ℕ) (hY : 8 ≤ Y) :
    200 + 7300 * (128 * Y + 1) ^ 5 * (2 ^ (96 * Y) + 1) ^ 2 ≤ (M + 1) ^ 15 * 2 ^ (4000 * Y) := by
  have a1 : (128 * Y + 1) ^ 5 ≤ 2 ^ (45 * Y) := by
    calc (128 * Y + 1) ^ 5 ≤ (2 ^ (9 * Y)) ^ 5 := Nat.pow_le_pow_left (lin_two_pow Y (by omega)) 5
      _ = 2 ^ (45 * Y) := by rw [← pow_mul]; ring_nf
  have a2 := sq_two_pow (96 * Y)
  have a3 : 7300 * (128 * Y + 1) ^ 5 * (2 ^ (96 * Y) + 1) ^ 2 ≤ 2 ^ (13 + 45 * Y + (2 * (96 * Y) + 2)) := by
    calc 7300 * (128 * Y + 1) ^ 5 * (2 ^ (96 * Y) + 1) ^ 2 ≤ 2 ^ 13 * 2 ^ (45 * Y) * 2 ^ (2 * (96 * Y) + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) a1) a2
      _ = 2 ^ (13 + 45 * Y + (2 * (96 * Y) + 2)) := by rw [← pow_add, ← pow_add]
  have a4 := to_ceiling (Y := Y) M a3 (by omega)
  have a5 : 200 ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) :=
    const_le_ceiling M Y 200 8 (by norm_num) (by omega)
  refine ceiling_sum (by omega) ?_
  omega

/-! ### intro node -/

theorem intro_node (Y M X : ℕ) (hY : 8 ≤ Y) (hX : X ≤ Y) :
    200 + 60 * M ^ 2 + X * (28 * M + 120) +
      (2 ^ (96 * Y) * (10 ^ 16 * (128 * Y + M + 1) ^ 15 * 2 ^ (3456 * Y) + 10 * 2 ^ (1728 * Y) + 100) + 100 +
        60 * (128 * Y + 1) * (2 ^ (1824 * Y) + 1) ^ 2) ≤ (M + 1) ^ 15 * 2 ^ (4000 * Y) := by
  have hQ := Q_ge M
  have hY2 : Y < 2 ^ Y := Nat.lt_two_pow_self
  -- 60 M^2
  have t2 : 60 * M ^ 2 ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := by
    have h1 : M ^ 2 ≤ (M + 1) ^ 15 := le_trans (Nat.pow_le_pow_left (Nat.le_succ M) 2)
      (Nat.pow_le_pow_right (by omega) (by norm_num))
    have h2 : 60 ≤ 2 ^ (3990 * Y) := le_trans (by norm_num : 60 ≤ 2 ^ 6) (pw_le (by omega))
    calc 60 * M ^ 2 ≤ 2 ^ (3990 * Y) * (M + 1) ^ 15 := Nat.mul_le_mul h2 h1
      _ = _ := by ring
  -- X (28 M + 120)
  have t3 : X * (28 * M + 120) ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := by
    have h1 : 28 * M + 120 ≤ 2 ^ 7 * (M + 1) ^ 15 := by
      have : M + 1 ≤ (M + 1) ^ 15 := by
        calc M + 1 = (M + 1) ^ 1 := (pow_one _).symm
          _ ≤ (M + 1) ^ 15 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega
    have h2 : X ≤ 2 ^ Y := le_trans hX (le_of_lt hY2)
    calc X * (28 * M + 120) ≤ 2 ^ Y * (2 ^ 7 * (M + 1) ^ 15) := Nat.mul_le_mul h2 h1
      _ = (M + 1) ^ 15 * 2 ^ (Y + 7) := by rw [pow_add]; ring
      _ ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := Nat.mul_le_mul_left _ (pw_le (by omega))
  -- the introC term
  have hb : 128 * Y + M + 1 ≤ 2 ^ (9 * Y) * (M + 1) := by
    have h1 := lin_two_pow Y (by omega)
    have h2 : 128 * Y + M + 1 ≤ (128 * Y + 1) * (M + 1) := by nlinarith
    exact le_trans h2 (Nat.mul_le_mul_right _ h1)
  have t4 : 2 ^ (96 * Y) * (10 ^ 16 * (128 * Y + M + 1) ^ 15 * 2 ^ (3456 * Y)) ≤
      (M + 1) ^ 15 * 2 ^ (3990 * Y) := by
    have h1 : (128 * Y + M + 1) ^ 15 ≤ 2 ^ (135 * Y) * (M + 1) ^ 15 := by
      calc (128 * Y + M + 1) ^ 15 ≤ (2 ^ (9 * Y) * (M + 1)) ^ 15 := Nat.pow_le_pow_left hb 15
        _ = 2 ^ (135 * Y) * (M + 1) ^ 15 := by rw [mul_pow, ← pow_mul]; ring_nf
    have h2 : 10 ^ 16 ≤ 2 ^ 54 := by norm_num
    calc 2 ^ (96 * Y) * (10 ^ 16 * (128 * Y + M + 1) ^ 15 * 2 ^ (3456 * Y))
        ≤ 2 ^ (96 * Y) * (2 ^ 54 * (2 ^ (135 * Y) * (M + 1) ^ 15) * 2 ^ (3456 * Y)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul h2 h1))
      _ = (M + 1) ^ 15 * 2 ^ (96 * Y + 54 + 135 * Y + 3456 * Y) := by ring
      _ ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := Nat.mul_le_mul_left _ (pw_le (by omega))
  have t5 : 2 ^ (96 * Y) * (10 * 2 ^ (1728 * Y)) ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := by
    have : 2 ^ (96 * Y) * (10 * 2 ^ (1728 * Y)) ≤ 2 ^ (96 * Y) * (2 ^ 4 * 2 ^ (1728 * Y)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by norm_num))
    refine to_ceiling M (le_trans this (le_of_eq ?_)) (e := 96 * Y + (4 + 1728 * Y)) (by omega)
    ring
  have t6 : 2 ^ (96 * Y) * 100 ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := by
    have : 2 ^ (96 * Y) * 100 ≤ 2 ^ (96 * Y) * 2 ^ 7 :=
      Nat.mul_le_mul_left _ (by norm_num)
    refine to_ceiling M (le_trans this (le_of_eq ?_)) (e := 96 * Y + 7) (by omega)
    ring
  have t8 : 60 * (128 * Y + 1) * (2 ^ (1824 * Y) + 1) ^ 2 ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := by
    have a1 := lin_two_pow Y (by omega)
    have a2 := sq_two_pow (1824 * Y)
    have : 60 * (128 * Y + 1) * (2 ^ (1824 * Y) + 1) ^ 2 ≤ 2 ^ 6 * 2 ^ (9 * Y) * 2 ^ (2 * (1824 * Y) + 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) a1) a2
    refine to_ceiling M (le_trans this (le_of_eq ?_)) (e := 6 + 9 * Y + (2 * (1824 * Y) + 2)) (by omega)
    rw [← pow_add, ← pow_add]
  have t1 : 200 ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := const_le_ceiling M Y 200 8 (by norm_num) (by omega)
  have t7 : 100 ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := const_le_ceiling M Y 100 7 (by norm_num) (by omega)
  refine ceiling_sum (by omega) ?_
  have e : 2 ^ (96 * Y) * (10 ^ 16 * (128 * Y + M + 1) ^ 15 * 2 ^ (3456 * Y) + 10 * 2 ^ (1728 * Y) + 100) =
      2 ^ (96 * Y) * (10 ^ 16 * (128 * Y + M + 1) ^ 15 * 2 ^ (3456 * Y)) + 2 ^ (96 * Y) * (10 * 2 ^ (1728 * Y)) +
        2 ^ (96 * Y) * 100 := by ring
  rw [e]
  omega

/-! ### join node -/

theorem join_node (Y M : ℕ) (hY : 8 ≤ Y) :
    200 + (2 ^ (96 * Y) * (2 ^ (96 * Y) * (14000 * (128 * Y + 1) * 2 ^ (1296 * Y) + 10 * 2 ^ (432 * Y) + 50) + 40 +
        10 * (2 ^ (96 * Y) * 2 ^ (432 * Y)) + 20) + 100 +
      60 * (128 * Y + 1) * (2 ^ (96 * Y) * (2 ^ (96 * Y) * 2 ^ (432 * Y)) + 1) ^ 2) ≤
      (M + 1) ^ 15 * 2 ^ (4000 * Y) := by
  have hl := lin_two_pow Y (by omega)
  -- the join cost of one call
  have c1 : 14000 * (128 * Y + 1) * 2 ^ (1296 * Y) ≤ 2 ^ (1305 * Y + 14) := by
    calc 14000 * (128 * Y + 1) * 2 ^ (1296 * Y) ≤ 2 ^ 14 * 2 ^ (9 * Y) * 2 ^ (1296 * Y) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (by norm_num) hl)
      _ = 2 ^ (1305 * Y + 14) := by rw [← pow_add, ← pow_add]; ring_nf
  have c1' : 10 * 2 ^ (432 * Y) ≤ 2 ^ (1305 * Y + 14) := by
    calc 10 * 2 ^ (432 * Y) ≤ 2 ^ 4 * 2 ^ (432 * Y) := Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ (4 + 432 * Y) := by rw [← pow_add]
      _ ≤ 2 ^ (1305 * Y + 14) := pw_le (by omega)
  have c1'' : 50 ≤ 2 ^ (1305 * Y + 14) := le_trans (by norm_num : 50 ≤ 2 ^ 6) (pw_le (by omega))
  have cs : 14000 * (128 * Y + 1) * 2 ^ (1296 * Y) + 10 * 2 ^ (432 * Y) + 50 ≤ 2 ^ (1305 * Y + 16) := by
    have : 2 ^ (1305 * Y + 16) = 4 * 2 ^ (1305 * Y + 14) := by rw [pow_add, pow_add]; ring
    omega
  -- La * Cs
  have c2a : 2 ^ (96 * Y) * (14000 * (128 * Y + 1) * 2 ^ (1296 * Y) + 10 * 2 ^ (432 * Y) + 50) ≤
      2 ^ (1401 * Y + 16) := by
    calc _ ≤ 2 ^ (96 * Y) * 2 ^ (1305 * Y + 16) := Nat.mul_le_mul_left _ cs
      _ = 2 ^ (1401 * Y + 16) := by rw [← pow_add]; ring_nf
  have c2b : 10 * (2 ^ (96 * Y) * 2 ^ (432 * Y)) ≤ 2 ^ (1401 * Y + 16) := by
    calc 10 * (2 ^ (96 * Y) * 2 ^ (432 * Y)) ≤ 2 ^ 4 * (2 ^ (96 * Y) * 2 ^ (432 * Y)) :=
          Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ (4 + (96 * Y + 432 * Y)) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (1401 * Y + 16) := pw_le (by omega)
  have c2c : 40 ≤ 2 ^ (1401 * Y + 16) := le_trans (by norm_num : 40 ≤ 2 ^ 6) (pw_le (by omega))
  have c2d : 20 ≤ 2 ^ (1401 * Y + 16) := le_trans (by norm_num : 20 ≤ 2 ^ 5) (pw_le (by omega))
  have c2 : 2 ^ (96 * Y) * (14000 * (128 * Y + 1) * 2 ^ (1296 * Y) + 10 * 2 ^ (432 * Y) + 50) + 40 +
        10 * (2 ^ (96 * Y) * 2 ^ (432 * Y)) + 20 ≤ 2 ^ (1401 * Y + 18) := by
    have : 2 ^ (1401 * Y + 18) = 4 * 2 ^ (1401 * Y + 16) := by rw [pow_add, pow_add]; ring
    omega
  have c3 : 2 ^ (96 * Y) * (2 ^ (96 * Y) * (14000 * (128 * Y + 1) * 2 ^ (1296 * Y) + 10 * 2 ^ (432 * Y) + 50) + 40 +
        10 * (2 ^ (96 * Y) * 2 ^ (432 * Y)) + 20) ≤ 2 ^ (1497 * Y + 18) := by
    calc _ ≤ 2 ^ (96 * Y) * 2 ^ (1401 * Y + 18) := Nat.mul_le_mul_left _ c2
      _ = 2 ^ (1497 * Y + 18) := by rw [← pow_add]; ring_nf
  have c4 : 60 * (128 * Y + 1) * (2 ^ (96 * Y) * (2 ^ (96 * Y) * 2 ^ (432 * Y)) + 1) ^ 2 ≤
      2 ^ (1259 * Y + 8) := by
    have e : 2 ^ (96 * Y) * (2 ^ (96 * Y) * 2 ^ (432 * Y)) = 2 ^ (624 * Y) := by
      rw [← pow_add, ← pow_add]; ring_nf
    rw [e]
    have a2 := sq_two_pow (624 * Y)
    calc 60 * (128 * Y + 1) * (2 ^ (624 * Y) + 1) ^ 2 ≤ 2 ^ 6 * 2 ^ (9 * Y) * 2 ^ (2 * (624 * Y) + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) hl) a2
      _ = 2 ^ (6 + 9 * Y + (2 * (624 * Y) + 2)) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (1259 * Y + 8) := pw_le (by omega)
  have d1 := to_ceiling (Y := Y) M c3 (by omega)
  have d2 := to_ceiling (Y := Y) M c4 (by omega)
  have d3 : 100 ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := const_le_ceiling M Y 100 7 (by norm_num) (by omega)
  have d4 : 200 ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := const_le_ceiling M Y 200 8 (by norm_num) (by omega)
  refine ceiling_sum (by omega) ?_
  omega

/-! ### the same bounds in terms of the step-cost functions -/

theorem forget_node' (Y M : ℕ) (hY : 8 ≤ Y) :
    200 + forgetCostF (128 * Y) (2 ^ (96 * Y)) ≤ (M + 1) ^ 15 * 2 ^ (4000 * Y) := by
  unfold forgetCostF; exact forget_node Y M hY

theorem intro_node' (Y M X : ℕ) (hY : 8 ≤ Y) (hX : X ≤ Y) :
    200 + 60 * M ^ 2 + X * (28 * M + 120) +
      introCostF (10 ^ 16 * (128 * Y + M + 1) ^ 15 * 2 ^ (3456 * Y)) (2 ^ (1728 * Y)) (2 ^ (96 * Y)) (128 * Y)
        (2 ^ (1824 * Y)) ≤ (M + 1) ^ 15 * 2 ^ (4000 * Y) := by
  unfold introCostF; exact intro_node Y M X hY hX

theorem join_node' (Y M : ℕ) (hY : 8 ≤ Y) :
    200 + joinCostF (14000 * (128 * Y + 1) * 2 ^ (1296 * Y)) (2 ^ (96 * Y)) (2 ^ (96 * Y)) (2 ^ (432 * Y))
      (128 * Y) ≤ (M + 1) ^ 15 * 2 ^ (4000 * Y) := by
  unfold joinCostF; exact join_node Y M hY

end E4
end Lax117284Proofs.Treewidth.Fun
