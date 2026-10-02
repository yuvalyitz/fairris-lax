import Lax117284Proofs.Treewidth.Fun.E6bMerge
import Lax117284Proofs.Treewidth.Fun.E6bMath2
import Lax117284Proofs.Treewidth.Fun.E5Inst
import Lax117284Proofs.Treewidth.Fun.E4Arith
import Lax117284Proofs.Treewidth.Fun.E6bZ

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6b (6): the arithmetic of the cost bounds

`Yk k = (k+2)^3`, `Zc M k = (M+1) · 2^(1728 Yk k)`: a *common ceiling*.  Every quantity of the cost analysis is at most
a power of `Zc M k`: `M+1 ≤ Zc`, `2^(1728 Y) ≤ Zc`, `k+2 ≤ Y ≤ 2^Y`, constants `≤ 2^Y` (as `Y ≥ 8`).  The cost functions of
E2/E3/E5 are polynomials in the sizes, so bounding all their arguments by `Zc^a` bounds them by `C · Zc^d`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open E5R E5D

/-- `(k+2)^3` -/
def Yk (k : ℕ) : ℕ := (k + 2) ^ 3

/-- the common ceiling -/
def Zc (M k : ℕ) : ℕ := (M + 1) * 2 ^ (1728 * Yk k)

theorem Yk_ge (k : ℕ) : 8 ≤ Yk k := E4.Y_ge k
theorem lin_Yk (k : ℕ) : k + 2 ≤ Yk k := E4.X_le_Y k

theorem Zc_ge_one (M k : ℕ) : 1 ≤ Zc M k := by
  unfold Zc
  exact Nat.mul_pos (by omega) (Nat.two_pow_pos _)

theorem Zc_ge_M (M k : ℕ) : M + 1 ≤ Zc M k := by
  unfold Zc
  exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)

theorem Zc_ge_pow (M k : ℕ) : 2 ^ (1728 * Yk k) ≤ Zc M k := by
  unfold Zc
  exact Nat.le_mul_of_pos_left _ (by omega)

/-! ## the parameters of the `realIntro` call -/

/-- bound on the sizes of everything `realIntro` is applied to (trees, plans, characteristics) -/
def sI (M k : ℕ) : ℕ := 16000 * Yk k * (M + 1)
/-- bound on the run-sequence length of the results of `introPlans`: `2 (k+3) + 1` -/
def LrI (k : ℕ) : ℕ := 2 * k + 7
/-- bound on the number of plans -/
def LenI (k : ℕ) : ℕ := 2 ^ (1728 * Yk k)
/-- bound on every natural number of the input of `introPlans` -/
def UI (M k : ℕ) : ℕ := M + 128 * Yk k + k + 2

/-! ### the basic bounds by powers of `Zc` -/

theorem Zc_big (M k : ℕ) : 2 ^ 200 ≤ Zc M k :=
  le_trans (Nat.pow_le_pow_right (by norm_num) (by have := Yk_ge k; omega)) (Zc_ge_pow M k)

theorem b_pow (M k e j : ℕ) (he : e ≤ 1728 * Yk k * j) : 2 ^ e ≤ Zc M k ^ j := by
  calc 2 ^ e ≤ 2 ^ (1728 * Yk k * j) := Nat.pow_le_pow_right (by norm_num) he
    _ = (2 ^ (1728 * Yk k)) ^ j := by rw [pow_mul]
    _ ≤ Zc M k ^ j := Nat.pow_le_pow_left (Zc_ge_pow M k) j

theorem b_M (M k : ℕ) : M + 1 ≤ Zc M k ^ 1 := by simpa using Zc_ge_M M k

theorem b_Y (M k : ℕ) : Yk k ≤ Zc M k ^ 1 := by
  have h1 : Yk k < 2 ^ Yk k := Nat.lt_two_pow_self
  have h2 := b_pow M k (Yk k) 1 (by have := Yk_ge k; omega)
  omega

theorem b_k (M k : ℕ) : k + 2 ≤ Zc M k ^ 1 := le_trans (lin_Yk k) (b_Y M k)

theorem b_sI (M k : ℕ) : sI M k ≤ Zc M k ^ 1 := by
  unfold sI
  have h1 : Yk k < 2 ^ Yk k := Nat.lt_two_pow_self
  have h2 : 16000 * Yk k ≤ 2 ^ (1728 * Yk k) := by
    have h3 : 16000 * Yk k ≤ 2 ^ 14 * 2 ^ Yk k := Nat.mul_le_mul (by norm_num) (le_of_lt h1)
    have h4 : 2 ^ 14 * 2 ^ Yk k = 2 ^ (14 + Yk k) := by rw [pow_add]
    have h5 : 2 ^ (14 + Yk k) ≤ 2 ^ (1728 * Yk k) := Nat.pow_le_pow_right (by norm_num) (by have := Yk_ge k; omega)
    omega
  have := Nat.mul_le_mul_right (M + 1) h2
  unfold Zc
  simpa [mul_comm] using this

theorem b_UI (M k : ℕ) : UI M k + 1 ≤ Zc M k ^ 1 := by
  unfold UI
  have h1 : Yk k < 2 ^ Yk k := Nat.lt_two_pow_self
  have hk := lin_Yk k
  have h2 : 128 * Yk k + k + 3 ≤ 2 ^ (1728 * Yk k) := by
    have h3 : 130 * Yk k ≤ 2 ^ 8 * 2 ^ Yk k := Nat.mul_le_mul (by norm_num) (le_of_lt h1)
    have h4 : 2 ^ 8 * 2 ^ Yk k = 2 ^ (8 + Yk k) := by rw [pow_add]
    have h5 : 2 ^ (8 + Yk k) ≤ 2 ^ (1728 * Yk k) := Nat.pow_le_pow_right (by norm_num) (by have := Yk_ge k; omega)
    omega
  have h6 : M + 128 * Yk k + k + 2 + 1 ≤ (M + 1) * (128 * Yk k + k + 3) := by nlinarith
  have := Nat.mul_le_mul_left (M + 1) h2
  unfold Zc
  simp only [pow_one]
  nlinarith

theorem b_3pow (M k n : ℕ) (hn : 2 * n ≤ 1728 * Yk k) : 3 ^ n ≤ Zc M k ^ 1 := by
  have h1 : 3 ^ n ≤ 4 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have h2 : 4 ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have := b_pow M k (2 * n) 1 (by omega)
  omega

theorem b_4pow (M k n : ℕ) (hn : 2 * n ≤ 1728 * Yk k) : 4 ^ n ≤ Zc M k ^ 1 := by
  have h2 : 4 ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have := b_pow M k (2 * n) 1 (by omega)
  omega

theorem introCCost_z (M k : ℕ) : E3C.introCCost (UI M k + 1) (3 * (k + 2)) ≤ Zc M k ^ 18 := by
  unfold E3C.introCCost
  have hZ := Zc_big M k
  have h1 := zb_mul (zb_num (cnum (by norm_num : 10 ^ 16 ≤ 2 ^ 200) hZ)) (zb_pow (b_UI M k) 15)
  have h2 : 2 ^ (128 * (3 * (k + 2)) ^ 3) ≤ Zc M k ^ 2 := b_pow M k _ 2 (by unfold Yk; nlinarith)
  have := zb_mul h1 h2
  exact zb_mono this (by omega) (hZ1 hZ)

theorem cip_z (M k cip : ℕ) (hcip : cip ≤ 2 * E3C.introCCost (UI M k + 1) (3 * (k + 2))) : cip ≤ Zc M k ^ 19 := by
  have hZ := Zc_big M k
  have h := zb_cmul (cnum (by norm_num : 2 ≤ 2 ^ 200) hZ) (introCCost_z M k)
  exact le_trans hcip (zb_mono h (by omega) (hZ1 hZ))

/-- the exponent of the `realIntro` cost -/
def pRI : ℕ := 40

theorem numRI_cost (M k cip : ℕ) (hcip : cip ≤ 2 * E3C.introCCost (UI M k + 1) (3 * (k + 2))) :
    cRealIntro (sI M k) (LenI k) (E5Inst.cNormE2 (5 * sI M k)) (E5Inst.cNormE2 (sI M k))
      (E5Inst.cDomE2 (LrI k) (sI M k)) (E5Inst.cKeyE2 (6 * sI M k)) cip ≤ Zc M k ^ pRI := by
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have hs := b_sI M k
  have hs5 := zb_cmul (cnum (by norm_num : 5 ≤ 2 ^ 200) hZ) hs
  have hs6 := zb_cmul (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ) hs
  have hn5 := cNormE2_z hZ hs5
  have hn := cNormE2_z hZ hs
  have h3 : 3 ^ (2 * LrI k) ≤ Zc M k ^ 1 := b_3pow M k _ (by unfold LrI; have := Yk_ge k; have := lin_Yk k; omega)
  have hd := cDomE2_z hZ h3 (le_refl 1) hs
  have hk := cKeyE2_z hZ hs6
  have hap := cApplyPlan_z hZ hs hk (q := 2 * (1 + 1) + 4) (by omega)
  have hcipZ := cip_z M k cip hcip
  have hL : LenI k ≤ Zc M k ^ 1 := by unfold LenI; simpa using b_pow M k (1728 * Yk k) 1 (by omega)
  -- part 1
  have a := zb_cmul (cnum (by norm_num : 200 ≤ 2 ^ 200) hZ) (zb_succ hs hZ2')
  have b := zb_mul a hs
  have c := zb_add' b hn5 hZ2' (r := 5 * (1 + 1) + 6) (by omega) le_rfl
  have d := zb_add' c (zb_num (cnum (by norm_num : 8 ≤ 2 ^ 200) hZ)) hZ2' (r := 5 * (1 + 1) + 6 + 1) (by omega) (by omega)
  have e := zb_add' d hcipZ hZ2' (r := 19) (by omega) le_rfl
  -- part 3
  have f1 := zb_add' hn hd hZ2' (r := 5 * 1 + 6) (by omega) (by omega)
  have f2 := zb_add' f1 (zb_cmul (cnum (by norm_num : 30 ≤ 2 ^ 200) hZ) hs) hZ2' (r := 5 * 1 + 6 + 1) (by omega) (by omega)
  have f3 := zb_add' f2 (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) hZ2' (r := 5 * 1 + 6 + 2) (by omega) (by omega)
  have g1 := zb_mul hL f3
  have g2 := zb_add' (zb_cmul (cnum (by norm_num : 24 ≤ 2 ^ 200) hZ) hL) (zb_num (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ)) hZ2'
    (r := 2) (by omega) (by omega)
  have g3 := zb_add' g2 g1 hZ2' (r := 1 + (5 * 1 + 6 + 2 + 1)) (by omega) (by omega)
  have h1 := zb_add' e g3 hZ2' (r := 20) (by omega) (by omega)
  have h2 := zb_add' h1 hap hZ2' (r := 7 * 1 + 24) (by omega) (by omega)
  have h3' := zb_add' h2 (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) hZ2' (r := 7 * 1 + 24 + 1) (by omega) (by omega)
  unfold cRealIntro cPredI
  exact zb_mono h3' (by unfold pRI; omega) (hZ1 hZ)

theorem numRI_B (M k cip : ℕ) (hcip : cip ≤ 2 * E3C.introCCost (UI M k + 1) (3 * (k + 2))) :
    20000 + 20000 * (sI M k + 1) + E5Inst.cKeyE2 (6 * sI M k) + E5Inst.cNormE2 (5 * sI M k) +
      E5Inst.cNormE2 (sI M k) + E5Inst.cDomE2 (LrI k) (sI M k) + cip ≤ Zc M k ^ pRI := by
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have hs := b_sI M k
  have hs5 := zb_cmul (cnum (by norm_num : 5 ≤ 2 ^ 200) hZ) hs
  have hs6 := zb_cmul (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ) hs
  have hn5 := cNormE2_z hZ hs5
  have hn := cNormE2_z hZ hs
  have h3 : 3 ^ (2 * LrI k) ≤ Zc M k ^ 1 := b_3pow M k _ (by unfold LrI; have := Yk_ge k; have := lin_Yk k; omega)
  have hd := cDomE2_z hZ h3 (le_refl 1) hs
  have hk := cKeyE2_z hZ hs6
  have hcipZ := cip_z M k cip hcip
  have a := zb_cmul (cnum (by norm_num : 20000 ≤ 2 ^ 200) hZ) (zb_succ hs hZ2')
  have b := zb_add' (zb_num (cnum (by norm_num : 20000 ≤ 2 ^ 200) hZ)) a hZ2' (r := 3) (by omega) (by omega)
  have c := zb_add' b hk hZ2' (r := 2 * 2 + 4) (by omega) le_rfl
  have d := zb_add' c hn5 hZ2' (r := 5 * (1 + 1) + 6) (by omega) le_rfl
  have e := zb_add' d hn hZ2' (r := 5 * (1 + 1) + 6 + 1) (by omega) (by omega)
  have f := zb_add' e hd hZ2' (r := 5 * (1 + 1) + 6 + 2) (by omega) (by omega)
  have g := zb_add' f hcipZ hZ2' (r := 19) (by omega) le_rfl
  exact zb_mono g (by unfold pRI; omega) (hZ1 hZ)

/-! ## the parameters of the `realJoin` call -/

/-- bound on the run-sequence length of the join options: `2 (k+1) + 1` -/
def LrJ (k : ℕ) : ℕ := 2 * k + 3
/-- bound on the number of join options -/
def LenJ (k : ℕ) : ℕ := 2 ^ (432 * Yk k)
/-- bound on the cost `cJ` of the join call inside `realJoin` -/
def cJb (M k : ℕ) : ℕ :=
  28000 * (256 * Yk k + 1) * 2 ^ (1296 * Yk k) + 2000 * (256 * Yk k + 1) + 2000 + 6000 * 2 ^ (1296 * Yk k) + 1000

theorem cJb_z (M k : ℕ) : cJb M k ≤ Zc M k ^ 9 := by
  unfold cJb
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have hY := b_Y M k
  have h256 := zb_succ (zb_cmul (cnum (by norm_num : 256 ≤ 2 ^ 200) hZ) hY) hZ2'
  have hP : 2 ^ (1296 * Yk k) ≤ Zc M k ^ 1 := b_pow M k _ 1 (by omega)
  have A1 := zb_cmul (cnum (by norm_num : 28000 ≤ 2 ^ 200) hZ) h256
  have A2 := zb_mul A1 hP
  have B1 := zb_cmul (cnum (by norm_num : 2000 ≤ 2 ^ 200) hZ) h256
  have C1 := zb_cmul (cnum (by norm_num : 6000 ≤ 2 ^ 200) hZ) hP
  have v1 := zb_add' A2 B1 hZ2' (r := 5) (by omega) (by omega)
  have v2 := zb_add' v1 (zb_num (cnum (by norm_num : 2000 ≤ 2 ^ 200) hZ)) hZ2' (r := 6) (by omega) (by omega)
  have v3 := zb_add' v2 C1 hZ2' (r := 7) (by omega) (by omega)
  have v4 := zb_add' v3 (zb_num (cnum (by norm_num : 1000 ≤ 2 ^ 200) hZ)) hZ2' (r := 8) (by omega) (by omega)
  exact zb_mono v4 (by omega) (hZ1 hZ)

/-- the exponent of the `realJoin` cost -/
def pRJ : ℕ := 50

theorem numRJ_cost (M k cj : ℕ) (hcj : cj ≤ cJb M k) :
    cRealJoin' (sI M k) (k + 1) (LrJ k) (LenJ k) (E5Inst.cNormE2 (5 * sI M k))
      (E5Inst.cDomE2 (LrJ k) (sI M k)) (E5Inst.cKeyE2 (6 * sI M k)) cj ≤ Zc M k ^ pRJ := by
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have hs := b_sI M k
  have hs5 := zb_cmul (cnum (by norm_num : 5 ≤ 2 ^ 200) hZ) hs
  have hs6 := zb_cmul (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ) hs
  have hn5 := cNormE2_z hZ hs5
  have h3 : 3 ^ (2 * LrJ k) ≤ Zc M k ^ 1 := b_3pow M k _ (by unfold LrJ; have := Yk_ge k; have := lin_Yk k; omega)
  have hd := cDomE2_z hZ h3 (le_refl 1) hs
  have hk := cKeyE2_z hZ hs6
  have hcjZ : cj ≤ Zc M k ^ 9 := le_trans hcj (cJb_z M k)
  have hL : LenJ k ≤ Zc M k ^ 1 := by unfold LenJ; simpa using b_pow M k (432 * Yk k) 1 (by omega)
  have L4 : 4 ^ ((k + 1) + (k + 1) + 1) ≤ Zc M k ^ 2 :=
    zb_mono (b_4pow M k _ (by have := Yk_ge k; have := lin_Yk k; omega)) (by omega) (hZ1 hZ)
  have L3 : 3 ^ (2 * ((k + 1) + (k + 1)) + 1 + LrJ k) ≤ Zc M k ^ 2 :=
    zb_mono (b_3pow M k _ (by unfold LrJ; have := Yk_ge k; have := lin_Yk k; omega)) (by omega) (hZ1 hZ)
  have LL : 2 * ((k + 1) + (k + 1)) + 1 + 2 ≤ Zc M k ^ 2 := by
    have := zb_cmul (cnum (by norm_num : 4 ≤ 2 ^ 200) hZ) (b_k M k)
    exact le_trans (by omega) (zb_mono this (by omega) (hZ1 hZ))
  have hMR := cMergeReal'_z hZ hs hk (q := 2 * 2 + 4) (by omega) L4 L3 LL
  have a := zb_cmul (cnum (by norm_num : 200 ≤ 2 ^ 200) hZ) (zb_succ hs hZ2')
  have b := zb_mul a hs
  have c := zb_add' b hn5 hZ2' (r := 5 * (1 + 1) + 6) (by omega) le_rfl
  have d := zb_add' c (zb_num (cnum (by norm_num : 8 ≤ 2 ^ 200) hZ)) hZ2' (r := 5 * (1 + 1) + 6 + 1) (by omega) (by omega)
  have d2 := zb_cmul (cnum (by norm_num : 2 ≤ 2 ^ 200) hZ) d
  have e := zb_add' d2 hcjZ hZ2' (r := 20) (by omega) (by omega)
  have f1 := zb_add' hd (zb_num (cnum (by norm_num : 10 ≤ 2 ^ 200) hZ)) hZ2' (r := 7) (by omega) (by omega)
  have f2 := zb_mul hL f1
  have g2 := zb_add' (zb_cmul (cnum (by norm_num : 24 ≤ 2 ^ 200) hZ) hL) (zb_num (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ)) hZ2'
    (r := 2) (by omega) (by omega)
  have g3 := zb_add' g2 f2 hZ2' (r := 9) (by omega) (by omega)
  have h1 := zb_add' e g3 hZ2' (r := 21) (by omega) (by omega)
  have h2 := zb_add' h1 hMR hZ2' (r := 7 * 1 + 4 * 2 + 24) (by omega) (by omega)
  have h3' := zb_add' h2 (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) hZ2' (r := 7 * 1 + 4 * 2 + 25) (by omega) (by omega)
  unfold cRealJoin'
  exact zb_mono h3' (by unfold pRJ; omega) (hZ1 hZ)

theorem numRJ_B (M k cj : ℕ) (hcj : cj ≤ cJb M k) :
    200000 + 100000 * (sI M k + 1) ^ 2 + E5Inst.cKeyE2 (6 * sI M k) + E5Inst.cNormE2 (5 * sI M k) +
      E5Inst.cDomE2 (LrJ k) (sI M k) + cj ≤ Zc M k ^ pRJ := by
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have hs := b_sI M k
  have hs5 := zb_cmul (cnum (by norm_num : 5 ≤ 2 ^ 200) hZ) hs
  have hs6 := zb_cmul (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ) hs
  have hn5 := cNormE2_z hZ hs5
  have h3 : 3 ^ (2 * LrJ k) ≤ Zc M k ^ 1 := b_3pow M k _ (by unfold LrJ; have := Yk_ge k; have := lin_Yk k; omega)
  have hd := cDomE2_z hZ h3 (le_refl 1) hs
  have hk := cKeyE2_z hZ hs6
  have hcjZ : cj ≤ Zc M k ^ 9 := le_trans hcj (cJb_z M k)
  have a := zb_cmul (cnum (by norm_num : 100000 ≤ 2 ^ 200) hZ) (zb_pow (zb_succ hs hZ2') 2)
  have b := zb_add' (zb_num (cnum (by norm_num : 200000 ≤ 2 ^ 200) hZ)) a hZ2' (r := 5) (by omega) (by omega)
  have c := zb_add' b hk hZ2' (r := 2 * 2 + 4) (by omega) (by omega)
  have d := zb_add' c hn5 hZ2' (r := 5 * (1 + 1) + 6) (by omega) (by omega)
  have e := zb_add' d hd hZ2' (r := 5 * (1 + 1) + 7) (by omega) (by omega)
  have f := zb_add' e hcjZ hZ2' (r := 5 * (1 + 1) + 8) (by omega) (by omega)
  exact zb_mono f (by unfold pRJ; omega) (hZ1 hZ)

end E6b
end Lax117284Proofs.Treewidth.Fun
