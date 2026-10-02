import Lax117284Proofs.Treewidth.Fun.E5Inst
import Lax117284Proofs.Treewidth.Fun.E6bMerge

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6b (14): the `Z`-calculus

`x ≤ Z^p` bounds: monotone in `p`, closed under `*` (exponents add), `+` (exponent `+1`), `+1`, powers, and multiplication by a
numeral `c ≤ Z`.  Used to bound the polynomial cost functions of E2/E3/E5 (whose arguments are all `≤ Z^p` for the common
ceiling `Z = Zc M k`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

section zcalc
variable {Z : ℕ}

theorem zb_mono {x p q : ℕ} (h : x ≤ Z ^ p) (hpq : p ≤ q) (hZ : 1 ≤ Z) : x ≤ Z ^ q :=
  le_trans h (Nat.pow_le_pow_right hZ hpq)

theorem zb_mul {x y p q : ℕ} (h1 : x ≤ Z ^ p) (h2 : y ≤ Z ^ q) : x * y ≤ Z ^ (p + q) := by
  rw [pow_add]; exact Nat.mul_le_mul h1 h2

theorem zb_add {x y p r : ℕ} (h1 : x ≤ Z ^ p) (h2 : y ≤ Z ^ p) (hZ : 2 ≤ Z) (hpr : p + 1 ≤ r) : x + y ≤ Z ^ r := by
  have h3 : Z ^ p + Z ^ p ≤ Z ^ (p + 1) := by
    rw [pow_succ]
    have : 1 ≤ Z ^ p := Nat.one_le_pow _ _ (by omega)
    nlinarith
  exact le_trans (by omega) (le_trans h3 (Nat.pow_le_pow_right (by omega) hpr))

theorem zb_add' {x y p q r : ℕ} (h1 : x ≤ Z ^ p) (h2 : y ≤ Z ^ q) (hZ : 2 ≤ Z) (hp : p ≤ r) (hq : q ≤ r) :
    x + y ≤ Z ^ (r + 1) :=
  zb_add (zb_mono h1 hp (by omega)) (zb_mono h2 hq (by omega)) hZ le_rfl

/-- a sum: exponent `max + 1` (no bookkeeping needed at the call site) -/
theorem zb_addm {x y p q : ℕ} (h1 : x ≤ Z ^ p) (h2 : y ≤ Z ^ q) (hZ : 2 ≤ Z) : x + y ≤ Z ^ (max p q + 1) :=
  zb_add' h1 h2 hZ (le_max_left p q) (le_max_right p q)

theorem zb_succ {x p : ℕ} (h : x ≤ Z ^ p) (hZ : 2 ≤ Z) : x + 1 ≤ Z ^ (p + 1) :=
  zb_add (zb_mono h le_rfl (by omega)) (by
    have : 1 ≤ Z ^ p := Nat.one_le_pow _ _ (by omega)
    omega) hZ le_rfl

theorem zb_pow {x p : ℕ} (h : x ≤ Z ^ p) (n : ℕ) : x ^ n ≤ Z ^ (p * n) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left h n

theorem zb_num {c : ℕ} (hc : c ≤ Z) : c ≤ Z ^ 1 := by simpa using hc

theorem zb_cmul {c x p : ℕ} (hc : c ≤ Z) (h : x ≤ Z ^ p) : c * x ≤ Z ^ (1 + p) := by
  have := zb_mul (zb_num hc) h
  simpa [add_comm] using this

theorem zb_one (p : ℕ) (hZ : 1 ≤ Z) : 1 ≤ Z ^ p := Nat.one_le_pow _ _ (by omega)

theorem cnum {c : ℕ} (hc : c ≤ 2 ^ 200) (hZ : 2 ^ 200 ≤ Z) : c ≤ Z := le_trans hc hZ

/-! ### the cost functions of E2, E5 -/

variable (hZ : 2 ^ 200 ≤ Z)
include hZ

theorem hZ2 : 2 ≤ Z := le_trans (by norm_num) hZ
theorem hZ1 : 1 ≤ Z := le_trans (by norm_num) hZ

theorem cKeyE2_z {s p : ℕ} (hs : s ≤ Z ^ p) : E5Inst.cKeyE2 s ≤ Z ^ (2 * p + 4) := by
  have h1 := zb_succ hs (hZ2 hZ)
  have h2 := zb_pow h1 2
  have h3 := zb_cmul (cnum (by norm_num : 1000 ≤ 2 ^ 200) hZ) h2
  have h4 := zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)
  have := zb_add' h3 h4 (hZ2 hZ) (r := 2 * p + 3) (by omega) (by omega)
  unfold E5Inst.cKeyE2
  exact zb_mono this (by omega) (hZ1 hZ)

theorem cNormE2_z {s p : ℕ} (hs : s ≤ Z ^ p) : E5Inst.cNormE2 s ≤ Z ^ (5 * p + 6) := by
  have h1 := zb_succ hs (hZ2 hZ)
  have h2 := zb_pow h1 5
  have h3 := zb_cmul (cnum (by norm_num : 14000 ≤ 2 ^ 200) hZ) h2
  unfold E5Inst.cNormE2
  exact zb_mono h3 (by omega) (hZ1 hZ)

theorem cDomE2_z {L s p t : ℕ} (h3 : 3 ^ (2 * L) ≤ Z ^ t) (ht : t ≤ p) (hs : s ≤ Z ^ p) :
    E5Inst.cDomE2 L s ≤ Z ^ (2 * p + 5) := by
  have a1 := zb_cmul (cnum (by norm_num : 30 ≤ 2 ^ 200) hZ) hs
  have a2 := zb_cmul (cnum (by norm_num : 60 ≤ 2 ^ 200) hZ) h3
  have a3 := zb_add' a1 a2 (hZ2 hZ) (r := p + 1) (by omega) (by omega)
  have a4 := zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)
  have a5 := zb_add' a3 a4 (hZ2 hZ) (r := p + 2) (by omega) (by omega)
  have a6 := zb_cmul (cnum (by norm_num : 2 ≤ 2 ^ 200) hZ) hs
  have a7 := zb_mul a5 a6
  have a8 := zb_num (cnum (by norm_num : 1000 ≤ 2 ^ 200) hZ)
  have a9 := zb_add' a7 a8 (hZ2 hZ) (r := 2 * p + 4) (by omega) (by omega)
  unfold E5Inst.cDomE2
  exact zb_mono a9 (by omega) (hZ1 hZ)

theorem cSort_z {s ck p q : ℕ} (hs : s ≤ Z ^ p) (hck : ck ≤ Z ^ q) (hq : q ≤ 4 * p + 5) :
    E5B.cSort s ck ≤ Z ^ (6 * p + 10) := by
  have b1 := zb_succ hs (hZ2 hZ)
  have b2 := zb_pow b1 4
  have b3 := zb_cmul (cnum (by norm_num : 800 ≤ 2 ^ 200) hZ) b2
  have b4 := zb_add' b3 hck (hZ2 hZ) (r := 4 * p + 5) (by omega) hq
  have b5 := zb_add' b4 (zb_num (cnum (by norm_num : 80 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := 4 * p + 6) (by omega) (by omega)
  have b6 := zb_pow b1 2
  have b7 := zb_mul b5 b6
  have b8 := zb_add' b7 (zb_num (cnum (by norm_num : 8 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := 6 * p + 9) (by omega) (by omega)
  unfold E5B.cSort
  exact zb_mono b8 (by omega) (hZ1 hZ)

theorem cAN_z {s ck p q : ℕ} (hs : s ≤ Z ^ p) (hck : ck ≤ Z ^ q) (hq : q ≤ 4 * p + 5) :
    E5B.cAN s ck ≤ Z ^ (6 * p + 11) := by
  have h1 := zb_succ hs (hZ2 hZ)
  have h2 := zb_pow h1 2
  have h3 := zb_cmul (cnum (by norm_num : 1000 ≤ 2 ^ 200) hZ) h2
  have h4 := cSort_z hZ hs hck hq
  have := zb_add' h3 h4 (hZ2 hZ) (r := 6 * p + 10) (by omega) le_rfl
  unfold E5B.cAN
  exact zb_mono this (by omega) (hZ1 hZ)

theorem cA_z {s ck p q : ℕ} (hs : s ≤ Z ^ p) (hck : ck ≤ Z ^ q) (hq : q ≤ 4 * p + 9) :
    E5B.cA s ck ≤ Z ^ (6 * p + 19) := by
  have h6 := zb_cmul (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ) hs
  have h1 := cAN_z hZ h6 hck (p := 1 + p) (by omega)
  have h2 := zb_cmul (cnum (by norm_num : 20 ≤ 2 ^ 200) hZ) hs
  have h3 := zb_add' h1 h2 (hZ2 hZ) (r := 6 * (1 + p) + 11) (by omega) (by omega)
  have h4 := zb_add' h3 (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := 6 * (1 + p) + 12) (by omega) (by omega)
  unfold E5B.cA
  exact zb_mono h4 (by omega) (hZ1 hZ)

theorem cPR_z {s p : ℕ} (hs : s ≤ Z ^ p) : E5C2.cPR s ≤ Z ^ (3 * p + 4) := by
  have h1 := zb_succ hs (hZ2 hZ)
  have h2 := zb_pow h1 3
  have h3 := zb_cmul (cnum (by norm_num : 3000 ≤ 2 ^ 200) hZ) h2
  unfold E5C2.cPR
  exact zb_mono h3 (by omega) (hZ1 hZ)

theorem cApplyPlan_z {s ck p q : ℕ} (hs : s ≤ Z ^ p) (hck : ck ≤ Z ^ q) (hq : q ≤ 4 * p + 9) :
    E5C3.cApplyPlan s ck ≤ Z ^ (7 * p + 24) := by
  have hcA := cA_z hZ hs hck hq
  have T1 := zb_mul hcA hs
  have s1 := zb_cmul (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ) hs
  have s2 := zb_add' s1 (zb_num (cnum (by norm_num : 60 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := p + 1) (by omega) (by omega)
  have T2 := zb_mul hs s2
  have s5 := zb_cmul (cnum (by norm_num : 5 ≤ 2 ^ 200) hZ) hs
  have hpr := cPR_z hZ s5
  have T3a := zb_mul hpr hs
  have s6 := zb_succ hs (hZ2 hZ)
  have s7 := zb_cmul (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ) s6
  have T3b := zb_add' T3a s7 (hZ2 hZ) (r := 4 * p + 8) (by omega) (by omega)
  have T3 := zb_add' T3b (zb_num (cnum (by norm_num : 40 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := 4 * p + 9) (by omega) (by omega)
  have u1 := zb_cmul (cnum (by norm_num : 58 ≤ 2 ^ 200) hZ) hs
  have u3 := zb_add' u1 (zb_num (cnum (by norm_num : 11 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := p + 1) (by omega) (by omega)
  have u2 := zb_succ u3 (hZ2 hZ)
  have T4a := zb_cmul (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ) u2
  have T4 := zb_mul T4a u3
  have v1 := zb_add' T1 T2 (hZ2 hZ) (r := 7 * p + 19) (by omega) (by omega)
  have v2 := zb_add' v1 T3 (hZ2 hZ) (r := 7 * p + 20) (by omega) (by omega)
  have v3 := zb_add' v2 T4 (hZ2 hZ) (r := 7 * p + 21) (by omega) (by omega)
  have v4 := zb_add' v3 (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := 7 * p + 22) (by omega) (by omega)
  unfold E5C3.cApplyPlan
  exact zb_mono v4 (by omega) (hZ1 hZ)

theorem fpBound'_z {s L Ly p t : ℕ} (hs : s ≤ Z ^ p) (h4 : 4 ^ (L + L + 1) ≤ Z ^ t)
    (h3 : 3 ^ (2 * (L + L) + 1 + Ly) ≤ Z ^ t) (hL : 2 * (L + L) + 1 + 2 ≤ Z ^ t) :
    E5D.fpBound' s L Ly ≤ Z ^ (2 * p + 4 * t + 8) := by
  have hs1 := zb_succ hs (hZ2 hZ)
  have A1 := zb_cmul (cnum (by norm_num : 6000 ≤ 2 ^ 200) hZ) hs1
  have A2 := zb_mul A1 hs1
  have A3 := zb_pow (zb_succ h4 (hZ2 hZ)) 2
  have A4 := zb_mul A2 A3
  have A5 := zb_pow hL 2
  have A6 := zb_mul A4 A5
  have B1 := zb_cmul (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ) h3
  have hL1 : 2 * (L + L) + 1 ≤ Z ^ t := le_trans (by omega) hL
  have B2 := zb_cmul (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ) hL1
  have B3 := zb_add' B1 B2 (hZ2 hZ) (r := t + 1) (by omega) (by omega)
  have B4 := zb_add' B3 (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := t + 2) (by omega) (by omega)
  have B5 := zb_mul h4 B4
  have C1 := zb_add' hs hs (hZ2 hZ) (r := p) le_rfl le_rfl
  have C2 := zb_cmul (cnum (by norm_num : 12 ≤ 2 ^ 200) hZ) C1
  have D1 := zb_add' A6 B5 (hZ2 hZ) (r := 2 * p + 4 * t + 5) (by omega) (by omega)
  have D2 := zb_add' D1 C2 (hZ2 hZ) (r := 2 * p + 4 * t + 6) (by omega) (by omega)
  have D3 := zb_add' D2 (zb_num (cnum (by norm_num : 200 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := 2 * p + 4 * t + 7) (by omega) (by omega)
  unfold E5D.fpBound'
  exact zb_mono D3 (by omega) (hZ1 hZ)

theorem cMA'_z {s L Ly p t : ℕ} (hs : s ≤ Z ^ p) (h4 : 4 ^ (L + L + 1) ≤ Z ^ t)
    (h3 : 3 ^ (2 * (L + L) + 1 + Ly) ≤ Z ^ t) (hL : 2 * (L + L) + 1 + 2 ≤ Z ^ t) :
    E5D.cMA' s L Ly ≤ Z ^ (2 * p + 4 * t + 11) := by
  have F := fpBound'_z hZ hs h4 h3 hL
  have hs3 := zb_add' hs (zb_num (cnum (by norm_num : 3 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := p + 1) (by omega) (by omega)
  have G1 := zb_cmul (cnum (by norm_num : 600 ≤ 2 ^ 200) hZ) (zb_pow hs3 2)
  have G2 := zb_cmul (cnum (by norm_num : 200 ≤ 2 ^ 200) hZ) (zb_succ hs (hZ2 hZ))
  have H1 := zb_add' F G1 (hZ2 hZ) (r := 2 * p + 4 * t + 8) (by omega) (by omega)
  have H2 := zb_add' H1 G2 (hZ2 hZ) (r := 2 * p + 4 * t + 9) (by omega) (by omega)
  have H3 := zb_add' H2 (zb_num (cnum (by norm_num : 300 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := 2 * p + 4 * t + 10) (by omega) (by omega)
  unfold E5D.cMA'
  exact zb_mono H3 (by omega) (hZ1 hZ)

theorem cMergeReal'_z {s L Ly ck p q t : ℕ} (hs : s ≤ Z ^ p) (hck : ck ≤ Z ^ q) (hq : q ≤ 4 * p + 9)
    (h4 : 4 ^ (L + L + 1) ≤ Z ^ t) (h3 : 3 ^ (2 * (L + L) + 1 + Ly) ≤ Z ^ t) (hL : 2 * (L + L) + 1 + 2 ≤ Z ^ t) :
    E5D.cMergeReal' s L Ly ck ≤ Z ^ (7 * p + 4 * t + 24) := by
  have hcA := cA_z hZ hs hck hq
  have T1 := zb_cmul (cnum (by norm_num : 2 ≤ 2 ^ 200) hZ) (zb_mul hcA hs)
  have s5 := zb_cmul (cnum (by norm_num : 5 ≤ 2 ^ 200) hZ) hs
  have hma := cMA'_z hZ s5 h4 h3 hL
  have T2 := zb_mul hma s5
  have ss := zb_mul hs hs
  have w1 := zb_cmul (cnum (by norm_num : 900 ≤ 2 ^ 200) hZ) ss
  have w2 := zb_succ w1 (hZ2 hZ)
  have w3 := zb_cmul (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ) w2
  have T3 := zb_mul w3 w1
  have v1 := zb_add' T1 T2 (hZ2 hZ) (r := 7 * p + 4 * t + 21) (by omega) (by omega)
  have v2 := zb_add' v1 T3 (hZ2 hZ) (r := 7 * p + 4 * t + 22) (by omega) (by omega)
  have v3 := zb_add' v2 (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := 7 * p + 4 * t + 23) (by omega) (by omega)
  unfold E5D.cMergeReal'
  exact zb_mono v3 (by omega) (hZ1 hZ)

end zcalc

end E6b
end Lax117284Proofs.Treewidth.Fun
