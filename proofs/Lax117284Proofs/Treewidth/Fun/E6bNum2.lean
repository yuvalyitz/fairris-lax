import Lax117284Proofs.Treewidth.Fun.E6bAsm

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6b (12): the node costs of `extract`

`Wx M k = Zc M k ^ pX` is the cost bound *per unit of `size²`*: `extract` on a nice tree with `s` nodes costs `≤ s² · Wx M k`.
The non-recursive work of a node is `≤ (its tables) + G`, with `G` from the table lengths (`Nt k = 2^(96 (k+2)^3)`),
the candidate costs (`cFgC`, `cInC`, `cJnC`) and the costs of `realIntro`/`realJoin` (`Zc^pRI`, `Zc^pRJ`).
The three numerical facts `cnode + G ≤ Wx` are the only arithmetic the induction needs.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

/-- the exponent of the per-node cost bound -/
def pX : ℕ := 60

/-- the per-node cost bound: `extract` on a nice tree with `s` nodes costs `s² · Wx M k` -/
def Wx (M k : ℕ) : ℕ := Zc M k ^ pX

/-- the number of table entries: `≤ 2^(96 Yk)` -/
def Nt (k : ℕ) : ℕ := 2 ^ (96 * Yk k)

/-- non-recursive overhead of a forget node (besides `tables` and the recursion) -/
def Gf (k : ℕ) : ℕ := 60 + 24 * Nt k + 6 + Nt k * cFgC k + cFgC k

/-- of an introduce node -/
def Gi (M k : ℕ) : ℕ :=
  100 + 60 * M ^ 2 + ((k + 2) * (28 * M + 120) + 60) + 24 * Nt k + 6 + Nt k * cInC M k + cInC M k + Zc M k ^ pRI

/-- of a join node -/
def Gj (M k : ℕ) : ℕ :=
  100 + 60 * M ^ 2 + 24 * Nt k + 6 + Nt k * (20 + 24 * Nt k + 6 + Nt k * cJnC k) +
    (20 + 24 * Nt k + 6 + Nt k * cJnC k + cJnC k + Zc M k ^ pRJ)

/-! ### the numerical facts -/

theorem Nt_z (M k : ℕ) : Nt k ≤ Zc M k ^ 1 := by
  unfold Nt; exact b_pow M k _ 1 (by omega)

theorem cnode_z (M k : ℕ) : E4.cnode M k ≤ Zc M k ^ 18 := by
  unfold E4.cnode
  have hZ := Zc_big M k
  have h1 := zb_pow (b_M M k) 15
  have h2 : 2 ^ (4000 * (k + 2) ^ 3) ≤ Zc M k ^ 3 := b_pow M k _ 3 (by unfold Yk; omega)
  have := zb_mul h1 h2
  exact zb_mono this (by omega) (hZ1 hZ)

theorem cFgC_z (M k : ℕ) : cFgC k ≤ Zc M k ^ 18 := by
  unfold cFgC
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have h1 := zb_succ (zb_cmul (cnum (by norm_num : 128 ≤ 2 ^ 200) hZ) (b_Y M k)) hZ2'
  have h2 := zb_cmul (cnum (by norm_num : 7000 ≤ 2 ^ 200) hZ) (zb_pow h1 5)
  have h3 := zb_cmul (cnum (by norm_num : 30 ≤ 2 ^ 200) hZ) (zb_cmul (cnum (by norm_num : 128 ≤ 2 ^ 200) hZ) (b_Y M k))
  have h4 := zb_add' h2 h3 hZ2' (r := 16) (by omega) (by omega)
  have h5 := zb_add' h4 (zb_num (cnum (by norm_num : 200 ≤ 2 ^ 200) hZ)) hZ2' (r := 17) (by omega) (by omega)
  exact zb_mono h5 (by omega) (hZ1 hZ)

theorem cMem_z (M k e : ℕ) (he : e ≤ 1728 * Yk k) :
    (30 * (128 * Yk k) + 24) * (2 ^ e + 1) + 8 ≤ Zc M k ^ 9 := by
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have h1 := zb_add' (zb_cmul (cnum (by norm_num : 30 ≤ 2 ^ 200) hZ)
    (zb_cmul (cnum (by norm_num : 128 ≤ 2 ^ 200) hZ) (b_Y M k))) (zb_num (cnum (by norm_num : 24 ≤ 2 ^ 200) hZ)) hZ2'
    (r := 3) (by omega) (by omega)
  have h2 := zb_succ (b_pow M k e 1 (by omega)) hZ2'
  have h3 := zb_mul h1 h2
  have h4 := zb_add' h3 (zb_num (cnum (by norm_num : 8 ≤ 2 ^ 200) hZ)) hZ2' (r := 6) (by omega) (by omega)
  exact zb_mono h4 (by omega) (hZ1 hZ)

theorem cInC_z (M k : ℕ) : cInC M k ≤ Zc M k ^ 21 := by
  unfold cInC cIntroCb cMemI
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have h1 := zb_add' (introCCost_z M k) (zb_num (cnum (by norm_num : 30 ≤ 2 ^ 200) hZ)) hZ2' (r := 18) (by omega)
    (by omega)
  have h2 := cMem_z M k (1728 * Yk k) le_rfl
  have h3 := zb_add' h1 h2 hZ2' (r := 19) (by omega) (by omega)
  have h4 := zb_add' h3 (zb_num (cnum (by norm_num : 300 ≤ 2 ^ 200) hZ)) hZ2' (r := 20) (by omega) (by omega)
  exact zb_mono h4 (by omega) (hZ1 hZ)

theorem cJnC_z (M k : ℕ) : cJnC k ≤ Zc M k ^ 12 := by
  unfold cJnC cJoinInner cMemJ
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have h1 := zb_succ (zb_cmul (cnum (by norm_num : 128 ≤ 2 ^ 200) hZ) (b_Y M k)) hZ2'
  have hP : 2 ^ (1296 * Yk k) ≤ Zc M k ^ 1 := b_pow M k _ 1 (by omega)
  have h2 := zb_mul (zb_cmul (cnum (by norm_num : 14000 ≤ 2 ^ 200) hZ) h1) hP
  have h3 := zb_add' h2 (zb_num (cnum (by norm_num : 30 ≤ 2 ^ 200) hZ)) hZ2' (r := 8) (by omega) (by omega)
  have h4 := cMem_z M k (432 * Yk k) (by omega)
  have h5 := zb_add' h3 h4 hZ2' (r := 9) (by omega) (by omega)
  have h6 := zb_add' h5 (zb_num (cnum (by norm_num : 400 ≤ 2 ^ 200) hZ)) hZ2' (r := 10) (by omega) (by omega)
  exact zb_mono h6 (by omega) (hZ1 hZ)

theorem numX_forget (M k : ℕ) : E4.cnode M k + Gf k ≤ Wx M k := by
  unfold Gf Wx pX
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have hN := Nt_z M k
  have hc := zb_mono (cFgC_z M k) le_rfl (hZ1 hZ)
  have a := zb_add' (zb_num (cnum (by norm_num : 60 ≤ 2 ^ 200) hZ)) (zb_cmul (cnum (by norm_num : 24 ≤ 2 ^ 200) hZ) hN)
    hZ2' (r := 2) (by omega) (by omega)
  have b := zb_add' a (zb_num (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ)) hZ2' (r := 3) (by omega) (by omega)
  have c := zb_add' b (zb_mul hN hc) hZ2' (r := 19) (by omega) (by omega)
  have d := zb_add' c hc hZ2' (r := 20) (by omega) (by omega)
  have e := zb_add' (cnode_z M k) d hZ2' (r := 21) (by omega) (by omega)
  exact zb_mono e (by omega) (hZ1 hZ)

theorem numX_intro (M k : ℕ) : E4.cnode M k + Gi M k ≤ Wx M k := by
  unfold Gi Wx pX
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have hN := Nt_z M k
  have hM := b_M M k
  have hM' : M ≤ Zc M k ^ 1 := by omega
  have a1 := zb_cmul (cnum (by norm_num : 60 ≤ 2 ^ 200) hZ) (zb_pow hM' 2)
  have a2 := zb_addm (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) a1 hZ2'
  have b1 := zb_addm (zb_cmul (cnum (by norm_num : 28 ≤ 2 ^ 200) hZ) hM') (zb_num (cnum (by norm_num : 120 ≤ 2 ^ 200) hZ)) hZ2'
  have b2 := zb_addm (zb_mul (b_k M k) b1) (zb_num (cnum (by norm_num : 60 ≤ 2 ^ 200) hZ)) hZ2'
  have a3 := zb_addm a2 b2 hZ2'
  have a4 := zb_addm a3 (zb_cmul (cnum (by norm_num : 24 ≤ 2 ^ 200) hZ) hN) hZ2'
  have a5 := zb_addm a4 (zb_num (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ)) hZ2'
  have a6 := zb_addm a5 (zb_mul hN (cInC_z M k)) hZ2'
  have a7 := zb_addm a6 (cInC_z M k) hZ2'
  have hp : Zc M k ^ pRI ≤ Zc M k ^ 40 := by unfold pRI; exact le_refl _
  have a8 := zb_addm a7 hp hZ2'
  have a9 := zb_addm (cnode_z M k) a8 hZ2'
  exact zb_mono a9 (by norm_num) (hZ1 hZ)

theorem numX_join (M k : ℕ) : E4.cnode M k + Gj M k ≤ Wx M k := by
  unfold Gj Wx pX
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have hN := Nt_z M k
  have hM := b_M M k
  have hM' : M ≤ Zc M k ^ 1 := by omega
  have hj := cJnC_z M k
  have a1 := zb_cmul (cnum (by norm_num : 60 ≤ 2 ^ 200) hZ) (zb_pow hM' 2)
  have a2 := zb_addm (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) a1 hZ2'
  have a3 := zb_addm a2 (zb_cmul (cnum (by norm_num : 24 ≤ 2 ^ 200) hZ) hN) hZ2'
  have a4 := zb_addm a3 (zb_num (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ)) hZ2'
  -- inner bracket `20 + 24 Nt + 6 + Nt * cJnC`
  have c1 := zb_addm (zb_num (cnum (by norm_num : 20 ≤ 2 ^ 200) hZ)) (zb_cmul (cnum (by norm_num : 24 ≤ 2 ^ 200) hZ) hN) hZ2'
  have c2 := zb_addm c1 (zb_num (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ)) hZ2'
  have c3 := zb_addm c2 (zb_mul hN hj) hZ2'
  have c4 := zb_mul hN c3
  have a5 := zb_addm a4 c4 hZ2'
  -- last bracket
  have d1 := zb_addm c2 (zb_mul hN hj) hZ2'
  have d2 := zb_addm d1 hj hZ2'
  have hp : Zc M k ^ pRJ ≤ Zc M k ^ 50 := by unfold pRJ; exact le_refl _
  have d3 := zb_addm d2 hp hZ2'
  have a6 := zb_addm a5 d3 hZ2'
  have a7 := zb_addm (cnode_z M k) a6 hZ2'
  exact zb_mono a7 (by norm_num) (hZ1 hZ)

/-! ## the algebra of the recursion `s ↦ s²` -/

theorem alg_one (s cn G X : ℕ) (hs : 1 ≤ s) (hX : cn + G ≤ X) :
    s * cn + G + s ^ 2 * X ≤ (s + 1) ^ 2 * X := by
  have h1 : s * cn + G ≤ s * X := by nlinarith
  have h2 : (s + 1) ^ 2 * X = s ^ 2 * X + (2 * s + 1) * X := by ring
  nlinarith

theorem alg_two (a b cn G X : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hX : cn + G ≤ X) :
    (a + b) * cn + G + a ^ 2 * X + b ^ 2 * X ≤ (a + b + 1) ^ 2 * X := by
  have h1 : (a + b) * cn + G ≤ (a + b) * X := by nlinarith
  have h2 : (a + b + 1) ^ 2 * X = a ^ 2 * X + b ^ 2 * X + (2 * a * b + 2 * a + 2 * b + 1) * X := by ring
  have h3 : (a + b) * X ≤ (2 * a * b + 2 * a + 2 * b + 1) * X := Nat.mul_le_mul_right _ (by nlinarith)
  omega

-- from now on `Wx` is opaque (its closed form is `E6bFinal.cost_closed`)
attribute [irreducible] Wx

end E6b
end Lax117284Proofs.Treewidth.Fun
