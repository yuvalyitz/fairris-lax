import Lax117284Proofs.Treewidth.Fun.E1
import Lax117284Proofs.Treewidth.Fun.E2Norm
import Lax117284Proofs.Treewidth.Fun.E2Forget
import Lax117284Proofs.Treewidth.Fun.E2Join2
import Lax117284Proofs.Treewidth.Fun.E2Dom

/-!
# WP E2: the assembled interface — table `e2Tbl` (ids 160…182), concrete cost bounds with the E1 functions

`e2Tbl rid` (E2Defs) has the E2 functions; `rid` is the id of `ringTypList` in the assembled table.  With WP E1's table
(`E1.e1Tbl`, ids `128 … 157`, `ringTypList` at `E1C.fRingTypList = 152`) the combined table is `e12Tbl`.

**How the assembler uses this.**  Every theorem below is stated for an arbitrary table `Δ'` with `hΔ : e2Δ 152 ⊑ Δ'` and
`hE1 : E1.e1Δ ⊑ Δ'` (for the assembly `layerΔ Lib.Δ 128 (orElseΔ e1Tbl (orElseΔ (e2Tbl 152) e3Tbl))`, obtain both by
`Ext.layer_mono (Ext.orElse_left …)` / `Ext.layer_mono (Ext.orElse_right (disj) …)`; `e2Tbl_disj_e1` is the disjointness fact).
The ids are `E2.fNorm = 166`, `E2.fForgetC = 169`, `E2.fJoinC = 177`, `E2.fJoinKids = 178`, `E2.fDomC = 181`, `E2.fKeyLe`, `E2.fSortKids`, `E2.fVerts`.

| Lean function | id | arguments | theorem | cost |
|---|---|---|---|---|
| `CT.norm` | `fNorm` | `[c]` | `norm_runs_e12` | `6200 (s+1)^5`, `sz c ≤ s` |
| `CT.forgetC` | `fForgetC` | `[x, c]` | `forgetC_runs_e12` | `7000 (s+1)^5` |
| `CT.joinC` | `fJoinC` | `[kmax, a, b]` | `joinC_runs_e12` | `14000 (s+1) 2^(48 (|B|+kmax+2)^3)` for `Wf B kmax a, b`, `sz ≤ s` |
| `CT.domCB` | `fDomC` | `[a, b]` | `domC_runs_e12` | `(30 s + 60·3^(2L) + 100)·2 count a`, run sequences `≤ L` |
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT Lib1 Lax117284Proofs.Treewidth.Seq

/-- the E2 table is disjoint from the E1 table -/
theorem e2Tbl_disj_e1 (rid : ℕ) : ∀ f b, e2Tbl rid f = some b → E1.e1Tbl f = none := by
  intro f b h
  by_contra hne
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hne
  have h1 := E1.e1Tbl_lt hc
  have h2 := (e2Tbl_lt rid h).1
  omega

/-- the combined E1 + E2 table -/
def e12Tbl : ℕ → Option Tm := orElseΔ E1.e1Tbl (e2Tbl E1C.fRingTypList)
def e12Δ : ℕ → Option Tm := Lib.extend e12Tbl

/-! ## the interface with `ringTypList` -/

/-- the cost of one call of `ringTypList` on run sequences with entries `≤ k` and length `≤ 2k + 1` -/
def R0k (k : ℕ) : ℕ := 6000 * (2 * k + 2) ^ 2 * (4 ^ (2 * k + 1) + 1) ^ 2 * (4 * k + 3) ^ 2

theorem R0k_ge (k : ℕ) : 6000 * (2 * k + 2) ≤ R0k k := by
  unfold R0k
  have h1 : 0 < (4 ^ (2 * k + 1) + 1) ^ 2 := by positivity
  have h2 : 0 < (4 * k + 3) ^ 2 := by positivity
  have h3 : 1 ≤ (4 ^ (2 * k + 1) + 1) ^ 2 * (4 * k + 3) ^ 2 := Nat.mul_pos h1 h2
  have h4 : 2 * k + 2 ≤ (2 * k + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  generalize (4 ^ (2 * k + 1) + 1) ^ 2 = P at *
  generalize (4 * k + 3) ^ 2 = Q at *
  generalize (2 * k + 2) ^ 2 = R at *
  calc 6000 * (2 * k + 2) ≤ 6000 * R := Nat.mul_le_mul_left _ h4
    _ = 6000 * R * 1 := by ring
    _ ≤ 6000 * R * (P * Q) := Nat.mul_le_mul_left _ h3
    _ = 6000 * R * P * Q := by ring

theorem ringOK_e1 {Δ' : ℕ → Option Tm} (hE : E1C.Δ ⊑ Δ') (B kmax : ℕ) (hB : R0k kmax + 1000 < B) :
    RingOK Δ' B E1C.fRingTypList (R0k kmax) kmax := by
  intro y y' hy hy' hly hly'
  have h0 := R0k_ge kmax
  have h := E1C.ringTypList_runs hE B (by linarith) y y' kmax kmax hy hy' (by linarith)
  refine h.mono ?_
  unfold R0k
  have e1 : kmax + kmax + 1 = 2 * kmax + 1 := by omega
  have e2 : 2 * (kmax + kmax) + 1 + 2 = 4 * kmax + 3 := by omega
  rw [e1, e2]
  have h1 : y.length + 1 ≤ 2 * kmax + 2 := by omega
  have h2 : y'.length + 1 ≤ 2 * kmax + 2 := by omega
  have h3 : (y.length + 1) * (y'.length + 1) ≤ (2 * kmax + 2) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul h1 h2
  have e : 6000 * (y.length + 1) * (y'.length + 1) = 6000 * ((y.length + 1) * (y'.length + 1)) := by ring
  rw [e]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3))

/-! ## the pure-arithmetic bound on the `ringTypList` contribution -/

theorem sq_le_pow2 (m : ℕ) : (m + 1) ^ 2 ≤ 2 ^ (2 * m) := by
  have h : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  calc (m + 1) ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h 2
    _ = 2 ^ (2 * m) := by rw [← pow_mul, mul_comm]

theorem f_lin (m : ℕ) : (2 * m + 2) ^ 2 ≤ 2 ^ (2 * m + 2) := by
  calc (2 * m + 2) ^ 2 = 4 * (m + 1) ^ 2 := by ring
    _ ≤ 4 * 2 ^ (2 * m) := Nat.mul_le_mul_left _ (sq_le_pow2 m)
    _ = 2 ^ (2 * m + 2) := by rw [pow_add]; ring

theorem f_four (k : ℕ) : (4 ^ (2 * k + 1) + 1) ^ 2 ≤ 2 ^ (8 * k + 6) := by
  have e : 4 ^ (2 * k + 1) = 2 ^ (4 * k + 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; congr 1; ring
  have h1 : 4 ^ (2 * k + 1) + 1 ≤ 2 ^ (4 * k + 3) := by
    have hA : 1 ≤ 4 ^ (2 * k + 1) := Nat.one_le_pow _ _ (by norm_num)
    calc 4 ^ (2 * k + 1) + 1 ≤ 2 * 4 ^ (2 * k + 1) := by linarith
      _ = 2 ^ (4 * k + 3) := by rw [e, ← pow_succ']
  calc (4 ^ (2 * k + 1) + 1) ^ 2 ≤ (2 ^ (4 * k + 3)) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = 2 ^ (8 * k + 6) := by rw [← pow_mul]; congr 1; ring

theorem f_lin2 (k : ℕ) : (4 * k + 3) ^ 2 ≤ 2 ^ (2 * k + 4) := by
  have h1 : 4 * k + 3 ≤ 4 * 2 ^ k := by
    have : k < 2 ^ k := Nat.lt_two_pow_self
    omega
  calc (4 * k + 3) ^ 2 ≤ (4 * 2 ^ k) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = 2 ^ (2 * k + 4) := by
      rw [mul_pow, ← pow_mul, show (4 : ℕ) ^ 2 = 2 ^ 4 by norm_num, ← pow_add]; congr 1; ring

theorem arr4 (A X1 X2 X3 : ℕ) : A * (6000 * X1 * X2 * X3) = 6000 * (A * X1 * X2 * X3) := by ring

theorem join_R0_bound (nb k : ℕ) : (2 * nb + 2) ^ 2 * R0k k ≤ 6000 * 2 ^ (48 * (nb + k + 2) ^ 3) := by
  have f1 := f_lin nb
  have f2 := f_lin k
  have f3 := f_four k
  have f4 := f_lin2 k
  unfold R0k
  rw [arr4]
  have h5 : (2 * nb + 2) ^ 2 * (2 * k + 2) ^ 2 * (4 ^ (2 * k + 1) + 1) ^ 2 * (4 * k + 3) ^ 2 ≤
      2 ^ (2 * nb + 2) * 2 ^ (2 * k + 2) * 2 ^ (8 * k + 6) * 2 ^ (2 * k + 4) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul f1 f2) f3) f4
  have h6 : 2 ^ (2 * nb + 2) * 2 ^ (2 * k + 2) * 2 ^ (8 * k + 6) * 2 ^ (2 * k + 4) = 2 ^ (2 * nb + 12 * k + 14) := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
  have h7 : 2 * nb + 12 * k + 14 ≤ 48 * (nb + k + 2) ^ 3 := by
    have : nb + k + 2 ≤ (nb + k + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  have h8 : 2 ^ (2 * nb + 12 * k + 14) ≤ 2 ^ (48 * (nb + k + 2) ^ 3) := Nat.pow_le_pow_right (by norm_num) h7
  have h9 := le_trans (le_trans h5 (le_of_eq h6)) h8
  exact Nat.mul_le_mul_left 6000 h9

theorem join_fit_arith (s E R : ℕ) (hE : 1 ≤ E) (hR : R ≤ 6000 * E) :
    28000 * (s + 1) * E + 2000 * (s + 1) + 2000 + R + 1000 ≤ (14000 * (s + 1) * E + 2) ^ 2 := by
  have h1 : 1 ≤ (s + 1) * E := Nat.mul_pos (by omega) hE
  nlinarith [Nat.zero_le ((s + 1) * E), Nat.zero_le (s + 1)]

/-! ## the concrete statements -/

section concrete
variable {Δ' : ℕ → Option Tm} (hΔ : e2Δ E1C.fRingTypList ⊑ Δ') (hE1 : E1.e1Δ ⊑ Δ') (B : ℕ)
include hΔ hE1

theorem norm_runs_e12 (c : CT) (s : ℕ) (hc : sz c ≤ s) (hB : 14000 * (s + 1) ^ 5 < B) :
    Runs Δ' B fNorm [toVal c] (toVal (norm c)) (6200 * (s + 1) ^ 5) :=
  norm_runs hΔ (Ext.trans E1.extA hE1) B c s hc hB

theorem forgetC_runs_e12 (x : ℕ) (c : CT) (s : ℕ) (hc : sz c ≤ s) (hB : 14000 * (s + 1) ^ 5 + 100 < B) :
    Runs Δ' B fForgetC [toVal x, toVal c] (toVal (forgetC x c)) (7000 * (s + 1) ^ 5) :=
  forgetC_runs hΔ (Ext.trans E1.extA hE1) B x c s hc hB

/-- **`joinC`**: for `a, b` well-formed over the boundary `B0` with entries `≤ kmax` and sizes `≤ s`, cost
`14000 (s+1) 2^(48 (|B0| + kmax + 2)^3)` (the constant is symbolic; never evaluate it). -/
theorem joinC_runs_e12 {B0 : Finset ℕ} {kmax : ℕ} {a b : CT} (ha : a.Wf B0 kmax) (hb : b.Wf B0 kmax) (s : ℕ)
    (hsa : sz a ≤ s) (hsb : sz b ≤ s)
    (hB : 28000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3) + 2000 * (s + 1) + 2000 + R0k kmax + 1000 < B) :
    Runs Δ' B fJoinC [toVal kmax, toVal a, toVal b] (toVal (joinC kmax a b))
      (14000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3)) := by
  have hR := join_R0_bound B0.card kmax
  have hpos := Nat.zero_le ((s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3))
  have hE : 1 ≤ 2 ^ (48 * (B0.card + kmax + 2) ^ 3) := Nat.one_le_two_pow
  have hring := ringOK_e1 (Ext.trans E1.extC hE1) B kmax (by nlinarith)
  have h := joinC_runs hΔ B ha hb (R0k kmax) s hring hsa hsb (by nlinarith)
  refine h.mono ?_
  nlinarith

theorem domC_runs_e12 (L s : ℕ) (a b : CT) (hla : RB s L a) (hlb : RB s L b) (hsa : sz a ≤ s) (hsb : sz b ≤ s)
    (hB : (30 * s + 60 * 3 ^ (2 * L) + 100) * (2 * count a) + 1000 < B) :
    Runs Δ' B fDomC [toVal a, toVal b] (toVal (domCB a b)) ((30 * s + 60 * 3 ^ (2 * L) + 100) * (2 * count a)) :=
  domC_runs hΔ (Ext.trans E1.extA hE1) B L s a b hla hlb hsa hsb hB

/-! ### the `Fits` forms: the hypothesis on `B` is `(cost + 2)^2 < B` (what `Fits B v cost` provides) -/

theorem forgetC_runs_fits (x : ℕ) (c : CT) (s : ℕ) (hc : sz c ≤ s) (hfit : (7000 * (s + 1) ^ 5 + 2) ^ 2 < B) :
    Runs Δ' B fForgetC [toVal x, toVal c] (toVal (forgetC x c)) (7000 * (s + 1) ^ 5) := by
  have h1 : 1 ≤ (s + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  refine forgetC_runs_e12 hΔ hE1 B x c s hc (lt_of_le_of_lt ?_ hfit)
  nlinarith

theorem joinC_runs_fits {B0 : Finset ℕ} {kmax : ℕ} {a b : CT} (ha : a.Wf B0 kmax) (hb : b.Wf B0 kmax) (s : ℕ)
    (hsa : sz a ≤ s) (hsb : sz b ≤ s)
    (hfit : (14000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3) + 2) ^ 2 < B) :
    Runs Δ' B fJoinC [toVal kmax, toVal a, toVal b] (toVal (joinC kmax a b))
      (14000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3)) := by
  have hR := join_R0_bound B0.card kmax
  have hR1 : R0k kmax ≤ 6000 * 2 ^ (48 * (B0.card + kmax + 2) ^ 3) :=
    le_trans (Nat.le_mul_of_pos_left (R0k kmax) (Nat.pow_pos (by omega : 0 < 2 * B0.card + 2))) hR
  have hE : 1 ≤ 2 ^ (48 * (B0.card + kmax + 2) ^ 3) := Nat.one_le_two_pow
  exact joinC_runs_e12 hΔ hE1 B ha hb s hsa hsb (lt_of_le_of_lt (join_fit_arith s _ _ hE hR1) hfit)

end concrete

end E2
end Lax117284Proofs.Treewidth.Fun
