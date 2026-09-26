import Lax808846Proofs.Transfer
import Lax808846Proofs.Tactic
import Lax808846Proofs.Machine
import Mathlib.Tactic

/-!
A word RAM program run inside an IMP+ program: the definitions.

The oracle (the solver of the integer programs) is a raw word RAM program. To use it as a subroutine, an IMP+
program interprets it: the program text sits in four arrays (`ip0`..`ip3`, one entry per
instruction: opcode and three operands), the oracle's memory of `2 ^ wp` cells in the array `om`,
its input in the array `z`. Words of `wp` bits are simulated on exact naturals: every result is
reduced modulo `2 ^ wp` by an `and` with the mask `2 ^ wp - 1`, multiplication by a splitting of
the operands into halves so that no value exceeds `4 * 2 ^ wp`, and a left shift by a right-hand
mask. So the interpreter needs values below `8 * 2 ^ wp` only, whatever the true word length.

This file: the encoding of instructions, the state relation, and the arithmetic of the
simulated operations.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-! ### Instructions as numbers -/

/-- The opcode and the three operands of an instruction. -/
def code : Instr → ℕ × ℕ × ℕ × ℕ
  | .set a n => (0, a, n, 0)
  | .load a b => (1, a, b, 0)
  | .store a b => (2, a, b, 0)
  | .add a b c => (3, a, b, c)
  | .sub a b c => (4, a, b, c)
  | .mul a b c => (5, a, b, c)
  | .div a b c => (6, a, b, c)
  | .and a b c => (7, a, b, c)
  | .shiftl a b c => (8, a, b, c)
  | .not a b => (9, a, b, 0)
  | .jump l => (10, l, 0, 0)
  | .jzero a l => (11, a, l, 0)
  | .jeof l => (12, l, 0, 0)
  | .inputLength a => (13, a, 0, 0)
  | .inputLoad a b => (14, a, b, 0)
  | .halt => (15, 0, 0, 0)
  | .read a => (16, a, 0, 0)
  | .write a => (17, a, 0, 0)

/-- The largest number occurring in the text of an instruction. -/
def lits (i : Instr) : ℕ :=
  let c := code i
  max c.1 (max c.2.1 (max c.2.2.1 c.2.2.2))

lemma lit_le_lits (i : Instr) : (code i).1 ≤ lits i ∧ (code i).2.1 ≤ lits i ∧
    (code i).2.2.1 ≤ lits i ∧ (code i).2.2.2 ≤ lits i := by
  simp only [lits]; omega

/-! ### The state relation -/

/-- The four program arrays hold the text of `P`. -/
def ProgEnc (P : Program) (σ : Env) : Prop :=
  (σ.arrs "ip0").length = P.length ∧ (σ.arrs "ip1").length = P.length ∧
  (σ.arrs "ip2").length = P.length ∧ (σ.arrs "ip3").length = P.length ∧
  ∀ (j : ℕ) (i : Instr), P[j]? = some i →
    (σ.arrs "ip0").getD j 0 = (code i).1 ∧ (σ.arrs "ip1").getD j 0 = (code i).2.1 ∧
    (σ.arrs "ip2").getD j 0 = (code i).2.2.1 ∧ (σ.arrs "ip3").getD j 0 = (code i).2.2.2

/-- What never changes while the interpreter runs: the program, the input, the constants of the
word length. -/
structure KRel (P : Program) (z : List ℕ) (wp : ℕ) (σ : Env) : Prop where
  plen : σ.vars "plen" = P.length
  zl : σ.vars "zl" = z.length
  wpv : σ.vars "wpv" = wp
  Mp : σ.vars "Mp" = 2 ^ wp
  mask : σ.vars "mk" = 2 ^ wp - 1
  hh : σ.vars "hh" = (wp + 1) / 2
  hm : σ.vars "hm" = 2 ^ ((wp + 1) / 2) - 1
  hm2 : σ.vars "hm2" = 2 ^ (wp - (wp + 1) / 2) - 1
  zarr : σ.arrs "z" = z
  prog : ProgEnc P σ

/-- The scalars and arrays that move: the counter, the tape position, the memory, the output. -/
structure DRel (z : List ℕ) (wp v : ℕ) (σ : Env) (s : State) : Prop where
  spc : σ.vars "spc" = s.pc
  rd : σ.vars "rd" ≤ z.length
  inp : s.inp = z.drop (σ.vars "rd")
  input : s.input = z
  omlen : (σ.arrs "om").length = 2 ^ wp
  mem : ∀ a < 2 ^ wp, (σ.arrs "om").getD a 0 = s.mem a
  word : ∀ a, s.mem a < 2 ^ wp
  out : (s.out = [] ∧ σ.vars "nout" = 0) ∨ (s.out = [v] ∧ σ.vars "nout" = 1 ∧ σ.vars "outv" = v)

/-! ### The arithmetic of the simulated operations -/

/-- The product modulo `2 ^ wp`, from halves: with `h = (wp + 1) / 2`, `x = x1 * 2 ^ h + x0`. -/
def mulmod (wp x y : ℕ) : ℕ :=
  let h := (wp + 1) / 2
  (x % 2 ^ h * (y % 2 ^ h) +
    ((x / 2 ^ h * (y % 2 ^ h) + x % 2 ^ h * (y / 2 ^ h)) % 2 ^ (wp - h)) * 2 ^ h) % 2 ^ wp

theorem mulmod_core (wp h x0 x1 y0 y1 : ℕ) (h2 : wp ≤ 2 * h) (h3 : h ≤ wp) :
    (x0 * y0 + ((x1 * y0 + x0 * y1) % 2 ^ (wp - h)) * 2 ^ h) % 2 ^ wp
      = (x1 * 2 ^ h + x0) * (y1 * 2 ^ h + y0) % 2 ^ wp := by
  have hwp : 2 ^ wp = 2 ^ (wp - h) * 2 ^ h := by rw [← pow_add]; congr 1; omega
  have hS : ((x1 * y0 + x0 * y1) % 2 ^ (wp - h)) * 2 ^ h
      = (x1 * y0 + x0 * y1) * 2 ^ h % 2 ^ wp := by
    rw [hwp, Nat.mul_mod_mul_right]
  have hxy : (x1 * 2 ^ h + x0) * (y1 * 2 ^ h + y0)
      = x0 * y0 + (x1 * y0 + x0 * y1) * 2 ^ h + x1 * y1 * 2 ^ (2 * h) := by
    have : (2 : ℕ) ^ (2 * h) = 2 ^ h * 2 ^ h := by rw [two_mul, pow_add]
    rw [this]
    ring
  have hdvd : 2 ^ wp ∣ x1 * y1 * 2 ^ (2 * h) :=
    Dvd.dvd.mul_left (pow_dvd_pow 2 h2) _
  obtain ⟨q, hq⟩ := hdvd
  have hxy' : (x1 * 2 ^ h + x0) * (y1 * 2 ^ h + y0)
      = (x0 * y0 + (x1 * y0 + x0 * y1) * 2 ^ h) + 2 ^ wp * q := by
    rw [hxy, ← hq]
  rw [hxy', Nat.add_mul_mod_self_left, hS, Nat.add_mod_mod]

theorem mulmod_eq (wp x y : ℕ) : mulmod wp x y = x * y % 2 ^ wp := by
  unfold mulmod
  have hx : x = x / 2 ^ ((wp + 1) / 2) * 2 ^ ((wp + 1) / 2) + x % 2 ^ ((wp + 1) / 2) := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod x _).symm
  have hy : y = y / 2 ^ ((wp + 1) / 2) * 2 ^ ((wp + 1) / 2) + y % 2 ^ ((wp + 1) / 2) := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod y _).symm
  simp only []
  rw [mulmod_core wp _ _ _ _ _ (by omega) (by omega)]
  congr 1
  rw [← hx, ← hy]

end Lax117284Proofs.Machine.ClSim
