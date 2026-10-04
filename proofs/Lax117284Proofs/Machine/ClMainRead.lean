import Lax808846Proofs.Transfer
import Lax808846Proofs.Tactic
import Lax808846Proofs.Machine
import Mathlib.Tactic
import Lax117284Proofs.ClientsILPEquiv
import Lax117284Proofs.ClientsILPSize
import Lax117284Proofs.ClientsWord
import Lax117284Proofs.ClientsILPIndep

/-! ### `Lax117284Proofs.Machine.ClSimDefs` -/

section
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

end

/-! ### `Lax117284Proofs.Machine.ClSimEff` -/

section
/-!
The effect of every instruction as one shape: the state after it is the state before, changed at
one memory cell, at the program counter, at the tape position, and at the output, by five numbers
the interpreter computes (`EffData`).
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846.Ram Lax808846Proofs.Machine

/-- The state after an instruction, from the five numbers the interpreter computes: a flag and
an address and a value for the memory write, the next counter, the number of tape entries read,
a flag and a value for the output. -/
def EffData (w wf wa wv npc rdi wo wov : ℕ) (s : State) : State where
  pc := npc
  mem := if wf = 1 then setCell w s.mem wa wv else s.mem
  input := s.input
  inp := s.inp.drop rdi
  out := if wo = 1 then s.out ++ [wov] else s.out

/-- The left shift modulo `2 ^ wp`, without forming the shifted number. -/
def shlmod (wp x y : ℕ) : ℕ := if y < wp then (x % 2 ^ (wp - y)) * 2 ^ y else 0

theorem shlmod_eq (wp x y : ℕ) : shlmod wp x y = x * 2 ^ y % 2 ^ wp := by
  unfold shlmod
  split_ifs with h
  · have : 2 ^ wp = 2 ^ (wp - y) * 2 ^ y := by rw [← pow_add]; congr 1; omega
    rw [this, Nat.mul_mod_mul_right]
  · symm
    exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _)

theorem setCell_norm (w : ℕ) (m : ℕ → ℕ) (a v : ℕ) :
    setCell w m (a % 2 ^ w) (v % 2 ^ w) = setCell w m a v := by
  funext b
  simp only [setCell, Nat.mod_mod]

theorem eff_set (w a n : ℕ) (s : State) :
    (Instr.set a n).effect w s =
      some (EffData w 1 (a % 2 ^ w) (n % 2 ^ w) (s.pc + 1) 0 0 0 s) := by
  simp only [Instr.effect, EffData, setCell_norm]; simp

theorem eff_load (w a b : ℕ) (s : State) :
    (Instr.load a b).effect w s =
      some (EffData w 1 (a % 2 ^ w) (s.mem (s.mem (b % 2 ^ w) % 2 ^ w) % 2 ^ w) (s.pc + 1) 0 0 0 s) := by
  simp only [Instr.effect, EffData, setCell_norm]; simp

theorem eff_store (w a b : ℕ) (s : State) :
    (Instr.store a b).effect w s =
      some (EffData w 1 (s.mem (a % 2 ^ w)) (s.mem (b % 2 ^ w)) (s.pc + 1) 0 0 0 s) := by
  simp only [Instr.effect, EffData]; simp

theorem eff_add (w a b c : ℕ) (s : State) :
    (Instr.add a b c).effect w s =
      some (EffData w 1 (a % 2 ^ w) ((s.mem (b % 2 ^ w) + s.mem (c % 2 ^ w)) % 2 ^ w)
        (s.pc + 1) 0 0 0 s) := by
  simp only [Instr.effect, EffData, setCell_norm]; simp

theorem eff_sub (w a b c : ℕ) (s : State) :
    (Instr.sub a b c).effect w s =
      some (EffData w 1 (a % 2 ^ w) ((s.mem (b % 2 ^ w) - s.mem (c % 2 ^ w)) % 2 ^ w)
        (s.pc + 1) 0 0 0 s) := by
  simp only [Instr.effect, EffData, setCell_norm]; simp

theorem eff_mul (w a b c : ℕ) (s : State) :
    (Instr.mul a b c).effect w s =
      some (EffData w 1 (a % 2 ^ w) ((s.mem (b % 2 ^ w) * s.mem (c % 2 ^ w)) % 2 ^ w)
        (s.pc + 1) 0 0 0 s) := by
  simp only [Instr.effect, EffData, setCell_norm]; simp

theorem eff_div (w a b c : ℕ) (s : State) :
    (Instr.div a b c).effect w s =
      some (EffData w 1 (a % 2 ^ w) ((s.mem (b % 2 ^ w) / s.mem (c % 2 ^ w)) % 2 ^ w)
        (s.pc + 1) 0 0 0 s) := by
  simp only [Instr.effect, EffData, setCell_norm]; simp

theorem eff_and (w a b c : ℕ) (s : State) :
    (Instr.and a b c).effect w s =
      some (EffData w 1 (a % 2 ^ w) (Nat.land (s.mem (b % 2 ^ w)) (s.mem (c % 2 ^ w)) % 2 ^ w)
        (s.pc + 1) 0 0 0 s) := by
  simp only [Instr.effect, EffData, setCell_norm]; simp

theorem eff_shiftl (w a b c : ℕ) (s : State) :
    (Instr.shiftl a b c).effect w s =
      some (EffData w 1 (a % 2 ^ w) ((s.mem (b % 2 ^ w) * 2 ^ s.mem (c % 2 ^ w)) % 2 ^ w)
        (s.pc + 1) 0 0 0 s) := by
  simp only [Instr.effect, EffData, setCell_norm]; simp

theorem eff_not (w a b : ℕ) (s : State) :
    (Instr.not a b).effect w s =
      some (EffData w 1 (a % 2 ^ w) ((2 ^ w - 1 - s.mem (b % 2 ^ w)) % 2 ^ w) (s.pc + 1) 0 0 0 s) := by
  simp only [Instr.effect, EffData, setCell_norm]; simp

theorem eff_jump (w l : ℕ) (s : State) :
    (Instr.jump l).effect w s = some (EffData w 0 0 0 l 0 0 0 s) := by
  simp only [Instr.effect, EffData]; simp

theorem eff_jzero (w a l : ℕ) (s : State) :
    (Instr.jzero a l).effect w s =
      some (EffData w 0 0 0 (if s.mem (a % 2 ^ w) = 0 then l else s.pc + 1) 0 0 0 s) := by
  simp only [Instr.effect, EffData]; simp

theorem eff_jeof (w l : ℕ) (s : State) :
    (Instr.jeof l).effect w s =
      some (EffData w 0 0 0 (if s.inp.isEmpty then l else s.pc + 1) 0 0 0 s) := by
  simp only [Instr.effect, EffData]; simp

theorem eff_inputLength (w a : ℕ) (s : State) :
    (Instr.inputLength a).effect w s =
      some (EffData w 1 (a % 2 ^ w) (s.input.length % 2 ^ w) (s.pc + 1) 0 0 0 s) := by
  simp only [Instr.effect, EffData, setCell_norm]; simp

theorem eff_inputLoad (w a b : ℕ) (s : State) :
    (Instr.inputLoad a b).effect w s =
      some (EffData w 1 (a % 2 ^ w) ((s.input[s.mem (b % 2 ^ w) % 2 ^ w]?.getD 0) % 2 ^ w)
        (s.pc + 1) 0 0 0 s) := by
  simp only [Instr.effect, EffData, setCell_norm]; simp

theorem eff_write (w a : ℕ) (s : State) :
    (Instr.write a).effect w s =
      some (EffData w 0 0 0 (s.pc + 1) 0 1 (s.mem (a % 2 ^ w) % 2 ^ w) s) := by
  simp only [Instr.effect, EffData]; simp

theorem eff_read_some (w a v : ℕ) (rest : List ℕ) (s : State) (h : s.inp = v :: rest) :
    (Instr.read a).effect w s =
      some (EffData w 1 (a % 2 ^ w) (v % 2 ^ w) (s.pc + 1) 1 0 0 s) := by
  simp only [Instr.effect, EffData, setCell_norm, h]; simp

theorem eff_read_none (w a : ℕ) (s : State) (h : s.inp = []) :
    (Instr.read a).effect w s = none := by
  simp [Instr.effect, h]

end Lax117284Proofs.Machine.ClSim

end

/-! ### `Lax117284Proofs.Machine.ClSimCom` -/

section
/-!
The interpreter of word RAM programs, as an IMP+ command.

One iteration fetches the instruction at the counter `spc` from the program arrays, computes the
five numbers of `EffData` (`wf wa wv npc rdi wo wov`) in the block of its opcode, and commits them:
the memory write, the output, the counter, the tape position.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

abbrev V (s : String) : Expr := .var s
abbrev lit (n : ℕ) : Expr := .lit n
abbrev asg (x : String) (e : Expr) : Com := .assign x e

/-- Right-nested sequence. -/
def seqs : List Com → Com
  | [] => .skip
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- Fetch the instruction and the cells it names; reset the five numbers. -/
def fetchCom : Com := seqs [
  asg "op" (.get "ip0" (V "spc")), asg "fa" (.get "ip1" (V "spc")),
  asg "fb" (.get "ip2" (V "spc")), asg "fc" (.get "ip3" (V "spc")),
  asg "ra" (.and (V "fa") (V "mk")), asg "rb" (.and (V "fb") (V "mk")),
  asg "rc" (.and (V "fc") (V "mk")),
  asg "xa" (.get "om" (V "ra")), asg "xv" (.get "om" (V "rb")), asg "yv" (.get "om" (V "rc")),
  asg "xx" (.get "om" (V "xv")),
  asg "wf" (lit 0), asg "wa" (lit 0), asg "wv" (lit 0), asg "npc" (.add (V "spc") (lit 1)),
  asg "rdi" (lit 0), asg "wo" (lit 0), asg "wov" (lit 0)]

/-- The product of `xv` and `yv` modulo the word, from halves. -/
abbrev mulE : Expr :=
  .and (.add (.mul (.and (V "xv") (V "hm")) (.and (V "yv") (V "hm")))
    (.shiftl (.and (.add (.mul (.shiftr (V "xv") (V "hh")) (.and (V "yv") (V "hm")))
      (.mul (.and (V "xv") (V "hm")) (.shiftr (V "yv") (V "hh")))) (V "hm2")) (V "hh")))
    (V "mk")

/-- The left shift of `xv` by `yv` modulo the word. -/
abbrev shlBlock : Com :=
  .ite (.lt (V "yv") (V "wpv"))
    (asg "wv" (.shiftl (.and (V "xv") (.sub (.shiftl (lit 1) (.sub (V "wpv") (V "yv"))) (lit 1)))
      (V "yv")))
    .skip

/-- The block of each opcode. -/
def blk : ℕ → Com
  | 0 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" (.and (V "fb") (V "mk"))]
  | 1 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" (V "xx")]
  | 2 => seqs [asg "wf" (lit 1), asg "wa" (V "xa"), asg "wv" (V "xv")]
  | 3 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"),
      asg "wv" (.and (.add (V "xv") (V "yv")) (V "mk"))]
  | 4 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" (.sub (V "xv") (V "yv"))]
  | 5 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" mulE]
  | 6 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" (.div (V "xv") (V "yv"))]
  | 7 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" (.and (V "xv") (V "yv"))]
  | 8 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), shlBlock]
  | 9 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" (.sub (V "mk") (V "xv"))]
  | 10 => asg "npc" (V "fa")
  | 11 => .ite (.eq (V "xa") (lit 0)) (asg "npc" (V "fb")) .skip
  | 12 => .ite (.eq (V "rd") (V "zl")) (asg "npc" (V "fa")) .skip
  | 13 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" (.and (V "zl") (V "mk"))]
  | 14 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"),
      .ite (.lt (V "xv") (V "zl")) (asg "wv" (.and (.get "z" (V "xv")) (V "mk"))) .skip]
  | 15 => asg "npc" (V "plen")
  | 16 => .ite (.lt (V "rd") (V "zl"))
      (seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" (.and (.get "z" (V "rd")) (V "mk")),
        asg "rdi" (lit 1)])
      (asg "npc" (V "plen"))
  | 17 => seqs [asg "wo" (lit 1), asg "wov" (V "xa")]
  | _ => .skip

/-- The ladder of tests on the opcode, from `k`, for `n` more steps. -/
def dispN : ℕ → ℕ → Com
  | 0, _ => .skip
  | n + 1, k => .ite (.eq (V "op") (lit k)) (blk k) (dispN n (k + 1))

def dispatch : Com := dispN 18 0

/-- Commit: the memory write, the output, the counter, the tape position. -/
def commitCom : Com := seqs [
  .ite (.eq (V "wf") (lit 1)) (.store "om" (V "wa") (V "wv")) .skip,
  .ite (.eq (V "wo") (lit 1)) (.seq (asg "outv" (V "wov")) (asg "nout" (lit 1))) .skip,
  asg "spc" (V "npc"), asg "rd" (.add (V "rd") (V "rdi"))]

/-- One iteration. -/
def bodyCom : Com := .seq fetchCom (.seq dispatch commitCom)

/-- The interpreter: run until the counter leaves the program. -/
def interpLoop : Com := .while (.lt (V "spc") (V "plen")) bodyCom

end Lax117284Proofs.Machine.ClSim

end

/-! ### `Lax117284Proofs.Machine.ClSimBlk` -/

section
/-!
The blocks of the interpreter, one specification per opcode.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-- What the fetch has computed, for the instruction of operands `a b c` in the state `s`. -/
structure Fetched (wp : ℕ) (s : State) (o a b c : ℕ) (σ : Env) : Prop where
  op : σ.vars "op" = o
  fa : σ.vars "fa" = a
  fb : σ.vars "fb" = b
  fc : σ.vars "fc" = c
  ra : σ.vars "ra" = a % 2 ^ wp
  rb : σ.vars "rb" = b % 2 ^ wp
  rc : σ.vars "rc" = c % 2 ^ wp
  xa : σ.vars "xa" = s.mem (a % 2 ^ wp)
  xv : σ.vars "xv" = s.mem (b % 2 ^ wp)
  yv : σ.vars "yv" = s.mem (c % 2 ^ wp)
  xx : σ.vars "xx" = s.mem (s.mem (b % 2 ^ wp) % 2 ^ wp)
  xa_lt : σ.vars "xa" < 2 ^ wp
  xv_lt : σ.vars "xv" < 2 ^ wp
  yv_lt : σ.vars "yv" < 2 ^ wp
  xx_lt : σ.vars "xx" < 2 ^ wp
  wf : σ.vars "wf" = 0
  wa : σ.vars "wa" = 0
  wv : σ.vars "wv" = 0
  npc : σ.vars "npc" = s.pc + 1
  rdi : σ.vars "rdi" = 0
  wo : σ.vars "wo" = 0
  wov : σ.vars "wov" = 0

/-- What the block has computed: the effect of the instruction, or a stop at the end of the
program. -/
def Res (B wp pl : ℕ) (s : State) (o : Option State) (σ : Env) : Prop :=
  match o with
  | some s' => s' = EffData wp (σ.vars "wf") (σ.vars "wa") (σ.vars "wv") (σ.vars "npc")
      (σ.vars "rdi") (σ.vars "wo") (σ.vars "wov") s ∧
      (σ.vars "wf" = 1 → σ.vars "wa" < 2 ^ wp ∧ σ.vars "wv" < 2 ^ wp) ∧
      σ.vars "rd" + σ.vars "rdi" ≤ σ.vars "zl" ∧ σ.vars "wf" ≤ 1 ∧ σ.vars "wo" ≤ 1 ∧
      (σ.vars "wo" = 1 → σ.vars "wov" < 2 ^ wp) ∧ σ.vars "npc" < B
  | none => σ.vars "npc" = pl ∧ σ.vars "wf" = 0 ∧ σ.vars "wo" = 0 ∧ σ.vars "rdi" = 0

/-- The bound the blocks need. -/
def Bnd (B wp : ℕ) : Prop := 8 * 2 ^ wp + 32 < B

variable {B wp pl v : ℕ} {s : State} {P : Program} {z : List ℕ}

theorem mod_pow_lt (x wp : ℕ) : x % 2 ^ wp < 2 ^ wp := Nat.mod_lt _ (Nat.two_pow_pos wp)

set_option linter.unusedVariables false
set_option hygiene false in
/-- Unpack the context of a block, everywhere. -/
macro "blk_prep" : tactic => `(tactic| (
  all_goals have hFe := ‹Fetched _ _ _ _ _ _ _›
  all_goals have hop := hFe.op
  all_goals have hfa := hFe.fa
  all_goals have hfb := hFe.fb
  all_goals have hfc := hFe.fc
  all_goals have hra := hFe.ra
  all_goals have hrb := hFe.rb
  all_goals have hrc := hFe.rc
  all_goals have hxa := hFe.xa
  all_goals have hxv := hFe.xv
  all_goals have hyv := hFe.yv
  all_goals have hxx := hFe.xx
  all_goals have hxalt := hFe.xa_lt
  all_goals have hxvlt := hFe.xv_lt
  all_goals have hyvlt := hFe.yv_lt
  all_goals have hxxlt := hFe.xx_lt
  all_goals have hwf := hFe.wf
  all_goals have hwa := hFe.wa
  all_goals have hwv := hFe.wv
  all_goals have hnpc := hFe.npc
  all_goals have hrdi := hFe.rdi
  all_goals have hwo := hFe.wo
  all_goals have hwov := hFe.wov
  all_goals clear hFe
  all_goals obtain ⟨hplen, hzl, hwpv, hMp, hmask, hhh, hhm, hhm2, hzarr, hprog⟩ := ‹KRel _ _ _ _›
  all_goals obtain ⟨hspc, hrd, hinp, hinput, homlen, hmem, hword, hout⟩ := ‹DRel _ _ _ _ _›
  all_goals simp only [Bnd] at hB))

set_option hygiene false in
/-- Simplify the goals of a block with the facts of the fetch. -/
macro "blk_simp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  all_goals try simp [Res, EffData, Env.setVar, hfa, hfb, hfc, hra, hrb, hrc, hxa, hxv, hyv, hxx, hmask, hnpc,
    hrdi, hwo, hwov, hwf, hwa, hwv, hplen, hzl, hwpv, hMp, hhh, hhm, hhm2, mod_pow_lt, $ts,*])

set_option hygiene false in
/-- Close what is left: an arithmetic bound. -/
macro "blk_bnd" : tactic => `(tactic| all_goals first
    | omega
    | (refine lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos wp)) ?_; omega)
    | (refine lt_of_lt_of_le (hw _) ?_; omega)
    | (refine lt_of_le_of_lt (Nat.div_le_self _ _) ?_; refine lt_of_lt_of_le (hw _) ?_; omega)
    | (refine lt_of_le_of_lt Nat.and_le_left ?_; refine lt_of_lt_of_le (hw _) ?_; omega)
    | exact ⟨hw _, by omega⟩
    | exact ⟨lt_of_le_of_lt (Nat.div_le_self _ _) (hw _), by omega⟩
    | exact ⟨lt_of_le_of_lt Nat.and_le_left (hw _), by omega⟩)

/-- The precondition of every block. -/
abbrev Pre (P : Program) (z : List ℕ) (wp v : ℕ) (s : State) (o a b c : ℕ) (σ : Env) : Prop :=
  Fetched wp s o a b c σ ∧ KRel P z wp σ ∧ DRel z wp v σ s

macro "blk_open" : tactic => `(tactic| (run_vcg; blk_prep))

theorem blk0_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) (hlb : b < B) :
    Spec B (Pre P z wp v s 0 a b c) (blk 0)
      (fun σ σ' => Res B wp P.length s ((Instr.set a b).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  run_vcg
  blk_prep
  blk_simp [eff_set]
  blk_bnd

theorem blk1_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 1 a b c) (blk 1)
      (fun σ σ' => Res B wp P.length s ((Instr.load a b).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hmw : ∀ x, s.mem x % 2 ^ wp = s.mem x := fun x => Nat.mod_eq_of_lt (hw x)
  run_vcg
  blk_prep
  blk_simp [eff_load, hmw]
  blk_bnd

theorem blk2_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 2 a b c) (blk 2)
      (fun σ σ' => Res B wp P.length s ((Instr.store a b).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  run_vcg
  blk_prep
  blk_simp [eff_store]
  blk_bnd

theorem blk3_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 3 a b c) (blk 3)
      (fun σ σ' => Res B wp P.length s ((Instr.add a b c).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  run_vcg
  blk_prep
  blk_simp [eff_add]
  blk_bnd

theorem blk4_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 4 a b c) (blk 4)
      (fun σ σ' => Res B wp P.length s ((Instr.sub a b c).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hsub : ∀ x y, (s.mem x - s.mem y) % 2 ^ wp = s.mem x - s.mem y :=
    fun x y => Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) (hw x))
  run_vcg
  blk_prep
  blk_simp [eff_sub, hsub]
  blk_bnd

theorem blk6_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 6 a b c) (blk 6)
      (fun σ σ' => Res B wp P.length s ((Instr.div a b c).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hdiv : ∀ x y, (s.mem x / s.mem y) % 2 ^ wp = s.mem x / s.mem y :=
    fun x y => Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (hw x))
  run_vcg
  blk_prep
  blk_simp [eff_div, hdiv]
  blk_bnd

theorem blk7_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 7 a b c) (blk 7)
      (fun σ σ' => Res B wp P.length s ((Instr.and a b c).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hand : ∀ x y, (s.mem x &&& s.mem y) % 2 ^ wp = s.mem x &&& s.mem y :=
    fun x y => Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left (hw x))
  run_vcg
  blk_prep
  blk_simp [eff_and, hand]
  blk_bnd

theorem blk9_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 9 a b c) (blk 9)
      (fun σ σ' => Res B wp P.length s ((Instr.not a b).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hnot : ∀ x, (2 ^ wp - 1 - s.mem x) % 2 ^ wp = 2 ^ wp - 1 - s.mem x :=
    fun x => Nat.mod_eq_of_lt (by have := hw x; omega)
  run_vcg
  blk_prep
  blk_simp [eff_not, hnot]
  blk_bnd

theorem blk10_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) (hla : a < B) :
    Spec B (Pre P z wp v s 10 a b c) (blk 10)
      (fun σ σ' => Res B wp P.length s ((Instr.jump a).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  run_vcg
  blk_prep
  blk_simp [eff_jump]
  blk_bnd

theorem blk13_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B)
    (hzl' : z.length < B) :
    Spec B (Pre P z wp v s 13 a b c) (blk 13)
      (fun σ σ' => Res B wp P.length s ((Instr.inputLength a).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  run_vcg
  blk_prep
  blk_simp [eff_inputLength, hinput]
  blk_bnd

theorem blk15_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B)  :
    Spec B (Pre P z wp v s 15 a b c) (blk 15)
      (fun σ σ' => Res B wp P.length s (Instr.halt.effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  run_vcg
  blk_prep
  blk_simp [Lax808846Proofs.Machine.effect_halt]
  blk_bnd

theorem blk17_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 17 a b c) (blk 17)
      (fun σ σ' => Res B wp P.length s ((Instr.write a).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hmw : ∀ x, s.mem x % 2 ^ wp = s.mem x := fun x => Nat.mod_eq_of_lt (hw x)
  run_vcg
  blk_prep
  blk_simp [eff_write, hmw]
  blk_bnd

/-! ### The bounds inside a multiplication -/

section MulBounds

variable (wp X Y : ℕ)

theorem mb_pow_h : 2 ^ ((wp + 1) / 2) ≤ 2 ^ wp := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem mb_mask_h : 2 ^ ((wp + 1) / 2) - 1 < 2 ^ wp := by
  have := mb_pow_h wp; have := Nat.two_pow_pos ((wp + 1) / 2); omega

theorem mb_mask_k : 2 ^ (wp - (wp + 1) / 2) - 1 < 2 ^ wp := by
  have : 2 ^ (wp - (wp + 1) / 2) ≤ 2 ^ wp := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := Nat.two_pow_pos (wp - (wp + 1) / 2); omega

theorem mb_mod_h : X % 2 ^ ((wp + 1) / 2) < 2 ^ wp :=
  lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (mb_pow_h wp)

theorem mb_prod_low : X % 2 ^ ((wp + 1) / 2) * (Y % 2 ^ ((wp + 1) / 2)) < 2 * 2 ^ wp := by
  have h1 : X % 2 ^ ((wp + 1) / 2) < 2 ^ ((wp + 1) / 2) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h2 : Y % 2 ^ ((wp + 1) / 2) < 2 ^ ((wp + 1) / 2) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h3 : 2 ^ ((wp + 1) / 2) * 2 ^ ((wp + 1) / 2) ≤ 2 * 2 ^ wp := by
    calc 2 ^ ((wp + 1) / 2) * 2 ^ ((wp + 1) / 2) = 2 ^ ((wp + 1) / 2 + (wp + 1) / 2) := by
          rw [pow_add]
      _ ≤ 2 ^ (wp + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 * 2 ^ wp := by rw [pow_succ]; ring
  calc X % 2 ^ ((wp + 1) / 2) * (Y % 2 ^ ((wp + 1) / 2))
      < 2 ^ ((wp + 1) / 2) * 2 ^ ((wp + 1) / 2) := Nat.mul_lt_mul'' h1 h2
    _ ≤ 2 * 2 ^ wp := h3

theorem mb_cross1 (hX : X < 2 ^ wp) :
    X / 2 ^ ((wp + 1) / 2) * (Y % 2 ^ ((wp + 1) / 2)) < 2 ^ wp := by
  have h2 : Y % 2 ^ ((wp + 1) / 2) < 2 ^ ((wp + 1) / 2) := Nat.mod_lt _ (Nat.two_pow_pos _)
  calc X / 2 ^ ((wp + 1) / 2) * (Y % 2 ^ ((wp + 1) / 2))
      ≤ X / 2 ^ ((wp + 1) / 2) * 2 ^ ((wp + 1) / 2) := Nat.mul_le_mul_left _ h2.le
    _ ≤ X := Nat.div_mul_le_self _ _
    _ < 2 ^ wp := hX

theorem mb_cross2 (hY : Y < 2 ^ wp) :
    X % 2 ^ ((wp + 1) / 2) * (Y / 2 ^ ((wp + 1) / 2)) < 2 ^ wp := by
  have h1 : X % 2 ^ ((wp + 1) / 2) < 2 ^ ((wp + 1) / 2) := Nat.mod_lt _ (Nat.two_pow_pos _)
  calc X % 2 ^ ((wp + 1) / 2) * (Y / 2 ^ ((wp + 1) / 2))
      ≤ 2 ^ ((wp + 1) / 2) * (Y / 2 ^ ((wp + 1) / 2)) := Nat.mul_le_mul_right _ h1.le
    _ = Y / 2 ^ ((wp + 1) / 2) * 2 ^ ((wp + 1) / 2) := mul_comm _ _
    _ ≤ Y := Nat.div_mul_le_self _ _
    _ < 2 ^ wp := hY

theorem mb_cross_sum (hX : X < 2 ^ wp) (hY : Y < 2 ^ wp) :
    X / 2 ^ ((wp + 1) / 2) * (Y % 2 ^ ((wp + 1) / 2)) +
      X % 2 ^ ((wp + 1) / 2) * (Y / 2 ^ ((wp + 1) / 2)) < 2 * 2 ^ wp := by
  have := mb_cross1 wp X Y hX
  have := mb_cross2 wp X Y hY
  omega

theorem mb_mod_k (S : ℕ) : S % 2 ^ (wp - (wp + 1) / 2) < 2 ^ wp :=
  lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem mb_high (S : ℕ) : S % 2 ^ (wp - (wp + 1) / 2) * 2 ^ ((wp + 1) / 2) < 2 ^ wp := by
  have h1 : S % 2 ^ (wp - (wp + 1) / 2) < 2 ^ (wp - (wp + 1) / 2) :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have h3 : 2 ^ (wp - (wp + 1) / 2) * 2 ^ ((wp + 1) / 2) = 2 ^ wp := by
    rw [← pow_add]; congr 1; omega
  calc S % 2 ^ (wp - (wp + 1) / 2) * 2 ^ ((wp + 1) / 2)
      < 2 ^ (wp - (wp + 1) / 2) * 2 ^ ((wp + 1) / 2) :=
        Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
    _ = 2 ^ wp := h3

theorem mb_total (S : ℕ) :
    X % 2 ^ ((wp + 1) / 2) * (Y % 2 ^ ((wp + 1) / 2)) +
      S % 2 ^ (wp - (wp + 1) / 2) * 2 ^ ((wp + 1) / 2) < 3 * 2 ^ wp := by
  have := mb_prod_low wp X Y
  have := mb_high wp S
  omega

end MulBounds

set_option hygiene false in
macro "blk_mulbnd" : tactic => `(tactic| first
    | (refine lt_of_lt_of_le (mb_mod_h _ _) ?_; omega)
    | (refine lt_of_lt_of_le (mb_mask_h _) ?_; omega)
    | (refine lt_of_lt_of_le (mb_mask_k _) ?_; omega)
    | (refine lt_of_lt_of_le (mb_prod_low _ _ _) ?_; omega)
    | (refine lt_of_lt_of_le (mb_cross1 _ _ _ (hw _)) ?_; omega)
    | (refine lt_of_lt_of_le (mb_cross2 _ _ _ (hw _)) ?_; omega)
    | (refine lt_of_lt_of_le (mb_cross_sum _ _ _ (hw _) (hw _)) ?_; omega)
    | (refine lt_of_lt_of_le (mb_mod_k _ _) ?_; omega)
    | (refine lt_of_lt_of_le (mb_high _ _) ?_; omega)
    | (refine lt_of_lt_of_le (mb_total _ _ _ _) ?_; omega))

theorem blk5_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 5 a b c) (blk 5)
      (fun σ σ' => Res B wp P.length s ((Instr.mul a b c).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hwlt : wp < 2 ^ wp := Nat.lt_two_pow_self
  run_vcg
  blk_prep
  blk_simp [eff_mul, ← mulmod_eq, mulmod]
  all_goals first | blk_bnd | blk_mulbnd

set_option hygiene false in
/-- Close what is left in a block with a case split. -/
macro "blk_fin" : tactic => `(tactic| all_goals first
    | omega
    | (intro _; omega)
    | (refine lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos wp)) ?_; omega)
    | (exfalso; omega))

theorem blk11_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) (hlb : b < B) :
    Spec B (Pre P z wp v s 11 a b c) (blk 11)
      (fun σ σ' => Res B wp P.length s ((Instr.jzero a b).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hwB : ∀ x, s.mem x < B := fun x => lt_of_lt_of_le (hw x) (by have : 8 * 2 ^ wp + 32 < B := hB; omega)
  run_vcg
  blk_prep
  all_goals try simp_all [Res, eff_jzero, EffData, Env.setVar]
  blk_fin

theorem blk12_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) (hla : a < B)
    (hzB : z.length < B) :
    Spec B (Pre P z wp v s 12 a b c) (blk 12)
      (fun σ σ' => Res B wp P.length s ((Instr.jeof a).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hwB : ∀ x, s.mem x < B := fun x => lt_of_lt_of_le (hw x) (by have : 8 * 2 ^ wp + 32 < B := hB; omega)
  run_vcg
  blk_prep
  all_goals try simp_all [Res, eff_jeof, EffData, Env.setVar]
  blk_fin

theorem shl_lt (wp X Y : ℕ) (hy : Y < wp) : X % 2 ^ (wp - Y) * 2 ^ Y < 2 ^ wp := by
  have h1 : X % 2 ^ (wp - Y) < 2 ^ (wp - Y) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h3 : 2 ^ (wp - Y) * 2 ^ Y = 2 ^ wp := by rw [← pow_add]; congr 1; omega
  calc X % 2 ^ (wp - Y) * 2 ^ Y < 2 ^ (wp - Y) * 2 ^ Y :=
        Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
    _ = 2 ^ wp := h3

theorem blk8_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 8 a b c) (blk 8)
      (fun σ σ' => Res B wp P.length s ((Instr.shiftl a b c).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hwlt : wp < 2 ^ wp := Nat.lt_two_pow_self
  have hwB : ∀ x, s.mem x < B := fun x => lt_of_lt_of_le (hw x) (by have : 8 * 2 ^ wp + 32 < B := hB; omega)
  have hpw : 2 ^ (wp - s.mem (c % 2 ^ wp)) ≤ 2 ^ wp :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have e : (s.mem (b % 2 ^ wp) * 2 ^ s.mem (c % 2 ^ wp)) % 2 ^ wp =
      if s.mem (c % 2 ^ wp) < wp then s.mem (b % 2 ^ wp) % 2 ^ (wp - s.mem (c % 2 ^ wp)) *
        2 ^ s.mem (c % 2 ^ wp) else 0 := by
    rw [← shlmod_eq]; rfl
  by_cases hy : s.mem (c % 2 ^ wp) < wp
  · have hsl := shl_lt wp (s.mem (b % 2 ^ wp)) (s.mem (c % 2 ^ wp)) hy
    rw [if_pos hy] at e
    run_vcg
    blk_prep
    all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
    all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
    blk_simp [eff_shiftl, e]
    blk_fin
  · rw [if_neg hy] at e
    run_vcg
    blk_prep
    all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
    blk_simp [eff_shiftl, e]
    blk_fin

theorem blk14_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B)
    (hzB : z.length < B) (hzE : ∀ i, z.getD i 0 < B) (hzE' : ∀ i (h : i < z.length), z[i] < B) :
    Spec B (Pre P z wp v s 14 a b c) (blk 14)
      (fun σ σ' => Res B wp P.length s ((Instr.inputLoad a b).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hwB : ∀ x, s.mem x < B := fun x => lt_of_lt_of_le (hw x) (by have : 8 * 2 ^ wp + 32 < B := hB; omega)
  have hmw : ∀ x, s.mem x % 2 ^ wp = s.mem x := fun x => Nat.mod_eq_of_lt (hw x)
  run_vcg
  blk_prep
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
  all_goals try simp_all [Res, eff_inputLoad, EffData, Env.setVar, hmw, List.getD_eq_getElem?_getD]
  blk_fin

theorem drop_cons_facts {z : List ℕ} {r u : ℕ} {rest : List ℕ} (h : u :: rest = z.drop r) :
    ∃ hr : r < z.length, u = z[r] := by
  have hr : r < z.length := by
    by_contra hcon
    rw [List.drop_eq_nil_of_le (by omega)] at h
    cases h
  refine ⟨hr, ?_⟩
  rw [List.drop_eq_getElem_cons hr] at h
  exact (List.cons.inj h).1

theorem blk16_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B)
    (hzB : z.length < B) (hzE : ∀ i, z.getD i 0 < B) (hzE' : ∀ i (h : i < z.length), z[i] < B)  :
    Spec B (Pre P z wp v s 16 a b c) (blk 16)
      (fun σ σ' => Res B wp P.length s ((Instr.read a).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hwB : ∀ x, s.mem x < B := fun x => lt_of_lt_of_le (hw x) (by have : 8 * 2 ^ wp + 32 < B := hB; omega)
  rcases hcs : s.inp with _ | ⟨u, rest⟩
  · have hn := eff_read_none wp a s hcs
    run_vcg
    blk_prep
    all_goals
      have hk : z.length ≤ σ.vars "rd" := by
        have h2 : [] = z.drop (σ.vars "rd") := hcs ▸ hinp
        exact List.drop_eq_nil_iff.mp h2.symm
    all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
    all_goals try simp_all [Res, hn, EffData, Env.setVar]
    blk_fin
  · have hn := eff_read_some wp a u rest s hcs
    run_vcg
    blk_prep
    all_goals
      obtain ⟨hk, hku⟩ : ∃ hr : σ.vars "rd" < z.length, u = z[σ.vars "rd"] :=
        drop_cons_facts (hcs ▸ hinp)
    all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
    all_goals try simp_all [Res, hn, EffData, Env.setVar]
    blk_fin

end Lax117284Proofs.Machine.ClSim

end

/-! ### `Lax117284Proofs.Machine.ClSimDisp` -/

section
/-!
The ladder of tests on the opcode reaches the block of the instruction at hand, and the block's
specification is the instruction's.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

variable {B wp v : ℕ} {s : State} {P : Program} {z : List ℕ}

theorem cond_op_eval (σ : Env) (k : ℕ) (h1 : σ.vars "op" < B) (h2 : k < B) :
    (Cond.eq (V "op") (lit k)).evalB B σ = some (decide (σ.vars "op" = k)) := by
  rw [evalB_condEq (m := σ.vars "op") (n := k) (evalB_var h1) (evalB_lit h2)]
  by_cases h : σ.vars "op" = k <;> simp [h]

/-- The ladder: from `k`, with `n` rungs, reaches the block of `o`. -/
theorem dispN_spec {Pr : Env → Prop} {Q : Env → Env → Prop} {K : ℕ} (o : ℕ)
    (hop : ∀ σ, Pr σ → σ.vars "op" = o) (hB : 20 < B) :
    ∀ (n k : ℕ), k ≤ o → o < k + n → k + n ≤ 18 → Spec B Pr (blk o) Q K →
      Spec B Pr (dispN n k) Q (4 * (o - k + 1) + K) := by
  intro n
  induction n with
  | zero => intro k hk1 hk2; omega
  | succ n ih =>
    intro k hk1 hk2 hk3 hblk
    have hdef : ∀ σ, Pr σ → ∃ b, (Cond.eq (V "op") (lit k)).evalB B σ = some b := fun σ hσ =>
      ⟨_, cond_op_eval σ k (by rw [hop σ hσ]; omega) (by omega)⟩
    have hev : ∀ σ, Pr σ → (Cond.eq (V "op") (lit k)).evalB B σ = some (decide (o = k)) := by
      intro σ hσ
      rw [cond_op_eval σ k (by rw [hop σ hσ]; omega) (by omega), hop σ hσ]
    have main : Spec B Pr (dispN (n + 1) k) Q (1 + (Cond.eq (V "op") (lit k)).size +
        (4 * (o - k) + K)) := by
      refine Spec.ite hdef ?_ ?_
      · by_cases hko : k = o
        · subst hko
          exact (Spec.pre hblk (fun σ h => h.1)).mono (by omega)
        · intro σ ⟨hσ, hc⟩
          rw [hev σ hσ] at hc
          simp at hc
          omega
      · by_cases hko : k = o
        · intro σ ⟨hσ, hc⟩
          rw [hev σ hσ] at hc
          subst hko
          simp at hc
        · have := ih (k + 1) (by omega) (by omega) (by omega) hblk
          refine (Spec.pre this (fun σ h => h.1)).mono ?_
          omega
    refine Spec.mono main ?_
    simp only [Cond.size, Expr.size]
    omega

/-- What the blocks assume of the world. -/
structure Hyp (B wp : ℕ) (s : State) (P : Program) (z : List ℕ) : Prop where
  hB : Bnd B wp
  hw : ∀ x, s.mem x < 2 ^ wp
  hzB : z.length < B
  hzE : ∀ i, z.getD i 0 < B
  hzE' : ∀ i (h : i < z.length), z[i] < B
  hpl : P.length < B
  hpc : s.pc < P.length

theorem dispatch_of_blk {Q : Env → Env → Prop} {K : ℕ} (o a b c : ℕ) (hB : 20 < B) (ho : o < 18)
    (hblk : Spec B (Pre P z wp v s o a b c) (blk o) Q K) :
    Spec B (Pre P z wp v s o a b c) dispatch Q (4 * (o + 1) + K) := by
  have := dispN_spec (B := B) (Pr := Pre P z wp v s o a b c) (Q := Q) (K := K) o
    (fun σ h => h.1.op) hB 18 0 (by omega) (by omega) (by omega) hblk
  simpa [dispatch] using this

theorem dispatch_spec (i : Instr) (H : Hyp B wp s P z)
    (hL : (code i).2.1 < B ∧ (code i).2.2.1 < B ∧ (code i).2.2.2 < B) :
    Spec B (Pre P z wp v s (code i).1 (code i).2.1 (code i).2.2.1 (code i).2.2.2) dispatch
      (fun σ σ' => Res B wp P.length s (i.effect wp s) σ') 300 := by
  have hB20 : 20 < B := by have := H.hB; simp only [Bnd] at this; have := Nat.two_pow_pos wp; omega
  obtain ⟨hB, hw, hzB, hzE, hzE', hpl, hpc⟩ := H
  cases i with
  | set a n =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 0 a n 0 hB20 (by omega) (blk0_spec a n 0 hB hw hpc hpl hL.2.1)).mono (by omega)
  | load a b =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 1 a b 0 hB20 (by omega) (blk1_spec a b 0 hB hw hpc hpl)).mono (by omega)
  | store a b =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 2 a b 0 hB20 (by omega) (blk2_spec a b 0 hB hw hpc hpl)).mono (by omega)
  | add a b c =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 3 a b c hB20 (by omega) (blk3_spec a b c hB hw hpc hpl)).mono (by omega)
  | sub a b c =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 4 a b c hB20 (by omega) (blk4_spec a b c hB hw hpc hpl)).mono (by omega)
  | mul a b c =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 5 a b c hB20 (by omega) (blk5_spec a b c hB hw hpc hpl)).mono (by omega)
  | div a b c =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 6 a b c hB20 (by omega) (blk6_spec a b c hB hw hpc hpl)).mono (by omega)
  | and a b c =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 7 a b c hB20 (by omega) (blk7_spec a b c hB hw hpc hpl)).mono (by omega)
  | shiftl a b c =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 8 a b c hB20 (by omega) (blk8_spec a b c hB hw hpc hpl)).mono (by omega)
  | not a b =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 9 a b 0 hB20 (by omega) (blk9_spec a b 0 hB hw hpc hpl)).mono (by omega)
  | jump l =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 10 l 0 0 hB20 (by omega) (blk10_spec l 0 0 hB hw hpc hpl hL.1)).mono (by omega)
  | jzero a l =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 11 a l 0 hB20 (by omega) (blk11_spec a l 0 hB hw hpc hpl hL.2.1)).mono (by omega)
  | jeof l =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 12 l 0 0 hB20 (by omega) (blk12_spec l 0 0 hB hw hpc hpl hL.1 hzB)).mono (by omega)
  | inputLength a =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 13 a 0 0 hB20 (by omega) (blk13_spec a 0 0 hB hw hpc hpl hzB)).mono (by omega)
  | inputLoad a b =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 14 a b 0 hB20 (by omega) (blk14_spec a b 0 hB hw hpc hpl hzB hzE hzE')).mono (by omega)
  | halt =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 15 0 0 0 hB20 (by omega) (blk15_spec 0 0 0 hB hw hpc hpl)).mono (by omega)
  | read a =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 16 a 0 0 hB20 (by omega) (blk16_spec a 0 0 hB hw hpc hpl hzB hzE hzE')).mono (by omega)
  | write a =>
    simp only [code] at hL ⊢
    exact (dispatch_of_blk 17 a 0 0 hB20 (by omega) (blk17_spec a 0 0 hB hw hpc hpl)).mono (by omega)

end Lax117284Proofs.Machine.ClSim

end

/-! ### `Lax117284Proofs.Machine.ClSimStep` -/

section
/-!
One iteration of the interpreter: fetch, dispatch, commit.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

variable {B wp v : ℕ} {s : State} {P : Program} {z : List ℕ}

/-- The scalars a fetch assigns. -/
def FV : List String := ["op", "fa", "fb", "fc", "ra", "rb", "rc", "xa", "xv", "yv", "xx", "wf",
  "wa", "wv", "npc", "rdi", "wo", "wov"]

/-- `σ'` differs from `σ` only in the scalars of the list. -/
def AgreeOff (L : List String) (σ σ' : Env) : Prop :=
  σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧ ∀ y, y ∉ L → σ'.vars y = σ.vars y

theorem KRel.agree {σ σ' : Env} (h : KRel P z wp σ) (hA : AgreeOff FV σ σ') : KRel P z wp σ' := by
  obtain ⟨ha, -, -, hv⟩ := hA
  have hp : ProgEnc P σ' := by simpa [ProgEnc, ha] using h.prog
  exact ⟨by rw [hv "plen" (by decide)]; exact h.plen, by rw [hv "zl" (by decide)]; exact h.zl,
    by rw [hv "wpv" (by decide)]; exact h.wpv, by rw [hv "Mp" (by decide)]; exact h.Mp,
    by rw [hv "mk" (by decide)]; exact h.mask, by rw [hv "hh" (by decide)]; exact h.hh,
    by rw [hv "hm" (by decide)]; exact h.hm, by rw [hv "hm2" (by decide)]; exact h.hm2,
    by rw [ha]; exact h.zarr, hp⟩

theorem DRel.agree {σ σ' : Env} (h : DRel z wp v σ s) (hA : AgreeOff FV σ σ') : DRel z wp v σ' s := by
  obtain ⟨ha, -, -, hv⟩ := hA
  refine ⟨by rw [hv "spc" (by decide)]; exact h.spc, by rw [hv "rd" (by decide)]; exact h.rd,
    by rw [hv "rd" (by decide)]; exact h.inp, h.input, by rw [ha]; exact h.omlen,
    fun a ha' => by rw [ha]; exact h.mem a ha', h.word, ?_⟩
  rw [hv "nout" (by decide), hv "outv" (by decide)]
  exact h.out

set_option maxHeartbeats 3200000 in
theorem code_fst_le (i : Instr) : (code i).1 ≤ 17 := by cases i <;> simp [code]

set_option maxHeartbeats 3200000 in
theorem fetch_spec (i : Instr) (H : Hyp B wp s P z)
    (hL : (code i).2.1 < B ∧ (code i).2.2.1 < B ∧ (code i).2.2.2 < B) :
    Spec B (fun σ => KRel P z wp σ ∧ DRel z wp v σ s ∧ P[s.pc]? = some i) fetchCom
      (fun σ σ' => Fetched wp s (code i).1 (code i).2.1 (code i).2.2.1 (code i).2.2.2 σ' ∧
        AgreeOff FV σ σ') 200 := by
  obtain ⟨hB, hw, hzB, hzE, hzE', hpl, hpc'⟩ := H
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hB' : 8 * 2 ^ wp + 32 < B := hB
  have hwlt : ∀ x, s.mem x < 2 ^ wp := hw
  run_vcg
  all_goals
    obtain ⟨hplen, hzl, hwpv, hMp, hmask, hhh, hhm, hhm2, hzarr, hprog⟩ := ‹KRel P z wp _›
    obtain ⟨hspc, hrd, hinp, hinput, homlen, hmem, hword, hout⟩ := ‹DRel z wp v _ s›
    have hget := ‹P[s.pc]? = some i›
    obtain ⟨hl0, hl1, hl2, hl3, henc⟩ := hprog
    obtain ⟨he0, he1, he2, he3⟩ := henc s.pc i hget
    have hpc : s.pc < P.length := (List.getElem?_eq_some_iff.mp hget).1
    have hb0 : ∀ h : s.pc < (‹Env›.arrs "ip0").length, (‹Env›.arrs "ip0")[s.pc] = (code i).1 := by
      intro h; simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using he0
    have hb1 : ∀ h : s.pc < (‹Env›.arrs "ip1").length, (‹Env›.arrs "ip1")[s.pc] = (code i).2.1 := by
      intro h; simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using he1
    have hb2 : ∀ h : s.pc < (‹Env›.arrs "ip2").length, (‹Env›.arrs "ip2")[s.pc] = (code i).2.2.1 := by
      intro h; simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using he2
    have hb3 : ∀ h : s.pc < (‹Env›.arrs "ip3").length, (‹Env›.arrs "ip3")[s.pc] = (code i).2.2.2 := by
      intro h; simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using he3
    have hmem' : ∀ x, (‹Env›.arrs "om")[x % 2 ^ wp]?.getD 0 = s.mem (x % 2 ^ wp) :=
      fun x => by simpa [List.getD_eq_getElem?_getD] using hmem _ (Nat.mod_lt _ hpos)
    have hmemw : ∀ x, (‹Env›.arrs "om")[s.mem x]?.getD 0 = s.mem (s.mem x) :=
      fun x => by simpa [List.getD_eq_getElem?_getD] using hmem _ (hword x)
    have hmemI : ∀ (k : ℕ) (h : k < (‹Env›.arrs "om").length), (‹Env›.arrs "om")[k] = s.mem k :=
      fun k h => by
        have := hmem k (homlen ▸ h)
        simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using this
    have hop17 := code_fst_le i
    have hwB : ∀ x, s.mem x < B := fun x => lt_of_lt_of_le (hw x) (by omega)
    have hwL : ∀ x, s.mem x < (‹Env›.arrs "om").length := fun x => homlen ▸ hword x
    have hmodw : ∀ x, s.mem x % 2 ^ wp = s.mem x := fun x => Nat.mod_eq_of_lt (hw x)
  all_goals try simp only [Env.setVar, arrs_setVar, String.reduceEq, ↓reduceIte] at *
  all_goals try omega
  all_goals try
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      rfl, rfl, rfl, ?_⟩
  all_goals try simp [Env.setVar, hspc, hl0, hl1, hl2, hl3, he0, he1, he2, he3, hb0, hb1, hb2, hb3,
    hmask, hmem', hmemw, hpc, hplen, hzl, hwpv, hMp, hhh, hhm, hhm2, hword,
    hL.1, hL.2.1, hL.2.2, hwB, hwL, hmodw, hmemI]
  all_goals try omega
  all_goals try
    (intro y hy
     simp only [FV, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
     obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := hy
     simp [Env.setVar, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18])

/-- The environment after the commit, as a function. -/
def commitEnv (σ : Env) : Env :=
  let σ1 := if σ.vars "wf" = 1 then σ.setArr "om" (σ.vars "wa") (σ.vars "wv") else σ
  let σ2 := if σ1.vars "wo" = 1 then (σ1.setVar "outv" (σ1.vars "wov")).setVar "nout" 1 else σ1
  let σ3 := σ2.setVar "spc" (σ2.vars "npc")
  σ3.setVar "rd" (σ3.vars "rd" + σ3.vars "rdi")

theorem commit_run (hK : True) :
    Spec B (fun σ => σ.vars "wf" ≤ 1 ∧ σ.vars "wo" ≤ 1 ∧
        (σ.vars "wf" = 1 → σ.vars "wa" < (σ.arrs "om").length ∧ σ.vars "wa" < B ∧ σ.vars "wv" < B) ∧
        (σ.vars "wo" = 1 → σ.vars "wov" < B) ∧ σ.vars "npc" < B ∧
        σ.vars "rd" + σ.vars "rdi" < B ∧ 1 < B) commitCom
      (fun σ σ' => σ' = commitEnv σ) 100 := by
  run_vcg
  all_goals try simp_all [commitEnv, Env.setVar, Env.setArr]
  all_goals try omega

theorem commitEnv_vars (σ : Env) (y : String) : (commitEnv σ).vars y =
    if y = "rd" then σ.vars "rd" + σ.vars "rdi"
    else if y = "spc" then σ.vars "npc"
    else if y = "nout" ∧ σ.vars "wo" = 1 then 1
    else if y = "outv" ∧ σ.vars "wo" = 1 then σ.vars "wov"
    else σ.vars y := by
  unfold commitEnv
  by_cases h1 : σ.vars "wf" = 1 <;> by_cases h2 : σ.vars "wo" = 1 <;>
    by_cases hy1 : y = "rd" <;> by_cases hy2 : y = "spc" <;> by_cases hy3 : y = "nout" <;>
    by_cases hy4 : y = "outv" <;> simp [Env.setVar, Env.setArr, h1, h2, hy1, hy2, hy3, hy4]

theorem commitEnv_arrs (σ : Env) (a : String) : (commitEnv σ).arrs a =
    if a = "om" ∧ σ.vars "wf" = 1 then (σ.arrs "om").set (σ.vars "wa") (σ.vars "wv")
    else σ.arrs a := by
  unfold commitEnv
  by_cases h1 : σ.vars "wf" = 1 <;> by_cases h2 : σ.vars "wo" = 1 <;>
    by_cases ha : a = "om" <;> simp [Env.setVar, Env.setArr, h1, h2, ha]

/-- The state after a halt or a stop at the end of the program: the counter at the end. -/
def halted (P : Program) (s : State) : State := { s with pc := P.length }

theorem List.prefix_single_iff {α : Type*} (l : List α) (a b : α) :
    (l ++ [a]) <+: [b] → l = [] ∧ a = b := by
  intro h
  obtain ⟨t, ht⟩ := h
  cases l with
  | nil => simp at ht; exact ⟨rfl, ht.1⟩
  | cons x l => simp at ht

theorem commit_krel {σ : Env} (hK : KRel P z wp σ) : KRel P z wp (commitEnv σ) := by
  obtain ⟨hplen, hzl, hwpv, hMp, hmask, hhh, hhm, hhm2, hzarr, hprog⟩ := hK
  obtain ⟨hl0, hl1, hl2, hl3, henc⟩ := hprog
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [commitEnv_vars]; simp [hplen, hzl, hwpv, hMp, hmask, hhh, hhm, hhm2]; done)
    | (rw [commitEnv_arrs]; simp [hzarr]; done)
    | skip
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [commitEnv_arrs]; simpa using hl0
  · rw [commitEnv_arrs]; simpa using hl1
  · rw [commitEnv_arrs]; simpa using hl2
  · rw [commitEnv_arrs]; simpa using hl3
  · intro j i hj
    have := henc j i hj
    rw [commitEnv_arrs, commitEnv_arrs, commitEnv_arrs, commitEnv_arrs]
    simpa using this

theorem commit_drel_some {σ : Env} {s s' : State} (hD : DRel z wp v σ s)
    (hzl : σ.vars "zl" = z.length)
    (hR : Res B wp P.length s (some s') σ) (hp : s'.out <+: [v]) :
    DRel z wp v (commitEnv σ) s' := by
  simp only [Res] at hR
  obtain ⟨hs', hwa, hrd, hwf1, hwo1, hwov, hnpc⟩ := hR
  obtain ⟨hspc, hrd', hinp, hinput, homlen, hmem, hword, hout⟩ := hD
  subst hs'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [commitEnv_vars]; simp [EffData]
  · rw [commitEnv_vars]; simp only [if_true]; omega
  · rw [commitEnv_vars]; simp [EffData, hinp, List.drop_drop]
  · simp [EffData, hinput]
  · rw [commitEnv_arrs]; split_ifs <;> simp [homlen]
  · intro a ha
    rw [commitEnv_arrs]
    by_cases h1 : σ.vars "wf" = 1
    · obtain ⟨hwa1, hwv1⟩ := hwa h1
      have hlen : σ.vars "wa" < (σ.arrs "om").length := by rw [homlen]; exact hwa1
      simp only [h1, and_self, if_true, EffData, setCell, Nat.mod_eq_of_lt hwa1,
        Nat.mod_eq_of_lt hwv1]
      by_cases hae : a = σ.vars "wa"
      · subst hae
        simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hlen]
      · simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hae), hae]
        exact hmem a ha
    · simp only [h1, and_false, if_false, EffData]
      exact hmem a ha
  · intro a
    by_cases h1 : σ.vars "wf" = 1
    · obtain ⟨hwa1, hwv1⟩ := hwa h1
      simp only [h1, if_true, EffData, setCell]
      split_ifs
      · exact Nat.mod_lt _ (Nat.two_pow_pos wp)
      · exact hword a
    · simp only [h1, if_false, EffData]
      exact hword a
  · by_cases h2 : σ.vars "wo" = 1
    · simp only [h2, if_true, EffData] at hp ⊢
      obtain ⟨hs0, hv0⟩ := List.prefix_single_iff _ _ _ hp
      right
      refine ⟨by simp [hs0, hv0], ?_, ?_⟩
      · rw [commitEnv_vars]; simp [h2]
      · rw [commitEnv_vars]; simp [h2, hv0]
    · simp only [h2, if_false, EffData]
      rcases hout with ⟨h3, h4⟩ | ⟨h3, h4, h5⟩
      · left
        refine ⟨h3, ?_⟩
        rw [commitEnv_vars]; simpa [h2] using h4
      · right
        refine ⟨h3, ?_, ?_⟩
        · rw [commitEnv_vars]; simpa [h2] using h4
        · rw [commitEnv_vars]; simpa [h2] using h5

theorem commit_drel_none {σ : Env} {s : State} (hD : DRel z wp v σ s)
    (hzl : σ.vars "zl" = z.length)
    (hR : Res B wp P.length s none σ) : DRel z wp v (commitEnv σ) (halted P s) := by
  simp only [Res] at hR
  obtain ⟨hnpc, hwf, hwo, hrdi⟩ := hR
  obtain ⟨hspc, hrd', hinp, hinput, homlen, hmem, hword, hout⟩ := hD
  have hwf' : ¬ σ.vars "wf" = 1 := by omega
  have hwo' : ¬ σ.vars "wo" = 1 := by omega
  refine ⟨?_, ?_, ?_, hinput, ?_, ?_, hword, ?_⟩
  · rw [commitEnv_vars]; simp [halted, hnpc]
  · rw [commitEnv_vars]; simp [hrdi]; exact hrd'
  · rw [commitEnv_vars]; simp [halted, hrdi, hinp]
  · rw [commitEnv_arrs]; simp [hwf', homlen]
  · intro a ha
    rw [commitEnv_arrs]; simp [hwf', halted]
    exact hmem a ha
  · rcases hout with ⟨h3, h4⟩ | ⟨h3, h4, h5⟩
    · left
      refine ⟨h3, ?_⟩
      rw [commitEnv_vars]; simpa [hwo'] using h4
    · right
      refine ⟨h3, ?_, ?_⟩
      · rw [commitEnv_vars]; simpa [hwo'] using h4
      · rw [commitEnv_vars]; simpa [hwo'] using h5

end Lax117284Proofs.Machine.ClSim

end

/-! ### `Lax117284Proofs.Machine.ClSimBody` -/

section
/-!
One iteration of the interpreter agrees with one step of the machine.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B wp v : ℕ} {s : State} {P : Program} {z : List ℕ}

/-- The postcondition of an iteration: the machine's next state, or the stop. -/
def StepPost (B : ℕ) (P : Program) (z : List ℕ) (wp v : ℕ) (s : State) (σ' : Env) : Prop :=
  KRel P z wp σ' ∧ σ'.vars "spc" < B ∧ match step wp P s with
    | some s' => DRel z wp v σ' s'
    | none => DRel z wp v σ' (halted P s)

theorem commit_pre {σ : Env} {o : Option State} (H : Hyp B wp s P z) (hK : KRel P z wp σ)
    (hD : DRel z wp v σ s) (hR : Res B wp P.length s o σ) :
    σ.vars "wf" ≤ 1 ∧ σ.vars "wo" ≤ 1 ∧
      (σ.vars "wf" = 1 → σ.vars "wa" < (σ.arrs "om").length ∧ σ.vars "wa" < B ∧ σ.vars "wv" < B) ∧
      (σ.vars "wo" = 1 → σ.vars "wov" < B) ∧ σ.vars "npc" < B ∧
      σ.vars "rd" + σ.vars "rdi" < B ∧ 1 < B := by
  have hB := H.hB
  have hw := H.hw
  have hzB := H.hzB
  have hzE := H.hzE
  have hzE' := H.hzE'
  have hpl := H.hpl
  have hpc := H.hpc
  clear H
  have hB' : 8 * 2 ^ wp + 32 < B := hB
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have homlen := hD.omlen
  have hrd := hD.rd
  have hzl := hK.zl
  cases o with
  | none =>
    simp only [Res] at hR
    obtain ⟨hnpc, hwf, hwo, hrdi⟩ := hR
    refine ⟨by omega, by omega, fun h => by omega, fun h => by omega, by omega, by omega, by omega⟩
  | some s' =>
    simp only [Res] at hR
    obtain ⟨-, hwa, hrd2, hwf1, hwo1, hwov, hnpc⟩ := hR
    refine ⟨hwf1, hwo1, fun h => ?_, fun h => ?_, hnpc, by omega, by omega⟩
    · have := hwa h; refine ⟨by omega, by omega, by omega⟩
    · have := hwov h; omega

theorem dispatch_frame_ok : (∀ y ∈ dispatch.wvars, y ∈ FV) ∧ dispatch.warrs = [] ∧ ¬ dispatch.reads ∧
    dispatch.NoWrite := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem agree_of_frame {c : Com} (hv : ∀ y ∈ c.wvars, y ∈ FV) (ha : c.warrs = []) (hr : ¬ c.reads)
    (hw : c.NoWrite) {σ σ' : Env} (h1 : ∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y)
    (h2 : ∀ a, a ∉ c.warrs → σ'.arrs a = σ.arrs a) (h3 : ¬ c.reads → σ'.inp = σ.inp)
    (h4 : c.NoWrite → σ'.out = σ.out) : AgreeOff FV σ σ' :=
  ⟨funext fun a => h2 a (by simp [ha]), h3 hr, h4 hw,
    fun y hy => h1 y (fun hc => hy (hv y hc))⟩

theorem body_spec (H : Hyp B wp s P z) (i : Instr) (hi : P[s.pc]? = some i)
    (hL : (code i).2.1 < B ∧ (code i).2.2.1 < B ∧ (code i).2.2.2 < B)
    (hpref : ∀ s', step wp P s = some s' → s'.out <+: [v]) :
    Spec B (fun σ => KRel P z wp σ ∧ DRel z wp v σ s) bodyCom (fun _ σ' => StepPost B P z wp v s σ')
      600 := by
  have hf := Spec.pre (P' := fun σ => KRel P z wp σ ∧ DRel z wp v σ s) (fetch_spec (v := v) i H hL)
    (fun σ h => ⟨h.1, h.2, hi⟩)
  have hd := (dispatch_spec (v := v) i H hL).frame
  have hstep : step wp P s = i.effect wp s := by simp [step, hi]
  obtain ⟨hv, ha, hr, hw⟩ := dispatch_frame_ok
  have hd' : Spec B (Pre P z wp v s (code i).1 (code i).2.1 (code i).2.2.1 (code i).2.2.2)
      dispatch (fun σ σ' => Res B wp P.length s (i.effect wp s) σ' ∧ AgreeOff FV σ σ') 300 :=
    hd.post fun σ σ' _ ⟨hR, h1, h2, h3, h4⟩ =>
      ⟨hR, agree_of_frame hv ha hr hw h1 h2 h3 h4⟩
  have hc' : Spec B (fun σ => KRel P z wp σ ∧ DRel z wp v σ s ∧
      Res B wp P.length s (i.effect wp s) σ) commitCom (fun _ σ' => StepPost B P z wp v s σ') 100 := by
    refine (commit_run (B := B) trivial).conseq
      (fun σ ⟨hK, hD, hR⟩ => commit_pre H hK hD hR) ?_ le_rfl
    intro σ σ' ⟨hK, hD, hR⟩ hσ'
    subst hσ'
    refine ⟨commit_krel hK, ?_, ?_⟩
    · rw [commitEnv_vars]; simp only [String.reduceEq, if_false, if_true, and_false, ite_false]
      have := H.hpl
      cases hE : i.effect wp s with
      | none => rw [hE] at hR; simp only [Res] at hR; omega
      | some s' => rw [hE] at hR; simp only [Res] at hR; omega
    · rw [hstep]
      cases hE : i.effect wp s with
      | none => rw [hE] at hR; exact commit_drel_none hD hK.zl hR
      | some s' =>
        rw [hE] at hR
        exact commit_drel_some hD hK.zl hR (hpref s' (by rw [hstep, hE]))
  have h23 : Spec B (Pre P z wp v s (code i).1 (code i).2.1 (code i).2.2.1 (code i).2.2.2)
      (.seq dispatch commitCom) (fun _ σ' => StepPost B P z wp v s σ') 400 := by
    refine Spec.seq hd' hc' ?_ ?_
    · rintro σ σ' ⟨hF, hK, hD⟩ ⟨hR, hA⟩
      exact ⟨hK.agree hA, hD.agree hA, hR⟩
    · intro σ σ' σ'' _ _ h
      exact h
  refine Spec.seq (P' := Pre P z wp v s (code i).1 (code i).2.1 (code i).2.2.1 (code i).2.2.2)
    hf h23 ?_ ?_
  · rintro σ σ' ⟨hK, hD⟩ ⟨hF, hA⟩
    exact ⟨hF, hK.agree hA, hD.agree hA⟩
  · intro σ σ' σ'' _ _ h
    exact h

end Lax117284Proofs.Machine.ClSim

end

/-! ### `Lax117284Proofs.Machine.ClSimRun` -/

section
/-!
The interpreter loop runs the machine to its halt: induction on the number of transitions.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B wp v : ℕ} {P : Program} {z : List ℕ}

/-- The assumptions on the world that do not depend on the state. -/
structure HypS (B wp : ℕ) (P : Program) (z : List ℕ) : Prop where
  hB : Bnd B wp
  hzB : z.length < B
  hzE : ∀ i, z.getD i 0 < B
  hzE' : ∀ i (h : i < z.length), z[i] < B
  hpl : P.length < B
  hLits : ∀ i ∈ P, (code i).2.1 < B ∧ (code i).2.2.1 < B ∧ (code i).2.2.2 < B

/-- The relation at the end of the run: everything but the counter, which is at or past the end
of the program. -/
def Fin' (P : Program) (z : List ℕ) (wp v : ℕ) (σ : Env) (s : State) : Prop :=
  DRel z wp v σ { s with pc := σ.vars "spc" } ∧ P.length ≤ σ.vars "spc"

theorem run_while_step {b : Cond} {c : Com} {σ σ1 σ2 : Env} {K1 K2 : ℕ}
    (hb : b.evalB B σ = some true) (h1 : Run B c σ σ1 K1) (h2 : Run B (.while b c) σ1 σ2 K2) :
    Run B (.while b c) σ σ2 (1 + b.size + K1 + K2) := by
  obtain ⟨k1, hk1, b1⟩ := h1
  obtain ⟨k2, hk2, b2⟩ := h2
  exact ⟨1 + b.size + k1 + k2, by omega, .while_true hb b1 b2⟩

theorem loopCond_eval (σ : Env) (h1 : σ.vars "spc" < B) (h2 : σ.vars "plen" < B) :
    (Cond.lt (V "spc") (V "plen")).evalB B σ = some (decide (σ.vars "spc" < σ.vars "plen")) :=
  evalB_condLt (evalB_var h1) (evalB_var h2)

theorem run_out_prefix {w : ℕ} {p : Program} : ∀ (n : ℕ) (s s' : State),
    run w p n s = some s' → s.out <+: s'.out := by
  intro n
  induction n with
  | zero => intro s s' h; simp only [run, Option.some.injEq] at h; subst h; exact List.prefix_refl _
  | succ n ih =>
    intro s s' h
    simp only [run] at h
    obtain ⟨s1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    refine (?_ : s.out <+: s1.out).trans (ih s1 s' h2)
    unfold step at h1
    rcases hp : p[s.pc]? with _ | i
    · simp [hp] at h1
    · rw [hp] at h1
      simp only [Option.bind_some] at h1
      cases i <;> simp only [Instr.effect] at h1
      case halt => cases h1
      case read a =>
        obtain ⟨u, -, rfl⟩ := Option.map_eq_some_iff.mp h1
        exact List.prefix_refl _
      case write a =>
        obtain rfl := Option.some.inj h1
        exact List.prefix_append _ _
      all_goals (obtain rfl := Option.some.inj h1; exact List.prefix_refl _)

theorem hyp_of {σ : Env} {s : State} (HS : HypS B wp P z) (hD : DRel z wp v σ s)
    (hpc : σ.vars "spc" < P.length) : Hyp B wp s P z :=
  ⟨HS.hB, hD.word, HS.hzB, HS.hzE, HS.hzE', HS.hpl, by rw [← hD.spc]; exact hpc⟩

theorem fin_of_ge {σ : Env} {s : State} (hD : DRel z wp v σ s) (hK : KRel P z wp σ)
    (hge : ¬ σ.vars "spc" < P.length) : Fin' P z wp v σ s := by
  refine ⟨?_, by omega⟩
  have : ({ s with pc := σ.vars "spc" } : State) = s := by rw [hD.spc]
  rw [this]; exact hD

theorem loop_run (HS : HypS B wp P z) (sf : State) (hfin : sf.out = [v])
    (hhalt : step wp P sf = none) :
    ∀ (n : ℕ) (s : State) (σ : Env), KRel P z wp σ → DRel z wp v σ s → σ.vars "spc" < B →
      run wp P n s = some sf →
      ∃ σ', Run B interpLoop σ σ' ((n + 1) * 604 + 4) ∧ KRel P z wp σ' ∧ Fin' P z wp v σ' sf := by
  intro n
  induction n with
  | zero =>
    intro s σ hK hD hsB hrun
    simp only [run, Option.some.injEq] at hrun
    subst hrun
    have hplB : σ.vars "plen" < B := by rw [hK.plen]; exact HS.hpl
    by_cases hpc : σ.vars "spc" < P.length
    · have hs := hyp_of HS hD hpc
      obtain ⟨i, hi⟩ : ∃ i, P[s.pc]? = some i :=
        ⟨P[s.pc]'(by rw [← hD.spc]; exact hpc), List.getElem?_eq_getElem _⟩
      have hbody := body_spec (v := v) hs i hi (HS.hLits i (List.mem_of_getElem? hi))
        (fun s' h => by rw [hhalt] at h; cases h)
      obtain ⟨σ1, hr1, hK1, hB1, hpost⟩ := hbody σ ⟨hK, hD⟩
      rw [hhalt] at hpost
      dsimp only at hpost
      have hsp : σ1.vars "spc" = P.length := hpost.spc
      have hct : (Cond.lt (V "spc") (V "plen")).evalB B σ = some true := by
        rw [loopCond_eval σ hsB hplB]; simp [hK.plen, hpc]
      have hcf : (Cond.lt (V "spc") (V "plen")).evalB B σ1 = some false := by
        rw [loopCond_eval σ1 hB1 (by rw [hK1.plen]; exact HS.hpl)]
        simp [hK1.plen, hsp]
      refine ⟨σ1, ((run_while_step hct hr1 (Run.while_false hcf)).mono (by simp [Cond.size])),
        hK1, ?_, by rw [hsp]⟩
      have : ({ s with pc := σ1.vars "spc" } : State) = halted P s := by
        rw [hsp]; rfl
      rw [this]; exact hpost
    · have hcf : (Cond.lt (V "spc") (V "plen")).evalB B σ = some false := by
        rw [loopCond_eval σ hsB hplB]; simp [hK.plen, hpc]
      exact ⟨σ, (Run.while_false hcf).mono (by simp [Cond.size]), hK, fin_of_ge hD hK hpc⟩
  | succ n ih =>
    intro s σ hK hD hsB hrun
    have hplB : σ.vars "plen" < B := by rw [hK.plen]; exact HS.hpl
    simp only [run] at hrun
    obtain ⟨s1, hs1, hrun1⟩ := Option.bind_eq_some_iff.mp hrun
    have hpc : σ.vars "spc" < P.length := by
      by_contra hcon
      have := Lax808846Proofs.Machine.step_none_of_length_le (w := wp) (p := P) (s := s) (by rw [← hD.spc]; omega)
      rw [this] at hs1; cases hs1
    have hs := hyp_of HS hD hpc
    obtain ⟨i, hi⟩ : ∃ i, P[s.pc]? = some i :=
      ⟨P[s.pc]'(by rw [← hD.spc]; exact hpc), List.getElem?_eq_getElem _⟩
    have hpref : ∀ s', step wp P s = some s' → s'.out <+: [v] := by
      intro s' h
      rw [hs1] at h
      cases h
      have := run_out_prefix n s1 sf hrun1
      rw [hfin] at this
      exact this
    have hbody := body_spec (v := v) hs i hi (HS.hLits i (List.mem_of_getElem? hi)) hpref
    obtain ⟨σ1, hr1, hK1, hB1, hpost⟩ := hbody σ ⟨hK, hD⟩
    rw [hs1] at hpost
    obtain ⟨σ', hr2, hK2, hF⟩ := ih s1 σ1 hK1 hpost hB1 hrun1
    have hct : (Cond.lt (V "spc") (V "plen")).evalB B σ = some true := by
      rw [loopCond_eval σ hsB hplB]; simp [hK.plen, hpc]
    refine ⟨σ', (run_while_step hct hr1 hr2).mono (by simp [Cond.size]; nlinarith), hK2, hF⟩

end Lax117284Proofs.Machine.ClSim

end

/-! ### `Lax117284Proofs.Machine.ClSimLoad` -/

section
/-!
Loading the text of the program into its four arrays, and setting the constants of the word length.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The stores of one instruction at position `j`. -/
def storeInstr (j : ℕ) (i : Instr) : Com :=
  .seq (.store "ip0" (lit j) (lit (code i).1))
    (.seq (.store "ip1" (lit j) (lit (code i).2.1))
      (.seq (.store "ip2" (lit j) (lit (code i).2.2.1))
        (.store "ip3" (lit j) (lit (code i).2.2.2))))

/-- The stores of a list of instructions, from position `j`. -/
def loadFrom : ℕ → List Instr → Com
  | _, [] => .skip
  | j, i :: rest => .seq (storeInstr j i) (loadFrom (j + 1) rest)

/-- The array `A'` is `A` with the numbers `fs` written from position `j`. -/
def ArrLoad (A A' : List ℕ) (j : ℕ) (fs : List ℕ) : Prop :=
  A'.length = A.length ∧
    ∀ t, A'.getD t 0 = if j ≤ t ∧ t - j < fs.length then fs.getD (t - j) 0 else A.getD t 0

theorem ArrLoad.nil (A : List ℕ) (j : ℕ) : ArrLoad A A j [] := ⟨rfl, fun t => by simp⟩

theorem ArrLoad.cons {A A1 A' : List ℕ} {j x : ℕ} {fs : List ℕ} (hj : j < A.length)
    (h1 : A1 = A.set j x) (h : ArrLoad A1 A' (j + 1) fs) : ArrLoad A A' j (x :: fs) := by
  obtain ⟨hl, ht⟩ := h
  refine ⟨by rw [hl, h1, List.length_set], fun t => ?_⟩
  rw [ht t]
  by_cases hj1 : j + 1 ≤ t ∧ t - (j + 1) < fs.length
  · have : j ≤ t ∧ t - j < (x :: fs).length := ⟨by omega, by simp; omega⟩
    rw [if_pos hj1, if_pos this]
    have : t - j = (t - (j + 1)) + 1 := by omega
    rw [this]; simp
  · rw [if_neg hj1]
    by_cases htj : t = j
    · subst htj
      have : t ≤ t ∧ t - t < (x :: fs).length := ⟨le_rfl, by simp⟩
      rw [if_pos this, h1]
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hj]
    · have : ¬ (j ≤ t ∧ t - j < (x :: fs).length) := by
        intro ⟨h1', h2'⟩; simp at h2'; omega
      rw [if_neg this, h1]
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm htj)]

/-- The effect of loading the instructions of `l` from position `j`. -/
def Loaded (j : ℕ) (l : List Instr) (σ σ' : Env) : Prop :=
  σ'.vars = σ.vars ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
  (∀ a, a ≠ "ip0" → a ≠ "ip1" → a ≠ "ip2" → a ≠ "ip3" → σ'.arrs a = σ.arrs a) ∧
  ArrLoad (σ.arrs "ip0") (σ'.arrs "ip0") j (l.map fun i => (code i).1) ∧
  ArrLoad (σ.arrs "ip1") (σ'.arrs "ip1") j (l.map fun i => (code i).2.1) ∧
  ArrLoad (σ.arrs "ip2") (σ'.arrs "ip2") j (l.map fun i => (code i).2.2.1) ∧
  ArrLoad (σ.arrs "ip3") (σ'.arrs "ip3") j (l.map fun i => (code i).2.2.2)

theorem arrLoad_single {A : List ℕ} {j x : ℕ} (hj : j < A.length) : ArrLoad A (A.set j x) j [x] :=
  ArrLoad.cons hj rfl (ArrLoad.nil _ _)

variable {B : ℕ}

theorem storeInstr_spec (j : ℕ) (i : Instr) (hjB : j < B) (hi : lits i < B) :
    Spec B (fun σ => j < (σ.arrs "ip0").length ∧ j < (σ.arrs "ip1").length ∧
        j < (σ.arrs "ip2").length ∧ j < (σ.arrs "ip3").length) (storeInstr j i)
      (fun σ σ' => Loaded j [i] σ σ') 20 := by
  have h1 := lit_le_lits i
  run_vcg
  all_goals try
    obtain ⟨hj0, hj1, hj2, hj3⟩ : j < (‹Env›.arrs "ip0").length ∧ j < (‹Env›.arrs "ip1").length ∧
      j < (‹Env›.arrs "ip2").length ∧ j < (‹Env›.arrs "ip3").length := ⟨‹_›, ‹_›, ‹_›, ‹_›⟩
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro a h0 h1 h2 h3; simp [Env.setArr, h0, h1, h2, h3]
    · simpa [Env.setArr] using arrLoad_single (x := (code i).1) hj0
    · simpa [Env.setArr] using arrLoad_single (x := (code i).2.1) hj1
    · simpa [Env.setArr] using arrLoad_single (x := (code i).2.2.1) hj2
    · simpa [Env.setArr] using arrLoad_single (x := (code i).2.2.2) hj3

theorem ArrLoad.comp {A A1 A' : List ℕ} {j x : ℕ} {fs : List ℕ} (h1 : ArrLoad A A1 j [x])
    (h2 : ArrLoad A1 A' (j + 1) fs) : ArrLoad A A' j (x :: fs) := by
  obtain ⟨hl1, ht1⟩ := h1
  obtain ⟨hl2, ht2⟩ := h2
  refine ⟨by rw [hl2, hl1], fun t => ?_⟩
  rw [ht2 t]
  by_cases hin : j + 1 ≤ t ∧ t - (j + 1) < fs.length
  · have : j ≤ t ∧ t - j < (x :: fs).length := ⟨by omega, by simp; omega⟩
    rw [if_pos hin, if_pos this]
    have : t - j = (t - (j + 1)) + 1 := by omega
    rw [this]; simp
  · rw [if_neg hin]
    have := ht1 t
    by_cases htj : t = j
    · subst htj
      have hc : t ≤ t ∧ t - t < (x :: fs).length := ⟨le_rfl, by simp⟩
      rw [if_pos hc]
      simpa using this
    · have hc : ¬ (j ≤ t ∧ t - j < (x :: fs).length) := by
        intro ⟨h1', h2'⟩; simp at h2'; omega
      have hc1 : ¬ (j ≤ t ∧ t - j < ([x] : List ℕ).length) := by
        intro ⟨h1', h2'⟩; simp at h2'; omega
      rw [if_neg hc]
      rw [if_neg hc1] at this
      exact this

theorem loadFrom_spec (l : List Instr) : ∀ j : ℕ, (∀ i ∈ l, lits i < B) → j + l.length < B →
    Spec B (fun σ => j + l.length ≤ (σ.arrs "ip0").length ∧ j + l.length ≤ (σ.arrs "ip1").length ∧
        j + l.length ≤ (σ.arrs "ip2").length ∧ j + l.length ≤ (σ.arrs "ip3").length)
      (loadFrom j l) (fun σ σ' => Loaded j l σ σ') (20 * l.length + 1) := by
  induction l with
  | nil =>
    intro j _ _
    refine Spec.mono (Spec.post Spec.skip fun σ σ' _ h => ?_) (by simp)
    subst h
    exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl, ArrLoad.nil _ _, ArrLoad.nil _ _,
      ArrLoad.nil _ _, ArrLoad.nil _ _⟩
  | cons i rest ih =>
    intro j hl hjB
    have h1 := storeInstr_spec (B := B) j i (by simp at hjB; omega) (hl i (by simp))
    have h2 := ih (j + 1) (fun i' hi' => hl i' (by simp [hi'])) (by simp at hjB; omega)
    refine Spec.mono (Spec.seq (P' := fun σ => j + 1 + rest.length ≤ (σ.arrs "ip0").length ∧
        j + 1 + rest.length ≤ (σ.arrs "ip1").length ∧ j + 1 + rest.length ≤ (σ.arrs "ip2").length ∧
        j + 1 + rest.length ≤ (σ.arrs "ip3").length)
      (Spec.pre h1 fun σ h => by simp only [List.length_cons] at h; omega) h2 ?_ ?_) (by simp; omega)
    · intro σ σ1 hσ hL
      obtain ⟨-, -, -, -, ⟨l0, -⟩, ⟨l1, -⟩, ⟨l2, -⟩, ⟨l3, -⟩⟩ := hL
      simp only [List.length_cons] at hσ
      rw [l0, l1, l2, l3]
      omega
    · intro σ σ1 σ' hσ hL1 hL2
      obtain ⟨v1, i1, o1, a1, c01, c11, c21, c31⟩ := hL1
      obtain ⟨v2, i2, o2, a2, c02, c12, c22, c32⟩ := hL2
      refine ⟨v2.trans v1, i2.trans i1, o2.trans o1, fun a h0 h1 h2 h3 =>
        (a2 a h0 h1 h2 h3).trans (a1 a h0 h1 h2 h3), ?_, ?_, ?_, ?_⟩
      · exact ArrLoad.comp c01 c02
      · exact ArrLoad.comp c11 c12
      · exact ArrLoad.comp c21 c22
      · exact ArrLoad.comp c31 c32

end Lax117284Proofs.Machine.ClSim

end

/-! ### `Lax117284Proofs.Machine.ClSimFinal` -/

section
/-!
The interpreter, whole: load the program, set the constants, run the loop.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B wp v : ℕ} {P : Program} {z : List ℕ}

/-- Set the constants of the word length, from `wpv`, `Mp` and `zl`, and the state of the machine
at the start. -/
def simInit (P : Program) : Com := seqs [
  asg "plen" (lit P.length), asg "mk" (.sub (V "Mp") (lit 1)),
  asg "hh" (.shiftr (.add (V "wpv") (lit 1)) (lit 1)),
  asg "hm" (.sub (.shiftl (lit 1) (V "hh")) (lit 1)),
  asg "hm2" (.sub (.shiftl (lit 1) (.sub (V "wpv") (V "hh"))) (lit 1)),
  asg "spc" (lit 0), asg "rd" (lit 0), asg "nout" (lit 0), asg "outv" (lit 0)]

theorem simInit_spec (hB : Bnd B wp) (hpl : P.length < B) :
    Spec B (fun σ => σ.vars "wpv" = wp ∧ σ.vars "Mp" = 2 ^ wp) (simInit P)
      (fun σ σ' => σ'.vars "plen" = P.length ∧ σ'.vars "mk" = 2 ^ wp - 1 ∧
        σ'.vars "hh" = (wp + 1) / 2 ∧ σ'.vars "hm" = 2 ^ ((wp + 1) / 2) - 1 ∧
        σ'.vars "hm2" = 2 ^ (wp - (wp + 1) / 2) - 1 ∧ σ'.vars "spc" = 0 ∧ σ'.vars "rd" = 0 ∧
        σ'.vars "nout" = 0 ∧ σ'.vars "outv" = 0 ∧
        (∀ y, y ∉ ["plen", "mk", "hh", "hm", "hm2", "spc", "rd", "nout", "outv"] →
          σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) 100 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hwlt : wp < 2 ^ wp := Nat.lt_two_pow_self
  have hB' : 8 * 2 ^ wp + 32 < B := hB
  have h1 : 2 ^ ((wp + 1) / 2) ≤ 2 ^ wp := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (wp - (wp + 1) / 2) ≤ 2 ^ wp := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 := Nat.two_pow_pos ((wp + 1) / 2)
  have h4 := Nat.two_pow_pos (wp - (wp + 1) / 2)
  run_vcg
  all_goals
    obtain ⟨hwp, hMp⟩ : σ.vars "wpv" = wp ∧ σ.vars "Mp" = 2 ^ wp := ⟨‹_›, ‹_›⟩
  all_goals try simp [Env.setVar, hwp, hMp]
  all_goals try omega
  all_goals try
    (intro y h1 h2 h3 h4 h5 h6 h7 h8 h9
     simp [Env.setVar, h1, h2, h3, h4, h5, h6, h7, h8, h9])

/-- The interpreter with its program. -/
def simCom (P : Program) : Com := .seq (.seq (loadFrom 0 P) (simInit P)) interpLoop

/-- What the interpreter needs at the start. -/
def Pre0 (P : Program) (z : List ℕ) (wp : ℕ) (σ : Env) : Prop :=
  (σ.arrs "ip0").length = P.length ∧ (σ.arrs "ip1").length = P.length ∧
  (σ.arrs "ip2").length = P.length ∧ (σ.arrs "ip3").length = P.length ∧
  σ.arrs "om" = List.replicate (2 ^ wp) 0 ∧ σ.arrs "z" = z ∧ σ.vars "wpv" = wp ∧
  σ.vars "Mp" = 2 ^ wp ∧ σ.vars "zl" = z.length

/-- The scalars the interpreter may change. -/
def SV : List String := FV ++ ["plen", "mk", "hh", "hm", "hm2", "spc", "rd", "nout", "outv"]

/-- The arrays the interpreter may change. -/
def SA : List String := ["ip0", "ip1", "ip2", "ip3", "om"]

theorem progEnc_of_loaded {σ σ' : Env} (h : Pre0 P z wp σ) (hL : Loaded 0 P σ σ') : ProgEnc P σ' := by
  obtain ⟨l0, l1, l2, l3, -, -, -, -, -⟩ := h
  obtain ⟨-, -, -, -, ⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩ := hL
  refine ⟨by rw [a0, l0], by rw [a1, l1], by rw [a2, l2], by rw [a3, l3], ?_⟩
  intro j i hj
  have hjl : j < P.length := (List.getElem?_eq_some_iff.mp hj).1
  have hmap : ∀ f : Instr → ℕ, (P.map f).getD j 0 = f i := by
    intro f
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, hj]
  have hc : 0 ≤ j ∧ j - 0 < P.length := ⟨Nat.zero_le _, by omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [b0, if_pos (by simpa using hc)]; exact hmap _
  · rw [b1, if_pos (by simpa using hc)]; exact hmap _
  · rw [b2, if_pos (by simpa using hc)]; exact hmap _
  · rw [b3, if_pos (by simpa using hc)]; exact hmap _

theorem lits_lt (HS : HypS B wp P z) : ∀ i ∈ P, lits i < B := by
  intro i hi
  have h1 := HS.hLits i hi
  have h2 := code_fst_le i
  have h3 := HS.hB
  simp only [Bnd] at h3
  have h4 := Nat.two_pow_pos wp
  simp only [lits]
  omega

/-- The machine has not started: the relations at the beginning. -/
theorem init_rel {σ0 σ1 σ2 : Env} (h0 : Pre0 P z wp σ0) (hL : Loaded 0 P σ0 σ1)
    (hI : σ2.vars "plen" = P.length ∧ σ2.vars "mk" = 2 ^ wp - 1 ∧
        σ2.vars "hh" = (wp + 1) / 2 ∧ σ2.vars "hm" = 2 ^ ((wp + 1) / 2) - 1 ∧
        σ2.vars "hm2" = 2 ^ (wp - (wp + 1) / 2) - 1 ∧ σ2.vars "spc" = 0 ∧ σ2.vars "rd" = 0 ∧
        σ2.vars "nout" = 0 ∧ σ2.vars "outv" = 0 ∧
        (∀ y, y ∉ ["plen", "mk", "hh", "hm", "hm2", "spc", "rd", "nout", "outv"] →
          σ2.vars y = σ1.vars y) ∧ σ2.arrs = σ1.arrs ∧ σ2.inp = σ1.inp ∧ σ2.out = σ1.out) :
    KRel P z wp σ2 ∧ DRel z wp v σ2 (initState z) := by
  obtain ⟨hplen, hmk, hhh, hhm, hhm2, hspc, hrd, hnout, houtv, hfr, harr, hinp, hout⟩ := hI
  have hpe := progEnc_of_loaded h0 hL
  obtain ⟨hv1, hi1, ho1, ha1, -⟩ := hL
  obtain ⟨l0, l1, l2, l3, hom, hz, hwp, hMp, hzl⟩ := h0
  have hom1 : σ1.arrs "om" = σ0.arrs "om" := ha1 "om" (by decide) (by decide) (by decide) (by decide)
  have hz1 : σ1.arrs "z" = σ0.arrs "z" := ha1 "z" (by decide) (by decide) (by decide) (by decide)
  have hnm : ∀ y, y ∉ ["plen", "mk", "hh", "hm", "hm2", "spc", "rd", "nout", "outv"] →
      σ2.vars y = σ0.vars y := fun y hy => by rw [hfr y hy, hv1]
  refine ⟨⟨hplen, by rw [hnm "zl" (by decide)]; exact hzl, by rw [hnm "wpv" (by decide)]; exact hwp,
    by rw [hnm "Mp" (by decide)]; exact hMp, hmk, hhh, hhm, hhm2, by rw [harr, hz1]; exact hz,
    by simpa [ProgEnc, harr] using hpe⟩, ?_⟩
  refine ⟨by simp [hspc, initState], by rw [hrd]; exact Nat.zero_le _, by simp [hrd, initState],
    rfl, ?_, ?_, ?_, ?_⟩
  · rw [harr, hom1, hom]; simp
  · intro a ha
    rw [harr, hom1, hom]; simp [initState, List.getD_eq_getElem?_getD, List.getElem?_replicate, ha]
  · intro a; simp [initState, Nat.two_pow_pos]
  · left; exact ⟨rfl, hnout⟩

theorem loop_frame_ok : (∀ y ∈ interpLoop.wvars, y ∈ SV) ∧ (∀ a ∈ interpLoop.warrs, a ∈ SA) ∧
    ¬ interpLoop.reads ∧ interpLoop.NoWrite := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem loadInit_spec (HS : HypS B wp P z) :
    Spec B (Pre0 P z wp) (.seq (loadFrom 0 P) (simInit P))
      (fun σ σ2 => KRel P z wp σ2 ∧ DRel z wp v σ2 (initState z) ∧ σ2.vars "spc" < B ∧
        (∀ y, y ∉ SV → σ2.vars y = σ.vars y) ∧ (∀ a, a ∉ SA → σ2.arrs a = σ.arrs a) ∧
        σ2.inp = σ.inp ∧ σ2.out = σ.out) (20 * P.length + 1 + 100) := by
  have hload := loadFrom_spec (B := B) P 0 (lits_lt HS) (by simpa using HS.hpl)
  have hinit := simInit_spec (B := B) (P := P) HS.hB HS.hpl
  refine Spec.seq (P' := fun σ => σ.vars "wpv" = wp ∧ σ.vars "Mp" = 2 ^ wp)
    (Spec.pre hload (fun σ h => by
      obtain ⟨l0, l1, l2, l3, -⟩ := h
      exact ⟨by omega, by omega, by omega, by omega⟩)) hinit ?_ ?_
  · intro σ σ1 h0 hL
    obtain ⟨-, -, -, -, -, -, hwp, hMp, -⟩ := h0
    obtain ⟨hv1, -⟩ := hL
    exact ⟨by rw [hv1]; exact hwp, by rw [hv1]; exact hMp⟩
  · intro σ σ1 σ2 h0 hL hI
    have hrel := init_rel (v := v) h0 hL hI
    obtain ⟨hplen, hmk, hhh, hhm, hhm2, hspc, hrd, hnout, houtv, hfr, harr, hinp, hout⟩ := hI
    obtain ⟨hv1, hi1, ho1, ha1, -⟩ := hL
    refine ⟨hrel.1, hrel.2, by rw [hspc]; have := HS.hpl; omega, ?_, ?_, ?_, ?_⟩
    · intro y hy
      have : y ∉ ["plen", "mk", "hh", "hm", "hm2", "spc", "rd", "nout", "outv"] := fun h =>
        hy (by simp only [SV, List.mem_append]; exact Or.inr h)
      rw [hfr y this, hv1]
    · intro a ha
      have h0 : a ≠ "ip0" := fun e => ha (by simp [SA, e])
      have h1 : a ≠ "ip1" := fun e => ha (by simp [SA, e])
      have h2 : a ≠ "ip2" := fun e => ha (by simp [SA, e])
      have h3 : a ≠ "ip3" := fun e => ha (by simp [SA, e])
      rw [harr, ha1 a h0 h1 h2 h3]
    · rw [hinp, hi1]
    · rw [hout, ho1]

/-- **The interpreter runs a machine program that halts with the output `[v]`.** From the state in
which the program is not yet loaded, the memory is zero, the input is in `z`, the counter is set
to the word length `wp` and its power, the command reaches a state with `nout = 1`, `outv = v`, and
changes nothing but the scalars `SV` and the arrays `SA`. -/
theorem simCom_spec (HS : HypS B wp P z) (t : ℕ) (hrun : RunsTo wp P z [v] t) :
    Spec B (Pre0 P z wp) (simCom P)
      (fun σ σ' => σ'.vars "nout" = 1 ∧ σ'.vars "outv" = v ∧
        (∀ y, y ∉ SV → σ'.vars y = σ.vars y) ∧ (∀ a, a ∉ SA → σ'.arrs a = σ.arrs a) ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out) (20 * P.length + 101 + ((t + 1) * 604 + 4)) := by
  obtain ⟨k, sf, hk, hstep, hout, ht⟩ := hrun
  have hkt : k ≤ t := by rw [ht]; exact Nat.le_add_right _ _
  have hloop : Spec B (fun σ => KRel P z wp σ ∧ DRel z wp v σ (initState z) ∧ σ.vars "spc" < B)
      interpLoop (fun σ σ' => KRel P z wp σ' ∧ Fin' P z wp v σ' sf) ((k + 1) * 604 + 4) := by
    intro σ ⟨hK, hD, hsB⟩
    obtain ⟨σ', hr, hK', hF⟩ := loop_run HS sf hout hstep k (initState z) σ hK hD hsB hk
    exact ⟨σ', hr, hK', hF⟩
  obtain ⟨hv, ha, hr, hw⟩ := loop_frame_ok
  refine Spec.mono (Spec.seq (loadInit_spec (v := v) HS) (Spec.frame hloop)
    (fun σ σ2 _ h => ⟨h.1, h.2.1, h.2.2.1⟩) ?_) (by nlinarith)
  intro σ σ2 σ' h0 hQ hQ'
  obtain ⟨hK, hD, hsB, hf1, hf2, hf3, hf4⟩ := hQ
  obtain ⟨⟨hK', ⟨hDf, -⟩⟩, hf1', hf2', hf3', hf4'⟩ := hQ'
  refine ⟨?_, ?_, fun y hy => ?_, fun a ha' => ?_, ?_, ?_⟩
  · have := hDf.out
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · rw [hout] at h1; simp at h1
    · exact h2
  · have := hDf.out
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · rw [hout] at h1; simp at h1
    · exact h3
  · rw [hf1' y (fun h => hy (hv y h |> fun h' => h')), hf1 y hy]
  · rw [hf2' a (fun h => ha' (ha a h)), hf2 a ha']
  · rw [hf3' hr, hf3]
  · rw [hf4' hw, hf4]

end Lax117284Proofs.Machine.ClSim

end

/-! ### `Lax117284Proofs.Machine.ClBuildDefs` -/

section
/-!
The builder of the integer program's word, as an IMP+ command: the definitions.

The input word is in the array `X`. The builder computes the sizes `T = 2 ^ (n*n)`, `Z = 2 ^ n`,
`V = T * Z`, `N = V + n`, `M = T + n` and `zl = 2 + M * N + M`; the table `cnt` of the number of days
of each type; the table `okt` of which pairs (type, subset) are independent; and finally the array
`z`, one entry per position, by the formula of `zFunRaw`.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev dv (e f : Expr) : Expr := .bin .div e f
/-- The smaller of two values. -/
abbrev cap (e f : Expr) : Expr := sub e (sub e f)
/-- `1` when `e < f`, `0` otherwise. -/
abbrev ltFl (e f : Expr) : Expr := cap (sub f e) (lit 1)
/-- Bit `p` of `x`: `1` or `0`. -/
abbrev bitE (x p : Expr) : Expr := .bin .and (.bin .shiftr x p) (lit 1)
/-- The power `2 ^ p`. -/
abbrev pow2 (p : Expr) : Expr := .bin .shiftl (lit 1) p

/-- The sizes of the program, from the number of clients. -/
def sizesCom : Com := seqs [
  asg "nn" (mul (V "n") (V "n")),
  asg "T" (pow2 (V "nn")), asg "Z" (pow2 (V "n")), asg "Vv" (mul (V "T") (V "Z")),
  asg "N" (add (V "Vv") (V "n")), asg "M" (add (V "T") (V "n")),
  asg "zl" (add (add (lit 2) (mul (V "M") (V "N"))) (V "M"))]

/-- What the builder knows about the word and the bounds. -/
structure Bh (I : Instance) (x : List ℕ) (k B : ℕ) : Prop where
  enc : Lax117284.InstanceEncoding.EncodesUniform x I k
  hL : x.length < B
  hX : ∀ v ∈ x, v < B
  hzB : zLen I.clients < B

/-- The scalars and the input array. -/
structure Ctx0 (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop where
  X : σ.arrs "X" = x
  n : σ.vars "n" = I.clients
  m : σ.vars "m" = I.days
  k : σ.vars "k" = k

/-- The sizes are set. -/
structure Sizes (I : Instance) (σ : Env) : Prop where
  nn : σ.vars "nn" = I.clients * I.clients
  T : σ.vars "T" = nT I.clients
  Z : σ.vars "Z" = nZ I.clients
  Vv : σ.vars "Vv" = nV I.clients
  N : σ.vars "N" = nN I.clients
  M : σ.vars "M" = nM I.clients
  zl : σ.vars "zl" = zLen I.clients

variable {B k : ℕ} {I : Instance} {x : List ℕ}

open Lax117284Proofs.Machine.ClSim (AgreeOff) in
theorem AgreeOff.trans' {L1 L2 : List String} {σ σ1 σ2 : Env} (h1 : AgreeOff L1 σ σ1)
    (h2 : AgreeOff L2 σ1 σ2) : AgreeOff (L1 ++ L2) σ σ2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, fun y hy => by
    rw [h2.2.2.2 y (fun h => hy (List.mem_append_right _ h)),
      h1.2.2.2 y (fun h => hy (List.mem_append_left _ h))]⟩

open Lax117284Proofs.Machine.ClSim (AgreeOff) in
theorem AgreeOff.mono' {L L' : List String} {σ σ' : Env} (h : AgreeOff L σ σ')
    (hs : ∀ y ∈ L, y ∈ L') : AgreeOff L' σ σ' :=
  ⟨h.1, h.2.1, h.2.2.1, fun y hy => h.2.2.2 y (fun hh => hy (hs y hh))⟩

theorem Bh.n_lt (h : Bh I x k B) : I.clients < B := by
  have := ClientsWord.x0 h.enc
  rw [← this]
  by_cases hj : 0 < x.length
  · rw [List.getD_eq_getElem _ _ hj]; exact h.hX _ (List.getElem_mem hj)
  · have := ClientsWord.len_eq h.enc; omega

theorem Bh.m_lt (h : Bh I x k B) : I.days < B := by
  have := ClientsWord.x1 h.enc
  rw [← this]
  have hl := ClientsWord.len_eq h.enc
  rw [List.getD_eq_getElem _ _ (by omega)]; exact h.hX _ (List.getElem_mem _)

theorem Bh.k_lt (h : Bh I x k B) : k < B := by
  have := ClientsWord.xk h.enc
  rw [← this]
  have hl := ClientsWord.len_eq h.enc
  rw [List.getD_eq_getElem _ _ (by omega)]; exact h.hX _ (List.getElem_mem _)

theorem Bh.getD_lt (h : Bh I x k B) (j : ℕ) : x.getD j 0 < B := by
  by_cases hj : j < x.length
  · rw [List.getD_eq_getElem _ _ hj]; exact h.hX _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]; have := h.hL; omega

theorem Bh.mn_le (h : Bh I x k B) : 2 * (I.days * I.clients) + 3 = x.length := by
  have := ClientsWord.len_eq h.enc; omega

/-- `σ'` differs from `σ` only in the scalars `LV` and the arrays `LA`. -/
def AgreeA (LV LA : List String) (σ σ' : Env) : Prop :=
  (∀ a, a ∉ LA → σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
    ∀ y, y ∉ LV → σ'.vars y = σ.vars y

theorem AgreeA.trans {LV LV' LA LA' : List String} {σ σ1 σ2 : Env} (h1 : AgreeA LV LA σ σ1)
    (h2 : AgreeA LV' LA' σ1 σ2) : AgreeA (LV ++ LV') (LA ++ LA') σ σ2 :=
  ⟨fun a ha => by
    rw [h2.1 a (fun h => ha (List.mem_append_right _ h)), h1.1 a (fun h => ha (List.mem_append_left _ h))],
    h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, fun y hy => by
    rw [h2.2.2.2 y (fun h => hy (List.mem_append_right _ h)),
      h1.2.2.2 y (fun h => hy (List.mem_append_left _ h))]⟩

theorem AgreeA.mono {LV LV' LA LA' : List String} {σ σ' : Env} (h : AgreeA LV LA σ σ')
    (hv : ∀ y ∈ LV, y ∈ LV') (ha : ∀ a ∈ LA, a ∈ LA') : AgreeA LV' LA' σ σ' :=
  ⟨fun a hh => h.1 a (fun h' => hh (ha a h')), h.2.1, h.2.2.1,
    fun y hy => h.2.2.2 y (fun h' => hy (hv y h'))⟩

theorem AgreeOff.toA {L : List String} {σ σ' : Env} (h : AgreeOff L σ σ') :
    AgreeA L [] σ σ' := ⟨fun a _ => by rw [h.1], h.2.1, h.2.2.1, h.2.2.2⟩

theorem agreeA_of_frame {c : Com} {LV LA : List String} (hv : ∀ y ∈ c.wvars, y ∈ LV)
    (ha : ∀ a ∈ c.warrs, a ∈ LA) (hr : ¬ c.reads) (hw : c.NoWrite) {σ σ' : Env}
    (h1 : ∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y) (h2 : ∀ a, a ∉ c.warrs → σ'.arrs a = σ.arrs a)
    (h3 : ¬ c.reads → σ'.inp = σ.inp) (h4 : c.NoWrite → σ'.out = σ.out) : AgreeA LV LA σ σ' :=
  ⟨fun a hh => h2 a (fun h' => hh (ha a h')), h3 hr, h4 hw, fun y hy => h1 y (fun hc => hy (hv y hc))⟩

theorem agree_of_frame_gen {c : Com} {L : List String} (hv : ∀ y ∈ c.wvars, y ∈ L)
    (ha : ∀ a ∈ c.warrs, False) (hr : ¬ c.reads) (hw : c.NoWrite) {σ σ' : Env}
    (h1 : ∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y) (h2 : ∀ a, a ∉ c.warrs → σ'.arrs a = σ.arrs a)
    (h3 : ¬ c.reads → σ'.inp = σ.inp) (h4 : c.NoWrite → σ'.out = σ.out) : AgreeOff L σ σ' :=
  ⟨funext fun a => h2 a (fun hh => ha a hh), h3 hr, h4 hw, fun y hy => h1 y (fun hc => hy (hv y hc))⟩

theorem Bh.dAt_lt (h : Bh I x k B) {i a : ℕ} (hi : i < I.days) (ha : a < I.clients) :
    I.dAt i a < B := by
  rw [← ClientsWord.due_eq h.enc hi ha]; exact h.getD_lt _

theorem Bh.pAt_lt (h : Bh I x k B) {i a : ℕ} (hi : i < I.days) (ha : a < I.clients) :
    I.pAt i a < B := by
  rw [← ClientsWord.proc_eq h.enc hi ha]; exact h.getD_lt _

theorem Bh.nn_lt (h : Bh I x k B) : I.clients * I.clients < B := by
  have := (sizes_le_zLen I.clients).2.2.2.2.2.1
  have := (sizes_le_zLen I.clients).1
  have := h.hzB
  have := h.hL
  omega

theorem Bh.nT_lt (h : Bh I x k B) : nT I.clients < B := by
  have := (sizes_le_zLen I.clients).1
  have := h.hzB
  have := h.hL
  omega

theorem sizesCom_spec (h : Bh I x k B) :
    Spec B (Ctx0 I x k) sizesCom (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧
      (∀ y, y ∉ ["nn", "T", "Z", "Vv", "N", "M", "zl"] → σ'.vars y = σ.vars y) ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) 100 := by
  have hz := h.hzB
  have hL := h.hL
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hT : (2 : ℕ) ^ (I.clients * I.clients) = nT I.clients := rfl
  have hZ : (2 : ℕ) ^ I.clients = nZ I.clients := rfl
  have hV : nT I.clients * nZ I.clients = nV I.clients := rfl
  have hN : nV I.clients + I.clients = nN I.clients := rfl
  have hM : nT I.clients + I.clients = nM I.clients := rfl
  have hzl' : 2 + nM I.clients * nN I.clients + nM I.clients = zLen I.clients := rfl
  run_vcg
  all_goals
    obtain ⟨hX, hn, hm, hk⟩ := ‹Ctx0 I x k _›
  all_goals try
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals try simp [Env.setVar, hX, hn, hm, hk, hT, hZ, hV, hN, hM, hzl']
  all_goals try (intro y a1 a2 a3 a4 a5 a6 a7
                 simp [Env.setVar, a1, a2, a3, a4, a5, a6, a7])
  all_goals try omega

end Lax117284Proofs.Machine.ClBuild

end

/-! ### `Lax117284Proofs.Machine.ClBuildType` -/

section
/-!
The type number of one day, and the table of how many days have each type.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The index of the processing time of client `a` on day `ci`. -/
abbrev procIdx (a : String) : Expr := add (add (lit 2) (mul (V "ci") (V "n"))) (V a)
/-- The index of the due date of client `a` on day `ci`. -/
abbrev dueIdx (a : String) : Expr :=
  add (add (add (lit 2) (mul (V "m") (V "n"))) (mul (V "ci") (V "n"))) (V a)

/-- The client indices of position `q`. -/
def phaseA : Com := seqs [asg "qa" (dv (V "q") (V "n")), asg "qb" (sub (V "q") (mul (V "qa") (V "n")))]

/-- The processing times and due dates of the two clients. -/
def phaseB : Com := seqs [
  asg "da" (.get "X" (dueIdx "qa")), asg "pa" (.get "X" (procIdx "qa")),
  asg "db" (.get "X" (dueIdx "qb")), asg "pb" (.get "X" (procIdx "qb"))]

/-- Whether they conflict, and the bit added. -/
def phaseC : Com := seqs [
  asg "fl" (mul (ltFl (sub (V "da") (V "pa")) (V "db")) (ltFl (sub (V "db") (V "pb")) (V "da"))),
  asg "tt" (add (V "tt") (mul (V "fl") (pow2 (V "q")))),
  asg "q" (add (V "q") (lit 1))]

/-- One position `q = a * n + b` of the type of day `ci`: add its bit. -/
def typeBody : Com := .seq phaseA (.seq phaseB phaseC)

/-- The number of the type of day `ci`, in `tt`. -/
def typeLoop : Com := seqs [asg "tt" (lit 0), asg "q" (lit 0), .while (.lt (V "q") (V "nn")) typeBody]

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The bit function of day `i`'s type. -/
def fconf (I : Instance) (i : ℕ) : ℕ → Bool :=
  fun q => confB I i (q / I.clients) (q % I.clients)

/-- The invariant of the type loop. -/
def TInv (I : Instance) (x : List ℕ) (k i : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ci" = i ∧ σ.vars "q" ≤ I.clients * I.clients ∧
    σ.vars "tt" = bitsNum (fconf I i) (σ.vars "q")

theorem flag_lt (e f : ℕ) : min (f - e) 1 = if e < f then 1 else 0 := by
  split_ifs with h <;> omega

open Lax117284Proofs.Machine.ClSim (AgreeOff)

theorem Ctx0.agree {L : List String} {σ σ' : Env} (h : Ctx0 I x k σ) (hA : AgreeOff L σ σ')
    (h1 : "n" ∉ L) (h2 : "m" ∉ L) (h3 : "k" ∉ L) : Ctx0 I x k σ' :=
  ⟨by rw [hA.1]; exact h.X, by rw [hA.2.2.2 _ h1]; exact h.n, by rw [hA.2.2.2 _ h2]; exact h.m,
    by rw [hA.2.2.2 _ h3]; exact h.k⟩

theorem Sizes.agree {L : List String} {σ σ' : Env} (h : Sizes I σ) (hA : AgreeOff L σ σ')
    (h1 : "nn" ∉ L) (h2 : "T" ∉ L) (h3 : "Z" ∉ L) (h4 : "Vv" ∉ L) (h5 : "N" ∉ L) (h6 : "M" ∉ L)
    (h7 : "zl" ∉ L) : Sizes I σ' :=
  ⟨by rw [hA.2.2.2 _ h1]; exact h.nn, by rw [hA.2.2.2 _ h2]; exact h.T,
    by rw [hA.2.2.2 _ h3]; exact h.Z, by rw [hA.2.2.2 _ h4]; exact h.Vv,
    by rw [hA.2.2.2 _ h5]; exact h.N, by rw [hA.2.2.2 _ h6]; exact h.M,
    by rw [hA.2.2.2 _ h7]; exact h.zl⟩

theorem phaseA_spec (h : Bh I x k B) (hn : 0 < I.clients) :
    Spec B (fun σ => Ctx0 I x k σ ∧ σ.vars "q" < I.clients * I.clients ∧ σ.vars "q" < B) phaseA
      (fun σ σ' => AgreeOff ["qa", "qb"] σ σ' ∧ σ'.vars "qa" = σ.vars "q" / I.clients ∧
        σ'.vars "qb" = σ.vars "q" % I.clients) 50 := by
  have hL := h.hL
  have hnB : I.clients < B := by
    have := h.hzB; have := n_le_nZ I.clients; have := (sizes_le_zLen I.clients).2.2.2.2.2.2.1
    have := zLen_le I.clients; have := (sizes_le_zLen I.clients).2.1
    omega
  run_vcg
  all_goals
    obtain ⟨hX, hnv, hm, hk⟩ := ‹Ctx0 I x k _›
  all_goals try
    refine ⟨⟨rfl, rfl, rfl, fun y hy => ?_⟩, ?_, ?_⟩
  all_goals try
    (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
     simp [Env.setVar, hy.1, hy.2])
  all_goals try simp [Env.setVar, hnv]
  all_goals try (rw [Nat.mod_def]; simp [Nat.mul_comm])
  all_goals try omega
  all_goals first
    | (exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
    | (exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) (by omega))

/-- The times of the two clients. -/
theorem phaseB_spec (h : Bh I x k B) (i : ℕ) (hi : i < I.days) :
    Spec B (fun σ => Ctx0 I x k σ ∧ σ.vars "ci" = i ∧ σ.vars "qa" < I.clients ∧
        σ.vars "qb" < I.clients) phaseB
      (fun σ σ' => AgreeOff ["da", "pa", "db", "pb"] σ σ' ∧ σ'.vars "da" = I.dAt i (σ.vars "qa") ∧
        σ'.vars "pa" = I.pAt i (σ.vars "qa") ∧ σ'.vars "db" = I.dAt i (σ.vars "qb") ∧
        σ'.vars "pb" = I.pAt i (σ.vars "qb")) 100 := by
  have hlen := ClientsWord.len_eq h.enc
  have hin : i * I.clients + I.clients ≤ I.days * I.clients := by
    have := Nat.mul_le_mul_right I.clients (Nat.succ_le_of_lt hi); nlinarith
  have hproc : ∀ a, a < I.clients → x.getD (2 + i * I.clients + a) 0 = I.pAt i a :=
    fun a ha => ClientsWord.proc_eq h.enc hi ha
  have hdue : ∀ a, a < I.clients → x.getD (2 + I.days * I.clients + i * I.clients + a) 0 = I.dAt i a :=
    fun a ha => ClientsWord.due_eq h.enc hi ha
  have hgB : ∀ j, x.getD j 0 < B := by
    intro j
    by_cases hj : j < x.length
    · rw [List.getD_eq_getElem _ _ hj]; exact h.hX _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (by omega)]; have := h.hL; omega
  have hL := h.hL
  have hmB := h.m_lt
  have hnB := h.n_lt
  have hlen' := h.mn_le
  have hproc' : ∀ a, a < I.clients → x[2 + i * I.clients + a]?.getD 0 = I.pAt i a := fun a ha => by
    simpa [List.getD_eq_getElem?_getD] using hproc a ha
  have hdue' : ∀ a, a < I.clients → x[2 + I.days * I.clients + i * I.clients + a]?.getD 0 =
      I.dAt i a := fun a ha => by simpa [List.getD_eq_getElem?_getD] using hdue a ha
  have hgB' : ∀ j, (x[j]?.getD 0) < B := fun j => by
    simpa [List.getD_eq_getElem?_getD] using hgB j
  have hdB : ∀ a, a < I.clients → I.dAt i a < B := fun a ha => by
    rw [← hdue' a ha]; exact hgB' _
  have hpB : ∀ a, a < I.clients → I.pAt i a < B := fun a ha => by
    rw [← hproc' a ha]; exact hgB' _
  run_vcg
  all_goals
    obtain ⟨hX, hnv, hm, hk⟩ := ‹Ctx0 I x k _›
    have hci : σ.vars "ci" = i := ‹_›
    have hqa : σ.vars "qa" < I.clients := ‹_›
    have hqb : σ.vars "qb" < I.clients := ‹_›
  all_goals try
    refine ⟨⟨rfl, rfl, rfl, fun y hy => ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals try
    (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
     simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2])
  all_goals try simp [Env.setVar, hX, hnv, hm, hci, hproc', hdue', hgB', hgB, hqa, hqb, hdB, hpB]
  all_goals try omega

theorem cap_one (a : ℕ) : a - (a - 1) = min a 1 := by omega

theorem conf_flag (da pa db pb : ℕ) :
    min (db - (da - pa)) 1 * min (da - (db - pb)) 1 =
      if da - pa < db ∧ db - pb < da then 1 else 0 := by
  rw [flag_lt, flag_lt]
  split_ifs <;> simp_all

theorem bitsNum_succ_conf (I : Instance) (i q : ℕ) :
    bitsNum (fconf I i) (q + 1) =
      bitsNum (fconf I i) q + if I.ConflictAt i (q / I.clients) (q % I.clients) then 2 ^ q else 0 := by
  simp only [bitsNum, fconf, confB, decide_eq_true_eq]

theorem pow_lt_nT {q n : ℕ} (hq : q < n * n) : 2 ^ q < nT n := by
  rw [nT]; exact Nat.pow_lt_pow_right (by norm_num) hq

theorem bitsNum_step_lt (f : ℕ → Bool) {q n : ℕ} (hq : q < n * n) (b : ℕ) (hb : b ≤ 1) :
    bitsNum f q + b * 2 ^ q < nT n := by
  have h1 := bitsNum_lt f q
  have h2 : 2 ^ (q + 1) ≤ nT n := by
    rw [nT]; exact Nat.pow_le_pow_right (by norm_num) hq
  rw [pow_succ] at h2
  have : b * 2 ^ q ≤ 2 ^ q := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> simp
  omega

/-- The precondition of the last phase. -/
def PC (I : Instance) (x : List ℕ) (k i B : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "q" < I.clients * I.clients ∧
    σ.vars "tt" = bitsNum (fconf I i) (σ.vars "q") ∧
    σ.vars "da" = I.dAt i (σ.vars "q" / I.clients) ∧
    σ.vars "pa" = I.pAt i (σ.vars "q" / I.clients) ∧
    σ.vars "db" = I.dAt i (σ.vars "q" % I.clients) ∧
    σ.vars "pb" = I.pAt i (σ.vars "q" % I.clients) ∧
    σ.vars "da" < B ∧ σ.vars "pa" < B ∧ σ.vars "db" < B ∧ σ.vars "pb" < B

set_option maxHeartbeats 1600000 in
theorem phaseC_spec (h : Bh I x k B) (i : ℕ) :
    Spec B (PC I x k i B) phaseC
      (fun σ σ' => AgreeOff ["fl", "tt", "q"] σ σ' ∧ σ'.vars "q" = σ.vars "q" + 1 ∧
        σ'.vars "tt" = bitsNum (fconf I i) (σ.vars "q" + 1)) 50 := by
  have hL := h.hL
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hgB := h.getD_lt
  unfold PC
  run_vcg
  all_goals
    obtain ⟨hX, hnv, hm, hk⟩ := ‹Ctx0 I x k _›
    obtain ⟨hnn, hT, hZ, hVv, hN, hM, hzl⟩ := ‹Sizes I _›
  all_goals
    have hq : σ.vars "q" < I.clients * I.clients := ‹_›
    have htt : σ.vars "tt" = bitsNum (fconf I i) (σ.vars "q") := ‹_›
    have hda : σ.vars "da" = I.dAt i (σ.vars "q" / I.clients) := ‹_›
    have hpa : σ.vars "pa" = I.pAt i (σ.vars "q" / I.clients) := ‹_›
    have hdb : σ.vars "db" = I.dAt i (σ.vars "q" % I.clients) := ‹_›
    have hpb : σ.vars "pb" = I.pAt i (σ.vars "q" % I.clients) := ‹_›
    have hdaB : σ.vars "da" < B := ‹_›
    have hpaB : σ.vars "pa" < B := ‹_›
    have hdbB : σ.vars "db" < B := ‹_›
    have hpbB : σ.vars "pb" < B := ‹_›
    have hbn : bitsNum (fconf I i) (σ.vars "q") < 2 ^ σ.vars "q" := bitsNum_lt _ _
    have hTq := pow_lt_nT hq
    have hstep := bitsNum_step_lt (fconf I i) hq
    have hs1 := hstep 1 (le_refl 1)
    have hs0 := hstep 0 (Nat.zero_le _)
    have hnT : nT I.clients < B := lt_of_le_of_lt h1 hz
  all_goals try
    refine ⟨⟨rfl, rfl, rfl, fun y hy => ?_⟩, ?_, ?_⟩
  all_goals try
    (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
     simp [Env.setVar, hy.1, hy.2.1, hy.2.2])
  all_goals try simp [Env.setVar, hnv, htt, hda, hpa, hdb, hpb, cap_one, conf_flag, bitsNum_succ_conf,
    Instance.ConflictAt]
  all_goals try (split_ifs <;> first | omega | simp_all)
  all_goals try omega
  all_goals try (exact lt_of_le_of_lt (Nat.sub_le _ _) (by omega))

end Lax117284Proofs.Machine.ClBuild

end

/-! ### `Lax117284Proofs.Machine.ClBuildCnt` -/

section
/-!
The type number of a day as a loop over the positions, and the table of counts as a loop over the
days.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The state between the phases of the type loop's body. -/
def Mid (I : Instance) (x : List ℕ) (k i : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ci" = i ∧ σ.vars "q" < I.clients * I.clients ∧
    σ.vars "tt" = bitsNum (fconf I i) (σ.vars "q") ∧ σ.vars "qa" = σ.vars "q" / I.clients ∧
    σ.vars "qb" = σ.vars "q" % I.clients ∧ σ.vars "qa" < I.clients ∧ σ.vars "qb" < I.clients

theorem typeBody_spec' (h : Bh I x k B) (i : ℕ) (hi : i < I.days) :
    Spec B (fun σ => TInv I x k i σ ∧ σ.vars "q" < I.clients * I.clients) typeBody
      (fun σ σ' => TInv I x k i σ' ∧ σ'.vars "q" = σ.vars "q" + 1) 200 := by
  have hnB := h.n_lt
  have hnnB := h.nn_lt
  rcases Nat.eq_zero_or_pos I.clients with h0 | hn
  · intro σ ⟨_, hq⟩
    rw [h0] at hq; simp at hq
  unfold typeBody
  have hA := Spec.pre (phaseA_spec h hn) (fun σ (hσ : TInv I x k i σ ∧ _) =>
    (⟨hσ.1.1, hσ.2, lt_trans hσ.2 hnnB⟩ : Ctx0 I x k σ ∧ _ ∧ _))
  have hB := phaseB_spec h i hi
  have hC := phaseC_spec h i
  have hBC : Spec B (Mid I x k i) (.seq phaseB phaseC)
      (fun σ σ' => TInv I x k i σ' ∧ σ'.vars "q" = σ.vars "q" + 1) (100 + 50) := by
    refine Spec.seq (P' := PC I x k i B) (Spec.pre hB (fun σ (hσ : Mid I x k i σ) =>
      ⟨hσ.1, hσ.2.2.1, hσ.2.2.2.2.2.2.2.1, hσ.2.2.2.2.2.2.2.2⟩)) hC ?_ ?_
    · rintro σ σ1 ⟨hC0, hS, hci, hq, htt, hqa, hqb, hqa', hqb'⟩ ⟨hA, hda, hpa, hdb, hpb⟩
      have hq1 : σ1.vars "q" = σ.vars "q" := hA.2.2.2 "q" (by decide)
      have hqa1 : σ1.vars "qa" = σ.vars "qa" := hA.2.2.2 "qa" (by decide)
      have hqb1 : σ1.vars "qb" = σ.vars "qb" := hA.2.2.2 "qb" (by decide)
      have htt1 : σ1.vars "tt" = σ.vars "tt" := hA.2.2.2 "tt" (by decide)
      refine ⟨hC0.agree hA (by decide) (by decide) (by decide), hS.agree hA (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hq1]; exact hq
      · rw [htt1, hq1]; exact htt
      · rw [hda, hqa, hq1]
      · rw [hpa, hqa, hq1]
      · rw [hdb, hqb, hq1]
      · rw [hpb, hqb, hq1]
      · rw [hda]; exact h.dAt_lt hi hqa'
      · rw [hpa]; exact h.pAt_lt hi hqa'
      · rw [hdb]; exact h.dAt_lt hi hqb'
      · rw [hpb]; exact h.pAt_lt hi hqb'
    · rintro σ σ1 σ2 ⟨hC0, hS, hci, hq, htt, hqa, hqb, hqa', hqb'⟩ ⟨hA, -⟩ ⟨hA2, hq2, htt2⟩
      have hq1 : σ1.vars "q" = σ.vars "q" := hA.2.2.2 "q" (by decide)
      have hci1 : σ1.vars "ci" = σ.vars "ci" := hA.2.2.2 "ci" (by decide)
      have hci2 : σ2.vars "ci" = σ1.vars "ci" := hA2.2.2.2 "ci" (by decide)
      have hσ1C := hC0.agree hA (by decide) (by decide) (by decide)
      have hσ1S := hS.agree hA (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)
      refine ⟨⟨hσ1C.agree hA2 (by decide) (by decide) (by decide),
        hσ1S.agree hA2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), by rw [hci2, hci1]; exact hci, ?_, ?_⟩, ?_⟩
      · omega
      · rw [htt2, ← hq2]
      · rw [hq2, hq1]
  refine Spec.mono (Spec.seq (P' := Mid I x k i) hA hBC ?_ ?_) (by omega)
  · rintro σ σ1 ⟨⟨hC0, hS, hci, hq0, htt⟩, hq⟩ ⟨hAg, hqa, hqb⟩
    have hq1 : σ1.vars "q" = σ.vars "q" := hAg.2.2.2 "q" (by decide)
    refine ⟨hC0.agree hAg (by decide) (by decide) (by decide),
      hS.agree hAg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), by rw [hAg.2.2.2 "ci" (by decide)]; exact hci, by rw [hq1]; exact hq,
      by rw [hAg.2.2.2 "tt" (by decide), hq1]; exact htt, by rw [hqa, hq1],
      by rw [hqb, hq1], ?_, ?_⟩
    · rw [hqa]; exact Nat.div_lt_of_lt_mul hq
    · rw [hqb]; exact Nat.mod_lt _ hn
  · rintro σ σ1 σ2 _ ⟨hAg, -⟩ ⟨hT, hq2⟩
    refine ⟨hT, ?_⟩
    rw [hq2, hAg.2.2.2 "q" (by decide)]

/-- The scalars the type loop may change. -/
def TL : List String := ["tt", "q", "qa", "qb", "da", "pa", "db", "pb", "fl"]

theorem typeLoop_frame : ∀ (c : Com), c = (Com.seq (.assign "q" (.lit 0))
      (.while (.lt (.var "q") (.var "nn")) typeBody)) →
    (∀ y ∈ c.wvars, y ∈ TL) ∧ (∀ a ∈ c.warrs, False) ∧ ¬ c.reads ∧ c.NoWrite := by
  intro c hc
  subst hc
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro a ha
  have : (Com.seq (.assign "q" (.lit 0)) (.while (.lt (.var "q") (.var "nn")) typeBody)).warrs = [] := by
    decide
  rw [this] at ha; simp at ha

theorem typeLoop_spec (h : Bh I x k B) (i : ℕ) (hi : i < I.days) :
    Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ci" = i) typeLoop
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧ σ'.vars "ci" = i ∧
        σ'.vars "tt" = typeNum I i ∧ AgreeOff TL σ σ') (((200 + 4) * (I.clients * I.clients) + 6) + 2) := by
  have hnnB := h.nn_lt
  have hloop := Spec.forRangeZero (B := B) (c := typeBody) "q" "nn" (TInv I x k i)
    (I.clients * I.clients) 200 hnnB (fun σ hσ => hσ.2.2.2.1) (fun σ hσ => hσ.2.1.nn)
    (typeBody_spec' h i hi)
  have hasg : Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ci" = i) (asg "tt" (lit 0))
      (fun σ σ' => σ' = σ.setVar "tt" 0) (1 + 1) := by
    have := Spec.assign (B := B) (P := fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ci" = i)
      (x := "tt") (e := lit 0) (f := fun _ => 0) (fun σ _ => evalB_lit (by omega))
    simpa using this
  have hfr := Spec.frame hloop
  unfold typeLoop
  refine Spec.mono (Spec.seq (P' := fun σ => TInv I x k i (σ.setVar "q" 0)) hasg hfr ?_ ?_)
    (by simp [Expr.size]; omega)
  · rintro σ σ1 ⟨hC, hS, hci⟩ rfl
    have hnn : σ.vars "nn" = I.clients * I.clients := hS.nn
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals simp [Env.setVar, hC.X, hC.n, hC.m, hC.k, hS.nn, hS.T, hS.Z, hS.Vv, hS.N, hS.M, hS.zl,
      hci, bitsNum]
  · rintro σ σ1 σ2 ⟨hC, hS, hci⟩ rfl ⟨⟨hT, hq⟩, hf1, hf2, hf3, hf4⟩
    obtain ⟨hv, ha, hr, hw⟩ := typeLoop_frame _ rfl
    have hA1 : AgreeOff ["tt"] σ (σ.setVar "tt" 0) :=
      ⟨rfl, rfl, rfl, fun y hy => by simp at hy; simp [Env.setVar, hy]⟩
    have hA2 := agree_of_frame_gen hv ha hr hw hf1 hf2 hf3 hf4
    refine ⟨hT.1, hT.2.1, hT.2.2.1, ?_, AgreeOff.mono' (AgreeOff.trans' hA1 hA2) ?_⟩
    · have := hT.2.2.2.2
      rw [this, hq]; rfl
    · intro y hy
      simp only [TL, List.mem_append, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      tauto

end Lax117284Proofs.Machine.ClBuild

end

/-! ### `Lax117284Proofs.Machine.ClBuildTab` -/

section
/-!
The table of counts: for every day, the number of its type is computed and the entry of the table
is incremented.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- One day: its type number, then the increment of the entry. -/
def dayBody : Com := seqs [typeLoop, .store "cnt" (V "tt") (add (.get "cnt" (V "tt")) (lit 1)),
  asg "ci" (add (V "ci") (lit 1))]

/-- The table of counts of the days below `ci`. -/
def cntCom : Com := seqs [asg "ci" (lit 0), .while (.lt (V "ci") (V "m")) dayBody]

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The invariant of the loop over the days. -/
def CInv (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ci" ≤ I.days ∧ (σ.arrs "cnt").length = nT I.clients ∧
    ∀ t < nT I.clients, (σ.arrs "cnt").getD t 0 =
      ((range (σ.vars "ci")).filter fun i' => typeNum I i' = t).card

/-- The store and the increment. -/
def bumpCom : Com := seqs [.store "cnt" (V "tt") (add (.get "cnt" (V "tt")) (lit 1)),
  asg "ci" (add (V "ci") (lit 1))]

theorem bump_spec :
    Spec B (fun σ => σ.vars "tt" < (σ.arrs "cnt").length ∧ (σ.arrs "cnt").getD (σ.vars "tt") 0 + 1 < B ∧
        σ.vars "ci" + 1 < B ∧ σ.vars "tt" < B) bumpCom
      (fun σ σ' => σ' = (σ.setArr "cnt" (σ.vars "tt") ((σ.arrs "cnt").getD (σ.vars "tt") 0 + 1)).setVar
        "ci" (σ.vars "ci" + 1)) 20 := by
  run_vcg
  all_goals try rfl

theorem dayBody_eq : dayBody = .seq typeLoop bumpCom := rfl

theorem typeAll_spec (h : Bh I x k B) :
    Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ci" < I.days) typeLoop
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧ σ'.vars "ci" = σ.vars "ci" ∧
        σ'.vars "tt" = typeNum I (σ.vars "ci") ∧ AgreeOff TL σ σ')
      (((200 + 4) * (I.clients * I.clients) + 6) + 2) := by
  intro σ ⟨hC, hS, hci⟩
  obtain ⟨σ', hr, hq⟩ := typeLoop_spec h (σ.vars "ci") hci σ ⟨hC, hS, rfl⟩
  exact ⟨σ', hr, hq.1, hq.2.1, by rw [hq.2.2.1], hq.2.2.2.1, hq.2.2.2.2⟩

theorem card_filter_succ (f : ℕ → ℕ) (t i : ℕ) :
    ((range (i + 1)).filter fun i' => f i' = t).card =
      ((range i).filter fun i' => f i' = t).card + if f i = t then 1 else 0 := by
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : f i = t
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp), if_pos h]
  · rw [if_neg h, if_neg h]; simp

theorem getD_set_ite (l : List ℕ) (i v t : ℕ) (hi : i < l.length) :
    (l.set i v).getD t 0 = if t = i then v else l.getD t 0 := by
  by_cases h : t = i
  · subst h; simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hi]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h), h]

theorem dayBody_spec (h : Bh I x k B) :
    Spec B (fun σ => CInv I x k σ ∧ σ.vars "ci" < I.days) dayBody
      (fun σ σ' => CInv I x k σ' ∧ σ'.vars "ci" = σ.vars "ci" + 1)
      (204 * (I.clients * I.clients) + 40) := by
  have hmB := h.m_lt
  have hnnB := h.nn_lt
  have hnT := h.nT_lt
  rw [dayBody_eq]
  have hT := Spec.pre (typeAll_spec h) (fun σ (hσ : CInv I x k σ ∧ σ.vars "ci" < I.days) =>
    (⟨hσ.1.1, hσ.1.2.1, hσ.2⟩ : Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ci" < I.days))
  refine Spec.mono (Spec.seq (P' := fun σ => σ.vars "tt" < (σ.arrs "cnt").length ∧
      (σ.arrs "cnt").getD (σ.vars "tt") 0 + 1 < B ∧ σ.vars "ci" + 1 < B ∧ σ.vars "tt" < B)
    hT bump_spec ?_ ?_) (by omega)
  · rintro σ σ1 ⟨hCI, hlt⟩ ⟨hC1, hS1, hci1, htt1, hA⟩
    obtain ⟨hC, hS, hcile, hlen, hcnt⟩ := hCI
    have harr : σ1.arrs "cnt" = σ.arrs "cnt" := by rw [hA.1]
    have hty := typeNum_lt I (σ.vars "ci")
    have hcardle : ((range (σ.vars "ci")).filter fun i' => typeNum I i' = typeNum I (σ.vars "ci")).card
        ≤ σ.vars "ci" := by
      refine le_trans (Finset.card_filter_le _ _) (by simp)
    refine ⟨by rw [htt1, harr, hlen]; exact hty, ?_, by omega, by rw [htt1]; omega⟩
    rw [htt1, harr, hcnt _ hty]
    omega
  · rintro σ σ1 σ2 ⟨hCI, hlt⟩ ⟨hC1, hS1, hci1, htt1, hA⟩ hσ2
    obtain ⟨hC, hS, hcile, hlen, hcnt⟩ := hCI
    have harr : σ1.arrs "cnt" = σ.arrs "cnt" := by rw [hA.1]
    have hci1' : σ1.vars "ci" = σ.vars "ci" := hci1
    have hty := typeNum_lt I (σ.vars "ci")
    subst hσ2
    have hlen1 : σ1.vars "tt" < (σ1.arrs "cnt").length := by rw [htt1, harr, hlen]; exact hty
    have hlen1' : ((σ1.arrs "cnt").set (σ1.vars "tt") ((σ1.arrs "cnt").getD (σ1.vars "tt") 0 + 1)).length = (σ.arrs "cnt").length := by
      rw [List.length_set, harr]
    have hents : ∀ t < nT I.clients,
        ((σ1.arrs "cnt").set (σ1.vars "tt") ((σ1.arrs "cnt").getD (σ1.vars "tt") 0 + 1)).getD t 0 =
          ((range (σ.vars "ci" + 1)).filter fun i' => typeNum I i' = t).card := by
      intro t ht
      rw [getD_set_ite _ _ _ _ hlen1, htt1, harr, card_filter_succ, hcnt t ht]
      by_cases hte : t = typeNum I (σ.vars "ci")
      · subst hte
        rw [if_pos rfl, if_pos rfl, hcnt _ ht]
      · rw [if_neg hte, if_neg (fun e => hte e.symm)]; simp
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
    all_goals simp [Env.setVar, Env.setArr, hC1.X, hC1.n, hC1.m, hC1.k, hS1.nn, hS1.T, hS1.Z,
      hS1.Vv, hS1.N, hS1.M, hS1.zl, hci1']
    · omega
    · rw [harr, hlen]
    · intro t ht
      simpa [List.getD_eq_getElem?_getD, hci1'] using hents t ht

/-- The scalars and arrays the table loop may change. -/
def CV : List String := "ci" :: TL
def CA : List String := ["cnt"]

theorem cntCom_frame : (∀ y ∈ cntCom.wvars, y ∈ CV) ∧ (∀ a ∈ cntCom.warrs, a ∈ CA) ∧
    ¬ cntCom.reads ∧ cntCom.NoWrite := by
  exact ⟨by decide, by decide, by decide, by decide⟩

theorem cntCom_spec (h : Bh I x k B) :
    Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.arrs "cnt" = List.replicate (nT I.clients) 0)
      cntCom
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧ (σ'.arrs "cnt").length = nT I.clients ∧
        (∀ t < nT I.clients, (σ'.arrs "cnt").getD t 0 = cntN I t) ∧ AgreeA CV CA σ σ')
      (((204 * (I.clients * I.clients) + 40) + 4) * I.days + 6) := by
  have hmB := h.m_lt
  have hloop := Spec.forRangeZero (B := B) (c := dayBody) "ci" "m" (CInv I x k) I.days
    (204 * (I.clients * I.clients) + 40) hmB (fun σ hσ => hσ.2.2.1) (fun σ hσ => hσ.1.m)
    (dayBody_spec h)
  have hfr := Spec.frame hloop
  obtain ⟨hv, ha, hr, hw⟩ := cntCom_frame
  have hpre : ∀ σ : Env, (Ctx0 I x k σ ∧ Sizes I σ ∧ σ.arrs "cnt" = List.replicate (nT I.clients) 0) →
      CInv I x k (σ.setVar "ci" 0) := by
    rintro σ ⟨hC, hS, hcnt⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals simp [Env.setVar, hC.X, hC.n, hC.m, hC.k, hS.nn, hS.T, hS.Z, hS.Vv, hS.N, hS.M, hS.zl,
      hcnt]
  refine Spec.conseq hfr hpre ?_ le_rfl
  rintro σ σ' hσ ⟨⟨⟨hC, hS, hle, hlen, hcnt⟩, hci⟩, hf1, hf2, hf3, hf4⟩
  refine ⟨hC, hS, hlen, fun t ht => ?_, agreeA_of_frame hv ha hr hw hf1 hf2 hf3 hf4⟩
  rw [hcnt t ht, hci]; rfl

end Lax117284Proofs.Machine.ClBuild

end

/-! ### `Lax117284Proofs.Machine.ClBuildOk` -/

section
/-!
The table of independent pairs: `okt[c] = 1` exactly when the pair (type `c / Z`, subset `c % Z`)
is independent.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- One position `q = a * n + b` of the pair `(ct, cs)`: the flag drops to zero on a violation. -/
def okStep : Com := seqs [
  asg "qa" (dv (V "q") (V "n")), asg "qb" (sub (V "q") (mul (V "qa") (V "n"))),
  asg "bd" (mul (mul (add (ltFl (V "qa") (V "qb")) (ltFl (V "qb") (V "qa")))
    (mul (bitE (V "cs") (V "qa")) (bitE (V "cs") (V "qb")))) (bitE (V "ct") (V "q"))),
  asg "fg" (sub (V "fg") (mul (V "fg") (V "bd"))),
  asg "q" (add (V "q") (lit 1))]

/-- The flag of one pair, in `fg`. -/
def okInner : Com := seqs [asg "fg" (lit 1), asg "q" (lit 0), .while (.lt (V "q") (V "nn")) okStep]

/-- The store into the table and the increment. -/
def okBump : Com := seqs [.store "okt" (V "cc") (V "fg"), asg "cc" (add (V "cc") (lit 1))]

/-- One column: split it into type and subset, compute the flag, store it. -/
def okBody : Com := .seq (.seq (asg "ct" (dv (V "cc") (V "Z")))
  (asg "cs" (sub (V "cc") (mul (V "ct") (V "Z"))))) (.seq okInner okBump)

/-- The whole table. -/
def okCom : Com := seqs [asg "cc" (lit 0), .while (.lt (V "cc") (V "Vv")) okBody]

theorem bitE_eq (x p : ℕ) : x / 2 ^ p % 2 = if x.testBit p = true then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h2 : x / 2 ^ p % 2 < 2 := Nat.mod_lt _ (by norm_num)
  by_cases h : x / 2 ^ p % 2 = 1
  · simp [h]
  · have : x / 2 ^ p % 2 = 0 := by omega
    simp [this]

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The invariant of the position loop for the column `c`. -/
def OInv (I : Instance) (x : List ℕ) (k c : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ct" = c / nZ I.clients ∧ σ.vars "cs" = c % nZ I.clients ∧
    σ.vars "q" ≤ I.clients * I.clients ∧
    σ.vars "fg" = if (∀ q' < σ.vars "q", ¬ badQ I.clients (c / nZ I.clients) (c % nZ I.clients) q')
      then 1 else 0

theorem bd_eq (n ct cs q : ℕ) :
    ((q % n - q / n - (q % n - q / n - 1)) + (q / n - q % n - (q / n - q % n - 1))) *
      (cs / 2 ^ (q / n) % 2 * (cs / 2 ^ (q % n) % 2)) * (ct / 2 ^ q % 2) =
      if badQ n ct cs q then 1 else 0 := by
  rw [bitE_eq, bitE_eq, bitE_eq]
  unfold badQ
  by_cases h1 : q / n = q % n
  · simp [h1]
  · have : (q % n - q / n - (q % n - q / n - 1)) + (q / n - q % n - (q / n - q % n - 1)) = 1 := by
      omega
    rw [this]
    by_cases h2 : cs.testBit (q / n) = true <;> by_cases h3 : cs.testBit (q % n) = true <;>
      by_cases h4 : ct.testBit q = true <;> simp [h1, h2, h3, h4]

theorem mod2_mul_le (a b : ℕ) : a % 2 * (b % 2) ≤ 1 := by
  have := Nat.mod_lt a (by norm_num : 0 < 2); have := Nat.mod_lt b (by norm_num : 0 < 2)
  interval_cases (a % 2) <;> interval_cases (b % 2) <;> simp

theorem sub1_sum (a b : ℕ) : (a - (a - 1)) + (b - (b - 1)) ≤ 2 := by omega

set_option maxHeartbeats 6400000 in
theorem okStep_spec (h : Bh I x k B) (c : ℕ) (hc : c < nV I.clients) :
    Spec B (fun σ => OInv I x k c σ ∧ σ.vars "q" < I.clients * I.clients) okStep
      (fun σ σ' => OInv I x k c σ' ∧ σ'.vars "q" = σ.vars "q" + 1) 200 := by
  have hnB := h.n_lt
  have hnnB := h.nn_lt
  have hnT := h.nT_lt
  rcases Nat.eq_zero_or_pos I.clients with h0 | hn
  · intro σ ⟨_, hq⟩
    rw [h0] at hq; simp at hq
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hctT : c / nZ I.clients < nT I.clients := by
    rw [Nat.div_lt_iff_lt_mul (nZ_pos _)]; exact hc
  have hcsZ : c % nZ I.clients < nZ I.clients := Nat.mod_lt _ (nZ_pos _)
  have hmod : ∀ q n : ℕ, q - q / n * n = q % n := fun q n => by
    rw [Nat.mul_comm]; exact (Nat.mod_def q n).symm
  have hlt : ∀ q' : ℕ, (∀ p ≤ q', ¬ badQ I.clients (c / nZ I.clients) (c % nZ I.clients) p) ↔
      ((∀ p < q', ¬ badQ I.clients (c / nZ I.clients) (c % nZ I.clients) p) ∧
        ¬ badQ I.clients (c / nZ I.clients) (c % nZ I.clients) q') := by
    intro q'
    constructor
    · intro hh; exact ⟨fun p hp => hh p (by omega), hh q' le_rfl⟩
    · rintro ⟨h1, h2⟩ p hp
      rcases Nat.lt_or_ge p q' with h3 | h3
      · exact h1 p h3
      · have : p = q' := by omega
        rw [this]; exact h2
  run_vcg
  all_goals
    obtain ⟨hC, hS, hct, hcs, hqle, hfg⟩ := ‹OInv I x k c _›
    have hq : σ.vars "q" < I.clients * I.clients := ‹_›
    have hd1 : σ.vars "q" / I.clients ≤ σ.vars "q" := Nat.div_le_self _ _
    have hd2 : σ.vars "q" / I.clients * I.clients ≤ σ.vars "q" := Nat.div_mul_le_self _ _
    have hd3 : σ.vars "q" % I.clients ≤ σ.vars "q" := Nat.mod_le _ _
    have hd4 : σ.vars "q" / I.clients < I.clients := Nat.div_lt_of_lt_mul hq
    have hd5 : σ.vars "q" % I.clients < I.clients := Nat.mod_lt _ hn
    have hd6 : σ.vars "q" % I.clients - σ.vars "q" / I.clients ≤ σ.vars "q" :=
      le_trans (Nat.sub_le _ _) hd3
    have hd7 : σ.vars "q" % I.clients - σ.vars "q" / I.clients - 1 ≤ σ.vars "q" :=
      le_trans (Nat.sub_le _ _) hd6
    have hd8 : σ.vars "q" / I.clients - σ.vars "q" % I.clients ≤ σ.vars "q" :=
      le_trans (Nat.sub_le _ _) hd1
    have hd9 : σ.vars "q" / I.clients - σ.vars "q" % I.clients - 1 ≤ σ.vars "q" :=
      le_trans (Nat.sub_le _ _) hd8
    have he1 : c % nZ I.clients / 2 ^ (σ.vars "q" / I.clients) ≤ c % nZ I.clients := Nat.div_le_self _ _
    have he2 : c % nZ I.clients / 2 ^ (σ.vars "q" % I.clients) ≤ c % nZ I.clients := Nat.div_le_self _ _
    have he3 : c / nZ I.clients / 2 ^ σ.vars "q" ≤ c / nZ I.clients := Nat.div_le_self _ _
    have hm2 : ∀ a : ℕ, a % 2 < 2 := fun a => Nat.mod_lt _ (by norm_num)
  all_goals try
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals try simp [Env.setVar, hC.X, hC.n, hC.m, hC.k, hS.nn, hS.T, hS.Z, hS.Vv, hS.N, hS.M,
    hS.zl, hct, hcs, hmod, bd_eq, hlt]
  all_goals try (rw [hfg]; split_ifs <;> simp_all)
  all_goals try omega
  all_goals try (rw [bd_eq]; split_ifs <;> omega)
  all_goals try (split_ifs <;> omega)
  all_goals try
    (have ha := hm2 (c % nZ I.clients / 2 ^ (σ.vars "q" / I.clients))
     have hb := hm2 (c % nZ I.clients / 2 ^ (σ.vars "q" % I.clients))
     have hB3 : 2 < B := by omega
     first
       | exact lt_of_le_of_lt (mod2_mul_le _ _) (by omega)
       | exact lt_of_le_of_lt (Nat.mul_le_mul (sub1_sum _ _) (mod2_mul_le _ _)) (by omega))

end Lax117284Proofs.Machine.ClBuild

end

/-! ### `Lax117284Proofs.Machine.ClBuildOk2` -/

section
/-!
The table of independent pairs: the loop over the positions gives the flag of one pair, the loop
over the columns fills the table.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The scalars the flag loop may change. -/
def OL : List String := ["fg", "q", "qa", "qb", "bd"]

theorem okInner_frame : ∀ (c : Com), c = (Com.seq (.assign "q" (.lit 0))
      (.while (.lt (.var "q") (.var "nn")) okStep)) →
    (∀ y ∈ c.wvars, y ∈ OL) ∧ (∀ a ∈ c.warrs, False) ∧ ¬ c.reads ∧ c.NoWrite := by
  intro c hc
  subst hc
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro a ha
  have : (Com.seq (.assign "q" (.lit 0)) (.while (.lt (.var "q") (.var "nn")) okStep)).warrs = [] := by
    decide
  rw [this] at ha; simp at ha

theorem okInner_spec (h : Bh I x k B) (c : ℕ) (hc : c < nV I.clients) :
    Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ct" = c / nZ I.clients ∧
        σ.vars "cs" = c % nZ I.clients) okInner
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧ σ'.vars "ct" = c / nZ I.clients ∧
        σ'.vars "cs" = c % nZ I.clients ∧
        σ'.vars "fg" = (if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0) ∧
        AgreeOff OL σ σ') (((200 + 4) * (I.clients * I.clients) + 6) + 2) := by
  have hnnB := h.nn_lt
  have hloop := Spec.forRangeZero (B := B) (c := okStep) "q" "nn" (OInv I x k c)
    (I.clients * I.clients) 200 hnnB (fun σ hσ => hσ.2.2.2.2.1) (fun σ hσ => hσ.2.1.nn)
    (okStep_spec h c hc)
  have hfr := Spec.frame hloop
  have hasg : Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ct" = c / nZ I.clients ∧
      σ.vars "cs" = c % nZ I.clients) (asg "fg" (lit 1)) (fun σ σ' => σ' = σ.setVar "fg" 1) (1 + 1) := by
    have := Spec.assign (B := B) (P := fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧
      σ.vars "ct" = c / nZ I.clients ∧ σ.vars "cs" = c % nZ I.clients)
      (x := "fg") (e := lit 1) (f := fun _ => 1) (fun σ _ => evalB_lit (by have := h.hL; have := h.mn_le; omega))
    simpa using this
  unfold okInner
  refine Spec.mono (Spec.seq (P' := fun σ => OInv I x k c (σ.setVar "q" 0)) hasg hfr ?_ ?_)
    (by simp [Expr.size]; omega)
  · rintro σ σ1 ⟨hC, hS, hct, hcs⟩ rfl
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    all_goals simp [Env.setVar, hC.X, hC.n, hC.m, hC.k, hS.nn, hS.T, hS.Z, hS.Vv, hS.N, hS.M, hS.zl,
      hct, hcs]
  · rintro σ σ1 σ2 ⟨hC, hS, hct, hcs⟩ rfl ⟨⟨hT, hq⟩, hf1, hf2, hf3, hf4⟩
    obtain ⟨hv, ha, hr, hw⟩ := okInner_frame _ rfl
    have hA1 : AgreeOff ["fg"] σ (σ.setVar "fg" 1) :=
      ⟨rfl, rfl, rfl, fun y hy => by simp at hy; simp [Env.setVar, hy]⟩
    have hA2 := agree_of_frame_gen hv ha hr hw hf1 hf2 hf3 hf4
    obtain ⟨hT1, hT2, hT3, hT4, hT5, hT6⟩ := hT
    refine ⟨hT1, hT2, hT3, hT4, ?_, AgreeOff.mono' (AgreeOff.trans' hA1 hA2) ?_⟩
    · rw [hT6, hq]
      have := indepB_iff_q I.clients (c / nZ I.clients) (c % nZ I.clients)
      by_cases hb : indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true
      · rw [if_pos hb, if_pos (this.mp hb)]
      · rw [if_neg hb, if_neg (fun hh => hb (this.mpr hh))]
    · intro y hy
      simp only [OL, List.mem_append, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      tauto

theorem okBump_spec :
    Spec B (fun σ => σ.vars "cc" < (σ.arrs "okt").length ∧ σ.vars "fg" < B ∧ σ.vars "cc" + 1 < B ∧
        σ.vars "cc" < B) okBump
      (fun σ σ' => σ' = (σ.setArr "okt" (σ.vars "cc") (σ.vars "fg")).setVar "cc" (σ.vars "cc" + 1)) 20 := by
  run_vcg
  all_goals try rfl

/-- The invariant of the loop over the columns. -/
def OkInv (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "cc" ≤ nV I.clients ∧ (σ.arrs "okt").length = nV I.clients ∧
    ∀ c < σ.vars "cc", (σ.arrs "okt").getD c 0 =
      if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0

theorem okSplit_spec (h : Bh I x k B) :
    Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "cc" < nV I.clients)
      (.seq (asg "ct" (dv (V "cc") (V "Z"))) (asg "cs" (sub (V "cc") (mul (V "ct") (V "Z")))))
      (fun σ σ' => AgreeOff ["ct", "cs"] σ σ' ∧ σ'.vars "ct" = σ.vars "cc" / nZ I.clients ∧
        σ'.vars "cs" = σ.vars "cc" % nZ I.clients) 20 := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hmod : ∀ q n : ℕ, q - q / n * n = q % n := fun q n => by
    rw [Nat.mul_comm]; exact (Nat.mod_def q n).symm
  run_vcg
  all_goals
    have hC : Ctx0 I x k σ := ‹_›
    have hS : Sizes I σ := ‹_›
    have hcc : σ.vars "cc" < nV I.clients := ‹_›
    have hd1 : σ.vars "cc" / nZ I.clients ≤ σ.vars "cc" := Nat.div_le_self _ _
    have hd2 : σ.vars "cc" / nZ I.clients * nZ I.clients ≤ σ.vars "cc" := Nat.div_mul_le_self _ _
  all_goals try refine ⟨⟨rfl, rfl, rfl, fun y hy => ?_⟩, ?_, ?_⟩
  all_goals try
    (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
     simp [Env.setVar, hy.1, hy.2])
  all_goals try simp [Env.setVar, hS.Z, hmod]
  all_goals try omega

/-- The state between the phases of the body. -/
def OkMid (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  OkInv I x k σ ∧ σ.vars "cc" < nV I.clients ∧ σ.vars "ct" = σ.vars "cc" / nZ I.clients ∧
    σ.vars "cs" = σ.vars "cc" % nZ I.clients

theorem okBody_spec (h : Bh I x k B) :
    Spec B (fun σ => OkInv I x k σ ∧ σ.vars "cc" < nV I.clients) okBody
      (fun σ σ' => OkInv I x k σ' ∧ σ'.vars "cc" = σ.vars "cc" + 1)
      (((200 + 4) * (I.clients * I.clients) + 6) + 2 + 60) := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hB3 : 2 < B := by have := h.mn_le; omega
  unfold okBody
  have hS1 := Spec.pre (okSplit_spec h) (fun σ (hσ : OkInv I x k σ ∧ σ.vars "cc" < nV I.clients) =>
    (⟨hσ.1.1, hσ.1.2.1, hσ.2⟩ : Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "cc" < nV I.clients))
  have hS2 : Spec B (fun σ => OkMid I x k σ) okInner
      (fun σ σ' => OkInv I x k σ' ∧ σ'.vars "cc" = σ.vars "cc" ∧ σ'.vars "cc" < nV I.clients ∧
        σ'.vars "fg" = (if indepB I.clients (σ.vars "cc" / nZ I.clients) (σ.vars "cc" % nZ I.clients) = true
          then 1 else 0)) (((200 + 4) * (I.clients * I.clients) + 6) + 2) := by
    intro σ hσ
    obtain ⟨hOK, hlt, hct, hcs⟩ := hσ
    obtain ⟨σ', hr, hq⟩ := okInner_spec h (σ.vars "cc") hlt σ ⟨hOK.1, hOK.2.1, hct, hcs⟩
    obtain ⟨hC', hS', hct', hcs', hfg', hA⟩ := hq
    have hlt' : σ'.vars "cc" = σ.vars "cc" := hA.2.2.2 "cc" (by decide)
    refine ⟨σ', hr, ⟨⟨hC', hS', ?_, ?_, ?_⟩, hlt', by rw [hlt']; exact hlt, hfg'⟩⟩
    · rw [hlt']; exact hOK.2.2.1
    · rw [hA.1]; exact hOK.2.2.2.1
    · intro c hc
      rw [hA.1, hlt'] at *
      exact hOK.2.2.2.2 c (by rw [← hlt']; exact hc)
  have hS3 : Spec B (fun σ => OkInv I x k σ ∧ σ.vars "cc" < nV I.clients ∧
      σ.vars "fg" = (if indepB I.clients (σ.vars "cc" / nZ I.clients) (σ.vars "cc" % nZ I.clients) = true
        then 1 else 0)) okBump
      (fun σ σ' => OkInv I x k σ' ∧ σ'.vars "cc" = σ.vars "cc" + 1) 20 := by
    intro σ ⟨hOK, hlt, hfg⟩
    obtain ⟨hC, hS, hle, hlen, hent⟩ := hOK
    have hcc : σ.vars "cc" < (σ.arrs "okt").length := by rw [hlen]; exact hlt
    have hfgB : σ.vars "fg" < B := by rw [hfg]; split_ifs <;> omega
    obtain ⟨σ', hr, hσ'⟩ := okBump_spec σ ⟨hcc, hfgB, by omega, by omega⟩
    refine ⟨σ', hr, ?_, by rw [hσ']; rfl⟩
    subst hσ'
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals simp [Env.setVar, Env.setArr, hC.X, hC.n, hC.m, hC.k, hS.nn, hS.T, hS.Z, hS.Vv, hS.N,
      hS.M, hS.zl]
    · omega
    · rw [hlen]
    · intro c hc
      by_cases hce : c = σ.vars "cc"
      · subst hce
        simp [List.getElem?_set_self hcc, hfg]
      · have hlt' : c < σ.vars "cc" := by omega
        rw [List.getElem?_set_ne (Ne.symm hce)]
        simpa [List.getD_eq_getElem?_getD] using hent c hlt'
  have hS23 : Spec B (OkMid I x k) (.seq okInner okBump)
      (fun σ σ' => OkInv I x k σ' ∧ σ'.vars "cc" = σ.vars "cc" + 1)
      ((((200 + 4) * (I.clients * I.clients) + 6) + 2) + 20) := by
    refine Spec.seq (P' := fun σ => OkInv I x k σ ∧ σ.vars "cc" < nV I.clients ∧
      σ.vars "fg" = (if indepB I.clients (σ.vars "cc" / nZ I.clients) (σ.vars "cc" % nZ I.clients) = true
        then 1 else 0)) hS2 hS3 ?_ ?_
    · rintro σ σ1 hσ ⟨hOK1, hcc1, hlt1, hfg1⟩
      exact ⟨hOK1, hlt1, by rw [hcc1]; exact hfg1⟩
    · rintro σ σ1 σ2 hσ ⟨hOK1, hcc1, hlt1, hfg1⟩ ⟨hOK2, hcc2⟩
      exact ⟨hOK2, by rw [hcc2, hcc1]⟩
  refine Spec.mono (Spec.seq (P' := OkMid I x k) hS1 hS23 ?_ ?_) (by omega)
  · rintro σ σ1 ⟨⟨hC, hS, hle, hlen, hent⟩, hlt⟩ ⟨hA, hct, hcs⟩
    have hcc1 : σ1.vars "cc" = σ.vars "cc" := hA.2.2.2 "cc" (by decide)
    refine ⟨⟨hC.agree hA (by decide) (by decide) (by decide),
      hS.agree hA (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      by rw [hcc1]; exact hle, by rw [hA.1]; exact hlen, ?_⟩, by rw [hcc1]; exact hlt,
      by rw [hct, hcc1], by rw [hcs, hcc1]⟩
    intro c hc
    rw [hA.1]
    exact hent c (by rw [← hcc1]; exact hc)
  · rintro σ σ1 σ2 hσ hQ1 ⟨hOK2, hcc2⟩
    have hcc1 : σ1.vars "cc" = σ.vars "cc" := hQ1.1.2.2.2 "cc" (by decide)
    exact ⟨hOK2, by rw [hcc2, hcc1]⟩

/-- The scalars and arrays the table loop may change. -/
def OV : List String := "cc" :: "ct" :: "cs" :: OL
def OA : List String := ["okt"]

theorem okCom_frame : (∀ y ∈ okCom.wvars, y ∈ OV) ∧ (∀ a ∈ okCom.warrs, a ∈ OA) ∧
    ¬ okCom.reads ∧ okCom.NoWrite := by
  exact ⟨by decide, by decide, by decide, by decide⟩

theorem okCom_spec (h : Bh I x k B) :
    Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ σ.arrs "okt" = List.replicate (nV I.clients) 0)
      okCom
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧ (σ'.arrs "okt").length = nV I.clients ∧
        (∀ c < nV I.clients, (σ'.arrs "okt").getD c 0 =
          if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0) ∧
        AgreeA OV OA σ σ')
      ((((200 + 4) * (I.clients * I.clients) + 6) + 2 + 60 + 4) * nV I.clients + 6) := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hVB : nV I.clients < B := by omega
  have hloop := Spec.forRangeZero (B := B) (c := okBody) "cc" "Vv" (OkInv I x k) (nV I.clients)
    (((200 + 4) * (I.clients * I.clients) + 6) + 2 + 60) hVB (fun σ hσ => hσ.2.2.1)
    (fun σ hσ => hσ.2.1.Vv) (okBody_spec h)
  have hfr := Spec.frame hloop
  obtain ⟨hv, ha, hr, hw⟩ := okCom_frame
  have hpre : ∀ σ : Env, (Ctx0 I x k σ ∧ Sizes I σ ∧ σ.arrs "okt" = List.replicate (nV I.clients) 0) →
      OkInv I x k (σ.setVar "cc" 0) := by
    rintro σ ⟨hC, hS, hok⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals simp [Env.setVar, hC.X, hC.n, hC.m, hC.k, hS.nn, hS.T, hS.Z, hS.Vv, hS.N, hS.M, hS.zl,
      hok]
  refine Spec.conseq hfr hpre ?_ le_rfl
  rintro σ σ' hσ ⟨⟨⟨hC, hS, hle, hlen, hent⟩, hcc⟩, hf1, hf2, hf3, hf4⟩
  refine ⟨hC, hS, hlen, fun c hc => ?_, agreeA_of_frame hv ha hr hw hf1 hf2 hf3 hf4⟩
  exact hent c (by rw [hcc]; exact hc)

end Lax117284Proofs.Machine.ClBuild

end

/-! ### `Lax117284Proofs.Machine.ClBuildFill` -/

section
/-!
The word of the program, entry by entry: the entry at position `idx` is the count, a coefficient,
or a right-hand side, by the formula `zFunRaw`.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The coefficient of variable `fc` in constraint `fr`, into `cf`. -/
def coefCom : Com := seqs [
  asg "cf" (lit 0),
  .ite (.lt (V "fc") (V "Vv"))
    (.ite (.eq (.get "okt" (V "fc")) (lit 1))
      (.ite (.lt (V "fr") (V "T"))
        (.ite (.eq (V "ct") (V "fr")) (asg "cf" (lit 1)) .skip)
        (.ite (.eq (bitE (V "cs") (sub (V "fr") (V "T"))) (lit 0)) (asg "cf" (lit 1)) .skip))
      .skip)
    (.ite (.lt (V "fr") (V "T")) .skip
      (.ite (.eq (sub (V "fc") (V "Vv")) (sub (V "fr") (V "T"))) (asg "cf" (lit 1)) .skip))]

/-- The position `fq` of the matrix, as row `fr` and column `fc`, the column as type and subset. -/
def idxCom : Com := seqs [
  asg "fq" (sub (V "idx") (lit 2)), asg "fr" (dv (V "fq") (V "N")),
  asg "fc" (sub (V "fq") (mul (V "fr") (V "N"))),
  asg "ct" (dv (V "fc") (V "Z")), asg "cs" (sub (V "fc") (mul (V "ct") (V "Z")))]

/-- Store `cf` into the word. -/
def zStore : Com := .store "z" (V "idx") (V "cf")

/-- A coefficient. -/
def coefPart : Com := .seq idxCom (.seq coefCom zStore)

/-- The right-hand side into `cf`. -/
def rhsCom : Com := seqs [
  asg "fr" (sub (sub (V "idx") (lit 2)) (mul (V "M") (V "N"))),
  .ite (.lt (V "fr") (V "T")) (asg "cf" (.get "cnt" (V "fr"))) (asg "cf" (sub (V "m") (V "k")))]

/-- A right-hand side. -/
def rhsPart : Com := .seq rhsCom zStore

/-- One entry of the word. -/
def zBody : Com :=
  .ite (.eq (V "idx") (lit 0)) (.store "z" (V "idx") (V "N"))
    (.ite (.eq (V "idx") (lit 1)) (.store "z" (V "idx") (V "M"))
      (.ite (.lt (V "idx") (add (lit 2) (mul (V "M") (V "N")))) coefPart rhsPart))

/-- The word. -/
def fillCom : Com := seqs [asg "idx" (lit 0), .while (.lt (V "idx") (V "zl")) (.seq zBody (asg "idx" (add (V "idx") (lit 1))))]

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The state at the coefficient: the table of independent pairs and the coordinates. -/
def CoefPre (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ (σ.arrs "okt").length = nV I.clients ∧
    (∀ c < nV I.clients, (σ.arrs "okt").getD c 0 =
      if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0) ∧
    σ.vars "ct" = σ.vars "fc" / nZ I.clients ∧ σ.vars "cs" = σ.vars "fc" % nZ I.clients ∧
    σ.vars "fr" < nM I.clients ∧ σ.vars "fc" < nN I.clients

set_option maxHeartbeats 3200000 in
theorem coefCom_spec (h : Bh I x k B) :
    Spec B (CoefPre I x k) coefCom
      (fun σ σ' => σ'.vars "cf" = coefRaw I.clients (σ.vars "fr") (σ.vars "fc") ∧
        AgreeOff ["cf"] σ σ') 100 := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hB3 : 2 < B := by have := h.mn_le; omega
  run_vcg
  all_goals
    obtain ⟨hC, hS, hlen, hok, hct, hcs, hfr, hfc⟩ := ‹CoefPre I x k _›
    have hd1 : σ.vars "fc" / nZ I.clients ≤ σ.vars "fc" := Nat.div_le_self _ _
    have hd2 : σ.vars "fc" % nZ I.clients ≤ σ.vars "fc" := Nat.mod_le _ _
    have hd5 : σ.vars "fc" % nZ I.clients / 2 ^ (σ.vars "fr" - nT I.clients) ≤ σ.vars "fc" % nZ I.clients := Nat.div_le_self _ _
    have hd3 : σ.vars "fr" < B := by omega
    have hd4 : σ.vars "fc" < B := by omega
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
  all_goals try
    refine ⟨?_, rfl, rfl, rfl, fun y hy => ?_⟩
  all_goals try
    (simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
     simp [Env.setVar, hy])
  all_goals try simp [Env.setVar, coefRaw, hS.Vv, hS.T, hS.Z, hct, hcs, Nat.testBit_eq_decide_div_mod_eq]
  all_goals try simp_all [coefRaw, hS.Vv, hS.T, hS.Z, hct, hcs, hok, Nat.testBit_eq_decide_div_mod_eq]
  all_goals try omega
  all_goals try (split_ifs <;> simp_all <;> omega)

end Lax117284Proofs.Machine.ClBuild

end

/-! ### `Lax117284Proofs.Machine.ClBuildFill2` -/

section
/-!
The entries of the word: a coefficient, a right-hand side, or one of the two counts.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The state at an entry of the word: the tables and the array of the word. -/
def ZPre (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ (σ.arrs "okt").length = nV I.clients ∧
    (∀ c < nV I.clients, (σ.arrs "okt").getD c 0 =
      if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0) ∧
    (σ.arrs "cnt").length = nT I.clients ∧
    (∀ t < nT I.clients, (σ.arrs "cnt").getD t 0 = cntN I t) ∧
    (σ.arrs "z").length = zLen I.clients ∧ σ.vars "idx" < zLen I.clients

/-- The scalars an entry may change. -/
def ZV : List String := ["fq", "fr", "fc", "ct", "cs", "cf"]

theorem idxCom_spec (h : Bh I x k B) :
    Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ 2 ≤ σ.vars "idx" ∧ σ.vars "idx" < zLen I.clients)
      idxCom
      (fun σ σ' => AgreeOff ["fq", "fr", "fc", "ct", "cs"] σ σ' ∧
        σ'.vars "fr" = (σ.vars "idx" - 2) / nN I.clients ∧
        σ'.vars "fc" = (σ.vars "idx" - 2) % nN I.clients ∧
        σ'.vars "ct" = σ'.vars "fc" / nZ I.clients ∧ σ'.vars "cs" = σ'.vars "fc" % nZ I.clients) 100 := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hmod : ∀ q n : ℕ, q - q / n * n = q % n := fun q n => by
    rw [Nat.mul_comm]; exact (Nat.mod_def q n).symm
  run_vcg
  all_goals
    have hC : Ctx0 I x k σ := ‹_›
    have hS : Sizes I σ := ‹_›
    have hi2 : 2 ≤ σ.vars "idx" := ‹_›
    have hil : σ.vars "idx" < zLen I.clients := ‹_›
    have hd1 : (σ.vars "idx" - 2) / nN I.clients ≤ σ.vars "idx" - 2 := Nat.div_le_self _ _
    have hd2 : (σ.vars "idx" - 2) / nN I.clients * nN I.clients ≤ σ.vars "idx" - 2 := Nat.div_mul_le_self _ _
    have hd3 : (σ.vars "idx" - 2) % nN I.clients ≤ σ.vars "idx" - 2 := Nat.mod_le _ _
    have hd4 : (σ.vars "idx" - 2) % nN I.clients / nZ I.clients ≤ (σ.vars "idx" - 2) % nN I.clients := Nat.div_le_self _ _
    have hd5 : (σ.vars "idx" - 2) % nN I.clients / nZ I.clients * nZ I.clients ≤ (σ.vars "idx" - 2) % nN I.clients := Nat.div_mul_le_self _ _
  all_goals try refine ⟨⟨rfl, rfl, rfl, fun y hy => ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals try
    (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
     simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2])
  all_goals try simp [Env.setVar, hS.N, hS.Z, hmod]
  all_goals try omega

theorem zStore_spec :
    Spec B (fun σ => σ.vars "idx" < (σ.arrs "z").length ∧ σ.vars "cf" < B ∧ σ.vars "idx" < B) zStore
      (fun σ σ' => σ' = σ.setArr "z" (σ.vars "idx") (σ.vars "cf")) 10 := by
  run_vcg
  all_goals try rfl

theorem coefPart_eq : coefPart = .seq idxCom (.seq coefCom zStore) := rfl

/-- The state after the coordinates of the entry are known. -/
def CP (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  CoefPre I x k σ ∧ (σ.arrs "z").length = zLen I.clients ∧ σ.vars "idx" < zLen I.clients ∧
    σ.vars "fr" = (σ.vars "idx" - 2) / nN I.clients ∧ σ.vars "fc" = (σ.vars "idx" - 2) % nN I.clients

theorem coefRaw_le (n r c : ℕ) : coefRaw n r c ≤ 1 := by
  unfold coefRaw
  split_ifs <;> omega

/-- The state before the coefficient's entry is computed. -/
def PZ (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  ZPre I x k σ ∧ 2 ≤ σ.vars "idx" ∧ σ.vars "idx" < 2 + nM I.clients * nN I.clients

theorem coefPart_spec (h : Bh I x k B) :
    Spec B (PZ I x k) coefPart
      (fun σ σ' => AgreeA ZV ["z"] σ σ' ∧
        σ'.arrs "z" = (σ.arrs "z").set (σ.vars "idx")
          (coefRaw I.clients ((σ.vars "idx" - 2) / nN I.clients) ((σ.vars "idx" - 2) % nN I.clients)))
      (100 + (100 + 10)) := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hB3 : 2 < B := by have := h.mn_le; omega
  have hidx := Spec.pre (idxCom_spec h) (fun σ (hσ : PZ I x k σ) =>
    (⟨hσ.1.1, hσ.1.2.1, hσ.2.1, hσ.1.2.2.2.2.2.2.2⟩ : Ctx0 I x k σ ∧ Sizes I σ ∧ 2 ≤ σ.vars "idx" ∧
      σ.vars "idx" < zLen I.clients))
  have hcoef := Spec.pre (coefCom_spec h (B := B)) (fun σ (hσ : CP I x k σ) => hσ.1)
  rw [coefPart_eq]
  have hin : Spec B (CP I x k) (.seq coefCom zStore)
      (fun σ σ' => AgreeA ["cf"] ["z"] σ σ' ∧ σ'.arrs "z" = (σ.arrs "z").set (σ.vars "idx")
        (coefRaw I.clients (σ.vars "fr") (σ.vars "fc"))) (100 + 10) := by
    refine Spec.seq (P' := fun σ => σ.vars "idx" < (σ.arrs "z").length ∧ σ.vars "cf" < B ∧
      σ.vars "idx" < B) hcoef zStore_spec ?_ ?_
    · rintro σ σ1 hσ ⟨hcf, hA⟩
      have hidx1 : σ1.vars "idx" = σ.vars "idx" := hA.2.2.2 "idx" (by decide)
      have hz1 : σ1.arrs "z" = σ.arrs "z" := by rw [hA.1]
      have hil := hσ.2.2.1
      refine ⟨by rw [hidx1, hz1, hσ.2.1]; exact hσ.2.2.1, ?_, by rw [hidx1]; omega⟩
      rw [hcf]
      have := coefRaw_le I.clients (σ.vars "fr") (σ.vars "fc")
      omega
    · rintro σ σ1 σ2 hσ ⟨hcf, hA⟩ hσ2
      subst hσ2
      have hz1 : σ1.arrs "z" = σ.arrs "z" := by rw [hA.1]
      have hidx1 : σ1.vars "idx" = σ.vars "idx" := hA.2.2.2 "idx" (by decide)
      have hfr1 : σ1.vars "fr" = σ.vars "fr" := hA.2.2.2 "fr" (by decide)
      have hfc1 : σ1.vars "fc" = σ.vars "fc" := hA.2.2.2 "fc" (by decide)
      refine ⟨⟨fun a ha => ?_, hA.2.1, hA.2.2.1, fun y hy => ?_⟩, ?_⟩
      · have : a ≠ "z" := by simpa using ha
        simp [Env.setArr, this, hA.1]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        simp [Env.setArr, hA.2.2.2 y (by simpa using hy)]
      · simp [Env.setArr, hz1, hidx1, hcf, hfr1, hfc1]
  refine Spec.mono (Spec.seq (P' := CP I x k) hidx hin ?_ ?_) (by omega)
  · rintro σ σ1 ⟨⟨hC, hS, hol, hoe, hcl, hce, hzl, hil⟩, hi2, hlt⟩ ⟨hA, hfr, hfc, hct, hcs⟩
    have hidx1 : σ1.vars "idx" = σ.vars "idx" := hA.2.2.2 "idx" (by decide)
    have hq : σ.vars "idx" - 2 < nM I.clients * nN I.clients := by omega
    have hN := nN_pos I.clients
    refine ⟨⟨hC.agree hA (by decide) (by decide) (by decide),
      hS.agree hA (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      by rw [hA.1]; exact hol, fun c hc => by rw [hA.1]; exact hoe c hc, hct, hcs, ?_, ?_⟩,
      by rw [hA.1]; exact hzl, by rw [hidx1]; exact hil, by rw [hfr, hidx1], by rw [hfc, hidx1]⟩
    · rw [hfr, Nat.div_lt_iff_lt_mul hN]; exact hq
    · rw [hfc]; exact Nat.mod_lt _ hN
  · rintro σ σ1 σ2 ⟨⟨hC, hS, hol, hoe, hcl, hce, hzl, hil⟩, hi2, hlt⟩ ⟨hA, hfr, hfc, hct, hcs⟩ ⟨hA2, hz2⟩
    have hidx1 : σ1.vars "idx" = σ.vars "idx" := hA.2.2.2 "idx" (by decide)
    have hz1 : σ1.arrs "z" = σ.arrs "z" := by rw [hA.1]
    refine ⟨?_, ?_⟩
    · exact AgreeA.mono (AgreeA.trans (AgreeOff.toA hA) hA2) (by
        intro y hy; simp only [ZV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
        tauto) (by intro a ha; simp at ha ⊢; tauto)
    · rw [hz2, hz1, hidx1, hfr, hfc]

/-- The state before the entry of a right-hand side. -/
def PR (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  ZPre I x k σ ∧ 2 + nM I.clients * nN I.clients ≤ σ.vars "idx"

theorem rhsCom_spec (h : Bh I x k B) :
    Spec B (PR I x k) rhsCom
      (fun σ σ' => AgreeOff ["fr", "cf"] σ σ' ∧
        σ'.vars "cf" = rhsRaw I.clients I.days k (cntN I) (σ.vars "idx" - 2 - nM I.clients * nN I.clients))
      100 := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hmB := h.m_lt
  have hkB := h.k_lt
  run_vcg
  all_goals
    obtain ⟨⟨hC, hS, hol, hoe, hcl, hce, hzl, hil⟩, hge⟩ := ‹PR I x k _›
    have hMN : σ.vars "M" * σ.vars "N" = nM I.clients * nN I.clients := by rw [hS.M, hS.N]
    have hMv : σ.vars "M" < B := by rw [hS.M]; omega
    have hNv : σ.vars "N" < B := by rw [hS.N]; omega
    have hcntle : ∀ r, cntN I r ≤ I.days := fun r => (Finset.card_filter_le _ _).trans (by simp)
  all_goals try refine ⟨⟨rfl, rfl, rfl, fun y hy => ?_⟩, ?_⟩
  all_goals try
    (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
     simp [Env.setVar, hy.1, hy.2])
  all_goals try simp [Env.setVar, rhsRaw, hS.T, hC.m, hC.k, hMN]
  all_goals try omega
  all_goals try simp_all [rhsRaw, hS.T, hC.m, hC.k, hMN, hce]
  all_goals try (exact lt_of_le_of_lt (hcntle _) hmB)

theorem rhsPart_spec (h : Bh I x k B) :
    Spec B (PR I x k) rhsPart
      (fun σ σ' => AgreeA ZV ["z"] σ σ' ∧
        σ'.arrs "z" = (σ.arrs "z").set (σ.vars "idx")
          (rhsRaw I.clients I.days k (cntN I) (σ.vars "idx" - 2 - nM I.clients * nN I.clients)))
      (100 + 10) := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hB3 : 2 < B := by have := h.mn_le; omega
  have hmB := h.m_lt
  have hkB := h.k_lt
  have hcntle : ∀ r, cntN I r ≤ I.days := fun r => (Finset.card_filter_le _ _).trans (by simp)
  unfold rhsPart
  refine Spec.seq (P' := fun σ => σ.vars "idx" < (σ.arrs "z").length ∧ σ.vars "cf" < B ∧
    σ.vars "idx" < B) (Spec.pre (rhsCom_spec h) (fun σ (hσ : PR I x k σ) => hσ)) zStore_spec ?_ ?_
  · rintro σ σ1 hσ ⟨hA, hcf⟩
    have hidx1 : σ1.vars "idx" = σ.vars "idx" := hA.2.2.2 "idx" (by decide)
    have hz1 : σ1.arrs "z" = σ.arrs "z" := by rw [hA.1]
    obtain ⟨⟨hC, hS, hol, hoe, hcl, hce, hzl, hil⟩, hge⟩ := hσ
    refine ⟨by rw [hidx1, hz1, hzl]; exact hil, ?_, by rw [hidx1]; omega⟩
    rw [hcf]
    unfold rhsRaw
    split_ifs
    · exact lt_of_le_of_lt (hcntle _) hmB
    · omega
  · rintro σ σ1 σ2 hσ ⟨hA, hcf⟩ hσ2
    subst hσ2
    have hz1 : σ1.arrs "z" = σ.arrs "z" := by rw [hA.1]
    have hidx1 : σ1.vars "idx" = σ.vars "idx" := hA.2.2.2 "idx" (by decide)
    refine ⟨⟨fun a ha => ?_, hA.2.1, hA.2.2.1, fun y hy => ?_⟩, ?_⟩
    · have : a ≠ "z" := by simpa using ha
      simp [Env.setArr, this, hA.1]
    · simp only [ZV, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [Env.setArr, hA.2.2.2 y (by simp; tauto)]
    · simp [Env.setArr, hz1, hidx1, hcf]

theorem zBody_spec (h : Bh I x k B) :
    Spec B (ZPre I x k) zBody
      (fun σ σ' => AgreeA ZV ["z"] σ σ' ∧
        σ'.arrs "z" = (σ.arrs "z").set (σ.vars "idx") (zFunRaw I.clients I.days k (cntN I) (σ.vars "idx")))
      (10 + 10 + 10 + (100 + 10) + 100 + 10) := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hB3 : 2 < B := by have := h.mn_le; omega
  unfold zBody
  run_vcg [coefPart_spec h, rhsPart_spec h]
  all_goals
    have hZ : ZPre I x k σ := ‹_›
    obtain ⟨hC, hS, hol, hoe, hcl, hce, hzl, hil⟩ := hZ
    have hMN : σ.vars "M" * σ.vars "N" = nM I.clients * nN I.clients := by rw [hS.M, hS.N]
    have hMv : σ.vars "M" < B := by rw [hS.M]; omega
    have hNv : σ.vars "N" < B := by rw [hS.N]; omega
    have hidxB : σ.vars "idx" < B := by omega
    have hMNle : 2 + nM I.clients * nN I.clients ≤ zLen I.clients := by simp only [zLen]; omega
  all_goals try omega
  all_goals try (rw [hMN]; omega)
  all_goals try
    (refine ⟨⟨hC, hS, hol, hoe, hcl, hce, hzl, hil⟩, ?_, ?_⟩ <;> rw [← hMN] at * <;> omega)
  all_goals try
    (refine ⟨⟨hC, hS, hol, hoe, hcl, hce, hzl, hil⟩, ?_⟩; rw [← hMN] at *; omega)
  all_goals try
    (refine ⟨?_, ?_⟩
     · exact ⟨fun a ha => by simp [Env.setArr, (by simpa using ha : a ≠ "z")], rfl, rfl,
         fun y hy => rfl⟩
     · simp [Env.setArr, zFunRaw, hS.N, hS.M, *])
  all_goals try
    (obtain ⟨hAg, hzeq⟩ := ‹AgreeA ZV ["z"] σ _ ∧ _›
     refine ⟨hAg, ?_⟩
     rw [hzeq]
     have hc' : ¬ σ.vars "idx" < 2 + nM I.clients * nN I.clients := by
       rw [← hMN]; assumption
     simp only [zFunRaw, if_neg hc', *]
     simp_all)
  all_goals try
    (obtain ⟨hAg, hzeq⟩ := ‹AgreeA ZV ["z"] σ _ ∧ _›
     refine ⟨hAg, ?_⟩
     rw [hzeq]
     have hc' : σ.vars "idx" < 2 + nM I.clients * nN I.clients := by
       rw [← hMN]; assumption
     simp only [zFunRaw, if_pos hc', *]
     simp_all)

end Lax117284Proofs.Machine.ClBuild

end

/-! ### `Lax117284Proofs.Machine.ClBuildFill3` -/

section
/-!
The loop over the entries of the word.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- One entry and the increment. -/
def fillBody : Com := .seq zBody (asg "idx" (add (V "idx") (lit 1)))

/-- The invariant of the loop over the entries. -/
def FInv (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ (σ.arrs "okt").length = nV I.clients ∧
    (∀ c < nV I.clients, (σ.arrs "okt").getD c 0 =
      if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0) ∧
    (σ.arrs "cnt").length = nT I.clients ∧
    (∀ t < nT I.clients, (σ.arrs "cnt").getD t 0 = cntN I t) ∧
    (σ.arrs "z").length = zLen I.clients ∧ σ.vars "idx" ≤ zLen I.clients ∧
    ∀ i < σ.vars "idx", (σ.arrs "z").getD i 0 = zFunRaw I.clients I.days k (cntN I) i

theorem incr_spec : Spec B (fun σ => σ.vars "idx" + 1 < B ∧ 1 < B ∧ σ.vars "idx" < B)
    (asg "idx" (add (V "idx") (lit 1)))
    (fun σ σ' => σ' = σ.setVar "idx" (σ.vars "idx" + 1)) 10 := by
  run_vcg
  all_goals try rfl

theorem zPre_of_finv {σ : Env} (hF : FInv I x k σ) (hlt : σ.vars "idx" < zLen I.clients) :
    ZPre I x k σ :=
  ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2.1, hF.2.2.2.2.2.1, hF.2.2.2.2.2.2.1, hlt⟩

theorem fillBody_spec (h : Bh I x k B) :
    Spec B (fun σ => FInv I x k σ ∧ σ.vars "idx" < zLen I.clients) fillBody
      (fun σ σ' => FInv I x k σ' ∧ σ'.vars "idx" = σ.vars "idx" + 1)
      ((10 + 10 + 10 + (100 + 10) + 100 + 10) + 20) := by
  have hzl := h.hzB
  have hL := h.hL
  unfold fillBody
  have hz := Spec.pre (zBody_spec h) (fun σ (hσ : FInv I x k σ ∧ _) => zPre_of_finv hσ.1 hσ.2)
  have hB1 : 1 < B := by have := h.mn_le; omega
  refine Spec.seq (P' := fun σ => σ.vars "idx" + 1 < B ∧ 1 < B ∧ σ.vars "idx" < B) hz
    (Spec.mono (Spec.pre (incr_spec (B := B)) (fun σ hσ => hσ)) (by omega)) ?_ ?_
  · rintro σ σ1 ⟨hF, hlt⟩ ⟨hA, hzeq⟩
    have hidx1 : σ1.vars "idx" = σ.vars "idx" := hA.2.2.2 "idx" (by decide)
    refine ⟨by rw [hidx1]; omega, hB1, by rw [hidx1]; omega⟩
  · rintro σ σ1 σ2 ⟨hF, hlt⟩ ⟨hA, hzeq⟩ hσ2
    subst hσ2
    have hidx1 : σ1.vars "idx" = σ.vars "idx" := hA.2.2.2 "idx" (by decide)
    obtain ⟨hC, hS, hol, hoe, hcl, hce, hzl2, hle, hent⟩ := hF
    have hz1 : ∀ a, a ≠ "z" → σ1.arrs a = σ.arrs a := fun a ha => hA.1 a (by simpa using ha)
    have hzlen1 : (σ1.arrs "z").length = zLen I.clients := by
      rw [hzeq, List.length_set]; exact hzl2
    have hV : ∀ y, y ∉ ZV → σ1.vars y = σ.vars y := hA.2.2.2
    have hX1 := hz1 "X" (by decide)
    have hok1 := hz1 "okt" (by decide)
    have hcn1 := hz1 "cnt" (by decide)
    have hv : ∀ y, y ≠ "idx" → y ≠ "fq" → y ≠ "fr" → y ≠ "fc" → y ≠ "ct" → y ≠ "cs" → y ≠ "cf" →
        σ1.vars y = σ.vars y := fun y h1 h2 h3 h4 h5 h6 h7 =>
      hV y (by simp [ZV, h2, h3, h4, h5, h6, h7])
    have hnv := hv "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hmv := hv "m" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hkv := hv "k" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hnnv := hv "nn" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hTv := hv "T" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hZv := hv "Z" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hVv := hv "Vv" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hNv := hv "N" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hMv := hv "M" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hzlv := hv "zl" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals simp [Env.setVar, hX1, hC.X, hnv, hC.n, hmv, hC.m, hkv, hC.k, hnnv, hS.nn, hTv, hS.T,
      hZv, hS.Z, hVv, hS.Vv, hNv, hS.N, hMv, hS.M, hzlv, hS.zl, hok1, hol, hcn1, hcl, hzlen1, hidx1]
    all_goals try (intro c hc; simpa [List.getD_eq_getElem?_getD] using hoe c hc)
    all_goals try (intro t ht; simpa [List.getD_eq_getElem?_getD] using hce t ht)
    all_goals try exact hlt
    all_goals try
      (intro i hi
       rw [hzeq]
       by_cases hie : i = σ.vars "idx"
       · subst hie
         have : σ.vars "idx" < (σ.arrs "z").length := by rw [hzl2]; exact hlt
         simp [List.getElem?_set_self this]
       · have hlt' : i < σ.vars "idx" := by omega
         rw [List.getElem?_set_ne (Ne.symm hie)]
         simpa [List.getD_eq_getElem?_getD] using hent i hlt')

/-- The scalars and arrays the fill may change. -/
def FV : List String := "idx" :: ZV
def FA : List String := ["z"]

theorem fillCom_frame : (∀ y ∈ fillCom.wvars, y ∈ FV) ∧ (∀ a ∈ fillCom.warrs, a ∈ FA) ∧
    ¬ fillCom.reads ∧ fillCom.NoWrite := by
  exact ⟨by decide, by decide, by decide, by decide⟩

theorem fillCom_spec (h : Bh I x k B) :
    Spec B (fun σ => Ctx0 I x k σ ∧ Sizes I σ ∧ (σ.arrs "okt").length = nV I.clients ∧
        (∀ c < nV I.clients, (σ.arrs "okt").getD c 0 =
          if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0) ∧
        (σ.arrs "cnt").length = nT I.clients ∧
        (∀ t < nT I.clients, (σ.arrs "cnt").getD t 0 = cntN I t) ∧
        (σ.arrs "z").length = zLen I.clients) fillCom
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧
        σ'.arrs "z" = zList I.clients I.days k (cntN I) ∧ AgreeA FV FA σ σ')
      ((((10 + 10 + 10 + (100 + 10) + 100 + 10) + 20) + 4) * zLen I.clients + 6) := by
  have hzl := h.hzB
  have hL := h.hL
  have hzB : zLen I.clients < B := by omega
  have hloop := Spec.forRangeZero (B := B) (c := fillBody) "idx" "zl" (FInv I x k) (zLen I.clients)
    ((10 + 10 + 10 + (100 + 10) + 100 + 10) + 20) hzB (fun σ hσ => hσ.2.2.2.2.2.2.2.1)
    (fun σ hσ => hσ.2.1.zl) (fillBody_spec h)
  have hfr := Spec.frame hloop
  obtain ⟨hv, ha, hr, hw⟩ := fillCom_frame
  have hpre : ∀ σ : Env, (Ctx0 I x k σ ∧ Sizes I σ ∧ (σ.arrs "okt").length = nV I.clients ∧
        (∀ c < nV I.clients, (σ.arrs "okt").getD c 0 =
          if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0) ∧
        (σ.arrs "cnt").length = nT I.clients ∧
        (∀ t < nT I.clients, (σ.arrs "cnt").getD t 0 = cntN I t) ∧
        (σ.arrs "z").length = zLen I.clients) → FInv I x k (σ.setVar "idx" 0) := by
    rintro σ ⟨hC, hS, hol, hoe, hcl, hce, hzl2⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [Env.setVar, hC.X, hC.n, hC.m, hC.k, hS.nn, hS.T, hS.Z, hS.Vv, hS.N, hS.M, hS.zl,
      hol, hcl, hzl2]
    · intro c hc; simpa [List.getD_eq_getElem?_getD] using hoe c hc
    · intro t ht; simpa [List.getD_eq_getElem?_getD] using hce t ht
  refine Spec.conseq hfr hpre ?_ le_rfl
  rintro σ σ' hσ ⟨⟨⟨hC, hS, hol, hoe, hcl, hce, hzl2, hle, hent⟩, hidx⟩, hf1, hf2, hf3, hf4⟩
  refine ⟨hC, hS, ?_, agreeA_of_frame hv ha hr hw hf1 hf2 hf3 hf4⟩
  refine List.ext_getElem (by rw [hzl2]; simp [zList, zLen]) fun i hi1 hi2 => ?_
  have hi : i < zLen I.clients := by rw [hzl2] at hi1; exact hi1
  have := hent i (by rw [hidx]; exact hi)
  rw [List.getD_eq_getElem _ _ hi1] at this
  rw [this]
  simp [zList, List.getElem_map, List.getElem_range]

end Lax117284Proofs.Machine.ClBuild

end

/-! ### `Lax117284Proofs.Machine.ClBuildAll` -/

section
/-!
The builder, whole: the sizes, the table of counts, the table of independent pairs, the word.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The whole builder. -/
def buildCom : Com := seqs [sizesCom, cntCom, okCom, fillCom]

/-- The scalars and arrays the builder may change. -/
def BV : List String := ["nn", "T", "Z", "Vv", "N", "M", "zl"] ++ (CV ++ (OV ++ FV))
def BA : List String := CA ++ (OA ++ FA)

theorem sizes_agreeA (h : Bh I x k B) {σ σ' : Env}
    (hf : (∀ y, y ∉ ["nn", "T", "Z", "Vv", "N", "M", "zl"] → σ'.vars y = σ.vars y) ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) :
    AgreeA ["nn", "T", "Z", "Vv", "N", "M", "zl"] [] σ σ' :=
  ⟨fun a _ => by rw [hf.2.1], hf.2.2.1, hf.2.2.2, hf.1⟩

/-- The state before the table of counts. -/
def B2 (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ σ.arrs "cnt" = List.replicate (nT I.clients) 0 ∧
    σ.arrs "okt" = List.replicate (nV I.clients) 0 ∧ σ.arrs "z" = List.replicate (zLen I.clients) 0

/-- The state after the table of counts. -/
def B3 (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ (σ.arrs "cnt").length = nT I.clients ∧
    (∀ t < nT I.clients, (σ.arrs "cnt").getD t 0 = cntN I t) ∧
    σ.arrs "okt" = List.replicate (nV I.clients) 0 ∧ σ.arrs "z" = List.replicate (zLen I.clients) 0

/-- The state after the table of independent pairs. -/
def B4 (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ (σ.arrs "okt").length = nV I.clients ∧
    (∀ c < nV I.clients, (σ.arrs "okt").getD c 0 =
      if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0) ∧
    (σ.arrs "cnt").length = nT I.clients ∧
    (∀ t < nT I.clients, (σ.arrs "cnt").getD t 0 = cntN I t) ∧
    (σ.arrs "z").length = zLen I.clients

theorem build234_spec (h : Bh I x k B) :
    Spec B (B2 I x k) (.seq cntCom (.seq okCom fillCom))
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧
        σ'.arrs "z" = zList I.clients I.days k (cntN I) ∧ AgreeA (CV ++ (OV ++ FV)) (CA ++ (OA ++ FA)) σ σ')
      ((((204 * (I.clients * I.clients) + 40) + 4) * I.days + 6) +
        ((((200 + 4) * (I.clients * I.clients) + 6) + 2 + 60 + 4) * nV I.clients + 6) +
        ((((10 + 10 + 10 + (100 + 10) + 100 + 10) + 20) + 4) * zLen I.clients + 6)) := by
  have hc := Spec.pre (cntCom_spec h) (fun σ (hσ : B2 I x k σ) =>
    (⟨hσ.1, hσ.2.1, hσ.2.2.1⟩ : Ctx0 I x k σ ∧ Sizes I σ ∧ σ.arrs "cnt" = List.replicate (nT I.clients) 0))
  have ho := Spec.pre (okCom_spec h) (fun σ (hσ : B3 I x k σ) =>
    (⟨hσ.1, hσ.2.1, hσ.2.2.2.2.1⟩ : Ctx0 I x k σ ∧ Sizes I σ ∧ σ.arrs "okt" = List.replicate (nV I.clients) 0))
  have hf := Spec.pre (fillCom_spec h) (fun σ (hσ : B4 I x k σ) => hσ)
  have hOF : Spec B (B3 I x k) (.seq okCom fillCom)
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧ σ'.arrs "z" = zList I.clients I.days k (cntN I) ∧
        AgreeA (OV ++ FV) (OA ++ FA) σ σ')
      (((((200 + 4) * (I.clients * I.clients) + 6) + 2 + 60 + 4) * nV I.clients + 6) +
        ((((10 + 10 + 10 + (100 + 10) + 100 + 10) + 20) + 4) * zLen I.clients + 6)) := by
    refine Spec.seq (P' := B4 I x k) ho hf ?_ ?_
    · rintro σ σ1 ⟨hC, hS, hcl, hce, hoke, hzr⟩ ⟨hC1, hS1, hol, hoe, hA⟩
      have hcn1 : σ1.arrs "cnt" = σ.arrs "cnt" := hA.1 "cnt" (by decide)
      have hz1 : σ1.arrs "z" = σ.arrs "z" := hA.1 "z" (by decide)
      refine ⟨hC1, hS1, hol, hoe, by rw [hcn1]; exact hcl, fun t ht => by rw [hcn1]; exact hce t ht, ?_⟩
      rw [hz1, hzr]; simp
    · rintro σ σ1 σ2 hσ ⟨hC1, hS1, hol, hoe, hA1⟩ ⟨hC2, hS2, hz2, hA2⟩
      exact ⟨hC2, hS2, hz2, AgreeA.trans hA1 hA2⟩
  refine Spec.mono (Spec.seq (P' := B3 I x k) hc hOF ?_ ?_) (by omega)
  · rintro σ σ1 ⟨hC, hS, hcn, hok, hzr⟩ ⟨hC1, hS1, hcl, hce, hA⟩
    have hok1 : σ1.arrs "okt" = σ.arrs "okt" := hA.1 "okt" (by decide)
    have hz1 : σ1.arrs "z" = σ.arrs "z" := hA.1 "z" (by decide)
    exact ⟨hC1, hS1, hcl, hce, by rw [hok1]; exact hok, by rw [hz1]; exact hzr⟩
  · rintro σ σ1 σ2 hσ ⟨hC1, hS1, hcl, hce, hA1⟩ ⟨hC2, hS2, hz2, hA2⟩
    exact ⟨hC2, hS2, hz2, AgreeA.trans hA1 hA2⟩

/-- The cost of the builder. -/
def buildCost (I : Instance) : ℕ :=
  100 + ((((204 * (I.clients * I.clients) + 40) + 4) * I.days + 6) +
    ((((200 + 4) * (I.clients * I.clients) + 6) + 2 + 60 + 4) * nV I.clients + 6) +
    ((((10 + 10 + 10 + (100 + 10) + 100 + 10) + 20) + 4) * zLen I.clients + 6))

/-- **The builder computes the word of the integer program.** -/
theorem buildCom_spec (h : Bh I x k B) :
    Spec B (fun σ => Ctx0 I x k σ ∧ σ.arrs "cnt" = List.replicate (nT I.clients) 0 ∧
        σ.arrs "okt" = List.replicate (nV I.clients) 0 ∧ σ.arrs "z" = List.replicate (zLen I.clients) 0)
      buildCom
      (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧
        σ'.arrs "z" = zList I.clients I.days k (cntN I) ∧ AgreeA BV BA σ σ') (buildCost I) := by
  have hs := Spec.pre (sizesCom_spec h) (fun σ (hσ : Ctx0 I x k σ ∧ σ.arrs "cnt" = List.replicate (nT I.clients) 0 ∧
    σ.arrs "okt" = List.replicate (nV I.clients) 0 ∧ σ.arrs "z" = List.replicate (zLen I.clients) 0) => hσ.1)
  have h234 := build234_spec h
  unfold buildCom buildCost
  refine Spec.mono (Spec.seq (P' := B2 I x k) hs h234 ?_ ?_) (by omega)
  · rintro σ σ1 ⟨hC, hcn, hok, hz⟩ ⟨hC1, hS1, hf, harr, hinp, hout⟩
    exact ⟨hC1, hS1, by rw [harr]; exact hcn, by rw [harr]; exact hok, by rw [harr]; exact hz⟩
  · rintro σ σ1 σ2 hσ ⟨hC1, hS1, hf, harr, hinp, hout⟩ ⟨hC2, hS2, hz2, hA2⟩
    refine ⟨hC2, hS2, hz2, ?_⟩
    exact AgreeA.mono (AgreeA.trans (sizes_agreeA h ⟨hf, harr, hinp, hout⟩) hA2)
      (fun y hy => by simp only [BV, List.mem_append] at hy ⊢; tauto)
      (fun a ha => by simp only [BA, List.mem_append, List.not_mem_nil, false_or] at ha ⊢; tauto)

end Lax117284Proofs.Machine.ClBuild

end

/-! ### `Lax117284Proofs.Machine.ClMainRead` -/

section
/-!
Reading the word: the two counts into scalars, the whole word into the array `X`, the fairness
parameter from its last entry.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.Machine.ClBuild
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- One further entry of the word into `X`. -/
def readStep : Com := seqs [.read "rv", .store "X" (V "rt") (V "rv"), asg "rt" (add (V "rt") (lit 1))]

/-- The header: the counts, the length, the first two cells, the counter. -/
def hdrCom : Com := seqs [
  .read "n", .read "m",
  asg "L" (add (mul (lit 2) (mul (V "m") (V "n"))) (lit 3)),
  .store "X" (lit 0) (V "n"), .store "X" (lit 1) (V "m"), asg "rt" (lit 2)]

/-- The word: the header, the rest, the parameter. -/
def readCom : Com := .seq hdrCom (.seq (.while (.lt (V "rt") (V "L")) readStep)
  (asg "k" (.get "X" (sub (V "L") (lit 1)))))

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The state before the reading. -/
def RIn (x : List ℕ) (σ : Env) : Prop :=
  σ.inp = x ∧ σ.out = [] ∧ (σ.arrs "X").length = x.length

/-- The reading loop's invariant. -/
def RLoop (I : Instance) (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "n" = I.clients ∧ σ.vars "m" = I.days ∧ σ.vars "L" = x.length ∧
    (σ.arrs "X").length = x.length ∧ σ.vars "rt" ≤ x.length ∧
    (∀ i < σ.vars "rt", (σ.arrs "X").getD i 0 = x.getD i 0) ∧
    σ.inp = x.drop (σ.vars "rt") ∧ σ.out = []

theorem x_eq_cons (h : Lax117284.InstanceEncoding.EncodesUniform x I k) :
    x = I.clients :: I.days :: x.drop 2 := by
  have h0 := ClientsWord.x0 h
  have h1 := ClientsWord.x1 h
  have hl := ClientsWord.len_eq h
  obtain ⟨a, b, r, rfl⟩ : ∃ a b r, x = a :: b :: r := by
    rcases x with _ | ⟨a, _ | ⟨b, r⟩⟩
    · simp only [List.length_nil] at hl; omega
    · simp only [List.length_singleton] at hl; omega
    · exact ⟨a, b, r, rfl⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1
  simp [h0, h1]

theorem readStep_spec (hL : x.length < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (fun σ => RLoop I x σ ∧ σ.vars "rt" < x.length) readStep
      (fun σ σ' => RLoop I x σ' ∧ σ'.vars "rt" = σ.vars "rt" + 1) 20 := by
  refine Spec.pre (P := fun σ => RLoop I x σ ∧ σ.vars "rt" < x.length ∧ σ.inp ≠ [] ∧
      σ.inp.headD 0 < B ∧ σ.vars "rt" < (σ.arrs "X").length) ?_ ?_
  · run_vcg
    · obtain ⟨hn, hm, hLv, hlen, hle, hcell, hinp, hout⟩ := ‹RLoop I x σ›
      have htlt := ‹σ.vars "rt" < x.length›
      have hidx : σ.vars "rt" < (σ.arrs "X").length := by rw [hlen]; exact htlt
      simp only [RLoop]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp
      · exact hn
      · exact hm
      · exact hLv
      · exact hlen
      · exact htlt
      · intro i hi
        rcases Nat.lt_or_ge i (σ.vars "rt") with h | h
        · rw [List.getElem?_set_ne (by omega)]
          simpa [List.getD_eq_getElem?_getD] using hcell i h
        · have hie : i = σ.vars "rt" := by omega
          subst hie
          rw [hinp]
          simp [hidx, List.head?_drop]
      · rw [hinp, List.tail_drop]
      · exact hout
    · simp only [Env.setVar]
      exact ‹σ.inp.headD 0 < B›
  · rintro σ ⟨hI, ht⟩
    have hinp : σ.inp = x.drop (σ.vars "rt") := hI.2.2.2.2.2.2.1
    have hne : σ.inp ≠ [] := by
      rw [hinp]; intro hc
      have : (x.drop (σ.vars "rt")).length = 0 := by rw [hc]; rfl
      simp only [List.length_drop] at this; omega
    refine ⟨hI, ht, hne, ?_, by rw [hI.2.2.2.1]; exact ht⟩
    rcases hh : σ.inp with _ | ⟨u, rest⟩
    · exact absurd hh hne
    · have : u ∈ x.drop (σ.vars "rt") := by rw [← hinp, hh]; exact List.mem_cons_self
      exact hX u (List.mem_of_mem_drop this)

theorem readLoop_spec (hL : x.length < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (fun σ => RLoop I x σ) (.while (.lt (V "rt") (V "L")) readStep)
      (fun _ σ' => RLoop I x σ' ∧ σ'.vars "rt" = x.length) (24 * x.length + 4) :=
  Spec.forRange "rt" "L" (RLoop I x) x.length 20 (24 * x.length + 4)
    (fun _ h => lt_of_le_of_lt h.2.2.2.2.1 hL) (fun _ h => by rw [h.2.2.1]; exact hL)
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.2.1) (readStep_spec hL hX) (fun _ h => h)
    (fun σ _ => by
      have : (20 + 4) * (x.length - σ.vars "rt") ≤ (20 + 4) * x.length :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      omega)

theorem hdrCom_spec (hdec : Lax117284.InstanceEncoding.EncodesUniform x I k)
    (hL : x.length < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (RIn x) hdrCom
      (fun σ σ' => RLoop I x σ' ∧ σ'.vars "rt" = 2 ∧ (∀ a, a ≠ "X" → σ'.arrs a = σ.arrs a) ∧
        ∀ y, y ∉ ["n", "m", "L", "rt", "rv"] → σ'.vars y = σ.vars y) 40 := by
  have hl := ClientsWord.len_eq hdec
  have h0 := ClientsWord.x0 hdec
  have h1 := ClientsWord.x1 hdec
  have hcons := x_eq_cons hdec
  have hnhd : x.head?.getD 0 = I.clients := by rw [hcons]; simp
  have hm1 : x[1]?.getD 0 = I.days := by rw [hcons]; simp
  have hhd : x.headD 0 = I.clients := by rw [hcons]; simp
  have hhd2 : x.tail.headD 0 = I.days := by rw [hcons]; simp
  have htt : x.tail.tail = x.drop 2 := by rw [hcons]; simp
  have hnB : I.clients < B := hX I.clients (by rw [hcons]; simp)
  have hmB : I.days < B := hX I.days (by rw [hcons]; simp)
  have hxne : x ≠ [] := by intro h; rw [h] at hl; simp only [List.length_nil] at hl; omega
  have hxt : x.tail ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  have hx0' : x[0]?.getD 0 = I.clients := by rw [hcons]; simp
  clear hcons
  run_vcg
  all_goals obtain ⟨hin, hout, hXl⟩ := ‹RIn x σ›
  all_goals simp [Env.setVar, hin, hhd, hhd2, htt, hxne, hxt, hnB, hmB, hnhd, hm1, hXl]
  all_goals try omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals try simp [RLoop, Env.setArr, hin, hout, hXl, hl]
  · omega
  · omega
  · have hX2 : 1 < (σ.arrs "X").length := by omega
    intro i hi
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · have hX0 : 0 < (σ.arrs "X").length := by omega
      simp [hX0, hx0', List.getElem?_set]
    · simp [hX2, hm1, List.getElem?_set]
  · intro a ha; simp [ha]
  · intro y h1 h2 h3 h4 h5; simp [h1, h2, h3, h4, h5]

/-- The last entry: the parameter. -/
theorem kCom_spec (hx : 0 < x.length) (hL : x.length < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (fun σ => RLoop I x σ ∧ σ.vars "rt" = x.length) (asg "k" (.get "X" (sub (V "L") (lit 1))))
      (fun σ σ' => σ'.vars "k" = x.getD (x.length - 1) 0 ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
        σ'.out = σ.out ∧ ∀ y, y ≠ "k" → σ'.vars y = σ.vars y) 10 := by
  have hgB : ∀ j, x.getD j 0 < B := by
    intro j
    by_cases hj : j < x.length
    · rw [List.getD_eq_getElem _ _ hj]; exact hX _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (by omega)]; omega
  run_vcg
  all_goals rename_i hRL hrt
  all_goals obtain ⟨hn1, hm1, hL1, hlen1, -, hcell1, hinp1, hout1⟩ := hRL
  all_goals (have hcx : (σ.arrs "X").getD (σ.vars "L" - 1) 0 = x.getD (x.length - 1) 0 := by
               rw [hL1]; exact hcell1 _ (by omega))
  · have hcx' : (σ.arrs "X")[σ.vars "L" - 1]?.getD 0 = x[x.length - 1]?.getD 0 := by
      simpa [List.getD_eq_getElem?_getD] using hcx
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Env.setVar, hcx']
    intro y h1 h2; exact absurd h2 h1
  all_goals try omega
  simp only [hcx]; exact hgB _

theorem readCore_spec (hdec : Lax117284.InstanceEncoding.EncodesUniform x I k)
    (hL : x.length < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (RIn x) readCom
      (fun σ σ' => Ctx0 I x k σ' ∧ σ'.vars "L" = x.length ∧ σ'.inp = [] ∧ σ'.out = [])
      (24 * x.length + 60) := by
  have hl := ClientsWord.len_eq hdec
  have hk := ClientsWord.xk hdec
  unfold readCom
  refine Spec.mono (Spec.post (Spec.seq' (hdrCom_spec hdec hL hX)
    (Spec.seq' (readLoop_spec (I := I) hL hX) (kCom_spec (by omega) hL hX)
      (fun σ σ' _ h => h))
    (fun σ σ' _ h => h.1)) ?_) (by omega)
  rintro σ σ2 hin ⟨σ1, ⟨hA1, hA2, hA3, hA4⟩, σ3, ⟨⟨hn1, hm1, hL1, hlen1, -, hcell1, hinp1, hout1⟩, hrt1⟩,
    hC1, hC2, hC3, hC4, hC5⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hC2]
    refine List.ext_getElem hlen1 fun i h1 h2 => ?_
    have := hcell1 i (by rw [hrt1]; exact h2)
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some,
      Option.getD_some] at this
  · rw [hC5 _ (by decide), hn1]
  · rw [hC5 _ (by decide), hm1]
  · rw [hC1, ← hk]; congr 1; omega
  · rw [hC5 _ (by decide), hL1]
  · rw [hC3, hinp1, hrt1]; simp
  · rw [hC4, hout1]

theorem readCom_spec (hdec : Lax117284.InstanceEncoding.EncodesUniform x I k)
    (hL : x.length < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (RIn x) readCom
      (fun σ σ' => Ctx0 I x k σ' ∧ σ'.vars "L" = x.length ∧ σ'.inp = [] ∧ σ'.out = [] ∧
        (∀ a, a ≠ "X" → σ'.arrs a = σ.arrs a) ∧
        ∀ y, y ∉ ["n", "m", "L", "rt", "k", "rv"] → σ'.vars y = σ.vars y)
      (24 * x.length + 60) := by
  refine (readCore_spec hdec hL hX).frame.post ?_
  rintro σ σ' - ⟨⟨h1, h2, h3, h4⟩, hv, ha, -, -⟩
  refine ⟨h1, h2, h3, h4, fun a hn => ha a ?_, fun y hy => hv y ?_⟩
  · simp [readCom, hdrCom, readStep, Com.warrs, seqs, asg, hn]
  · simp only [readCom, hdrCom, readStep, Com.wvars, seqs, asg, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    tauto

end Lax117284Proofs.Machine.ClMain

end
