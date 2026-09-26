import Lax117284Proofs.Machine.ClSimDefs

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
