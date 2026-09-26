import Lax117284Proofs.Machine.FreeRun
import Lax117284Proofs.Machine.RamBridge2
import Lax117284Proofs.Machine.RamToTuring
import Lax808846Proofs.Transfer

/-!
The reduction that adds a conflict-free day is polynomial-time computable: on the word RAM,
and hence on a Turing machine.
-/

namespace Lax117284Proofs.Machine.FreeFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.FreeRun

/-- The largest entry. -/
def Mx (y : List ℕ) : ℕ := y.foldr max 0

lemma le_Mx {y : List ℕ} {v : ℕ} (hv : v ∈ y) : v ≤ Mx y := by
  induction y with
  | nil => cases hv
  | cons a t ih =>
    simp only [Mx, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp hv with rfl | h
    · omega
    · have := ih h; omega

lemma Mx_mem_or_zero (y : List ℕ) : Mx y ∈ y ∨ Mx y = 0 := by
  induction y with
  | nil => right; rfl
  | cons a t ih =>
    simp only [Mx, List.foldr_cons] at ih ⊢
    rcases le_total a (t.foldr max 0) with h | h
    · rw [max_eq_right h]
      rcases ih with h1 | h1
      · left; exact List.mem_cons_of_mem _ h1
      · right; exact h1
    · rw [max_eq_left h]; left; exact List.mem_cons_self

def layout : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "n",
    "m", "N", "N2", "m1", "g", "kp", "ok", "d", "b3", "v", "s", "u", "i2", "ix", "aa", "M"],
   ["a", "TK"], 12⟩

theorem com_ok : Com.Ok layout mainFree := by
  simp [mainFree, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, UNk.nkU,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    FreeAccept.acceptFree, FreeAccept.prepF, FreeAccept.rejectPrint, FreeCheck.okLoop,
    FreeCheck.okBody, FreeCheck.okChk, FreeCheck.gapLoop, FreeCheck.gapBody, FreeCheck.gapChk,
    FreeProg.printFree, FreeProg.loop1, FreeProg.loop2, FreeProg.step2, Out.outLoop, Out.emitTK,
    Out.emitAt, Out.emitVal, Out.emitVar, Out.emitLit, EmitNat.emitNat, EmitNat.sizeLoop,
    EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody,
    layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

/-- The value bound of an input. -/
def Bd (y : List ℕ) : ℕ := 2 ^ (2 * y.length + 4) + 8 * y.length + 64 + Mx y

/-- The words the program is handed: a list preceded by its length. -/
def Shape : Set (List ℕ) := {z | z ≠ [] ∧ z.headD 0 = z.tail.length}

lemma shape_eq {z : List ℕ} (h : z ∈ Shape) : z = z.tail.length :: z.tail := by
  obtain ⟨hne, hh⟩ := h
  rcases z with _ | ⟨a, t⟩
  · exact absurd rfl hne
  · simp only [List.headD_cons, List.tail_cons] at hh ⊢
    rw [hh]

/-- What the program computes, on the zeros and ones of its input. -/
noncomputable def red (y : List ℕ) : List ℕ :=
  natBits (Lax117284.Corollary8.reduceFreeDay (bitsOf y))

theorem solves : Solves layout mainFree Shape (fun x => red x.tail) (fun x => Bd x.tail)
    (fun x => Kmain x.tail.length (Bd x.tail).size) where
  ok := com_ok
  inp := by
    intro x hx v hv
    rw [shape_eq hx] at hv
    have hpow : x.tail.length < 2 ^ (2 * x.tail.length + 4) := by
      have := Nat.lt_two_pow_self (n := x.tail.length)
      have h2 : 2 ^ x.tail.length ≤ 2 ^ (2 * x.tail.length + 4) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    rcases List.mem_cons.mp hv with rfl | hv'
    · unfold Bd; omega
    · have := le_Mx hv'; unfold Bd; omega
  run := by
    intro x hx
    obtain ⟨σ', hrun, hout⟩ := mainFree_spec (B := Bd x.tail) x.tail
      (fun v hv => by
        have := le_Mx hv
        have h2 : 2 ^ (2 * x.tail.length + 4) ≥ 1 := Nat.one_le_two_pow
        unfold Bd; omega)
      (by unfold Bd; omega)
    rw [← shape_eq hx] at hrun
    exact ⟨_, σ', hrun, hout⟩

def prog : Program := compileProgram layout mainFree

theorem prog_runs (w : ℕ) (x : List ℕ) (hfit : 70 + 2 * Bd x ≤ 2 ^ w) :
    ∃ t ≤ 10 * Kmain x.length (Bd x).size + 1, RunsTo w prog (x.length :: x) (red x) t := by
  have hs : Solves layout mainFree {z | z = x.length :: x} (fun z => red z.tail)
      (fun z => Bd z.tail) (fun z => Kmain z.tail.length (Bd z.tail).size) :=
    ⟨solves.ok, fun z hz => solves.inp z (by rw [hz]; exact ⟨by simp, by simp⟩),
      fun z hz => solves.run z (by rw [hz]; exact ⟨by simp, by simp⟩)⟩
  have h := computesInTime_of_solves (w := w)
    (T := fun z => 10 * Kmain z.tail.length (Bd z.tail).size + 1) hs
    (fun z hz => by
      rw [hz]; simp only [List.tail_cons]
      have hB : 64 ≤ Bd x := by
        have := Nat.zero_le (2 ^ (2 * x.length + 4))
        unfold Bd; omega
      refine fitsWords_of_max_le (by omega) ?_
      simp only [Layout.span, layout, List.length_cons, List.length_nil, max_le_iff]
      omega)
    (fun z hz => by simp [Layout.const])
  obtain ⟨t, ht, hrun⟩ := h (x.length :: x) rfl
  exact ⟨t, by simpa using ht, by simpa [prog] using hrun⟩

/-! ### Word length and running time -/

open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax759944Proofs.Encoding

lemma Bd_lt (x : List ℕ) : Bd x < 2 ^ (2 * bitSize x + 7) := by
  have hlen := length_le_bitSize x
  have hM : Mx x < 2 ^ (bitSize x + 1) := by
    rcases Mx_mem_or_zero x with hm | hm
    · exact mem_lt_two_pow_bitSize_add_one hm
    · rw [hm]; exact Nat.pos_of_ne_zero (by positivity)
  have h1 : 2 ^ (2 * x.length + 4) ≤ 2 ^ (2 * bitSize x + 4) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ (bitSize x + 1) ≤ 2 ^ (2 * bitSize x + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : bitSize x < 2 ^ bitSize x := Nat.lt_two_pow_self
  have h4 : 2 ^ bitSize x ≤ 2 ^ (2 * bitSize x) := Nat.pow_le_pow_right (by omega) (by omega)
  have e1 : (2 : ℕ) ^ (2 * bitSize x + 4) = 16 * 2 ^ (2 * bitSize x) := by ring
  have e2 : (2 : ℕ) ^ (2 * bitSize x + 1) = 2 * 2 ^ (2 * bitSize x) := by ring
  have e3 : (2 : ℕ) ^ (2 * bitSize x + 7) = 128 * 2 ^ (2 * bitSize x) := by ring
  have h5 : 1 ≤ 2 ^ (2 * bitSize x) := Nat.one_le_two_pow
  unfold Bd
  omega

/-- The time bound, a polynomial of degree two in the bit size. -/
noncomputable def timePoly : Polynomial ℕ :=
  Polynomial.C 100000 * (Polynomial.X + Polynomial.C 1) ^ 2

theorem ramPolytime_red : RamPolytime red := by
  refine Lax117284Proofs.Machine.RamBridge2.ramPolytime_of_wordlen (d := 2) (K := 10)
    (prog := prog) timePoly (by omega) ?_ ?_
  · intro x v hv
    unfold red at hv
    simp only [natBits, List.mem_map] at hv
    obtain ⟨b, -, rfl⟩ := hv
    have : (2 : ℕ) ^ 10 ≤ 2 ^ (2 * bitSize x + 10) := Nat.pow_le_pow_right (by omega) (by omega)
    split <;> omega
  · intro w x hw
    have hB := Bd_lt x
    have hlen := length_le_bitSize x
    have hfit : 70 + 2 * Bd x ≤ 2 ^ w := by
      have h1 : (2 : ℕ) ^ (2 * bitSize x + 11) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
      have e : (2 : ℕ) ^ (2 * bitSize x + 11) = 16 * 2 ^ (2 * bitSize x + 7) := by ring
      have h5 : 128 ≤ 2 ^ (2 * bitSize x + 7) := by
        calc (128 : ℕ) = 2 ^ 7 := by norm_num
          _ ≤ 2 ^ (2 * bitSize x + 7) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    obtain ⟨t, ht, hrun⟩ := prog_runs w x hfit
    refine ⟨t, ?_, hrun⟩
    have hsz : (Bd x).size ≤ 2 * bitSize x + 7 := Nat.size_le.mpr hB
    unfold Kmain FreeAccept.Kacc at ht
    simp only [timePoly, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
    have hprod : (96 * (Bd x).size + 200) * (3 * x.length + 4)
        ≤ (96 * (2 * bitSize x + 7) + 200) * (3 * bitSize x + 4) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith [Nat.zero_le (bitSize x)]

/--
---
conclusion: Lax117284.Corollary8.reduceFreeDay_polyTime
---
The reduction is a word RAM program on the zeros and ones of its input: a one-pass tokenizer
reads the numbers of the instance, a first pass over the table checks that every job takes
some time and is not due before it starts, a second pass finds the largest processing time of
the first day, and the numbers of the output are written — the old table, then the new day,
whose due dates are that gap times one, two, and so on. A word that is not the code of such an
instance is answered with the rejected word. The numbers may be exponential in the length of
the input, which the word length of a polynomial-time word RAM accommodates, and polynomial
time on the word RAM transfers to a Turing machine.
-/
theorem reduceFreeDay_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id id Lax117284.Corollary8.reduceFreeDay) := by
  refine Lax117284Proofs.Machine.RamToTuring.polyTime_of_ram ramPolytime_red ?_
  intro w
  unfold red
  rw [bitsOf_natBits]

end Lax117284Proofs.Machine.FreeFinal
