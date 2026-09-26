import Lax808846Proofs.Transfer
import Lax808846Proofs.Tactic

/-!
A word RAM program interpreted inside IMP+: the definitions.

The cited decomposition program is an arbitrary `Program`, and there is no way to call one
machine program from another. What can be done is to write a *universal interpreter* in IMP+ and
prove that it simulates the machine step by step. This file fixes the encoding of a program as
four code arrays, the correspondence `Rel` between a machine state and an IMP+ environment, and
the facts about arrays the correspondence needs.
-/

namespace Lax117284Proofs.Machine.TwRam

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

abbrev V (s : String) : Expr := .var s
abbrev L (n : ℕ) : Expr := .lit n
abbrev G (a : String) (e : Expr) : Expr := .get a e
abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev dvd (e f : Expr) : Expr := .bin .div e f

/-! ### The encoding of a program -/

/-- The code of an instruction. -/
def opcode : Instr → ℕ
  | .set .. => 0 | .load .. => 1 | .store .. => 2 | .add .. => 3 | .sub .. => 4
  | .mul .. => 5 | .div .. => 6 | .and .. => 7 | .shiftl .. => 8 | .not .. => 9
  | .jump .. => 10 | .jzero .. => 11 | .jeof .. => 12 | .inputLength .. => 13
  | .inputLoad .. => 14 | .halt => 15 | .read .. => 16 | .write .. => 17

/-- The first number of an instruction. -/
def fa : Instr → ℕ
  | .set a _ => a | .load a _ => a | .store a _ => a | .add a _ _ => a | .sub a _ _ => a
  | .mul a _ _ => a | .div a _ _ => a | .and a _ _ => a | .shiftl a _ _ => a | .not a _ => a
  | .jump l => l | .jzero a _ => a | .jeof l => l | .inputLength a => a
  | .inputLoad a _ => a | .halt => 0 | .read a => a | .write a => a

/-- The second number of an instruction. -/
def fb : Instr → ℕ
  | .set _ n => n | .load _ b => b | .store _ b => b | .add _ b _ => b | .sub _ b _ => b
  | .mul _ b _ => b | .div _ b _ => b | .and _ b _ => b | .shiftl _ b _ => b | .not _ b => b
  | .jzero _ l => l | .inputLoad _ b => b | _ => 0

/-- The third number of an instruction. -/
def fc : Instr → ℕ
  | .add _ _ c => c | .sub _ _ c => c | .mul _ _ c => c | .div _ _ c => c | .and _ _ c => c
  | .shiftl _ _ c => c | _ => 0

/-- Every number of every instruction is a word of length `Wp`. -/
def Small (Wp : ℕ) (P : Program) : Prop :=
  ∀ i ∈ P, fa i < 2 ^ Wp ∧ fb i < 2 ^ Wp ∧ fc i < 2 ^ Wp

/-! ### Reading and writing arrays -/

lemma getD_set (l : List ℕ) (i j v : ℕ) :
    (l.set i v).getD j 0 = if j = i ∧ i < l.length then v else l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> simp_all

lemma getD_of_le {l : List ℕ} {j : ℕ} (h : l.length ≤ j) : l.getD j 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-! ### The correspondence between a machine state and an environment -/

/-- The things a run of the interpreter never changes. -/
structure Cst (Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) (σ : Env) : Prop where
  Pv : σ.vars "P" = Pn
  wp : σ.vars "wp" = Wp
  ylen : σ.vars "ylen" = y.length
  plen : σ.vars "plen" = P.length
  Y : σ.arrs "Y" = y
  OP : σ.arrs "OP" = P.map opcode
  XA : σ.arrs "XA" = P.map fa
  XB : σ.arrs "XB" = P.map fb
  XC : σ.arrs "XC" = P.map fc
  Mlen : (σ.arrs "M").length = Pn
  Olen : (σ.arrs "O").length = OL

/-- The machine state `s` and the environment `σ` describe the same moment of the run. -/
structure Rel (Pn : ℕ) (y : List ℕ) (s : State) (σ : Env) : Prop where
  pc : σ.vars "pc" = s.pc
  input : s.input = y
  inp : s.inp = y.drop (σ.vars "cur")
  cur : σ.vars "cur" ≤ y.length
  ol : s.out = (σ.arrs "O").take (σ.vars "ol")
  olen : σ.vars "ol" ≤ (σ.arrs "O").length
  M : ∀ a < Pn, (σ.arrs "M").getD a 0 = s.mem a
  mem : ∀ a, s.mem a < Pn

lemma Rel.setMem {Wp Pn : ℕ} (hPn : Pn = 2 ^ Wp) {y : List ℕ} {s : State} {σ : Env}
    (h : Rel Pn y s σ) (hM : (σ.arrs "M").length = Pn) {a v : ℕ} (ha : a < Pn) (hv : v < Pn) :
    Rel Pn y { s with pc := s.pc + 1, mem := setCell Wp s.mem a v }
      ((σ.setArr "M" a v).setVar "pc" (σ.vars "pc" + 1)) := by
  subst hPn
  have hmod : ∀ x, x < 2 ^ Wp → x % 2 ^ Wp = x := fun x hx => Nat.mod_eq_of_lt hx
  refine ⟨by simp [h.pc], h.input, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h.inp
  · simpa using h.cur
  · simpa using h.ol
  · simpa using h.olen
  · intro b hb
    simp only [arrs_setVar, arrs_setArr, if_true, getD_set, setCell, hM, hmod a ha, hmod v hv]
    by_cases hba : b = a
    · simp [hba, ha]
    · have := h.M b hb
      simpa [hba, List.getD_eq_getElem?_getD] using this
  · intro b
    simp only [setCell, hmod a ha, hmod v hv]
    split_ifs
    · exact hv
    · exact h.mem b

end Lax117284Proofs.Machine.TwRam
