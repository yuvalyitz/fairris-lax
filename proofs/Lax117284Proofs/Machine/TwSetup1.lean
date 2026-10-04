import Lax808846Proofs.Transfer
import Lax808846Proofs.Tactic

/-! ### `Lax117284Proofs.Machine.TwRamDefs` -/

section
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

end

/-! ### `Lax117284Proofs.Machine.TwRamBlocks` -/

section
/-!
The blocks of the interpreter that compute what an instruction stores and where: each leaves the
destination in `ta` and the value, already reduced modulo `2 ^ Wp`, in `t1`.
-/

namespace Lax117284Proofs.Machine.TwRam

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

variable {B : ℕ}

/-- The environment `σ'` is `σ` with the scratch scalars `ta`, `t1`, `t2` changed, `ta` and `t1`
to the destination `d` and the value `v`. -/
structure Wr (σ σ' : Env) (d v : ℕ) : Prop where
  ta : σ'.vars "ta" = d
  t1 : σ'.vars "t1" = v
  arrs : σ'.arrs = σ.arrs
  fr : ∀ x, x ≠ "ta" → x ≠ "t1" → x ≠ "t2" → σ'.vars x = σ.vars x

/-- Normalize the reads of an updated environment. -/
macro "nrm" : tactic => `(tactic| simp only [vars_setVar, arrs_setVar, inp_setVar, out_setVar,
  vars_setArr, ↓reduceIte, String.reduceEq, eq_self])

lemma land_le (a b : ℕ) : Nat.land a b ≤ a := Nat.and_le_left

lemma mod_eq' (x P : ℕ) : x - x / P * P = x % P := by
  rw [Nat.mod_eq_sub_mul_div, Nat.mul_comm]

/-- The side goals of a walk over a block that reduces modulo `P`. -/
macro "side" : tactic => `(tactic| first
  | omega
  | (nrm <;> omega)
  | (nrm; exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) (by omega))
  | (nrm; exact lt_of_le_of_lt (Nat.sub_le _ _) (by omega))
  | (nrm; exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
  | (nrm; exact lt_of_le_of_lt (land_le _ _) (by omega)))

/-- The unchanged parts of a `Wr`. -/
macro "wr_fr" : tactic => `(tactic| (intro x h1 h2 h3; simp only [vars_setVar, h1, h2, h3,
  ↓reduceIte, if_false]))

def cSet : Com := .seq (.assign "ta" (V "ia")) (.assign "t1" (V "ib"))
def modP : Com := .assign "t1" (sub (V "t1") (mul (dvd (V "t1") (V "P")) (V "P")))
def cAdd : Com := .seq (.assign "ta" (V "ia"))
  (.seq (.assign "t1" (add (G "M" (V "ib")) (G "M" (V "ic")))) modP)

theorem cSet_run {Pn : ℕ} {σ : Env} (hP : Pn < B) (ha : σ.vars "ia" < Pn) (hb : σ.vars "ib" < Pn) :
    ∃ σ', Run B cSet σ σ' 10 ∧ Wr σ σ' (σ.vars "ia") (σ.vars "ib") := by
  unfold cSet
  run_vcg
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm
  · nrm
  · wr_fr

/-- The reads of `M` at two operands, in terms of the machine state. -/
structure Ops (Pn : ℕ) (y : List ℕ) (s : State) (σ : Env) : Prop where
  ia : σ.vars "ia" < Pn
  ib : σ.vars "ib" < Pn
  ic : σ.vars "ic" < Pn
  e1 : (σ.arrs "M").getD (σ.vars "ib") 0 = s.mem (σ.vars "ib")
  e2 : (σ.arrs "M").getD (σ.vars "ic") 0 = s.mem (σ.vars "ic")
  f1 : s.mem (σ.vars "ib") < Pn
  f2 : s.mem (σ.vars "ic") < Pn
  e3 : (σ.arrs "M").getD (σ.vars "ia") 0 = s.mem (σ.vars "ia")
  f3 : s.mem (σ.vars "ia") < Pn
  e4 : (σ.arrs "M").getD (s.mem (σ.vars "ib")) 0 = s.mem (s.mem (σ.vars "ib"))
  f4 : s.mem (s.mem (σ.vars "ib")) < Pn
  Pv : σ.vars "P" = Pn
  Mlen : (σ.arrs "M").length = Pn

lemma Ops.mk' {Wp Pn : ℕ} {y : List ℕ} {P : Program} {OL : ℕ} {s : State} {σ : Env}
    (hR : Rel Pn y s σ) (hC : Cst Wp Pn P y OL σ) (ha : σ.vars "ia" < Pn)
    (hb : σ.vars "ib" < Pn) (hc : σ.vars "ic" < Pn) : Ops Pn y s σ :=
  ⟨ha, hb, hc, hR.M _ hb, hR.M _ hc, hR.mem _, hR.mem _, hR.M _ ha, hR.mem _,
    hR.M _ (hR.mem _), hR.mem _, hC.Pv, hC.Mlen⟩

theorem cAdd_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ)
    (hP : Pn + Pn < B) :
    ∃ σ', Run B cAdd σ σ' 40 ∧
      Wr σ σ' (σ.vars "ia") ((s.mem (σ.vars "ib") + s.mem (σ.vars "ic")) % Pn) := by
  have ha := hO.ia
  have hb := hO.ib
  have hc := hO.ic
  have e1 := hO.e1
  have e2 := hO.e2
  have f1 := hO.f1
  have f2 := hO.f2
  have e3 := hO.e3
  have f3 := hO.f3
  have e4 := hO.e4
  have f4 := hO.f4
  have hPv := hO.Pv
  have hL := hO.Mlen
  clear hO
  unfold cAdd modP
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm
    rw [e1, e2, hPv]
    exact mod_eq' _ _
  · nrm
  · wr_fr

def cLoad : Com := .seq (.assign "ta" (V "ia")) (.assign "t1" (G "M" (G "M" (V "ib"))))
def cStore : Com := .seq (.assign "ta" (G "M" (V "ia"))) (.assign "t1" (G "M" (V "ib")))
def cSub : Com := .seq (.assign "ta" (V "ia")) (.assign "t1" (sub (G "M" (V "ib")) (G "M" (V "ic"))))
def cMul : Com := .seq (.assign "ta" (V "ia"))
  (.seq (.assign "t1" (mul (G "M" (V "ib")) (G "M" (V "ic")))) modP)
def cDiv : Com := .seq (.assign "ta" (V "ia")) (.assign "t1" (dvd (G "M" (V "ib")) (G "M" (V "ic"))))
def cAnd : Com := .seq (.assign "ta" (V "ia")) (.assign "t1" (.bin .and (G "M" (V "ib")) (G "M" (V "ic"))))
/-- The shift, without a case split: `t2` is `1` if the shift amount is below the word length and
`0` otherwise, and the amount is multiplied by it. -/
def cShl : Com := .seq (.assign "ta" (V "ia"))
  (.seq (.assign "t2" (sub (V "wp") (G "M" (V "ic"))))
    (.seq (.assign "t2" (dvd (V "t2") (V "t2")))
      (.seq (.assign "t1" (.bin .shiftl (G "M" (V "ib")) (mul (G "M" (V "ic")) (V "t2"))))
        (.seq modP (.assign "t1" (mul (V "t1") (V "t2")))))))
def cNot : Com := .seq (.assign "ta" (V "ia")) (.assign "t1" (sub (sub (V "P") (L 1)) (G "M" (V "ib"))))
def cIlen : Com := .seq (.assign "ta" (V "ia")) (.assign "t1" (V "ylen"))
def cIload : Com :=
  .seq (.ite (.lt (G "M" (V "ib")) (V "ylen")) (.assign "t1" (G "Y" (G "M" (V "ib"))))
    (.assign "t1" (L 0))) (.assign "ta" (V "ia"))

/-- All the fields of a `Wr` except the value. -/
macro "wr_rest" : tactic => `(tactic| (refine ⟨?_, ?_, ?_, ?_⟩ <;> first
  | (nrm; done) | wr_fr | skip))

theorem cLoad_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ) (hB : Pn < B) :
    ∃ σ', Run B cLoad σ σ' 30 ∧ Wr σ σ' (σ.vars "ia") (s.mem (s.mem (σ.vars "ib"))) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  unfold cLoad
  run_vcg
  all_goals try side
  all_goals try (nrm; rw [e1, e4]; omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; rw [e1]; exact e4
  · nrm
  · wr_fr

theorem cStore_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ) (hB : Pn < B) :
    ∃ σ', Run B cStore σ σ' 30 ∧ Wr σ σ' (s.mem (σ.vars "ia")) (s.mem (σ.vars "ib")) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  unfold cStore
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm; exact e3
  · nrm; exact e1
  · nrm
  · wr_fr

theorem cSub_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ) (hB : Pn < B) :
    ∃ σ', Run B cSub σ σ' 40 ∧
      Wr σ σ' (σ.vars "ia") (s.mem (σ.vars "ib") - s.mem (σ.vars "ic")) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  unfold cSub
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; rw [e1, e2]
  · nrm
  · wr_fr

theorem cMul_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ)
    (hB : Pn * Pn < B) :
    ∃ σ', Run B cMul σ σ' 60 ∧
      Wr σ σ' (σ.vars "ia") ((s.mem (σ.vars "ib") * s.mem (σ.vars "ic")) % Pn) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  have hp : s.mem (σ.vars "ib") * s.mem (σ.vars "ic") < B :=
    lt_of_lt_of_le (Nat.mul_lt_mul'' f1 f2) hB.le
  have hp' : (σ.arrs "M").getD (σ.vars "ib") 0 * (σ.arrs "M").getD (σ.vars "ic") 0 < B := by
    rw [e1, e2]; exact hp
  have hPB : Pn < B := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by omega)) hB
  unfold cMul modP
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; rw [e1, e2, hPv]; exact mod_eq' _ _
  · nrm
  · wr_fr


theorem cDiv_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ) (hB : Pn < B) :
    ∃ σ', Run B cDiv σ σ' 40 ∧
      Wr σ σ' (σ.vars "ia") (s.mem (σ.vars "ib") / s.mem (σ.vars "ic")) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  unfold cDiv
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; rw [e1, e2]
  · nrm
  · wr_fr

theorem cAnd_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ) (hB : Pn < B) :
    ∃ σ', Run B cAnd σ σ' 40 ∧
      Wr σ σ' (σ.vars "ia") (Nat.land (s.mem (σ.vars "ib")) (s.mem (σ.vars "ic"))) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  unfold cAnd
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; rw [e1, e2]
  · nrm
  · wr_fr

theorem cNot_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ) (hB : Pn < B) :
    ∃ σ', Run B cNot σ σ' 40 ∧
      Wr σ σ' (σ.vars "ia") (Pn - 1 - s.mem (σ.vars "ib")) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  unfold cNot
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; rw [e1, hPv]
  · nrm
  · wr_fr

theorem cIlen_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hylen : σ.vars "ylen" = y.length)
    (hB : y.length < B) (hP : Pn < B) (ha : σ.vars "ia" < Pn) :
    ∃ σ', Run B cIlen σ σ' 20 ∧ Wr σ σ' (σ.vars "ia") y.length := by
  unfold cIlen
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; exact hylen
  · nrm
  · wr_fr



lemma div_self_le (a : ℕ) : a / a ≤ 1 := by
  rcases Nat.eq_zero_or_pos a with h | h
  · simp [h]
  · rw [Nat.div_self h]

lemma flag_eq (c W : ℕ) : (W - c) / (W - c) = if c < W then 1 else 0 := by
  by_cases h : c < W
  · rw [if_pos h]; exact Nat.div_self (by omega)
  · rw [if_neg h]; have : W - c = 0 := by omega
    rw [this]

lemma shl_bound {Pn Wp B b c : ℕ} (hPn : Pn = 2 ^ Wp) (hB : Pn * Pn < B) (hb : b < Pn) :
    b * 2 ^ (c * ((Wp - c) / (Wp - c))) < B := by
  rw [flag_eq]
  by_cases h : c < Wp
  · rw [if_pos h, Nat.mul_one]
    have h1 : 2 ^ c < Pn := by rw [hPn]; exact Nat.pow_lt_pow_right (by omega) h
    exact lt_of_lt_of_le (Nat.mul_lt_mul'' hb h1) hB.le
  · rw [if_neg h]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
    have hp : 0 < Pn := hPn ▸ Nat.two_pow_pos _
    exact lt_of_lt_of_le hb ((Nat.le_mul_of_pos_left _ hp).trans hB.le)

theorem cShl_run {Pn Wp : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ)
    (hB : Pn * Pn < B) (hPn : Pn = 2 ^ Wp) (hwp : σ.vars "wp" = Wp) :
    ∃ σ', Run B cShl σ σ' 80 ∧
      Wr σ σ' (σ.vars "ia")
        (if s.mem (σ.vars "ic") < Wp then (s.mem (σ.vars "ib") * 2 ^ s.mem (σ.vars "ic")) % Pn
          else 0) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  have hPB : Pn < B := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by omega)) hB
  have hW : Wp < B := lt_of_lt_of_le (hPn ▸ Nat.lt_two_pow_self) hPB.le
  have hsh := shl_bound (b := s.mem (σ.vars "ib")) (c := s.mem (σ.vars "ic")) hPn hB f1
  have hshg : (σ.arrs "M").getD (σ.vars "ib") 0 *
      2 ^ ((σ.arrs "M").getD (σ.vars "ic") 0 *
        ((σ.vars "wp" - (σ.arrs "M").getD (σ.vars "ic") 0) /
          (σ.vars "wp" - (σ.arrs "M").getD (σ.vars "ic") 0))) < B := by
    rw [e1, e2, hwp]; exact hsh
  unfold cShl modP
  run_vcg
  all_goals try side
  all_goals try (nrm; rw [hwp]; exact hW)
  all_goals try (nrm; rw [e2, hwp, flag_eq]; split_ifs <;> omega)
  all_goals try (nrm; rw [e1, e2, hwp]; exact hsh)
  all_goals try (nrm; exact lt_of_le_of_lt (Nat.div_le_self _ _) hshg)
  all_goals try (nrm; exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) hshg)
  all_goals try (nrm; exact lt_of_le_of_lt (Nat.sub_le _ _) hshg)
  all_goals try (nrm; exact lt_of_le_of_lt ((Nat.mul_le_mul_left _ (div_self_le _)).trans_eq
    (Nat.mul_one _)) (lt_of_le_of_lt (Nat.sub_le _ _) hshg))
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm
    rw [e1, e2, hwp, hPv, mod_eq', flag_eq]
    by_cases h : s.mem (σ.vars "ic") < Wp
    · simp [h]
    · simp [h]
  · nrm
  · wr_fr


theorem cIload_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ)
    (hB : Pn < B) (hY : σ.arrs "Y" = y) (hylen : σ.vars "ylen" = y.length)
    (hyB : ∀ v ∈ y, v < B) (hyl : y.length < B) :
    ∃ σ', Run B cIload σ σ' 40 ∧
      Wr σ σ' (σ.vars "ia") (if s.mem (σ.vars "ib") < y.length then y.getD (s.mem (σ.vars "ib")) 0
        else 0) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  have hyg : ∀ k, (σ.arrs "Y").getD k 0 < B := by
    intro k; rw [hY]
    by_cases hk : k < y.length
    · have := hyB (y.getD k 0) (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk)
      simpa using this
    · rw [getD_of_le (by omega)]; omega
  have hYl : (σ.arrs "Y").length = y.length := by rw [hY]
  unfold cIload
  run_vcg
  all_goals try side
  all_goals try exact hyg _
  all_goals refine ⟨?_, ?_, ?_, ?_⟩
  all_goals try nrm
  all_goals try wr_fr
  · rw [e1, hY, if_pos (by omega)]
  · rw [if_neg (by omega)]

end Lax117284Proofs.Machine.TwRam

end

/-! ### `Lax117284Proofs.Machine.TwRamStep` -/

section
/-!
One step of the interpreter: the instructions that store into memory, through the common tail.
-/

namespace Lax117284Proofs.Machine.TwRam

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

variable {B : ℕ}

/-- What an instruction that stores into memory stores, and where: the raw destination and
the raw value, before the reduction modulo `2 ^ Wp` that `setCell` performs. -/
def upd (Wp : ℕ) (s : State) : Instr → Option (ℕ × ℕ)
  | .set a n => some (a, n)
  | .load a b => some (a, s.mem (s.mem (b % 2 ^ Wp) % 2 ^ Wp))
  | .store a b => some (s.mem (a % 2 ^ Wp), s.mem (b % 2 ^ Wp))
  | .add a b c => some (a, s.mem (b % 2 ^ Wp) + s.mem (c % 2 ^ Wp))
  | .sub a b c => some (a, s.mem (b % 2 ^ Wp) - s.mem (c % 2 ^ Wp))
  | .mul a b c => some (a, s.mem (b % 2 ^ Wp) * s.mem (c % 2 ^ Wp))
  | .div a b c => some (a, s.mem (b % 2 ^ Wp) / s.mem (c % 2 ^ Wp))
  | .and a b c => some (a, Nat.land (s.mem (b % 2 ^ Wp)) (s.mem (c % 2 ^ Wp)))
  | .shiftl a b c => some (a, s.mem (b % 2 ^ Wp) * 2 ^ s.mem (c % 2 ^ Wp))
  | .not a b => some (a, 2 ^ Wp - 1 - s.mem (b % 2 ^ Wp))
  | .inputLength a => some (a, s.input.length)
  | .inputLoad a b => some (a, s.input[s.mem (b % 2 ^ Wp) % 2 ^ Wp]?.getD 0)
  | _ => none

lemma effect_of_upd {Wp : ℕ} {s : State} {i : Instr} {d X : ℕ} (h : upd Wp s i = some (d, X)) :
    i.effect Wp s = some { s with pc := s.pc + 1, mem := setCell Wp s.mem d X } := by
  cases i <;> simp_all [upd, Instr.effect]

lemma setCell_red (Wp : ℕ) (m : ℕ → ℕ) (a v : ℕ) :
    setCell Wp m a v = setCell Wp m (a % 2 ^ Wp) (v % 2 ^ Wp) := by
  funext b
  simp [setCell]

lemma Rel.setMem' {Wp Pn : ℕ} (hPn : Pn = 2 ^ Wp) {y : List ℕ} {s : State} {σ : Env}
    (h : Rel Pn y s σ) (hM : (σ.arrs "M").length = Pn) {d X : ℕ} (hd : d < Pn) :
    Rel Pn y { s with pc := s.pc + 1, mem := setCell Wp s.mem d X }
      ((σ.setArr "M" d (X % Pn)).setVar "pc" (σ.vars "pc" + 1)) := by
  have := Rel.setMem hPn h hM hd (v := X % Pn) (Nat.mod_lt _ (by rw [hPn]; exact Nat.two_pow_pos _))
  have e : setCell Wp s.mem d X = setCell Wp s.mem d (X % Pn) := by
    rw [setCell_red, setCell_red Wp s.mem d (X % Pn), hPn, Nat.mod_mod]
  rw [e]; exact this

/-- The tail every memory instruction ends in. -/
def tailM : Com := .seq (.store "M" (V "ta") (V "t1")) (.assign "pc" (add (V "pc") (L 1)))

/-- A `Wr` changes no part of the correspondence. -/
lemma Rel.of_wr {Pn : ℕ} {y : List ℕ} {s : State} {σ σ' : Env} {d v : ℕ}
    (h : Rel Pn y s σ) (w : Wr σ σ' d v) : Rel Pn y s σ' := by
  refine ⟨?_, h.input, ?_, ?_, ?_, ?_, ?_, h.mem⟩
  · rw [w.fr "pc" (by decide) (by decide) (by decide)]; exact h.pc
  · rw [w.fr "cur" (by decide) (by decide) (by decide)]; exact h.inp
  · rw [w.fr "cur" (by decide) (by decide) (by decide)]; exact h.cur
  · rw [w.fr "ol" (by decide) (by decide) (by decide), w.arrs]; exact h.ol
  · rw [w.fr "ol" (by decide) (by decide) (by decide), w.arrs]; exact h.olen
  · intro a ha; rw [w.arrs]; exact h.M a ha

theorem tailM_run {Pn : ℕ} {σ : Env} (hP : Pn < B) (hpc : σ.vars "pc" + 1 < B)
    (hd : σ.vars "ta" < Pn) (hv : σ.vars "t1" < Pn) (hL : (σ.arrs "M").length = Pn) :
    ∃ σ', Run B tailM σ σ' 20 ∧
      σ' = (σ.setArr "M" (σ.vars "ta") (σ.vars "t1")).setVar "pc" (σ.vars "pc" + 1) := by
  unfold tailM
  run_vcg
  all_goals try side


/-! ### The context of a step -/

/-- Everything a step of the interpreter is proved under. -/
structure SCtx (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) (s : State) (σ : Env) : Prop where
  rel : Rel Pn y s σ
  cst : Cst Wp Pn P y OL σ
  hPn : Pn = 2 ^ Wp
  bPP : Pn * Pn < B
  b2 : Pn + Pn < B
  bnd : P.length + OL + y.length + Pn + 24 < B
  hpc : σ.vars "pc" ≤ P.length ∨ σ.vars "pc" < Pn
  hyP : ∀ v ∈ y, v < Pn
  hyl : y.length < Pn
  hsm : Small Wp P
  hbud : s.out.length < OL
  run : σ.vars "run" = 1

/-- The scalars a fetch leaves for the instruction `i`. -/
structure Fetched (σ : Env) (i : Instr) : Prop where
  op : σ.vars "op" = opcode i
  ia : σ.vars "ia" = fa i
  ib : σ.vars "ib" = fb i
  ic : σ.vars "ic" = fc i

lemma SCtx.pn_pos {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {s : State} {σ : Env}
    (h : SCtx B Wp Pn P y OL s σ) : 0 < Pn := by rw [h.hPn]; exact Nat.two_pow_pos _

lemma SCtx.pn_lt {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {s : State} {σ : Env}
    (h : SCtx B Wp Pn P y OL s σ) : Pn < B :=
  lt_of_le_of_lt (Nat.le_mul_of_pos_left _ h.pn_pos) h.bPP

/-- The result of a step, as a relation between the states. -/
def Outc (Pn : ℕ) (y : List ℕ) (s : State) : Option State → Env → Prop
  | some s', σ' => Rel Pn y s' σ' ∧ σ'.vars "run" = 1
  | none, σ' => Rel Pn y s σ' ∧ σ'.vars "run" = 0

/-- The block `blk` carries out the instructions with code `k`. -/
def OpSpec (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) (blk : Com) (K k : ℕ) : Prop :=
  ∀ (s : State) (σ : Env) (i : Instr), SCtx B Wp Pn P y OL s σ → i ∈ P → Fetched σ i →
    opcode i = k →
    ∃ σ', Run B blk σ σ' K ∧ Cst Wp Pn P y OL σ' ∧ Outc Pn y s (i.effect Wp s) σ'

lemma Cst.of_wr {Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {σ σ' : Env} {d v : ℕ}
    (h : Cst Wp Pn P y OL σ) (w : Wr σ σ' d v) : Cst Wp Pn P y OL σ' := by
  have hv : ∀ x, x ≠ "ta" → x ≠ "t1" → x ≠ "t2" → σ'.vars x = σ.vars x := w.fr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv "P" (by decide) (by decide) (by decide)]; exact h.Pv
  · rw [hv "wp" (by decide) (by decide) (by decide)]; exact h.wp
  · rw [hv "ylen" (by decide) (by decide) (by decide)]; exact h.ylen
  · rw [hv "plen" (by decide) (by decide) (by decide)]; exact h.plen
  · rw [w.arrs]; exact h.Y
  · rw [w.arrs]; exact h.OP
  · rw [w.arrs]; exact h.XA
  · rw [w.arrs]; exact h.XB
  · rw [w.arrs]; exact h.XC
  · rw [w.arrs]; exact h.Mlen
  · rw [w.arrs]; exact h.Olen

/-- Storing into `M` and moving the counter keeps the constants. -/
lemma Cst.mem_tail {Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {σ : Env} {a v : ℕ}
    (h : Cst Wp Pn P y OL σ) :
    Cst Wp Pn P y OL ((σ.setArr "M" a v).setVar "pc" (σ.vars "pc" + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h.Pv
  · simpa using h.wp
  · simpa using h.ylen
  · simpa using h.plen
  · simpa using h.Y
  · simpa using h.OP
  · simpa using h.XA
  · simpa using h.XB
  · simpa using h.XC
  · simpa using h.Mlen
  · simpa using h.Olen

/-- **The common ending.** A block that computed the destination and the value, and the tail. -/
theorem mem_finish {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {s : State} {σ : Env}
    (hS : SCtx B Wp Pn P y OL s σ) {d X K : ℕ} (hd : d < Pn) (c : Com) {σ1 : Env}
    (hc : Run B c σ σ1 K) (hw : Wr σ σ1 d (X % Pn)) :
    ∃ σ', Run B (.seq c tailM) σ σ' (K + 20) ∧ Cst Wp Pn P y OL σ' ∧
      Outc Pn y s (some { s with pc := s.pc + 1, mem := setCell Wp s.mem d X }) σ' ∧
      (∀ x, x ≠ "ta" → x ≠ "t1" → x ≠ "t2" → x ≠ "pc" → σ'.vars x = σ.vars x) ∧
      (∀ a, a ≠ "M" → σ'.arrs a = σ.arrs a) := by
  have hR1 : Rel Pn y s σ1 := hS.rel.of_wr hw
  have hC1 : Cst Wp Pn P y OL σ1 := hS.cst.of_wr hw
  have hpc : σ1.vars "pc" + 1 < B := by
    have h2 := hw.fr "pc" (by decide) (by decide) (by decide)
    have hb := hS.bnd
    have hp := hS.hpc
    omega
  have hta := hw.ta
  have ht1 := hw.t1
  have hv : σ1.vars "t1" < Pn := by rw [ht1]; exact Nat.mod_lt _ hS.pn_pos
  obtain ⟨σ', hr, he⟩ := tailM_run (B := B) hS.pn_lt hpc (hta ▸ hd) hv hC1.Mlen
  refine ⟨σ', (hc.seq hr).mono le_rfl, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [he]; exact hC1.mem_tail
  · rw [he, hta, ht1]
    exact hR1.setMem' hS.hPn hC1.Mlen hd
  · rw [he]
    simp only [vars_setVar, vars_setArr, String.reduceEq, ↓reduceIte]
    rw [hw.fr "run" (by decide) (by decide) (by decide)]; exact hS.run
  · intro x h1 h2 h3 h4
    rw [he]
    simp only [vars_setVar, vars_setArr, h4, ↓reduceIte, if_false]
    exact hw.fr x h1 h2 h3
  · intro a' ha'
    rw [he]
    simp only [arrs_setVar, arrs_setArr, ha', ↓reduceIte, if_false]
    rw [hw.arrs]


lemma Wr.congr {σ σ' : Env} {d v d' v' : ℕ} (h : Wr σ σ' d v) (hd : d = d') (hv : v = v') :
    Wr σ σ' d' v' := by subst hd; subst hv; exact h

/-- Any block that computes the destination and value of a memory instruction, with the tail. -/
theorem mem_op {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {s : State} {σ : Env}
    (hS : SCtx B Wp Pn P y OL s σ) {i : Instr} {d X K : ℕ} (hu : upd Wp s i = some (d, X))
    (hd : d < Pn) {c : Com} (hc : ∃ σ1, Run B c σ σ1 K ∧ Wr σ σ1 d (X % Pn)) :
    ∃ σ', Run B (.seq c tailM) σ σ' (K + 20) ∧ Cst Wp Pn P y OL σ' ∧
      Outc Pn y s (i.effect Wp s) σ' := by
  obtain ⟨σ1, hr, hw⟩ := hc
  rw [effect_of_upd hu]
  obtain ⟨σ', r, hC, hO, -, -⟩ := mem_finish hS hd c hr hw
  exact ⟨σ', r, hC, hO⟩

/-- The fetched numbers of `i`, as numbers below `Pn`. -/
lemma SCtx.small {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {s : State} {σ : Env}
    (hS : SCtx B Wp Pn P y OL s σ) {i : Instr} (hi : i ∈ P) :
    fa i < Pn ∧ fb i < Pn ∧ fc i < Pn := by
  have := hS.hsm i hi
  rw [hS.hPn]; exact this

theorem opSet (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL (.seq cSet tailM) 30 0 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i a n
  obtain ⟨ha, hb, -⟩ := hS.small hiP
  obtain ⟨-, hia, hib, -⟩ := hF
  simp only [fa, fb] at ha hb hia hib
  have hu : upd Wp s (.set a n) = some (a, n) := rfl
  refine mem_op hS hu ha ?_
  obtain ⟨σ1, r1, w1⟩ := cSet_run (B := B) (Pn := Pn) (σ := σ) hS.pn_lt (by omega) (by omega)
  refine ⟨σ1, r1.mono (by omega), w1.congr hia ?_⟩
  rw [hib, Nat.mod_eq_of_lt hb]


lemma SCtx.ops {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {s : State} {σ : Env}
    (hS : SCtx B Wp Pn P y OL s σ) {i : Instr} (hi : i ∈ P) (hF : Fetched σ i) :
    Ops Pn y s σ := by
  obtain ⟨h1, h2, h3⟩ := hS.small hi
  exact Ops.mk' hS.rel hS.cst (hF.ia ▸ h1) (hF.ib ▸ h2) (hF.ic ▸ h3)

/-- Reducing a number below `Pn` modulo `2 ^ Wp` changes nothing. -/
lemma SCtx.mm {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {s : State} {σ : Env}
    (hS : SCtx B Wp Pn P y OL s σ) {x : ℕ} (hx : x < Pn) : x % 2 ^ Wp = x := by
  rw [← hS.hPn]; exact Nat.mod_eq_of_lt hx

lemma SCtx.mem_lt {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {s : State} {σ : Env}
    (hS : SCtx B Wp Pn P y OL s σ) (a : ℕ) : s.mem a < Pn := hS.rel.mem a

theorem opLoad (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL (.seq cLoad tailM) 50 1 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i a b
  have hia : σ.vars "ia" = a := hF.ia
  have hib : σ.vars "ib" = b := hF.ib
  obtain ⟨ha, hb, -⟩ := hS.small hiP
  replace ha : a < Pn := ha
  replace hb : b < Pn := hb
  have hu : upd Wp s (.load a b) = some (a, s.mem (s.mem (b % 2 ^ Wp) % 2 ^ Wp)) := rfl
  refine mem_op hS hu ha ?_
  obtain ⟨σ1, r1, w1⟩ := cLoad_run (B := B) (hS.ops hiP hF) hS.pn_lt
  refine ⟨σ1, r1.mono (by omega), w1.congr hia ?_⟩
  rw [hib, hS.mm hb, hS.mm (hS.mem_lt b), Nat.mod_eq_of_lt (hS.mem_lt _)]

theorem opStore (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL (.seq cStore tailM) 50 2 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i a b
  have hia : σ.vars "ia" = a := hF.ia
  have hib : σ.vars "ib" = b := hF.ib
  obtain ⟨ha, hb, -⟩ := hS.small hiP
  replace ha : a < Pn := ha
  replace hb : b < Pn := hb
  have hu : upd Wp s (.store a b) = some (s.mem (a % 2 ^ Wp), s.mem (b % 2 ^ Wp)) := rfl
  refine mem_op hS hu (hS.mem_lt _) ?_
  obtain ⟨σ1, r1, w1⟩ := cStore_run (B := B) (hS.ops hiP hF) hS.pn_lt
  refine ⟨σ1, r1.mono (by omega), w1.congr ?_ ?_⟩
  · rw [hia, hS.mm ha]
  · rw [hib, hS.mm hb, Nat.mod_eq_of_lt (hS.mem_lt _)]

theorem opAdd (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL (.seq cAdd tailM) 70 3 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i a b c
  have hia : σ.vars "ia" = a := hF.ia
  have hib : σ.vars "ib" = b := hF.ib
  have hic : σ.vars "ic" = c := hF.ic
  obtain ⟨ha, hb, hc⟩ := hS.small hiP
  replace ha : a < Pn := ha
  replace hb : b < Pn := hb
  replace hc : c < Pn := hc
  have hu : upd Wp s (.add a b c) = some (a, s.mem (b % 2 ^ Wp) + s.mem (c % 2 ^ Wp)) := rfl
  refine mem_op hS hu ha ?_
  obtain ⟨σ1, r1, w1⟩ := cAdd_run (B := B) (hS.ops hiP hF) hS.b2
  refine ⟨σ1, r1.mono (by omega), w1.congr hia ?_⟩
  rw [hib, hic, hS.mm hb, hS.mm hc]

theorem opSub (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL (.seq cSub tailM) 70 4 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i a b c
  have hia : σ.vars "ia" = a := hF.ia
  have hib : σ.vars "ib" = b := hF.ib
  have hic : σ.vars "ic" = c := hF.ic
  obtain ⟨ha, hb, hc⟩ := hS.small hiP
  replace ha : a < Pn := ha
  replace hb : b < Pn := hb
  replace hc : c < Pn := hc
  have hu : upd Wp s (.sub a b c) = some (a, s.mem (b % 2 ^ Wp) - s.mem (c % 2 ^ Wp)) := rfl
  refine mem_op hS hu ha ?_
  obtain ⟨σ1, r1, w1⟩ := cSub_run (B := B) (hS.ops hiP hF) hS.pn_lt
  refine ⟨σ1, r1.mono (by omega), w1.congr hia ?_⟩
  rw [hib, hic, hS.mm hb, hS.mm hc, Nat.mod_eq_of_lt
    (lt_of_le_of_lt (Nat.sub_le _ _) (hS.mem_lt _))]

theorem opMul (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL (.seq cMul tailM) 90 5 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i a b c
  have hia : σ.vars "ia" = a := hF.ia
  have hib : σ.vars "ib" = b := hF.ib
  have hic : σ.vars "ic" = c := hF.ic
  obtain ⟨ha, hb, hc⟩ := hS.small hiP
  replace ha : a < Pn := ha
  replace hb : b < Pn := hb
  replace hc : c < Pn := hc
  have hu : upd Wp s (.mul a b c) = some (a, s.mem (b % 2 ^ Wp) * s.mem (c % 2 ^ Wp)) := rfl
  refine mem_op hS hu ha ?_
  obtain ⟨σ1, r1, w1⟩ := cMul_run (B := B) (hS.ops hiP hF) hS.bPP
  refine ⟨σ1, r1.mono (by omega), w1.congr hia ?_⟩
  rw [hib, hic, hS.mm hb, hS.mm hc]

theorem opDiv (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL (.seq cDiv tailM) 70 6 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i a b c
  have hia : σ.vars "ia" = a := hF.ia
  have hib : σ.vars "ib" = b := hF.ib
  have hic : σ.vars "ic" = c := hF.ic
  obtain ⟨ha, hb, hc⟩ := hS.small hiP
  replace ha : a < Pn := ha
  replace hb : b < Pn := hb
  replace hc : c < Pn := hc
  have hu : upd Wp s (.div a b c) = some (a, s.mem (b % 2 ^ Wp) / s.mem (c % 2 ^ Wp)) := rfl
  refine mem_op hS hu ha ?_
  obtain ⟨σ1, r1, w1⟩ := cDiv_run (B := B) (hS.ops hiP hF) hS.pn_lt
  refine ⟨σ1, r1.mono (by omega), w1.congr hia ?_⟩
  rw [hib, hic, hS.mm hb, hS.mm hc, Nat.mod_eq_of_lt
    (lt_of_le_of_lt (Nat.div_le_self _ _) (hS.mem_lt _))]

theorem opAnd (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL (.seq cAnd tailM) 70 7 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i a b c
  have hia : σ.vars "ia" = a := hF.ia
  have hib : σ.vars "ib" = b := hF.ib
  have hic : σ.vars "ic" = c := hF.ic
  obtain ⟨ha, hb, hc⟩ := hS.small hiP
  replace ha : a < Pn := ha
  replace hb : b < Pn := hb
  replace hc : c < Pn := hc
  have hu : upd Wp s (.and a b c) =
      some (a, Nat.land (s.mem (b % 2 ^ Wp)) (s.mem (c % 2 ^ Wp))) := rfl
  refine mem_op hS hu ha ?_
  obtain ⟨σ1, r1, w1⟩ := cAnd_run (B := B) (hS.ops hiP hF) hS.pn_lt
  refine ⟨σ1, r1.mono (by omega), w1.congr hia ?_⟩
  rw [hib, hic, hS.mm hb, hS.mm hc, Nat.mod_eq_of_lt
    (lt_of_le_of_lt (land_le _ _) (hS.mem_lt _))]

lemma shl_mod (x c Wp : ℕ) (h : Wp ≤ c) : (x * 2 ^ c) % 2 ^ Wp = 0 :=
  have e : 2 ^ c = 2 ^ Wp * 2 ^ (c - Wp) := by
    rw [← Nat.pow_add]; congr 1; omega
  Nat.mod_eq_zero_of_dvd ⟨x * 2 ^ (c - Wp), by rw [e, Nat.mul_left_comm]⟩

theorem opShl (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL (.seq cShl tailM) 100 8 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i a b c
  have hia : σ.vars "ia" = a := hF.ia
  have hib : σ.vars "ib" = b := hF.ib
  have hic : σ.vars "ic" = c := hF.ic
  obtain ⟨ha, hb, hc⟩ := hS.small hiP
  replace ha : a < Pn := ha
  replace hb : b < Pn := hb
  replace hc : c < Pn := hc
  have hu : upd Wp s (.shiftl a b c) = some (a, s.mem (b % 2 ^ Wp) * 2 ^ s.mem (c % 2 ^ Wp)) := rfl
  refine mem_op hS hu ha ?_
  obtain ⟨σ1, r1, w1⟩ := cShl_run (B := B) (hS.ops hiP hF) hS.bPP hS.hPn hS.cst.wp
  refine ⟨σ1, r1.mono (by omega), w1.congr hia ?_⟩
  rw [hib, hic, hS.mm hb, hS.mm hc]
  split_ifs with h
  · rfl
  · rw [hS.hPn, shl_mod _ _ _ (by omega)]


lemma getElem?_getD_lt {Pn : ℕ} {y : List ℕ} (hy : ∀ v ∈ y, v < Pn) (hp : 0 < Pn) (m : ℕ) :
    y[m]?.getD 0 < Pn := by
  by_cases hm : m < y.length
  · rw [List.getElem?_eq_getElem hm]; exact hy _ (List.getElem_mem hm)
  · rw [List.getElem?_eq_none (by omega)]; exact hp

lemma getD_ite (y : List ℕ) (m : ℕ) :
    (if m < y.length then y.getD m 0 else 0) = y[m]?.getD 0 := by
  by_cases hm : m < y.length
  · rw [if_pos hm, List.getD_eq_getElem?_getD]
  · rw [if_neg hm, List.getElem?_eq_none (by omega)]; rfl

theorem opNot (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL (.seq cNot tailM) 70 9 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i a b
  have hia : σ.vars "ia" = a := hF.ia
  have hib : σ.vars "ib" = b := hF.ib
  obtain ⟨ha, hb, -⟩ := hS.small hiP
  replace ha : a < Pn := ha
  replace hb : b < Pn := hb
  have hu : upd Wp s (.not a b) = some (a, 2 ^ Wp - 1 - s.mem (b % 2 ^ Wp)) := rfl
  refine mem_op hS hu ha ?_
  obtain ⟨σ1, r1, w1⟩ := cNot_run (B := B) (hS.ops hiP hF) hS.pn_lt
  refine ⟨σ1, r1.mono (by omega), w1.congr hia ?_⟩
  have hp := hS.pn_pos
  rw [hib, hS.mm hb, ← hS.hPn, Nat.mod_eq_of_lt (by omega)]

theorem opIlen (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL (.seq cIlen tailM) 50 13 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i a
  have hia : σ.vars "ia" = a := hF.ia
  obtain ⟨ha, -, -⟩ := hS.small hiP
  replace ha : a < Pn := ha
  have hu : upd Wp s (.inputLength a) = some (a, s.input.length) := rfl
  refine mem_op hS hu ha ?_
  have hyl := hS.hyl
  have hp := hS.pn_lt
  obtain ⟨σ1, r1, w1⟩ := cIlen_run (B := B) (σ := σ) (y := y) (s := s) hS.cst.ylen (by omega) hp
    (by omega)
  refine ⟨σ1, r1.mono (by omega), w1.congr hia ?_⟩
  rw [hS.rel.input, Nat.mod_eq_of_lt hS.hyl]

theorem opIload (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL (.seq cIload tailM) 70 14 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i a b
  have hia : σ.vars "ia" = a := hF.ia
  have hib : σ.vars "ib" = b := hF.ib
  obtain ⟨ha, hb, -⟩ := hS.small hiP
  replace ha : a < Pn := ha
  replace hb : b < Pn := hb
  have hu : upd Wp s (.inputLoad a b) = some (a, s.input[s.mem (b % 2 ^ Wp) % 2 ^ Wp]?.getD 0) := rfl
  refine mem_op hS hu ha ?_
  have hyl := hS.hyl
  have hp := hS.pn_lt
  obtain ⟨σ1, r1, w1⟩ := cIload_run (B := B) (hS.ops hiP hF) hp hS.cst.Y hS.cst.ylen
    (fun v hv => lt_trans (hS.hyP v hv) hp) (by omega)
  refine ⟨σ1, r1.mono (by omega), w1.congr hia ?_⟩
  rw [hib, hS.mm hb, hS.mm (hS.mem_lt _), hS.rel.input, getD_ite,
    Nat.mod_eq_of_lt (getElem?_getD_lt hS.hyP hS.pn_pos _)]


/-! ### The other instructions -/

lemma Rel.setPc {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (h : Rel Pn y s σ) (v : ℕ) :
    Rel Pn y { s with pc := v } (σ.setVar "pc" v) :=
  ⟨by simp, h.input, by simpa using h.inp, by simpa using h.cur, by simpa using h.ol,
    by simpa using h.olen, by simpa using h.M, h.mem⟩

lemma Rel.setRun {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (h : Rel Pn y s σ) (v : ℕ) :
    Rel Pn y s (σ.setVar "run" v) :=
  ⟨by simpa using h.pc, h.input, by simpa using h.inp, by simpa using h.cur, by simpa using h.ol,
    by simpa using h.olen, by simpa using h.M, h.mem⟩

lemma Cst.setVar' {Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {σ : Env}
    (h : Cst Wp Pn P y OL σ) {x : String} (hx : x ≠ "P" ∧ x ≠ "wp" ∧ x ≠ "ylen" ∧ x ≠ "plen")
    (v : ℕ) : Cst Wp Pn P y OL (σ.setVar x v) := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Ne.symm h1] using h.Pv
  · simpa [Ne.symm h2] using h.wp
  · simpa [Ne.symm h3] using h.ylen
  · simpa [Ne.symm h4] using h.plen
  · simpa using h.Y
  · simpa using h.OP
  · simpa using h.XA
  · simpa using h.XB
  · simpa using h.XC
  · simpa using h.Mlen
  · simpa using h.Olen

theorem opJump (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL (.assign "pc" (V "ia")) 10 10 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i l
  have hia : σ.vars "ia" = l := hF.ia
  obtain ⟨hl, -, -⟩ := hS.small hiP
  replace hl : l < Pn := hl
  have hp := hS.pn_lt
  refine ⟨σ.setVar "pc" l, ?_, hS.cst.setVar' (by decide) l, ?_⟩
  · have := Run.assign (B := B) (σ := σ) (x := "pc") (e := V "ia") (v := l)
      (by rw [← hia]; exact evalB_var (by omega))
    exact this.mono (by simp)
  · show Rel Pn y { s with pc := l } (σ.setVar "pc" l) ∧ (σ.setVar "pc" l).vars "run" = 1
    exact ⟨hS.rel.setPc l, by simpa using hS.run⟩


def bJzero : Com := .ite (.eq (G "M" (V "ia")) (L 0)) (.assign "pc" (V "ib"))
  (.assign "pc" (add (V "pc") (L 1)))

theorem opJzero (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL bJzero 20 11 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i a l
  have hia : σ.vars "ia" = a := hF.ia
  have hib : σ.vars "ib" = l := hF.ib
  obtain ⟨ha, hl, -⟩ := hS.small hiP
  replace ha : a < Pn := ha
  replace hl : l < Pn := hl
  obtain ⟨-, hb', -, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hS.ops hiP hF
  have e3' : (σ.arrs "M").getD (σ.vars "ia") 0 = s.mem a := by rw [e3, hia]
  have hp := hS.pn_lt
  have hb := hS.bnd
  have hpc := hS.hpc
  have hpcs := hS.rel.pc
  have hval : (Instr.jzero a l).effect Wp s = some { s with pc :=
      if (s.mem a = 0) then l else s.pc + 1 } := by
    simp [Instr.effect, hS.mm ha]
  unfold bJzero
  refine (?_ : ∃ σ', Run B _ σ σ' 20 ∧ σ' = σ.setVar "pc" (if (s.mem a = 0) then l else σ.vars "pc" + 1))
    |>.elim fun σ' ⟨hr, he⟩ => ⟨σ', hr, ?_, ?_⟩
  · run_vcg
    all_goals try side
    · rw [if_pos (by omega), hib]
    · rw [if_neg (by omega)]
  · rw [he]; exact hS.cst.setVar' (by decide) _
  · rw [hval, he]
    show Rel Pn y _ _ ∧ _
    refine ⟨?_, ?_⟩
    · have := hS.rel.setPc (if (s.mem a = 0) then l else σ.vars "pc" + 1)
      rw [hpcs] at this ⊢
      exact this
    · simpa using hS.run


def bJeof : Com := .ite (.eq (V "cur") (V "ylen")) (.assign "pc" (V "ia"))
  (.assign "pc" (add (V "pc") (L 1)))

lemma isEmpty_drop (y : List ℕ) (c : ℕ) : (y.drop c).isEmpty = decide (y.length ≤ c) := by
  by_cases h : y.length ≤ c
  · simp [List.drop_eq_nil_of_le h, h]
  · have : y.drop c ≠ [] := fun hh => h (List.drop_eq_nil_iff.mp hh)
    simp [h, List.isEmpty_iff, this]

theorem opJeof (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL bJeof 20 12 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i l
  have hia : σ.vars "ia" = l := hF.ia
  obtain ⟨hl, -, -⟩ := hS.small hiP
  replace hl : l < Pn := hl
  have hp := hS.pn_lt
  have hb := hS.bnd
  have hpc := hS.hpc
  have hpcs := hS.rel.pc
  have hcur := hS.rel.cur
  have hyl := hS.cst.ylen
  have hinp := hS.rel.inp
  have hval : (Instr.jeof l).effect Wp s = some { s with pc :=
      if (y.length ≤ σ.vars "cur") then l else s.pc + 1 } := by
    simp [Instr.effect, hinp, isEmpty_drop]
  unfold bJeof
  refine (?_ : ∃ σ', Run B _ σ σ' 20 ∧
      σ' = σ.setVar "pc" (if (y.length ≤ σ.vars "cur") then l else σ.vars "pc" + 1))
    |>.elim fun σ' ⟨hr, he⟩ => ⟨σ', hr, ?_, ?_⟩
  · run_vcg
    all_goals try side
    · rw [if_pos (by omega), hia]
    · rw [if_neg (by omega)]
  · rw [he]; exact hS.cst.setVar' (by decide) _
  · rw [hval, he]
    show Rel Pn y _ _ ∧ _
    refine ⟨?_, ?_⟩
    · have := hS.rel.setPc (if (y.length ≤ σ.vars "cur") then l else σ.vars "pc" + 1)
      rw [hpcs] at this ⊢
      exact this
    · simpa using hS.run

def bHalt : Com := .assign "run" (L 0)

theorem opHalt (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL bHalt 10 15 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  have hp := hS.pn_lt
  have hb := hS.bnd
  refine ⟨σ.setVar "run" 0, ?_, hS.cst.setVar' (by decide) 0, ?_⟩
  · have := Run.assign (B := B) (σ := σ) (x := "run") (e := L 0) (v := 0) (evalB_lit (by omega))
    exact this.mono (by simp)
  · show Rel Pn y s (σ.setVar "run" 0) ∧ (σ.setVar "run" 0).vars "run" = 0
    exact ⟨hS.rel.setRun 0, by simp⟩


def cRd : Com := .seq (.assign "t1" (G "Y" (V "cur"))) (.assign "ta" (V "ia"))

def bRead : Com := .ite (.lt (V "cur") (V "ylen"))
  (.seq (.seq cRd tailM) (.assign "cur" (add (V "cur") (L 1))))
  (.assign "run" (L 0))

theorem cRd_run {Pn : ℕ} {y : List ℕ} {σ : Env} (hY : σ.arrs "Y" = y)
    (hyB : ∀ v ∈ y, v < B) (hlt : σ.vars "cur" < y.length) (hp : Pn < B)
    (ha : σ.vars "ia" < Pn) (hcB : σ.vars "cur" < B) :
    ∃ σ', Run B cRd σ σ' 10 ∧ Wr σ σ' (σ.vars "ia") (y.getD (σ.vars "cur") 0) := by
  have hg : (σ.arrs "Y").getD (σ.vars "cur") 0 < B := by
    rw [hY, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    exact hyB _ (List.getElem_mem hlt)
  have hL : σ.vars "cur" < (σ.arrs "Y").length := by rw [hY]; exact hlt
  unfold cRd
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; rw [hY]
  · nrm
  · wr_fr

lemma Rel.advance {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (h : Rel Pn y s σ)
    (hlt : σ.vars "cur" < y.length) :
    Rel Pn y { s with inp := y.drop (σ.vars "cur" + 1) } (σ.setVar "cur" (σ.vars "cur" + 1)) :=
  ⟨by simpa using h.pc, h.input, by simp, by simpa using hlt, by simpa using h.ol,
    by simpa using h.olen, by simpa using h.M, h.mem⟩

/-- The state after a `read` of the entry at `c` into cell `a`. -/
def rdState (Wp : ℕ) (y : List ℕ) (s : State) (c a : ℕ) : State :=
  { s with pc := s.pc + 1, mem := setCell Wp s.mem a (y.getD c 0), inp := y.drop (c + 1) }

theorem opRead (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL bRead 60 16 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i a
  have hia : σ.vars "ia" = a := hF.ia
  obtain ⟨ha, -, -⟩ := hS.small hiP
  replace ha : a < Pn := ha
  have hp := hS.pn_lt
  have hb := hS.bnd
  have hpc := hS.hpc
  have hcur := hS.rel.cur
  have hyl := hS.cst.ylen
  have hinp := hS.rel.inp
  unfold bRead
  by_cases hc : σ.vars "cur" < y.length
  · have hval : (Instr.read a).effect Wp s = some (rdState Wp y s (σ.vars "cur") a) := by
      have hg : y.getD (σ.vars "cur") 0 = y[σ.vars "cur"] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]; rfl
      simp only [Instr.effect, hinp, List.drop_eq_getElem_cons hc, List.head?_cons,
        List.tail_cons, Option.map_some, rdState, hg]
    have hyv : y.getD (σ.vars "cur") 0 < Pn := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]
      exact hS.hyP _ (List.getElem_mem hc)
    obtain ⟨σ1, r1, w1⟩ := cRd_run (B := B) (Pn := Pn) hS.cst.Y
      (fun v hv => lt_trans (hS.hyP v hv) hp) hc hp (by omega) (by omega)
    obtain ⟨σ2, r2, hC2, ⟨hR2, hrun2⟩, hfv, hfa⟩ := mem_finish hS (d := a)
      (X := y.getD (σ.vars "cur") 0) ha cRd r1 (w1.congr hia (by rw [Nat.mod_eq_of_lt hyv]))
    have hcur2 : σ2.vars "cur" = σ.vars "cur" := hfv "cur" (by decide) (by decide) (by decide)
      (by decide)
    have hcond : (Cond.lt (V "cur") (V "ylen")).evalB B σ = some true :=
      RunStep.cond_lt_true B σ (V "cur") (V "ylen") _ _ (evalB_var (by omega))
        (evalB_var (by omega)) (by rw [hyl]; exact hc)
    have r3 : Run B (.assign "cur" (add (V "cur") (L 1))) σ2
        (σ2.setVar "cur" (σ2.vars "cur" + 1)) 5 :=
      (Run.assign (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))).mono
        (by simp)
    refine ⟨σ2.setVar "cur" (σ2.vars "cur" + 1), ?_, hC2.setVar' (by decide) _, ?_⟩
    · exact (Run.ite_true hcond (r2.seq r3)).mono (by simp)
    · rw [hval]
      refine ⟨?_, by simpa using hrun2⟩
      have := hR2.advance (by omega)
      rw [hcur2] at this ⊢
      simpa [rdState] using this
  · have hc' : ¬ σ.vars "cur" < y.length := hc
    have hval : (Instr.read a).effect Wp s = none := by
      have : y.length ≤ σ.vars "cur" := by omega
      simp [Instr.effect, hinp, List.drop_eq_nil_of_le this]
    have hcond : (Cond.lt (V "cur") (V "ylen")).evalB B σ = some false :=
      RunStep.cond_lt_false B σ (V "cur") (V "ylen") _ _ (evalB_var (by omega))
        (evalB_var (by omega)) (by rw [hyl]; exact hc)
    refine ⟨σ.setVar "run" 0, ?_, hS.cst.setVar' (by decide) 0, ?_⟩
    · exact (Run.ite_false hcond (Run.assign (evalB_lit (by omega)))).mono (by simp)
    · rw [hval]
      exact ⟨hS.rel.setRun 0, by simp⟩


def bWrite : Com := .seq (.store "O" (V "ol") (G "M" (V "ia")))
  (.seq (.assign "ol" (add (V "ol") (L 1))) (.assign "pc" (add (V "pc") (L 1))))

lemma take_set_snoc (l : List ℕ) (i v : ℕ) (h : i < l.length) :
    (l.set i v).take (i + 1) = l.take i ++ [v] := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_take, List.getElem?_append, List.getElem?_set, List.length_take,
    List.getElem?_singleton]
  by_cases hj : j < i + 1
  · by_cases hji : j < i
    · simp [hj, hji, Nat.ne_of_gt hji, Nat.min_eq_left h.le]
    · have : j = i := by omega
      subst this
      simp [h]
      omega
  · have : ¬ j < i := by omega
    simp [hj, this]; omega

/-- The state after a `write` of cell `a`. -/
def wrState (s : State) (a : ℕ) : State := { s with pc := s.pc + 1, out := s.out ++ [s.mem a] }

theorem opWrite (B Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) :
    OpSpec B Wp Pn P y OL bWrite 30 17 := by
  intro s σ i hS hiP hF hk
  cases i <;> simp [opcode] at hk
  rename_i a
  have hia : σ.vars "ia" = a := hF.ia
  obtain ⟨ha, -, -⟩ := hS.small hiP
  replace ha : a < Pn := ha
  obtain ⟨-, -, -, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hS.ops hiP hF
  have e3' : (σ.arrs "M").getD (σ.vars "ia") 0 = s.mem a := by rw [e3, hia]
  have hp := hS.pn_lt
  have hb := hS.bnd
  have hpc := hS.hpc
  have hpcs := hS.rel.pc
  have hol := hS.rel.ol
  have holen := hS.rel.olen
  have hOl := hS.cst.Olen
  have hbud := hS.hbud
  have hlen : (s.out).length = σ.vars "ol" := by
    rw [hol, List.length_take]; omega
  have hlt : σ.vars "ol" < (σ.arrs "O").length := by omega
  have hval : (Instr.write a).effect Wp s = some (wrState s a) := by
    simp [Instr.effect, hS.mm ha, hS.mm (hS.mem_lt a), wrState]
  unfold bWrite
  have hM : (σ.arrs "M").length = Pn := hS.cst.Mlen
  refine (?_ : ∃ σ', Run B _ σ σ' 30 ∧ σ' = ((σ.setArr "O" (σ.vars "ol") (s.mem a)).setVar "ol"
      (σ.vars "ol" + 1)).setVar "pc" (σ.vars "pc" + 1))
    |>.elim fun σ' ⟨hr, he⟩ => ⟨σ', hr, ?_, ?_⟩
  · run_vcg
    all_goals try side
    all_goals try (nrm; omega)
    all_goals try (nrm; rw [e3'])
  · rw [he]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hS.cst.Pv
    · simpa using hS.cst.wp
    · simpa using hS.cst.ylen
    · simpa using hS.cst.plen
    · simpa using hS.cst.Y
    · simpa using hS.cst.OP
    · simpa using hS.cst.XA
    · simpa using hS.cst.XB
    · simpa using hS.cst.XC
    · simpa using hS.cst.Mlen
    · simpa using hS.cst.Olen
  · rw [hval, he]
    simp only [Outc, wrState]
    refine ⟨⟨?_, hS.rel.input, ?_, ?_, ?_, ?_, ?_, hS.rel.mem⟩, ?_⟩
    · simpa using hpcs
    · simpa using hS.rel.inp
    · simpa using hS.rel.cur
    · simp only [arrs_setVar, arrs_setArr, vars_setVar, vars_setArr, ↓reduceIte, String.reduceEq,
        eq_self]
      rw [take_set_snoc _ _ _ hlt, ← hol]
    · simp; omega
    · simpa using hS.rel.M
    · simpa using hS.run


/-! ### One step: fetch and dispatch -/

lemma Rel.setVarN {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (h : Rel Pn y s σ) {x : String}
    (h1 : x ≠ "pc") (h2 : x ≠ "cur") (h3 : x ≠ "ol") (v : ℕ) : Rel Pn y s (σ.setVar x v) :=
  ⟨by simpa [Ne.symm h1] using h.pc, h.input, by simpa [Ne.symm h2] using h.inp,
    by simpa [Ne.symm h2] using h.cur, by simpa [Ne.symm h3] using h.ol,
    by simpa [Ne.symm h3] using h.olen, by simpa using h.M, h.mem⟩

lemma SCtx.setVarN {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {s : State} {σ : Env}
    (h : SCtx B Wp Pn P y OL s σ) {x : String}
    (hx : x ≠ "pc" ∧ x ≠ "cur" ∧ x ≠ "ol" ∧ x ≠ "P" ∧ x ≠ "wp" ∧ x ≠ "ylen" ∧ x ≠ "plen" ∧
      x ≠ "run") (v : ℕ) : SCtx B Wp Pn P y OL s (σ.setVar x v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hx
  refine ⟨h.rel.setVarN h1 h2 h3 v, h.cst.setVar' ⟨h4, h5, h6, h7⟩ v, h.hPn, h.bPP, h.b2, h.bnd,
    ?_, h.hyP, h.hyl, h.hsm, h.hbud, ?_⟩
  · simpa [Ne.symm h1] using h.hpc
  · simpa [Ne.symm h8] using h.run

def fetch : Com := .seq (.assign "op" (G "OP" (V "pc"))) (.seq (.assign "ia" (G "XA" (V "pc")))
  (.seq (.assign "ib" (G "XB" (V "pc"))) (.assign "ic" (G "XC" (V "pc")))))

/-- The instruction at the program counter. -/
lemma SCtx.fetch_instr {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {s : State} {σ : Env}
    (h : SCtx B Wp Pn P y OL s σ) (hlt : σ.vars "pc" < P.length) :
    ∃ i, P[σ.vars "pc"]? = some i ∧ i ∈ P ∧ (σ.arrs "OP").getD (σ.vars "pc") 0 = opcode i ∧
      (σ.arrs "XA").getD (σ.vars "pc") 0 = fa i ∧ (σ.arrs "XB").getD (σ.vars "pc") 0 = fb i ∧
      (σ.arrs "XC").getD (σ.vars "pc") 0 = fc i ∧ σ.vars "pc" < (σ.arrs "OP").length ∧
      σ.vars "pc" < (σ.arrs "XA").length ∧ σ.vars "pc" < (σ.arrs "XB").length ∧
      σ.vars "pc" < (σ.arrs "XC").length := by
  have hi : P[σ.vars "pc"]? = some P[σ.vars "pc"] := List.getElem?_eq_getElem hlt
  refine ⟨P[σ.vars "pc"], hi, List.getElem_mem hlt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.cst.OP]; simp [List.getD_eq_getElem?_getD, hlt]
  · rw [h.cst.XA]; simp [List.getD_eq_getElem?_getD, hlt]
  · rw [h.cst.XB]; simp [List.getD_eq_getElem?_getD, hlt]
  · rw [h.cst.XC]; simp [List.getD_eq_getElem?_getD, hlt]
  · rw [h.cst.OP]; simpa using hlt
  · rw [h.cst.XA]; simpa using hlt
  · rw [h.cst.XB]; simpa using hlt
  · rw [h.cst.XC]; simpa using hlt


lemma opcode_le (i : Instr) : opcode i ≤ 17 := by cases i <;> simp [opcode]

theorem fetch_run {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {s : State} {σ : Env}
    (hS : SCtx B Wp Pn P y OL s σ) (hlt : σ.vars "pc" < P.length) :
    ∃ σ1, Run B fetch σ σ1 20 ∧ ∃ i, i ∈ P ∧ P[σ.vars "pc"]? = some i ∧ Fetched σ1 i ∧
      SCtx B Wp Pn P y OL s σ1 := by
  obtain ⟨i, hi, hiP, e1, e2, e3, e4, l1, l2, l3, l4⟩ := hS.fetch_instr hlt
  have hb := hS.bnd
  have hp := hS.pn_lt
  obtain ⟨h1, h2, h3⟩ := hS.small hiP
  have hop := opcode_le i
  have f1 : (σ.arrs "OP").getD (σ.vars "pc") 0 < B := by omega
  have f2 : (σ.arrs "XA").getD (σ.vars "pc") 0 < B := by omega
  have f3 : (σ.arrs "XB").getD (σ.vars "pc") 0 < B := by omega
  have f4 : (σ.arrs "XC").getD (σ.vars "pc") 0 < B := by omega
  have hpcB : σ.vars "pc" < B := by have := hS.hpc; omega
  unfold fetch
  run_vcg
  all_goals try side
  refine ⟨i, hiP, hi, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · nrm; exact e1
  · nrm; exact e2
  · nrm; exact e3
  · nrm; exact e4
  · exact (((hS.setVarN (x := "op") (by decide) _).setVarN (x := "ia") (by decide) _).setVarN
      (x := "ib") (by decide) _).setVarN (x := "ic") (by decide) _


/-- A chain of tests on the opcode. -/
def mkD : List (ℕ × Com) → Com
  | [] => .skip
  | (k, c) :: r => .ite (.eq (V "op") (L k)) c (mkD r)

/-- The blocks of the instructions, by opcode. -/
def dispList : List (ℕ × Com) :=
  [(0, .seq cSet tailM), (1, .seq cLoad tailM), (2, .seq cStore tailM), (3, .seq cAdd tailM),
   (4, .seq cSub tailM), (5, .seq cMul tailM), (6, .seq cDiv tailM), (7, .seq cAnd tailM),
   (8, .seq cShl tailM), (9, .seq cNot tailM), (10, .assign "pc" (V "ia")), (11, bJzero),
   (12, bJeof), (13, .seq cIlen tailM), (14, .seq cIload tailM), (15, bHalt), (16, bRead),
   (17, bWrite)]

theorem mkD_run {l : List (ℕ × Com)} (hn : (l.map Prod.fst).Nodup) {k : ℕ} {c : Com}
    (hm : (k, c) ∈ l) {σ σ' : Env} {K : ℕ} (hk : σ.vars "op" = k) (hkB : ∀ q ∈ l, q.1 < B)
    (hr : Run B c σ σ' K) : Run B (mkD l) σ σ' (K + 4 * l.length) := by
  induction l with
  | nil => simp at hm
  | cons q r ih =>
    obtain ⟨k', c'⟩ := q
    have hk' : k' < B := hkB _ (List.mem_cons_self ..)
    have hkB' : k < B := by
      rcases List.mem_cons.1 hm with h1 | h1
      · rw [Prod.mk.injEq] at h1; rw [h1.1]; exact hk'
      · exact hkB _ (List.mem_cons_of_mem _ h1)
    simp only [mkD, List.length_cons]
    by_cases hkk : k = k'
    · have hcc : c = c' := by
        rcases List.mem_cons.1 hm with h1 | h1
        · rw [Prod.mk.injEq] at h1; exact h1.2
        · exfalso
          have : k ∈ r.map Prod.fst := List.mem_map.2 ⟨(k, c), h1, rfl⟩
          simp only [List.map_cons, List.nodup_cons] at hn
          exact hn.1 (hkk ▸ this)
      subst hcc; subst hkk
      have hc : (Cond.eq (V "op") (L k)).evalB B σ = some true :=
        RunStep.cond_eq_true B σ (V "op") (L k) _ _ (evalB_var (by omega)) (evalB_lit hk') hk
      exact (Run.ite_true hc hr).mono (by simp; omega)
    · have hmr : (k, c) ∈ r := by
        rcases List.mem_cons.1 hm with h1 | h1
        · rw [Prod.mk.injEq] at h1; exact absurd h1.1 hkk
        · exact h1
      have hc : (Cond.eq (V "op") (L k')).evalB B σ = some false :=
        RunStep.cond_eq_false B σ (V "op") (L k') _ _ (evalB_var (by omega)) (evalB_lit hk') (by
          rw [hk]; exact hkk)
      simp only [List.map_cons, List.nodup_cons] at hn
      have := ih hn.2 hmr (fun q hq => hkB q (List.mem_cons_of_mem _ hq))
      exact (Run.ite_false hc this).mono (by simp; omega)


lemma dispList_keys : (dispList.map Prod.fst).Nodup := by decide

lemma dispList_len : dispList.length = 18 := rfl

theorem disp_of_spec {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {s : State} {σ : Env}
    (hS : SCtx B Wp Pn P y OL s σ) {i : Instr} (hiP : i ∈ P) (hF : Fetched σ i)
    {blk : Com} {K k : ℕ} (hs : OpSpec B Wp Pn P y OL blk K k) (hm : (k, blk) ∈ dispList)
    (hK : K + 72 ≤ 200) (hk : opcode i = k) :
    ∃ σ', Run B (mkD dispList) σ σ' 200 ∧ Cst Wp Pn P y OL σ' ∧
      Outc Pn y s (i.effect Wp s) σ' := by
  have hb := hS.bnd
  have hkB : ∀ q ∈ dispList, q.1 < B := by
    intro q hq
    simp only [dispList, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  obtain ⟨σ', r, hC, hO⟩ := hs s σ i hS hiP hF hk
  refine ⟨σ', ?_, hC, hO⟩
  have := mkD_run (B := B) dispList_keys hm (hF.op.trans hk) hkB r
  exact this.mono (by rw [dispList_len]; omega)

theorem dispatch_run {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {s : State} {σ : Env}
    (hS : SCtx B Wp Pn P y OL s σ) {i : Instr} (hiP : i ∈ P) (hF : Fetched σ i) :
    ∃ σ', Run B (mkD dispList) σ σ' 200 ∧ Cst Wp Pn P y OL σ' ∧
      Outc Pn y s (i.effect Wp s) σ' := by
  cases i with
  | set a n => exact disp_of_spec hS hiP hF (opSet B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | load a b => exact disp_of_spec hS hiP hF (opLoad B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | store a b => exact disp_of_spec hS hiP hF (opStore B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | add a b c => exact disp_of_spec hS hiP hF (opAdd B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | sub a b c => exact disp_of_spec hS hiP hF (opSub B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | mul a b c => exact disp_of_spec hS hiP hF (opMul B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | div a b c => exact disp_of_spec hS hiP hF (opDiv B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | and a b c => exact disp_of_spec hS hiP hF (opAnd B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | shiftl a b c => exact disp_of_spec hS hiP hF (opShl B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | not a b => exact disp_of_spec hS hiP hF (opNot B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | jump l => exact disp_of_spec hS hiP hF (opJump B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | jzero a l => exact disp_of_spec hS hiP hF (opJzero B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | jeof l => exact disp_of_spec hS hiP hF (opJeof B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | inputLength a => exact disp_of_spec hS hiP hF (opIlen B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | inputLoad a b => exact disp_of_spec hS hiP hF (opIload B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | halt => exact disp_of_spec hS hiP hF (opHalt B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | read a => exact disp_of_spec hS hiP hF (opRead B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl
  | write a => exact disp_of_spec hS hiP hF (opWrite B Wp Pn P y OL) (by simp [dispList]) (by omega) rfl


/-- One step of the machine: fetch, then dispatch; or stop when the counter is past the code. -/
def stepCom : Com := .ite (.lt (V "pc") (V "plen")) (.seq fetch (mkD dispList))
  (.assign "run" (L 0))

theorem step_run {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {s : State} {σ : Env}
    (hS : SCtx B Wp Pn P y OL s σ) :
    ∃ σ', Run B stepCom σ σ' 240 ∧ Cst Wp Pn P y OL σ' ∧
      Outc Pn y s (step Wp P s) σ' := by
  have hb := hS.bnd
  have hp := hS.pn_lt
  have hpcs := hS.rel.pc
  have hpl := hS.cst.plen
  have hpc := hS.hpc
  unfold stepCom
  by_cases hlt : σ.vars "pc" < P.length
  · obtain ⟨σ1, r1, i, hiP, hi, hF, hS1⟩ := fetch_run hS hlt
    obtain ⟨σ2, r2, hC2, hO2⟩ := dispatch_run hS1 hiP hF
    have hcond : (Cond.lt (V "pc") (V "plen")).evalB B σ = some true :=
      RunStep.cond_lt_true B σ (V "pc") (V "plen") _ _ (evalB_var (by omega))
        (evalB_var (by omega)) (by rw [hpl]; exact hlt)
    have hstep : step Wp P s = i.effect Wp s := by
      rw [step, ← hpcs, hi]; rfl
    refine ⟨σ2, (Run.ite_true hcond (r1.seq r2)).mono (by simp), hC2, ?_⟩
    rw [hstep]; exact hO2
  · have hcond : (Cond.lt (V "pc") (V "plen")).evalB B σ = some false :=
      RunStep.cond_lt_false B σ (V "pc") (V "plen") _ _ (evalB_var (by omega))
        (evalB_var (by omega)) (by rw [hpl]; exact hlt)
    have hstep : step Wp P s = none := by
      rw [step, ← hpcs, List.getElem?_eq_none (by omega)]; rfl
    refine ⟨σ.setVar "run" 0, ?_, hS.cst.setVar' (by decide) 0, ?_⟩
    · exact (Run.ite_false hcond (Run.assign (evalB_lit (by omega)))).mono (by simp)
    · rw [hstep]
      exact ⟨hS.rel.setRun 0, by simp⟩

end Lax117284Proofs.Machine.TwRam

end

/-! ### `Lax117284Proofs.Machine.TwRamLoop` -/

section
/-!
The loop of the interpreter: it runs the machine to its halt, at a cost of a constant per step.
-/

namespace Lax117284Proofs.Machine.TwRam

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

variable {B : ℕ}

/-- A step appends at most one number to the output. -/
lemma step_out_le {Wp : ℕ} {P : Program} {s s' : State} (h : step Wp P s = some s') :
    s'.out.length ≤ s.out.length + 1 := by
  unfold step at h
  cases hi : P[s.pc]? with
  | none => rw [hi] at h; simp at h
  | some i =>
    rw [hi] at h
    simp only [Option.bind_some] at h
    cases i <;> simp only [Instr.effect, Option.some.injEq] at h <;>
      first
      | (subst h; simp)
      | (cases hh : s.inp.head? <;> simp_all [Option.map] <;> (subst h; simp))
      | skip


/-- A step is taken only inside the code, and lands on the next instruction or on a label. -/
lemma step_pc {Wp Pn : ℕ} {P : Program} (hsm : Small Wp P) (hPn : Pn = 2 ^ Wp) {s s' : State}
    (h : step Wp P s = some s') :
    s.pc < P.length ∧ (s'.pc = s.pc + 1 ∨ s'.pc < Pn) := by
  unfold step at h
  cases hi : P[s.pc]? with
  | none => rw [hi] at h; simp at h
  | some i =>
    rw [hi] at h
    simp only [Option.bind_some] at h
    have hlt : s.pc < P.length := (List.getElem?_eq_some_iff.1 hi).1
    have hmem : i ∈ P := List.mem_of_getElem? hi
    obtain ⟨h1, h2, h3⟩ := hsm i hmem
    refine ⟨hlt, ?_⟩
    rw [← hPn] at h1 h2 h3
    cases i <;> simp only [Instr.effect, Option.some.injEq, fa, fb, fc] at h h1 h2 h3 <;>
      first
      | (subst h; dsimp only; split_ifs <;> first | (left; rfl) | (right; omega))
      | (subst h; dsimp only; first | (left; rfl) | (right; omega))
      | (subst h; simp; done)
      | (cases hh : s.inp.head? <;> simp_all [Option.map] <;> (subst h; simp))


theorem Run.while_step {B : ℕ} {b : Cond} {c : Com} {σ σ1 σ2 : Env} {K1 K2 : ℕ}
    (hb : b.evalB B σ = some true) (h1 : Run B c σ σ1 K1) (h2 : Run B (.while b c) σ1 σ2 K2) :
    Run B (.while b c) σ σ2 (1 + b.size + K1 + K2) := by
  obtain ⟨k1, hk1, hbs1⟩ := h1
  obtain ⟨k2, hk2, hbs2⟩ := h2
  exact ⟨1 + b.size + k1 + k2, by omega, .while_true hb hbs1 hbs2⟩

/-- The interpreter's loop: step while the machine runs. -/
def loopCom : Com := .while (.eq (V "run") (L 1)) stepCom

theorem loop_aux {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} :
    ∀ (n : ℕ) (s : State) (σ : Env) (send : State), SCtx B Wp Pn P y OL s σ →
      s.out.length + n < OL → run Wp P n s = some send → step Wp P send = none →
      ∃ σ', Run B loopCom σ σ' (250 * (n + 1)) ∧ Cst Wp Pn P y OL σ' ∧ Rel Pn y send σ' ∧
        σ'.vars "run" = 0 := by
  intro n
  induction n with
  | zero =>
    intro s σ send hS hbud hrun hstep
    simp only [run, Option.some.injEq] at hrun
    subst hrun
    have hb := hS.bnd
    have hcond : (Cond.eq (V "run") (L 1)).evalB B σ = some true :=
      RunStep.cond_eq_true B σ (V "run") (L 1) _ _ (evalB_var (by rw [hS.run]; omega))
        (evalB_lit (by omega)) hS.run
    obtain ⟨σ1, r1, hC1, hO1⟩ := step_run hS
    rw [hstep] at hO1
    obtain ⟨hR1, hrun1⟩ := hO1
    have hcond' : (Cond.eq (V "run") (L 1)).evalB B σ1 = some false :=
      RunStep.cond_eq_false B σ1 (V "run") (L 1) _ _ (evalB_var (by rw [hrun1]; omega))
        (evalB_lit (by omega)) (by rw [hrun1]; omega)
    refine ⟨σ1, ?_, hC1, hR1, hrun1⟩
    have := Run.while_step (c := stepCom) hcond r1 (Run.while_false hcond')
    exact this.mono (by simp)
  | succ n ih =>
    intro s σ send hS hbud hrun hstep
    have hb := hS.bnd
    simp only [run] at hrun
    cases hs : step Wp P s with
    | none => rw [hs] at hrun; simp at hrun
    | some s' =>
      rw [hs] at hrun
      simp only [Option.bind_some] at hrun
      have hcond : (Cond.eq (V "run") (L 1)).evalB B σ = some true :=
        RunStep.cond_eq_true B σ (V "run") (L 1) _ _ (evalB_var (by rw [hS.run]; omega))
          (evalB_lit (by omega)) hS.run
      obtain ⟨σ1, r1, hC1, hO1⟩ := step_run hS
      rw [hs] at hO1
      obtain ⟨hR1, hrun1⟩ := hO1
      have hout := step_out_le hs
      obtain ⟨-, hpc'⟩ := step_pc hS.hsm hS.hPn hs
      have hS1 : SCtx B Wp Pn P y OL s' σ1 :=
        ⟨hR1, hC1, hS.hPn, hS.bPP, hS.b2, hS.bnd, by
          rw [hR1.pc]
          rcases hpc' with h | h
          · left; have := (step_pc hS.hsm hS.hPn hs).1; omega
          · right; exact h, hS.hyP, hS.hyl, hS.hsm, by omega, hrun1⟩
      obtain ⟨σ', r2, hC', hR', hrun'⟩ := ih s' σ1 send hS1 (by omega) hrun hstep
      refine ⟨σ', ?_, hC', hR', hrun'⟩
      have := Run.while_step (c := stepCom) hcond r1 r2
      exact this.mono (by simp; omega)


/-- The initial environment corresponds to the initial state. -/
structure InitEnv (Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) (σ : Env) : Prop where
  cst : Cst Wp Pn P y OL σ
  pc : σ.vars "pc" = 0
  cur : σ.vars "cur" = 0
  ol : σ.vars "ol" = 0
  run : σ.vars "run" = 1
  M : σ.arrs "M" = List.replicate Pn 0

theorem InitEnv.sctx {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {σ : Env}
    (h : InitEnv Wp Pn P y OL σ) (hPn : Pn = 2 ^ Wp) (bPP : Pn * Pn < B) (b2 : Pn + Pn < B)
    (bnd : P.length + OL + y.length + Pn + 24 < B) (hyP : ∀ v ∈ y, v < Pn) (hyl : y.length < Pn)
    (hsm : Small Wp P) (hOL : 0 < OL) : SCtx B Wp Pn P y OL (initState y) σ := by
  have hpos : 0 < Pn := by rw [hPn]; exact Nat.two_pow_pos _
  refine ⟨⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩, h.cst, hPn, bPP, b2, bnd, Or.inl (by rw [h.pc]; omega),
    hyP, hyl, hsm, ?_, h.run⟩
  · simpa [initState] using h.pc
  · simp [initState, h.cur]
  · simp [h.cur]
  · simp [initState, h.ol]
  · rw [h.ol]; omega
  · intro a ha; rw [h.M]; simp [initState, List.getD_eq_getElem?_getD, List.getElem?_replicate, ha]
  · intro a; simpa [initState] using hpos
  · simpa [initState] using hOL

/-- **The interpreter.** Started on the initial environment, the loop runs to the end of the run
and leaves the output of the machine in the array `O`. -/
theorem interp_run {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {σ : Env} {z : List ℕ} {t : ℕ}
    (hS : SCtx B Wp Pn P y OL (initState y) σ) (hRuns : RunsTo Wp P y z t) (hOL : t < OL) :
    ∃ σ', Run B loopCom σ σ' (250 * (t + 1)) ∧ Cst Wp Pn P y OL σ' ∧ σ'.vars "run" = 0 ∧
      z = (σ'.arrs "O").take (σ'.vars "ol") := by
  obtain ⟨k, sk, hrun, hstep, hout, ht⟩ := hRuns
  have hk : k ≤ t := by rw [ht]; omega
  obtain ⟨σ', r, hC, hR, hrun'⟩ := loop_aux k (initState y) σ sk hS (by simp [initState]; omega) hrun hstep
  refine ⟨σ', r.mono (Nat.mul_le_mul_left _ (by omega)), hC, hrun', ?_⟩
  rw [← hout]; exact hR.ol

end Lax117284Proofs.Machine.TwRam

end

/-! ### `Lax117284Proofs.Machine.TwSetup1` -/

section
/-!
Facts about a run of a machine program that the setup of the decomposition step needs: every
number it writes is a word.
-/

namespace Lax117284Proofs.Machine.TwSetup

open Lax808846.Ram

lemma step_out_lt {w : ℕ} {p : Program} {s s' : State} (h : step w p s = some s')
    (ho : ∀ v ∈ s.out, v < 2 ^ w) : ∀ v ∈ s'.out, v < 2 ^ w := by
  unfold step at h
  cases hi : p[s.pc]? with
  | none => rw [hi] at h; simp at h
  | some i =>
    rw [hi] at h
    simp only [Option.bind_some] at h
    have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
    cases i <;> simp only [Instr.effect, Option.some.injEq] at h <;>
      first
      | (simp at h; done)
      | (subst h; exact ho)
      | (subst h; intro v hv
         simp only [List.mem_append, List.mem_singleton] at hv
         rcases hv with hv | rfl
         · exact ho v hv
         · exact Nat.mod_lt _ hpos)
      | (cases hh : s.inp.head? <;> simp only [hh, Option.map] at h
         · exact absurd h (by simp)
         · rename_i v
           simp only [Option.some.injEq] at h
           subst h; exact ho)
      | skip

lemma run_out_lt {w : ℕ} {p : Program} : ∀ (n : ℕ) (s s' : State),
    run w p n s = some s' → (∀ v ∈ s.out, v < 2 ^ w) → ∀ v ∈ s'.out, v < 2 ^ w
  | 0, s, s', h, ho => by
    simp only [run, Option.some.injEq] at h; subst h; exact ho
  | n + 1, s, s', h, ho => by
    simp only [run] at h
    cases hs : step w p s with
    | none => rw [hs] at h; simp at h
    | some s1 =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      exact run_out_lt n s1 s' h (step_out_lt hs ho)

/-- **Every number a run writes is a word.** -/
theorem RunsTo.out_lt {w : ℕ} {p : Program} {x y : List ℕ} {t : ℕ} (h : RunsTo w p x y t) :
    ∀ v ∈ y, v < 2 ^ w := by
  obtain ⟨k, s, hrun, -, hout, -⟩ := h
  rw [← hout]
  exact run_out_lt k _ s hrun (by simp [initState])

end Lax117284Proofs.Machine.TwSetup

end
