import Lax117284Proofs.Treewidth.Fun.VMDefs
import Lax808846Proofs.Transfer
import Lax808846Proofs.Tactic

/-!
# WP V2 (1): the IMP+ interpreter of the VM — layout, blocks, abstraction relation

The interpreter is one IMP+ command `vmLoop = while run = 1 do (fetch; dispatch)`.  Its data:

*Scalars* `pc sp rp hp B run op oa t1 t2`.
*Arrays* (all of length `W + 1`, where `W` is the word bound of `StepsB`):

| array          | contents                                                                                |
|----------------|-----------------------------------------------------------------------------------------|
| `OP`, `OA`     | opcode (`opc`) and operand (`opa`) of `P.code i`, `i ≤ W`   (`halt` = `(0,0)`: unloaded cells are `halt`) |
| `FT`           | `P.ft f` for `f ≤ W`                                                                    |
| `STK`          | value stack, **bottom first**: `STK[0..sp)` = `s.stk.reverse`, `sp = s.stk.length`         |
| `RETPC`,`RETH` | return stack, bottom first, `rp = s.ret.length`                                          |
| `HA`,`HB`      | heap: `HA[p]`, `HB[p]` are the car/cdr of cell `p`, `hp = s.heap.length`; cells `≥ hp` are garbage |

`B` holds the VM's tag bound `P.B`.  Every operand of the code must be `< Bi` (`Cst.opa_lt`): the fetch reads
`OA[pc]` into a scalar, and every value of an IMP+ run must stay below the bound `Bi ≥ W + 18`.  `Abs P W s σ` is the (garbage-tolerant) representation relation of the
dynamic part; `Cst P W Bi σ` the never-changing part.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-! ## Opcodes -/

/-- Opcode of an instruction; `halt = 0`, so unloaded (all-zero) cells of the code arrays are `halt`. -/
def opc : Instr → ℕ
  | .halt => 0 | .lit _ => 1 | .var _ => 2 | .add => 3 | .sub => 4 | .mul => 5 | .lt => 6 | .eq => 7
  | .cons => 8 | .fst => 9 | .snd => 10 | .isNat => 11 | .jz _ => 12 | .jmp _ => 13 | .slide => 14
  | .call _ => 15 | .ret => 16

/-- Operand of an instruction (`0` if none). -/
def opa : Instr → ℕ
  | .lit n => n | .var i => i | .jz k => k | .jmp k => k | .call n => n | _ => 0

/-! ## Prefix representation of a list by an array -/

/-- The list `l` is stored at the beginning of the array `a` (later cells are unconstrained). -/
def Pfx (l a : List ℕ) : Prop := ∀ j, j < l.length → a[j]? = l[j]?

theorem Pfx.nil (a : List ℕ) : Pfx [] a := fun j hj => by simp at hj

theorem Pfx.left {l m a : List ℕ} (h : Pfx (l ++ m) a) : Pfx l a := by
  intro j hj
  have := h j (by simp; omega)
  rwa [List.getElem?_append_left hj] at this

theorem Pfx.take {l a : List ℕ} (h : Pfx l a) (n : ℕ) : Pfx (l.take n) a := by
  intro j hj
  simp only [List.length_take] at hj
  rw [List.getElem?_take_of_lt (by omega)]
  exact h j (by omega)

theorem Pfx.get {l a : List ℕ} (h : Pfx l a) {j x : ℕ} (hj : l[j]? = some x) : a[j]? = some x := by
  have hlt : j < l.length := (List.getElem?_eq_some_iff.mp hj).1
  rw [h j hlt]; exact hj

/-- Overwrite position `k = |l|` of an array whose prefix is `l ++ m`: the prefix becomes `l ++ [v]`. -/
theorem Pfx.write {l m a : List ℕ} (h : Pfx (l ++ m) a) {k : ℕ} (hk : k = l.length) (hlt : k < a.length)
    (v : ℕ) : Pfx (l ++ [v]) (a.set k v) := by
  subst hk
  intro j hj
  simp only [List.length_append, List.length_cons, List.length_nil] at hj
  rw [List.getElem?_set]
  by_cases hjk : j = l.length
  · subst hjk
    simp [hlt]
  · have hjl : j < l.length := by omega
    rw [if_neg (Ne.symm hjk)]
    have := h j (by simp; omega)
    rw [List.getElem?_append_left hjl] at this
    rw [this, List.getElem?_append_left hjl]

theorem Pfx.push {l a : List ℕ} (h : Pfx l a) {k : ℕ} (hk : k = l.length) (hlt : k < a.length) (v : ℕ) :
    Pfx (l ++ [v]) (a.set k v) :=
  Pfx.write (m := []) (by simpa using h) hk hlt v

/-- A value at depth `i` of the (top-first) stack `l` sits at position `|l| - 1 - i` of the array. -/
theorem Pfx.getTop {l a : List ℕ} (h : Pfx l.reverse a) {i x : ℕ} (hi : l[i]? = some x) :
    a[l.length - 1 - i]? = some x := by
  have hlt : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  apply h.get
  rw [List.getElem?_reverse (by omega)]
  have : l.length - 1 - (l.length - 1 - i) = i := by omega
  rw [this]; exact hi

/-! ## The abstraction relation -/

/-- The dynamic part: the machine state `s` is represented by the environment `σ`. -/
structure Abs (s : St) (σ : Env) : Prop where
  pc : σ.vars "pc" = s.pc
  sp : σ.vars "sp" = s.stk.length
  rp : σ.vars "rp" = s.ret.length
  hp : σ.vars "hp" = s.heap.length
  stk : Pfx s.stk.reverse (σ.arrs "STK")
  rpc : Pfx (s.ret.reverse.map Prod.fst) (σ.arrs "RETPC")
  rh : Pfx (s.ret.reverse.map Prod.snd) (σ.arrs "RETH")
  ha : Pfx (s.heap.map Prod.fst) (σ.arrs "HA")
  hb : Pfx (s.heap.map Prod.snd) (σ.arrs "HB")

/-- The names of the eight arrays. -/
def arrNames : List String := ["OP", "OA", "FT", "STK", "RETPC", "RETH", "HA", "HB"]

/-- The constant part: program, tag bound, array lengths; `W` is the word bound, `Bi` the IMP+ bound. -/
structure Cst (P : Prog) (W Bi : ℕ) (σ : Env) : Prop where
  tb : σ.vars "B" = P.B
  op : ∀ i, i ≤ W → (σ.arrs "OP")[i]? = some (opc (P.code i))
  oa : ∀ i, i ≤ W → (σ.arrs "OA")[i]? = some (opa (P.code i))
  ft : ∀ f, f ≤ W → (σ.arrs "FT")[f]? = some (P.ft f)
  opa_lt : ∀ i, i ≤ W → opa (P.code i) < Bi
  len : ∀ a ∈ arrNames, (σ.arrs a).length = W + 1
  bW : P.B ≤ W
  bi : W + 18 ≤ Bi

/-- What a fetch leaves for the instruction `i`. -/
structure Fetched (σ : Env) (i : Instr) : Prop where
  op : σ.vars "op" = opc i
  oa : σ.vars "oa" = opa i

/-- Normalize reads of an updated environment. -/
macro "nrm" : tactic => `(tactic| simp only [vars_setVar, arrs_setVar, inp_setVar, out_setVar,
  vars_setArr, arrs_setArr, ↓reduceIte, String.reduceEq, eq_self, if_true, if_false])

/-! ## The blocks -/

abbrev V (s : String) : Expr := .var s
abbrev L (n : ℕ) : Expr := .lit n
abbrev G (a : String) (e : Expr) : Expr := .get a e
abbrev pl (e f : Expr) : Expr := .bin .add e f
abbrev mi (e f : Expr) : Expr := .bin .sub e f
abbrev ml (e f : Expr) : Expr := .bin .mul e f

/-- Stack cell `sp - 1` (top) and `sp - 2` (second). -/
abbrev tp : Expr := mi (V "sp") (L 1)
abbrev nx : Expr := mi (V "sp") (L 2)

abbrev incPc : Com := .assign "pc" (pl (V "pc") (L 1))
abbrev decSp : Com := .assign "sp" (mi (V "sp") (L 1))
abbrev incSp : Com := .assign "sp" (pl (V "sp") (L 1))

def bHalt : Com := .assign "run" (L 0)
def bLit : Com := .seq (.store "STK" (V "sp") (V "oa")) (.seq incSp incPc)
def bVar : Com :=
  .seq (.store "STK" (V "sp") (G "STK" (mi tp (V "oa")))) (.seq incSp incPc)
/-- `add`, `sub`, `mul`: `op` applied to the second (left) and top (right) cell. -/
def bBin (o : Bop) : Com :=
  .seq (.store "STK" nx (.bin o (G "STK" nx) (G "STK" tp))) (.seq decSp incPc)
def bLt : Com :=
  .seq (.ite (.lt (G "STK" nx) (G "STK" tp)) (.store "STK" nx (L 1)) (.store "STK" nx (L 0)))
    (.seq decSp incPc)
def bEq : Com :=
  .seq (.ite (.eq (G "STK" nx) (G "STK" tp)) (.store "STK" nx (L 1)) (.store "STK" nx (L 0)))
    (.seq decSp incPc)
def bCons : Com :=
  .seq (.store "HA" (V "hp") (G "STK" nx))
    (.seq (.store "HB" (V "hp") (G "STK" tp))
      (.seq (.store "STK" nx (pl (V "B") (V "hp")))
        (.seq (.assign "hp" (pl (V "hp") (L 1))) (.seq decSp incPc))))
def bFst : Com := .seq (.store "STK" tp (G "HA" (mi (G "STK" tp) (V "B")))) incPc
def bSnd : Com := .seq (.store "STK" tp (G "HB" (mi (G "STK" tp) (V "B")))) incPc
def bIsNat : Com :=
  .seq (.ite (.lt (G "STK" tp) (V "B")) (.store "STK" tp (L 1)) (.store "STK" tp (L 0))) incPc
def bJz : Com :=
  .seq (.ite (.eq (G "STK" tp) (L 0)) (.assign "pc" (pl (pl (V "pc") (L 1)) (V "oa"))) incPc) decSp
def bJmp : Com := .assign "pc" (pl (pl (V "pc") (L 1)) (V "oa"))
def bSlide : Com := .seq (.store "STK" nx (G "STK" tp)) (.seq decSp incPc)
def bCall : Com :=
  .seq (.assign "t1" (G "STK" tp))
    (.seq decSp
      (.seq (.store "RETPC" (V "rp") (pl (V "pc") (L 1)))
        (.seq (.store "RETH" (V "rp") (mi (V "sp") (V "oa")))
          (.seq (.assign "rp" (pl (V "rp") (L 1))) (.assign "pc" (G "FT" (V "t1")))))))
def bRet : Com :=
  .seq (.assign "t1" (G "STK" tp))
    (.seq (.assign "t2" (G "RETH" (mi (V "rp") (L 1))))
      (.seq (.assign "pc" (G "RETPC" (mi (V "rp") (L 1))))
        (.seq (.assign "rp" (mi (V "rp") (L 1)))
          (.seq (.ite (.lt (V "t2") tp) .skip (.assign "t2" tp))
            (.seq (.store "STK" (V "t2") (V "t1")) (.assign "sp" (pl (V "t2") (L 1))))))))

/-- Fetch the opcode and the operand of the instruction at `pc`. -/
def bFetch : Com := .seq (.assign "op" (G "OP" (V "pc"))) (.assign "oa" (G "OA" (V "pc")))

/-- The block of the opcode `j` (`16`, `ret`, is the default). -/
def blkOp : ℕ → Com
  | 0 => bHalt | 1 => bLit | 2 => bVar | 3 => bBin .add | 4 => bBin .sub | 5 => bBin .mul
  | 6 => bLt | 7 => bEq | 8 => bCons | 9 => bFst | 10 => bSnd | 11 => bIsNat | 12 => bJz
  | 13 => bJmp | 14 => bSlide | 15 => bCall | _ => bRet

/-- The dispatch chain `if op = k then blk k else if op = k+1 then … else blk (k+f)`. -/
def dispatchFrom : ℕ → ℕ → Com
  | k, 0 => blkOp k
  | k, f + 1 => .ite (.eq (V "op") (L k)) (blkOp k) (dispatchFrom (k + 1) f)

/-- The dispatcher over the opcodes `0 … 16`. -/
def bDispatch : Com := dispatchFrom 0 16

/-- One turn of the interpreter. -/
def bBody : Com := .seq bFetch bDispatch

/-- The interpreter: run while the machine runs. -/
def vmLoop : Com := .while (.eq (V "run") (L 1)) bBody

/-! ## The layout -/

/-- The layout of the interpreter: 10 scalars, 8 arrays, 8 temporaries (all expressions are shallow). -/
def Lvm : Layout where
  scalars := ["pc", "sp", "rp", "hp", "B", "run", "op", "oa", "t1", "t2"]
  arrays := arrNames
  temps := 8

/-! ## Frame facts -/

theorem bigStepB_len_arr {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStepB B c σ σ' k) :
    ∀ a, (σ'.arrs a).length = (σ.arrs a).length := by
  induction h with
  | skip => intro a; rfl
  | assign _ => intro a; rfl
  | store _ _ _ => intro a; exact length_arrs_setArr _ _ _ _ _
  | seq _ _ ih ih' => intro a; rw [ih', ih]
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => intro a; rw [ih', ih]
  | while_false _ => intro a; rfl
  | read _ => intro a; rfl
  | write _ => intro a; rfl

theorem run_len_arr {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) (a : String) :
    (σ'.arrs a).length = (σ.arrs a).length := by
  obtain ⟨k, _, hb⟩ := h
  exact bigStepB_len_arr hb a

/-- The constants survive a run of a command that does not write `B`, `OP`, `OA`, `FT`. -/
theorem Cst.of_run {P : Prog} {W Bi : ℕ} {σ σ' : Env} {c : Com} {K : ℕ} (hC : Cst P W Bi σ)
    (hr : Run Bi c σ σ' K) (h1 : "B" ∉ c.wvars) (h2 : "OP" ∉ c.warrs) (h3 : "OA" ∉ c.warrs)
    (h4 : "FT" ∉ c.warrs) : Cst P W Bi σ' where
  tb := by rw [hr.frame_var _ h1]; exact hC.tb
  op := fun i hi => by rw [hr.frame_arr _ h2]; exact hC.op i hi
  oa := fun i hi => by rw [hr.frame_arr _ h3]; exact hC.oa i hi
  ft := fun f hf => by rw [hr.frame_arr _ h4]; exact hC.ft f hf
  opa_lt := hC.opa_lt
  len := fun a ha => by rw [run_len_arr hr]; exact hC.len a ha
  bW := hC.bW
  bi := hC.bi

/-- The blocks never write these. -/
abbrev Frames (c : Com) : Prop :=
  "B" ∉ c.wvars ∧ "run" ∉ c.wvars ∧ "OP" ∉ c.warrs ∧ "OA" ∉ c.warrs ∧ "FT" ∉ c.warrs

/-- `blk` refines the instruction `i`: on a represented state whose one step (with all words `≤ W`)
is `s → s'`, it runs at cost `≤ K`, represents `s'`, and keeps the constants and the flag `run`. -/
def Refines (blk : Com) (K : ℕ) (i : Instr) : Prop :=
  ∀ (P : Prog) (W Bi : ℕ) (s s' : St) (σ : Env), Abs s σ → Cst P W Bi σ → s.Bd W → s'.Bd W →
    P.code s.pc = i → P.step s = some s' → Fetched σ i →
    ∃ σ', Run Bi blk σ σ' K ∧ Abs s' σ' ∧ Cst P W Bi σ' ∧ σ'.vars "run" = σ.vars "run"

/-- The same without the frame conclusions, which are obtained from the syntax of the block. -/
def Core (blk : Com) (K : ℕ) (i : Instr) : Prop :=
  ∀ (P : Prog) (W Bi : ℕ) (s s' : St) (σ : Env), Abs s σ → Cst P W Bi σ → s.Bd W → s'.Bd W →
    P.code s.pc = i → P.step s = some s' → Fetched σ i →
    ∃ σ', Run Bi blk σ σ' K ∧ Abs s' σ'

theorem Core.refines {blk : Com} {K : ℕ} {i : Instr} (h : Core blk K i) (hF : Frames blk) :
    Refines blk K i := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨σ', hr, hA'⟩ := h P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨h1, h2, h3, h4, h5⟩ := hF
  exact ⟨σ', hr, hA', hC.of_run hr h1 h3 h4 h5, hr.frame_var _ h2⟩

end Lax117284Proofs.Treewidth.Fun.VM.Ram
