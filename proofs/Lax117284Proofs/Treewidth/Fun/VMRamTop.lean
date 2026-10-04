import Lax117284Proofs.Treewidth.Fun.Defs
import Lax808846Proofs.Transfer
import Lax808846Proofs.Tactic

/-! ### `Lax117284Proofs.Treewidth.Fun.VMDefs` -/

section
/-!
# WP V1 (1): the virtual machine for the fragment F — instruction set, pure small-step semantics

A stack machine over a cons-cell heap.  Everything here is *pure* (lists and naturals); the IMP+ interpreter
of WP V2 implements `Prog.step`, with the following abstraction dictionary (documented for V2):

* `code`/`ft`      : the arrays `OP`/`OA` (op code and operand) and the function-entry table `FT`; `len` = code length;
* `stk`            : the value stack `STK`, **top first** (array bottom = list end; `sp = stk.length`);
* `ret`            : the return stack `RET`, top first, entries `(return pc, saved stack height)`;
* `heap`           : the cons heap, **bottom first**, cell `p` is `(HA[p], HB[p])`, `hp = heap.length`; append-only;
* a machine word is a natural; a *number* `n < B` is represented by the word `n`, a *pair* stored in cell `p`
  by the word `B + p` (`Rep` below).  `B = P.B` is a register of the machine.

Instructions: `lit n` pushes `n`; `var i` pushes a copy of the stack cell at depth `i` (0 = top); the binary
operations pop `b` (top) then `a` and push `op a b`; `cons` allocates; `fst`/`snd`/`isNat` inspect; `jz k`/`jmp k`
are *relative* forward jumps (`pc + 1 + k`); `slide` drops the cell under the top; `call n` pops a function id
`f`, pushes the frame `(pc + 1, stack height without the `n` argument cells)` and jumps to `ft f`; `ret` returns
the top value, discarding the callee's frame down to the saved height.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The instruction set (17 instructions; each carries at most one natural operand). -/
inductive Instr where
  | lit (n : ℕ) | var (i : ℕ)
  | add | sub | mul | lt | eq
  | cons | fst | snd | isNat
  | jz (k : ℕ) | jmp (k : ℕ) | slide
  | call (n : ℕ) | ret | halt
  deriving DecidableEq

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A machine program: code array (default `halt` outside), function-entry table, code length, tag bound `B`. -/
structure Prog where
  code : ℕ → Instr
  ft : ℕ → ℕ
  len : ℕ
  B : ℕ

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Machine state: pc, value stack (top first), return stack (top first), heap (bottom first, append-only). -/
structure St where
  pc : ℕ
  stk : List ℕ
  ret : List (ℕ × ℕ)
  heap : List (ℕ × ℕ)

/-- One step; `none` = halted (`halt`) or stuck. -/
def Prog.step (P : Prog) (s : St) : Option St :=
  match P.code s.pc with
  | .lit n => some { s with pc := s.pc + 1, stk := n :: s.stk }
  | .var i =>
    match s.stk[i]? with
    | some w => some { s with pc := s.pc + 1, stk := w :: s.stk }
    | none => none
  | .add =>
    match s.stk with
    | b :: a :: r => some { s with pc := s.pc + 1, stk := (a + b) :: r }
    | _ => none
  | .sub =>
    match s.stk with
    | b :: a :: r => some { s with pc := s.pc + 1, stk := (a - b) :: r }
    | _ => none
  | .mul =>
    match s.stk with
    | b :: a :: r => some { s with pc := s.pc + 1, stk := (a * b) :: r }
    | _ => none
  | .lt =>
    match s.stk with
    | b :: a :: r => some { s with pc := s.pc + 1, stk := (if a < b then 1 else 0) :: r }
    | _ => none
  | .eq =>
    match s.stk with
    | b :: a :: r => some { s with pc := s.pc + 1, stk := (if a = b then 1 else 0) :: r }
    | _ => none
  | .cons =>
    match s.stk with
    | b :: a :: r =>
      some { s with pc := s.pc + 1, stk := (P.B + s.heap.length) :: r, heap := s.heap ++ [(a, b)] }
    | _ => none
  | .fst =>
    match s.stk with
    | w :: r =>
      if P.B ≤ w then
        match s.heap[w - P.B]? with
        | some c => some { s with pc := s.pc + 1, stk := c.1 :: r }
        | none => none
      else none
    | _ => none
  | .snd =>
    match s.stk with
    | w :: r =>
      if P.B ≤ w then
        match s.heap[w - P.B]? with
        | some c => some { s with pc := s.pc + 1, stk := c.2 :: r }
        | none => none
      else none
    | _ => none
  | .isNat =>
    match s.stk with
    | w :: r => some { s with pc := s.pc + 1, stk := (if w < P.B then 1 else 0) :: r }
    | _ => none
  | .jz k =>
    match s.stk with
    | w :: r => some { s with pc := if w = 0 then s.pc + 1 + k else s.pc + 1, stk := r }
    | _ => none
  | .jmp k => some { s with pc := s.pc + 1 + k }
  | .slide =>
    match s.stk with
    | v :: _ :: r => some { s with pc := s.pc + 1, stk := v :: r }
    | _ => none
  | .call n =>
    match s.stk with
    | f :: r => some { s with pc := P.ft f, stk := r, ret := (s.pc + 1, r.length - n) :: s.ret }
    | _ => none
  | .ret =>
    match s.stk, s.ret with
    | w :: r, (pc', h) :: rs => some { s with pc := pc', stk := w :: r.drop (r.length - h), ret := rs }
    | _, _ => none
  | .halt => none

/-! ## Word-size accounting -/

/-- Every machine natural of the state (pc, all words on the stacks and in the heap, all lengths) is `≤ W`. -/
structure St.Bd (W : ℕ) (s : St) : Prop where
  pc : s.pc ≤ W
  stkLen : s.stk.length ≤ W
  stk : ∀ w ∈ s.stk, w ≤ W
  retLen : s.ret.length ≤ W
  ret : ∀ p ∈ s.ret, p.1 ≤ W ∧ p.2 ≤ W
  heapLen : s.heap.length ≤ W
  heap : ∀ p ∈ s.heap, p.1 ≤ W ∧ p.2 ≤ W

theorem St.Bd.mono {W W' : ℕ} {s : St} (h : s.Bd W) (hW : W ≤ W') : s.Bd W' :=
  ⟨Nat.le_trans h.pc hW, Nat.le_trans h.stkLen hW, fun w hw => Nat.le_trans (h.stk w hw) hW, Nat.le_trans h.retLen hW,
    fun p hp => ⟨Nat.le_trans (h.ret p hp).1 hW, Nat.le_trans (h.ret p hp).2 hW⟩, Nat.le_trans h.heapLen hW,
    fun p hp => ⟨Nat.le_trans (h.heap p hp).1 hW, Nat.le_trans (h.heap p hp).2 hW⟩⟩

/-- `n` steps of the machine, every state along the run (including both ends) satisfying `Bd W`. -/
inductive StepsB (P : Prog) (W : ℕ) : ℕ → St → St → Prop
  | refl {s : St} : s.Bd W → StepsB P W 0 s s
  | step {s s' s'' : St} {n : ℕ} : s.Bd W → P.step s = some s' → StepsB P W n s' s'' →
      StepsB P W (n + 1) s s''

theorem StepsB.trans {P : Prog} {W : ℕ} {n m : ℕ} {s s' s'' : St} (h₁ : StepsB P W n s s')
    (h₂ : StepsB P W m s' s'') : StepsB P W (n + m) s s'' := by
  induction h₁ with
  | refl _ => simpa using h₂
  | step hb hs _ ih =>
    have := StepsB.step hb hs (ih h₂)
    convert this using 1; omega

theorem StepsB.one {P : Prog} {W : ℕ} {s s' : St} (h : s.Bd W) (hs : P.step s = some s') (h' : s'.Bd W) :
    StepsB P W 1 s s' := StepsB.step h hs (StepsB.refl h')

theorem StepsB.bd_start {P : Prog} {W n : ℕ} {s s' : St} (h : StepsB P W n s s') : s.Bd W := by
  cases h <;> assumption

theorem StepsB.bd_end {P : Prog} {W n : ℕ} {s s' : St} (h : StepsB P W n s s') : s'.Bd W := by
  induction h with
  | refl h => exact h
  | step _ _ _ ih => exact ih

/-! ## Heap representation of values (monotone under the append-only heap) -/

/-- Heap extension: `H'` is `H` with cells appended. -/
def HExt (H H' : List (ℕ × ℕ)) : Prop := ∃ t, H' = H ++ t

theorem HExt.refl (H : List (ℕ × ℕ)) : HExt H H := ⟨[], by simp⟩
theorem HExt.trans {H₁ H₂ H₃ : List (ℕ × ℕ)} (h₁ : HExt H₁ H₂) (h₂ : HExt H₂ H₃) : HExt H₁ H₃ := by
  obtain ⟨a, rfl⟩ := h₁; obtain ⟨b, rfl⟩ := h₂; exact ⟨a ++ b, by simp⟩
theorem HExt.getElem? {H H' : List (ℕ × ℕ)} (h : HExt H H') {p : ℕ} {c : ℕ × ℕ} (hp : H[p]? = some c) :
    H'[p]? = some c := by
  obtain ⟨t, rfl⟩ := h
  have : p < H.length := (List.getElem?_eq_some_iff.mp hp).1
  rw [List.getElem?_append_left this]; exact hp
theorem HExt.snoc (H : List (ℕ × ℕ)) (c : ℕ × ℕ) : HExt H (H ++ [c]) := ⟨[c], rfl⟩

/-- The word `w` represents the value `v` in the heap `H` (tree-shaped; sharing is allowed but not assumed):
a number `n < B` is the word `n`, a pair is a pointer `B + p` to the cell `p`. -/
inductive Rep (B : ℕ) (H : List (ℕ × ℕ)) : ℕ → Val → Prop
  | nat {n : ℕ} : n < B → Rep B H n (.nat n)
  | cons {p a b : ℕ} {u v : Val} : H[p]? = some (a, b) → Rep B H a u → Rep B H b v →
      Rep B H (B + p) (.cons u v)

/-- Lists of words representing lists of values. -/
inductive RepL (B : ℕ) (H : List (ℕ × ℕ)) : List ℕ → List Val → Prop
  | nil : RepL B H [] []
  | cons {w : ℕ} {v : Val} {ws vs} : Rep B H w v → RepL B H ws vs → RepL B H (w :: ws) (v :: vs)

theorem Rep.mono {B : ℕ} {H H' : List (ℕ × ℕ)} (hH : HExt H H') {w : ℕ} {v : Val} (h : Rep B H w v) :
    Rep B H' w v := by
  induction h with
  | nat hn => exact .nat hn
  | cons hp _ _ ih₁ ih₂ => exact .cons (hH.getElem? hp) ih₁ ih₂

theorem RepL.mono {B : ℕ} {H H' : List (ℕ × ℕ)} (hH : HExt H H') {ws : List ℕ} {vs : List Val}
    (h : RepL B H ws vs) : RepL B H' ws vs := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (h.mono hH) ih

theorem RepL.length_eq {B : ℕ} {H : List (ℕ × ℕ)} {ws : List ℕ} {vs : List Val} (h : RepL B H ws vs) :
    ws.length = vs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem RepL.get {B : ℕ} {H : List (ℕ × ℕ)} {ws : List ℕ} {vs : List Val} (h : RepL B H ws vs) {i : ℕ}
    {x : Val} (hi : vs[i]? = some x) : ∃ w, ws[i]? = some w ∧ Rep B H w x := by
  induction h generalizing i with
  | nil => simp at hi
  | cons hw _ ih =>
    cases i with
    | zero => simp at hi ⊢; subst hi; exact hw
    | succ i => simp at hi ⊢; exact ih hi

theorem Rep.nat_inv {B : ℕ} {H : List (ℕ × ℕ)} {w n : ℕ} (h : Rep B H w (.nat n)) : w = n ∧ n < B := by
  cases h with
  | nat hn => exact ⟨rfl, hn⟩

theorem Rep.cons_inv {B : ℕ} {H : List (ℕ × ℕ)} {w : ℕ} {u v : Val} (h : Rep B H w (.cons u v)) :
    ∃ p a b, w = B + p ∧ H[p]? = some (a, b) ∧ Rep B H a u ∧ Rep B H b v := by
  cases h with
  | cons hp h₁ h₂ => exact ⟨_, _, _, rfl, hp, h₁, h₂⟩

end Lax117284Proofs.Treewidth.Fun.VM

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMRamDefs` -/

section
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

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMRamOps1` -/

section
/-!
# WP V2 (2): one-step lemmas, part 1 — inversion of `Prog.step` and the stack instructions

`lit`, `var`, `add`, `sub`, `mul`, `lt`, `eq`, `slide`.  Every lemma has the shape `Core blk 40 i`
(`Run` at cost `≤ 40`, `Abs` of the successor); the frame conclusions of `Refines` come from `Frames`.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-! ## Inversion of `Prog.step` -/

theorem inv_lit {P : Prog} {s s' : St} {n : ℕ} (hc : P.code s.pc = .lit n) (h : P.step s = some s') :
    s' = { s with pc := s.pc + 1, stk := n :: s.stk } := by
  simp only [Prog.step, hc] at h
  exact (Option.some.inj h).symm

theorem inv_var {P : Prog} {s s' : St} {i : ℕ} (hc : P.code s.pc = .var i) (h : P.step s = some s') :
    ∃ w, s.stk[i]? = some w ∧ s' = { s with pc := s.pc + 1, stk := w :: s.stk } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i w hw; exact ⟨w, hw, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_add {P : Prog} {s s' : St} (hc : P.code s.pc = .add) (h : P.step s = some s') :
    ∃ b a r, s.stk = b :: a :: r ∧ s' = { s with pc := s.pc + 1, stk := (a + b) :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i b a r hst; exact ⟨b, a, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_sub {P : Prog} {s s' : St} (hc : P.code s.pc = .sub) (h : P.step s = some s') :
    ∃ b a r, s.stk = b :: a :: r ∧ s' = { s with pc := s.pc + 1, stk := (a - b) :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i b a r hst; exact ⟨b, a, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_mul {P : Prog} {s s' : St} (hc : P.code s.pc = .mul) (h : P.step s = some s') :
    ∃ b a r, s.stk = b :: a :: r ∧ s' = { s with pc := s.pc + 1, stk := (a * b) :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i b a r hst; exact ⟨b, a, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_lt {P : Prog} {s s' : St} (hc : P.code s.pc = .lt) (h : P.step s = some s') :
    ∃ b a r, s.stk = b :: a :: r ∧
      s' = { s with pc := s.pc + 1, stk := (if a < b then 1 else 0) :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i b a r hst; exact ⟨b, a, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_eq {P : Prog} {s s' : St} (hc : P.code s.pc = .eq) (h : P.step s = some s') :
    ∃ b a r, s.stk = b :: a :: r ∧
      s' = { s with pc := s.pc + 1, stk := (if a = b then 1 else 0) :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i b a r hst; exact ⟨b, a, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_slide {P : Prog} {s s' : St} (hc : P.code s.pc = .slide) (h : P.step s = some s') :
    ∃ v u r, s.stk = v :: u :: r ∧ s' = { s with pc := s.pc + 1, stk := v :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i v u r hst; exact ⟨v, u, r, hst, (Option.some.inj h).symm⟩
  · simp at h

/-! ## Reading the stack -/

theorem stk_get {s : St} {σ : Env} (hA : Abs s σ) {i x : ℕ} (hi : s.stk[i]? = some x) :
    (σ.arrs "STK").getD (σ.vars "sp" - 1 - i) 0 = x := by
  rw [hA.sp, List.getD_eq_getElem?_getD, hA.stk.getTop hi]; rfl

theorem stk_top {s : St} {σ : Env} (hA : Abs s σ) {b : ℕ} {r : List ℕ} (hst : s.stk = b :: r) :
    (σ.arrs "STK").getD (σ.vars "sp" - 1) 0 = b := by
  have := stk_get hA (i := 0) (x := b) (by simp [hst])
  simpa using this

theorem stk_nx {s : St} {σ : Env} (hA : Abs s σ) {b a : ℕ} {r : List ℕ} (hst : s.stk = b :: a :: r) :
    (σ.arrs "STK").getD (σ.vars "sp" - 2) 0 = a := by
  have := stk_get hA (i := 1) (x := a) (by simp [hst])
  simpa [Nat.sub_sub] using this

/-- The tower produced by the `add`/`sub`/`mul`/`lt`/`eq`/`slide` blocks (value `v` written at `sp - 2`). -/
def twBin (σ : Env) (v : ℕ) : Env :=
  ((σ.setArr "STK" (σ.vars "sp" - 2) v).setVar "sp" ((σ.setArr "STK" (σ.vars "sp" - 2) v).vars "sp" - 1)).setVar
    "pc" (((σ.setArr "STK" (σ.vars "sp" - 2) v).setVar "sp" ((σ.setArr "STK" (σ.vars "sp" - 2) v).vars "sp" - 1)).vars
      "pc" + 1)

theorem abs_bin {P : Prog} {W Bi : ℕ} {s : St} {σ : Env} (hA : Abs s σ) (hC : Cst P W Bi σ)
    (hlen : s.stk.length ≤ W) {b a : ℕ} {r : List ℕ} (hst : s.stk = b :: a :: r) (v : ℕ) :
    Abs ⟨s.pc + 1, v :: r, s.ret, s.heap⟩ (twBin σ v) := by
  have hsp : σ.vars "sp" = r.length + 2 := by rw [hA.sp, hst]; simp
  have hl : (σ.arrs "STK").length = W + 1 := hC.len "STK" (by simp [arrNames])
  have hstk : Pfx (r.reverse ++ [a, b]) (σ.arrs "STK") := by
    have := hA.stk; rw [hst] at this; simpa using this
  have hlen' : r.length + 2 ≤ W := by rw [hst] at hlen; simp at hlen; omega
  unfold twBin
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; rw [hA.pc]
  · nrm; rw [hsp]; simp
  · nrm; exact hA.rp
  · nrm; exact hA.hp
  · nrm
    have := hstk.write (k := σ.vars "sp" - 2) (by rw [hsp]; simp) (by omega) v
    simpa using this
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm; exact hA.ha
  · nrm; exact hA.hb

/-! ## The instructions -/

theorem core_lit (n : ℕ) : Core bLit 40 (.lit n) := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  have hs' := inv_lit hc hs
  subst hs'
  have hn : n ≤ W := hB'.stk n (by simp)
  have hspW : s.stk.length + 1 ≤ W := by have := hB'.stkLen; simpa using this
  have hl : (σ.arrs "STK").length = W + 1 := hC.len "STK" (by simp [arrNames])
  have hoa : σ.vars "oa" = n := hf.oa
  have hsp := hA.sp
  have hpc := hA.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  unfold bLit
  run_vcg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; rw [hpc]
  · nrm; rw [hsp]; simp
  · nrm; exact hA.rp
  · nrm; exact hA.hp
  · nrm
    have := hA.stk.push (k := σ.vars "sp") (by rw [hsp]; simp) (by omega) n
    rw [hoa]; simpa using this
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm; exact hA.ha
  · nrm; exact hA.hb

theorem core_var (i : ℕ) : Core bVar 40 (.var i) := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨w, hw, rfl⟩ := inv_var hc hs
  have hwW : w ≤ W := hB.stk w (List.mem_of_getElem? hw)
  have hspW : s.stk.length + 1 ≤ W := by have := hB'.stkLen; simpa using this
  have hl : (σ.arrs "STK").length = W + 1 := hC.len "STK" (by simp [arrNames])
  have hoa : σ.vars "oa" = i := hf.oa
  have hsp := hA.sp
  have hpc := hA.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hilt : i < s.stk.length := (List.getElem?_eq_some_iff.mp hw).1
  have g := stk_get hA hw
  rw [← hoa] at g
  unfold bVar
  run_vcg
  rw [g]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; rw [hpc]
  · nrm; rw [hsp]; simp
  · nrm; exact hA.rp
  · nrm; exact hA.hp
  · nrm
    have := hA.stk.push (k := σ.vars "sp") (by rw [hsp]; simp) (by omega) w
    simpa using this
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm; exact hA.ha
  · nrm; exact hA.hb

/-- Facts shared by the binary instructions. -/
theorem bin_facts {P : Prog} {W Bi : ℕ} {s : St} {σ : Env} (hA : Abs s σ) (hC : Cst P W Bi σ)
    (hB : s.Bd W) {b a : ℕ} {r : List ℕ} (hst : s.stk = b :: a :: r) :
    b ≤ W ∧ a ≤ W ∧ σ.vars "sp" = r.length + 2 ∧ r.length + 2 ≤ W ∧
    (σ.arrs "STK").length = W + 1 ∧
    (σ.arrs "STK").getD (σ.vars "sp" - 1) 0 = b ∧ (σ.arrs "STK").getD (σ.vars "sp" - 2) 0 = a := by
  refine ⟨hB.stk b (by simp [hst]), hB.stk a (by simp [hst]), by rw [hA.sp, hst]; simp, ?_,
    hC.len "STK" (by simp [arrNames]), stk_top hA hst, stk_nx hA hst⟩
  have := hB.stkLen; rw [hst] at this; simp at this; omega

theorem core_add : Core (bBin .add) 40 .add := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨b, a, r, hst, rfl⟩ := inv_add hc hs
  obtain ⟨hbW, haW, hsp, hspW, hl, g1, g2⟩ := bin_facts hA hC hB hst
  have hvW : a + b ≤ W := hB'.stk _ (by simp)
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  unfold bBin
  run_vcg
  rw [g1, g2]
  exact abs_bin hA hC hB.stkLen hst _

theorem core_sub : Core (bBin .sub) 40 .sub := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨b, a, r, hst, rfl⟩ := inv_sub hc hs
  obtain ⟨hbW, haW, hsp, hspW, hl, g1, g2⟩ := bin_facts hA hC hB hst
  have hvW : a - b ≤ W := hB'.stk _ (by simp)
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  unfold bBin
  run_vcg
  rw [g1, g2]
  exact abs_bin hA hC hB.stkLen hst _

theorem core_mul : Core (bBin .mul) 40 .mul := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨b, a, r, hst, rfl⟩ := inv_mul hc hs
  obtain ⟨hbW, haW, hsp, hspW, hl, g1, g2⟩ := bin_facts hA hC hB hst
  have hvW : a * b ≤ W := hB'.stk _ (by simp)
  have hprod : (σ.arrs "STK").getD (σ.vars "sp" - 2) 0 * (σ.arrs "STK").getD (σ.vars "sp" - 1) 0 ≤ W := by
    rw [g1, g2]; exact hvW
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  unfold bBin
  run_vcg
  rw [g1, g2]
  exact abs_bin hA hC hB.stkLen hst _

theorem core_lt : Core bLt 40 .lt := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨b, a, r, hst, rfl⟩ := inv_lt hc hs
  obtain ⟨hbW, haW, hsp, hspW, hl, g1, g2⟩ := bin_facts hA hC hB hst
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  unfold bLt
  run_vcg
  · have h : a < b := by omega
    rw [if_pos h]; exact abs_bin hA hC hB.stkLen hst 1
  · have h : ¬ a < b := by omega
    rw [if_neg h]; exact abs_bin hA hC hB.stkLen hst 0

theorem core_eq : Core bEq 40 .eq := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨b, a, r, hst, rfl⟩ := inv_eq hc hs
  obtain ⟨hbW, haW, hsp, hspW, hl, g1, g2⟩ := bin_facts hA hC hB hst
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  unfold bEq
  run_vcg
  · have h : a = b := by omega
    rw [if_pos h]; exact abs_bin hA hC hB.stkLen hst 1
  · have h : ¬ a = b := by omega
    rw [if_neg h]; exact abs_bin hA hC hB.stkLen hst 0

theorem core_slide : Core bSlide 40 .slide := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨v, u, r, hst, rfl⟩ := inv_slide hc hs
  obtain ⟨hbW, haW, hsp, hspW, hl, g1, g2⟩ := bin_facts hA hC hB hst
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  unfold bSlide
  run_vcg
  rw [g1]
  exact abs_bin hA hC hB.stkLen hst _

end Lax117284Proofs.Treewidth.Fun.VM.Ram

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMRamOps2` -/

section
/-!
# WP V2 (3): one-step lemmas, part 2 — heap, tests, jumps, calls, `halt`

`cons`, `fst`, `snd`, `isNat`, `jz`, `jmp`, `call`, `ret`, `halt`.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-! ## Inversion of `Prog.step` -/

theorem inv_cons {P : Prog} {s s' : St} (hc : P.code s.pc = .cons) (h : P.step s = some s') :
    ∃ b a r, s.stk = b :: a :: r ∧
      s' = { s with pc := s.pc + 1, stk := (P.B + s.heap.length) :: r, heap := s.heap ++ [(a, b)] } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i b a r hst; exact ⟨b, a, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_fst {P : Prog} {s s' : St} (hc : P.code s.pc = .fst) (h : P.step s = some s') :
    ∃ w r c, s.stk = w :: r ∧ P.B ≤ w ∧ s.heap[w - P.B]? = some c ∧
      s' = { s with pc := s.pc + 1, stk := c.1 :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i w r hst
    split at h
    · rename_i hle
      split at h
      · rename_i c hc'; exact ⟨w, r, c, hst, hle, hc', (Option.some.inj h).symm⟩
      · simp at h
    · simp at h
  · simp at h

theorem inv_snd {P : Prog} {s s' : St} (hc : P.code s.pc = .snd) (h : P.step s = some s') :
    ∃ w r c, s.stk = w :: r ∧ P.B ≤ w ∧ s.heap[w - P.B]? = some c ∧
      s' = { s with pc := s.pc + 1, stk := c.2 :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i w r hst
    split at h
    · rename_i hle
      split at h
      · rename_i c hc'; exact ⟨w, r, c, hst, hle, hc', (Option.some.inj h).symm⟩
      · simp at h
    · simp at h
  · simp at h

theorem inv_isNat {P : Prog} {s s' : St} (hc : P.code s.pc = .isNat) (h : P.step s = some s') :
    ∃ w r, s.stk = w :: r ∧
      s' = { s with pc := s.pc + 1, stk := (if w < P.B then 1 else 0) :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i w r hst; exact ⟨w, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_jz {P : Prog} {s s' : St} {k : ℕ} (hc : P.code s.pc = .jz k) (h : P.step s = some s') :
    ∃ w r, s.stk = w :: r ∧
      s' = { s with pc := if w = 0 then s.pc + 1 + k else s.pc + 1, stk := r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i w r hst; exact ⟨w, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_jmp {P : Prog} {s s' : St} {k : ℕ} (hc : P.code s.pc = .jmp k) (h : P.step s = some s') :
    s' = { s with pc := s.pc + 1 + k } := by
  simp only [Prog.step, hc] at h
  exact (Option.some.inj h).symm

theorem inv_call {P : Prog} {s s' : St} {n : ℕ} (hc : P.code s.pc = .call n) (h : P.step s = some s') :
    ∃ f r, s.stk = f :: r ∧
      s' = { s with pc := P.ft f, stk := r, ret := (s.pc + 1, r.length - n) :: s.ret } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i f r hst; exact ⟨f, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_ret {P : Prog} {s s' : St} (hc : P.code s.pc = .ret) (h : P.step s = some s') :
    ∃ w r pc' h' rs, s.stk = w :: r ∧ s.ret = (pc', h') :: rs ∧
      s' = { s with pc := pc', stk := w :: r.drop (r.length - h'), ret := rs } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i w r pc' h' rs hst hret; exact ⟨w, r, pc', h', rs, hst, hret, (Option.some.inj h).symm⟩
  · simp at h

/-! ## `cons` -/

theorem core_cons : Core bCons 40 .cons := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨b, a, r, hst, rfl⟩ := inv_cons hc hs
  obtain ⟨hbW, haW, hsp, hspW, hl, g1, g2⟩ := bin_facts hA hC hB hst
  have hvW : P.B + s.heap.length ≤ W := hB'.stk _ (by simp)
  have hhW : s.heap.length + 1 ≤ W := by have := hB'.heapLen; simpa using this
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  have hhp := hA.hp
  have htb := hC.tb
  have hlA : (σ.arrs "HA").length = W + 1 := hC.len "HA" (by simp [arrNames])
  have hlB : (σ.arrs "HB").length = W + 1 := hC.len "HB" (by simp [arrNames])
  have hsum : σ.vars "B" + σ.vars "hp" ≤ W := by rw [htb, hhp]; exact hvW
  unfold bCons
  run_vcg
  all_goals try (nrm; omega)
  nrm
  rw [g1, g2]
  have hstk : Pfx (r.reverse ++ [a, b]) (σ.arrs "STK") := by
    have := hA.stk; rw [hst] at this; simpa using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; rw [hpc]
  · nrm; rw [hsp]; simp
  · nrm; exact hA.rp
  · nrm; rw [hhp]; simp
  · nrm
    have := hstk.write (k := σ.vars "sp" - 2) (by rw [hsp]; simp) (by omega) (σ.vars "B" + σ.vars "hp")
    rw [htb, hhp] at this ⊢
    simpa using this
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm
    have := hA.ha.push (k := σ.vars "hp") (by rw [hhp]; simp) (by omega) a
    rw [hhp] at this ⊢
    simpa using this
  · nrm
    have := hA.hb.push (k := σ.vars "hp") (by rw [hhp]; simp) (by omega) b
    rw [hhp] at this ⊢
    simpa using this

/-! ## `fst`, `snd`, `isNat` -/

/-- The tower of the blocks that overwrite the top of the stack and advance `pc`. -/
def twTop (σ : Env) (v : ℕ) : Env :=
  (σ.setArr "STK" (σ.vars "sp" - 1) v).setVar "pc" ((σ.setArr "STK" (σ.vars "sp" - 1) v).vars "pc" + 1)

theorem abs_top {P : Prog} {W Bi : ℕ} {s : St} {σ : Env} (hA : Abs s σ) (hC : Cst P W Bi σ)
    (hlen : s.stk.length ≤ W) {w : ℕ} {r : List ℕ} (hst : s.stk = w :: r) (v : ℕ) :
    Abs ⟨s.pc + 1, v :: r, s.ret, s.heap⟩ (twTop σ v) := by
  have hsp : σ.vars "sp" = r.length + 1 := by rw [hA.sp, hst]; simp
  have hl : (σ.arrs "STK").length = W + 1 := hC.len "STK" (by simp [arrNames])
  have hstk : Pfx (r.reverse ++ [w]) (σ.arrs "STK") := by
    have := hA.stk; rw [hst] at this; simpa using this
  have hlen' : r.length + 1 ≤ W := by rw [hst] at hlen; simpa using hlen
  unfold twTop
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; rw [hA.pc]
  · nrm; rw [hsp]; simp
  · nrm; exact hA.rp
  · nrm; exact hA.hp
  · nrm
    have := hstk.write (k := σ.vars "sp" - 1) (by rw [hsp]; simp) (by omega) v
    simpa using this
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm; exact hA.ha
  · nrm; exact hA.hb

theorem top_facts {P : Prog} {W Bi : ℕ} {s : St} {σ : Env} (hA : Abs s σ) (hC : Cst P W Bi σ)
    (hB : s.Bd W) {w : ℕ} {r : List ℕ} (hst : s.stk = w :: r) :
    w ≤ W ∧ σ.vars "sp" = r.length + 1 ∧ r.length + 1 ≤ W ∧
    (σ.arrs "STK").length = W + 1 ∧ (σ.arrs "STK").getD (σ.vars "sp" - 1) 0 = w := by
  refine ⟨hB.stk w (by simp [hst]), by rw [hA.sp, hst]; simp, ?_, hC.len "STK" (by simp [arrNames]),
    stk_top hA hst⟩
  have := hB.stkLen; rw [hst] at this; simp at this; omega

theorem core_fst : Core bFst 40 .fst := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨w, r, c, hst, hle, hheap, rfl⟩ := inv_fst hc hs
  obtain ⟨hwW, hsp, hspW, hl, g1⟩ := top_facts hA hC hB hst
  have hvW : c.1 ≤ W := hB'.stk _ (by simp)
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  have htb := hC.tb
  have hlA : (σ.arrs "HA").length = W + 1 := hC.len "HA" (by simp [arrNames])
  have hidx : w - P.B < s.heap.length := (List.getElem?_eq_some_iff.mp hheap).1
  have hhW : s.heap.length ≤ W := hB.heapLen
  have hHA : (σ.arrs "HA").getD ((σ.arrs "STK").getD (σ.vars "sp" - 1) 0 - σ.vars "B") 0 = c.1 := by
    rw [g1, htb, List.getD_eq_getElem?_getD]
    have : (σ.arrs "HA")[w - P.B]? = some c.1 := by
      apply hA.ha.get; simp [hheap]
    rw [this]; rfl
  unfold bFst
  run_vcg
  rw [hHA]
  exact abs_top hA hC hB.stkLen hst _

theorem core_snd : Core bSnd 40 .snd := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨w, r, c, hst, hle, hheap, rfl⟩ := inv_snd hc hs
  obtain ⟨hwW, hsp, hspW, hl, g1⟩ := top_facts hA hC hB hst
  have hvW : c.2 ≤ W := hB'.stk _ (by simp)
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  have htb := hC.tb
  have hlA : (σ.arrs "HB").length = W + 1 := hC.len "HB" (by simp [arrNames])
  have hidx : w - P.B < s.heap.length := (List.getElem?_eq_some_iff.mp hheap).1
  have hhW : s.heap.length ≤ W := hB.heapLen
  have hHB : (σ.arrs "HB").getD ((σ.arrs "STK").getD (σ.vars "sp" - 1) 0 - σ.vars "B") 0 = c.2 := by
    rw [g1, htb, List.getD_eq_getElem?_getD]
    have : (σ.arrs "HB")[w - P.B]? = some c.2 := by
      apply hA.hb.get; simp [hheap]
    rw [this]; rfl
  unfold bSnd
  run_vcg
  rw [hHB]
  exact abs_top hA hC hB.stkLen hst _

theorem core_isNat : Core bIsNat 40 .isNat := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨w, r, hst, rfl⟩ := inv_isNat hc hs
  obtain ⟨hwW, hsp, hspW, hl, g1⟩ := top_facts hA hC hB hst
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  have htb := hC.tb
  have hPB := hC.bW
  unfold bIsNat
  run_vcg
  · have h : w < P.B := by omega
    rw [if_pos h]; exact abs_top hA hC hB.stkLen hst 1
  · have h : ¬ w < P.B := by omega
    rw [if_neg h]; exact abs_top hA hC hB.stkLen hst 0

/-! ## `jz`, `jmp` -/

/-- The tower of the blocks that only change `pc` (to the value `v`). -/
def twPc (σ : Env) (v : ℕ) : Env := σ.setVar "pc" v

/-- The tower of `jz`: `pc := v`, `sp := sp - 1`. -/
def twJz (σ : Env) (v : ℕ) : Env :=
  (σ.setVar "pc" v).setVar "sp" ((σ.setVar "pc" v).vars "sp" - 1)

theorem abs_jz {s : St} {σ : Env} (hA : Abs s σ) {w : ℕ} {r : List ℕ}
    (hst : s.stk = w :: r) (v : ℕ) :
    Abs ⟨v, r, s.ret, s.heap⟩ (twJz σ v) := by
  have hsp : σ.vars "sp" = r.length + 1 := by rw [hA.sp, hst]; simp
  have hstk : Pfx (r.reverse ++ [w]) (σ.arrs "STK") := by
    have := hA.stk; rw [hst] at this; simpa using this
  unfold twJz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; rw [hsp]; simp
  · nrm; exact hA.rp
  · nrm; exact hA.hp
  · nrm; exact hstk.left
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm; exact hA.ha
  · nrm; exact hA.hb

theorem core_jz (k : ℕ) : Core bJz 40 (.jz k) := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨w, r, hst, rfl⟩ := inv_jz hc hs
  obtain ⟨hwW, hsp, hspW, hl, g1⟩ := top_facts hA hC hB hst
  have hpcW : (if w = 0 then s.pc + 1 + k else s.pc + 1) ≤ W := hB'.pc
  have hpcW1 : s.pc + 1 ≤ W := by split_ifs at hpcW <;> omega
  have hpcW2 : w = 0 → s.pc + 1 + k ≤ W := fun h => by simpa [h] using hpcW
  have hB18 := hC.bi
  have hpc := hA.pc
  have hoa : σ.vars "oa" = k := hf.oa
  unfold bJz
  run_vcg
  · have h : w = 0 := by omega
    rw [if_pos h]
    rw [hpc, hoa]
    exact abs_jz hA hst _
  · have h : ¬ w = 0 := by omega
    rw [if_neg h]
    rw [hpc]
    exact abs_jz hA hst _

theorem core_jmp (k : ℕ) : Core bJmp 40 (.jmp k) := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  have hs' := inv_jmp hc hs
  subst hs'
  have hpcW : s.pc + 1 + k ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  have hoa : σ.vars "oa" = k := hf.oa
  unfold bJmp
  run_vcg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; rw [hpc, hoa]
  · nrm; exact hA.sp
  · nrm; exact hA.rp
  · nrm; exact hA.hp
  · nrm; exact hA.stk
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm; exact hA.ha
  · nrm; exact hA.hb

/-! ## `halt` -/

theorem halt_run {P : Prog} {W Bi : ℕ} {s : St} {σ : Env} (hA : Abs s σ) (hC : Cst P W Bi σ) :
    ∃ σ', Run Bi bHalt σ σ' 4 ∧ Abs s σ' ∧ Cst P W Bi σ' ∧ σ'.vars "run" = 0 := by
  have hB18 := hC.bi
  obtain ⟨σ', hr, rfl⟩ : ∃ σ', Run Bi bHalt σ σ' 4 ∧ σ' = σ.setVar "run" 0 := by
    unfold bHalt
    run_vcg
    rfl
  refine ⟨_, hr, ?_, hC.of_run hr (by decide) (by decide) (by decide) (by decide), by simp⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; exact hA.pc
  · nrm; exact hA.sp
  · nrm; exact hA.rp
  · nrm; exact hA.hp
  · nrm; exact hA.stk
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm; exact hA.ha
  · nrm; exact hA.hb

end Lax117284Proofs.Treewidth.Fun.VM.Ram

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMRamOps3` -/

section
/-!
# WP V2 (4): one-step lemmas, part 3 — `call` and `ret`
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-! ## `call` -/

theorem core_call (n : ℕ) : Core bCall 40 (.call n) := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨f, r, hst, rfl⟩ := inv_call hc hs
  obtain ⟨hfW, hsp, hspW, hl, g1⟩ := top_facts hA hC hB hst
  have hp1 : s.pc + 1 ≤ W := (hB'.ret (s.pc + 1, r.length - n) (by simp)).1
  have hp2 : r.length - n ≤ W := (hB'.ret (s.pc + 1, r.length - n) (by simp)).2
  have hrpW : s.ret.length + 1 ≤ W := by have := hB'.retLen; simpa using this
  have hftW : P.ft f ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  have hrp := hA.rp
  have hoa : σ.vars "oa" = n := hf.oa
  have hnB : n < Bi := by
    have := hC.opa_lt s.pc hB.pc
    rwa [hc] at this
  have hlP : (σ.arrs "RETPC").length = W + 1 := hC.len "RETPC" (by simp [arrNames])
  have hlH : (σ.arrs "RETH").length = W + 1 := hC.len "RETH" (by simp [arrNames])
  have hlF : (σ.arrs "FT").length = W + 1 := hC.len "FT" (by simp [arrNames])
  have hFT : (σ.arrs "FT").getD f 0 = P.ft f := by
    rw [List.getD_eq_getElem?_getD, hC.ft f hfW]; rfl
  have hstk : Pfx (r.reverse ++ [f]) (σ.arrs "STK") := by
    have := hA.stk; rw [hst] at this; simpa using this
  unfold bCall
  run_vcg
  all_goals try (first | (nrm; omega) | (nrm; rw [g1]; omega))
  nrm
  rw [g1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; rw [hFT]
  · nrm; rw [hsp]; simp
  · nrm; rw [hrp]; simp
  · nrm; exact hA.hp
  · nrm; exact hstk.left
  · nrm
    have := hA.rpc.push (k := σ.vars "rp") (by rw [hrp]; simp) (by omega) (σ.vars "pc" + 1)
    rw [hpc] at this ⊢
    simpa using this
  · nrm
    have := hA.rh.push (k := σ.vars "rp") (by rw [hrp]; simp) (by omega) (r.length - n)
    have e : σ.vars "sp" - 1 - σ.vars "oa" = r.length - n := by omega
    rw [e]
    simpa using this
  · nrm; exact hA.ha
  · nrm; exact hA.hb

/-! ## `ret` -/

theorem pfx_ret {r arr : List ℕ} {w h k : ℕ} (hs : Pfx (r.reverse ++ [w]) arr) (hk : k = min h r.length)
    (hlt : k < arr.length) : Pfx (w :: r.drop (r.length - h)).reverse (arr.set k w) := by
  have e1 : (w :: r.drop (r.length - h)).reverse = r.reverse.take h ++ [w] := by
    rw [List.reverse_cons, ← List.take_reverse]
  rw [e1]
  have hs' : Pfx (r.reverse.take h ++ (r.reverse.drop h ++ [w])) arr := by
    rw [← List.append_assoc, List.take_append_drop]; exact hs
  exact hs'.write (by simp [hk]) hlt w

theorem abs_ret {P : Prog} {W Bi : ℕ} {s : St} {σ σ' : Env} (hA : Abs s σ) (hC : Cst P W Bi σ)
    {w : ℕ} {r : List ℕ} {pc' h : ℕ} {rs : List (ℕ × ℕ)} (hst : s.stk = w :: r)
    (hret : s.ret = (pc', h) :: rs) (hlt : min h r.length < W + 1)
    (e1 : σ'.vars "pc" = pc') (e2 : σ'.vars "sp" = min h r.length + 1) (e3 : σ'.vars "rp" = rs.length)
    (e4 : σ'.vars "hp" = s.heap.length)
    (e5 : σ'.arrs "STK" = (σ.arrs "STK").set (min h r.length) w)
    (e6 : σ'.arrs "RETPC" = σ.arrs "RETPC") (e7 : σ'.arrs "RETH" = σ.arrs "RETH")
    (e8 : σ'.arrs "HA" = σ.arrs "HA") (e9 : σ'.arrs "HB" = σ.arrs "HB") :
    Abs ⟨pc', w :: r.drop (r.length - h), rs, s.heap⟩ σ' := by
  have hl : (σ.arrs "STK").length = W + 1 := hC.len "STK" (by simp [arrNames])
  have hstk : Pfx (r.reverse ++ [w]) (σ.arrs "STK") := by
    have := hA.stk; rw [hst] at this; simpa using this
  have hrpc : Pfx ((s.ret.reverse.map Prod.fst)) (σ.arrs "RETPC") := hA.rpc
  have hrh : Pfx ((s.ret.reverse.map Prod.snd)) (σ.arrs "RETH") := hA.rh
  rw [hret] at hrpc hrh
  simp only [List.reverse_cons, List.map_append] at hrpc hrh
  refine ⟨e1, ?_, e3, e4, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e2]; simp; omega
  · rw [e5]; exact pfx_ret hstk rfl (by omega)
  · rw [e6]; have := hrpc.left; simpa using this
  · rw [e7]; have := hrh.left; simpa using this
  · rw [e8]; exact hA.ha
  · rw [e9]; exact hA.hb

theorem core_ret : Core bRet 40 .ret := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨w, r, pc', h, rs, hst, hret, rfl⟩ := inv_ret hc hs
  obtain ⟨hwW, hsp, hspW, hl, g1⟩ := top_facts hA hC hB hst
  have hpW : pc' ≤ W := (hB.ret (pc', h) (by simp [hret])).1
  have hhW : h ≤ W := (hB.ret (pc', h) (by simp [hret])).2
  have hrpW : rs.length + 1 ≤ W := by have := hB.retLen; rw [hret] at this; simpa using this
  have hrp : σ.vars "rp" = rs.length + 1 := by rw [hA.rp, hret]; simp
  have hB18 := hC.bi
  have hpc := hA.pc
  have hlP : (σ.arrs "RETPC").length = W + 1 := hC.len "RETPC" (by simp [arrNames])
  have hlH : (σ.arrs "RETH").length = W + 1 := hC.len "RETH" (by simp [arrNames])
  have hRH : (σ.arrs "RETH").getD (σ.vars "rp" - 1) 0 = h := by
    rw [List.getD_eq_getElem?_getD]
    have : (σ.arrs "RETH")[σ.vars "rp" - 1]? = some h := by
      apply hA.rh.get
      rw [hret, show σ.vars "rp" - 1 = rs.length by omega]; simp
    rw [this]; rfl
  have hRPC : (σ.arrs "RETPC").getD (σ.vars "rp" - 1) 0 = pc' := by
    rw [List.getD_eq_getElem?_getD]
    have : (σ.arrs "RETPC")[σ.vars "rp" - 1]? = some pc' := by
      apply hA.rpc.get
      rw [hret, show σ.vars "rp" - 1 = rs.length by omega]; simp
    rw [this]; rfl
  have hstk : Pfx (r.reverse ++ [w]) (σ.arrs "STK") := by
    have := hA.stk; rw [hst] at this; simpa using this
  have hdrop : (r.drop (r.length - h)).length ≤ r.length := by simp
  have hNL : (w :: r.drop (r.length - h)).length ≤ W := by simpa using hB'.stkLen
  unfold bRet
  run_vcg
  all_goals try (first | (nrm; omega) | (nrm; rw [g1]; omega))
  all_goals refine abs_ret hA hC hst hret (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals nrm
  all_goals (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq, eq_self] at *)
  all_goals first
    | exact hRPC
    | exact hA.hp
    | omega
    | (rw [g1, hRH]; congr 1; omega)
    | (rw [g1]; congr 1; omega)

end Lax117284Proofs.Treewidth.Fun.VM.Ram

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMRamLoop` -/

section
/-!
# WP V2 (5): the dispatch loop

`refines_blkOp` collects the sixteen instruction lemmas; `turn_step` is one turn of `vmLoop` (fetch,
dispatch, execute) and `loop_run` runs the loop along a `StepsB` run, at cost `≤ 120 (n + 1) + 4`.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

theorem opc_le (i : Instr) : opc i ≤ 16 := by cases i <;> simp [opc]

/-- Every instruction is refined by the block of its opcode (`halt` vacuously: it never steps). -/
theorem refines_blkOp (i : Instr) : Refines (blkOp (opc i)) 40 i := by
  cases i with
  | halt =>
    intro P W Bi s s' σ hA hC hB hB' hc hs hf
    simp [Prog.step, hc] at hs
  | lit n => exact (core_lit n).refines (by decide)
  | var i => exact (core_var i).refines (by decide)
  | add => exact core_add.refines (by decide)
  | sub => exact core_sub.refines (by decide)
  | mul => exact core_mul.refines (by decide)
  | lt => exact core_lt.refines (by decide)
  | eq => exact core_eq.refines (by decide)
  | cons => exact core_cons.refines (by decide)
  | fst => exact core_fst.refines (by decide)
  | snd => exact core_snd.refines (by decide)
  | isNat => exact core_isNat.refines (by decide)
  | jz k => exact (core_jz k).refines (by decide)
  | jmp k => exact (core_jmp k).refines (by decide)
  | slide => exact core_slide.refines (by decide)
  | call n => exact (core_call n).refines (by decide)
  | ret => exact core_ret.refines (by decide)

/-! ## The dispatch chain -/

theorem dispatchFrom_run {Bi K : ℕ} :
    ∀ (f k : ℕ) (σ σ' : Env), k ≤ σ.vars "op" → σ.vars "op" ≤ k + f → k + f < Bi →
      Run Bi (blkOp (σ.vars "op")) σ σ' K → Run Bi (dispatchFrom k f) σ σ' (4 * f + K) := by
  intro f
  induction f with
  | zero =>
    intro k σ σ' h1 h2 h3 h
    have e : σ.vars "op" = k := by omega
    rw [e] at h
    simpa [dispatchFrom] using h
  | succ f ih =>
    intro k σ σ' h1 h2 h3 h
    have hop : σ.vars "op" < Bi := by omega
    have hk : k < Bi := by omega
    have hev : (Expr.var "op").evalB Bi σ = some (σ.vars "op") := RunStep.eval_var Bi σ "op" hop
    have hel : (Expr.lit k).evalB Bi σ = some k := RunStep.eval_lit Bi k σ hk
    by_cases hc : σ.vars "op" = k
    · have hb := RunStep.cond_eq_true Bi σ (V "op") (L k) _ _ hev hel hc
      rw [hc] at h
      have := Run.ite_true (d := dispatchFrom (k + 1) f) hb h
      simp only [dispatchFrom]
      exact this.mono (by (try simp) <;> omega)
    · have hb := RunStep.cond_eq_false Bi σ (V "op") (L k) _ _ hev hel hc
      have := Run.ite_false (c := blkOp k) hb (ih (k + 1) σ σ' (by omega) (by omega) (by omega) h)
      simp only [dispatchFrom]
      exact this.mono (by (try simp) <;> omega)

theorem dispatch_run {Bi K : ℕ} (hBi : 17 < Bi) {σ σ' : Env} (hop : σ.vars "op" ≤ 16)
    (h : Run Bi (blkOp (σ.vars "op")) σ σ' K) : Run Bi bDispatch σ σ' (4 * 16 + K) :=
  dispatchFrom_run 16 0 σ σ' (by omega) (by omega) (by omega) h

/-! ## Fetch -/

theorem fetch_run {P : Prog} {W Bi : ℕ} {s : St} {σ : Env} (hA : Abs s σ) (hC : Cst P W Bi σ)
    (hB : s.Bd W) :
    ∃ σ', Run Bi bFetch σ σ' 6 ∧
      σ' = (σ.setVar "op" (opc (P.code s.pc))).setVar "oa" (opa (P.code s.pc)) := by
  have hpc : σ.vars "pc" = s.pc := hA.pc
  have hpcW : s.pc ≤ W := hB.pc
  have g1 : (σ.arrs "OP").getD (σ.vars "pc") 0 = opc (P.code s.pc) := by
    rw [hpc, List.getD_eq_getElem?_getD, hC.op _ hpcW]; rfl
  have g2 : (σ.arrs "OA").getD (σ.vars "pc") 0 = opa (P.code s.pc) := by
    rw [hpc, List.getD_eq_getElem?_getD, hC.oa _ hpcW]; rfl
  have hl1 : (σ.arrs "OP").length = W + 1 := hC.len "OP" (by simp [arrNames])
  have hl2 : (σ.arrs "OA").length = W + 1 := hC.len "OA" (by simp [arrNames])
  have ho : opc (P.code s.pc) ≤ 16 := opc_le _
  have ha : opa (P.code s.pc) < Bi := hC.opa_lt _ hpcW
  have hB18 := hC.bi
  unfold bFetch
  run_vcg
  all_goals try (nrm; omega)
  nrm
  rw [g1, g2]

theorem abs_op_oa {s : St} {σ : Env} (hA : Abs s σ) (a b : ℕ) :
    Abs s ((σ.setVar "op" a).setVar "oa" b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; exact hA.pc
  · nrm; exact hA.sp
  · nrm; exact hA.rp
  · nrm; exact hA.hp
  · nrm; exact hA.stk
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm; exact hA.ha
  · nrm; exact hA.hb

/-! ## One turn of the loop -/

theorem turn_step {P : Prog} {W Bi : ℕ} {s s' : St} {σ : Env} (hA : Abs s σ) (hC : Cst P W Bi σ)
    (hB : s.Bd W) (hB' : s'.Bd W) (hs : P.step s = some s') (hrun : σ.vars "run" = 1) :
    ∃ σ', Run Bi bBody σ σ' 110 ∧ Abs s' σ' ∧ Cst P W Bi σ' ∧ σ'.vars "run" = 1 := by
  obtain ⟨σ1, hr1, e1⟩ := fetch_run hA hC hB
  obtain ⟨i, hi⟩ : ∃ i, P.code s.pc = i := ⟨_, rfl⟩
  rw [hi] at e1
  have hA1 : Abs s σ1 := by rw [e1]; exact abs_op_oa hA _ _
  have hC1 : Cst P W Bi σ1 := hC.of_run hr1 (by decide) (by decide) (by decide) (by decide)
  have hop : σ1.vars "op" = opc i := by rw [e1]; nrm
  have hF : Fetched σ1 i := ⟨by rw [e1]; nrm⟩
  have hrun1 : σ1.vars "run" = 1 := by rw [hr1.frame_var _ (by decide)]; exact hrun
  obtain ⟨σ2, hr2, hA2, hC2, hrun2⟩ := refines_blkOp i P W Bi s s' σ1 hA1 hC1 hB hB' hi hs hF
  have hd := dispatch_run (Bi := Bi) (K := 40) (by have := hC.bi; omega) (σ := σ1) (σ' := σ2)
    (by rw [hop]; exact opc_le i) (by rw [hop]; exact hr2)
  exact ⟨σ2, (hr1.seq hd).mono (by omega), hA2, hC2, by rw [hrun2, hrun1]⟩

theorem turn_halt {P : Prog} {W Bi : ℕ} {s : St} {σ : Env} (hA : Abs s σ) (hC : Cst P W Bi σ)
    (hB : s.Bd W) (hhalt : P.code s.pc = .halt) :
    ∃ σ', Run Bi bBody σ σ' 110 ∧ Abs s σ' ∧ Cst P W Bi σ' ∧ σ'.vars "run" = 0 := by
  obtain ⟨σ1, hr1, e1⟩ := fetch_run hA hC hB
  rw [hhalt] at e1
  have hA1 : Abs s σ1 := by rw [e1]; exact abs_op_oa hA _ _
  have hC1 : Cst P W Bi σ1 := hC.of_run hr1 (by decide) (by decide) (by decide) (by decide)
  have hop : σ1.vars "op" = 0 := by rw [e1]; simp [opc]
  obtain ⟨σ2, hr2, hA2, hC2, hrun2⟩ := halt_run hA1 hC1
  have hd := dispatch_run (Bi := Bi) (K := 4) (by have := hC.bi; omega) (σ := σ1) (σ' := σ2)
    (by rw [hop]; omega) (by rw [hop]; exact hr2)
  exact ⟨σ2, (hr1.seq hd).mono (by omega), hA2, hC2, hrun2⟩

/-! ## The loop -/

theorem run_while_step {B : ℕ} {b : Cond} {c : Com} {σ σ1 σ2 : Env} {K1 K2 : ℕ}
    (hb : b.evalB B σ = some true) (h1 : Run B c σ σ1 K1) (h2 : Run B (.while b c) σ1 σ2 K2) :
    Run B (.while b c) σ σ2 (1 + b.size + K1 + K2) := by
  obtain ⟨k1, hk1, hbs1⟩ := h1
  obtain ⟨k2, hk2, hbs2⟩ := h2
  exact ⟨1 + b.size + k1 + k2, by omega, .while_true hb hbs1 hbs2⟩

theorem run_cond_true {Bi : ℕ} {σ : Env} (hB : 1 < Bi) (h : σ.vars "run" = 1) (hr : σ.vars "run" < Bi) :
    (Cond.eq (V "run") (L 1)).evalB Bi σ = some true :=
  RunStep.cond_eq_true Bi σ (V "run") (L 1) _ _ (RunStep.eval_var Bi σ "run" hr)
    (RunStep.eval_lit Bi 1 σ hB) h

theorem run_cond_false {Bi : ℕ} {σ : Env} (hB : 1 < Bi) (h : σ.vars "run" = 0) :
    (Cond.eq (V "run") (L 1)).evalB Bi σ = some false :=
  RunStep.cond_eq_false Bi σ (V "run") (L 1) _ _ (RunStep.eval_var Bi σ "run" (by omega))
    (RunStep.eval_lit Bi 1 σ hB) (by omega)

/-- **The loop.**  Along a bounded run `s → … → s'` ending at a `halt`, `vmLoop` started on a representation
of `s` (with `run = 1`) runs to a representation of `s'` with `run = 0`, at cost `≤ 120 (n + 1) + 4`. -/
theorem loop_run {P : Prog} {W Bi n : ℕ} {s s' : St} (h : StepsB P W n s s')
    (hhalt : P.code s'.pc = .halt) :
    ∀ σ, Abs s σ → Cst P W Bi σ → σ.vars "run" = 1 →
      ∃ σ', Run Bi vmLoop σ σ' (120 * (n + 1) + 4) ∧ Abs s' σ' ∧ Cst P W Bi σ' ∧ σ'.vars "run" = 0 := by
  induction h with
  | refl hb =>
    intro σ hA hC hrun
    have hB1 : 1 < Bi := by have := hC.bi; omega
    obtain ⟨σ1, hr, hA1, hC1, hrun1⟩ := turn_halt hA hC hb hhalt
    have hw := run_while_step (run_cond_true hB1 hrun (by omega)) hr
      (Run.while_false (c := bBody) (run_cond_false hB1 hrun1))
    exact ⟨σ1, by simpa [vmLoop] using hw.mono (by simp), hA1, hC1, hrun1⟩
  | @step s0 s1 s2 m hb hs hrest ih =>
    intro σ hA hC hrun
    have hB1 : 1 < Bi := by have := hC.bi; omega
    obtain ⟨σ1, hr, hA1, hC1, hrun1⟩ := turn_step hA hC hb hrest.bd_start hs hrun
    obtain ⟨σ2, hr2, hA2, hC2, hrun2⟩ := ih hhalt σ1 hA1 hC1 hrun1
    have hw := run_while_step (run_cond_true hB1 hrun (by omega)) hr hr2
    exact ⟨σ2, by simpa [vmLoop] using hw.mono (by simp; omega), hA2, hC2, hrun2⟩

end Lax117284Proofs.Treewidth.Fun.VM.Ram

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMCompile` -/

section
/-!
# WP V1 (2): the compiler `Tm → bytecode` and the assembled program

De Bruijn variables are resolved at compile time by a *depth function* `dep : ℕ → ℕ`: variable `i` of the
current environment lives at depth `dep i` of the value stack (0 = top).  A function body starts with
`dep = id` (its `k` arguments are on top of the stack, argument 0 on top); evaluating a sub-term with `j` more
cells on the stack shifts the depths by `j`; `letE` binds the new variable at depth 0.  Arguments of a call are
evaluated *last to first*, so that the argument list ends up on the stack with argument 0 on top.

Code of a function: `compile id body ++ [ret]`.  Program: `[lit main, call k, halt] ++` the functions `0 … N-1`
in order; `ft f` is the address of the code of `f`.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM

def shiftDep (k : ℕ) (dep : ℕ → ℕ) : ℕ → ℕ := fun i => dep i + k

def letDep (dep : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => dep i + 1

mutual
/-- Code of a term under the depth function `dep`; it leaves the value on top of the stack. -/
def compile (dep : ℕ → ℕ) : Tm → List Instr
  | .lit n => [.lit n]
  | .var i => [.var (dep i)]
  | .add a b => compile dep a ++ (compile (shiftDep 1 dep) b ++ [.add])
  | .sub a b => compile dep a ++ (compile (shiftDep 1 dep) b ++ [.sub])
  | .mul a b => compile dep a ++ (compile (shiftDep 1 dep) b ++ [.mul])
  | .lt a b => compile dep a ++ (compile (shiftDep 1 dep) b ++ [.lt])
  | .eq a b => compile dep a ++ (compile (shiftDep 1 dep) b ++ [.eq])
  | .cons a b => compile dep a ++ (compile (shiftDep 1 dep) b ++ [.cons])
  | .fst a => compile dep a ++ [.fst]
  | .snd a => compile dep a ++ [.snd]
  | .isNat a => compile dep a ++ [.isNat]
  | .ite c t e =>
    compile dep c ++ (Instr.jz ((compile dep t).length + 1) :: (compile dep t ++
      (Instr.jmp (compile dep e).length :: compile dep e)))
  | .letE a b => compile dep a ++ (compile (letDep dep) b ++ [.slide])
  | .call f args => compileArgs dep args ++ [.lit f, .call args.length]
  | .callv ft args =>
    compileArgs dep args ++ (compile (shiftDep args.length dep) ft ++ [.call args.length])
/-- Code of an argument list: last argument first, leaving the arguments on the stack, argument 0 on top. -/
def compileArgs (dep : ℕ → ℕ) : List Tm → List Instr
  | [] => []
  | t :: ts => compileArgs dep ts ++ compile (shiftDep ts.length dep) t
end

/-- The code of the table entry `f`: its body followed by `ret`; `halt` if `f` is not in the table. -/
def funCode (Δ : ℕ → Option Tm) (f : ℕ) : List Instr :=
  match Δ f with
  | some b => compile id b ++ [.ret]
  | none => [.halt]

/-- The driver: push the function id of `main`, call it with `k` arguments already on the stack, stop. -/
def stub (main k : ℕ) : List Instr := [.lit main, .call k, .halt]

/-- The program text for the functions `0 … N-1` with entry function `main` of arity `k`. -/
def progCode (Δ : ℕ → Option Tm) (N main k : ℕ) : List Instr :=
  stub main k ++ (List.range N).flatMap (funCode Δ)

/-- Address of the code of function `f` (functions are laid out in order after the 3-instruction stub). -/
def offset (Δ : ℕ → Option Tm) (f : ℕ) : ℕ := 3 + ((List.range f).map (fun g => (funCode Δ g).length)).sum

/-- The machine program of the table `Δ` (functions `< N`), entry `main` of arity `k`, number bound `B`. -/
def mkProg (Δ : ℕ → Option Tm) (N main k B : ℕ) : Prog where
  code := fun i => (progCode Δ N main k).getD i .halt
  ft := offset Δ
  len := (progCode Δ N main k).length
  B := B

/-- The list `l` sits in the code array of `P` at address `pc`. -/
def FitsAt (P : Prog) (pc : ℕ) (l : List Instr) : Prop :=
  pc + l.length ≤ P.len ∧ ∀ (i : ℕ) (h : i < l.length), P.code (pc + i) = l[i]

theorem FitsAt.append_left {P : Prog} {pc : ℕ} {l l' : List Instr} (h : FitsAt P pc (l ++ l')) :
    FitsAt P pc l := by
  refine ⟨by have := h.1; simp at this; omega, fun i hi => ?_⟩
  have := h.2 i (by simp; omega)
  rw [this]; simp [List.getElem_append_left hi]

theorem FitsAt.append_right {P : Prog} {pc : ℕ} {l l' : List Instr} (h : FitsAt P pc (l ++ l')) :
    FitsAt P (pc + l.length) l' := by
  refine ⟨by have := h.1; simp at this; omega, fun i hi => ?_⟩
  have := h.2 (l.length + i) (by simp; omega)
  rw [show pc + l.length + i = pc + (l.length + i) by omega, this]
  simp [List.getElem_append_right]

theorem FitsAt.tail {P : Prog} {pc : ℕ} {i : Instr} {l : List Instr} (h : FitsAt P pc (i :: l)) :
    FitsAt P (pc + 1) l := by
  have := FitsAt.append_right (l := [i]) (l' := l) (by simpa using h)
  simpa using this

theorem FitsAt.head {P : Prog} {pc : ℕ} {i : Instr} {l : List Instr} (h : FitsAt P pc (i :: l)) :
    P.code pc = i := by
  exact h.2 0 (by simp)

/-- The code array is the given list, the last element being followed by `halt`. -/
theorem fitsAt_of_sublist (L pre seg post : List Instr) (hL : L = pre ++ seg ++ post) (B : ℕ)
    (ft : ℕ → ℕ) :
    FitsAt { code := fun i => L.getD i .halt, ft := ft, len := L.length, B := B } pre.length seg := by
  subst hL
  refine ⟨by simp, fun i hi => ?_⟩
  show (pre ++ seg ++ post).getD (pre.length + i) .halt = seg[i]
  rw [List.getD_eq_getElem?_getD]
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simp [List.getElem?_append_left hi, hi]

/-- Every function of the table lies in the assembled program at its offset. -/
theorem flatMap_split (Δ : ℕ → Option Tm) {N f : ℕ} (hf : f < N) :
    ∃ post, (List.range N).flatMap (funCode Δ) =
      (List.range f).flatMap (funCode Δ) ++ funCode Δ f ++ post := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases hlt : f < N
    · obtain ⟨post, h⟩ := ih hlt
      exact ⟨post ++ funCode Δ N, by simp [h]⟩
    · have : f = N := by omega
      subst this
      exact ⟨[], by simp⟩

theorem offset_eq (Δ : ℕ → Option Tm) (f : ℕ) :
    offset Δ f = 3 + ((List.range f).flatMap (funCode Δ)).length := by
  simp [offset, List.length_flatMap]

/-- The program contains the code of every function `f < N` at `ft f`. -/
theorem mkProg_fits (Δ : ℕ → Option Tm) {N f : ℕ} (hf : f < N) (main k B : ℕ) :
    FitsAt (mkProg Δ N main k B) ((mkProg Δ N main k B).ft f) (funCode Δ f) := by
  obtain ⟨post, h⟩ := flatMap_split Δ hf
  have := fitsAt_of_sublist (progCode Δ N main k) (stub main k ++ (List.range f).flatMap (funCode Δ))
    (funCode Δ f) post (by simp [progCode, h]) B (offset Δ)
  have hoff : offset Δ f = (stub main k ++ (List.range f).flatMap (funCode Δ)).length := by
    rw [offset_eq]; simp [stub]; omega
  show FitsAt _ (offset Δ f) _
  rw [hoff]; exact this

/-- The stub at address 0. -/
theorem mkProg_stub (Δ : ℕ → Option Tm) (N main k B : ℕ) :
    FitsAt (mkProg Δ N main k B) 0 (stub main k) := by
  have := fitsAt_of_sublist (progCode Δ N main k) [] (stub main k) ((List.range N).flatMap (funCode Δ))
    (by simp [progCode]) B (offset Δ)
  simpa [mkProg] using this

end Lax117284Proofs.Treewidth.Fun.VM

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMSim` -/

section
/-!
# WP V1 (3): simulation `Ev ⇒ VM run` — infrastructure and the simple cases

`SimEv P ρ t v c` : whenever the code of `t` sits at the pc of a state `s` whose stack holds (a representation of)
the environment `ρ` according to the depth function `dep`, and `s` is inside the word budget `Cfg`, the machine
runs in at most `3c` steps, all states within the word bound `W`, to the state with the pc after the code, one
more value on the stack (a representation of `v`), the return stack unchanged and the heap extended by at most
`c` cells.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM

/-! ## environments on the stack -/

/-- The environment `ρ` is on the stack `stk` (variable `i` at depth `dep i`), represented in the heap `H`. -/
def Env (B : ℕ) (H : List (ℕ × ℕ)) (dep : ℕ → ℕ) (ρ : List Val) (stk : List ℕ) : Prop :=
  ∀ i x, ρ[i]? = some x → ∃ w, stk[dep i]? = some w ∧ Rep B H w x

theorem Env.mono {B : ℕ} {H H' : List (ℕ × ℕ)} {dep ρ stk} (hH : HExt H H') (h : Env B H dep ρ stk) :
    Env B H' dep ρ stk := by
  intro i x hi
  obtain ⟨w, hw, hr⟩ := h i x hi
  exact ⟨w, hw, hr.mono hH⟩

theorem Env.push {B : ℕ} {H : List (ℕ × ℕ)} {dep ρ stk} (w : ℕ) (h : Env B H dep ρ stk) :
    Env B H (shiftDep 1 dep) ρ (w :: stk) := by
  intro i x hi
  obtain ⟨w', hw, hr⟩ := h i x hi
  exact ⟨w', by simpa [shiftDep] using hw, hr⟩

theorem Env.shift {B : ℕ} {H : List (ℕ × ℕ)} {dep ρ stk} (ws : List ℕ) (h : Env B H dep ρ stk) :
    Env B H (shiftDep ws.length dep) ρ (ws ++ stk) := by
  intro i x hi
  obtain ⟨w', hw, hr⟩ := h i x hi
  refine ⟨w', ?_, hr⟩
  rw [shiftDep, List.getElem?_append_right (by omega)]
  simpa using hw

theorem Env.letE {B : ℕ} {H : List (ℕ × ℕ)} {dep ρ stk} {u : Val} {w : ℕ} (hw : Rep B H w u)
    (h : Env B H dep ρ stk) : Env B H (letDep dep) (u :: ρ) (w :: stk) := by
  intro i x hi
  cases i with
  | zero =>
    simp at hi; subst hi
    exact ⟨w, by simp [letDep], hw⟩
  | succ i =>
    simp at hi
    obtain ⟨w', hw', hr⟩ := h i x hi
    exact ⟨w', by simpa [letDep] using hw', hr⟩

theorem Env.of_repl {B : ℕ} {H : List (ℕ × ℕ)} {ws : List ℕ} {vs : List Val} (h : RepL B H ws vs)
    (stk : List ℕ) : Env B H id vs (ws ++ stk) := by
  intro i x hi
  obtain ⟨w, hw, hr⟩ := h.get hi
  refine ⟨w, ?_, hr⟩
  have := (List.getElem?_eq_some_iff.mp hw).1
  rw [id, List.getElem?_append_left this]; exact hw

/-! ## the word budget and the conclusion -/

/-- Word budget for running a derivation of cost `c` from `s` inside the bound `W`. -/
structure Cfg (P : Prog) (W : ℕ) (s : St) (c : ℕ) : Prop where
  bd : s.Bd W
  len : P.len ≤ W
  heap : P.B + s.heap.length + c ≤ W
  stk : s.stk.length + 3 * c ≤ W
  ret : s.ret.length + 3 * c ≤ W

theorem Cfg.sub {P : Prog} {W : ℕ} {s : St} {c c' : ℕ} (h : Cfg P W s c) (hc : c' ≤ c) : Cfg P W s c' :=
  ⟨h.bd, h.len, by have := h.heap; omega, by have := h.stk; omega, by have := h.ret; omega⟩

/-- Passing from the state before a sub-run of cost `c₁` to the state after it (`s₁`): the budget for the
remaining cost `c₂`. -/
theorem Cfg.next {P : Prog} {W : ℕ} {s s₁ : St} {c c₁ c₂ : ℕ} (h : Cfg P W s c) (hc : c₁ + c₂ + 1 ≤ c)
    (hb : s₁.Bd W) (hheap : s₁.heap.length ≤ s.heap.length + c₁)
    (hstk : s₁.stk.length ≤ s.stk.length + c₁ + 1) (hret : s₁.ret.length ≤ s.ret.length) :
    Cfg P W s₁ c₂ :=
  ⟨hb, h.len, by have := h.heap; omega, by have := h.stk; omega, by have := h.ret; omega⟩

def Post (P : Prog) (W : ℕ) (s : St) (endpc : ℕ) (v : Val) (c : ℕ) : Prop :=
  ∃ n ≤ 3 * c, ∃ (w : ℕ) (H' : List (ℕ × ℕ)),
    StepsB P W n s ⟨endpc, w :: s.stk, s.ret, H'⟩ ∧ HExt s.heap H' ∧ Rep P.B H' w v ∧
      H'.length ≤ s.heap.length + c

def PostL (P : Prog) (W : ℕ) (s : St) (endpc : ℕ) (ts : List Tm) (vs : List Val) (c : ℕ) : Prop :=
  ∃ n ≤ 3 * c, ∃ (ws : List ℕ) (H' : List (ℕ × ℕ)),
    StepsB P W n s ⟨endpc, ws ++ s.stk, s.ret, H'⟩ ∧ HExt s.heap H' ∧ RepL P.B H' ws vs ∧
      H'.length ≤ s.heap.length + c ∧ ws.length = ts.length

/-- The simulation statement for a term. -/
def SimEv (P : Prog) (ρ : List Val) (t : Tm) (v : Val) (c : ℕ) : Prop :=
  ∀ (dep : ℕ → ℕ) (W : ℕ) (s : St), FitsAt P s.pc (compile dep t) → Env P.B s.heap dep ρ s.stk →
    Cfg P W s c → Post P W s (s.pc + (compile dep t).length) v c

/-- The simulation statement for an argument list. -/
def SimEvL (P : Prog) (ρ : List Val) (ts : List Tm) (vs : List Val) (c : ℕ) : Prop :=
  ∀ (dep : ℕ → ℕ) (W : ℕ) (s : St), FitsAt P s.pc (compileArgs dep ts) → Env P.B s.heap dep ρ s.stk →
    Cfg P W s c → PostL P W s (s.pc + (compileArgs dep ts).length) ts vs c

/-! ## boundedness of updated states -/

theorem St.Bd.setStk {W : ℕ} {s : St} (h : s.Bd W) {pc : ℕ} {stk : List ℕ} (hpc : pc ≤ W)
    (hs : ∀ w ∈ stk, w ≤ W) (hl : stk.length ≤ W) : St.Bd W { s with pc := pc, stk := stk } :=
  ⟨hpc, hl, hs, h.retLen, h.ret, h.heapLen, h.heap⟩

theorem St.Bd.setPc {W : ℕ} {s : St} (h : s.Bd W) {pc : ℕ} (hpc : pc ≤ W) : St.Bd W { s with pc := pc } :=
  ⟨hpc, h.stkLen, h.stk, h.retLen, h.ret, h.heapLen, h.heap⟩

theorem St.Bd.cons {W : ℕ} {s : St} (h : s.Bd W) {pc w : ℕ} (hpc : pc ≤ W) (hw : w ≤ W)
    (hl : s.stk.length + 1 ≤ W) : St.Bd W { s with pc := pc, stk := w :: s.stk } :=
  h.setStk hpc (by simpa using ⟨hw, h.stk⟩) (by simpa using hl)

/-! ## single-step lemmas -/

theorem step_lit {P : Prog} {s : St} {n : ℕ} (h : P.code s.pc = .lit n) :
    P.step s = some ⟨s.pc + 1, n :: s.stk, s.ret, s.heap⟩ := by simp [Prog.step, h]

theorem step_var {P : Prog} {s : St} {i w : ℕ} (h : P.code s.pc = .var i) (hw : s.stk[i]? = some w) :
    P.step s = some ⟨s.pc + 1, w :: s.stk, s.ret, s.heap⟩ := by simp [Prog.step, h, hw]

theorem step_add {P : Prog} {s : St} (h : P.code s.pc = .add) (x y : ℕ) (r : List ℕ)
    (hs : s.stk = y :: x :: r) : P.step s = some ⟨s.pc + 1, (x + y) :: r, s.ret, s.heap⟩ := by
  simp [Prog.step, h, hs]
theorem step_sub {P : Prog} {s : St} (h : P.code s.pc = .sub) (x y : ℕ) (r : List ℕ)
    (hs : s.stk = y :: x :: r) : P.step s = some ⟨s.pc + 1, (x - y) :: r, s.ret, s.heap⟩ := by
  simp [Prog.step, h, hs]
theorem step_mul {P : Prog} {s : St} (h : P.code s.pc = .mul) (x y : ℕ) (r : List ℕ)
    (hs : s.stk = y :: x :: r) : P.step s = some ⟨s.pc + 1, (x * y) :: r, s.ret, s.heap⟩ := by
  simp [Prog.step, h, hs]
theorem step_lt {P : Prog} {s : St} (h : P.code s.pc = .lt) (x y : ℕ) (r : List ℕ)
    (hs : s.stk = y :: x :: r) :
    P.step s = some ⟨s.pc + 1, (if x < y then 1 else 0) :: r, s.ret, s.heap⟩ := by
  simp [Prog.step, h, hs]
theorem step_eq {P : Prog} {s : St} (h : P.code s.pc = .eq) (x y : ℕ) (r : List ℕ)
    (hs : s.stk = y :: x :: r) :
    P.step s = some ⟨s.pc + 1, (if x = y then 1 else 0) :: r, s.ret, s.heap⟩ := by
  simp [Prog.step, h, hs]

theorem step_cons {P : Prog} {s : St} (h : P.code s.pc = .cons) (x y : ℕ) (r : List ℕ)
    (hs : s.stk = y :: x :: r) :
    P.step s = some ⟨s.pc + 1, (P.B + s.heap.length) :: r, s.ret, s.heap ++ [(x, y)]⟩ := by
  simp [Prog.step, h, hs]

theorem step_fst {P : Prog} {s : St} (h : P.code s.pc = .fst) (p a b : ℕ) (r : List ℕ)
    (hs : s.stk = (P.B + p) :: r) (hp : s.heap[p]? = some (a, b)) :
    P.step s = some ⟨s.pc + 1, a :: r, s.ret, s.heap⟩ := by
  simp [Prog.step, h, hs, hp]
theorem step_snd {P : Prog} {s : St} (h : P.code s.pc = .snd) (p a b : ℕ) (r : List ℕ)
    (hs : s.stk = (P.B + p) :: r) (hp : s.heap[p]? = some (a, b)) :
    P.step s = some ⟨s.pc + 1, b :: r, s.ret, s.heap⟩ := by
  simp [Prog.step, h, hs, hp]

theorem step_isNat {P : Prog} {s : St} (h : P.code s.pc = .isNat) (w : ℕ) (r : List ℕ)
    (hs : s.stk = w :: r) :
    P.step s = some ⟨s.pc + 1, (if w < P.B then 1 else 0) :: r, s.ret, s.heap⟩ := by
  simp [Prog.step, h, hs]

theorem step_jz {P : Prog} {s : St} {k : ℕ} (h : P.code s.pc = .jz k) (w : ℕ) (r : List ℕ)
    (hs : s.stk = w :: r) :
    P.step s = some ⟨if w = 0 then s.pc + 1 + k else s.pc + 1, r, s.ret, s.heap⟩ := by
  simp [Prog.step, h, hs]

theorem step_jmp {P : Prog} {s : St} {k : ℕ} (h : P.code s.pc = .jmp k) :
    P.step s = some ⟨s.pc + 1 + k, s.stk, s.ret, s.heap⟩ := by
  simp [Prog.step, h]

theorem step_slide {P : Prog} {s : St} (h : P.code s.pc = .slide) (v u : ℕ) (r : List ℕ)
    (hs : s.stk = v :: u :: r) : P.step s = some ⟨s.pc + 1, v :: r, s.ret, s.heap⟩ := by
  simp [Prog.step, h, hs]

theorem step_call {P : Prog} {s : St} {n : ℕ} (h : P.code s.pc = .call n) (f : ℕ) (r : List ℕ)
    (hs : s.stk = f :: r) :
    P.step s = some ⟨P.ft f, r, (s.pc + 1, r.length - n) :: s.ret, s.heap⟩ := by
  simp [Prog.step, h, hs]

theorem step_ret {P : Prog} {s : St} (h : P.code s.pc = .ret) (w : ℕ) (r : List ℕ) (pc' hh : ℕ)
    (rs : List (ℕ × ℕ)) (hs : s.stk = w :: r) (hr : s.ret = (pc', hh) :: rs) :
    P.step s = some ⟨pc', w :: r.drop (r.length - hh), rs, s.heap⟩ := by
  simp [Prog.step, h, hs, hr]

end Lax117284Proofs.Treewidth.Fun.VM

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMSimCases` -/

section
/-!
# WP V1 (4): simulation, the cases other than calls
-/

namespace Lax117284Proofs.Treewidth.Fun.VM

variable {P : Prog}

theorem sim_lit {ρ : List Val} {n : ℕ} (hn : n < P.B) : SimEv P ρ (.lit n) (.nat n) 1 := by
  intro dep W s hfit henv hcfg
  have e : (compile dep (.lit n)).length = 1 := by simp [compile]
  have hfit' : FitsAt P s.pc [Instr.lit n] := by simpa [compile] using hfit
  have hlen : s.pc + 1 ≤ P.len := by simpa using hfit'.1
  have hB := hcfg.heap
  have hstk := hcfg.stk
  have hL := hcfg.len
  rw [e]
  refine ⟨1, by omega, n, s.heap, StepsB.one hcfg.bd (step_lit hfit'.head) ?_, HExt.refl _, .nat hn,
    by omega⟩
  exact hcfg.bd.cons (by omega) (by omega) (by omega)

theorem sim_var {ρ : List Val} {i : ℕ} {v : Val} (h : ρ[i]? = some v) : SimEv P ρ (.var i) v 1 := by
  intro dep W s hfit henv hcfg
  have e : (compile dep (.var i)).length = 1 := by simp [compile]
  have hfit' : FitsAt P s.pc [Instr.var (dep i)] := by simpa [compile] using hfit
  have hlen : s.pc + 1 ≤ P.len := by simpa using hfit'.1
  have hstk := hcfg.stk
  have hL := hcfg.len
  obtain ⟨w, hw, hr⟩ := henv i v h
  have hwW : w ≤ W := hcfg.bd.stk w (List.mem_of_getElem? hw)
  rw [e]
  refine ⟨1, by omega, w, s.heap, StepsB.one hcfg.bd (step_var hfit'.head hw) ?_, HExt.refl _, hr,
    by omega⟩
  exact hcfg.bd.cons (by omega) hwW (by omega)

theorem bin_sim {ρ : List Val} {a b t : Tm} {ins : Instr} {op : ℕ → ℕ → ℕ} {m n c₁ c₂ : ℕ}
    (hcode : ∀ dep, compile dep t = compile dep a ++ (compile (shiftDep 1 dep) b ++ [ins]))
    (hins : ∀ (s : St) (x y : ℕ) (r : List ℕ), P.code s.pc = ins → s.stk = y :: x :: r →
      P.step s = some ⟨s.pc + 1, op x y :: r, s.ret, s.heap⟩)
    (hres : m < P.B → n < P.B → op m n < P.B)
    (ha : SimEv P ρ a (.nat m) c₁) (hb : SimEv P ρ b (.nat n) c₂) :
    SimEv P ρ t (.nat (op m n)) (c₁ + c₂ + 1) := by
  intro dep W s hfit henv hcfg
  rw [hcode] at hfit ⊢
  have hfa : FitsAt P s.pc (compile dep a) := hfit.append_left
  have hrest := hfit.append_right
  have hfb : FitsAt P (s.pc + (compile dep a).length) (compile (shiftDep 1 dep) b) := hrest.append_left
  have hfi : FitsAt P (s.pc + (compile dep a).length + (compile (shiftDep 1 dep) b).length) [ins] :=
    hrest.append_right
  have hlen := hfit.1
  have e : s.pc + (compile dep a ++ (compile (shiftDep 1 dep) b ++ [ins])).length =
      s.pc + (compile dep a).length + (compile (shiftDep 1 dep) b).length + 1 := by simp; omega
  rw [e]
  simp only [List.length_append, List.length_singleton] at hlen
  have hL := hcfg.len
  have hB := hcfg.heap
  have hstk := hcfg.stk
  obtain ⟨n₁, hn₁, w₁, H₁, hs₁, hx₁, hr₁, hh₁⟩ := ha dep W s hfa henv (hcfg.sub (by omega))
  have hc₂ : Cfg P W ⟨s.pc + (compile dep a).length, w₁ :: s.stk, s.ret, H₁⟩ c₂ :=
    hcfg.next (c₁ := c₁) (by omega) hs₁.bd_end hh₁ (by simp) (by simp)
  obtain ⟨n₂, hn₂, w₂, H₂, hs₂, hx₂, hr₂, hh₂⟩ := hb (shiftDep 1 dep) W
    ⟨s.pc + (compile dep a).length, w₁ :: s.stk, s.ret, H₁⟩ hfb ((henv.mono hx₁).push w₁) hc₂
  dsimp only at hs₂ hh₂ hx₂
  obtain ⟨rfl, hm⟩ := hr₁.nat_inv
  obtain ⟨rfl, hn⟩ := hr₂.nat_inv
  have hstep := hins ⟨s.pc + (compile dep a).length + (compile (shiftDep 1 dep) b).length,
    w₂ :: w₁ :: s.stk, s.ret, H₂⟩ w₁ w₂ s.stk hfi.head rfl
  have hbd := hs₂.bd_end
  have hres' : op w₁ w₂ ≤ W := by have := hres hm hn; omega
  refine ⟨n₁ + (n₂ + 1), by omega, op w₁ w₂, H₂, hs₁.trans (hs₂.trans (StepsB.one hbd hstep ?_)),
    hx₁.trans hx₂, .nat (hres hm hn), by omega⟩
  refine hbd.setStk (by omega) ?_ (by simp; omega)
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hres'
  · exact hbd.stk x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))

theorem sim_cons {ρ : List Val} {a b : Tm} {u v : Val} {c₁ c₂ : ℕ}
    (ha : SimEv P ρ a u c₁) (hb : SimEv P ρ b v c₂) :
    SimEv P ρ (.cons a b) (.cons u v) (c₁ + c₂ + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfa : FitsAt P s.pc (compile dep a) := hfit.append_left
  have hrest := hfit.append_right
  have hfb : FitsAt P (s.pc + (compile dep a).length) (compile (shiftDep 1 dep) b) := hrest.append_left
  have hfi : FitsAt P (s.pc + (compile dep a).length + (compile (shiftDep 1 dep) b).length)
      [Instr.cons] := hrest.append_right
  have hlen := hfit.1
  have e : s.pc + (compile dep a ++ (compile (shiftDep 1 dep) b ++ [Instr.cons])).length =
      s.pc + (compile dep a).length + (compile (shiftDep 1 dep) b).length + 1 := by simp; omega
  rw [e]
  simp only [List.length_append, List.length_singleton] at hlen
  have hL := hcfg.len
  have hB := hcfg.heap
  have hstk := hcfg.stk
  obtain ⟨n₁, hn₁, w₁, H₁, hs₁, hx₁, hr₁, hh₁⟩ := ha dep W s hfa henv (hcfg.sub (by omega))
  have hc₂ : Cfg P W ⟨s.pc + (compile dep a).length, w₁ :: s.stk, s.ret, H₁⟩ c₂ :=
    hcfg.next (c₁ := c₁) (by omega) hs₁.bd_end hh₁ (by simp) (by simp)
  obtain ⟨n₂, hn₂, w₂, H₂, hs₂, hx₂, hr₂, hh₂⟩ := hb (shiftDep 1 dep) W
    ⟨s.pc + (compile dep a).length, w₁ :: s.stk, s.ret, H₁⟩ hfb ((henv.mono hx₁).push w₁) hc₂
  dsimp only at hs₂ hh₂ hx₂
  have hstep := step_cons (P := P) (s := ⟨s.pc + (compile dep a).length +
    (compile (shiftDep 1 dep) b).length, w₂ :: w₁ :: s.stk, s.ret, H₂⟩) hfi.head w₁ w₂ s.stk rfl
  have hbd := hs₂.bd_end
  have hw₁ : w₁ ≤ W := hbd.stk w₁ (by simp)
  have hw₂ : w₂ ≤ W := hbd.stk w₂ (by simp)
  refine ⟨n₁ + (n₂ + 1), by omega, P.B + H₂.length, H₂ ++ [(w₁, w₂)],
    hs₁.trans (hs₂.trans (StepsB.one hbd hstep ?_)), (hx₁.trans hx₂).trans (HExt.snoc _ _),
    .cons (p := H₂.length) (by simp) ((hr₁.mono hx₂).mono (HExt.snoc _ _)) (hr₂.mono (HExt.snoc _ _)),
    by simp; omega⟩
  refine ⟨by dsimp only; omega, by simp; omega, ?_, hbd.retLen, hbd.ret, by simp; omega, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · exact hbd.stk x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hbd.heap p hp
    · simp at hp; subst hp; exact ⟨hw₁, hw₂⟩

theorem sim_fst {ρ : List Val} {a : Tm} {u v : Val} {c : ℕ} (ha : SimEv P ρ a (.cons u v) c) :
    SimEv P ρ (.fst a) u (c + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfa : FitsAt P s.pc (compile dep a) := hfit.append_left
  have hfi : FitsAt P (s.pc + (compile dep a).length) [Instr.fst] := hfit.append_right
  have hlen := hfit.1
  simp only [List.length_append, List.length_singleton] at hlen ⊢
  have hL := hcfg.len
  have hstk := hcfg.stk
  obtain ⟨n₁, hn₁, w, H₁, hs₁, hx₁, hr₁, hh₁⟩ := ha dep W s hfa henv (hcfg.sub (by omega))
  obtain ⟨p, a', b', rfl, hp, hra, hrb⟩ := hr₁.cons_inv
  have hbd := hs₁.bd_end
  have hstep := step_fst (P := P) (s := ⟨s.pc + (compile dep a).length, (P.B + p) :: s.stk, s.ret, H₁⟩)
    hfi.head p a' b' s.stk rfl hp
  have ha'W : a' ≤ W := (hbd.heap (a', b') (List.mem_of_getElem? hp)).1
  refine ⟨n₁ + 1, by omega, a', H₁, hs₁.trans (StepsB.one hbd hstep ?_), hx₁, hra, by omega⟩
  refine hbd.setStk (by omega) ?_ (by simp; omega)
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ha'W
  · exact hbd.stk x (List.mem_cons_of_mem _ hx)

theorem sim_snd {ρ : List Val} {a : Tm} {u v : Val} {c : ℕ} (ha : SimEv P ρ a (.cons u v) c) :
    SimEv P ρ (.snd a) v (c + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfa : FitsAt P s.pc (compile dep a) := hfit.append_left
  have hfi : FitsAt P (s.pc + (compile dep a).length) [Instr.snd] := hfit.append_right
  have hlen := hfit.1
  simp only [List.length_append, List.length_singleton] at hlen ⊢
  have hL := hcfg.len
  have hstk := hcfg.stk
  obtain ⟨n₁, hn₁, w, H₁, hs₁, hx₁, hr₁, hh₁⟩ := ha dep W s hfa henv (hcfg.sub (by omega))
  obtain ⟨p, a', b', rfl, hp, hra, hrb⟩ := hr₁.cons_inv
  have hbd := hs₁.bd_end
  have hstep := step_snd (P := P) (s := ⟨s.pc + (compile dep a).length, (P.B + p) :: s.stk, s.ret, H₁⟩)
    hfi.head p a' b' s.stk rfl hp
  have hb'W : b' ≤ W := (hbd.heap (a', b') (List.mem_of_getElem? hp)).2
  refine ⟨n₁ + 1, by omega, b', H₁, hs₁.trans (StepsB.one hbd hstep ?_), hx₁, hrb, by omega⟩
  refine hbd.setStk (by omega) ?_ (by simp; omega)
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hb'W
  · exact hbd.stk x (List.mem_cons_of_mem _ hx)

theorem sim_isNatT (hB : 2 ≤ P.B) {ρ : List Val} {a : Tm} {n c : ℕ} (ha : SimEv P ρ a (.nat n) c) :
    SimEv P ρ (.isNat a) (.nat 1) (c + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfa : FitsAt P s.pc (compile dep a) := hfit.append_left
  have hfi : FitsAt P (s.pc + (compile dep a).length) [Instr.isNat] := hfit.append_right
  have hlen := hfit.1
  simp only [List.length_append, List.length_singleton] at hlen ⊢
  have hL := hcfg.len
  have hstk := hcfg.stk
  have hHB := hcfg.heap
  obtain ⟨n₁, hn₁, w, H₁, hs₁, hx₁, hr₁, hh₁⟩ := ha dep W s hfa henv (hcfg.sub (by omega))
  obtain ⟨rfl, hn⟩ := hr₁.nat_inv
  have hbd := hs₁.bd_end
  have hstep := step_isNat (P := P) (s := ⟨s.pc + (compile dep a).length, w :: s.stk, s.ret, H₁⟩)
    hfi.head w s.stk rfl
  simp only [if_pos hn] at hstep
  refine ⟨n₁ + 1, by omega, 1, H₁, hs₁.trans (StepsB.one hbd hstep ?_), hx₁, .nat (by omega), by omega⟩
  refine hbd.setStk (by omega) ?_ (by simp; omega)
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · omega
  · exact hbd.stk x (List.mem_cons_of_mem _ hx)

theorem sim_isNatF (hB : 2 ≤ P.B) {ρ : List Val} {a : Tm} {u v : Val} {c : ℕ}
    (ha : SimEv P ρ a (.cons u v) c) : SimEv P ρ (.isNat a) (.nat 0) (c + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfa : FitsAt P s.pc (compile dep a) := hfit.append_left
  have hfi : FitsAt P (s.pc + (compile dep a).length) [Instr.isNat] := hfit.append_right
  have hlen := hfit.1
  simp only [List.length_append, List.length_singleton] at hlen ⊢
  have hL := hcfg.len
  have hstk := hcfg.stk
  have hHB := hcfg.heap
  obtain ⟨n₁, hn₁, w, H₁, hs₁, hx₁, hr₁, hh₁⟩ := ha dep W s hfa henv (hcfg.sub (by omega))
  obtain ⟨p, a', b', rfl, hp, hra, hrb⟩ := hr₁.cons_inv
  have hbd := hs₁.bd_end
  have hstep := step_isNat (P := P) (s := ⟨s.pc + (compile dep a).length, (P.B + p) :: s.stk, s.ret, H₁⟩)
    hfi.head (P.B + p) s.stk rfl
  simp only [if_neg (show ¬ (P.B + p < P.B) by omega)] at hstep
  refine ⟨n₁ + 1, by omega, 0, H₁, hs₁.trans (StepsB.one hbd hstep ?_), hx₁, .nat (by omega), by omega⟩
  refine hbd.setStk (by omega) ?_ (by simp; omega)
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · omega
  · exact hbd.stk x (List.mem_cons_of_mem _ hx)

end Lax117284Proofs.Treewidth.Fun.VM

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMSimCall` -/

section
/-!
# WP V1 (5): simulation of `ite`, `letE`, argument lists, calls; the main theorem `ev_sim`
-/

namespace Lax117284Proofs.Treewidth.Fun.VM

variable {P : Prog}

/-- `P` contains, for every function of the table, its code (followed by `ret`) at the address `ft f`; and
function ids are bounded by the code length (they are pushed as machine words). -/
def Prog.Real (P : Prog) (Δ : ℕ → Option Tm) : Prop :=
  ∀ f body, Δ f = some body → f ≤ P.len ∧ FitsAt P (P.ft f) (compile id body ++ [.ret])

theorem sim_iteT {ρ : List Val} {cnd t e : Tm} {n : ℕ} {v : Val} {c₁ c₂ : ℕ} (hn : n ≠ 0)
    (hc : SimEv P ρ cnd (.nat n) c₁) (ht : SimEv P ρ t v c₂) :
    SimEv P ρ (.ite cnd t e) v (c₁ + c₂ + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfc : FitsAt P s.pc (compile dep cnd) := hfit.append_left
  have hr1 := hfit.append_right
  have hjz := hr1.head
  have hr2 := hr1.tail
  have hft : FitsAt P (s.pc + (compile dep cnd).length + 1) (compile dep t) := hr2.append_left
  have hr3 := hr2.append_right
  have hjmp := hr3.head
  have hlen := hfit.1
  have e : s.pc + (compile dep cnd ++ (Instr.jz ((compile dep t).length + 1) ::
      (compile dep t ++ (Instr.jmp (compile dep e).length :: compile dep e)))).length =
      s.pc + (compile dep cnd).length + 1 + (compile dep t).length + 1 + (compile dep e).length := by
    simp; omega
  rw [e]
  simp only [List.length_append, List.length_cons] at hlen
  have hL := hcfg.len
  have hB := hcfg.heap
  have hstk := hcfg.stk
  have hret := hcfg.ret
  obtain ⟨n₁, hn₁, w₁, H₁, hs₁, hx₁, hr₁, hh₁⟩ := hc dep W s hfc henv (hcfg.sub (by omega))
  obtain ⟨rfl, hnB⟩ := hr₁.nat_inv
  have hbd := hs₁.bd_end
  have hstep := step_jz (P := P) (s := ⟨s.pc + (compile dep cnd).length, w₁ :: s.stk, s.ret, H₁⟩)
    hjz w₁ s.stk rfl
  simp only [if_neg hn] at hstep
  have hbd₂ : St.Bd W ⟨s.pc + (compile dep cnd).length + 1, s.stk, s.ret, H₁⟩ :=
    hbd.setStk (by omega) (fun x hx => hbd.stk x (List.mem_cons_of_mem _ hx)) (by omega)
  have hc₂ : Cfg P W ⟨s.pc + (compile dep cnd).length + 1, s.stk, s.ret, H₁⟩ c₂ :=
    ⟨hbd₂, hL, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
  obtain ⟨n₂, hn₂, w₂, H₂, hs₂, hx₂, hr₂, hh₂⟩ := ht dep W
    ⟨s.pc + (compile dep cnd).length + 1, s.stk, s.ret, H₁⟩ hft (henv.mono hx₁) hc₂
  dsimp only at hs₂ hh₂ hx₂
  have hstep2 := step_jmp (P := P) (s := ⟨s.pc + (compile dep cnd).length + 1 + (compile dep t).length,
    w₂ :: s.stk, s.ret, H₂⟩) hjmp
  have hbd₄ := hs₂.bd_end
  refine ⟨n₁ + (n₂ + 1 + 1), by omega, w₂, H₂,
    hs₁.trans (StepsB.step hbd hstep (hs₂.trans (StepsB.one hbd₄ hstep2 ?_))),
    hx₁.trans hx₂, hr₂, by omega⟩
  exact hbd₄.setPc (by omega)

theorem sim_iteF {ρ : List Val} {cnd t e : Tm} {v : Val} {c₁ c₂ : ℕ}
    (hc : SimEv P ρ cnd (.nat 0) c₁) (he : SimEv P ρ e v c₂) :
    SimEv P ρ (.ite cnd t e) v (c₁ + c₂ + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfc : FitsAt P s.pc (compile dep cnd) := hfit.append_left
  have hr1 := hfit.append_right
  have hjz := hr1.head
  have hr2 := hr1.tail
  have hr3 := hr2.append_right
  have hr4 := hr3.tail
  have hfe : FitsAt P (s.pc + (compile dep cnd).length + 1 + ((compile dep t).length + 1))
      (compile dep e) := by
    have := hr4
    rwa [show s.pc + (compile dep cnd).length + 1 + (compile dep t).length + 1 =
      s.pc + (compile dep cnd).length + 1 + ((compile dep t).length + 1) by omega] at this
  have hlen := hfit.1
  have e : s.pc + (compile dep cnd ++ (Instr.jz ((compile dep t).length + 1) ::
      (compile dep t ++ (Instr.jmp (compile dep e).length :: compile dep e)))).length =
      s.pc + (compile dep cnd).length + 1 + ((compile dep t).length + 1) + (compile dep e).length := by
    simp; omega
  rw [e]
  simp only [List.length_append, List.length_cons] at hlen
  have hL := hcfg.len
  have hB := hcfg.heap
  have hstk := hcfg.stk
  have hret := hcfg.ret
  obtain ⟨n₁, hn₁, w₁, H₁, hs₁, hx₁, hr₁, hh₁⟩ := hc dep W s hfc henv (hcfg.sub (by omega))
  obtain ⟨rfl, hnB⟩ := hr₁.nat_inv
  have hbd := hs₁.bd_end
  have hstep := step_jz (P := P) (s := ⟨s.pc + (compile dep cnd).length, 0 :: s.stk, s.ret, H₁⟩)
    hjz 0 s.stk rfl
  have hbd₂ : St.Bd W ⟨s.pc + (compile dep cnd).length + 1 + ((compile dep t).length + 1), s.stk, s.ret, H₁⟩ :=
    hbd.setStk (by omega) (fun x hx => hbd.stk x (List.mem_cons_of_mem _ hx)) (by omega)
  have hc₂ : Cfg P W ⟨s.pc + (compile dep cnd).length + 1 + ((compile dep t).length + 1), s.stk, s.ret, H₁⟩
      c₂ := ⟨hbd₂, hL, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
  obtain ⟨n₂, hn₂, w₂, H₂, hs₂, hx₂, hr₂, hh₂⟩ := he dep W
    ⟨s.pc + (compile dep cnd).length + 1 + ((compile dep t).length + 1), s.stk, s.ret, H₁⟩ hfe
    (henv.mono hx₁) hc₂
  dsimp only at hs₂ hh₂ hx₂
  refine ⟨n₁ + (n₂ + 1), by omega, w₂, H₂, hs₁.trans (StepsB.step hbd hstep hs₂), hx₁.trans hx₂, hr₂,
    by omega⟩

theorem sim_let {ρ : List Val} {a b : Tm} {u v : Val} {c₁ c₂ : ℕ} (ha : SimEv P ρ a u c₁)
    (hb : SimEv P (u :: ρ) b v c₂) : SimEv P ρ (.letE a b) v (c₁ + c₂ + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfa : FitsAt P s.pc (compile dep a) := hfit.append_left
  have hrest := hfit.append_right
  have hfb : FitsAt P (s.pc + (compile dep a).length) (compile (letDep dep) b) := hrest.append_left
  have hfi : FitsAt P (s.pc + (compile dep a).length + (compile (letDep dep) b).length) [Instr.slide] :=
    hrest.append_right
  have hlen := hfit.1
  have e : s.pc + (compile dep a ++ (compile (letDep dep) b ++ [Instr.slide])).length =
      s.pc + (compile dep a).length + (compile (letDep dep) b).length + 1 := by simp; omega
  rw [e]
  simp only [List.length_append, List.length_singleton] at hlen
  have hL := hcfg.len
  have hB := hcfg.heap
  have hstk := hcfg.stk
  obtain ⟨n₁, hn₁, w₁, H₁, hs₁, hx₁, hr₁, hh₁⟩ := ha dep W s hfa henv (hcfg.sub (by omega))
  have hc₂ : Cfg P W ⟨s.pc + (compile dep a).length, w₁ :: s.stk, s.ret, H₁⟩ c₂ :=
    hcfg.next (c₁ := c₁) (by omega) hs₁.bd_end hh₁ (by simp) (by simp)
  obtain ⟨n₂, hn₂, w₂, H₂, hs₂, hx₂, hr₂, hh₂⟩ := hb (letDep dep) W
    ⟨s.pc + (compile dep a).length, w₁ :: s.stk, s.ret, H₁⟩ hfb (Env.letE hr₁ (henv.mono hx₁)) hc₂
  dsimp only at hs₂ hh₂ hx₂
  have hstep := step_slide (P := P) (s := ⟨s.pc + (compile dep a).length + (compile (letDep dep) b).length,
    w₂ :: w₁ :: s.stk, s.ret, H₂⟩) hfi.head w₂ w₁ s.stk rfl
  have hbd := hs₂.bd_end
  refine ⟨n₁ + (n₂ + 1), by omega, w₂, H₂, hs₁.trans (hs₂.trans (StepsB.one hbd hstep ?_)),
    hx₁.trans hx₂, hr₂, by omega⟩
  refine hbd.setStk (by omega) ?_ (by simp; omega)
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hbd.stk x (by simp)
  · exact hbd.stk x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))

/-! ## argument lists -/

theorem sim_evl_nil {ρ : List Val} : SimEvL P ρ [] [] 0 := by
  intro dep W s hfit henv hcfg
  refine ⟨0, by omega, [], s.heap, ?_, HExt.refl _, .nil, by omega, rfl⟩
  simpa [compileArgs] using StepsB.refl hcfg.bd

theorem sim_evl_cons {ρ : List Val} {t : Tm} {ts : List Tm} {v : Val} {vs : List Val} {c₁ c₂ : ℕ}
    (hlen : ts.length ≤ c₂) (ht : SimEv P ρ t v c₁) (hts : SimEvL P ρ ts vs c₂) :
    SimEvL P ρ (t :: ts) (v :: vs) (c₁ + c₂) := by
  intro dep W s hfit henv hcfg
  simp only [compileArgs] at hfit ⊢
  have hfa : FitsAt P s.pc (compileArgs dep ts) := hfit.append_left
  have hfb : FitsAt P (s.pc + (compileArgs dep ts).length) (compile (shiftDep ts.length dep) t) :=
    hfit.append_right
  have hlen' := hfit.1
  have e : s.pc + (compileArgs dep ts ++ compile (shiftDep ts.length dep) t).length =
      s.pc + (compileArgs dep ts).length + (compile (shiftDep ts.length dep) t).length := by
    simp; omega
  rw [e]
  simp only [List.length_append] at hlen'
  have hL := hcfg.len
  have hB := hcfg.heap
  have hstk := hcfg.stk
  have hret := hcfg.ret
  obtain ⟨n₁, hn₁, ws, H₁, hs₁, hx₁, hr₁, hh₁, hwl⟩ := hts dep W s hfa henv (hcfg.sub (by omega))
  have hbd := hs₁.bd_end
  have hc₂ : Cfg P W ⟨s.pc + (compileArgs dep ts).length, ws ++ s.stk, s.ret, H₁⟩ c₁ :=
    ⟨hbd, hL, by dsimp only; omega, by simp; omega, by dsimp only; omega⟩
  have henv' : Env P.B H₁ (shiftDep ts.length dep) ρ (ws ++ s.stk) := by
    have := (henv.mono hx₁).shift ws
    rwa [hwl] at this
  obtain ⟨n₂, hn₂, w, H₂, hs₂, hx₂, hr₂, hh₂⟩ := ht (shiftDep ts.length dep) W
    ⟨s.pc + (compileArgs dep ts).length, ws ++ s.stk, s.ret, H₁⟩ hfb henv' hc₂
  dsimp only at hs₂ hh₂ hx₂
  refine ⟨n₁ + n₂, by omega, w :: ws, H₂, hs₁.trans hs₂, hx₁.trans hx₂,
    .cons hr₂ (hr₁.mono hx₂), by omega, by simp [hwl]⟩

/-! ## calls -/

/-- From the state right after the argument words and the function id were pushed, up to the return. -/
theorem callee_run {Δ : ℕ → Option Tm} (hreal : P.Real Δ) {f : ℕ} {body : Tm} {vs : List Val} {v : Val}
    {c₂ W : ℕ} (hΔ : Δ f = some body) (hbody : SimEv P vs body v c₂) {ws stk₀ : List ℕ}
    {ret₀ : List (ℕ × ℕ)} {H : List (ℕ × ℕ)} {pcc : ℕ}
    (hcode : P.code pcc = .call ws.length) (hrep : RepL P.B H ws vs)
    (hbd : St.Bd W ⟨pcc, f :: (ws ++ stk₀), ret₀, H⟩)
    (hL : P.len ≤ W) (hpc : pcc + 1 ≤ P.len) (hheap : P.B + H.length + c₂ ≤ W)
    (hstk : (ws ++ stk₀).length + 3 * c₂ ≤ W) (hret : ret₀.length + 1 + 3 * c₂ ≤ W) :
    ∃ n ≤ 3 * c₂ + 2, ∃ (w : ℕ) (H' : List (ℕ × ℕ)),
      StepsB P W n ⟨pcc, f :: (ws ++ stk₀), ret₀, H⟩ ⟨pcc + 1, w :: stk₀, ret₀, H'⟩ ∧ HExt H H' ∧
        Rep P.B H' w v ∧ H'.length ≤ H.length + c₂ := by
  obtain ⟨hfl, hfit⟩ := hreal f body hΔ
  have hfit' : FitsAt P (P.ft f) (compile id body) := hfit.append_left
  have hfret : FitsAt P (P.ft f + (compile id body).length) [Instr.ret] := hfit.append_right
  have hlen := hfit.1
  simp only [List.length_append, List.length_singleton] at hlen
  have hstep := step_call (P := P) (s := ⟨pcc, f :: (ws ++ stk₀), ret₀, H⟩) hcode f (ws ++ stk₀) rfl
  have hsub : (ws ++ stk₀).length - ws.length = stk₀.length := by simp
  simp only [hsub] at hstep
  have hws : ∀ x ∈ ws ++ stk₀, x ≤ W := fun x hx => hbd.stk x (List.mem_cons_of_mem _ hx)
  have hbd₃ : St.Bd W ⟨P.ft f, ws ++ stk₀, (pcc + 1, stk₀.length) :: ret₀, H⟩ := by
    refine ⟨by show P.ft f ≤ W; omega, by show (ws ++ stk₀).length ≤ W; omega, hws, by simp; omega, ?_, hbd.heapLen, hbd.heap⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨by omega, by simp at hstk; omega⟩
    · exact hbd.ret p hp
  have hc₃ : Cfg P W ⟨P.ft f, ws ++ stk₀, (pcc + 1, stk₀.length) :: ret₀, H⟩ c₂ :=
    ⟨hbd₃, hL, by dsimp only; omega, by dsimp only; omega, by simp; omega⟩
  obtain ⟨n₂, hn₂, w, H₂, hs₂, hx₂, hr₂, hh₂⟩ := hbody id W
    ⟨P.ft f, ws ++ stk₀, (pcc + 1, stk₀.length) :: ret₀, H⟩ hfit' (Env.of_repl hrep stk₀) hc₃
  dsimp only at hs₂ hh₂ hx₂
  have hbd₄ := hs₂.bd_end
  have hstep2 := step_ret (P := P) (s := ⟨P.ft f + (compile id body).length, w :: (ws ++ stk₀),
    (pcc + 1, stk₀.length) :: ret₀, H₂⟩) hfret.head w (ws ++ stk₀) (pcc + 1) stk₀.length ret₀ rfl rfl
  have hdrop : (ws ++ stk₀).drop ((ws ++ stk₀).length - stk₀.length) = stk₀ := by
    rw [List.length_append, Nat.add_sub_cancel]; exact List.drop_left ..
  simp only [hdrop] at hstep2
  refine ⟨(n₂ + 1) + 1, by omega, w, H₂, StepsB.step hbd hstep (hs₂.trans (StepsB.one hbd₄ hstep2 ?_)),
    hx₂, hr₂, by omega⟩
  refine ⟨by show pcc + 1 ≤ W; omega, ?_, ?_, ?_, ?_, hbd₄.heapLen, hbd₄.heap⟩
  · have := hbd₄.stkLen; simp at this ⊢; omega
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hbd₄.stk x (by simp)
    · exact hbd₄.stk x (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
  · have := hbd₄.retLen; simp at this ⊢; omega
  · intro p hp
    exact hbd₄.ret p (List.mem_cons_of_mem _ hp)

theorem sim_call {Δ : ℕ → Option Tm} (hreal : P.Real Δ) {ρ : List Val} {f : ℕ} {args : List Tm}
    {body : Tm} {vs : List Val} {v : Val} {c₁ c₂ : ℕ} (hlen : args.length ≤ c₁)
    (hargs : SimEvL P ρ args vs c₁) (hΔ : Δ f = some body) (hbody : SimEv P vs body v c₂) :
    SimEv P ρ (.call f args) v (c₁ + c₂ + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfa : FitsAt P s.pc (compileArgs dep args) := hfit.append_left
  have hr := hfit.append_right
  have hlit : P.code (s.pc + (compileArgs dep args).length) = .lit f := hr.head
  have hcall : P.code (s.pc + (compileArgs dep args).length + 1) = .call args.length := hr.tail.head
  have hlen' := hfit.1
  have e : s.pc + (compileArgs dep args ++ [Instr.lit f, Instr.call args.length]).length =
      s.pc + (compileArgs dep args).length + 1 + 1 := by simp; omega
  rw [e]
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen'
  have hL := hcfg.len
  have hB := hcfg.heap
  have hstk := hcfg.stk
  have hret := hcfg.ret
  have hfW : f ≤ W := Nat.le_trans (hreal f body hΔ).1 hL
  obtain ⟨n₁, hn₁, ws, H₁, hs₁, hx₁, hr₁, hh₁, hwl⟩ := hargs dep W s hfa henv (hcfg.sub (by omega))
  have hbd := hs₁.bd_end
  have hstep := step_lit (P := P) (s := ⟨s.pc + (compileArgs dep args).length, ws ++ s.stk, s.ret, H₁⟩) hlit
  have hbd₂ : St.Bd W ⟨s.pc + (compileArgs dep args).length + 1, f :: (ws ++ s.stk), s.ret, H₁⟩ :=
    hbd.setStk (by omega) (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hfW
      · exact hbd.stk x hx) (by simp; omega)
  obtain ⟨n₂, hn₂, w, H₂, hs₂, hx₂, hr₂, hh₂⟩ := callee_run hreal hΔ hbody
    (ws := ws) (stk₀ := s.stk) (ret₀ := s.ret) (H := H₁) (pcc := s.pc + (compileArgs dep args).length + 1)
    (by rw [hwl]; exact hcall) hr₁ hbd₂ hL (by omega) (by omega) (by simp; omega) (by omega)
  refine ⟨n₁ + (n₂ + 1), by omega, w, H₂, hs₁.trans (StepsB.step hbd hstep hs₂), hx₁.trans hx₂, hr₂,
    by omega⟩

theorem sim_callv {Δ : ℕ → Option Tm} (hreal : P.Real Δ) {ρ : List Val} {ft : Tm} {f : ℕ}
    {args : List Tm} {body : Tm} {vs : List Val} {v : Val} {c₀ c₁ c₂ : ℕ} (hlen : args.length ≤ c₁)
    (hf : SimEv P ρ ft (.nat f) c₀) (hargs : SimEvL P ρ args vs c₁) (hΔ : Δ f = some body)
    (hbody : SimEv P vs body v c₂) : SimEv P ρ (.callv ft args) v (c₀ + c₁ + c₂ + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfa : FitsAt P s.pc (compileArgs dep args) := hfit.append_left
  have hrest := hfit.append_right
  have hff : FitsAt P (s.pc + (compileArgs dep args).length) (compile (shiftDep args.length dep) ft) :=
    hrest.append_left
  have hcall : P.code (s.pc + (compileArgs dep args).length + (compile (shiftDep args.length dep) ft).length)
      = .call args.length := hrest.append_right.head
  have hlen' := hfit.1
  have e : s.pc + (compileArgs dep args ++ (compile (shiftDep args.length dep) ft ++
      [Instr.call args.length])).length =
      s.pc + (compileArgs dep args).length + (compile (shiftDep args.length dep) ft).length + 1 := by
    simp; omega
  rw [e]
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen'
  have hL := hcfg.len
  have hB := hcfg.heap
  have hstk := hcfg.stk
  have hret := hcfg.ret
  obtain ⟨n₁, hn₁, ws, H₁, hs₁, hx₁, hr₁, hh₁, hwl⟩ := hargs dep W s hfa henv (hcfg.sub (by omega))
  have hbd := hs₁.bd_end
  have hc₂ : Cfg P W ⟨s.pc + (compileArgs dep args).length, ws ++ s.stk, s.ret, H₁⟩ c₀ :=
    ⟨hbd, hL, by dsimp only; omega, by simp; omega, by dsimp only; omega⟩
  have henv' : Env P.B H₁ (shiftDep args.length dep) ρ (ws ++ s.stk) := by
    have := (henv.mono hx₁).shift ws
    rwa [hwl] at this
  obtain ⟨n₃, hn₃, wf, H₃, hs₃, hx₃, hr₃, hh₃⟩ := hf (shiftDep args.length dep) W
    ⟨s.pc + (compileArgs dep args).length, ws ++ s.stk, s.ret, H₁⟩ hff henv' hc₂
  dsimp only at hs₃ hh₃ hx₃
  obtain ⟨rfl, hfB⟩ := hr₃.nat_inv
  have hbd₃ := hs₃.bd_end
  obtain ⟨n₂, hn₂, w, H₂, hs₂, hx₂, hr₂, hh₂⟩ := callee_run hreal hΔ hbody
    (ws := ws) (stk₀ := s.stk) (ret₀ := s.ret) (H := H₃)
    (pcc := s.pc + (compileArgs dep args).length + (compile (shiftDep args.length dep) ft).length)
    (by rw [hwl]; exact hcall) (hr₁.mono hx₃) hbd₃ hL (by omega) (by omega) (by simp; omega)
    (by omega)
  refine ⟨n₁ + (n₃ + n₂), by omega, w, H₂, hs₁.trans (hs₃.trans hs₂), (hx₁.trans hx₃).trans hx₂, hr₂,
    by omega⟩

/-! ## the main theorem -/

theorem _root_.Lax117284Proofs.Treewidth.Fun.Ev.pos {Δ : ℕ → Option Tm} {B : ℕ} {ρ : List Val} {t : Tm} {v : Val} {c : ℕ}
    (h : Ev Δ B ρ t v c) : 1 ≤ c := by
  cases h <;> omega

theorem _root_.Lax117284Proofs.Treewidth.Fun.EvL.len_eq_le {Δ : ℕ → Option Tm} {B : ℕ} :
    ∀ (ts : List Tm) {ρ : List Val} {vs : List Val} {c : ℕ}, EvL Δ B ρ ts vs c →
      vs.length = ts.length ∧ ts.length ≤ c
  | [], _, _, _, h => by cases h; simp
  | t :: ts, _, _, _, h => by
    cases h with
    | cons h₁ h₂ =>
      have := h₁.pos
      have := EvL.len_eq_le ts h₂
      simp; omega

/-- **The simulation theorem**: every big-step derivation of the fragment is simulated by the machine. -/
theorem ev_sim {Δ : ℕ → Option Tm} (hB : 2 ≤ P.B) (hreal : P.Real Δ) {ρ : List Val} {t : Tm} {v : Val}
    {c : ℕ} (h : Ev Δ P.B ρ t v c) : SimEv P ρ t v c :=
  Ev.rec (motive_1 := fun ρ t v c _ => SimEv P ρ t v c)
    (motive_2 := fun ρ ts vs c _ => SimEvL P ρ ts vs c)
    (fun hn => sim_lit hn)
    (fun hi => sim_var hi)
    (fun _ _ hm iha ihb => bin_sim (op := (· + ·)) (fun dep => by simp [compile])
      (fun s x y r hc hs => step_add hc x y r hs) (fun _ _ => hm) iha ihb)
    (fun _ _ iha ihb => bin_sim (op := (· - ·)) (fun dep => by simp [compile])
      (fun s x y r hc hs => step_sub hc x y r hs) (fun h _ => by omega) iha ihb)
    (fun _ _ hm iha ihb => bin_sim (op := (· * ·)) (fun dep => by simp [compile])
      (fun s x y r hc hs => step_mul hc x y r hs) (fun _ _ => hm) iha ihb)
    (fun _ _ iha ihb => bin_sim (op := fun x y => if x < y then 1 else 0) (fun dep => by simp [compile])
      (fun s x y r hc hs => step_lt hc x y r hs) (fun _ _ => by split <;> omega) iha ihb)
    (fun _ _ iha ihb => bin_sim (op := fun x y => if x = y then 1 else 0) (fun dep => by simp [compile])
      (fun s x y r hc hs => step_eq hc x y r hs) (fun _ _ => by split <;> omega) iha ihb)
    (fun _ _ iha ihb => sim_cons iha ihb)
    (fun _ iha => sim_fst iha)
    (fun _ iha => sim_snd iha)
    (fun _ iha => sim_isNatT hB iha)
    (fun _ iha => sim_isNatF hB iha)
    (fun _ hn _ ihc iht => sim_iteT hn ihc iht)
    (fun _ _ ihc ihe => sim_iteF ihc ihe)
    (fun _ _ iha ihb => sim_let iha ihb)
    (fun hargs hΔ _ ihargs ihbody => sim_call hreal (hargs.len_eq_le).2 ihargs hΔ ihbody)
    (fun _ hargs hΔ _ ihf ihargs ihbody => sim_callv hreal (hargs.len_eq_le).2 ihf ihargs hΔ ihbody)
    sim_evl_nil
    (fun _ hts iht ihts => sim_evl_cons (hts.len_eq_le).2 iht ihts)
    h

end Lax117284Proofs.Treewidth.Fun.VM

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMTop` -/

section
/-!
# WP V1 (6): the top-level theorem — `Runs Δ B f xs y c` ⇒ the machine halts with a representation of `y`

The program `mkProg Δ N main k B` (stub + all functions `< N` of the table) started with `k` argument words on
the stack (representing `xs`, argument 0 on top), stops at pc `2` (the `halt` of the stub) with one word on the
stack representing `y`, after at most `3c + 3` steps; the heap only grew (by at most `c` cells); and all machine
naturals stay `≤ W₀ + len + B + 3c + 3`, where `W₀` bounds the naturals of the initial state.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM

theorem funCode_length_pos (Δ : ℕ → Option Tm) (f : ℕ) : 1 ≤ (funCode Δ f).length := by
  unfold funCode; cases Δ f <;> simp

theorem le_offset (Δ : ℕ → Option Tm) (f : ℕ) : f ≤ offset Δ f := by
  rw [offset_eq]
  induction f with
  | zero => omega
  | succ f ih =>
    rw [List.range_succ, List.flatMap_append]
    have := funCode_length_pos Δ f
    simp only [List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    omega

/-- Words are bounded by the heap: a representation of a value uses only words `< B + |H|`. -/
theorem Rep.lt {B : ℕ} {H : List (ℕ × ℕ)} {w : ℕ} {v : Val} (h : Rep B H w v) : w < B + H.length := by
  cases h with
  | nat hn => omega
  | cons hp _ _ =>
    have := (List.getElem?_eq_some_iff.mp hp).1
    omega

/-! ## building representations (for the loader of WP V3) -/

/-- The number of `cons` nodes of a value (= the heap cells needed to represent it). -/
def _root_.Lax117284Proofs.Treewidth.Fun.Val.cells : Val → ℕ
  | .nat _ => 0
  | .cons a b => a.cells + b.cells + 1

end Lax117284Proofs.Treewidth.Fun.VM

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMRamTop` -/

section
/-!
# WP V2 (6): compilability, initial states, and `vm_ram_correct`
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-! ## `Com.Ok` for the layout, block by block -/

macro "okSimp" : tactic => `(tactic| simp [Com.Ok, Cond.Ok, Expr.Ok, condExpr, Lvm, arrNames, tp, nx, incPc, incSp, decSp])

theorem ok_bHalt : Com.Ok Lvm bHalt := by unfold bHalt; okSimp
theorem ok_bLit : Com.Ok Lvm bLit := by unfold bLit; okSimp
theorem ok_bVar : Com.Ok Lvm bVar := by unfold bVar; okSimp
theorem ok_bBin (o : Bop) : Com.Ok Lvm (bBin o) := by unfold bBin; okSimp
theorem ok_bLt : Com.Ok Lvm bLt := by unfold bLt; okSimp
theorem ok_bEq : Com.Ok Lvm bEq := by unfold bEq; okSimp
theorem ok_bCons : Com.Ok Lvm bCons := by unfold bCons; okSimp
theorem ok_bFst : Com.Ok Lvm bFst := by unfold bFst; okSimp
theorem ok_bSnd : Com.Ok Lvm bSnd := by unfold bSnd; okSimp
theorem ok_bIsNat : Com.Ok Lvm bIsNat := by unfold bIsNat; okSimp
theorem ok_bJz : Com.Ok Lvm bJz := by unfold bJz; okSimp
theorem ok_bJmp : Com.Ok Lvm bJmp := by unfold bJmp; okSimp
theorem ok_bSlide : Com.Ok Lvm bSlide := by unfold bSlide; okSimp
theorem ok_bCall : Com.Ok Lvm bCall := by unfold bCall; okSimp
theorem ok_bRet : Com.Ok Lvm bRet := by unfold bRet; okSimp
theorem ok_bFetch : Com.Ok Lvm bFetch := by unfold bFetch; okSimp

theorem ok_blkOp (j : ℕ) : Com.Ok Lvm (blkOp j) := by
  unfold blkOp
  split
  all_goals first
    | exact ok_bHalt
    | exact ok_bLit
    | exact ok_bVar
    | exact ok_bBin _
    | exact ok_bLt
    | exact ok_bEq
    | exact ok_bCons
    | exact ok_bFst
    | exact ok_bSnd
    | exact ok_bIsNat
    | exact ok_bJz
    | exact ok_bJmp
    | exact ok_bSlide
    | exact ok_bCall
    | exact ok_bRet

theorem ok_dispatchFrom : ∀ (f k : ℕ), Com.Ok Lvm (dispatchFrom k f) := by
  intro f
  induction f with
  | zero => intro k; simpa [dispatchFrom] using ok_blkOp k
  | succ f ih =>
    intro k
    simp only [dispatchFrom, Com.Ok]
    refine ⟨?_, ok_blkOp k, ih (k + 1)⟩
    simp [Cond.Ok, Expr.Ok, condExpr, Lvm]

/-- **The interpreter compiles under the layout `Lvm`.** -/
theorem ok_vmLoop : Com.Ok Lvm vmLoop := by
  unfold vmLoop
  simp only [Com.Ok]
  refine ⟨by simp [Cond.Ok, Expr.Ok, condExpr, Lvm], ?_⟩
  unfold bBody
  exact ⟨ok_bFetch, ok_dispatchFrom 16 0⟩

/-! ## Compilability is monotone in the layout (V3 extends `Lvm` by its reader/writer names) -/

theorem expr_ok_mono {L L' : Layout} (hs : ∀ x ∈ L.scalars, x ∈ L'.scalars)
    (ha : ∀ a ∈ L.arrays, a ∈ L'.arrays) (ht : L.temps ≤ L'.temps) :
    ∀ (e : Expr) (d : ℕ), Expr.Ok L e d → Expr.Ok L' e d := by
  intro e
  induction e with
  | lit n => intro d _; exact Expr.ok_lit _ _ _
  | var x => intro d h; exact hs x h
  | get a i ih => intro d h; exact ⟨ha a h.1, ih d h.2.1, by have := h.2.2; omega⟩
  | bin o e f ihe ihf => intro d h; exact ⟨ihf d h.1, ihe (d + 1) h.2.1, by have := h.2.2; omega⟩

theorem com_ok_mono {L L' : Layout} (hs : ∀ x ∈ L.scalars, x ∈ L'.scalars)
    (ha : ∀ a ∈ L.arrays, a ∈ L'.arrays) (ht : L.temps ≤ L'.temps) :
    ∀ c : Com, Com.Ok L c → Com.Ok L' c := by
  have hE := expr_ok_mono hs ha ht
  have hC : ∀ (b : Cond) (d : ℕ), Cond.Ok L b d → Cond.Ok L' b d := by
    intro b d h; exact hE _ _ h
  intro c
  induction c with
  | skip => intro _; exact Com.ok_skip _
  | assign x e => intro h; exact ⟨hs x h.1, hE _ _ h.2⟩
  | store a i e => intro h; exact ⟨ha a h.1, hE _ _ h.2.1, hE _ _ h.2.2.1, by have := h.2.2.2; omega⟩
  | seq c d ihc ihd => intro h; exact ⟨ihc h.1, ihd h.2⟩
  | ite b c d ihc ihd => intro h; exact ⟨hC b 0 h.1, ihc h.2.1, ihd h.2.2⟩
  | «while» b c ih => intro h; exact ⟨hC b 0 h.1, ih h.2⟩
  | read x => intro h; exact hs x h
  | write e => intro h; exact ⟨hE _ _ h.1, by have := h.2; omega⟩

/-! ## Initial and final states -/

/-- **What the loader (V3) must establish, part 1.**  An initial configuration `⟨0, stk, [], H⟩` is represented as
soon as the scalars are right and the stack and the heap sit in their arrays. -/
theorem Abs.init {σ : Lax808846Proofs.Imp.Env} {stk : List ℕ} {H : List (ℕ × ℕ)} (hpc : σ.vars "pc" = 0)
    (hsp : σ.vars "sp" = stk.length) (hrp : σ.vars "rp" = 0) (hhp : σ.vars "hp" = H.length)
    (hstk : Pfx stk.reverse (σ.arrs "STK")) (hha : Pfx (H.map Prod.fst) (σ.arrs "HA"))
    (hhb : Pfx (H.map Prod.snd) (σ.arrs "HB")) : Abs ⟨0, stk, [], H⟩ σ :=
  ⟨hpc, hsp, by simpa using hrp, hhp, hstk, Pfx.nil _, Pfx.nil _, hha, hhb⟩

/-- **What the loader (V3) must establish, part 2.**  The constants: the code, operand and function-table
arrays are the `W + 1` first cells of the program; the other five arrays have length `W + 1`; `B` holds `P.B`;
every operand of the program is `< Bi`. -/
theorem Cst.of_arrays {P : Prog} {W Bi : ℕ} {σ : Lax808846Proofs.Imp.Env} (htb : σ.vars "B" = P.B)
    (hOP : σ.arrs "OP" = arrOf (W + 1) (fun i => opc (P.code i)))
    (hOA : σ.arrs "OA" = arrOf (W + 1) (fun i => opa (P.code i)))
    (hFT : σ.arrs "FT" = arrOf (W + 1) P.ft)
    (hlen : ∀ a ∈ ["STK", "RETPC", "RETH", "HA", "HB"], (σ.arrs a).length = W + 1)
    (hopa : ∀ i, i ≤ W → opa (P.code i) < Bi) (hbW : P.B ≤ W) (hbi : W + 18 ≤ Bi) : Cst P W Bi σ where
  tb := htb
  op := fun i hi => by rw [hOP, getElem?_arrOf _ (by omega)]
  oa := fun i hi => by rw [hOA, getElem?_arrOf _ (by omega)]
  ft := fun i hi => by rw [hFT, getElem?_arrOf _ (by omega)]
  opa_lt := hopa
  len := fun a ha => by
    simp only [arrNames, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hOP]; simp
    · rw [hOA]; simp
    · rw [hFT]; simp
    all_goals exact hlen _ (by simp)
  bW := hbW
  bi := hbi

/-- The result of a finished run: the stack has the result on top, above the untouched `stk₀`. -/
theorem Abs.result {σ : Lax808846Proofs.Imp.Env} {w : ℕ} {stk₀ : List ℕ} {H' : List (ℕ × ℕ)}
    (hA : Abs ⟨2, w :: stk₀, [], H'⟩ σ) :
    σ.vars "sp" = stk₀.length + 1 ∧ (σ.arrs "STK")[stk₀.length]? = some w := by
  refine ⟨by simpa using hA.sp, ?_⟩
  have := hA.stk (stk₀.length) (by simp)
  simpa using this

/-! ## The combined theorem -/

end Lax117284Proofs.Treewidth.Fun.VM.Ram

end
