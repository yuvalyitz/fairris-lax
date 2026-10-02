import Lax117284Proofs.Treewidth.Fun.Defs

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

/-- The instruction set (17 instructions; each carries at most one natural operand). -/
inductive Instr where
  | lit (n : ℕ) | var (i : ℕ)
  | add | sub | mul | lt | eq
  | cons | fst | snd | isNat
  | jz (k : ℕ) | jmp (k : ℕ) | slide
  | call (n : ℕ) | ret | halt
  deriving DecidableEq

/-- A machine program: code array (default `halt` outside), function-entry table, code length, tag bound `B`. -/
structure Prog where
  code : ℕ → Instr
  ft : ℕ → ℕ
  len : ℕ
  B : ℕ

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
theorem HExt.length_le {H H' : List (ℕ × ℕ)} (h : HExt H H') : H.length ≤ H'.length := by
  obtain ⟨t, rfl⟩ := h; simp
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

/-- A word represents at most one value. -/
theorem Rep.det {B : ℕ} {H : List (ℕ × ℕ)} {w : ℕ} {v v' : Val} (h : Rep B H w v) (h' : Rep B H w v') :
    v = v' := by
  induction h generalizing v' with
  | nat hn =>
    cases h' with
    | nat _ => rfl
    | cons _ _ _ => omega
  | @cons p a b u v hp _ _ ih₁ ih₂ =>
    cases v' with
    | nat n => have := h'.nat_inv; omega
    | cons u' v'' =>
      obtain ⟨p', a', b', hw, hp', h₁', h₂'⟩ := h'.cons_inv
      have : p' = p := by omega
      subst this
      have hc := hp.symm.trans hp'
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      rw [ih₁ h₁', ih₂ h₂']

end Lax117284Proofs.Treewidth.Fun.VM
