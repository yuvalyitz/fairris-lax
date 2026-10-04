import Lax434930Proofs.PolynomialComposition
import Lax117284Proofs.Machine.Bits
import Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram

/-! ### `Lax117284Proofs.Machine.TMCompose` -/

section
set_option backward.isDefEq.respectTransparency false

/-!
Sequential composition of two polynomial-time Turing machines through an intermediate
word over an arbitrary finite alphabet.

The archive's composition theorem asks for a binary intermediate encoding, because that
is what the complexity classes it was written for use. The equivalence between word RAMs
and Turing machines speaks a three-letter alphabet — a separator and two digits — so a
reduction computed on a word RAM cannot be composed with a binary one as it stands. This
file is that theorem with the alphabet of the transfer stack made a parameter; the
construction and its proof are otherwise the archive's.
-/

namespace Lax117284Proofs.Machine.TMCompose

open Turing Lax434930Proofs Lax434930Proofs.TM2Bounds Polynomial

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin


variable (M N : FinTM2) (Γm : Type) [Fintype Γm] [Inhabited Γm]

abbrev Key := M.K ⊕ (N.K ⊕ Unit)
abbrev Label := M.Λ ⊕ (Bool ⊕ N.Λ)
abbrev State := M.σ × (N.σ × Option Γm)

def Alphabet : Key M N → Type
  | .inl k => M.Γ k
  | .inr (.inl k) => N.Γ k
  | .inr (.inr _) => Γm

abbrev Cfg := TM2.Cfg (Alphabet M N Γm) (Label M N) (State M N Γm)
abbrev Stmt := TM2.Stmt (Alphabet M N Γm) (Label M N) (State M N Γm)

def joinedStacks (s : (k : M.K) → List (M.Γ k)) (t : (k : N.K) → List (N.Γ k))
    (tmp : List Γm) : (k : Key M N) → List (Alphabet M N Γm k)
  | .inl k => s k
  | .inr (.inl k) => t k
  | .inr (.inr _) => tmp

theorem update_left (s : (k : M.K) → List (M.Γ k)) (t : (k : N.K) → List (N.Γ k))
    (tmp : List Γm) (k : M.K) (xs : List (M.Γ k)) :
    Function.update (joinedStacks M N Γm s t tmp) (.inl k) xs =
      joinedStacks M N Γm (Function.update s k xs) t tmp := by
  funext j
  cases j with
  | inl j => by_cases hj : j = k <;> simp_all [joinedStacks] <;> rfl
  | inr j => cases j <;> simp [joinedStacks]

theorem update_right (s : (k : M.K) → List (M.Γ k)) (t : (k : N.K) → List (N.Γ k))
    (tmp : List Γm) (k : N.K) (xs : List (N.Γ k)) :
    Function.update (joinedStacks M N Γm s t tmp) (.inr (.inl k)) xs =
      joinedStacks M N Γm s (Function.update t k xs) tmp := by
  funext j
  cases j with
  | inl j => simp [joinedStacks]
  | inr j =>
      cases j with
      | inl j => by_cases hj : j = k <;> simp_all [joinedStacks] <;> rfl
      | inr j => simp [joinedStacks]

theorem update_tmp (s : (k : M.K) → List (M.Γ k)) (t : (k : N.K) → List (N.Γ k))
    (tmp xs : List Γm) :
    Function.update (joinedStacks M N Γm s t tmp) (.inr (.inr ())) xs = joinedStacks M N Γm s t xs := by
  funext j
  cases j with
  | inl j => simp [joinedStacks]
  | inr j => cases j <;> simp [joinedStacks]

def leftStmt : M.Stmt → Stmt M N Γm
  | .push k f q => .push (.inl k) (fun v => f v.1) (leftStmt q)
  | .pop k f q => .pop (.inl k) (fun v b => (f v.1 b, v.2)) (leftStmt q)
  | .peek k f q => .peek (.inl k) (fun v b => (f v.1 b, v.2)) (leftStmt q)
  | .load f q => .load (fun v => (f v.1, v.2)) (leftStmt q)
  | .branch f p q => .branch (fun v => f v.1) (leftStmt p) (leftStmt q)
  | .goto f => .goto (fun v => .inl (f v.1))
  | .halt => .goto (fun _ => .inr (.inl false))

def rightStmt : N.Stmt → Stmt M N Γm
  | .push k f q => .push (.inr (.inl k)) (fun v => f v.2.1) (rightStmt q)
  | .pop k f q => .pop (.inr (.inl k)) (fun v b => (v.1, f v.2.1 b, v.2.2)) (rightStmt q)
  | .peek k f q => .peek (.inr (.inl k)) (fun v b => (v.1, f v.2.1 b, v.2.2)) (rightStmt q)
  | .load f q => .load (fun v => (v.1, f v.2.1, v.2.2)) (rightStmt q)
  | .branch f p q => .branch (fun v => f v.2.1) (rightStmt p) (rightStmt q)
  | .goto f => .goto (fun v => .inr (.inr (f v.2.1)))
  | .halt => .halt

def leftCfg (c : M.Cfg) : Cfg M N Γm where
  l := some (c.l.elim (.inr (.inl false)) Sum.inl)
  var := (c.var, N.initialState, none)
  stk := joinedStacks M N Γm c.stk (fun _ => []) []

def rightCfg (c : N.Cfg) : Cfg M N Γm where
  l := c.l.map (fun l => .inr (.inr l))
  var := (M.initialState, c.var, none)
  stk := joinedStacks M N Γm (fun _ => []) c.stk []

theorem left_stepAux (q : M.Stmt) (v : M.σ) (s : (k : M.K) → List (M.Γ k)) :
    TM2.stepAux (leftStmt M N Γm q) (v, N.initialState, none)
      (joinedStacks M N Γm s (fun _ => []) []) = leftCfg M N Γm (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih => simpa only [leftStmt, TM2.stepAux, update_left] using! ih v _
  | pop k f q ih =>
      simpa only [leftStmt, TM2.stepAux, joinedStacks, update_left] using! ih (f v (s k).head?) _
  | peek k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f p q ihp ihq => cases hf : f v <;> simp [leftStmt, TM2.stepAux, hf, ihp, ihq]
  | goto f => rfl
  | halt => rfl

theorem right_stepAux (q : N.Stmt) (v : N.σ) (s : (k : N.K) → List (N.Γ k)) :
    TM2.stepAux (rightStmt M N Γm q) (M.initialState, v, none)
      (joinedStacks M N Γm (fun _ => []) s []) = rightCfg M N Γm (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih => simpa only [rightStmt, TM2.stepAux, update_right] using! ih v _
  | pop k f q ih =>
      simpa only [rightStmt, TM2.stepAux, joinedStacks, update_right] using! ih (f v (s k).head?) _
  | peek k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f p q ihp ihq => cases hf : f v <;> simp [rightStmt, TM2.stepAux, hf, ihp, ihq]
  | goto f => rfl
  | halt => rfl

variable (out : M.Γ M.k₁ ≃ Γm) (inp : N.Γ N.k₀ ≃ Γm)

def firstTransfer : Stmt M N Γm :=
  .pop (.inl M.k₁) (fun v b => (v.1, v.2.1, b.map out))
    (.branch (fun v => v.2.2.isSome)
      (.push (.inr (.inr ())) (fun v => v.2.2.getD default)
        (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => .inr (.inl false)))))
      (.goto (fun _ => .inr (.inl true))))

def secondTransfer : Stmt M N Γm :=
  .pop (.inr (.inr ())) (fun v b => (v.1, v.2.1, b))
    (.branch (fun v => v.2.2.isSome)
      (.push (.inr (.inl N.k₀)) (fun v => inp.symm (v.2.2.getD default))
        (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => .inr (.inl true)))))
      (.goto (fun _ => .inr (.inr N.main))))

def code : Label M N → Stmt M N Γm
  | .inl l => leftStmt M N Γm (M.m l)
  | .inr (.inl false) => firstTransfer M N Γm out
  | .inr (.inl true) => secondTransfer M N Γm inp
  | .inr (.inr l) => rightStmt M N Γm (N.m l)

def machine : FinTM2 where
  K := Key M N
  k₀ := .inl M.k₀
  k₁ := .inr (.inl N.k₁)
  Γ := Alphabet M N Γm
  Γk₀Fin := M.Γk₀Fin
  Λ := Label M N
  main := .inl M.main
  σ := State M N Γm
  initialState := (M.initialState, N.initialState, none)
  m := code M N Γm out inp

theorem left_step {c d : M.Cfg} (h : M.step c = some d) :
    (machine M N Γm out inp).step (leftCfg M N Γm c) = some (leftCfg M N Γm d) := by
  cases c with
  | mk l v s =>
      cases l with
      | none => simp [FinTM2.step, TM2.step] at h
      | some l =>
          have hd : TM2.stepAux (M.m l) v s = d := Option.some.inj h
          rw [← hd]
          exact congrArg some (left_stepAux M N Γm (M.m l) v s)

theorem right_step {c d : N.Cfg} (h : N.step c = some d) :
    (machine M N Γm out inp).step (rightCfg M N Γm c) = some (rightCfg M N Γm d) := by
  cases c with
  | mk l v s =>
      cases l with
      | none => simp [FinTM2.step, TM2.step] at h
      | some l =>
          have hd : TM2.stepAux (N.m l) v s = d := Option.some.inj h
          rw [← hd]
          exact congrArg some (right_stepAux M N Γm (N.m l) v s)


def single {K : Type} [DecidableEq K] (Γ : K → Type) (port : K) (xs : List (Γ port)) :
    (k : K) → List (Γ k) := Function.update (fun _ => []) port xs

def firstCfg (xs : List (M.Γ M.k₁)) (tmp : List Γm) : Cfg M N Γm where
  l := some (.inr (.inl false))
  var := (M.initialState, N.initialState, none)
  stk := joinedStacks M N Γm (single M.Γ M.k₁ xs) (fun _ => []) tmp

def secondCfg (tmp : List Γm) (ys : List (N.Γ N.k₀)) : Cfg M N Γm where
  l := some (.inr (.inl true))
  var := (M.initialState, N.initialState, none)
  stk := joinedStacks M N Γm (fun _ => []) (single N.Γ N.k₀ ys) tmp

theorem first_cons (x : M.Γ M.k₁) (xs : List (M.Γ M.k₁)) (tmp : List Γm) :
    (machine M N Γm out inp).step (firstCfg M N Γm (x :: xs) tmp) =
      some (firstCfg M N Γm xs (out x :: tmp)) := by
  simp [FinTM2.step, machine, code, firstTransfer, firstCfg, TM2.step, TM2.stepAux,
    update_left, update_tmp, joinedStacks, single, List.head?, List.tail]

theorem first_nil (tmp : List Γm) :
    (machine M N Γm out inp).step (firstCfg M N Γm [] tmp) = some (secondCfg M N Γm tmp []) := by
  simp [FinTM2.step, machine, code, firstTransfer, firstCfg, secondCfg, TM2.step, TM2.stepAux,
    update_left, joinedStacks, single, List.head?, List.tail]

theorem second_cons (b : Γm) (tmp : List Γm) (ys : List (N.Γ N.k₀)) :
    (machine M N Γm out inp).step (secondCfg M N Γm (b :: tmp) ys) =
      some (secondCfg M N Γm tmp (inp.symm b :: ys)) := by
  simp [FinTM2.step, machine, code, secondTransfer, secondCfg, TM2.step, TM2.stepAux,
    update_right, update_tmp, joinedStacks, single, List.head?, List.tail]

theorem second_nil (ys : List (N.Γ N.k₀)) :
    (machine M N Γm out inp).step (secondCfg M N Γm [] ys) = some (rightCfg M N Γm (initList N ys)) := by
  simp [FinTM2.step, machine, code, secondTransfer, secondCfg, rightCfg,
    TM2.step, TM2.stepAux, update_tmp, joinedStacks, single, initList, Function.update,
    List.head?, List.tail]
  congr 2
  funext k
  by_cases hk : k = N.k₀
  · subst k; simp
  · simp [hk]

theorem first_run (xs : List (M.Γ M.k₁)) (tmp : List Γm) :
    (fun c : Option (Cfg M N Γm) => c.bind (machine M N Γm out inp).step)^[xs.length + 1]
      (some (firstCfg M N Γm xs tmp)) =
      some (secondCfg M N Γm ((xs.map out).reverse ++ tmp) []) := by
  induction xs generalizing tmp with
  | nil => simpa using first_nil M N Γm out inp tmp
  | cons x xs ih =>
      rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply, Option.bind_some,
        first_cons, ih]
      simp

theorem second_run (tmp : List Γm) (ys : List (N.Γ N.k₀)) :
    (fun c : Option (Cfg M N Γm) => c.bind (machine M N Γm out inp).step)^[tmp.length + 1]
      (some (secondCfg M N Γm tmp ys)) =
      some (rightCfg M N Γm (initList N (tmp.reverse.map inp.symm ++ ys))) := by
  induction tmp generalizing ys with
  | nil => simpa using second_nil M N Γm out inp ys
  | cons b tmp ih =>
      rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply, Option.bind_some,
        second_cons, ih]
      simp

theorem left_halt (xs : List (M.Γ M.k₁)) : leftCfg M N Γm (haltList M xs) = firstCfg M N Γm xs [] := by
  simp [leftCfg, haltList, firstCfg, single, Function.update]
  congr 1
  funext k
  by_cases hk : k = M.k₁
  · subst k; simp
  · simp [hk]

/-- Exactly two linear transfers, including their end-of-stack tests. -/
theorem transfer_run (xs : List (M.Γ M.k₁)) :
    (fun c : Option (Cfg M N Γm) => c.bind (machine M N Γm out inp).step)^[2 * xs.length + 2]
      (some (leftCfg M N Γm (haltList M xs))) =
      some (rightCfg M N Γm (initList N ((xs.map out).map inp.symm))) := by
  have h₁ := first_run M N Γm out inp xs []
  have h₂ := second_run M N Γm out inp (xs.map out).reverse []
  simp only [List.append_nil] at h₁
  simp only [List.length_reverse, List.length_map, List.reverse_reverse, List.append_nil] at h₂
  have h := append_run (machine M N Γm out inp).step h₁ h₂
  rw [left_halt]
  simpa only [show xs.length + 1 + (xs.length + 1) = 2 * xs.length + 2 by omega] using! h

theorem initial_eq (xs : List (M.Γ M.k₀)) :
    initList (machine M N Γm out inp) xs = leftCfg M N Γm (initList M xs) := by
  apply cfg_ext
  · rfl
  · rfl
  funext k
  cases k with
  | inl k =>
      by_cases hk : k = M.k₀
      · subst k; simp [initList, machine, leftCfg, joinedStacks]
      · simp [initList, machine, leftCfg, joinedStacks, hk]
  | inr k => cases k <;> simp [initList, machine, leftCfg, joinedStacks]

theorem terminal_eq (ys : List (N.Γ N.k₁)) :
    rightCfg M N Γm (haltList N ys) = haltList (machine M N Γm out inp) ys := by
  apply cfg_ext
  · rfl
  · rfl
  funext k
  cases k with
  | inl k => simp [haltList, machine, rightCfg, joinedStacks]
  | inr k =>
      cases k with
      | inl k =>
          by_cases hk : k = N.k₁
          · subst k; simp [haltList, machine, rightCfg, joinedStacks]
          · simp [haltList, machine, rightCfg, joinedStacks, hk]
      | inr k => simp [haltList, machine, rightCfg, joinedStacks]


theorem eval_mono (p : Polynomial ℕ) {m n : ℕ} (h : m ≤ n) : p.eval m ≤ p.eval n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add] using Nat.add_le_add hp hq
  | monomial k c =>
      simp only [eval_monomial]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h k)

/-- Composition of polynomial-time functions with a binary intermediate encoding. -/
theorem comp {α β γ αΓ γΓ : Type} {eα : α → List αΓ} {Γm : Type} [Fintype Γm] [Inhabited Γm] {eβ : β → List Γm}
    {eγ : γ → List γΓ} {f : α → β} {g : β → γ}
    (h₁ : TM2ComputableInPolyTime eα eβ f) (h₂ : TM2ComputableInPolyTime eβ eγ g) :
    Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) := by
  classical
  let q : Polynomial ℕ := X + C (factor h₁.tm) * h₁.time
  let p : Polynomial ℕ := h₁.time + 2 * q + 2 + h₂.time.comp q
  let T := machine h₁.tm h₂.tm Γm h₁.outputAlphabet h₂.inputAlphabet
  refine ⟨{ tm := T
            inputAlphabet := h₁.inputAlphabet
            outputAlphabet := h₂.outputAlphabet
            time := p
            outputsFun := ?_ }⟩
  intro a
  let r₁ := h₁.outputsFun a
  let r₂ := h₂.outputsFun (f a)
  have hl : (eβ (f a)).length ≤ q.eval (eα a).length := by
    have h := output_length h₁.tm r₁
    simpa [q] using h
  have ht₂ : h₂.time.eval (eβ (f a)).length ≤ h₂.time.eval (q.eval (eα a).length) :=
    eval_mono h₂.time hl
  have hfirst := lift_run h₁.tm.step T.step (leftCfg h₁.tm h₂.tm Γm)
    (fun _ _ h => left_step h₁.tm h₂.tm Γm h₁.outputAlphabet h₂.inputAlphabet h)
    r₁.steps r₁.evals_in_steps
  have hcopy := transfer_run h₁.tm h₂.tm Γm h₁.outputAlphabet h₂.inputAlphabet
    ((eβ (f a)).map h₁.outputAlphabet.invFun)
  have hmiddle :
      (((eβ (f a)).map h₁.outputAlphabet.invFun).map h₁.outputAlphabet).map
        h₂.inputAlphabet.symm = (eβ (f a)).map h₂.inputAlphabet.invFun := by
    simp [List.map_map, Function.comp_def]
  rw [hmiddle] at hcopy
  have hsecond := lift_run h₂.tm.step T.step (rightCfg h₁.tm h₂.tm Γm)
    (fun _ _ h => right_step h₁.tm h₂.tm Γm h₁.outputAlphabet h₂.inputAlphabet h)
    r₂.steps r₂.evals_in_steps
  have hfull := append_run T.step (append_run T.step hfirst hcopy) hsecond
  refine ⟨⟨r₁.steps + (2 * (eβ (f a)).length + 2) + r₂.steps, ?_⟩, ?_⟩
  · simpa only [List.length_map, initial_eq,
      terminal_eq h₁.tm h₂.tm Γm h₁.outputAlphabet h₂.inputAlphabet, Function.comp_apply, T,
      Option.map_some] using! hfull
  · have hb₁ := r₁.steps_le_m
    have hb₂ := r₂.steps_le_m
    change r₁.steps ≤ h₁.time.eval (eα a).length at hb₁
    change r₂.steps ≤ h₂.time.eval (eβ (f a)).length at hb₂
    dsimp only [p]
    simp only [eval_add, eval_mul, eval_ofNat, eval_comp]
    omega


end Lax117284Proofs.Machine.TMCompose

end

/-! ### `Lax117284Proofs.Machine.TMToNats` -/

section
set_option backward.isDefEq.respectTransparency false

/-!
From a binary word to the encoding of its bits, on a Turing machine.

A bit becomes a number, and a number is written as a separator followed by its binary
digits; so `true` becomes a separator and a one, and `false` a separator alone. The
machine pops the word off its input stack writing those symbols to a work stack, which
reverses them, and then moves the work stack to the output stack, which reverses them
back. Both loops are linear.
-/

namespace Lax117284Proofs.Machine.TMToNats

open Turing Lax759944.BinaryWordEncoding Lax434930.PolynomialTime
open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram
open Lax117284Proofs.Machine.Bits

set_option genSizeOfSpec false in
/-- The three stacks. -/
inductive Key | inp | tmp | out
  deriving DecidableEq, Fintype

/-- The input is bits; the other two hold symbols. -/
def Γ : Key → Type
  | .inp => Bool
  | .tmp => Symbol
  | .out => Symbol

instance : Fintype (Γ .inp) := inferInstanceAs (Fintype Bool)

/-- Two registers: the bit and the symbol last popped. -/
abbrev Reg := Option Bool × Option Symbol

abbrev Prog := Program Γ Reg
abbrev St := Store Γ Reg

/-- A store, by its three stacks and its registers. -/
def st (i : List Bool) (t o : List Symbol) (r : Reg) : St where
  state := r
  stk := fun k => match k with
    | .inp => i
    | .tmp => t
    | .out => o

def rdI : Prog := .atom (.pop .inp (fun s b => (b, s.2)))
def rdT : Prog := .atom (.pop .tmp (fun s b => (s.1, b)))

def body1 : Prog :=
  .seq (.atom (.push .tmp (fun _ => Symbol.separator)))
    (.seq (.branch (fun s => s.1 == some true) (.atom (.push .tmp (fun _ => Symbol.one)))
        (.atom (.load id))) rdI)

abbrev loop1 : Prog := .loop (fun s => s.1.isSome) body1

def body2 : Prog := .seq (.atom (.push .out (fun s => s.2.getD Symbol.separator))) rdT

abbrev loop2 : Prog := .loop (fun s => s.2.isSome) body2

abbrev prog : Prog := .seq (.seq rdI loop1) (.seq rdT loop2)

/-- The symbols of one bit. -/
def enc (b : Bool) : List Symbol := if b then [.separator, .one] else [.separator]

lemma stk_ext {s t : St} (hs : s.state = t.state) (h : ∀ k, s.stk k = t.stk k) : s = t :=
  Store.ext _ _ hs (funext h)

lemma rdI_exec (i : List Bool) (t o : List Symbol) (r : Reg) :
    Executes rdI (st i t o r) (st i.tail t o (i.head?, r.2)) 1 := by
  have h := Executes.atom (Γ := Γ) (σ := Reg) (.pop .inp (fun s b => (b, s.2))) (st i t o r)
  have he : Op.apply (.pop .inp (fun (s : Reg) b => (b, s.2))) (st i t o r)
      = st i.tail t o (i.head?, r.2) := by
    refine stk_ext rfl fun k => ?_
    cases k <;> simp [Op.apply, st]
  rw [he] at h; exact h

lemma rdT_exec (i : List Bool) (t o : List Symbol) (r : Reg) :
    Executes rdT (st i t o r) (st i t.tail o (r.1, t.head?)) 1 := by
  have h := Executes.atom (Γ := Γ) (σ := Reg) (.pop .tmp (fun s b => (s.1, b))) (st i t o r)
  have he : Op.apply (.pop .tmp (fun (s : Reg) b => (s.1, b))) (st i t o r)
      = st i t.tail o (r.1, t.head?) := by
    refine stk_ext rfl fun k => ?_
    cases k <;> simp [Op.apply, st]
  rw [he] at h; exact h

lemma pushT_exec (i : List Bool) (t o : List Symbol) (r : Reg) (a : Symbol) :
    Executes (.atom (.push .tmp (fun _ => a))) (st i t o r) (st i (a :: t) o r) 1 := by
  have h := Executes.atom (Γ := Γ) (σ := Reg) (.push .tmp (fun _ => a)) (st i t o r)
  have he : Op.apply (.push .tmp (fun (_ : Reg) => a)) (st i t o r) = st i (a :: t) o r := by
    refine stk_ext rfl fun k => ?_
    cases k <;> simp [Op.apply, st]
  rw [he] at h; exact h

lemma pushO_exec (i : List Bool) (t o : List Symbol) (r : Reg) :
    Executes (.atom (.push .out (fun s : Reg => s.2.getD Symbol.separator)))
      (st i t o r) (st i t (r.2.getD Symbol.separator :: o) r) 1 := by
  have h := Executes.atom (Γ := Γ) (σ := Reg)
    (.push .out (fun s : Reg => s.2.getD Symbol.separator)) (st i t o r)
  have he : Op.apply (.push .out (fun s : Reg => s.2.getD Symbol.separator)) (st i t o r)
      = st i t (r.2.getD Symbol.separator :: o) r := by
    refine stk_ext rfl fun k => ?_
    cases k <;> simp [Op.apply, st]
  rw [he] at h; exact h

/-- The first loop writes the symbols of the word, reversed, onto the work stack. -/
lemma loop1_exec (bs : List Bool) (t o : List Symbol) (r2 : Option Symbol) :
    ∃ c ≤ 6 * bs.length + 1,
      Executes loop1 (st bs.tail t o (bs.head?, r2))
        (st [] ((bs.flatMap enc).reverse ++ t) o (none, r2)) c := by
  induction bs generalizing t with
  | nil => exact ⟨1, by simp, Executes.loop_false rfl⟩
  | cons b rest ih =>
      obtain ⟨c, hc, hrest⟩ := ih (t := (enc b).reverse ++ t)
      have hsep := pushT_exec rest t o (some b, r2) Symbol.separator
      cases b with
      | true =>
          have hone := pushT_exec rest (Symbol.separator :: t) o (some true, r2) Symbol.one
          have hrd := rdI_exec rest (Symbol.one :: Symbol.separator :: t) o (some true, r2)
          have hbody : Executes body1 (st rest t o (some true, r2))
              (st rest.tail (Symbol.one :: Symbol.separator :: t) o (rest.head?, r2)) _ :=
            .seq hsep (.seq (.branch_true (by rfl) hone) hrd)
          refine ⟨_, ?_, Executes.loop_true (b := fun s : Reg => s.1.isSome) rfl hbody
            (by simpa [enc] using hrest)⟩
          simp only [List.length_cons]; omega
      | false =>
          have hskip := Executes.atom (Γ := Γ) (σ := Reg) (.load id)
            (st rest (Symbol.separator :: t) o (some false, r2))
          have hrd := rdI_exec rest (Symbol.separator :: t) o (some false, r2)
          have hbody : Executes body1 (st rest t o (some false, r2))
              (st rest.tail (Symbol.separator :: t) o (rest.head?, r2)) _ :=
            .seq hsep (.seq (.branch_false (by rfl) hskip) hrd)
          refine ⟨_, ?_, Executes.loop_true (b := fun s : Reg => s.1.isSome) rfl hbody
            (by simpa [enc] using hrest)⟩
          simp only [List.length_cons]; omega

/-- The second loop moves the work stack to the output, reversing it again. -/
lemma loop2_exec (ts o : List Symbol) :
    ∃ c ≤ 3 * ts.length + 1,
      Executes loop2 (st [] ts.tail o (none, ts.head?)) (st [] [] (ts.reverse ++ o) (none, none)) c := by
  induction ts generalizing o with
  | nil => exact ⟨1, by simp, Executes.loop_false rfl⟩
  | cons a rest ih =>
      obtain ⟨c, hc, hrest⟩ := ih (o := a :: o)
      have hp := pushO_exec [] rest o (none, some a)
      have hrd := rdT_exec [] rest (a :: o) (none, some a)
      refine ⟨_, ?_, Executes.loop_true (b := fun s : Reg => s.2.isSome) rfl (.seq hp hrd)
        (by simpa using hrest)⟩
      simp only [List.length_cons]; omega

lemma enc_length (w : Word) : (w.flatMap enc).length ≤ 2 * w.length := by
  induction w with
  | nil => simp
  | cons b t ih => cases b <;> simp [enc] at ih ⊢ <;> omega

lemma encode_natBits (w : Word) : encode (natBits w) = w.flatMap enc := by
  induction w with
  | nil => rfl
  | cons b t ih =>
      simp only [natBits, List.map_cons, encode, List.flatMap_cons] at ih ⊢
      rw [ih]
      cases b <;> simp [enc, encodeNat]

lemma ioStore_inp (w : Word) : ioStore (Γ := Γ) Key.inp ((none, none) : Reg) w = st w [] [] (none, none) := by
  refine stk_ext rfl fun k => ?_
  cases k <;> simp [ioStore, st]

lemma ioStore_out (o : List Symbol) :
    ioStore (Γ := Γ) Key.out ((none, none) : Reg) o = st [] [] o (none, none) := by
  refine stk_ext rfl fun k => ?_
  cases k <;> simp [ioStore, st]

/-- **A binary word becomes the encoding of its bits in linear time.** -/
theorem toNats : Nonempty (TM2ComputableInPolyTime id encode natBits) := by
  refine program_polytime prog Key.inp Key.out ((none, none) : Reg) id encode natBits
    (Polynomial.C 18 * Polynomial.X + Polynomial.C 8) fun w => ?_
  obtain ⟨c1, hc1, h1⟩ := loop1_exec w [] [] none
  obtain ⟨c2, hc2, h2⟩ := loop2_exec ((w.flatMap enc).reverse ++ []) []
  have hr1 := rdI_exec w [] [] (none, none)
  have hr2 := rdT_exec [] ((w.flatMap enc).reverse ++ []) [] (none, none)
  have hlen := enc_length w
  refine ⟨1 + c1 + (1 + c2), ?_, ?_⟩
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      id]
    simp only [List.append_nil, List.length_reverse] at hc2
    omega
  · rw [ioStore_inp, ioStore_out, encode_natBits]
    have := Executes.seq (Executes.seq hr1 h1) (Executes.seq hr2 h2)
    simpa using this

end Lax117284Proofs.Machine.TMToNats

end

/-! ### `Lax117284Proofs.Machine.TMToBits` -/

section
set_option backward.isDefEq.respectTransparency false

/-!
From the encoding of a list of numbers to the binary word saying which are nonzero, on a
Turing machine.

A number is written as a separator followed by its binary digits, and zero has none; so a
number is nonzero exactly when a digit follows its separator. The machine reads the
symbols once, remembering for the number in progress whether a digit has been seen, and
writes that bit to a work stack when the next separator or the end of the input arrives.
A second loop moves the work stack to the output, restoring the order.
-/

namespace Lax117284Proofs.Machine.TMToBits

open Turing Lax759944.BinaryWordEncoding Lax434930.PolynomialTime
open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram
open Lax117284Proofs.Machine.Bits

set_option genSizeOfSpec false in
inductive Key | inp | tmp | out
  deriving DecidableEq, Fintype

def Γ : Key → Type
  | .inp => Symbol
  | .tmp => Bool
  | .out => Bool

instance : Fintype (Γ .inp) := inferInstanceAs (Fintype Symbol)

/-- The symbol last read, the bit of the number in progress, and the bit last popped. -/
abbrev Reg := Option Symbol × Option Bool × Option Bool

abbrev Prog := Program Γ Reg
abbrev St := Store Γ Reg

def st (i : List Symbol) (t o : List Bool) (r : Reg) : St where
  state := r
  stk := fun k => match k with
    | .inp => i
    | .tmp => t
    | .out => o

lemma stk_ext {s t : St} (hs : s.state = t.state) (h : ∀ k, s.stk k = t.stk k) : s = t :=
  Store.ext _ _ hs (funext h)

abbrev rdI : Prog := .atom (.pop .inp (fun s b => (b, s.2.1, s.2.2)))
abbrev rdT : Prog := .atom (.pop .tmp (fun s b => (s.1, s.2.1, b)))
abbrev flush : Prog :=
  .branch (fun s => s.2.1.isSome) (.atom (.push .tmp (fun s => s.2.1.getD false)))
    (.atom (.load id))
abbrev setP (b : Option Bool) : Prog := .atom (.load (fun s => (s.1, b, s.2.2)))

abbrev body1 : Prog :=
  .seq (.branch (fun s => s.1 == some Symbol.separator) (.seq flush (setP (some false)))
      (setP (some true))) rdI

abbrev loop1 : Prog := .loop (fun s => s.1.isSome) body1
abbrev body2 : Prog := .seq (.atom (.push .out (fun s => s.2.2.getD false))) rdT
abbrev loop2 : Prog := .loop (fun s => s.2.2.isSome) body2
abbrev prog : Prog :=
  .seq (.seq rdI loop1) (.seq (.seq flush (setP none)) (.seq rdT loop2))

/-- The bits the first loop has pushed, in order, from pending bit `p` on symbols `l`. -/
def emitted : Option Bool → List Symbol → List Bool
  | _, [] => []
  | p, .separator :: r => p.toList ++ emitted (some false) r
  | _, _ :: r => emitted (some true) r

/-- The pending bit when the symbols run out. -/
def pendAfter : Option Bool → List Symbol → Option Bool
  | p, [] => p
  | _, .separator :: r => pendAfter (some false) r
  | _, _ :: r => pendAfter (some true) r

lemma rdI_exec (i : List Symbol) (t o : List Bool) (r : Reg) :
    Executes rdI (st i t o r) (st i.tail t o (i.head?, r.2.1, r.2.2)) 1 := by
  have h := Executes.atom (Γ := Γ) (σ := Reg) (.pop .inp (fun s b => (b, s.2.1, s.2.2)))
    (st i t o r)
  have he : Op.apply (.pop .inp (fun (s : Reg) b => (b, s.2.1, s.2.2))) (st i t o r)
      = st i.tail t o (i.head?, r.2.1, r.2.2) := by
    refine stk_ext rfl fun k => ?_
    cases k <;> simp [Op.apply, st]
  rw [he] at h; exact h

lemma rdT_exec (i : List Symbol) (t o : List Bool) (r : Reg) :
    Executes rdT (st i t o r) (st i t.tail o (r.1, r.2.1, t.head?)) 1 := by
  have h := Executes.atom (Γ := Γ) (σ := Reg) (.pop .tmp (fun s b => (s.1, s.2.1, b)))
    (st i t o r)
  have he : Op.apply (.pop .tmp (fun (s : Reg) b => (s.1, s.2.1, b))) (st i t o r)
      = st i t.tail o (r.1, r.2.1, t.head?) := by
    refine stk_ext rfl fun k => ?_
    cases k <;> simp [Op.apply, st]
  rw [he] at h; exact h

lemma setP_exec (i : List Symbol) (t o : List Bool) (r : Reg) (b : Option Bool) :
    Executes (setP b) (st i t o r) (st i t o (r.1, b, r.2.2)) 1 := by
  have h := Executes.atom (Γ := Γ) (σ := Reg) (.load (fun s => (s.1, b, s.2.2))) (st i t o r)
  exact h

/-- Flushing pushes the pending bit, if there is one. -/
lemma flush_exec (i : List Symbol) (t o : List Bool) (r : Reg) :
    Executes flush (st i t o r) (st i (r.2.1.toList.reverse ++ t) o r) 2 := by
  rcases hp : r.2.1 with _ | b
  · have h := Executes.atom (Γ := Γ) (σ := Reg) (.load id) (st i t o r)
    have he : Op.apply (.load id) (st i t o r) = st i t o r := rfl
    rw [he] at h
    have := Executes.branch_false (p := .atom (.push .tmp (fun s : Reg => s.2.1.getD false)))
      (b := fun s : Reg => s.2.1.isSome) (by simp [st, hp]) h
    simpa using this
  · have h := Executes.atom (Γ := Γ) (σ := Reg) (.push .tmp (fun s : Reg => s.2.1.getD false))
      (st i t o r)
    have he : Op.apply (.push .tmp (fun s : Reg => s.2.1.getD false)) (st i t o r)
        = st i (b :: t) o r := by
      refine stk_ext rfl fun k => ?_
      cases k <;> simp [Op.apply, st, hp]
    rw [he] at h
    have := Executes.branch_true (q := .atom (.load id))
      (b := fun s : Reg => s.2.1.isSome) (by simp [st, hp]) h
    simpa using this

lemma pushO_exec (i : List Symbol) (t o : List Bool) (r : Reg) :
    Executes (.atom (.push .out (fun s : Reg => s.2.2.getD false)))
      (st i t o r) (st i t (r.2.2.getD false :: o) r) 1 := by
  have h := Executes.atom (Γ := Γ) (σ := Reg)
    (.push .out (fun s : Reg => s.2.2.getD false)) (st i t o r)
  have he : Op.apply (.push .out (fun s : Reg => s.2.2.getD false)) (st i t o r)
      = st i t (r.2.2.getD false :: o) r := by
    refine stk_ext rfl fun k => ?_
    cases k <;> simp [Op.apply, st]
  rw [he] at h; exact h

lemma loop1_exec (l : List Symbol) (p : Option Bool) (t o : List Bool) (r3 : Option Bool) :
    ∃ c ≤ 6 * l.length + 1,
      Executes loop1 (st l.tail t o (l.head?, p, r3))
        (st [] ((emitted p l).reverse ++ t) o (none, pendAfter p l, r3)) c := by
  induction l generalizing p t with
  | nil => exact ⟨1, by simp, by simpa [emitted, pendAfter] using Executes.loop_false rfl⟩
  | cons a rest ih =>
      cases a with
      | separator =>
          obtain ⟨c, hc, hrest⟩ := ih (p := some false) (t := p.toList.reverse ++ t)
          have hf := flush_exec rest t o (some Symbol.separator, p, r3)
          have hs := setP_exec rest (p.toList.reverse ++ t) o (some Symbol.separator, p, r3)
            (some false)
          have hrd := rdI_exec rest (p.toList.reverse ++ t) o
            (some Symbol.separator, some false, r3)
          have hbody : Executes body1 (st rest t o (some Symbol.separator, p, r3))
              (st rest.tail (p.toList.reverse ++ t) o (rest.head?, some false, r3)) _ :=
            .seq (.branch_true (by rfl) (.seq hf hs)) hrd
          refine ⟨_, ?_, Executes.loop_true (b := fun s : Reg => s.1.isSome) rfl hbody
            (by simpa [emitted, pendAfter] using hrest)⟩
          simp only [List.length_cons]; omega
      | zero =>
          obtain ⟨c, hc, hrest⟩ := ih (p := some true) (t := t)
          have hs := setP_exec rest t o (some Symbol.zero, p, r3) (some true)
          have hrd := rdI_exec rest t o (some Symbol.zero, some true, r3)
          have hbody : Executes body1 (st rest t o (some Symbol.zero, p, r3))
              (st rest.tail t o (rest.head?, some true, r3)) _ :=
            .seq (.branch_false (by rfl) hs) hrd
          refine ⟨_, ?_, Executes.loop_true (b := fun s : Reg => s.1.isSome) rfl hbody
            (by simpa [emitted, pendAfter] using hrest)⟩
          simp only [List.length_cons]; omega
      | one =>
          obtain ⟨c, hc, hrest⟩ := ih (p := some true) (t := t)
          have hs := setP_exec rest t o (some Symbol.one, p, r3) (some true)
          have hrd := rdI_exec rest t o (some Symbol.one, some true, r3)
          have hbody : Executes body1 (st rest t o (some Symbol.one, p, r3))
              (st rest.tail t o (rest.head?, some true, r3)) _ :=
            .seq (.branch_false (by rfl) hs) hrd
          refine ⟨_, ?_, Executes.loop_true (b := fun s : Reg => s.1.isSome) rfl hbody
            (by simpa [emitted, pendAfter] using hrest)⟩
          simp only [List.length_cons]; omega

lemma loop2_exec (ts o : List Bool) :
    ∃ c ≤ 3 * ts.length + 1,
      Executes loop2 (st [] ts.tail o (none, none, ts.head?))
        (st [] [] (ts.reverse ++ o) (none, none, none)) c := by
  induction ts generalizing o with
  | nil => exact ⟨1, by simp, Executes.loop_false rfl⟩
  | cons a rest ih =>
      obtain ⟨c, hc, hrest⟩ := ih (o := a :: o)
      have hp := pushO_exec [] rest o (none, none, some a)
      have hrd := rdT_exec [] rest (a :: o) (none, none, some a)
      refine ⟨_, ?_, Executes.loop_true (b := fun s : Reg => s.2.2.isSome) rfl (.seq hp hrd)
        (by simpa using hrest)⟩
      simp only [List.length_cons]; omega

/-! ### What the loop computes -/

/-- Everything the machine writes: the bits pushed, then the pending one. -/
def total (p : Option Bool) (l : List Symbol) : List Bool :=
  emitted p l ++ (pendAfter p l).toList

lemma total_sep (p : Option Bool) (r : List Symbol) :
    total p (Symbol.separator :: r) = p.toList ++ total (some false) r := by
  simp [total, emitted, pendAfter]

lemma total_digits (p : Option Bool) (ds r : List Symbol)
    (hds : ∀ s ∈ ds, s ≠ Symbol.separator) :
    total p (ds ++ r) = total (if ds = [] then p else some true) r := by
  induction ds generalizing p with
  | nil => simp
  | cons a ds ih =>
      have ha : a ≠ Symbol.separator := hds a (by simp)
      have hstep : total p (a :: (ds ++ r)) = total (some true) (ds ++ r) := by
        cases a <;> simp_all [total, emitted, pendAfter]
      rw [List.cons_append, hstep, ih _ (fun s hs => hds s (by simp [hs]))]
      by_cases h : ds = [] <;> simp [h]

lemma bits_eq_nil_iff (n : ℕ) : n.bits = [] ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    have h1 : n.bits.length = n.size := Nat.size_eq_bits_len n
    have h2 : 0 < n.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [h] at h1; simp at h1; omega
  · rintro rfl; simp

lemma total_encodeNat (p : Option Bool) (n : ℕ) (r : List Symbol) :
    total p (encodeNat n ++ r) = p.toList ++ total (some (decide (n ≠ 0))) r := by
  rw [encodeNat, List.cons_append, total_sep, total_digits _ _ _ (by
    intro s hs
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
    cases b <;> simp)]
  congr 2
  by_cases hn : n = 0
  · subst hn; simp
  · have : n.bits ≠ [] := fun h => hn ((bits_eq_nil_iff n).mp h)
    simp [this, hn]

lemma total_encode (p : Option Bool) (l : List ℕ) :
    total p (encode l) = p.toList ++ bitsOf l := by
  induction l generalizing p with
  | nil => simp [total, encode, emitted, pendAfter, bitsOf]
  | cons n l ih =>
      rw [show encode (n :: l) = encodeNat n ++ encode l by simp [encode], total_encodeNat, ih]
      simp [bitsOf]

lemma ioStore_inp (w : List Symbol) :
    ioStore (Γ := Γ) Key.inp ((none, none, none) : Reg) w = st w [] [] (none, none, none) := by
  refine stk_ext rfl fun k => ?_
  cases k <;> simp [ioStore, st]

lemma ioStore_out (o : List Bool) :
    ioStore (Γ := Γ) Key.out ((none, none, none) : Reg) o = st [] [] o (none, none, none) := by
  refine stk_ext rfl fun k => ?_
  cases k <;> simp [ioStore, st]

lemma emitted_length (p : Option Bool) (l : List Symbol) :
    (emitted p l).length + (pendAfter p l).toList.length ≤ l.length + 1 := by
  induction l generalizing p with
  | nil => cases p <;> simp [emitted, pendAfter]
  | cons a r ih =>
      cases a
      · have := ih (some false)
        cases p <;> simp [emitted, pendAfter] at this ⊢ <;> omega
      · have := ih (some true); simp [emitted, pendAfter] at this ⊢; omega
      · have := ih (some true); simp [emitted, pendAfter] at this ⊢; omega

/-- **The encoding of a list of numbers becomes its word of nonzero flags in linear
time.** -/
theorem toBits : Nonempty (TM2ComputableInPolyTime encode id bitsOf) := by
  refine program_polytime prog Key.inp Key.out ((none, none, none) : Reg) encode id bitsOf
    (Polynomial.C 12 * Polynomial.X + Polynomial.C 12) fun l => ?_
  set w := encode l with hw
  obtain ⟨c1, hc1, h1⟩ := loop1_exec w none [] [] none
  have hr1 := rdI_exec w [] [] (none, none, none)
  have hf := flush_exec [] ((emitted none w).reverse ++ []) [] (none, pendAfter none w, none)
  have hs := setP_exec [] ((pendAfter none w).toList.reverse ++ ((emitted none w).reverse ++ []))
    [] (none, pendAfter none w, none) none
  have htot : (pendAfter none w).toList.reverse ++ ((emitted none w).reverse ++ [])
      = (bitsOf l).reverse := by
    have := total_encode none l
    simp only [total, Option.toList_none, List.nil_append] at this
    rw [← this, ← hw]; simp
  rw [htot] at hs hf
  obtain ⟨c2, hc2, h2⟩ := loop2_exec (bitsOf l).reverse []
  have hr2 := rdT_exec [] (bitsOf l).reverse [] (none, none, none)
  have hlen := emitted_length none w
  have hbl : (bitsOf l).length ≤ w.length + 1 := by
    have := congrArg List.length htot
    simp at this; omega
  refine ⟨1 + c1 + (2 + 1 + (1 + c2)), ?_, ?_⟩
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    simp only [List.length_reverse] at hc2
    omega
  · rw [ioStore_inp, ioStore_out]
    have := Executes.seq (Executes.seq hr1 h1) (Executes.seq (Executes.seq hf hs)
      (Executes.seq hr2 h2))
    simpa using this

end Lax117284Proofs.Machine.TMToBits

end

/-! ### `Lax117284Proofs.Machine.RamToTuring` -/

section
/-!
A map on binary words that a word RAM computes in polynomial time, on the zeros and ones
of its input, is polynomial-time computable on a Turing machine.
-/

namespace Lax117284Proofs.Machine.RamToTuring

open Turing Lax434930.PolynomialTime Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax117284Proofs.Machine.Bits

theorem polyTime_of_ram {f : Word → Word} {g : List ℕ → List ℕ} (hg : RamPolytime g)
    (h : ∀ w, g (natBits w) = natBits (f w)) :
    Nonempty (TM2ComputableInPolyTime id id f) := by
  obtain ⟨t1⟩ := Lax117284Proofs.Machine.TMToNats.toNats
  obtain ⟨t2⟩ :=
    (Lax759944Proofs.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime g).mp hg
  obtain ⟨t3⟩ := Lax117284Proofs.Machine.TMToBits.toBits
  obtain ⟨c12⟩ := Lax117284Proofs.Machine.TMCompose.comp t1 t2
  obtain ⟨c⟩ := Lax117284Proofs.Machine.TMCompose.comp c12 t3
  refine ⟨{ tm := c.tm, inputAlphabet := c.inputAlphabet, outputAlphabet := c.outputAlphabet,
            time := c.time, outputsFun := fun w => ?_ }⟩
  have hc := c.outputsFun w
  simp only [Function.comp_apply, h, bitsOf_natBits] at hc
  exact hc

end Lax117284Proofs.Machine.RamToTuring

end
