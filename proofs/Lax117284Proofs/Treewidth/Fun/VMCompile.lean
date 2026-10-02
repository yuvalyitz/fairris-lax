import Lax117284Proofs.Treewidth.Fun.VMDefs

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
