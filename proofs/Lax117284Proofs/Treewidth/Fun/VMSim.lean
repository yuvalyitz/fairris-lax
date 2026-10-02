import Lax117284Proofs.Treewidth.Fun.VMCompile

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
