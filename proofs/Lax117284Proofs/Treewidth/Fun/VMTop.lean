import Lax117284Proofs.Treewidth.Fun.VMSimCall

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

/-- The assembled program realizes the table. -/
theorem mkProg_real (Δ : ℕ → Option Tm) {N : ℕ} (hN : ∀ f, N ≤ f → Δ f = none) (main k B : ℕ) :
    (mkProg Δ N main k B).Real Δ := by
  intro f body hf
  have hfN : f < N := by
    by_contra h
    have := hN f (by omega); rw [this] at hf; simp at hf
  have hfit := mkProg_fits Δ hfN main k B
  have hcode : funCode Δ f = compile id body ++ [.ret] := by simp [funCode, hf]
  rw [hcode] at hfit
  refine ⟨?_, hfit⟩
  have h1 := hfit.1
  have h2 := le_offset Δ f
  show f ≤ (mkProg Δ N main k B).len
  have : (mkProg Δ N main k B).ft f = offset Δ f := rfl
  omega

theorem mkProg_halt (Δ : ℕ → Option Tm) (N main k B : ℕ) (s : St) (h : s.pc = 2) :
    (mkProg Δ N main k B).step s = none := by
  have := (mkProg_stub Δ N main k B).2 2 (by simp [stub])
  have hc : (mkProg Δ N main k B).code 2 = .halt := by simpa [stub] using this
  simp [Prog.step, h, hc]

/-- **V1 theorem.**  `W` is any bound with the (explicit) budget below. -/
theorem vm_runs (Δ : ℕ → Option Tm) {N : ℕ} (hN : ∀ f, N ≤ f → Δ f = none) {B : ℕ} (hB : 2 ≤ B)
    {main : ℕ} {xs : List Val} {y : Val} {c : ℕ} (h : Runs Δ B main xs y c) {ws stk₀ : List ℕ}
    {H : List (ℕ × ℕ)} (hrep : RepL B H ws xs) {W : ℕ}
    (hbd : St.Bd W ⟨0, ws ++ stk₀, [], H⟩) (hL : (mkProg Δ N main xs.length B).len ≤ W)
    (hheap : B + H.length + c ≤ W) (hstk : (ws ++ stk₀).length + 3 * c ≤ W) (hret : 3 * c + 1 ≤ W) :
    ∃ n ≤ 3 * c + 3, ∃ (w : ℕ) (H' : List (ℕ × ℕ)),
      StepsB (mkProg Δ N main xs.length B) W n ⟨0, ws ++ stk₀, [], H⟩ ⟨2, w :: stk₀, [], H'⟩ ∧
        HExt H H' ∧ Rep B H' w y ∧ H'.length ≤ H.length + c := by
  obtain ⟨body, hΔ, c', hc', hev⟩ := h
  have hreal := mkProg_real Δ hN main xs.length B
  have hstub := mkProg_stub Δ N main xs.length B
  have hPB : (mkProg Δ N main xs.length B).B = B := rfl
  generalize mkProg Δ N main xs.length B = P at hreal hstub hL hPB ⊢
  subst hPB
  have hsim := ev_sim hB hreal hev
  have hpos := hev.pos
  have hlen3 : 3 ≤ P.len := by simpa [stub] using hstub.1
  have hcode0 : P.code 0 = .lit main := by simpa [stub] using hstub.head
  have hcode1 : P.code 1 = .call ws.length := by
    have := (hstub.tail).head
    simpa [stub, hrep.length_eq] using this
  have hmain : main ≤ W := Nat.le_trans (hreal main body hΔ).1 hL
  have hstep := step_lit (P := P) (s := ⟨0, ws ++ stk₀, [], H⟩) hcode0
  have hbd₁ : St.Bd W ⟨0 + 1, main :: (ws ++ stk₀), [], H⟩ :=
    hbd.setStk (by omega) (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hmain
      · exact hbd.stk x hx) (by simp only [List.length_cons]; omega)
  obtain ⟨n, hn, w, H', hs, hx, hr, hh⟩ := callee_run hreal hΔ hsim (ws := ws) (stk₀ := stk₀) (ret₀ := [])
    (H := H) (pcc := 1) hcode1 hrep hbd₁ hL (by omega) (by omega) (by omega) (by show 0 + 1 + 3 * c' ≤ W; omega)
  exact ⟨n + 1, by omega, w, H', StepsB.step hbd hstep hs, hx, hr, by omega⟩

/-- Words are bounded by the heap: a representation of a value uses only words `< B + |H|`. -/
theorem Rep.lt {B : ℕ} {H : List (ℕ × ℕ)} {w : ℕ} {v : Val} (h : Rep B H w v) : w < B + H.length := by
  cases h with
  | nat hn => omega
  | cons hp _ _ =>
    have := (List.getElem?_eq_some_iff.mp hp).1
    omega

theorem StepsB.mono_W {P : Prog} {W W' n : ℕ} {s s' : St} (h : StepsB P W n s s') (hW : W ≤ W') :
    StepsB P W' n s s' := by
  induction h with
  | refl hb => exact .refl (hb.mono hW)
  | step hb hs _ ih => exact .step (hb.mono hW) hs ih

/-- **V1, with the word accounting made explicit.**  If the naturals of the initial state are `≤ W₀`, then all
naturals of all states of the run (pc, stack words, saved pcs and heights, heap words, all lengths) are
`≤ W₀ + P.len + B + 3c + 3`; the machine halts (`step = none`) at the end. -/
theorem vm_correct (Δ : ℕ → Option Tm) {N : ℕ} (hN : ∀ f, N ≤ f → Δ f = none) {B : ℕ} (hB : 2 ≤ B)
    {main : ℕ} {xs : List Val} {y : Val} {c : ℕ} (h : Runs Δ B main xs y c) {ws stk₀ : List ℕ}
    {H : List (ℕ × ℕ)} (hrep : RepL B H ws xs) {W₀ : ℕ} (hbd : St.Bd W₀ ⟨0, ws ++ stk₀, [], H⟩) :
    ∃ n ≤ 3 * c + 3, ∃ (w : ℕ) (H' : List (ℕ × ℕ)),
      StepsB (mkProg Δ N main xs.length B) (W₀ + (mkProg Δ N main xs.length B).len + B + 3 * c + 3) n
        ⟨0, ws ++ stk₀, [], H⟩ ⟨2, w :: stk₀, [], H'⟩ ∧
      (mkProg Δ N main xs.length B).step ⟨2, w :: stk₀, [], H'⟩ = none ∧
        HExt H H' ∧ Rep B H' w y ∧ H'.length ≤ H.length + c := by
  have h1 : H.length ≤ W₀ := hbd.heapLen
  have h2 : (ws ++ stk₀).length ≤ W₀ := hbd.stkLen
  obtain ⟨n, hn, w, H', hs, hx, hr, hh⟩ := vm_runs Δ hN hB h hrep
    (W := W₀ + (mkProg Δ N main xs.length B).len + B + 3 * c + 3) (hbd.mono (by omega)) (by omega)
    (by omega) (by omega) (by omega)
  exact ⟨n, hn, w, H', hs, mkProg_halt Δ N main xs.length B _ rfl, hx, hr, hh⟩

/-! ## building representations (for the loader of WP V3) -/

/-- The number of `cons` nodes of a value (= the heap cells needed to represent it). -/
def _root_.Lax117284Proofs.Treewidth.Fun.Val.cells : Val → ℕ
  | .nat _ => 0
  | .cons a b => a.cells + b.cells + 1

/-- Every value with all its naturals `< B` can be laid out in the heap, allocating exactly `v.cells` cells;
all pointers/words stay `< B + |H'|` and the new cells only mention words below that. -/
theorem exists_rep (B : ℕ) (v : Val) (hv : v.maxNat < B) (H : List (ℕ × ℕ)) :
    ∃ (w : ℕ) (H' : List (ℕ × ℕ)), HExt H H' ∧ Rep B H' w v ∧ H'.length = H.length + v.cells := by
  induction v generalizing H with
  | nat n => exact ⟨n, H, HExt.refl _, .nat hv, by simp [Val.cells]⟩
  | cons a b iha ihb =>
    have ha : a.maxNat < B := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hv
    have hb : b.maxNat < B := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv
    obtain ⟨wa, H₁, hx₁, hra, hl₁⟩ := iha ha H
    obtain ⟨wb, H₂, hx₂, hrb, hl₂⟩ := ihb hb H₁
    refine ⟨B + H₂.length, H₂ ++ [(wa, wb)], (hx₁.trans hx₂).trans (HExt.snoc _ _),
      .cons (p := H₂.length) (by simp) ((hra.mono hx₂).mono (HExt.snoc _ _)) (hrb.mono (HExt.snoc _ _)),
      by simp [Val.cells]; omega⟩

end Lax117284Proofs.Treewidth.Fun.VM
