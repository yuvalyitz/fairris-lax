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
