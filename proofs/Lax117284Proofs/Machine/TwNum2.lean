import Mathlib.Tactic
import Lax117284Proofs.Machine.TwNum1

/-!
Polynomial bounds: a quantity depending on the word is *polynomially bounded* on a set of words
when some `C * a x ^ E`, with `C` and `E` fixed, bounds it on every word of the set, where `a x`
is a size of the word. These are closed under sums and products.
-/

namespace Lax117284Proofs.Machine.TwNum

/-- `f` is at most `C * a x ^ E` on the words satisfying `P`, for some constants. -/
def PlOn (a : List ℕ → ℕ) (P : List ℕ → Prop) (f : List ℕ → ℕ) : Prop :=
  ∃ C E : ℕ, ∀ x, P x → f x ≤ C * a x ^ E

variable {a : List ℕ → ℕ} {P : List ℕ → Prop} {f g : List ℕ → ℕ}

theorem PlOn.mono (h : PlOn a P g) (hle : ∀ x, P x → f x ≤ g x) : PlOn a P f := by
  obtain ⟨C, E, h⟩ := h
  exact ⟨C, E, fun x hx => (hle x hx).trans (h x hx)⟩

theorem PlOn.const (c : ℕ) : PlOn a P (fun _ => c) := ⟨c, 0, fun x _ => by simp⟩

theorem PlOn.base : PlOn a P a := ⟨1, 1, fun x _ => by simp⟩

theorem PlOn.add (ha : ∀ x, P x → 1 ≤ a x) (hf : PlOn a P f) (hg : PlOn a P g) :
    PlOn a P (fun x => f x + g x) := by
  obtain ⟨C1, E1, h1⟩ := hf
  obtain ⟨C2, E2, h2⟩ := hg
  refine ⟨C1 + C2, max E1 E2, fun x hx => ?_⟩
  have h3 : a x ^ E1 ≤ a x ^ max E1 E2 := Nat.pow_le_pow_right (ha x hx) (le_max_left _ _)
  have h4 : a x ^ E2 ≤ a x ^ max E1 E2 := Nat.pow_le_pow_right (ha x hx) (le_max_right _ _)
  calc f x + g x ≤ C1 * a x ^ E1 + C2 * a x ^ E2 := Nat.add_le_add (h1 x hx) (h2 x hx)
    _ ≤ C1 * a x ^ max E1 E2 + C2 * a x ^ max E1 E2 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h3) (Nat.mul_le_mul_left _ h4)
    _ = (C1 + C2) * a x ^ max E1 E2 := by ring

theorem PlOn.mul (hf : PlOn a P f) (hg : PlOn a P g) : PlOn a P (fun x => f x * g x) := by
  obtain ⟨C1, E1, h1⟩ := hf
  obtain ⟨C2, E2, h2⟩ := hg
  refine ⟨C1 * C2, E1 + E2, fun x hx => ?_⟩
  calc f x * g x ≤ (C1 * a x ^ E1) * (C2 * a x ^ E2) := Nat.mul_le_mul (h1 x hx) (h2 x hx)
    _ = C1 * C2 * a x ^ (E1 + E2) := by ring

theorem PlOn.pow (hf : PlOn a P f) (e : ℕ) : PlOn a P (fun x => f x ^ e) := by
  obtain ⟨C, E, h⟩ := hf
  refine ⟨C ^ e, E * e, fun x hx => ?_⟩
  calc f x ^ e ≤ (C * a x ^ E) ^ e := Nat.pow_le_pow_left (h x hx) _
    _ = C ^ e * a x ^ (E * e) := by rw [mul_pow, ← pow_mul]

open Classical in
/-- A quantity that is set to zero unless a condition holds, bounded where it holds. -/
theorem PlOn.guard {Q : List ℕ → Prop} (h : PlOn a (fun x => P x ∧ Q x) f) :
    PlOn a P (fun x => if Q x then f x else 0) := by
  obtain ⟨C, E, h⟩ := h
  refine ⟨C, E, fun x hx => ?_⟩
  by_cases hq : Q x
  · show (if Q x then f x else 0) ≤ _
    rw [if_pos hq]; exact h x ⟨hx, hq⟩
  · show (if Q x then f x else 0) ≤ _
    rw [if_neg hq]; exact Nat.zero_le _

/-- A bigger size gives the same bounds. -/
theorem PlOn.base_mono {b : List ℕ → ℕ} (h : PlOn a P f) (hab : ∀ x, P x → a x ≤ b x) :
    PlOn b P f := by
  obtain ⟨C, E, h⟩ := h
  exact ⟨C, E, fun x hx => (h x hx).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hab x hx) _))⟩

end Lax117284Proofs.Machine.TwNum
