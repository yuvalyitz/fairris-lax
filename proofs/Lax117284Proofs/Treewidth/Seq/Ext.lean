import Lax117284Proofs.Treewidth.Seq.Typical
import Mathlib.Data.List.Forall2
import Mathlib.Tactic.Ring

/-!
# Extensions of integer sequences (Def. 3.6) and Lemma 3.6

`Ext a a'` says `a' ∈ E(a)`: `a'` arises from `a` by repeating every entry at least once.
It is defined by the "stay or move" recursion on `a'` (each entry of `a'` is either another copy
of the current entry of `a`, or the first copy of the next one), which is decidable
(`extB`), and equivalent to the paper's index description `1 = t₁ < … < t_{n+1}` (see
`ext_cons_iff`, the block form).
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- Boolean version of `Ext`: recursion on the extension. -/
def extB : List ℕ → List ℕ → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | x :: a, y :: w => (y == x) && (extB (x :: a) w || extB a w)

/-- `Ext a a'` : `a' ∈ E(a)` (Def. 3.6). -/
def Ext (a a' : List ℕ) : Prop := extB a a' = true

instance (a a' : List ℕ) : Decidable (Ext a a') := inferInstanceAs (Decidable (_ = true))

@[simp] theorem ext_nil_nil : Ext [] [] := rfl
@[simp] theorem ext_nil_cons (y : ℕ) (w : List ℕ) : ¬ Ext [] (y :: w) := by simp [Ext, extB]
@[simp] theorem ext_cons_nil (x : ℕ) (a : List ℕ) : ¬ Ext (x :: a) [] := by simp [Ext, extB]

theorem ext_cons_cons {x y : ℕ} {a w : List ℕ} :
    Ext (x :: a) (y :: w) ↔ y = x ∧ (Ext (x :: a) w ∨ Ext a w) := by
  simp [Ext, extB]

theorem ext_nil_iff {w : List ℕ} : Ext [] w ↔ w = [] := by
  cases w with
  | nil => simp
  | cons y w => simp

theorem ext_nil_right {a : List ℕ} : Ext a [] ↔ a = [] := by
  cases a with
  | nil => simp
  | cons x a => simp

/-- Block form: an extension of `x :: a` is `p+1` copies of `x` followed by an extension of `a`. -/
theorem ext_cons_iff {x : ℕ} {a w : List ℕ} :
    Ext (x :: a) w ↔ ∃ p u, w = List.replicate (p + 1) x ++ u ∧ Ext a u := by
  constructor
  · induction w with
    | nil => intro h; exact absurd h (ext_cons_nil x a)
    | cons y w' ih =>
      intro h
      obtain ⟨rfl, h | h⟩ := ext_cons_cons.mp h
      · obtain ⟨p, u, rfl, hu⟩ := ih h
        exact ⟨p + 1, u, by simp [List.replicate_succ], hu⟩
      · exact ⟨0, w', by simp, h⟩
  · rintro ⟨p, u, rfl, hu⟩
    induction p with
    | zero => exact ext_cons_cons.mpr ⟨rfl, Or.inr hu⟩
    | succ p ih =>
      rw [List.replicate_succ, List.cons_append]
      exact ext_cons_cons.mpr ⟨rfl, Or.inl ih⟩

theorem Ext.refl (a : List ℕ) : Ext a a := by
  induction a with
  | nil => exact ext_nil_nil
  | cons x a ih => exact ext_cons_cons.mpr ⟨rfl, Or.inr ih⟩

theorem Ext.trans {a b c : List ℕ} (h1 : Ext a b) (h2 : Ext b c) : Ext a c := by
  induction c generalizing a b with
  | nil => rw [ext_nil_right] at h2 ⊢; subst h2; exact ext_nil_right.mp h1
  | cons z c' ih =>
    cases b with
    | nil => exact absurd h2 (ext_nil_cons z c')
    | cons y b' =>
      obtain ⟨rfl, h2 | h2⟩ := ext_cons_cons.mp h2
      · cases a with
        | nil => exact absurd h1 (ext_nil_cons _ _)
        | cons x a' =>
          obtain ⟨rfl, _⟩ := ext_cons_cons.mp h1
          exact ext_cons_cons.mpr ⟨rfl, Or.inl (ih h1 h2)⟩
      · cases a with
        | nil => exact absurd h1 (ext_nil_cons _ _)
        | cons x a' =>
          obtain ⟨rfl, h1' | h1'⟩ := ext_cons_cons.mp h1
          · exact ext_cons_cons.mpr ⟨rfl, Or.inl (ih h1' h2)⟩
          · exact ext_cons_cons.mpr ⟨rfl, Or.inr (ih h1' h2)⟩

/-- **Lemma 3.18** (concatenation of extensions). -/
theorem Ext.append {a b c d : List ℕ} (h1 : Ext a b) (h2 : Ext c d) : Ext (a ++ c) (b ++ d) := by
  induction a generalizing b with
  | nil => rw [ext_nil_iff] at h1; subst h1; exact h2
  | cons x a ih =>
    obtain ⟨p, u, rfl, hu⟩ := ext_cons_iff.mp h1
    exact ext_cons_iff.mpr ⟨p, u ++ d, by simp [List.append_assoc], ih hu⟩

theorem ext_replicate {x p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    Ext (List.replicate p x) (List.replicate q x) := by
  induction p generalizing q with
  | zero => omega
  | succ p ih =>
    rw [List.replicate_succ]
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [List.replicate_succ]
    by_cases hp0 : p = 0
    · subst hp0
      simp only [List.replicate_zero]
      exact ext_cons_iff.mpr ⟨q', [], by simp [List.replicate_succ], ext_nil_nil⟩
    · exact ext_cons_iff.mpr ⟨0, List.replicate q' x, by simp, ih (by omega) (by omega)⟩

theorem Ext.mem {a w : List ℕ} (h : Ext a w) {x : ℕ} : x ∈ w ↔ x ∈ a := by
  induction w generalizing a with
  | nil => rw [ext_nil_right] at h; subst h; simp
  | cons y w ih =>
    cases a with
    | nil => exact absurd h (ext_nil_cons _ _)
    | cons x0 a =>
      obtain ⟨rfl, h | h⟩ := ext_cons_cons.mp h
      · have := ih h; simp at *; tauto
      · have := ih h; simp at *; tauto

/-- **Lemma 3.6**: `a* ∈ E(a) → τ(a*) = τ(a)`. -/
theorem Ext.reach {a w : List ℕ} (h : Ext a w) : Reach w a := by
  induction w generalizing a with
  | nil => rw [ext_nil_right] at h; subst h; exact Relation.ReflTransGen.refl
  | cons y w ih =>
    cases a with
    | nil => exact absurd h (ext_nil_cons _ _)
    | cons x a =>
      obtain ⟨rfl, h | h⟩ := ext_cons_cons.mp h
      · have := (ih h).append_left [y]
        exact this.tail (Red.dup [] y a)
      · exact (ih h).append_left [y]

theorem Ext.typical {a w : List ℕ} (h : Ext a w) : typical w = typical a :=
  typical_reach h.reach

/-! ### Uniform stretching -/

/-- Repeat every entry `k` times. -/
def stretch (k : ℕ) (a : List ℕ) : List ℕ := a.flatMap (fun x => List.replicate k x)

@[simp] theorem stretch_nil (k : ℕ) : stretch k [] = [] := rfl
@[simp] theorem stretch_cons (k x : ℕ) (a : List ℕ) :
    stretch k (x :: a) = List.replicate k x ++ stretch k a := by simp [stretch]
theorem stretch_append (k : ℕ) (a b : List ℕ) : stretch k (a ++ b) = stretch k a ++ stretch k b := by
  simp [stretch]
theorem stretch_replicate (k n x : ℕ) : stretch k (List.replicate n x) = List.replicate (k * n) x := by
  induction n with
  | zero => rw [List.replicate_zero, stretch_nil]; simp
  | succ n ih =>
    rw [List.replicate_succ, stretch_cons, ih, ← List.replicate_add]
    congr 1; ring

/-- Stretching a common base far enough gives an extension of any other extension of it. -/
theorem ext_stretch_of {a a' a₂ : List ℕ} {k : ℕ} (h1 : Ext a a') (h2 : Ext a a₂)
    (hk : a₂.length ≤ k) : Ext a₂ (stretch k a') := by
  induction a generalizing a' a₂ with
  | nil =>
    rw [ext_nil_iff] at h1 h2; subst h1; subst h2; exact ext_nil_nil
  | cons x a ih =>
    obtain ⟨q, u', rfl, hu'⟩ := ext_cons_iff.mp h1
    obtain ⟨p, u₂, rfl, hu₂⟩ := ext_cons_iff.mp h2
    simp only [List.length_append, List.length_replicate] at hk
    rw [stretch_append, stretch_replicate]
    exact Ext.append (ext_replicate (by omega) (by nlinarith)) (ih hu' hu₂ (by omega))

/-! ### Lifting along an extension -/

/-- If `w` extends `u` and `v` is related to `u` entrywise, then `v` has an extension related to
`w` entrywise (repeat the entries of `v` as those of `u` are repeated). -/
theorem ext_lift {R : ℕ → ℕ → Prop} {u w v : List ℕ} (h : Ext u w) (hR : List.Forall₂ R v u) :
    ∃ x, Ext v x ∧ List.Forall₂ R x w := by
  induction w generalizing u v with
  | nil =>
    rw [ext_nil_right] at h; subst h
    obtain rfl := List.forall₂_nil_right_iff.mp hR
    exact ⟨[], ext_nil_nil, List.Forall₂.nil⟩
  | cons y w ih =>
    cases u with
    | nil => exact absurd h (ext_nil_cons _ _)
    | cons x0 u' =>
      obtain ⟨rfl, h | h⟩ := ext_cons_cons.mp h
      · obtain ⟨v0, v', hv0, hv', rfl⟩ := List.forall₂_cons_right_iff.mp hR
        obtain ⟨x1, hx1, hx1R⟩ := ih h hR
        exact ⟨v0 :: x1, ext_cons_cons.mpr ⟨rfl, Or.inl hx1⟩, List.Forall₂.cons hv0 hx1R⟩
      · obtain ⟨v0, v', hv0, hv', rfl⟩ := List.forall₂_cons_right_iff.mp hR
        obtain ⟨x1, hx1, hx1R⟩ := ih h hv'
        exact ⟨v0 :: x1, ext_cons_cons.mpr ⟨rfl, Or.inr hx1⟩, List.Forall₂.cons hv0 hx1R⟩

end Lax117284Proofs.Treewidth.Seq
