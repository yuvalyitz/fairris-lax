import Lax117284Proofs.Treewidth.Seq.Ext
import Lax117284Proofs.Treewidth.Seq.Rel

/-!
# The dominance preorder `≺` (Defs 3.7; Lemmas 3.7, 3.9, 3.10; Cor. 3.8, 3.11)

`Dom a b` is `a ≺ b`: there are extensions `a* ∈ E(a)`, `b* ∈ E(b)` of the same length with
`a* ≤ b*`.  `DomEquiv a b` is `a ≡ b`.
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- `a ≺ b` (Def. 3.7). -/
def Dom (a b : List ℕ) : Prop :=
  ∃ a' b', Ext a a' ∧ Ext b b' ∧ LeSeq a' b'

/-- `a ≡ b` (Def. 3.7): `a ≺ b` and `b ≺ a`. -/
def DomEquiv (a b : List ℕ) : Prop := Dom a b ∧ Dom b a

theorem Dom.refl (a : List ℕ) : Dom a a := ⟨a, a, Ext.refl a, Ext.refl a, LeSeq.refl a⟩

/-- **Lemma 3.7**: `≺` is transitive. -/
theorem Dom.trans {a b c : List ℕ} (h1 : Dom a b) (h2 : Dom b c) : Dom a c := by
  obtain ⟨a1, b1, ha1, hb1, hab⟩ := h1
  obtain ⟨b2, c2, hb2, hc2, hbc⟩ := h2
  set k := b1.length + b2.length with hk
  have e1 : Ext b1 (stretch k b) := ext_stretch_of (Ext.refl b) hb1 (by omega)
  have e2 : Ext b2 (stretch k b) := ext_stretch_of (Ext.refl b) hb2 (by omega)
  obtain ⟨x, hx, hxw⟩ := ext_lift e1 hab
  obtain ⟨y, hy, hyw⟩ := ext_lift e2 (R := fun p q => q ≤ p) hbc.flip'
  exact ⟨x, y, ha1.trans hx, hc2.trans hy, LeSeq.trans hxw (LeSeq.flip hyw)⟩

/-- Preorder instance, for `calc`/`gcongr`-style use. -/
instance : Trans Dom Dom Dom := ⟨Dom.trans⟩

/-! ### Lemma 3.9 / 3.10 -/

/-- `n` has an extension lying entrywise below `a` (in particular of the length of `a`). -/
def Below (a n : List ℕ) : Prop := ∃ n', Ext n n' ∧ LeSeq n' a

/-- `n` has an extension lying entrywise above `a` (in particular of the length of `a`). -/
def Above (a n : List ℕ) : Prop := ∃ n', Ext n n' ∧ LeSeq a n'

theorem Below.refl (a : List ℕ) : Below a a := ⟨a, Ext.refl a, LeSeq.refl a⟩
theorem Above.refl (a : List ℕ) : Above a a := ⟨a, Ext.refl a, LeSeq.refl a⟩

theorem Below.trans {a b c : List ℕ} (h1 : Below a b) (h2 : Below b c) : Below a c := by
  obtain ⟨b', hb', hba⟩ := h1
  obtain ⟨c', hc', hcb⟩ := h2
  obtain ⟨x, hx, hxb⟩ := ext_lift hb' hcb
  exact ⟨x, hc'.trans hx, LeSeq.trans hxb hba⟩

theorem Above.trans {a b c : List ℕ} (h1 : Above a b) (h2 : Above b c) : Above a c := by
  obtain ⟨b', hb', hab⟩ := h1
  obtain ⟨c', hc', hbc⟩ := h2
  obtain ⟨x, hx, hxb⟩ := ext_lift (R := fun p q => q ≤ p) hb' hbc.flip'
  exact ⟨x, hc'.trans hx, LeSeq.trans hab (LeSeq.flip hxb)⟩

theorem Below.append {a1 a2 b1 b2 : List ℕ} (h1 : Below a1 b1) (h2 : Below a2 b2) :
    Below (a1 ++ a2) (b1 ++ b2) := by
  obtain ⟨x, hx, hxa⟩ := h1
  obtain ⟨y, hy, hya⟩ := h2
  exact ⟨x ++ y, hx.append hy, hxa.append hya⟩

theorem Above.append {a1 a2 b1 b2 : List ℕ} (h1 : Above a1 b1) (h2 : Above a2 b2) :
    Above (a1 ++ a2) (b1 ++ b2) := by
  obtain ⟨x, hx, hxa⟩ := h1
  obtain ⟨y, hy, hya⟩ := h2
  exact ⟨x ++ y, hx.append hy, hxa.append hya⟩

theorem Below.dom {a n : List ℕ} (h : Below a n) : Dom n a :=
  let ⟨n', hn', hle⟩ := h
  ⟨n', a, hn', Ext.refl a, hle⟩

theorem Above.dom {a n : List ℕ} (h : Above a n) : Dom a n :=
  let ⟨n', hn', hle⟩ := h
  ⟨a, n', Ext.refl a, hn', hle⟩

/-- The interior of a window lies between its ends: the window is `≡` to its two ends, from
below. -/
theorem below_window {x y : ℕ} {m : List ℕ} (hz : ∀ z ∈ m, InR z x y) :
    Below (x :: (m ++ [y])) [x, y] := by
  by_cases hxy : x ≤ y
  · refine ⟨List.replicate (m.length + 1) x ++ [y], ?_, ?_⟩
    · exact ext_cons_iff.mpr ⟨m.length, [y], by simp, Ext.refl [y]⟩
    · rw [List.replicate_succ, List.cons_append]
      refine List.Forall₂.cons (Nat.le_refl x) (LeSeq.append ?_ (LeSeq.refl [y]))
      exact leSeq_replicate_left fun z hzm => by have := hz z hzm; unfold InR at this; omega
  · refine ⟨x :: List.replicate (m.length + 1) y, ?_, ?_⟩
    · exact ext_cons_iff.mpr ⟨0, List.replicate (m.length + 1) y, by simp,
        by simpa using ext_replicate (x := y) (p := 1) (q := m.length + 1) (by omega) (by omega)⟩
    · rw [List.replicate_succ']
      refine List.Forall₂.cons (Nat.le_refl x) (LeSeq.append ?_ (LeSeq.refl [y]))
      exact leSeq_replicate_left fun z hzm => by have := hz z hzm; unfold InR at this; omega

theorem above_window {x y : ℕ} {m : List ℕ} (hz : ∀ z ∈ m, InR z x y) :
    Above (x :: (m ++ [y])) [x, y] := by
  by_cases hxy : x ≤ y
  · refine ⟨x :: List.replicate (m.length + 1) y, ?_, ?_⟩
    · exact ext_cons_iff.mpr ⟨0, List.replicate (m.length + 1) y, by simp,
        by simpa using ext_replicate (x := y) (p := 1) (q := m.length + 1) (by omega) (by omega)⟩
    · rw [List.replicate_succ']
      refine List.Forall₂.cons (Nat.le_refl x) (LeSeq.append ?_ (LeSeq.refl [y]))
      exact leSeq_replicate_right fun z hzm => by have := hz z hzm; unfold InR at this; omega
  · refine ⟨List.replicate (m.length + 1) x ++ [y], ?_, ?_⟩
    · exact ext_cons_iff.mpr ⟨m.length, [y], by simp, Ext.refl [y]⟩
    · rw [List.replicate_succ, List.cons_append]
      refine List.Forall₂.cons (Nat.le_refl x) (LeSeq.append ?_ (LeSeq.refl [y]))
      exact leSeq_replicate_right fun z hzm => by have := hz z hzm; unfold InR at this; omega

/-- **Lemma 3.9** (one operation): the result of an operation has an extension below `a` and
one above `a`, of the length of `a`; hence `a' ≡ a`. -/
theorem below_of_red {a b : List ℕ} (h : Red a b) : Below a b := by
  cases h with
  | dup l x r =>
    refine ⟨l ++ x :: x :: r, ?_, LeSeq.refl _⟩
    have := Ext.append (Ext.refl l) (Ext.append (ext_replicate (x := x) (p := 1) (q := 2) (by omega)
      (by omega)) (Ext.refl r))
    simpa using this
  | typ l x m y r hm hz =>
    have := Below.append (Below.refl l) (Below.append (below_window hz) (Below.refl r))
    simpa using this

theorem above_of_red {a b : List ℕ} (h : Red a b) : Above a b := by
  cases h with
  | dup l x r =>
    refine ⟨l ++ x :: x :: r, ?_, LeSeq.refl _⟩
    have := Ext.append (Ext.refl l) (Ext.append (ext_replicate (x := x) (p := 1) (q := 2) (by omega)
      (by omega)) (Ext.refl r))
    simpa using this
  | typ l x m y r hm hz =>
    have := Above.append (Above.refl l) (Above.append (above_window hz) (Above.refl r))
    simpa using this

theorem below_of_reach {a b : List ℕ} (h : Reach a b) : Below a b := by
  induction h with
  | refl => exact Below.refl _
  | tail _ hr ih => exact ih.trans (below_of_red hr)

theorem above_of_reach {a b : List ℕ} (h : Reach a b) : Above a b := by
  induction h with
  | refl => exact Above.refl _
  | tail _ hr ih => exact ih.trans (above_of_red hr)

/-- **Lemma 3.10**: `τ(a)` has an extension of the length of `a` below `a` and one above `a`. -/
theorem below_typical (a : List ℕ) : Below a (typical a) := below_of_reach (reach_typical a)
theorem above_typical (a : List ℕ) : Above a (typical a) := above_of_reach (reach_typical a)

/-- **Lemma 3.10**: `τ(a) ≡ a`. -/
theorem domEquiv_typical (a : List ℕ) : DomEquiv (typical a) a :=
  ⟨(below_typical a).dom, (above_typical a).dom⟩

/-- **Corollary 3.11**: `a ≺ b ↔ τ(a) ≺ τ(b)`. -/
theorem dom_typical_iff {a b : List ℕ} : Dom a b ↔ Dom (typical a) (typical b) := by
  constructor
  · intro h
    exact ((domEquiv_typical a).1.trans h).trans (domEquiv_typical b).2
  · intro h
    exact ((domEquiv_typical a).2.trans h).trans (domEquiv_typical b).1

/-- Extensions are equivalent (Lemma 3.9 for repetitions). -/
theorem domEquiv_of_ext {a a' : List ℕ} (h : Ext a a') : DomEquiv a' a :=
  ⟨⟨a', a', Ext.refl a', h, LeSeq.refl _⟩, ⟨a', a', h, Ext.refl a', LeSeq.refl _⟩⟩

/-! ### `≺` is decidable: the alignment recursion

`domB (x :: a) (y :: b)` walks a monotone lattice path: the current entries must satisfy
`x ≤ y`, and then either both sequences end, or one of them advances, or both do. -/

/-- Decision procedure for `a ≺ b` (lattice-path recursion). -/
def domB : List ℕ → List ℕ → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | x :: a, y :: b =>
    decide (x ≤ y) &&
      ((a.isEmpty && b.isEmpty) || domB a (y :: b) || domB (x :: a) b || domB a b)
termination_by l1 l2 => l1.length + l2.length

theorem domB_cons_cons (x y : ℕ) (a b : List ℕ) :
    domB (x :: a) (y :: b) = (decide (x ≤ y) &&
      ((a.isEmpty && b.isEmpty) || domB a (y :: b) || domB (x :: a) b || domB a b)) := by
  rw [domB]

theorem domB_of_dom_aux : ∀ (a1 : List ℕ) (a b b1 : List ℕ),
    Ext a a1 → Ext b b1 → LeSeq a1 b1 → domB a b = true := by
  intro a1
  induction a1 with
  | nil =>
    intro a b b1 h1 h2 h3
    rw [ext_nil_right] at h1; subst h1
    have := LeSeq.length_eq h3
    have hb1 : b1 = [] := List.length_eq_zero_iff.mp (by simpa using this.symm)
    subst hb1
    rw [ext_nil_right] at h2; subst h2
    simp [domB]
  | cons x1 a1 ih =>
    intro a b b1 h1 h2 h3
    cases h3 with
    | cons hxy h3' =>
      rename_i y1 b1'
      cases a with
      | nil => exact absurd h1 (ext_nil_cons _ _)
      | cons x a0 =>
        cases b with
        | nil => exact absurd h2 (ext_nil_cons _ _)
        | cons y b0 =>
          obtain ⟨rfl, h1' | h1'⟩ := ext_cons_cons.mp h1 <;>
          obtain ⟨rfl, h2' | h2'⟩ := ext_cons_cons.mp h2
          · exact ih _ _ _ h1' h2' h3'
          · have := ih _ _ _ h1' h2' h3'
            rw [domB_cons_cons]; simp [hxy, this]
          · have := ih _ _ _ h1' h2' h3'
            rw [domB_cons_cons]; simp [hxy, this]
          · have := ih _ _ _ h1' h2' h3'
            rw [domB_cons_cons]; simp [hxy, this]

theorem dom_of_domB_aux : ∀ (n : ℕ) (a b : List ℕ), a.length + b.length = n →
    domB a b = true → Dom a b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn h
    cases a with
    | nil =>
      cases b with
      | nil => exact Dom.refl []
      | cons y b => simp [domB] at h
    | cons x a =>
      cases b with
      | nil => simp [domB] at h
      | cons y b =>
        rw [domB_cons_cons] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
        obtain ⟨hxy, h⟩ := h
        simp only [List.length_cons] at hn
        rcases h with ((h | h) | h) | h
        · simp only [Bool.and_eq_true, List.isEmpty_iff] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨[x], [y], Ext.refl _, Ext.refl _, List.Forall₂.cons hxy List.Forall₂.nil⟩
        · obtain ⟨a1, b1, ha1, hb1, hle⟩ := ih (a.length + (y :: b).length) (by simp at *; omega) a
            (y :: b) rfl h
          refine ⟨x :: a1, y :: b1, ext_cons_cons.mpr ⟨rfl, Or.inr ha1⟩,
            ext_cons_cons.mpr ⟨rfl, Or.inl hb1⟩, List.Forall₂.cons hxy hle⟩
        · obtain ⟨a1, b1, ha1, hb1, hle⟩ := ih ((x :: a).length + b.length) (by simp at *; omega)
            (x :: a) b rfl h
          refine ⟨x :: a1, y :: b1, ext_cons_cons.mpr ⟨rfl, Or.inl ha1⟩,
            ext_cons_cons.mpr ⟨rfl, Or.inr hb1⟩, List.Forall₂.cons hxy hle⟩
        · obtain ⟨a1, b1, ha1, hb1, hle⟩ := ih (a.length + b.length) (by omega) a b rfl h
          refine ⟨x :: a1, y :: b1, ext_cons_cons.mpr ⟨rfl, Or.inr ha1⟩,
            ext_cons_cons.mpr ⟨rfl, Or.inr hb1⟩, List.Forall₂.cons hxy hle⟩

/-- `a ≺ b` is decided by the lattice-path recursion `domB`. -/
theorem dom_iff_domB {a b : List ℕ} : Dom a b ↔ domB a b = true :=
  ⟨fun ⟨a1, b1, h1, h2, h3⟩ => domB_of_dom_aux a1 a b b1 h1 h2 h3,
   dom_of_domB_aux _ a b rfl⟩

instance : DecidableRel Dom := fun a b => decidable_of_iff _ dom_iff_domB.symm

instance : DecidableRel DomEquiv := fun a b => inferInstanceAs (Decidable (Dom a b ∧ Dom b a))

end Lax117284Proofs.Treewidth.Seq
