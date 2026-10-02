import Lax117284Proofs.Treewidth.Seq.RingSum
import Lax117284Proofs.Treewidth.Seq.Concat

/-!
# Lists of integer sequences and Lemma 3.21

A *list* `[a] = (a⁽¹⁾,…,a⁽ⁿ⁾)` is a `List (List ℕ)`.  All notions of the paper's list of
definitions before Lemma 3.21 are defined here, and the seven items of Lemma 3.21 are proved.
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- The maximum entry of a list of sequences (`max([a]) = max_i max(a⁽ⁱ⁾)`). -/
def maxL (A : List (List ℕ)) : ℕ := A.flatten.foldr max 0

/-- Same length *in the strong sense*: same number of sequences and `l(a⁽ⁱ⁾) = l(b⁽ⁱ⁾)`. -/
def SameShape (A B : List (List ℕ)) : Prop :=
  List.Forall₂ (fun a b => a.length = b.length) A B

/-- `[a] ≤ [b]` (strong sense): `a⁽ⁱ⁾ ≤ b⁽ⁱ⁾` for each `i`. -/
def LeL (A B : List (List ℕ)) : Prop := List.Forall₂ LeSeq A B

/-- `[a] + [b]`. -/
def addL (A B : List (List ℕ)) : List (List ℕ) := List.zipWith zadd A B

/-- The typical list `τ[a]`. -/
def typicalL (A : List (List ℕ)) : List (List ℕ) := A.map typical

/-- `[b] ∈ E[a]`: each `b⁽ⁱ⁾ ∈ E(a⁽ⁱ⁾)`. -/
def ExtL (A B : List (List ℕ)) : Prop := List.Forall₂ Ext A B

/-- `[c] ∈ [a] ⊕ [b]`: each `c⁽ⁱ⁾ ∈ a⁽ⁱ⁾ ⊕ b⁽ⁱ⁾` (the lists have the same length). -/
def RingSumL : List (List ℕ) → List (List ℕ) → List (List ℕ) → Prop
  | [], [], [] => True
  | a :: A, b :: B, c :: C => RingSum a b c ∧ RingSumL A B C
  | _, _, _ => False

/-- `[a] ≺ [b]`: there are `[a*] ∈ E[a]`, `[b*] ∈ E[b]` with `[a*] ≤ [b*]`. -/
def DomL (A B : List (List ℕ)) : Prop := ∃ A' B', ExtL A A' ∧ ExtL B B' ∧ LeL A' B'

/-- `[a] ≡ [b]`. -/
def DomEquivL (A B : List (List ℕ)) : Prop := DomL A B ∧ DomL B A

/-! ### Componentwise description -/

theorem domL_iff_forall₂ : ∀ {A B : List (List ℕ)}, DomL A B ↔ List.Forall₂ Dom A B := by
  intro A
  induction A with
  | nil =>
    intro B
    constructor
    · rintro ⟨A', B', h1, h2, h3⟩
      obtain rfl := List.forall₂_nil_left_iff.mp h1
      obtain rfl := List.forall₂_nil_left_iff.mp h3
      obtain rfl := List.forall₂_nil_right_iff.mp h2
      exact List.Forall₂.nil
    · intro h
      obtain rfl := List.forall₂_nil_left_iff.mp h
      exact ⟨[], [], List.Forall₂.nil, List.Forall₂.nil, List.Forall₂.nil⟩
  | cons a A ih =>
    intro B
    constructor
    · rintro ⟨A', B', h1, h2, h3⟩
      obtain ⟨a', A'', h1a, h1b, rfl⟩ := List.forall₂_cons_left_iff.mp h1
      obtain ⟨b', B'', h3a, h3b, rfl⟩ := List.forall₂_cons_left_iff.mp h3
      obtain ⟨b, B0, h2a, h2b, rfl⟩ := List.forall₂_cons_right_iff.mp h2
      exact List.Forall₂.cons ⟨a', b', h1a, h2a, h3a⟩ (ih.mp ⟨A'', B'', h1b, h2b, h3b⟩)
    · intro h
      obtain ⟨b, B0, hab, hAB, rfl⟩ := List.forall₂_cons_left_iff.mp h
      obtain ⟨a', b', h1, h2, h3⟩ := hab
      obtain ⟨A'', B'', h4, h5, h6⟩ := ih.mpr hAB
      exact ⟨a' :: A'', b' :: B'', List.Forall₂.cons h1 h4, List.Forall₂.cons h2 h5,
        List.Forall₂.cons h3 h6⟩

theorem forall₂_trans_of {α : Type _} {R : α → α → Prop} (h : ∀ a b c, R a b → R b c → R a c) :
    ∀ {A B C : List α}, List.Forall₂ R A B → List.Forall₂ R B C → List.Forall₂ R A C := by
  intro A B C h1 h2
  induction h1 generalizing C with
  | nil => exact h2
  | cons hab _ ih =>
    obtain ⟨c, C', hbc, h2', rfl⟩ := List.forall₂_cons_left_iff.mp h2
    exact List.Forall₂.cons (h _ _ _ hab hbc) (ih h2')

/-! ### Lemma 3.21 -/

/-- **Lemma 3.21 (1)**: `≺` is transitive for lists. -/
theorem DomL.trans {A B C : List (List ℕ)} (h1 : DomL A B) (h2 : DomL B C) : DomL A C :=
  domL_iff_forall₂.mpr (forall₂_trans_of (R := Dom) (fun _ _ _ => Dom.trans)
    (domL_iff_forall₂.mp h1) (domL_iff_forall₂.mp h2))

theorem DomEquivL.trans {A B C : List (List ℕ)} (h1 : DomEquivL A B) (h2 : DomEquivL B C) :
    DomEquivL A C := ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

end Lax117284Proofs.Treewidth.Seq
