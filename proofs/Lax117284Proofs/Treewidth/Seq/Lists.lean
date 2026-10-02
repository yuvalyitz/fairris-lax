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

theorem forall₂_refl_of {α : Type _} {R : α → α → Prop} (h : ∀ a, R a a) :
    ∀ A : List α, List.Forall₂ R A A := by
  intro A; induction A with
  | nil => exact List.Forall₂.nil
  | cons a A ih => exact List.Forall₂.cons (h a) ih

/-! ### Lemma 3.21 -/

theorem DomL.refl (A : List (List ℕ)) : DomL A A :=
  domL_iff_forall₂.mpr (forall₂_refl_of Dom.refl A)

/-- **Lemma 3.21 (1)**: `≺` is transitive for lists. -/
theorem DomL.trans {A B C : List (List ℕ)} (h1 : DomL A B) (h2 : DomL B C) : DomL A C :=
  domL_iff_forall₂.mpr (forall₂_trans_of (R := Dom) (fun _ _ _ => Dom.trans)
    (domL_iff_forall₂.mp h1) (domL_iff_forall₂.mp h2))

theorem DomEquivL.refl (A : List (List ℕ)) : DomEquivL A A := ⟨DomL.refl A, DomL.refl A⟩
theorem DomEquivL.symm {A B : List (List ℕ)} (h : DomEquivL A B) : DomEquivL B A := ⟨h.2, h.1⟩
theorem DomEquivL.trans {A B C : List (List ℕ)} (h1 : DomEquivL A B) (h2 : DomEquivL B C) :
    DomEquivL A C := ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

/-- **Lemma 3.21 (1)**: `≡` is an equivalence relation for lists. -/
theorem domEquivL_equivalence : Equivalence DomEquivL :=
  ⟨DomEquivL.refl, DomEquivL.symm, DomEquivL.trans⟩

/-- **Lemma 3.21 (2)**: `[b] ∈ E[a] → τ[b] = τ[a]`. -/
theorem ExtL.typicalL_eq {A B : List (List ℕ)} (h : ExtL A B) : typicalL B = typicalL A := by
  unfold typicalL
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [hab.typical, ih]

/-- **Lemma 3.21 (3)**: `[a] ≺ [b] ↔ τ[a] ≺ τ[b]`. -/
theorem domL_typicalL_iff {A B : List (List ℕ)} : DomL A B ↔ DomL (typicalL A) (typicalL B) := by
  rw [domL_iff_forall₂, domL_iff_forall₂]
  unfold typicalL
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  constructor
  · intro h
    induction h with
    | nil => exact List.Forall₂.nil
    | cons hab _ ih => exact List.Forall₂.cons (dom_typical_iff.mp hab) ih
  · intro h
    induction h with
    | nil => exact List.Forall₂.nil
    | cons hab _ ih => exact List.Forall₂.cons (dom_typical_iff.mpr hab) ih

/-- **Lemma 3.21 (4)**: `τ[a] ≡ [a]`; moreover there are `[a'], [a''] ∈ E(τ[a])` with
`[a'] ≤ [a] ≤ [a'']`. -/
theorem lemma_3_21_4 (A : List (List ℕ)) :
    DomEquivL (typicalL A) A ∧
      ∃ A' A'', ExtL (typicalL A) A' ∧ ExtL (typicalL A) A'' ∧ LeL A' A ∧ LeL A A'' := by
  induction A with
  | nil => exact ⟨DomEquivL.refl [], [], [], List.Forall₂.nil, List.Forall₂.nil, List.Forall₂.nil,
      List.Forall₂.nil⟩
  | cons a A ih =>
    obtain ⟨⟨h1, h2⟩, A', A'', hA', hA'', hl1, hl2⟩ := ih
    obtain ⟨n1, hn1, hl1'⟩ := below_typical a
    obtain ⟨n2, hn2, hl2'⟩ := above_typical a
    refine ⟨⟨?_, ?_⟩, n1 :: A', n2 :: A'', ?_, ?_, ?_, ?_⟩
    · obtain ⟨X, Y, hX, hY, hXY⟩ := h1
      exact ⟨n1 :: X, a :: Y, List.Forall₂.cons hn1 hX, List.Forall₂.cons (Ext.refl a) hY,
        List.Forall₂.cons hl1' hXY⟩
    · obtain ⟨X, Y, hX, hY, hXY⟩ := h2
      exact ⟨a :: X, n2 :: Y, List.Forall₂.cons (Ext.refl a) hX, List.Forall₂.cons hn2 hY,
        List.Forall₂.cons hl2' hXY⟩
    · exact List.Forall₂.cons hn1 hA'
    · exact List.Forall₂.cons hn2 hA''
    · exact List.Forall₂.cons hl1' hl1
    · exact List.Forall₂.cons hl2' hl2

/-- **Lemma 3.21 (5)**: (Lemma 3.12 for lists). -/
theorem RingSumL.of_ext : ∀ {A B C A' B' : List (List ℕ)}, RingSumL A B C → ExtL A A' → ExtL B B' →
    ∃ C', ExtL C C' ∧ RingSumL A' B' C' := by
  intro A
  induction A with
  | nil =>
    intro B C A' B' h hA hB
    cases B with
    | nil =>
      cases C with
      | nil =>
        obtain rfl := List.forall₂_nil_left_iff.mp hA
        obtain rfl := List.forall₂_nil_left_iff.mp hB
        exact ⟨[], List.Forall₂.nil, trivial⟩
      | cons c C => simp [RingSumL] at h
    | cons b B => cases C <;> simp [RingSumL] at h
  | cons a A ih =>
    intro B C A' B' h hA hB
    cases B with
    | nil => cases C <;> simp [RingSumL] at h
    | cons b B =>
      cases C with
      | nil => simp [RingSumL] at h
      | cons c C =>
        obtain ⟨hc, hrest⟩ := h
        obtain ⟨a', A'', ha, hA', rfl⟩ := List.forall₂_cons_left_iff.mp hA
        obtain ⟨b', B'', hb, hB', rfl⟩ := List.forall₂_cons_left_iff.mp hB
        obtain ⟨c', hc1, hc2⟩ := RingSum.of_ext hc ha hb
        obtain ⟨C', hC1, hC2⟩ := ih hrest hA' hB'
        exact ⟨c' :: C', List.Forall₂.cons hc1 hC1, hc2, hC2⟩

/-- **Lemma 3.21 (6)**: (Lemma 3.13 for lists). -/
theorem RingSumL.dom_of_dom : ∀ {A B A₀ B₀ : List (List ℕ)}, SameShape A B →
    DomL A₀ A → DomL B₀ B → ∃ Y₀, RingSumL A₀ B₀ Y₀ ∧ DomL Y₀ (addL A B) := by
  intro A
  induction A with
  | nil =>
    intro B A₀ B₀ hs hA hB
    obtain rfl := List.forall₂_nil_left_iff.mp hs
    have h1 := domL_iff_forall₂.mp hA
    have h2 := domL_iff_forall₂.mp hB
    obtain rfl := List.forall₂_nil_right_iff.mp h1
    obtain rfl := List.forall₂_nil_right_iff.mp h2
    exact ⟨[], trivial, DomL.refl _⟩
  | cons a A ih =>
    intro B A₀ B₀ hs hA hB
    obtain ⟨b, B1, hab, hs', rfl⟩ := List.forall₂_cons_left_iff.mp hs
    have h1 := domL_iff_forall₂.mp hA
    have h2 := domL_iff_forall₂.mp hB
    obtain ⟨a₀, A₀', hd1, hA', rfl⟩ := List.forall₂_cons_right_iff.mp h1
    obtain ⟨b₀, B₀', hd2, hB', rfl⟩ := List.forall₂_cons_right_iff.mp h2
    obtain ⟨y₀, hy, hd⟩ := RingSum.dom_of_dom hab hd1 hd2
    obtain ⟨Y₀, hY, hdY⟩ := ih hs' (domL_iff_forall₂.mpr hA') (domL_iff_forall₂.mpr hB')
    refine ⟨y₀ :: Y₀, ⟨hy, hY⟩, ?_⟩
    have := domL_iff_forall₂.mp hdY
    exact domL_iff_forall₂.mpr (List.Forall₂.cons hd this)

/-- **Lemma 3.21 (7)**: (Lemma 3.14 for lists). -/
theorem RingSumL.dom_typicalL : ∀ {A B C : List (List ℕ)}, RingSumL A B C →
    ∃ C', RingSumL (typicalL A) (typicalL B) C' ∧ DomL C' C := by
  intro A
  induction A with
  | nil =>
    intro B C h
    cases B with
    | nil =>
      cases C with
      | nil => exact ⟨[], trivial, DomL.refl _⟩
      | cons c C => simp [RingSumL] at h
    | cons b B => cases C <;> simp [RingSumL] at h
  | cons a A ih =>
    intro B C h
    cases B with
    | nil => cases C <;> simp [RingSumL] at h
    | cons b B =>
      cases C with
      | nil => simp [RingSumL] at h
      | cons c C =>
        obtain ⟨hc, hrest⟩ := h
        obtain ⟨c', hc', hd⟩ := RingSum.dom_typical hc
        obtain ⟨C', hC', hdC⟩ := ih hrest
        refine ⟨c' :: C', ⟨hc', hC'⟩, ?_⟩
        exact domL_iff_forall₂.mpr (List.Forall₂.cons hd (domL_iff_forall₂.mp hdC))

end Lax117284Proofs.Treewidth.Seq
