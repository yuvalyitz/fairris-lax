import Lax117284Proofs.Treewidth.Seq.RingSum
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union

/-!
# Lattice paths and the computable ring sum (Lemma 3.15, `ringTyp`)

`pathSums a b` is the finite set of sums along the monotone lattice paths
`(0,0) → (|a|-1,|b|-1)` with steps `(1,0)`, `(0,1)`, `(1,1)` (Althaus–Ziegler, P5).  Every
element of `a ⊕ b` can be shortened (removing repeated pairs) to a path sum without changing the
typical sequence: this is Lemma 3.15, and gives the computable `ringTyp`.
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- Sums along monotone lattice paths. -/
def pathSums : List ℕ → List ℕ → Finset (List ℕ)
  | [], _ => ∅
  | _ :: _, [] => ∅
  | x :: a, y :: b =>
    (if a = [] ∧ b = [] then {[x + y]} else ∅) ∪
      (pathSums a (y :: b) ∪ pathSums (x :: a) b ∪ pathSums a b).image (List.cons (x + y))
termination_by l1 l2 => l1.length + l2.length

theorem pathSums_cons_cons (x y : ℕ) (a b : List ℕ) :
    pathSums (x :: a) (y :: b) =
      (if a = [] ∧ b = [] then {[x + y]} else ∅) ∪
      (pathSums a (y :: b) ∪ pathSums (x :: a) b ∪ pathSums a b).image (List.cons (x + y)) := by
  rw [pathSums]

@[simp] theorem pathSums_nil_left (b : List ℕ) : pathSums [] b = ∅ := by
  rw [pathSums]

@[simp] theorem pathSums_nil_right (a : List ℕ) : pathSums a [] = ∅ := by
  cases a <;> simp [pathSums]

theorem mem_pathSums_cons_cons {x y : ℕ} {a b c : List ℕ} :
    c ∈ pathSums (x :: a) (y :: b) ↔
      (a = [] ∧ b = [] ∧ c = [x + y]) ∨
      ∃ p, (p ∈ pathSums a (y :: b) ∨ p ∈ pathSums (x :: a) b ∨ p ∈ pathSums a b) ∧
        c = (x + y) :: p := by
  rw [pathSums_cons_cons]
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨p, hp, rfl⟩)
    · split_ifs at h with hc
      · simp at h; exact Or.inl ⟨hc.1, hc.2, h⟩
      · simp at h
    · exact Or.inr ⟨p, by tauto, rfl⟩
  · rintro (⟨h1, h2, rfl⟩ | ⟨p, hp, rfl⟩)
    · left; rw [if_pos ⟨h1, h2⟩]; simp
    · right; exact ⟨p, by tauto, rfl⟩

/-- Every path sum is an element of `a ⊕ b` of length at most `|a| + |b| - 1`. -/
theorem pathSums_sound : ∀ (n : ℕ) (a b c : List ℕ), a.length + b.length = n →
    c ∈ pathSums a b → RingSum a b c ∧ c.length + 1 ≤ a.length + b.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c hn hc
    cases a with
    | nil => simp at hc
    | cons x a =>
      cases b with
      | nil => simp at hc
      | cons y b =>
        simp only [List.length_cons] at hn ⊢
        rcases mem_pathSums_cons_cons.mp hc with ⟨rfl, rfl, rfl⟩ | ⟨p, hp, rfl⟩
        · exact ⟨⟨[x], [y], Ext.refl _, Ext.refl _, rfl, rfl⟩, by simp⟩
        · rcases hp with hp | hp | hp
          · obtain ⟨⟨a', b', h1, h2, h3, rfl⟩, hl⟩ := ih (a.length + (y :: b).length)
              (by simp; omega) a (y :: b) p rfl hp
            refine ⟨⟨x :: a', y :: b', ext_cons_cons.mpr ⟨rfl, Or.inr h1⟩,
              ext_cons_cons.mpr ⟨rfl, Or.inl h2⟩, by simp [h3], by simp⟩, ?_⟩
            simp at hl ⊢; omega
          · obtain ⟨⟨a', b', h1, h2, h3, rfl⟩, hl⟩ := ih ((x :: a).length + b.length)
              (by simp; omega) (x :: a) b p rfl hp
            refine ⟨⟨x :: a', y :: b', ext_cons_cons.mpr ⟨rfl, Or.inl h1⟩,
              ext_cons_cons.mpr ⟨rfl, Or.inr h2⟩, by simp [h3], by simp⟩, ?_⟩
            simp at hl ⊢; omega
          · obtain ⟨⟨a', b', h1, h2, h3, rfl⟩, hl⟩ := ih (a.length + b.length)
              (by omega) a b p rfl hp
            refine ⟨⟨x :: a', y :: b', ext_cons_cons.mpr ⟨rfl, Or.inr h1⟩,
              ext_cons_cons.mpr ⟨rfl, Or.inr h2⟩, by simp [h3], by simp⟩, ?_⟩
            simp at hl ⊢; omega

theorem head_of_mem_pathSums {x y : ℕ} {a b c : List ℕ} (h : c ∈ pathSums (x :: a) (y :: b)) :
    ∃ p, c = (x + y) :: p := by
  rcases mem_pathSums_cons_cons.mp h with ⟨_, _, rfl⟩ | ⟨p, _, rfl⟩
  · exact ⟨[], rfl⟩
  · exact ⟨p, rfl⟩

/-- Every extension pair is, after removing repeated pairs, a lattice path. -/
theorem pathSums_complete : ∀ (a₁ : List ℕ) {a b b₁ : List ℕ}, Ext a a₁ → Ext b b₁ →
    a₁.length = b₁.length → a ≠ [] →
    ∃ c', c' ∈ pathSums a b ∧ Ext c' (zadd a₁ b₁) := by
  intro a₁
  induction a₁ with
  | nil =>
    intro a b b₁ h1 h2 h3 ha
    rw [ext_nil_right] at h1; exact absurd h1 ha
  | cons x1 a₁ ih =>
    intro a b b₁ h1 h2 h3 ha
    cases b₁ with
    | nil => simp at h3
    | cons y1 b₁ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h3
      cases a with
      | nil => exact absurd rfl ha
      | cons x a0 =>
        cases b with
        | nil => exact absurd h2 (by simp)
        | cons y b0 =>
          obtain ⟨rfl, h1'⟩ := ext_cons_cons.mp h1
          obtain ⟨rfl, h2'⟩ := ext_cons_cons.mp h2
          have hz : zadd (x1 :: a₁) (y1 :: b₁) = (x1 + y1) :: zadd a₁ b₁ := rfl
          rw [hz]
          rcases h1' with h1' | h1' <;> rcases h2' with h2' | h2'
          · -- stay, stay
            obtain ⟨c', hc', he⟩ := ih h1' h2' h3 (by simp)
            obtain ⟨p, rfl⟩ := head_of_mem_pathSums hc'
            exact ⟨_, hc', ext_cons_cons.mpr ⟨rfl, Or.inl he⟩⟩
          · -- stay in a, move in b
            obtain ⟨c', hc', he⟩ := ih h1' h2' h3 (by simp)
            exact ⟨(x1 + y1) :: c',
              mem_pathSums_cons_cons.mpr (Or.inr ⟨c', Or.inr (Or.inl hc'), rfl⟩),
              ext_cons_cons.mpr ⟨rfl, Or.inr he⟩⟩
          · -- move in a, stay in b
            have ha0 : a0 ≠ [] := by
              rintro rfl
              rw [ext_nil_iff] at h1'; subst h1'
              have : b₁ = [] := List.length_eq_zero_iff.mp (by simpa using h3.symm)
              subst this
              exact absurd h2' (by simp)
            obtain ⟨c', hc', he⟩ := ih h1' h2' h3 ha0
            exact ⟨(x1 + y1) :: c',
              mem_pathSums_cons_cons.mpr (Or.inr ⟨c', Or.inl hc', rfl⟩),
              ext_cons_cons.mpr ⟨rfl, Or.inr he⟩⟩
          · -- move in both
            by_cases ha0 : a0 = []
            · subst ha0
              rw [ext_nil_iff] at h1'; subst h1'
              have : b₁ = [] := List.length_eq_zero_iff.mp (by simpa using h3.symm)
              subst this
              rw [ext_nil_right] at h2'; subst h2'
              exact ⟨[x1 + y1], mem_pathSums_cons_cons.mpr (Or.inl ⟨rfl, rfl, rfl⟩), Ext.refl _⟩
            · obtain ⟨c', hc', he⟩ := ih h1' h2' h3 ha0
              exact ⟨(x1 + y1) :: c',
                mem_pathSums_cons_cons.mpr (Or.inr ⟨c', Or.inr (Or.inr hc'), rfl⟩),
                ext_cons_cons.mpr ⟨rfl, Or.inr he⟩⟩

/-- **Lemma 3.15**: an element `c ∈ a ⊕ b` has a representative `c' ∈ a ⊕ b` with the same
typical sequence and `l(c') ≤ l(a) + l(b) - 1` (in fact a lattice-path sum). -/
theorem RingSum.short {a b c : List ℕ} (h : RingSum a b c) (ha : a ≠ []) :
    ∃ c', c' ∈ pathSums a b ∧ RingSum a b c' ∧ typical c' = typical c ∧
      c'.length + 1 ≤ a.length + b.length ∧ Ext c' c := by
  obtain ⟨a', b', h1, h2, h3, rfl⟩ := h
  obtain ⟨c', hc', he⟩ := pathSums_complete a' h1 h2 h3 ha
  obtain ⟨hr, hl⟩ := pathSums_sound _ a b c' rfl hc'
  exact ⟨c', hc', hr, (he.typical).symm, hl, he⟩

/-- The typical sequences of the ring sum, as a computable finite set. -/
def ringTyp (a b : List ℕ) : Finset (List ℕ) := (pathSums a b).image typical

theorem mem_ringTyp {a b c : List ℕ} (ha : a ≠ []) :
    c ∈ ringTyp a b ↔ ∃ c', RingSum a b c' ∧ typical c' = c := by
  unfold ringTyp
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨c', hc', rfl⟩
    exact ⟨c', (pathSums_sound _ a b c' rfl hc').1, rfl⟩
  · rintro ⟨c', hc', rfl⟩
    obtain ⟨c'', hc'', -, hty, -⟩ := RingSum.short hc' ha
    exact ⟨c'', hc'', hty⟩

/-- ... and conversely every element of `ringTyp (τ a) (τ b)` is dominated by an element of
`ringTyp a b`. -/
theorem ringTyp_cover_right {a b c' : List ℕ} (ha : a ≠ []) (hc : c' ∈ ringTyp (typical a) (typical b)) :
    ∃ c ∈ ringTyp a b, Dom c c' := by
  obtain ⟨c0, ⟨x, y, hx, hy, hl, rfl⟩, rfl⟩ := (mem_ringTyp (typical_ne_nil ha)).mp hc
  have h1 : Dom a x := ((above_typical a).dom).trans (domEquiv_of_ext hx).2
  have h2 : Dom b y := ((above_typical b).dom).trans (domEquiv_of_ext hy).2
  obtain ⟨y₀, hy₀, hd⟩ := RingSum.dom_of_dom hl h1 h2
  exact ⟨typical y₀, (mem_ringTyp ha).mpr ⟨y₀, hy₀, rfl⟩, dom_typical_iff.mp hd⟩

end Lax117284Proofs.Treewidth.Seq
