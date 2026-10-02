import Lax117284Proofs.Treewidth.Seq.Dom
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Order.Interval.Finset.Nat

/-!
# Concatenation and splits (Lemmas 3.17–3.20, Def. 3.10)

Concatenation `∘ab` of the paper is `a ++ b`.
-/

namespace Lax117284Proofs.Treewidth.Seq

theorem typical_append_typical_left (a b : List ℕ) :
    typical (a ++ b) = typical (typical a ++ b) :=
  typical_reach ((reach_typical a).append_right b)

theorem typical_append_typical_right (a b : List ℕ) :
    typical (a ++ b) = typical (a ++ typical b) :=
  typical_reach ((reach_typical b).append_left a)

/-- **Lemma 3.19**: `a' ≺ a` and `b' ≺ b` ⟹ `∘a'b' ≺ ∘ab`. -/
theorem Dom.append {a b a' b' : List ℕ} (h1 : Dom a' a) (h2 : Dom b' b) :
    Dom (a' ++ b') (a ++ b) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h1
  obtain ⟨u, v, hu, hv, huv⟩ := h2
  exact ⟨x ++ u, y ++ v, hx.append hu, hy.append hv, hxy.append huv⟩

/-! ### Splits (Def. 3.10) -/

/-- A split of the first type: `δ₁ = (a₁..a_f)`, `δ₂ = (a_f..a_n)` (`1 ≤ f ≤ n`). -/
def Split1 (a d1 d2 : List ℕ) : Prop :=
  ∃ f, 1 ≤ f ∧ f ≤ a.length ∧ d1 = a.take f ∧ d2 = a.drop (f - 1)

/-- A split of the second type: `δ₁ = (a₁..a_f)`, `δ₂ = (a_{f+1}..a_n)` (`1 ≤ f < n`, so that
`δ₂` is a sequence). -/
def Split2 (a d1 d2 : List ℕ) : Prop :=
  ∃ f, 1 ≤ f ∧ f < a.length ∧ d1 = a.take f ∧ d2 = a.drop f

/-- The splits of the first type, as a finite set. -/
def splits1 (a : List ℕ) : Finset (List ℕ × List ℕ) :=
  (Finset.Icc 1 a.length).image (fun f => (a.take f, a.drop (f - 1)))

/-- The splits of the second type, as a finite set. -/
def splits2 (a : List ℕ) : Finset (List ℕ × List ℕ) :=
  (Finset.Ico 1 a.length).image (fun f => (a.take f, a.drop f))

/-- All splits of `a` (both types). -/
def splits (a : List ℕ) : Finset (List ℕ × List ℕ) := splits1 a ∪ splits2 a

theorem mem_splits1 {a d1 d2 : List ℕ} : (d1, d2) ∈ splits1 a ↔ Split1 a d1 d2 := by
  unfold splits1 Split1
  simp only [Finset.mem_image, Finset.mem_Icc, Prod.mk.injEq]
  constructor
  · rintro ⟨f, ⟨h1, h2⟩, rfl, rfl⟩; exact ⟨f, h1, h2, rfl, rfl⟩
  · rintro ⟨f, h1, h2, rfl, rfl⟩; exact ⟨f, ⟨h1, h2⟩, rfl, rfl⟩

theorem mem_splits2 {a d1 d2 : List ℕ} : (d1, d2) ∈ splits2 a ↔ Split2 a d1 d2 := by
  unfold splits2 Split2
  simp only [Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro ⟨f, ⟨h1, h2⟩, rfl, rfl⟩; exact ⟨f, h1, h2, rfl, rfl⟩
  · rintro ⟨f, h1, h2, rfl, rfl⟩; exact ⟨f, ⟨h1, h2⟩, rfl, rfl⟩

theorem mem_splits {a d1 d2 : List ℕ} :
    (d1, d2) ∈ splits a ↔ Split1 a d1 d2 ∨ Split2 a d1 d2 := by
  unfold splits; rw [Finset.mem_union, mem_splits1, mem_splits2]

/-! ### Lemma 3.20 -/

/-- Cutting an extension after the block of the first `f` entries. -/
theorem ext_cut : ∀ {t a : List ℕ} (f : ℕ), Ext t a →
    ∃ a1 a2, a = a1 ++ a2 ∧ Ext (t.take f) a1 ∧ Ext (t.drop f) a2 := by
  intro t
  induction t with
  | nil =>
    intro a f h
    rw [ext_nil_iff] at h; subst h
    exact ⟨[], [], rfl, by simp, by simp⟩
  | cons x t ih =>
    intro a f h
    cases f with
    | zero => exact ⟨[], a, rfl, by simp, by simpa using h⟩
    | succ f =>
      obtain ⟨p, a0, rfl, ha0⟩ := ext_cons_iff.mp h
      obtain ⟨a1, a2, rfl, h1, h2⟩ := ih f ha0
      refine ⟨List.replicate (p + 1) x ++ a1, a2, by simp, ?_, by simpa using h2⟩
      rw [List.take_succ_cons]
      exact ext_cons_iff.mpr ⟨p, a1, rfl, h1⟩

/-- The pieces of a split of a normal form are normal forms. -/
theorem nf_of_split {t d1 d2 : List ℕ} (ht : NF t) (h : Split1 t d1 d2 ∨ Split2 t d1 d2) :
    NF d1 ∧ NF d2 := by
  rcases h with ⟨f, -, -, rfl, rfl⟩ | ⟨f, -, -, rfl, rfl⟩
  · refine ⟨?_, ?_⟩
    · rw [← List.take_append_drop f t] at ht; exact ht.append_left
    · rw [← List.take_append_drop (f - 1) t] at ht; exact ht.append_right
  · refine ⟨?_, ?_⟩
    · rw [← List.take_append_drop f t] at ht; exact ht.append_left
    · rw [← List.take_append_drop f t] at ht; exact ht.append_right

end Lax117284Proofs.Treewidth.Seq
