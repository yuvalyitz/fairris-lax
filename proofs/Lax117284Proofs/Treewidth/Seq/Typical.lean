import Lax117284Proofs.Treewidth.Seq.Stack
import Mathlib.Data.List.Induction

/-!
# Lemma 3.2: the typical sequence is uniquely defined

`typical` (a stack algorithm, see `Stack.lean`) computes the *unique* normal form reachable
from `a` by the two operations of Def. 3.5.  The paper's proof is one line ("removability of
`a_k` is preserved by every operation"), which is not literally true at the level of
positions (two equal entries may each be removable, and removing one makes the other
irremovable); the real content is the confluence of the rewriting system, which is proved
here through the invariance of the stack algorithm under every single step
(`typical_red`, using the absorption lemma `push_push`).
-/

namespace Lax117284Proofs.Treewidth.Seq

theorem foldl_push_nf {t : List ℕ} (ht : NF t) (a : List ℕ) : NF (a.foldl push t) := by
  induction a generalizing t with
  | nil => exact ht
  | cons y a ih => exact ih (nf_push ht y)

theorem nf_typical (a : List ℕ) : NF (typical a) := foldl_push_nf nf_nil a

theorem typical_append (a b : List ℕ) : typical (a ++ b) = b.foldl push (typical a) := by
  simp [typical, List.foldl_append]

theorem typical_concat (a : List ℕ) (y : ℕ) : typical (a ++ [y]) = push (typical a) y := by
  simp [typical_append]

@[simp] theorem typical_nil : typical [] = [] := rfl

theorem typical_of_nf {a : List ℕ} (h : NF a) : typical a = a := by
  induction a using List.reverseRecOn with
  | nil => rfl
  | append_singleton a y ih =>
    rw [typical_concat, ih h.append_left]
    exact push_of_nf h

theorem typical_typical (a : List ℕ) : typical (typical a) = typical a :=
  typical_of_nf (nf_typical a)

theorem typical_ne_nil {a : List ℕ} (h : a ≠ []) : typical a ≠ [] := by
  induction a using List.reverseRecOn with
  | nil => exact absurd rfl h
  | append_singleton b y _ => rw [typical_concat]; exact push_ne_nil _ _

theorem typical_singleton (x : ℕ) : typical [x] = [x] := by
  have := typical_concat [] x
  simp only [List.nil_append, typical_nil, push_nil] at this
  exact this

/-- The stack invariant of one step: the algorithm cannot tell `a` from `b`. -/
theorem typical_red {a b : List ℕ} (h : Red a b) : typical a = typical b := by
  cases h with
  | dup l x r =>
    have e1 : l ++ x :: x :: r = (l ++ [x]) ++ (x :: r) := by simp
    have e2 : l ++ x :: r = (l ++ [x]) ++ r := by simp
    have hnf : NF (typical (l ++ [x])) := nf_typical _
    have hlast : (typical (l ++ [x])).getLast? = some x := by
      rw [typical_concat]; exact push_getLast _ _
    rw [e1, e2, typical_append (l ++ [x]) (x :: r), typical_append (l ++ [x]) r]
    simp only [List.foldl_cons]
    rw [push_of_last hnf hlast]
  | typ l x m y r hm hz =>
    have e1 : l ++ x :: (m ++ y :: r) = (l ++ [x]) ++ ((m ++ [y]) ++ r) := by simp
    have e2 : l ++ x :: y :: r = (l ++ [x]) ++ (y :: r) := by simp
    have hnf : NF (typical (l ++ [x])) := nf_typical _
    have hlast : (typical (l ++ [x])).getLast? = some x := by
      rw [typical_concat]; exact push_getLast _ _
    rw [e1, e2, typical_append (l ++ [x]) ((m ++ [y]) ++ r), typical_append (l ++ [x]) (y :: r),
      List.foldl_append, foldl_push_window hnf hlast m hz]
    simp

theorem typical_reach {a b : List ℕ} (h : Reach a b) : typical a = typical b := by
  induction h with
  | refl => rfl
  | tail _ hr ih => rw [ih, typical_red hr]

/-- The typical sequence is reachable from `a` by the two operations. -/
theorem reach_typical (a : List ℕ) : Reach a (typical a) := by
  obtain ⟨b, hab, hb⟩ := exists_nf a
  have : typical a = b := by rw [typical_reach hab, typical_of_nf hb]
  rw [this]; exact hab

/-- **Lemma 3.2**: any normal form reachable from `a` is `typical a`. -/
theorem eq_typical_of_reach_nf {a b : List ℕ} (h : Reach a b) (hb : NF b) : b = typical a := by
  rw [typical_reach h, typical_of_nf hb]

/-- **Lemma 3.2** (unique existence): there is exactly one normal form reachable from `a`. -/
theorem existsUnique_nf (a : List ℕ) : ∃! b, Reach a b ∧ NF b :=
  ⟨typical a, ⟨reach_typical a, nf_typical a⟩, fun b hb => eq_typical_of_reach_nf hb.1 hb.2⟩

/-- The relational characterisation: `τ a = b` iff `b` is the result of iterating the
operations until none is possible. -/
theorem typical_eq_iff {a b : List ℕ} : typical a = b ↔ Reach a b ∧ NF b := by
  constructor
  · rintro rfl; exact ⟨reach_typical a, nf_typical a⟩
  · rintro ⟨h1, h2⟩; exact (eq_typical_of_reach_nf h1 h2).symm

/-- `a` is a typical sequence: `a = τ a`. -/
def IsTypical (a : List ℕ) : Prop := typical a = a

theorem isTypical_iff_nf {a : List ℕ} : IsTypical a ↔ NF a :=
  ⟨fun h => h ▸ nf_typical a, typical_of_nf⟩

/-- Def. 3.5's two descriptions of "typical sequence" agree: `a` is the typical sequence of
some sequence iff `a = τ a`. -/
theorem isTypical_iff_exists {a : List ℕ} : IsTypical a ↔ ∃ c, typical c = a :=
  ⟨fun h => ⟨a, h⟩, fun ⟨c, hc⟩ => hc ▸ typical_typical c⟩

instance (a : List ℕ) : Decidable (NF a) :=
  decidable_of_iff (typical a = a) isTypical_iff_nf

instance (a : List ℕ) : Decidable (IsTypical a) :=
  inferInstanceAs (Decidable (typical a = a))

theorem typical_congr_red {a b : List ℕ} (h : Red a b) : typical a = typical b := typical_red h

end Lax117284Proofs.Treewidth.Seq
