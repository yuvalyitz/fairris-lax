import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Logic.Relation
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Typical sequences (Bodlaender–Kloks, §3): the two reduction operations

Integer sequences are `List ℕ`.  This file defines the two operations of Def. 3.5
(remove a consecutive repetition; the *typical operation*) as one reduction step `Red`,
its reflexive-transitive closure `Reach`, the normal forms `NF` ("no operation possible
any more"), and an index view (`Dup`, `Win`) of the same notions.
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- `z` lies in the closed interval spanned by `x` and `y`. -/
def InR (z x y : ℕ) : Prop := min x y ≤ z ∧ z ≤ max x y

instance (z x y : ℕ) : Decidable (InR z x y) := inferInstanceAs (Decidable (_ ∧ _))

theorem InR.left (x y : ℕ) : InR x x y := by unfold InR; omega
theorem InR.right (x y : ℕ) : InR y x y := by unfold InR; omega
theorem InR.symm {z x y : ℕ} (h : InR z x y) : InR z y x := by unfold InR at *; omega
theorem InR.self_iff {z x : ℕ} : InR z x x ↔ z = x := by unfold InR; omega

/-- One reduction step (Def. 3.5): removal of a consecutive repetition, or the typical
operation (delete a non-empty interior all of whose entries lie between its two neighbours). -/
inductive Red : List ℕ → List ℕ → Prop
  | dup (l : List ℕ) (x : ℕ) (r : List ℕ) : Red (l ++ x :: x :: r) (l ++ x :: r)
  | typ (l : List ℕ) (x : ℕ) (m : List ℕ) (y : ℕ) (r : List ℕ) :
      m ≠ [] → (∀ z ∈ m, InR z x y) →
      Red (l ++ x :: (m ++ y :: r)) (l ++ x :: y :: r)

/-- Iterating the operations. -/
abbrev Reach : List ℕ → List ℕ → Prop := Relation.ReflTransGen Red

/-- No operation is possible any more. -/
def NF (a : List ℕ) : Prop := ∀ b, ¬ Red a b

theorem Red.length_lt {a b : List ℕ} (h : Red a b) : b.length < a.length := by
  cases h with
  | dup l x r => simp
  | typ l x m y r hm _ =>
    have : 0 < m.length := List.length_pos_iff.mpr hm
    simp; omega

theorem Red.sublist {a b : List ℕ} (h : Red a b) : b.Sublist a := by
  cases h with
  | dup l x r =>
    apply List.Sublist.append_left
    exact (List.Sublist.cons _ (List.Sublist.refl _))
  | typ l x m y r hm _ =>
    apply List.Sublist.append_left
    exact List.Sublist.cons_cons x (List.sublist_append_right _ _)

theorem Reach.sublist {a b : List ℕ} (h : Reach a b) : b.Sublist a := by
  induction h with
  | refl => exact List.Sublist.refl _
  | tail _ hr ih => exact hr.sublist.trans ih

theorem Red.append_left (c : List ℕ) {a b : List ℕ} (h : Red a b) : Red (c ++ a) (c ++ b) := by
  cases h with
  | dup l x r => simpa [List.append_assoc] using Red.dup (c ++ l) x r
  | typ l x m y r hm hz => simpa [List.append_assoc] using Red.typ (c ++ l) x m y r hm hz

theorem Red.append_right (c : List ℕ) {a b : List ℕ} (h : Red a b) : Red (a ++ c) (b ++ c) := by
  cases h with
  | dup l x r => simpa [List.append_assoc] using Red.dup l x (r ++ c)
  | typ l x m y r hm hz => simpa [List.append_assoc] using Red.typ l x m y (r ++ c) hm hz

theorem Reach.append_left (c : List ℕ) {a b : List ℕ} (h : Reach a b) : Reach (c ++ a) (c ++ b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hr ih => exact ih.tail (hr.append_left c)

theorem Reach.append_right (c : List ℕ) {a b : List ℕ} (h : Reach a b) : Reach (a ++ c) (b ++ c) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hr ih => exact ih.tail (hr.append_right c)

theorem NF.append_left {a b : List ℕ} (h : NF (a ++ b)) : NF a := fun _ hc =>
  h _ (hc.append_right b)

theorem NF.append_right {a b : List ℕ} (h : NF (a ++ b)) : NF b := fun _ hc =>
  h _ (hc.append_left a)

theorem nf_nil : NF [] := by
  intro b h; have := h.length_lt; simp at this

theorem exists_nf_aux : ∀ (n : ℕ) (a : List ℕ), a.length = n → ∃ b, Reach a b ∧ NF b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a hn
    by_cases h : NF a
    · exact ⟨a, Relation.ReflTransGen.refl, h⟩
    · simp only [NF, not_forall, not_not] at h
      obtain ⟨c, hc⟩ := h
      obtain ⟨b, hb, hnf⟩ := ih c.length (hn ▸ hc.length_lt) c rfl
      exact ⟨b, Relation.ReflTransGen.head hc hb, hnf⟩

/-- Some normal form is reachable (the operations terminate). -/
theorem exists_nf (a : List ℕ) : ∃ b, Reach a b ∧ NF b := exists_nf_aux _ a rfl

/-! ### The index view -/

/-- Entry `i` of `a` (`0` outside the range). -/
def ent (a : List ℕ) (i : ℕ) : ℕ := a.getD i 0

theorem ent_append_left {a : List ℕ} (b : List ℕ) {i : ℕ} (h : i < a.length) :
    ent (a ++ b) i = ent a i := by
  unfold ent; exact List.getD_append _ _ _ _ h

theorem ent_append_right (a : List ℕ) {b : List ℕ} {i : ℕ} (h : a.length ≤ i) :
    ent (a ++ b) i = ent b (i - a.length) := by
  unfold ent; exact List.getD_append_right _ _ _ _ h

@[simp] theorem ent_cons_zero (x : ℕ) (a : List ℕ) : ent (x :: a) 0 = x := by
  simp [ent]

@[simp] theorem ent_cons_succ (x : ℕ) (a : List ℕ) (i : ℕ) : ent (x :: a) (i + 1) = ent a i := by
  simp [ent]

theorem ent_eq_getElem {a : List ℕ} {i : ℕ} (h : i < a.length) : ent a i = a[i] := by
  unfold ent; exact List.getD_eq_getElem _ _ h

theorem ent_mem {a : List ℕ} {i : ℕ} (h : i < a.length) : ent a i ∈ a := by
  rw [ent_eq_getElem h]; exact List.getElem_mem h

/-- A repetition at index `k`. -/
def Dup (a : List ℕ) (k : ℕ) : Prop := k + 1 < a.length ∧ ent a k = ent a (k + 1)

/-- A window: indices `k < j` with `j - k ≥ 2` whose interior lies between the endpoints. -/
def Win (a : List ℕ) (k j : ℕ) : Prop :=
  k + 2 ≤ j ∧ j < a.length ∧ ∀ m, k < m → m < j → InR (ent a m) (ent a k) (ent a j)

theorem red_witness {a b : List ℕ} (h : Red a b) : (∃ k, Dup a k) ∨ ∃ k j, Win a k j := by
  cases h with
  | dup l x r =>
    left; refine ⟨l.length, ?_, ?_⟩
    · simp
    · rw [ent_append_right _ (Nat.le_refl _), ent_append_right _ (by omega)]; simp
  | typ l x m y r hm hz =>
    right
    have hmpos : 0 < m.length := List.length_pos_iff.mpr hm
    refine ⟨l.length, l.length + m.length + 1, by omega, by simp; omega, ?_⟩
    intro q hq1 hq2
    have e1 : ent (l ++ x :: (m ++ y :: r)) l.length = x := by
      rw [ent_append_right _ (Nat.le_refl _)]; simp
    have e2 : ent (l ++ x :: (m ++ y :: r)) (l.length + m.length + 1) = y := by
      rw [ent_append_right _ (by omega)]
      have : l.length + m.length + 1 - l.length = m.length + 1 := by omega
      rw [this]; simp only [ent_cons_succ]
      rw [ent_append_right _ (Nat.le_refl _)]; simp
    have e3 : ent (l ++ x :: (m ++ y :: r)) q = ent m (q - l.length - 1) := by
      rw [ent_append_right _ (by omega)]
      have : q - l.length = (q - l.length - 1) + 1 := by omega
      rw [this]; simp only [ent_cons_succ]
      rw [ent_append_left _ (by omega)]; simp
    rw [e1, e2, e3]
    exact hz _ (ent_mem (by omega))

theorem exists_red_of_dup {a : List ℕ} {k : ℕ} (h : Dup a k) : ∃ b, Red a b := by
  obtain ⟨hk, he⟩ := h
  rw [ent_eq_getElem (by omega), ent_eq_getElem hk] at he
  have h1 : a = a.take k ++ a[k] :: a[k] :: a.drop (k + 1 + 1) := by
    calc a = a.take k ++ a.drop k := (List.take_append_drop k a).symm
      _ = _ := by
        rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega), ← he]
  have := Red.dup (a.take k) a[k] (a.drop (k + 1 + 1))
  rw [← h1] at this
  exact ⟨_, this⟩

theorem exists_red_of_win {a : List ℕ} {k j : ℕ} (h : Win a k j) : ∃ b, Red a b := by
  obtain ⟨hkj, hj, hz⟩ := h
  set m := (a.drop (k + 1)).take (j - k - 1) with hm
  have hmlen : m.length = j - k - 1 := by
    rw [hm]; simp; omega
  have hdrop : a.drop (k + 1) = m ++ a.drop j := by
    rw [hm]
    conv_lhs => rw [← List.take_append_drop (j - k - 1) (a.drop (k + 1))]
    rw [List.drop_drop]
    congr 2; omega
  have h1 : a = a.take k ++ ent a k :: (m ++ ent a j :: a.drop (j + 1)) := by
    calc a = a.take k ++ a.drop k := (List.take_append_drop k a).symm
      _ = _ := by
        rw [List.drop_eq_getElem_cons (by omega), hdrop, ent_eq_getElem (by omega),
          List.drop_eq_getElem_cons hj, ent_eq_getElem hj]
  have hm0 : m ≠ [] := by
    intro h0; rw [h0] at hmlen; simp at hmlen; omega
  have hmz : ∀ z ∈ m, InR z (ent a k) (ent a j) := by
    intro z hz'
    rw [hm] at hz'
    obtain ⟨u, hu, rfl⟩ := List.mem_iff_getElem.mp hz'
    have hu' : u < j - k - 1 := by simp at hu; omega
    simp only [List.getElem_take, List.getElem_drop]
    rw [← ent_eq_getElem (by omega)]
    exact hz _ (by omega) (by omega)
  have := Red.typ (a.take k) (ent a k) m (ent a j) (a.drop (j + 1)) hm0 hmz
  rw [← h1] at this
  exact ⟨_, this⟩

theorem nf_iff {a : List ℕ} : NF a ↔ (∀ k, ¬ Dup a k) ∧ ∀ k j, ¬ Win a k j := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k j hw => ?_⟩
    · obtain ⟨b, hb⟩ := exists_red_of_dup hk; exact h b hb
    · obtain ⟨b, hb⟩ := exists_red_of_win hw; exact h b hb
  · rintro ⟨h1, h2⟩ b hb
    rcases red_witness hb with ⟨k, hk⟩ | ⟨k, j, hw⟩
    · exact h1 k hk
    · exact h2 k j hw

end Lax117284Proofs.Treewidth.Seq
