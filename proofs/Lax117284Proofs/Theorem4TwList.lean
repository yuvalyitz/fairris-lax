import Lax117284Proofs.Theorem4TwBags

/-!
Reading the entries of a bag after an insertion or a removal, and counting the entries below a
number as a sum: the facts the loops that build and scan a bag need.
-/

namespace Lax117284Proofs.TwList

open Lax117284Proofs.TwBags

/-- **The number of entries below `v` is a sum over the positions.** -/
lemma pos_eq_sum (l : List ℕ) (v : ℕ) :
    pos l v = ∑ t ∈ Finset.range l.length, if l[t]! < v then 1 else 0 := by
  induction l with
  | nil => simp [pos]
  | cons a l ih =>
    have h1 : pos (a :: l) v = pos l v + (if a < v then 1 else 0) := by
      unfold pos
      rw [List.countP_cons]
      by_cases h : a < v <;> simp [h]
    rw [h1, ih, List.length_cons, Finset.sum_range_succ']
    simp [Nat.add_comm]

/-- The entries of a list with `v` inserted at `p`. -/
lemma getElem!_insertIdx (l : List ℕ) (p v : ℕ) (hp : p ≤ l.length) (t : ℕ) :
    (l.insertIdx p v)[t]! = if t < p then l[t]! else if t = p then v else l[t - 1]! := by
  induction l generalizing p t with
  | nil =>
    have : p = 0 := by simpa using hp
    subst this
    rcases t with _ | t
    · simp
    · simp
  | cons a l ih =>
    rcases p with _ | p
    · rcases t with _ | t <;> simp
    · rcases t with _ | t
      · simp
      · rw [List.insertIdx_succ_cons]
        simp only [List.getElem!_cons_succ]
        rw [ih p (by simpa using hp) t]
        by_cases h1 : t < p
        · simp [h1, show t + 1 < p + 1 by omega]
        · by_cases h2 : t = p
          · simp [h2]
          · have h3 : ¬ t + 1 < p + 1 := by omega
            have h4 : ¬ t + 1 = p + 1 := by omega
            simp [h1, h2, h3, h4]
            rcases t with _ | t
            · omega
            · simp

/-- The entries of a list with the entry at `p` removed. -/
lemma getElem!_eraseIdx (l : List ℕ) (p t : ℕ) :
    (l.eraseIdx p)[t]! = if t < p then l[t]! else l[t + 1]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eraseIdx]
  split_ifs <;> rfl

end Lax117284Proofs.TwList
