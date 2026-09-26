import Lax117284.BoundedSat
import Mathlib.Data.List.Count
import Mathlib.Data.Fintype.Card

/-!
The occurrence slots of a [2,3]-bounded 3-SAT formula, numbered: the two slots of every
clause of two literals first, then the three slots of every clause of three literals. A
construction reads a formula through these numbers, and the number of a slot determines the
position it names.
-/

namespace Lax117284Proofs.Theorem7Slots

open Lax117284.BoundedSat

variable (φ : Formula)

/-- The number of a position. -/
def slotNum : φ.Occ → ℕ
  | Sum.inl q => 2 * (q.1 : ℕ) + (q.2 : ℕ)
  | Sum.inr q => 2 * φ.twoClauses + 3 * (q.1 : ℕ) + (q.2 : ℕ)

theorem slotNum_lt (o : φ.Occ) : slotNum φ o < slots φ := by
  rcases o with ⟨c, α⟩ | ⟨c, α⟩
  · have h1 := c.isLt
    have h2 := α.isLt
    have h3 : 2 * ((c : ℕ) + 1) ≤ 2 * φ.twoClauses := Nat.mul_le_mul_left _ h1
    simp only [slotNum, slots]
    omega
  · have h1 := c.isLt
    have h2 := α.isLt
    have h3 : 3 * ((c : ℕ) + 1) ≤ 3 * φ.threeClauses := Nat.mul_le_mul_left _ h1
    simp only [slotNum, slots]
    omega

theorem slotNum_inl_lt (q : Fin φ.twoClauses × Fin 2) :
    slotNum φ (Sum.inl q) < 2 * φ.twoClauses := by
  have h1 := q.1.isLt
  have h2 := q.2.isLt
  have h3 : 2 * ((q.1 : ℕ) + 1) ≤ 2 * φ.twoClauses := Nat.mul_le_mul_left _ h1
  simp only [slotNum]
  omega

theorem slotNum_inr_ge (q : Fin φ.threeClauses × Fin 3) :
    2 * φ.twoClauses ≤ slotNum φ (Sum.inr q) := by
  simp only [slotNum]
  omega

theorem slotNum_injective : Function.Injective (slotNum φ) := by
  rintro (⟨c, α⟩ | ⟨c, α⟩) (⟨c', α'⟩ | ⟨c', α'⟩) h
  · have h1 := α.isLt
    have h2 := α'.isLt
    simp only [slotNum] at h
    have hc : (c : ℕ) = (c' : ℕ) := by omega
    have ha : (α : ℕ) = (α' : ℕ) := by omega
    exact congrArg Sum.inl (Prod.ext (Fin.ext hc) (Fin.ext ha))
  · exact absurd (h ▸ slotNum_inl_lt φ (c, α)) (by
      have := slotNum_inr_ge φ (c', α'); omega)
  · exact absurd (h ▸ slotNum_inr_ge φ (c, α)) (by
      have := slotNum_inl_lt φ (c', α'); omega)
  · have h1 := α.isLt
    have h2 := α'.isLt
    simp only [slotNum] at h
    have hc : (c : ℕ) = (c' : ℕ) := by omega
    have ha : (α : ℕ) = (α' : ℕ) := by omega
    exact congrArg Sum.inr (Prod.ext (Fin.ext hc) (Fin.ext ha))

theorem exists_slotNum {n : ℕ} (hn : n < slots φ) : ∃ o : φ.Occ, slotNum φ o = n := by
  simp only [slots] at hn
  by_cases h : n < 2 * φ.twoClauses
  · have hc : n / 2 < φ.twoClauses := by omega
    have ha : n % 2 < 2 := by omega
    exact ⟨Sum.inl (⟨n / 2, hc⟩, ⟨n % 2, ha⟩), by simp only [slotNum]; omega⟩
  · have hc : (n - 2 * φ.twoClauses) / 3 < φ.threeClauses := by omega
    have ha : (n - 2 * φ.twoClauses) % 3 < 3 := by omega
    exact ⟨Sum.inr (⟨(n - 2 * φ.twoClauses) / 3, hc⟩, ⟨(n - 2 * φ.twoClauses) % 3, ha⟩), by
      simp only [slotNum]; omega⟩

/-- The literal a numbered slot carries is the literal of the position it names. -/
theorem litOfSlot_slotNum (o : φ.Occ) :
    litOfSlot φ (slotNum φ o) = (((φ.litAt o).1 : ℕ), (φ.litAt o).2) := by
  rcases o with ⟨c, α⟩ | ⟨c, α⟩
  · have h1 := α.isLt
    have key : ∀ (h : (2 * (c : ℕ) + (α : ℕ)) / 2 < φ.twoClauses)
        (h' : (2 * (c : ℕ) + (α : ℕ)) % 2 < 2),
        φ.aLit ⟨(2 * (c : ℕ) + (α : ℕ)) / 2, h⟩ ⟨(2 * (c : ℕ) + (α : ℕ)) % 2, h'⟩
          = φ.aLit c α := by
      intro h h'
      congr 1
      · exact Fin.ext (show (2 * (c : ℕ) + (α : ℕ)) / 2 = (c : ℕ) by omega)
      · exact Fin.ext (show (2 * (c : ℕ) + (α : ℕ)) % 2 = (α : ℕ) by omega)
    show litOfSlot φ (2 * (c : ℕ) + (α : ℕ)) = _
    simp only [litOfSlot]
    rw [if_pos (show 2 * (c : ℕ) + (α : ℕ) < 2 * φ.twoClauses from by
      have := c.isLt; omega), dif_pos (show (2 * (c : ℕ) + (α : ℕ)) / 2
      < φ.twoClauses from by have := c.isLt; omega)]
    simp only [key]
    rfl
  · have h1 := α.isLt
    have key : ∀ (h : (2 * φ.twoClauses + 3 * (c : ℕ) + (α : ℕ) - 2 * φ.twoClauses) / 3
          < φ.threeClauses)
        (h' : (2 * φ.twoClauses + 3 * (c : ℕ) + (α : ℕ) - 2 * φ.twoClauses) % 3 < 3),
        φ.bLit ⟨(2 * φ.twoClauses + 3 * (c : ℕ) + (α : ℕ) - 2 * φ.twoClauses) / 3, h⟩
            ⟨(2 * φ.twoClauses + 3 * (c : ℕ) + (α : ℕ) - 2 * φ.twoClauses) % 3, h'⟩
          = φ.bLit c α := by
      intro h h'
      congr 1
      · exact Fin.ext (show (2 * φ.twoClauses + 3 * (c : ℕ) + (α : ℕ)
          - 2 * φ.twoClauses) / 3 = (c : ℕ) by omega)
      · exact Fin.ext (show (2 * φ.twoClauses + 3 * (c : ℕ) + (α : ℕ)
          - 2 * φ.twoClauses) % 3 = (α : ℕ) by omega)
    show litOfSlot φ (2 * φ.twoClauses + 3 * (c : ℕ) + (α : ℕ)) = _
    simp only [litOfSlot]
    rw [if_neg (by omega), dif_pos (show (2 * φ.twoClauses + 3 * (c : ℕ) + (α : ℕ)
      - 2 * φ.twoClauses) / 3 < φ.threeClauses from by have := c.isLt; omega)]
    simp only [key]
    rfl

/-- The literal is determined by its numbered form. -/
theorem litAt_eq_of_litOfSlot {o o' : φ.Occ}
    (h : litOfSlot φ (slotNum φ o) = litOfSlot φ (slotNum φ o')) :
    φ.litAt o = φ.litAt o' := by
  rw [litOfSlot_slotNum, litOfSlot_slotNum] at h
  refine Prod.ext (Fin.ext ?_) ?_
  · exact congrArg (fun p : ℕ × Bool => p.1) h
  · exact congrArg (fun p : ℕ × Bool => p.2) h

/-! ### The rank of a slot

The rank of a slot is the number of earlier slots carrying the same literal. Since a
literal occupies at most two positions, a rank is `0` or `1`, and two positions of the same
literal have different ranks — which is Tovey's bound in the form the construction uses. -/

theorem countP_range_lt {p : ℕ → Bool} {a b : ℕ} (hab : a < b) (hp : p a = true) :
    (List.range a).countP p < (List.range b).countP p := by
  have h1 : (List.range (a + 1)).countP p = (List.range a).countP p + 1 := by
    rw [List.range_succ, List.countP_append]
    simp [hp]
  have h2 : (List.range (a + 1)).countP p ≤ (List.range b).countP p :=
    List.Sublist.countP_le (List.range_sublist.2 (by omega))
  omega

theorem slotRank_lt {a b : ℕ} (hab : a < b) (hl : litOfSlot φ a = litOfSlot φ b) :
    slotRank φ a < slotRank φ b := by
  simp only [slotRank, hl]
  exact countP_range_lt hab (by simp [hl])

theorem length_le_one {α : Type*} {l : List α} (hn : l.Nodup)
    (h : ∀ a ∈ l, ∀ b ∈ l, a = b) : l.length ≤ 1 := by
  match l with
  | [] => simp
  | [_] => simp
  | a :: b :: t =>
    exfalso
    have hab : a = b := h a (by simp) b (by simp)
    exact (List.nodup_cons.1 hn).1 (by simp [hab])

/-- The positions carrying a given literal. -/
noncomputable def sameLit (l : Fin φ.vars × Bool) : Finset φ.Occ := by
  classical
  exact Finset.univ.filter fun o => φ.litAt o = l

theorem card_sameLit_le (l : Fin φ.vars × Bool) : (sameLit φ l).card ≤ 2 :=
  φ.occ_le_two l

theorem mem_sameLit {o : φ.Occ} {l : Fin φ.vars × Bool} (h : φ.litAt o = l) :
    o ∈ sameLit φ l := by
  classical
  simp only [sameLit, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h

/-- **Tovey's bound, in the numbered form**: a slot has at most one earlier slot carrying
its literal. -/
theorem slotRank_le_one (o : φ.Occ) : slotRank φ (slotNum φ o) ≤ 1 := by
  classical
  rw [slotRank, List.countP_eq_length_filter]
  refine length_le_one ((List.nodup_range).filter _) ?_
  intro a ha b hb
  by_contra hab
  rw [List.mem_filter, List.mem_range] at ha hb
  obtain ⟨hna, hpa⟩ := ha
  obtain ⟨hnb, hpb⟩ := hb
  obtain ⟨oa, hoa⟩ := exists_slotNum φ (lt_trans hna (slotNum_lt φ o))
  obtain ⟨ob, hob⟩ := exists_slotNum φ (lt_trans hnb (slotNum_lt φ o))
  have hla : φ.litAt oa = φ.litAt o :=
    litAt_eq_of_litOfSlot φ (by rw [hoa]; exact of_decide_eq_true (by simpa using hpa))
  have hlb : φ.litAt ob = φ.litAt o :=
    litAt_eq_of_litOfSlot φ (by rw [hob]; exact of_decide_eq_true (by simpa using hpb))
  have hnea : oa ≠ o := fun hh => by rw [hh] at hoa; omega
  have hneb : ob ≠ o := fun hh => by rw [hh] at hob; omega
  have hneab : oa ≠ ob := fun hh => hab (by rw [← hoa, ← hob, hh])
  have hsub : ({oa, ob, o} : Finset φ.Occ) ⊆ sameLit φ (φ.litAt o) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem_sameLit φ hla
    · exact mem_sameLit φ hlb
    · exact mem_sameLit φ rfl
  have hcard : ({oa, ob, o} : Finset φ.Occ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hneab, hnea]),
      Finset.card_insert_of_notMem (by simp [hneb]), Finset.card_singleton]
  have := Finset.card_le_card hsub
  have := card_sameLit_le φ (φ.litAt o)
  omega

/-- The rank of a position, as one of two. -/
noncomputable def rankOf (o : φ.Occ) : Fin 2 :=
  ⟨slotRank φ (slotNum φ o), by have := slotRank_le_one φ o; omega⟩

/-- **Positions of the same literal have different ranks.** -/
theorem occ_eq_of_lit_rank {o o' : φ.Occ} (hl : φ.litAt o = φ.litAt o')
    (hr : rankOf φ o = rankOf φ o') : o = o' := by
  have hlit : litOfSlot φ (slotNum φ o) = litOfSlot φ (slotNum φ o') := by
    rw [litOfSlot_slotNum, litOfSlot_slotNum, hl]
  have hrank : slotRank φ (slotNum φ o) = slotRank φ (slotNum φ o') :=
    congrArg Fin.val hr
  rcases Nat.lt_trichotomy (slotNum φ o) (slotNum φ o') with h | h | h
  · exact absurd hrank (by have := slotRank_lt φ h hlit; omega)
  · exact slotNum_injective φ h
  · exact absurd hrank (by have := slotRank_lt φ h hlit.symm; omega)

end Lax117284Proofs.Theorem7Slots
