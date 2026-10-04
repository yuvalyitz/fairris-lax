import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Logic.Relation
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-! ### `Lax117284Proofs.Treewidth.Seq.Basic` -/

section
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

end

/-! ### `Lax117284Proofs.Treewidth.Seq.Stack` -/

section
/-!
# The stack algorithm computing the typical sequence

`typical a` is a left fold of `push` over `a`; the intermediate state is always a normal
form.  `push t y` cuts the stack back to the *leftmost* index `i` whose entry `t_i` "sees"
the rest of the stack `t_{i+1}, …` inside the interval spanned by `t_i` and the new entry `y`,
and then appends `y`.
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- The part of the stack that survives when `y` is pushed. -/
def cut : List ℕ → ℕ → List ℕ
  | [], _ => []
  | x :: t, y =>
    if (∀ z ∈ t, InR z x y) then (if t = [] ∧ x = y then [] else [x]) else x :: cut t y

/-- Push `y` on the stack `t` (bottom first). -/
def push (t : List ℕ) (y : ℕ) : List ℕ := cut t y ++ [y]

/-- The typical sequence `τ(a)` (Def. 3.5), computed by the stack algorithm. -/
def typical (a : List ℕ) : List ℕ := a.foldl push []

/-- Index `i` is a *candidate* for the new entry `y`: everything above it lies between `t_i` and
`y`. -/
def Cand (t : List ℕ) (i y : ℕ) : Prop :=
  ∀ k, i < k → k < t.length → InR (ent t k) (ent t i) y

theorem cand_cons_zero {x : ℕ} {t : List ℕ} {y : ℕ} :
    Cand (x :: t) 0 y ↔ ∀ z ∈ t, InR z x y := by
  constructor
  · intro h z hz
    obtain ⟨u, hu, rfl⟩ := List.mem_iff_getElem.mp hz
    have := h (u + 1) (by omega) (by simp; omega)
    rw [← ent_eq_getElem hu]; simpa using this
  · intro h k hk hk'
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [ent_cons_succ, ent_cons_zero]
    exact h _ (ent_mem (by simp at hk'; omega))

theorem cand_cons_succ {x : ℕ} {t : List ℕ} {i y : ℕ} :
    Cand (x :: t) (i + 1) y ↔ Cand t i y := by
  constructor
  · intro h k hk hk'
    have := h (k + 1) (by omega) (by simp; omega)
    simpa using this
  · intro h k hk hk'
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [ent_cons_succ]
    exact h _ (by omega) (by simp at hk'; omega)

theorem cut_spec {t : List ℕ} {y : ℕ} (h0 : t ≠ []) (hy : t ≠ [y]) :
    ∃ i, i < t.length ∧ Cand t i y ∧ (∀ i' < i, ¬ Cand t i' y) ∧ cut t y = t.take (i + 1) := by
  induction t with
  | nil => exact absurd rfl h0
  | cons x t0 ih =>
    by_cases h : ∀ z ∈ t0, InR z x y
    · have hc : cut (x :: t0) y = [x] := by
        rw [cut, if_pos h, if_neg]
        rintro ⟨h1, h2⟩; subst h1; subst h2; exact hy rfl
      exact ⟨0, by simp, cand_cons_zero.mpr h, fun i' hi' => absurd hi' (by omega), by simp [hc]⟩
    · have hc : cut (x :: t0) y = x :: cut t0 y := by rw [cut, if_neg h]
      have ht0 : t0 ≠ [] := by
        rintro rfl; exact h (by simp)
      have ht0y : t0 ≠ [y] := by
        rintro rfl; exact h (by simp [InR.right])
      obtain ⟨i, hi, hci, hli, hcut⟩ := ih ht0 ht0y
      refine ⟨i + 1, by simp; omega, cand_cons_succ.mpr hci, ?_, ?_⟩
      · intro i' hi'
        cases i' with
        | zero => exact fun hc0 => h (cand_cons_zero.mp hc0)
        | succ i'' => exact fun hc' => hli i'' (by omega) (cand_cons_succ.mp hc')
      · rw [hc, hcut]; simp

theorem push_eq {t : List ℕ} {y i : ℕ} (h0 : t ≠ []) (hy : t ≠ [y]) (hi : i < t.length)
    (hc : Cand t i y) (hl : ∀ i' < i, ¬ Cand t i' y) : push t y = t.take (i + 1) ++ [y] := by
  obtain ⟨i0, hi0, hc0, hl0, hcut⟩ := cut_spec h0 hy
  have : i = i0 := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact hl0 i hlt hc
    · exact hl i0 hgt hc0
  subst this
  simp [push, hcut]

theorem push_nil (y : ℕ) : push [] y = [y] := by simp [push, cut]

theorem push_single_self (y : ℕ) : push [y] y = [y] := by simp [push, cut]

theorem push_ne_nil (t : List ℕ) (y : ℕ) : push t y ≠ [] := by simp [push]

theorem push_getLast (t : List ℕ) (y : ℕ) : (push t y).getLast? = some y := by simp [push]

theorem nf_singleton (x : ℕ) : NF [x] := by
  rw [nf_iff]
  refine ⟨fun k hk => ?_, fun k j hw => ?_⟩
  · have := hk.1; simp at this
  · have := hw.2.1; have := hw.1; simp at *; omega

/-! ### Entries of `t.take (i+1) ++ [y]` -/

theorem ent_take {t : List ℕ} {n m : ℕ} (h : m < n) : ent (t.take n) m = ent t m := by
  unfold ent
  simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

theorem ent_top {t : List ℕ} {i y m : ℕ} (hi : i < t.length) (hm : m ≤ i) :
    ent (t.take (i + 1) ++ [y]) m = ent t m := by
  rw [ent_append_left _ (by simp; omega), ent_take (by omega)]

theorem ent_top_new {t : List ℕ} {i y : ℕ} (hi : i < t.length) :
    ent (t.take (i + 1) ++ [y]) (i + 1) = y := by
  have hl : (t.take (i + 1)).length = i + 1 := by simp; omega
  rw [ent_append_right _ (by omega), hl]
  simp

/-! ### `push` preserves normal forms -/

theorem nf_push {t : List ℕ} (ht : NF t) (y : ℕ) : NF (push t y) := by
  by_cases h0 : t = []
  · subst h0; rw [push_nil]; exact nf_singleton y
  by_cases hy : t = [y]
  · subst hy; rw [push_single_self]; exact nf_singleton y
  obtain ⟨i, hi, hc, hl, hcut⟩ := cut_spec h0 hy
  have hp : push t y = t.take (i + 1) ++ [y] := by simp [push, hcut]
  rw [hp]
  have ht' := nf_iff.mp ht
  obtain ⟨hd, hw⟩ := ht'
  have hlen : (t.take (i + 1) ++ [y]).length = i + 2 := by simp; omega
  have e1 : ∀ m ≤ i, ent (t.take (i + 1) ++ [y]) m = ent t m := fun m hm => ent_top hi hm
  have e2 : ent (t.take (i + 1) ++ [y]) (i + 1) = y := ent_top_new hi
  rw [nf_iff]
  refine ⟨fun k hk => ?_, fun k j hwin => ?_⟩
  · obtain ⟨hk1, hk2⟩ := hk
    rw [hlen] at hk1
    by_cases hki : k + 1 ≤ i
    · rw [e1 k (by omega), e1 (k + 1) hki] at hk2
      exact hd k ⟨by omega, hk2⟩
    · have hk : k = i := by omega
      subst hk
      rw [e1 k le_rfl, e2] at hk2
      by_cases hlt : k + 1 < t.length
      · have := hc (k + 1) (by omega) hlt
        rw [hk2] at this
        have := InR.self_iff.mp this
        exact hd k ⟨hlt, by rw [hk2, this]⟩
      · have hlen1 : t.length = k + 1 := by omega
        by_cases hk0 : k = 0
        · subst hk0
          obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen1
          simp at hk2; exact hy (by rw [hk2])
        · apply hl (k - 1) (by omega)
          intro m hm1 hm2
          have : m = k := by omega
          subst this
          rw [hk2]; exact InR.right _ _
  · obtain ⟨hk1, hj, hwin⟩ := hwin
    rw [hlen] at hj
    by_cases hji : j ≤ i
    · apply hw k j
      refine ⟨hk1, by omega, fun m hm1 hm2 => ?_⟩
      have := hwin m hm1 hm2
      rwa [e1 m (by omega), e1 k (by omega), e1 j hji] at this
    · have hj' : j = i + 1 := by omega
      subst hj'
      apply hl k (by omega)
      intro m hm1 hm2
      by_cases hmi : m ≤ i
      · have := hwin m hm1 (by omega)
        rwa [e1 m hmi, e1 k (by omega), e2] at this
      · have h1 := hc m (by omega) hm2
        have h2 := hwin i (by omega) (by omega)
        rw [e1 i le_rfl, e1 k (by omega), e2] at h2
        unfold InR at *; omega

/-! ### The fixed points of `push` -/

/-- Appending to a normal form that stays a normal form is `push`. -/
theorem push_of_nf {t : List ℕ} {y : ℕ} (h : NF (t ++ [y])) : push t y = t ++ [y] := by
  by_cases h0 : t = []
  · subst h0; simp [push_nil]
  by_cases hy : t = [y]
  · subst hy
    exfalso; exact ((nf_iff.mp h).1 0) ⟨by simp, by simp [ent]⟩
  obtain ⟨i, hi, hc, hl, hcut⟩ := cut_spec h0 hy
  have hin : i = t.length - 1 := by
    by_contra hne
    have hlt : i + 1 < t.length := by omega
    apply (nf_iff.mp h).2 i t.length
    refine ⟨by omega, by simp, fun m hm1 hm2 => ?_⟩
    rw [ent_append_left _ hm2, ent_append_left _ hi, ent_append_right _ (le_refl _)]
    simpa using hc m hm1 hm2
  have : t.length - 1 + 1 = t.length := by omega
  rw [push, hcut, hin, this, List.take_length]

/-- Pushing the current top of a normal form changes nothing. -/
theorem push_of_last {t : List ℕ} {y : ℕ} (ht : NF t) (hlast : t.getLast? = some y) :
    push t y = t := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  by_cases hys : ys = []
  · subst hys; exact push_single_self y
  have h0 : ys ++ [y] ≠ [] := by simp
  have hy : ys ++ [y] ≠ [y] := by simpa using hys
  obtain ⟨i, hi, hc, hl, hcut⟩ := cut_spec h0 hy
  have hn : 1 ≤ ys.length := List.length_pos_iff.mpr hys
  have hlen : (ys ++ [y]).length = ys.length + 1 := by simp
  have hly : ent (ys ++ [y]) ys.length = y := by
    rw [ent_append_right _ (le_refl _)]; simp
  have hin : i = ys.length - 1 := by
    apply le_antisymm
    · by_contra hne
      apply hl (ys.length - 1) (by omega)
      intro k hk1 hk2
      have : k = ys.length := by omega
      subst this; rw [hly]; exact InR.right _ _
    · by_contra hne
      apply (nf_iff.mp ht).2 i ys.length
      refine ⟨by omega, by omega, fun m hm1 hm2 => ?_⟩
      rw [hly]; exact hc m hm1 (by omega)
  have : ys.length - 1 + 1 = ys.length := by omega
  rw [push, hcut, hin, this, List.take_append_of_le_length (le_refl _), List.take_length]

/-! ### Absorption: pushing an entry that the cut index of `y` already sees changes nothing -/

theorem push_push {t : List ℕ} (ht : NF t) {y z i : ℕ} (h0 : t ≠ []) (hy : t ≠ [y])
    (hi : i < t.length) (hc : Cand t i y) (hl : ∀ i' < i, ¬ Cand t i' y)
    (hz : InR z (ent t i) y) : push (push t z) y = push t y := by
  have hpy : push t y = t.take (i + 1) ++ [y] := push_eq h0 hy hi hc hl
  by_cases htz : t = [z]
  · subst htz; rw [push_single_self]
  obtain ⟨j, hj, hcj, hlj, hcutj⟩ := cut_spec h0 htz
  have hpz : push t z = t.take (j + 1) ++ [z] := by simp [push, hcutj]
  have hlen' : (t.take (j + 1) ++ [z]).length = j + 2 := by simp; omega
  have e1 : ∀ m ≤ j, ent (t.take (j + 1) ++ [z]) m = ent t m := fun m hm => ent_top hj hm
  have e2 : ent (t.take (j + 1) ++ [z]) (j + 1) = z := ent_top_new hj
  have ht'0 : t.take (j + 1) ++ [z] ≠ [] := by
    intro h; rw [h] at hlen'; simp at hlen'
  have ht'y : t.take (j + 1) ++ [z] ≠ [y] := by
    intro h; rw [h] at hlen'; simp at hlen'
  rw [hpz]
  by_cases hij : i ≤ j
  · have hc' : Cand (t.take (j + 1) ++ [z]) i y := by
      intro k hk1 hk2
      by_cases hkj : k ≤ j
      · rw [e1 k hkj, e1 i hij]; exact hc k hk1 (by omega)
      · have : k = j + 1 := by omega
        rw [this, e2, e1 i hij]; exact hz
    have hl' : ∀ i' < i, ¬ Cand (t.take (j + 1) ++ [z]) i' y := by
      intro i' hi' hcand
      apply hl i' hi'
      intro k hk1 hk2
      by_cases hkj : k ≤ j
      · rw [← e1 k hkj, ← e1 i' (by omega)]; exact hcand k hk1 (by omega)
      · have h1 := hcj k (by omega) hk2
        have h2 := hcand j (by omega) (by omega)
        have h3 := hcand (j + 1) (by omega) (by omega)
        rw [e1 j le_rfl, e1 i' (by omega)] at h2
        rw [e2, e1 i' (by omega)] at h3
        unfold InR at *; omega
    rw [push_eq ht'0 ht'y (by omega) hc' hl', hpy]
    congr 1
    rw [List.take_append_of_le_length (by simp; omega), List.take_take]
    congr 1; omega
  · have hji : j < i := by omega
    have h1 : InR (ent t i) (ent t j) z := hcj i hji hi
    have hzeq : ent t i = z := by
      by_contra hne
      apply hl j hji
      intro k hk1 hk2
      have h2 := hcj k hk1 hk2
      unfold InR at *; omega
    have hij1 : i = j + 1 := by
      by_contra hne
      have hwin : Win t j i := ⟨by omega, hi, fun m hm1 hm2 => by
        have := hcj m hm1 (by omega); rw [hzeq]; exact this⟩
      exact (nf_iff.mp ht).2 j i hwin
    subst hij1
    have hc' : Cand (t.take (j + 1) ++ [z]) (j + 1) y := fun k hk1 hk2 => by omega
    have hl' : ∀ i' < j + 1, ¬ Cand (t.take (j + 1) ++ [z]) i' y := by
      intro i' hi' hcand
      apply hl i' (by omega)
      intro k hk1 hk2
      have h3 := hcand (j + 1) (by omega) (by omega)
      rw [e2, e1 i' (by omega)] at h3
      by_cases hkj : k ≤ j
      · rw [← e1 k hkj, ← e1 i' (by omega)]; exact hcand k hk1 (by omega)
      · have h1 := hcj k (by omega) hk2
        have h2 : InR (ent t j) (ent t i') y := by
          by_cases hij' : i' = j
          · subst hij'; exact InR.left _ _
          · have := hcand j (by omega) (by omega)
            rwa [e1 j le_rfl, e1 i' (by omega)] at this
        unfold InR at *; omega
    rw [push_eq ht'0 ht'y (by omega) hc' hl', hpy]
    congr 1
    have hh : (t.take (j + 1) ++ [z]).take (j + 1 + 1) = t.take (j + 1 + 1) := by
      rw [List.take_of_length_le (by omega), List.take_succ_eq_append_getElem (i := j + 1) (by omega),
        ← ent_eq_getElem (by omega), hzeq]
    rw [hh]

/-! ### Skipping a window -/

theorem foldl_push_inv {t : List ℕ} {x y i : ℕ} (h0 : t ≠ []) (hy : t ≠ [y])
    (hi : i < t.length) (hc : Cand t i y) (hl : ∀ i' < i, ¬ Cand t i' y)
    (hx : InR x (ent t i) y) :
    ∀ (m t' : List ℕ), NF t' → push t' y = push t y → (∀ w ∈ m, InR w x y) →
      NF (m.foldl push t') ∧ push (m.foldl push t') y = push t y := by
  intro m
  induction m with
  | nil => intro t' h1 h2 _; exact ⟨h1, h2⟩
  | cons w m ih =>
    intro t' h1 h2 hm
    have hpy : push t y = t.take (i + 1) ++ [y] := push_eq h0 hy hi hc hl
    have hlen : (push t y).length = i + 2 := by rw [hpy]; simp; omega
    have ht'0 : t' ≠ [] := by
      rintro rfl; rw [push_nil] at h2; rw [← h2] at hlen; simp at hlen
    have ht'y : t' ≠ [y] := by
      rintro rfl; rw [push_single_self] at h2; rw [← h2] at hlen; simp at hlen
    obtain ⟨i', hi', hc', hl', hcut'⟩ := cut_spec ht'0 ht'y
    have hpy' : push t' y = t'.take (i' + 1) ++ [y] := by simp [push, hcut']
    have htk : t'.take (i' + 1) = t.take (i + 1) := by
      rw [hpy'] at h2; rw [hpy] at h2; exact List.append_cancel_right h2
    have hii : i' = i := by
      have := congrArg List.length htk
      simp at this; omega
    subst hii
    have hent : ent t' i' = ent t i' := by
      have := congrArg (fun l => ent l i') htk
      simp only [ent_take (Nat.lt_succ_self i')] at this
      exact this
    have hw : InR w (ent t' i') y := by
      have := hm w (List.mem_cons_self ..)
      rw [hent]; unfold InR at *; omega
    have hnf' : NF t' := h1
    have hpp := push_push hnf' ht'0 ht'y hi' hc' hl' hw
    refine ih (push t' w) (nf_push h1 w) ?_ (fun w' hw' => hm w' (List.mem_cons_of_mem _ hw'))
    rw [hpp, h2]

theorem foldl_push_window {t : List ℕ} (ht : NF t) {x y : ℕ} (hlast : t.getLast? = some x)
    (m : List ℕ) (hm : ∀ z ∈ m, InR z x y) : (m ++ [y]).foldl push t = push t y := by
  by_cases hty : t = [y]
  · subst hty
    have hx : x = y := by simpa using hlast.symm
    subst hx
    have : ∀ m : List ℕ, (∀ z ∈ m, InR z x x) → (m ++ [x]).foldl push [x] = push [x] x := by
      intro m
      induction m with
      | nil => intro _; rfl
      | cons w m ih =>
        intro hm
        have hw : w = x := InR.self_iff.mp (hm w (List.mem_cons_self ..))
        subst hw
        simp only [List.cons_append, List.foldl_cons, push_single_self] at *
        exact ih (fun z hz => hm z (List.mem_cons_of_mem _ hz))
    exact this m hm
  · have h0 : t ≠ [] := by rintro rfl; simp at hlast
    obtain ⟨i, hi, hc, hl, hcut⟩ := cut_spec h0 hty
    have hx : InR x (ent t i) y := by
      have hlt : t.length - 1 < t.length := by have := List.length_pos_iff.mpr h0; omega
      have hxe : ent t (t.length - 1) = x := by
        rw [ent_eq_getElem hlt]
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlt] at hlast
        exact Option.some.inj hlast
      by_cases hin : i = t.length - 1
      · rw [← hin] at hxe; rw [← hxe]; exact InR.left _ _
      · have := hc (t.length - 1) (by omega) hlt
        rwa [hxe] at this
    have := (foldl_push_inv h0 hty hi hc hl hx m t ht rfl hm).2
    rw [List.foldl_append]
    simpa using this

end Lax117284Proofs.Treewidth.Seq

end
