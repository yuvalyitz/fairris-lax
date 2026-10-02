import Lax117284Proofs.Treewidth.Seq.Symmetry
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# Structure of typical sequences (Bodlaender–Kloks, Lemma 3.3)

* `maxOf`, `minOf` and the invariance of the set of upper (lower) bounds under the two
  operations, hence `maxOf (typical a) = maxOf a` (**Lemma 3.3 (i)**);
* the *spiral lemma*: if `NF (u ++ [w])` and `w` is strictly above (below) every entry of `u`,
  then the last entry of `u` is a strict minimum (maximum) of `u`; consequently such a `u` has
  pairwise distinct entries and is uniquely determined by its set of values;
* the *extreme lemma*: a non-empty normal form contains its minimum exactly once or its maximum
  exactly once;
* **Lemma 3.3 (ii)**: `(typical a).length ≤ 2 * maxOf a + 1`.
-/

namespace Lax117284Proofs.Treewidth.Seq

/-! ### Maximum and minimum -/

/-- The maximum entry (`0` for the empty list). -/
def maxOf (a : List ℕ) : ℕ := a.foldr max 0

/-- The minimum entry (`0` for the empty list). -/
def minOf : List ℕ → ℕ
  | [] => 0
  | x :: a => a.foldr min x

theorem maxOf_nil : maxOf [] = 0 := rfl
theorem maxOf_cons (x : ℕ) (a : List ℕ) : maxOf (x :: a) = max x (maxOf a) := rfl

theorem le_maxOf {a : List ℕ} {x : ℕ} (h : x ∈ a) : x ≤ maxOf a := by
  induction a with
  | nil => simp at h
  | cons y t ih =>
    rw [maxOf_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem maxOf_le {a : List ℕ} {L : ℕ} (h : ∀ x ∈ a, x ≤ L) : maxOf a ≤ L := by
  induction a with
  | nil => exact Nat.zero_le _
  | cons y t ih =>
    rw [maxOf_cons]
    exact max_le (h y (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem maxOf_le_iff {a : List ℕ} {L : ℕ} : maxOf a ≤ L ↔ ∀ x ∈ a, x ≤ L :=
  ⟨fun h x hx => (le_maxOf hx).trans h, maxOf_le⟩

theorem maxOf_mem {a : List ℕ} (h : a ≠ []) : maxOf a ∈ a := by
  induction a with
  | nil => exact absurd rfl h
  | cons y t ih =>
    rw [maxOf_cons]
    by_cases ht : t = []
    · subst ht; simp [maxOf_nil]
    · rcases max_choice y (maxOf t) with e | e
      · rw [e]; simp
      · rw [e]; exact List.mem_cons_of_mem _ (ih ht)

theorem foldr_min_le (x : ℕ) (a : List ℕ) : ∀ z ∈ x :: a, a.foldr min x ≤ z := by
  induction a with
  | nil => intro z hz; simp at hz; simp [hz]
  | cons y t ih =>
    intro z hz
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hz with rfl | hz
    · exact (min_le_right _ _).trans (ih z (by simp))
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih z (List.mem_cons_of_mem _ hz))

theorem foldr_min_mem (x : ℕ) (a : List ℕ) : a.foldr min x ∈ x :: a := by
  induction a with
  | nil => simp
  | cons y t ih =>
    simp only [List.foldr_cons]
    rcases min_choice y (t.foldr min x) with e | e
    · rw [e]; simp
    · rw [e]
      rcases List.mem_cons.1 ih with h | h
      · rw [h]; simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem minOf_le {a : List ℕ} {x : ℕ} (h : x ∈ a) : minOf a ≤ x := by
  cases a with
  | nil => simp at h
  | cons y t => exact foldr_min_le y t x h

theorem minOf_mem {a : List ℕ} (h : a ≠ []) : minOf a ∈ a := by
  cases a with
  | nil => exact absurd rfl h
  | cons y t => exact foldr_min_mem y t

/-! ### Lemma 3.3 (i): the bounds are invariant -/

theorem Red.upper_iff {a b : List ℕ} (h : Red a b) (L : ℕ) :
    (∀ x ∈ b, x ≤ L) ↔ ∀ x ∈ a, x ≤ L := by
  constructor
  · intro hb
    cases h with
    | dup l x r =>
      intro z hz
      apply hb z
      simp only [List.mem_append, List.mem_cons] at hz ⊢
      tauto
    | typ l x m y r hm hz =>
      intro z hzm
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      simp only [List.mem_append, List.mem_cons] at hzm
      by_cases hzz : z ∈ m
      · have := hz z hzz
        unfold InR at this; omega
      · apply hb z
        simp only [List.mem_append, List.mem_cons]
        tauto
  · intro ha x hx; exact ha x (h.sublist.subset hx)

theorem Red.lower_iff {a b : List ℕ} (h : Red a b) (L : ℕ) :
    (∀ x ∈ b, L ≤ x) ↔ ∀ x ∈ a, L ≤ x := by
  constructor
  · intro hb
    cases h with
    | dup l x r =>
      intro z hz
      apply hb z
      simp only [List.mem_append, List.mem_cons] at hz ⊢
      tauto
    | typ l x m y r hm hz =>
      intro z hzm
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      simp only [List.mem_append, List.mem_cons] at hzm
      by_cases hzz : z ∈ m
      · have := hz z hzz
        unfold InR at this; omega
      · apply hb z
        simp only [List.mem_append, List.mem_cons]
        tauto
  · intro ha x hx; exact ha x (h.sublist.subset hx)

theorem Reach.upper_iff {a b : List ℕ} (h : Reach a b) (L : ℕ) :
    (∀ x ∈ b, x ≤ L) ↔ ∀ x ∈ a, x ≤ L := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hr ih => exact (hr.upper_iff L).trans ih

theorem Reach.lower_iff {a b : List ℕ} (h : Reach a b) (L : ℕ) :
    (∀ x ∈ b, L ≤ x) ↔ ∀ x ∈ a, L ≤ x := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hr ih => exact (hr.lower_iff L).trans ih

/-- Every entry of the typical sequence occurs in the original sequence. -/
theorem mem_of_mem_typical {a : List ℕ} {x : ℕ} (h : x ∈ typical a) : x ∈ a :=
  (reach_typical a).sublist.subset h

/-- **Lemma 3.3 (i)**, in the form of bounds. -/
theorem typical_upper_iff (a : List ℕ) (L : ℕ) :
    (∀ x ∈ typical a, x ≤ L) ↔ ∀ x ∈ a, x ≤ L := (reach_typical a).upper_iff L

theorem typical_lower_iff (a : List ℕ) (L : ℕ) :
    (∀ x ∈ typical a, L ≤ x) ↔ ∀ x ∈ a, L ≤ x := (reach_typical a).lower_iff L

/-- **Lemma 3.3 (i)**: the maximum is invariant. -/
theorem maxOf_typical (a : List ℕ) : maxOf (typical a) = maxOf a := by
  apply le_antisymm
  · exact maxOf_le ((typical_upper_iff a _).2 fun x hx => le_maxOf hx)
  · exact maxOf_le fun x hx =>
      (typical_upper_iff a (maxOf (typical a))).1 (fun y hy => le_maxOf hy) x hx

/-- **Lemma 3.3 (i)**: the minimum is invariant. -/
theorem minOf_typical {a : List ℕ} (ha : a ≠ []) : minOf (typical a) = minOf a := by
  have hb : typical a ≠ [] := typical_ne_nil ha
  apply le_antisymm
  · exact (typical_lower_iff a (minOf (typical a))).1 (fun y hy => minOf_le hy) _ (minOf_mem ha)
  · exact (typical_lower_iff a (minOf a)).2 (fun y hy => minOf_le hy) _ (minOf_mem hb)

/-! ### Windows and repetitions at the level of lists -/

theorem nf_no_win {l m r : List ℕ} {x y : ℕ} (h : NF (l ++ x :: (m ++ y :: r))) (hm : m ≠ [])
    (hz : ∀ z ∈ m, InR z x y) : False := h _ (Red.typ l x m y r hm hz)

theorem nf_no_dup {l r : List ℕ} {x : ℕ} (h : NF (l ++ x :: x :: r)) : False :=
  h _ (Red.dup l x r)

/-! ### The spiral lemma -/

/-- If `w` is strictly above all of `v ++ [e]`, then `e` is strictly below all of `v`. -/
theorem spiral_last_min {v : List ℕ} {e w : ℕ} (h : NF (v ++ [e] ++ [w]))
    (hw : ∀ x ∈ v ++ [e], x < w) : ∀ x ∈ v, e < x := by
  intro x hx
  by_contra hxe
  have hxe : x ≤ e := by omega
  have hv : v ≠ [] := List.ne_nil_of_mem hx
  obtain ⟨m0, hm0, hle⟩ : ∃ m0 ∈ v, ∀ z ∈ v, m0 ≤ z :=
    ⟨minOf v, minOf_mem hv, fun z hz => minOf_le hz⟩
  have hm0e : m0 ≤ e := (hle x hx).trans hxe
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hm0
  refine nf_no_win (l := s) (m := t ++ [e]) (r := []) (x := m0) (y := w) ?_ (by simp) ?_
  · have : s ++ m0 :: t ++ [e] ++ [w] = s ++ m0 :: ((t ++ [e]) ++ w :: []) := by simp
    rwa [this] at h
  · intro z hz
    have hzw : z < w := hw z (by simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto)
    have hz0 : m0 ≤ z := by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with hz | rfl
      · exact hle z (by simp [hz])
      · exact hm0e
    unfold InR; omega

/-- If `w` is strictly below all of `v ++ [e]`, then `e` is strictly above all of `v`. -/
theorem spiral_last_max {v : List ℕ} {e w : ℕ} (h : NF (v ++ [e] ++ [w]))
    (hw : ∀ x ∈ v ++ [e], w < x) : ∀ x ∈ v, x < e := by
  intro x hx
  by_contra hxe
  have hxe : e ≤ x := by omega
  have hv : v ≠ [] := List.ne_nil_of_mem hx
  obtain ⟨m0, hm0, hle⟩ : ∃ m0 ∈ v, ∀ z ∈ v, z ≤ m0 :=
    ⟨maxOf v, maxOf_mem hv, fun z hz => le_maxOf hz⟩
  have hm0e : e ≤ m0 := hxe.trans (hle x hx)
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hm0
  refine nf_no_win (l := s) (m := t ++ [e]) (r := []) (x := m0) (y := w) ?_ (by simp) ?_
  · have : s ++ m0 :: t ++ [e] ++ [w] = s ++ m0 :: ((t ++ [e]) ++ w :: []) := by simp
    rwa [this] at h
  · intro z hz
    have hzw : w < z := hw z (by simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto)
    have hz0 : z ≤ m0 := by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with hz | rfl
      · exact hle z (by simp [hz])
      · exact hm0e
    unfold InR; omega

theorem eq_nil_or_snoc (u : List ℕ) : u = [] ∨ ∃ v e, u = v ++ [e] := by
  rcases List.eq_nil_or_concat u with h | ⟨v, e, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨v, e, by simpa using h⟩

theorem spiral_nodup_aux : ∀ n : ℕ, ∀ (u : List ℕ) (w : ℕ), u.length ≤ n → NF (u ++ [w]) →
    ((∀ x ∈ u, x < w) ∨ (∀ x ∈ u, w < x)) → u.Nodup := by
  intro n
  induction n with
  | zero =>
    intro u w hl _ _
    have : u = [] := List.length_eq_zero_iff.1 (by omega)
    subst this; exact List.nodup_nil
  | succ n ih =>
    intro u w hl h hw
    rcases eq_nil_or_snoc u with rfl | ⟨v, e, rfl⟩
    · exact List.nodup_nil
    · have hv : v.length ≤ n := by simp at hl; omega
      have hnf : NF (v ++ [e]) := h.append_left
      rcases hw with hw | hw
      · have hs := spiral_last_min h hw
        have := ih v e hv hnf (Or.inr hs)
        rw [List.nodup_append]
        refine ⟨this, List.nodup_singleton _, ?_⟩
        intro x hx y hy
        simp only [List.mem_singleton] at hy; subst hy
        exact Nat.ne_of_gt (hs x hx)
      · have hs := spiral_last_max h hw
        have := ih v e hv hnf (Or.inl hs)
        rw [List.nodup_append]
        refine ⟨this, List.nodup_singleton _, ?_⟩
        intro x hx y hy
        simp only [List.mem_singleton] at hy; subst hy
        exact Nat.ne_of_lt (hs x hx)

/-- A *spiral* `u` (a normal form `u ++ [w]` with `w` strictly on one side of all of `u`) has
pairwise distinct entries. -/
theorem spiral_nodup {u : List ℕ} {w : ℕ} (h : NF (u ++ [w]))
    (hw : (∀ x ∈ u, x < w) ∨ (∀ x ∈ u, w < x)) : u.Nodup :=
  spiral_nodup_aux u.length u w le_rfl h hw

theorem spiral_unique_aux : ∀ n : ℕ, ∀ (u u' : List ℕ) (w : ℕ), u.length ≤ n →
    NF (u ++ [w]) → NF (u' ++ [w]) →
    (((∀ x ∈ u, x < w) ∧ (∀ x ∈ u', x < w)) ∨ ((∀ x ∈ u, w < x) ∧ (∀ x ∈ u', w < x))) →
    (∀ x, x ∈ u ↔ x ∈ u') → u = u' := by
  intro n
  induction n with
  | zero =>
    intro u u' w hl _ _ _ hs
    have : u = [] := List.length_eq_zero_iff.1 (by omega)
    subst this
    rcases eq_nil_or_snoc u' with rfl | ⟨v', e', rfl⟩
    · rfl
    · exact absurd ((hs e').2 (by simp)) (by simp)
  | succ n ih =>
    intro u u' w hl h h' hw hs
    rcases eq_nil_or_snoc u with rfl | ⟨v, e, rfl⟩
    · rcases eq_nil_or_snoc u' with rfl | ⟨v', e', rfl⟩
      · rfl
      · exact absurd ((hs e').2 (by simp)) (by simp)
    · rcases eq_nil_or_snoc u' with rfl | ⟨v', e', rfl⟩
      · exact absurd ((hs e).1 (by simp)) (by simp)
      · have hv : v.length ≤ n := by simp at hl; omega
        have hnf : NF (v ++ [e]) := h.append_left
        have hnf' : NF (v' ++ [e']) := h'.append_left
        rcases hw with ⟨hw, hw'⟩ | ⟨hw, hw'⟩
        · have s1 := spiral_last_min h hw
          have s2 := spiral_last_min h' hw'
          have e1 : e' ≤ e := by
            have : e ∈ v' ++ [e'] := (hs e).1 (by simp)
            rcases List.mem_append.1 this with h1 | h1
            · exact Nat.le_of_lt (s2 e h1)
            · simp at h1; omega
          have e2 : e ≤ e' := by
            have : e' ∈ v ++ [e] := (hs e').2 (by simp)
            rcases List.mem_append.1 this with h1 | h1
            · exact Nat.le_of_lt (s1 e' h1)
            · simp at h1; omega
          have hee : e = e' := le_antisymm e2 e1
          subst hee
          have := ih v v' e hv hnf hnf' (Or.inr ⟨s1, s2⟩) (by
            intro x
            constructor
            · intro hx
              have := (hs x).1 (by simp [hx])
              rcases List.mem_append.1 this with h1 | h1
              · exact h1
              · simp at h1; have := s1 x hx; omega
            · intro hx
              have := (hs x).2 (by simp [hx])
              rcases List.mem_append.1 this with h1 | h1
              · exact h1
              · simp at h1; have := s2 x hx; omega)
          rw [this]
        · have s1 := spiral_last_max h hw
          have s2 := spiral_last_max h' hw'
          have e1 : e ≤ e' := by
            have : e ∈ v' ++ [e'] := (hs e).1 (by simp)
            rcases List.mem_append.1 this with h1 | h1
            · exact Nat.le_of_lt (s2 e h1)
            · simp at h1; omega
          have e2 : e' ≤ e := by
            have : e' ∈ v ++ [e] := (hs e').2 (by simp)
            rcases List.mem_append.1 this with h1 | h1
            · exact Nat.le_of_lt (s1 e' h1)
            · simp at h1; omega
          have hee : e = e' := le_antisymm e1 e2
          subst hee
          have := ih v v' e hv hnf hnf' (Or.inl ⟨s1, s2⟩) (by
            intro x
            constructor
            · intro hx
              have := (hs x).1 (by simp [hx])
              rcases List.mem_append.1 this with h1 | h1
              · exact h1
              · simp at h1; have := s1 x hx; omega
            · intro hx
              have := (hs x).2 (by simp [hx])
              rcases List.mem_append.1 this with h1 | h1
              · exact h1
              · simp at h1; have := s2 x hx; omega)
          rw [this]

/-- **Uniqueness of spirals** (entries below `w`). -/
theorem spiral_unique_lt {u u' : List ℕ} {w : ℕ} (h : NF (u ++ [w])) (h' : NF (u' ++ [w]))
    (hu : ∀ x ∈ u, x < w) (hu' : ∀ x ∈ u', x < w) (hs : ∀ x, x ∈ u ↔ x ∈ u') : u = u' :=
  spiral_unique_aux u.length u u' w le_rfl h h' (Or.inl ⟨hu, hu'⟩) hs

/-- **Uniqueness of spirals** (entries above `w`). -/
theorem spiral_unique_gt {u u' : List ℕ} {w : ℕ} (h : NF (u ++ [w])) (h' : NF (u' ++ [w]))
    (hu : ∀ x ∈ u, w < x) (hu' : ∀ x ∈ u', w < x) (hs : ∀ x, x ∈ u ↔ x ∈ u') : u = u' :=
  spiral_unique_aux u.length u u' w le_rfl h h' (Or.inr ⟨hu, hu'⟩) hs

/-- A spiral inside a finite set of values is no longer than that set. -/
theorem spiral_length_le {u : List ℕ} {w : ℕ} (h : NF (u ++ [w]))
    (hw : (∀ x ∈ u, x < w) ∨ (∀ x ∈ u, w < x)) {S : Finset ℕ} (hS : ∀ x ∈ u, x ∈ S) :
    u.length ≤ S.card := by
  rw [← List.toFinset_card_of_nodup (spiral_nodup h hw)]
  exact Finset.card_le_card fun x hx => hS x (List.mem_toFinset.1 hx)

/-! ### Extremes of a normal form -/

theorem exists_two_of_count {a : ℕ} : ∀ {l : List ℕ}, 2 ≤ l.count a →
    ∃ A B C, l = A ++ a :: (B ++ a :: C)
  | [], h => by simp at h
  | y :: t, h => by
    by_cases hy : y = a
    · subst hy
      have h1 : 0 < t.count y := by
        simp only [List.count_cons, beq_self_eq_true, if_true] at h; omega
      obtain ⟨B, C, htc⟩ := List.append_of_mem (List.count_pos_iff.1 h1)
      exact ⟨[], B, C, by simp [htc]⟩
    · have h2 : 2 ≤ t.count a := by
        simp only [List.count_cons] at h
        have : (y == a) = false := by simpa using hy
        simp [this] at h; exact h
      obtain ⟨A, B, C, e⟩ := exists_two_of_count h2
      exact ⟨y :: A, B, C, by simp [e]⟩

/-- If the maximum `M` occurs twice (`n = A ++ M :: (B ++ M :: C)`) then a strictly smaller
minimum occurs exactly once. -/
theorem nf_min_unique {A B C : List ℕ} {m M : ℕ}
    (h : NF (A ++ M :: (B ++ M :: C)))
    (hmin : ∀ z ∈ A ++ M :: (B ++ M :: C), m ≤ z) (hmax : ∀ z ∈ A ++ M :: (B ++ M :: C), z ≤ M)
    (hmM : m ≠ M) (hmn : m ∈ A ++ M :: (B ++ M :: C)) :
    (A ++ M :: (B ++ M :: C)).count m = 1 := by
  have hA : m ∉ A := by
    intro hmA
    obtain ⟨A1, A2, rfl⟩ := List.append_of_mem hmA
    refine nf_no_win (l := A1) (m := A2 ++ M :: B) (r := C) (x := m) (y := M) ?_ (by simp) ?_
    · have : A1 ++ m :: A2 ++ M :: (B ++ M :: C) = A1 ++ m :: ((A2 ++ M :: B) ++ M :: C) := by
        simp
      rwa [this] at h
    · intro z hz
      have h1 := hmin z (by simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto)
      have h2 := hmax z (by simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto)
      unfold InR; omega
  have hC : m ∉ C := by
    intro hmC
    obtain ⟨C1, C2, rfl⟩ := List.append_of_mem hmC
    refine nf_no_win (l := A) (m := B ++ M :: C1) (r := C2) (x := M) (y := m) ?_ (by simp) ?_
    · have : A ++ M :: (B ++ M :: (C1 ++ m :: C2)) = A ++ M :: ((B ++ M :: C1) ++ m :: C2) := by
        simp
      rwa [this] at h
    · intro z hz
      have h1 := hmin z (by simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto)
      have h2 := hmax z (by simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto)
      unfold InR; omega
  have hB : m ∈ B := by
    simp only [List.mem_append, List.mem_cons] at hmn
    rcases hmn with h1 | h1 | h1 | h1 | h1
    · exact absurd h1 hA
    · exact absurd h1 hmM
    · exact h1
    · exact absurd h1 hmM
    · exact absurd h1 hC
  obtain ⟨B1, B2, rfl⟩ := List.append_of_mem hB
  have hB1 : B1 = [] := by
    by_contra hne
    refine nf_no_win (l := A) (m := B1) (r := B2 ++ M :: C) (x := M) (y := m) ?_ hne ?_
    · have : A ++ M :: (B1 ++ m :: B2 ++ M :: C) = A ++ M :: (B1 ++ m :: (B2 ++ M :: C)) := by
        simp
      rwa [this] at h
    · intro z hz
      have h1 := hmin z (by simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto)
      have h2 := hmax z (by simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto)
      unfold InR; omega
  have hB2 : B2 = [] := by
    by_contra hne
    refine nf_no_win (l := A ++ M :: B1) (m := B2) (r := C) (x := m) (y := M) ?_ hne ?_
    · have : A ++ M :: (B1 ++ m :: B2 ++ M :: C) = (A ++ M :: B1) ++ m :: (B2 ++ M :: C) := by
        simp
      rwa [this] at h
    · intro z hz
      have h1 := hmin z (by simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto)
      have h2 := hmax z (by simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto)
      unfold InR; omega
  subst hB1; subst hB2
  have h0A : A.count m = 0 := List.count_eq_zero.2 hA
  have h0C : C.count m = 0 := List.count_eq_zero.2 hC
  simp [List.count_append, List.count_cons, h0A, h0C, hmM.symm]

theorem nf_count_aux {n : List ℕ} (h : NF n) {m M : ℕ} (hmin : ∀ z ∈ n, m ≤ z)
    (hmax : ∀ z ∈ n, z ≤ M) (hmn : m ∈ n) (hMn : M ∈ n) (h1 : n.count M ≠ 1) :
    n.count m = 1 := by
  have hpos : 0 < n.count M := List.count_pos_iff.2 hMn
  obtain ⟨A, B, C, hn⟩ := exists_two_of_count (a := M) (l := n) (by omega)
  subst hn
  by_cases hmM : m = M
  · exfalso
    subst hmM
    have hall : ∀ z ∈ A ++ m :: (B ++ m :: C), z = m := fun z hz => by
      have := hmin z hz; have := hmax z hz; omega
    by_cases hB : B = []
    · subst hB
      exact nf_no_dup (l := A) (r := C) (x := m) (by simpa using h)
    · refine nf_no_win h hB ?_
      intro z hz
      have := hall z (by simp [hz])
      rw [InR.self_iff]; exact this
  · exact nf_min_unique h hmin hmax hmM hmn

/-- A non-empty normal form contains its minimum exactly once, or its maximum exactly once. -/
theorem nf_count_extreme {n : List ℕ} (h : NF n) (hne : n ≠ []) :
    n.count (minOf n) = 1 ∨ n.count (maxOf n) = 1 := by
  by_cases h1 : n.count (maxOf n) = 1
  · exact Or.inr h1
  · exact Or.inl (nf_count_aux h (fun z hz => minOf_le hz) (fun z hz => le_maxOf hz)
      (minOf_mem hne) (maxOf_mem hne) h1)

theorem decomp_of_count_one {n : List ℕ} {a : ℕ} (h : n.count a = 1) :
    ∃ P Q, n = P ++ a :: Q ∧ a ∉ P ∧ a ∉ Q := by
  obtain ⟨P, Q, e⟩ := List.append_of_mem (List.count_pos_iff.1 (by omega : 0 < n.count a))
  refine ⟨P, Q, e, ?_, ?_⟩
  · intro hP
    have := List.count_pos_iff.2 hP
    rw [e] at h; simp [List.count_append, List.count_cons] at h; omega
  · intro hQ
    have := List.count_pos_iff.2 hQ
    rw [e] at h; simp [List.count_append, List.count_cons] at h; omega

/-- **The extreme lemma**: in a non-empty normal form, the minimum or the maximum occurs exactly
once, so `n = P ++ m :: Q` with `m` strictly below (resp. above) everything else. -/
theorem nf_extreme_decomp {n : List ℕ} (h : NF n) (hne : n ≠ []) :
    (∃ P m Q, n = P ++ m :: Q ∧ (∀ x ∈ P, m < x) ∧ (∀ x ∈ Q, m < x)) ∨
    (∃ P M Q, n = P ++ M :: Q ∧ (∀ x ∈ P, x < M) ∧ (∀ x ∈ Q, x < M)) := by
  rcases nf_count_extreme h hne with h1 | h1
  · left
    obtain ⟨P, Q, e, hP, hQ⟩ := decomp_of_count_one h1
    refine ⟨P, minOf n, Q, e, fun x hx => ?_, fun x hx => ?_⟩
    · have := minOf_le (a := n) (x := x) (by rw [e]; simp [hx])
      have : x ≠ minOf n := fun h => hP (h ▸ hx)
      omega
    · have := minOf_le (a := n) (x := x) (by rw [e]; simp [hx])
      have : x ≠ minOf n := fun h => hQ (h ▸ hx)
      omega
  · right
    obtain ⟨P, Q, e, hP, hQ⟩ := decomp_of_count_one h1
    refine ⟨P, maxOf n, Q, e, fun x hx => ?_, fun x hx => ?_⟩
    · have := le_maxOf (a := n) (x := x) (by rw [e]; simp [hx])
      have : x ≠ maxOf n := fun h => hP (h ▸ hx)
      omega
    · have := le_maxOf (a := n) (x := x) (by rw [e]; simp [hx])
      have : x ≠ maxOf n := fun h => hQ (h ▸ hx)
      omega

/-! ### Lemma 3.3 (ii): the length bound -/

theorem card_Ioc_le (m L : ℕ) : (Finset.Ioc m L).card ≤ L := by
  rw [Nat.card_Ioc]; omega

/-- A normal form over `{0, …, L}` has at most `2 L + 1` entries. -/
theorem nf_length_le {n : List ℕ} {L : ℕ} (h : NF n) (hL : ∀ x ∈ n, x ≤ L) :
    n.length ≤ 2 * L + 1 := by
  by_cases hne : n = []
  · subst hne; simp
  rcases nf_extreme_decomp h hne with ⟨P, m, Q, rfl, hP, hQ⟩ | ⟨P, M, Q, rfl, hP, hQ⟩
  · have h1 : NF (P ++ [m]) := by
      have : P ++ m :: Q = (P ++ [m]) ++ Q := by simp
      rw [this] at h; exact h.append_left
    have h2 : NF (Q.reverse ++ [m]) := by
      have := nf_reverse h.append_right
      simpa using this
    have l1 := spiral_length_le h1 (Or.inr hP) (S := Finset.Ioc m L) (fun x hx => by
      simp only [Finset.mem_Ioc]; exact ⟨hP x hx, hL x (by simp [hx])⟩)
    have l2 := spiral_length_le h2 (Or.inr (fun x hx => hQ x (List.mem_reverse.1 hx)))
      (S := Finset.Ioc m L) (fun x hx => by
        have hx' := List.mem_reverse.1 hx
        simp only [Finset.mem_Ioc]; exact ⟨hQ x hx', hL x (by simp [hx'])⟩)
    have := card_Ioc_le m L
    simp only [List.length_append, List.length_cons, List.length_reverse] at l2 ⊢
    omega
  · have h1 : NF (P ++ [M]) := by
      have : P ++ M :: Q = (P ++ [M]) ++ Q := by simp
      rw [this] at h; exact h.append_left
    have h2 : NF (Q.reverse ++ [M]) := by
      have := nf_reverse h.append_right
      simpa using this
    have hML : M ≤ L := hL M (by simp)
    have l1 := spiral_length_le h1 (Or.inl hP) (S := Finset.range M) (fun x hx => by
      simp only [Finset.mem_range]; exact hP x hx)
    have l2 := spiral_length_le h2 (Or.inl (fun x hx => hQ x (List.mem_reverse.1 hx)))
      (S := Finset.range M) (fun x hx => by
        have hx' := List.mem_reverse.1 hx
        simp only [Finset.mem_range]; exact hQ x hx')
    simp only [Finset.card_range] at l1 l2
    simp only [List.length_append, List.length_cons, List.length_reverse] at l2 ⊢
    omega

/-- **Lemma 3.3 (ii)**: `|τ a| ≤ 2 · max a + 1`. -/
theorem typical_length_le (a : List ℕ) : (typical a).length ≤ 2 * maxOf a + 1 :=
  nf_length_le (nf_typical a) ((typical_upper_iff a _).2 fun x hx => le_maxOf hx)

/-- The bounded form of Lemma 3.3 (ii). -/
theorem typical_length_le' {a : List ℕ} {L : ℕ} (h : ∀ x ∈ a, x ≤ L) :
    (typical a).length ≤ 2 * L + 1 :=
  nf_length_le (nf_typical a) ((typical_upper_iff a L).2 h)

end Lax117284Proofs.Treewidth.Seq
