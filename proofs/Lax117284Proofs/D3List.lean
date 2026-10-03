import Lax117284Proofs.MathlibLite

/-!
The loops over the table, as functions on lists: the in-place sweep that serves a client on a day,
the collapse that keeps the states that served `k` days, and the stores that write the order.
-/

namespace Lax117284Proofs.D3List

open scoped Classical

lemma getD_set_self (A : List ℕ) (i v : ℕ) (h : i < A.length) : (A.set i v).getD i 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]; rfl

lemma getD_set_ne (A : List ℕ) (i j v : ℕ) (h : i ≠ j) : (A.set i v).getD j 0 = A.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, h]

lemma getD_set (A : List ℕ) (i j v : ℕ) (h : i < A.length) :
    (A.set i v).getD j 0 = if i = j then v else A.getD j 0 := by
  by_cases hij : i = j
  · rw [if_pos hij]; subst hij; exact getD_set_self A i v h
  · rw [if_neg hij]; exact getD_set_ne A i j v hij

/-! ### The sweep -/

/-- The step of the sweep at position `x`: when the cell holds a state and has a target, set it. -/
def swStep (f : ℕ → Option ℕ) (x : ℕ) (A : List ℕ) : List ℕ :=
  match f x with
  | none => A
  | some y => if A.getD x 0 = 1 then A.set y 1 else A

/-- The sweep from the last position to the first. -/
def swRun (N : ℕ) (f : ℕ → Option ℕ) (A0 : List ℕ) : List ℕ :=
  (List.range N).foldl (fun A j => swStep f (N - 1 - j) A) A0

/-- **What the sweep does.** -/
theorem swRun_inv (N : ℕ) (f : ℕ → Option ℕ) (A0 : List ℕ)
    (hf : ∀ x < N, A0.getD x 0 = 1 → ∀ y, f x = some y → x < y ∧ y < N)
    (hA : ∀ x < N, A0.getD x 0 ≤ 1)
    (hlen : N ≤ A0.length) :
    ∀ j ≤ N, ((List.range j).foldl (fun A j => swStep f (N - 1 - j) A) A0).length = A0.length ∧
      (∀ y, N ≤ y → ((List.range j).foldl (fun A j => swStep f (N - 1 - j) A) A0).getD y 0 =
        A0.getD y 0) ∧
      ∀ y < N, ((List.range j).foldl (fun A j => swStep f (N - 1 - j) A) A0).getD y 0 =
        if A0.getD y 0 = 1 ∨ ∃ x, N - j ≤ x ∧ x < N ∧ A0.getD x 0 = 1 ∧ f x = some y then 1 else 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨rfl, fun y _ => rfl, fun y hy => ?_⟩
    simp only [List.range_zero, List.foldl_nil]
    have := hA y hy
    have h2 : ¬ ∃ x, N - 0 ≤ x ∧ x < N ∧ A0.getD x 0 = 1 ∧ f x = some y := by
      rintro ⟨x, h1, h2, -⟩; omega
    simp only [h2, or_false]
    split <;> omega
  | succ j ih =>
    intro hj
    obtain ⟨hl, hout, hin⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set R := (List.range j).foldl (fun A j => swStep f (N - 1 - j) A) A0 with hR
    have hx : N - 1 - j < N := by omega
    -- the cell being processed has not been changed
    have hcell : R.getD (N - 1 - j) 0 = A0.getD (N - 1 - j) 0 := by
      rw [hin _ hx]
      have hn : ¬ ∃ x, N - j ≤ x ∧ x < N ∧ A0.getD x 0 = 1 ∧ f x = some (N - 1 - j) := by
        rintro ⟨x, h1, h2, h3, h4⟩
        have := (hf x h2 h3 _ h4).1
        omega
      simp only [hn, or_false]
      have := hA _ hx
      split <;> omega
    refine ⟨?_, ?_, ?_⟩
    · unfold swStep
      split
      · exact hl
      · rename_i y hy
        split
        · rename_i hc
          have h1 : A0.getD (N - 1 - j) 0 = 1 := by rw [← hcell]; exact hc
          have := (hf _ hx h1 y hy).2
          simp [hl]
        · exact hl
    · intro y hy
      unfold swStep
      split
      · exact hout y hy
      · rename_i y' hy'
        split
        · rename_i hc
          have h1 : A0.getD (N - 1 - j) 0 = 1 := by rw [← hcell]; exact hc
          have := (hf _ hx h1 y' hy').2
          rw [getD_set_ne _ _ _ _ (by omega)]
          exact hout y hy
        · exact hout y hy
    · intro y hy
      have hlR : R.length = A0.length := hl
      unfold swStep
      split
      · rename_i hfx
        rw [hin y hy]
        have : (∃ x, N - j ≤ x ∧ x < N ∧ A0.getD x 0 = 1 ∧ f x = some y) ↔
            (∃ x, N - (j + 1) ≤ x ∧ x < N ∧ A0.getD x 0 = 1 ∧ f x = some y) := by
          constructor
          · rintro ⟨x, h1, h2, h3, h4⟩; exact ⟨x, by omega, h2, h3, h4⟩
          · rintro ⟨x, h1, h2, h3, h4⟩
            by_cases hxe : x = N - 1 - j
            · subst hxe; rw [hfx] at h4; exact absurd h4 (by simp)
            · exact ⟨x, by omega, h2, h3, h4⟩
        simp only [this]
      · rename_i y' hy'
        by_cases h1 : A0.getD (N - 1 - j) 0 = 1
        · have hy'N := (hf _ hx h1 y' hy').2
          rw [if_pos (by rw [hcell]; exact h1)]
          rw [getD_set _ _ _ _ (by omega)]
          by_cases hyy : y' = y
          · subst hyy
            simp only [if_true]
            have : (∃ x, N - (j + 1) ≤ x ∧ x < N ∧ A0.getD x 0 = 1 ∧ f x = some y') := ⟨N - 1 - j, by omega, hx, h1, hy'⟩
            rw [if_pos (Or.inr this)]
          · rw [if_neg hyy, hin y hy]
            have : (∃ x, N - j ≤ x ∧ x < N ∧ A0.getD x 0 = 1 ∧ f x = some y) ↔
                (∃ x, N - (j + 1) ≤ x ∧ x < N ∧ A0.getD x 0 = 1 ∧ f x = some y) := by
              constructor
              · rintro ⟨x, h1', h2, h3, h4⟩; exact ⟨x, by omega, h2, h3, h4⟩
              · rintro ⟨x, h1', h2, h3, h4⟩
                by_cases hxe : x = N - 1 - j
                · subst hxe; rw [hy'] at h4; exact absurd (Option.some.inj h4) hyy
                · exact ⟨x, by omega, h2, h3, h4⟩
            simp only [this]
        · rw [if_neg (by rw [hcell]; exact h1), hin y hy]
          have : (∃ x, N - j ≤ x ∧ x < N ∧ A0.getD x 0 = 1 ∧ f x = some y) ↔
              (∃ x, N - (j + 1) ≤ x ∧ x < N ∧ A0.getD x 0 = 1 ∧ f x = some y) := by
            constructor
            · rintro ⟨x, h1', h2, h3, h4⟩; exact ⟨x, by omega, h2, h3, h4⟩
            · rintro ⟨x, h1', h2, h3, h4⟩
              by_cases hxe : x = N - 1 - j
              · subst hxe; exact absurd h3 h1
              · exact ⟨x, by omega, h2, h3, h4⟩
          simp only [this]

/-- **The cells not yet reached are untouched.** -/
theorem swRun_pre (N : ℕ) (f : ℕ → Option ℕ) (A0 : List ℕ)
    (hf : ∀ x < N, A0.getD x 0 = 1 → ∀ y, f x = some y → x < y ∧ y < N)
    (hA : ∀ x < N, A0.getD x 0 ≤ 1) (hlen : N ≤ A0.length) (j : ℕ) (hj : j ≤ N) (y : ℕ)
    (hy : y + j < N) :
    ((List.range j).foldl (fun A j => swStep f (N - 1 - j) A) A0).getD y 0 = A0.getD y 0 := by
  obtain ⟨-, -, hin⟩ := swRun_inv N f A0 hf hA hlen j hj
  rw [hin y (by omega)]
  have hn : ¬ ∃ x, N - j ≤ x ∧ x < N ∧ A0.getD x 0 = 1 ∧ f x = some y := by
    rintro ⟨x, h1, h2, h3, h4⟩
    have := (hf x h2 h3 _ h4).1
    omega
  simp only [hn, or_false]
  have := hA y (by omega)
  split <;> omega

/-! ### The collapse -/

/-- The step of the collapse at position `x`: the states that served `k` days move to the first layer,
the others are dropped. -/
def clStep (P k : ℕ) (x : ℕ) (A : List ℕ) : List ℕ :=
  A.set x (if x < P then A.getD (x + P * k) 0 else 0)

/-- **What the collapse does.** -/
theorem clRun_inv (P k : ℕ) (A0 : List ℕ) (hlen : P * (k + 1) ≤ A0.length) :
    ∀ j ≤ P * (k + 1), ((List.range j).foldl (fun A x => clStep P k x A) A0).length = A0.length ∧
      (∀ x, j ≤ x → ((List.range j).foldl (fun A x => clStep P k x A) A0).getD x 0 =
        A0.getD x 0) ∧
      ∀ x < j, ((List.range j).foldl (fun A x => clStep P k x A) A0).getD x 0 =
        if x < P then A0.getD (x + P * k) 0 else 0 := by
  intro j
  induction j with
  | zero => intro _; exact ⟨rfl, fun _ _ => rfl, fun x hx => absurd hx (by omega)⟩
  | succ j ih =>
    intro hj
    obtain ⟨hl, hout, hin⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set R := (List.range j).foldl (fun A x => clStep P k x A) A0 with hR
    have hread : R.getD (j + P * k) 0 = A0.getD (j + P * k) 0 := hout _ (by omega)
    have hjl : j < R.length := by rw [hl]; omega
    refine ⟨?_, ?_, ?_⟩
    · unfold clStep; simp [hl]
    · intro x hx
      unfold clStep
      rw [getD_set_ne _ _ _ _ (by omega)]
      exact hout x (by omega)
    · intro x hx
      unfold clStep
      rw [getD_set _ _ _ _ hjl]
      by_cases hxj : j = x
      · subst hxj
        simp only [if_true]
        split
        · rw [hread]
        · rfl
      · rw [if_neg hxj, hin x (by omega)]

/-! ### Stores in order -/

/-- Store `val j` at `idx j` for every `j` below `N`. -/
def stFold (N : ℕ) (idx val : ℕ → ℕ) (A0 : List ℕ) : List ℕ :=
  (List.range N).foldl (fun A j => A.set (idx j) (val j)) A0

theorem stFold_inv (idx val : ℕ → ℕ) (A0 : List ℕ) (N : ℕ)
    (hinj : ∀ a b, a < N → b < N → idx a = idx b → a = b) (hlt : ∀ j < N, idx j < A0.length) :
    ∀ j ≤ N, (stFold j idx val A0).length = A0.length ∧
      (∀ a < j, (stFold j idx val A0).getD (idx a) 0 = val a) ∧
      ∀ y, (∀ a < j, idx a ≠ y) → (stFold j idx val A0).getD y 0 = A0.getD y 0 := by
  intro j
  induction j with
  | zero => intro _; exact ⟨rfl, fun a ha => absurd ha (by omega), fun _ _ => rfl⟩
  | succ j ih =>
    intro hj
    obtain ⟨hl, hin, hout⟩ := ih (by omega)
    unfold stFold at *
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set R := (List.range j).foldl (fun A j => A.set (idx j) (val j)) A0 with hR
    have hjl : idx j < R.length := by rw [hl]; exact hlt j (by omega)
    refine ⟨by simp [hl], fun a ha => ?_, fun y hy => ?_⟩
    · rw [getD_set _ _ _ _ hjl]
      by_cases haj : idx j = idx a
      · rw [if_pos haj]
        have := hinj j a (by omega) (by omega) haj
        rw [this]
      · rw [if_neg haj]
        have hne : a ≠ j := fun h => haj (by rw [h])
        exact hin a (by omega)
    · rw [getD_set _ _ _ _ hjl, if_neg (hy j (by omega))]
      exact hout y (fun a ha => hy a (by omega))

end Lax117284Proofs.D3List
