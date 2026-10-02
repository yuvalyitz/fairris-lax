import Lax117284Proofs.Treewidth.Chars.Alg

/-!
# The witnesses of a typical sequence (work package C4, part 2)

`witnesses a` (`Chars/Alg.lean`) runs the stack algorithm of `Seq.push` on pairs `(value, index)`.
`witnesses_spec`: the indices are strictly increasing, in range, and read off exactly `typical a`.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

/-- The values of `wpush` are `push` of the values. -/
theorem wpush_map_fst : ∀ (st : List (ℕ × ℕ)) (y j : ℕ),
    (wpush st y j).map Prod.fst = push (st.map Prod.fst) y := by
  intro st y j
  induction st with
  | nil => simp [wpush, push, cut]
  | cons p t ih =>
    obtain ⟨x, i⟩ := p
    simp only [wpush, List.map_cons, push, cut]
    by_cases h : t.all (fun z => decide (InR z.1 x y)) = true
    · have h' : ∀ z ∈ t.map Prod.fst, InR z x y := by
        intro z hz
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
        have := List.all_eq_true.1 h p hp
        simpa using this
      rw [h, if_pos h']
      by_cases hte : t = [] ∧ x = y
      · obtain ⟨rfl, rfl⟩ := hte
        simp
      · have h2 : ¬ (t.isEmpty = true ∧ decide (x = y) = true) := by
          intro hh
          apply hte
          exact ⟨List.isEmpty_iff.1 hh.1, by simpa using hh.2⟩
        have h3 : ¬ (t.map Prod.fst = [] ∧ x = y) := by
          intro hh; apply hte
          exact ⟨by simpa using hh.1, hh.2⟩
        rw [if_neg h3]
        simp only [Bool.and_eq_true] at *
        rw [if_neg h2]
        simp
    · have h' : ¬ ∀ z ∈ t.map Prod.fst, InR z x y := by
        intro hh
        apply h
        rw [List.all_eq_true]
        intro p hp
        simpa using hh p.1 (List.mem_map.2 ⟨p, hp, rfl⟩)
      rw [if_neg h', if_neg (by simpa using h)]
      have := ih
      simp only [push] at this
      simp [this]

/-- Every pair of `wpush` is an old pair or the new one. -/
theorem mem_wpush : ∀ (st : List (ℕ × ℕ)) (y j : ℕ), ∀ p ∈ wpush st y j, p ∈ st ∨ p = (y, j) := by
  intro st y j
  induction st with
  | nil => intro p hp; simp [wpush] at hp; exact Or.inr hp
  | cons q t ih =>
    obtain ⟨x, i⟩ := q
    intro p hp
    simp only [wpush] at hp
    split_ifs at hp with h1 h2
    · simp at hp; exact Or.inl (by simp [hp])
    · simp at hp
      rcases hp with rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr rfl
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact Or.inl (by simp)
      · rcases ih p hp with h | h
        · exact Or.inl (by simp [h])
        · exact Or.inr h

/-- Indices stay strictly increasing and below `j + 1`. -/
theorem wpush_indices : ∀ (st : List (ℕ × ℕ)) (y j : ℕ), (st.map Prod.snd).Pairwise (· < ·) →
    (∀ p ∈ st, p.2 < j) →
    ((wpush st y j).map Prod.snd).Pairwise (· < ·) := by
  intro st y j
  induction st with
  | nil => intro _ _; simp [wpush]
  | cons q t ih =>
    obtain ⟨x, i⟩ := q
    intro hpw hlt
    simp only [wpush]
    have hi : i < j := hlt (x, i) (by simp)
    have hpw' := List.pairwise_cons.1 hpw
    split_ifs with h1 h2
    · simp
    · simp [hi]
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨?_, ih hpw'.2 (fun p hp => hlt p (by simp [hp]))⟩
      intro b hb
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
      rcases mem_wpush t y j p hp with h | h
      · exact hpw'.1 p.2 (List.mem_map.2 ⟨p, h, rfl⟩)
      · rw [h]; exact hi

theorem wpush_lt : ∀ (st : List (ℕ × ℕ)) (y j : ℕ), (∀ p ∈ st, p.2 < j) → ∀ p ∈ wpush st y j, p.2 < j + 1 := by
  intro st y j h p hp
  rcases mem_wpush st y j p hp with h' | rfl
  · exact Nat.lt_succ_of_lt (h p h')
  · exact Nat.lt_succ_self _

theorem witnessesAux_map_fst : ∀ (a : List ℕ) (j : ℕ) (st : List (ℕ × ℕ)),
    (witnessesAux j st a).map Prod.fst = a.foldl push (st.map Prod.fst) := by
  intro a
  induction a with
  | nil => intro j st; simp [witnessesAux]
  | cons y a ih =>
    intro j st
    simp only [witnessesAux, List.foldl_cons]
    rw [ih, wpush_map_fst]

theorem witnessesAux_inv : ∀ (a pre : List ℕ) (st : List (ℕ × ℕ)),
    (∀ p ∈ st, p.2 < pre.length ∧ pre.getD p.2 0 = p.1) → (st.map Prod.snd).Pairwise (· < ·) →
    (∀ p ∈ witnessesAux pre.length st a, p.2 < (pre ++ a).length ∧ (pre ++ a).getD p.2 0 = p.1) ∧
      ((witnessesAux pre.length st a).map Prod.snd).Pairwise (· < ·) := by
  intro a
  induction a with
  | nil =>
    intro pre st h1 h2
    simp only [witnessesAux, List.append_nil]
    exact ⟨h1, h2⟩
  | cons y a ih =>
    intro pre st h1 h2
    have hlt : ∀ p ∈ st, p.2 < pre.length := fun p hp => (h1 p hp).1
    have := ih (pre ++ [y]) (wpush st y pre.length) ?_ (wpush_indices st y pre.length h2 hlt)
    · simp only [witnessesAux]
      have hh := this
      have e1 : (pre ++ [y] ++ a) = pre ++ y :: a := by simp
      have e2 : (pre ++ [y]).length = pre.length + 1 := by simp
      rw [e2, e1] at hh
      exact hh
    · intro p hp
      rcases mem_wpush st y pre.length p hp with h | rfl
      · have hp2 := (h1 p h).1
        refine ⟨by simp; omega, ?_⟩
        have := h1 p h
        rw [List.getD_eq_getElem?_getD] at this ⊢
        rw [List.getElem?_append_left this.1]; exact this.2
      · simp [List.getD_eq_getElem?_getD]

/-- **The witnesses of a typical sequence**: increasing indices into `a` that read off `typical a`. -/
theorem witnesses_spec (a : List ℕ) :
    (witnesses a).map (fun i => a.getD i 0) = typical a ∧ (witnesses a).Pairwise (· < ·) ∧
      ∀ i ∈ witnesses a, i < a.length := by
  have h := witnessesAux_inv a [] [] (by simp) (by simp)
  simp only [List.length_nil, List.nil_append] at h
  refine ⟨?_, h.2, ?_⟩
  · unfold witnesses
    have hv : ∀ p ∈ witnessesAux 0 [] a, a.getD p.2 0 = p.1 := fun p hp => (h.1 p hp).2
    have := witnessesAux_map_fst a 0 []
    simp only [List.map_nil] at this
    rw [List.map_map]
    calc (witnessesAux 0 [] a).map (fun p => a.getD p.2 0)
        = (witnessesAux 0 [] a).map Prod.fst := List.map_congr_left hv
      _ = typical a := this
  · intro i hi
    unfold witnesses at hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
    exact (h.1 p hp).1

end Lax117284Proofs.Treewidth.Chars
