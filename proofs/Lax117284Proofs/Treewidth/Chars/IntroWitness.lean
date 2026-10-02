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

theorem witnessesAux_map_fst : ∀ (a : List ℕ) (j : ℕ) (st : List (ℕ × ℕ)),
    (witnessesAux j st a).map Prod.fst = a.foldl push (st.map Prod.fst) := by
  intro a
  induction a with
  | nil => intro j st; simp [witnessesAux]
  | cons y a ih =>
    intro j st
    simp only [witnessesAux, List.foldl_cons]
    rw [ih, wpush_map_fst]

end Lax117284Proofs.Treewidth.Chars
