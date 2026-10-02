import Lax117284Proofs.Treewidth.Fun.E4Defs

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E4

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees

section base
variable {Δ' : ℕ → Option Tm} (hΔ : Ext4 Δ') (B : ℕ)
include hΔ

/-- `nth` with a default: out of range it is `0`. -/
theorem nth0_runs (xs : List ℕ) (i : ℕ) (hB : 1 < B) :
    Runs Δ' B fNth [toVal xs, toVal i] (toVal (xs.getD i 0)) (14 * xs.length + 9) := by
  induction xs generalizing i with
  | nil =>
    refine Runs.mk (hΔ.l1 _ _ Δ_nth) ?_
    simp only [List.getD_nil, toVal_nil]
    ev_start
    · ev_run
    · simp
  | cons a xs ih =>
    refine Runs.mk (hΔ.l1 _ _ Δ_nth) ?_
    cases i with
    | zero =>
      simp only [List.getD_cons_zero]
      ev_start
      · ev_run
      · simp
    | succ i =>
      have ih := ih i
      simp only [List.getD_cons_succ]
      ev_start
      · ev_run
      · simp; omega

/-- `adjOfWord x u v` read off the word (cost `≤ 28 |x| + 60`; needs `n² < B` only for the index arithmetic). -/
theorem adjW_runs (x : List ℕ) (u v : ℕ) (hB : 1 < B) (hn : (nOfWord x) ^ 2 < B) :
    Runs Δ' B fAdjW [toVal x, toVal u, toVal v] (toVal (adjOfWord x u v)) (28 * x.length + 60) := by
  have h0 : Runs Δ' B fNth [toVal x, toVal 0] (toVal (nOfWord x)) (14 * x.length + 9) :=
    nth0_runs hΔ B x 0 hB
  by_cases hu : u < nOfWord x
  · by_cases hv : v < nOfWord x
    · have h1 := nth0_runs hΔ B x (1 + u * nOfWord x + v) hB
      have hle : 1 + u * nOfWord x + v ≤ (nOfWord x) ^ 2 := by
        have h2 : u * nOfWord x + nOfWord x ≤ nOfWord x * nOfWord x := by nlinarith
        nlinarith
      have hlt : 1 + u * nOfWord x + v < B := lt_of_le_of_lt hle hn
      have e : toVal (adjOfWord x u v) = Val.nat (if x.getD (1 + u * nOfWord x + v) 0 = 1 then 1 else 0) := by
        simp [adjOfWord, hu, hv]
      rw [e]
      refine Runs.mk (hΔ.e4 _ _ Δ_adjW) ?_
      ev_start
      · ev_run
        all_goals first | omega | simp [hu, hv]
      · omega
    · have e : toVal (adjOfWord x u v) = Val.nat 0 := by simp [adjOfWord, hv]
      rw [e]
      refine Runs.mk (hΔ.e4 _ _ Δ_adjW) ?_
      ev_start
      · ev_run
        all_goals first | omega | simp [hu, hv]
      · omega
  · have e : toVal (adjOfWord x u v) = Val.nat 0 := by simp [adjOfWord, hu]
    rw [e]
    refine Runs.mk (hΔ.e4 _ _ Δ_adjW) ?_
    ev_start
    · ev_run
      all_goals first | omega | simp [hu]
    · omega

theorem nbrPred_runs (x : List ℕ) (v w : ℕ) (hB : 500 < B) (hn : (nOfWord x) ^ 2 < B) :
    Runs Δ' B fNbrPred [toVal (x, v), toVal w] (toVal (adjOfWord x v w)) (28 * x.length + 70) := by
  have h := adjW_runs hΔ B x v w (by omega) hn
  refine Runs.mk (hΔ.e4 _ _ Δ_nbrPred) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

omit hΔ in
theorem toVal_nbrs (x : List ℕ) (v : ℕ) (Bg : Finset ℕ) :
    toVal (nbrs (adjOfWord x) v Bg) = toVal ((Bg.sort (· ≤ ·)).filter (fun w => adjOfWord x v w)) := by
  refine Lib3.toVal_finset_of_sorted ((Lib3.sorted_sort Bg).sublist List.filter_sublist) ?_
  intro a
  simp [nbrs, Finset.mem_filter, List.mem_filter, Finset.mem_sort]

theorem nbrs_runs (x : List ℕ) (v : ℕ) (Bg : Finset ℕ) (hB : 500 < B) (hn : (nOfWord x) ^ 2 < B) :
    Runs Δ' B fNbrs [toVal x, toVal v, toVal Bg] (toVal (nbrs (adjOfWord x) v Bg))
      (Bg.card * (28 * x.length + 120) + 60) := by
  have hf : ∀ w ∈ Bg.sort (· ≤ ·), Runs Δ' B fNbrPred [toVal (x, v), toVal w]
      (toVal (adjOfWord x v w)) (28 * x.length + 70) := fun w _ => nbrPred_runs hΔ B x v w hB hn
  have h := filter_runs hΔ.l1 B fNbrPred (toVal (x, v)) (fun w => adjOfWord x v w) (fun _ => 28 * x.length + 70)
    (Bg.sort (· ≤ ·)) hf
  have hsum : ((Bg.sort (· ≤ ·)).map (fun _ => 28 * x.length + 70)).sum = Bg.card * (28 * x.length + 70) := by
    simp
  rw [hsum, Finset.length_sort] at h
  rw [toVal_nbrs]
  have hl : toVal (Bg.sort (· ≤ ·)) = toVal Bg := rfl
  rw [hl] at h
  have hid : fNbrPred < B := by show 385 < B; omega
  refine Runs.mk (hΔ.e4 _ _ Δ_nbrs) ?_
  ev_start
  · ev_run
  · nlinarith

/-! ### the bag of a nice tree -/

omit hΔ in
theorem bag_card_le_inner : ∀ nt : NT, nt.bag.card ≤ nt.inner
  | .leaf => by simp [NT.bag]
  | .intro v c => by
    have := bag_card_le_inner c
    have h2 := Finset.card_insert_le v c.bag
    simp only [NT.bag, NT.inner]; omega
  | .forget v c => by
    have := bag_card_le_inner c
    have h2 := Finset.card_erase_le (a := v) (s := c.bag)
    simp only [NT.bag, NT.inner]; omega
  | .join a b => by
    have := bag_card_le_inner a
    simp only [NT.bag, NT.inner]; omega

omit hΔ in
theorem bag_card_le_sz (nt : NT) : nt.bag.card ≤ sz nt := by
  have := bag_card_le_inner nt
  rw [sz_nt_eq]; omega

omit hΔ in
theorem bag_subset_mentioned : ∀ nt : NT, nt.bag ⊆ nt.mentioned
  | .leaf => by simp [NT.bag]
  | .intro v c => by
    have := bag_subset_mentioned c
    intro u hu
    simp only [NT.bag, Finset.mem_insert] at hu
    simp only [NT.mentioned, Finset.mem_insert]
    rcases hu with h | h
    · exact Or.inl h
    · exact Or.inr (this h)
  | .forget v c => by
    have := bag_subset_mentioned c
    intro u hu
    simp only [NT.bag, Finset.mem_erase] at hu
    simp only [NT.mentioned, Finset.mem_insert]
    exact Or.inr (this hu.2)
  | .join a b => by
    have := bag_subset_mentioned a
    intro u hu
    simp only [NT.bag] at hu
    simp only [NT.mentioned, Finset.mem_union]
    exact Or.inl (this hu)

theorem ntBag_runs (hB : 500 < B) : ∀ nt : NT,
    Runs Δ' B fNtBag [toVal nt] (toVal nt.bag) (60 * sz nt ^ 2)
  | .leaf => by
    refine Runs.mk (hΔ.e4 _ _ Δ_ntBag) ?_
    simp only [toVal_nt_leaf, NT.bag, toVal_empty_finset, sz_nt_leaf]
    ev_start
    · ev_run
    · omega
  | .intro v c => by
    have ih := ntBag_runs hB c
    have h := Lib3.insert_runs hΔ.l3 B v c.bag
    have hc := bag_card_le_sz c
    have hp := sz_pos c
    have e : NT.bag (NT.intro v c) = insert v c.bag := rfl
    refine Runs.mk (hΔ.e4 _ _ Δ_ntBag) ?_
    rw [e]
    simp only [toVal_nt_intro, sz_nt_intro]
    ev_start
    · ev_run
    · nlinarith
  | .forget v c => by
    have ih := ntBag_runs hB c
    have h := Lib3.erase_runs hΔ.l3 B v c.bag
    have hc := bag_card_le_sz c
    have hp := sz_pos c
    have e : NT.bag (NT.forget v c) = c.bag.erase v := rfl
    refine Runs.mk (hΔ.e4 _ _ Δ_ntBag) ?_
    rw [e]
    simp only [toVal_nt_forget, sz_nt_forget]
    ev_start
    · ev_run
    · nlinarith
  | .join a b => by
    have ih := ntBag_runs hB a
    have hp := sz_pos a
    have hq := sz_pos b
    have e : NT.bag (NT.join a b) = a.bag := rfl
    refine Runs.mk (hΔ.e4 _ _ Δ_ntBag) ?_
    rw [e]
    simp only [toVal_nt_join, sz_nt_join]
    ev_start
    · ev_run
    · nlinarith

end base

end E4
end Lax117284Proofs.Treewidth.Fun
