import Lax117284Proofs.Treewidth.Chars.RealizeWinClaim

/-!
# The new branch of an attach plan (work package C5, part 11)

`branchRT v chain M` (a chain of nested bags ending in the leaf `M ∪ {v}`) versus `pathSubtree v chain M`: profile,
vertices, tops, entries.  `Nest chain M top` says the chain is nested inside `top` and ends above `M`.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- `chain` is a nested sequence of subsets of `top`, ending above `M`. -/
def Nest : List (Finset ℕ) → Finset ℕ → Finset ℕ → Prop
  | [], M, top => M ⊆ top
  | X :: rest, M, top => X ⊆ top ∧ Nest rest M X

theorem nest_of_chain {M : Finset ℕ} : ∀ (chain : List (Finset ℕ)) (top : Finset ℕ),
    chain.IsChain (fun X Y => Y ⊂ X) → (∀ X ∈ chain.head?, X ⊆ top) → M ⊆ chain.getLastD top →
    Nest chain M top := by
  intro chain
  induction chain with
  | nil => intro top _ _ hM; simpa [Nest] using hM
  | cons X rest ih =>
    intro top hc h0 hM
    refine ⟨h0 X rfl, ?_⟩
    rw [List.isChain_cons] at hc
    apply ih X hc.2
    · intro Y hY
      exact (hc.1 Y hY).subset
    · rw [List.getLastD_cons] at hM; exact hM

theorem branchRT_cons (v : ℕ) (X : Finset ℕ) (rest : List (Finset ℕ)) (M : Finset ℕ) :
    branchRT v (X :: rest) M = RT.node X [branchRT v rest M] := by
  simp [branchRT, List.foldr_cons]

theorem branchRT_nil (v : ℕ) (M : Finset ℕ) : branchRT v [] M = RT.node (insert v M) [] := by
  simp [branchRT]

/-- The profile of the new branch is the raw characteristic `pathSubtree`. -/
theorem prof_branch {v : ℕ} {B : Finset ℕ} (hv : v ∉ B) : ∀ (chain : List (Finset ℕ)) (M : Finset ℕ),
    (∀ X ∈ chain, X ⊆ B) → M ⊆ B → RT.prof (insert v B) (branchRT v chain M) = pathSubtree v chain M := by
  intro chain M
  induction chain with
  | nil =>
    intro _ hM
    rw [branchRT_nil, RT.prof_node, pathSubtree_nil]
    have e : insert v M ∩ insert v B = insert v M := by
      apply Finset.inter_eq_left.2
      exact Finset.insert_subset_insert v hM
    rw [e, Finset.card_insert_of_notMem (fun h => hv (hM h))]
    rfl
  | cons X rest ih =>
    intro hX hM
    rw [branchRT_cons, RT.prof_node, pathSubtree_cons]
    have e : X ∩ insert v B = X := Finset.inter_eq_left.2 (fun x hx => Finset.mem_insert_of_mem (hX X List.mem_cons_self hx))
    rw [e]
    simp only [List.map_cons, List.map_nil]
    rw [ih (fun Y hY => hX Y (List.mem_cons_of_mem _ hY)) hM]

theorem verts_pathSubtree_v (v : ℕ) : ∀ (chain : List (Finset ℕ)) (M : Finset ℕ),
    v ∈ CT.verts (pathSubtree v chain M) := by
  intro chain M
  induction chain with
  | nil => simp [pathSubtree_nil, CT.verts_node]
  | cons X rest ih =>
    rw [pathSubtree_cons]
    exact CT.mem_verts.2 (Or.inr ⟨_, List.mem_singleton_self _, ih⟩)

/-- Entries of the branch survive. -/
theorem entry_pathSubtree {v : ℕ} {top : Finset ℕ} (hv : v ∉ top) : ∀ (chain : List (Finset ℕ)) (M : Finset ℕ),
    Nest chain M top → (∀ X ∈ chain, v ∉ X) → M.card + 1 ≤ maxEntry (norm (pathSubtree v chain M)) := by
  intro chain M
  induction chain generalizing top with
  | nil =>
    intro _ _
    rw [pathSubtree_nil]
    have := norm_y_le (σ := insert v M) (y := [M.card + 1]) (K := ([] : List CT)) (Or.inr (by simp)) (e := M.card + 1) (by simp)
    exact this
  | cons X rest ih =>
    intro hN hX
    rw [pathSubtree_cons]
    have hvX : v ∉ X := hX X List.mem_cons_self
    have h1 := ih (top := X) hvX hN.2 (fun Y hY => hX Y (List.mem_cons_of_mem _ hY))
    have h2 := norm_kid_le (σ := X) (y := [X.card]) (K := [pathSubtree v rest M]) (List.mem_singleton_self _)
      (keep_of_mem_verts (verts_pathSubtree_v v rest M) hvX)
    exact h1.trans h2

/-! ## tops -/

theorem tc_branch (v u : ℕ) (hu : u ≠ v) : ∀ (chain : List (Finset ℕ)) (M top : Finset ℕ), Nest chain M top →
    ∀ p : Bool, (u ∈ top → p = true) → tc u (branchRT v chain M) p = 0 := by
  intro chain M
  induction chain with
  | nil =>
    intro top hN p hp
    rw [branchRT_nil, tc_node]
    have : ¬ (u ∈ insert v M ∧ p = false) := by
      rintro ⟨h1, h2⟩
      rcases Finset.mem_insert.1 h1 with rfl | h1
      · exact hu rfl
      · have := hp (hN h1)
        rw [this] at h2; exact absurd h2 (by simp)
    rw [if_neg this]; simp
  | cons X rest ih =>
    intro top hN p hp
    rw [branchRT_cons, tc_node]
    have h1 : ¬ (u ∈ X ∧ p = false) := by
      rintro ⟨h1, h2⟩
      have := hp (hN.1 h1)
      rw [this] at h2; exact absurd h2 (by simp)
    simp only [if_neg h1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_add, add_zero]
    exact ih X hN.2 _ (fun h => by simp [h])

theorem tc_branch_v (v : ℕ) : ∀ (chain : List (Finset ℕ)) (M : Finset ℕ), (∀ X ∈ chain, v ∉ X) → chain ≠ [] →
    ∀ p : Bool, tc v (branchRT v chain M) p = 1 := by
  intro chain M
  induction chain with
  | nil => intro _ h; exact absurd rfl h
  | cons X rest ih =>
    intro hX _ p
    have hvX : v ∉ X := hX X List.mem_cons_self
    rw [branchRT_cons, tc_node]
    have hdec : decide (v ∈ X) = false := by simp [hvX]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hdec]
    rw [if_neg (fun h => hvX h.1), zero_add]
    cases rest with
    | nil =>
      rw [branchRT_nil, tc_node]
      have : v ∈ insert v M := Finset.mem_insert_self _ _
      simp [this]
    | cons Y rest' => exact ih (fun Z hZ => hX Z (List.mem_cons_of_mem _ hZ)) (by simp) false

theorem tc_branch_v_nil (v : ℕ) (M : Finset ℕ) (p : Bool) :
    tc v (branchRT v [] M) p = if p = false then 1 else 0 := by
  rw [branchRT_nil, tc_node]
  simp

/-! ## vertices and bags -/

theorem mem_verts_branch (v : ℕ) : ∀ (chain : List (Finset ℕ)) (M top : Finset ℕ), Nest chain M top →
    ∀ x ∈ (branchRT v chain M).verts, x = v ∨ x ∈ top := by
  intro chain M
  induction chain with
  | nil =>
    intro top hN x hx
    rw [branchRT_nil, RT.verts_node] at hx
    rcases hx with hx | ⟨k, hk, _⟩
    · rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (hN hx)
    · simp at hk
  | cons X rest ih =>
    intro top hN x hx
    rw [branchRT_cons, RT.verts_node] at hx
    rcases hx with hx | ⟨k, hk, hxk⟩
    · exact Or.inr (hN.1 hx)
    · rw [List.mem_singleton] at hk; subst hk
      rcases ih X hN.2 x hxk with h | h
      · exact Or.inl h
      · exact Or.inr (hN.1 h)

theorem mem_bags_branch (v : ℕ) : ∀ (chain : List (Finset ℕ)) (M top : Finset ℕ), Nest chain M top →
    ∀ Y ∈ (branchRT v chain M).bags, v ∈ Y ∨ Y ⊆ top := by
  intro chain M
  induction chain with
  | nil =>
    intro top hN Y hY
    rw [branchRT_nil, RT.bags_node] at hY
    rcases hY with rfl | ⟨k, hk, _⟩
    · exact Or.inl (Finset.mem_insert_self _ _)
    · simp at hk
  | cons X rest ih =>
    intro top hN Y hY
    rw [branchRT_cons, RT.bags_node] at hY
    rcases hY with rfl | ⟨k, hk, hYk⟩
    · exact Or.inr hN.1
    · rw [List.mem_singleton] at hk; subst hk
      rcases ih X hN.2 Y hYk with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans hN.1)

theorem leaf_mem_bags_branch (v : ℕ) : ∀ (chain : List (Finset ℕ)) (M : Finset ℕ),
    insert v M ∈ (branchRT v chain M).bags := by
  intro chain M
  induction chain with
  | nil => rw [branchRT_nil, RT.bags_node]; exact Or.inl rfl
  | cons X rest ih =>
    rw [branchRT_cons, RT.bags_node]
    exact Or.inr ⟨_, List.mem_singleton_self _, ih⟩

end Lax117284Proofs.Treewidth.Chars
