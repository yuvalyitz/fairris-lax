import Lax117284Proofs.Treewidth.Chars.RealizeWinClaim
import Lax117284Proofs.Treewidth.Chars.IntroMono
import Lax117284Proofs.Treewidth.Chars.MergeFinal
import Lax117284Proofs.Treewidth.Chars.Forget
import Lax117284Proofs.Treewidth.Chars.TablesComplete
import Lax117284Proofs.Treewidth.Chars.Join
import Lax117284Proofs.Treewidth.Chars.Leaf
import Lax117284Proofs.Treewidth.Wrap.Decompose

/-! ### `Lax117284Proofs.Treewidth.Chars.RealizeBranch` -/

section
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

end

/-! ### `Lax117284Proofs.Treewidth.Chars.RealizeAttChain` -/

section
/-!
# Attaching the branch to a chain (work package C5, part 12)

Lemmas about `addJunk` and the topology `TI` of a chain with an attached branch.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem addJunk_nil (x : ℕ) (br : RT) : addJunk x br [] = [] := by rfl

theorem addJunk_cons_zero (br : RT) (n : CNode) (r : List CNode) :
    addJunk 0 br (n :: r) = ⟨n.bag, n.junk ++ [br]⟩ :: r := by
  unfold addJunk
  rw [List.mapIdx_cons, if_pos rfl]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_mapIdx]

theorem addJunk_cons_succ (x : ℕ) (br : RT) (n : CNode) (r : List CNode) :
    addJunk (x + 1) br (n :: r) = n :: addJunk x br r := by
  unfold addJunk
  rw [List.mapIdx_cons, if_neg (by omega)]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_mapIdx]

theorem length_addJunk (x : ℕ) (br : RT) (ns : List CNode) : (addJunk x br ns).length = ns.length := by
  unfold addJunk; simp

theorem addJunk_append_left (br : RT) : ∀ (L R : List CNode) (i : ℕ), i < L.length →
    addJunk i br (L ++ R) = addJunk i br L ++ R := by
  intro L
  induction L with
  | nil => intro R i h; simp at h
  | cons n r ih =>
    intro R i h
    cases i with
    | zero => simp [addJunk_cons_zero]
    | succ j =>
      simp only [List.cons_append, addJunk_cons_succ]
      rw [ih R j (by simpa using h)]

theorem chainToRT_addJunk_last (br : RT) : ∀ (c : List CNode) (K : List RT), c ≠ [] →
    AR.chainToRT (addJunk (c.length - 1) br c) K = AR.chainToRT c (br :: K) := by
  intro c
  induction c with
  | nil => intro K h; exact absurd rfl h
  | cons n r ih =>
    intro K _
    cases r with
    | nil =>
      simp only [List.length_singleton, Nat.sub_self]
      rw [addJunk_cons_zero, chainToRT_single, chainToRT_single]
      simp
    | cons m r' =>
      have hl : (n :: m :: r').length - 1 = (m :: r').length - 1 + 1 := by simp
      rw [hl, addJunk_cons_succ]
      have hne : addJunk ((m :: r').length - 1) br (m :: r') ≠ [] := by
        intro h
        have := congrArg List.length h
        rw [length_addJunk] at this; simp at this
      rw [chainToRT_cons_of_ne _ hne, chainToRT_cons_of_ne _ (by simp), ih K (by simp)]

/-- Nodes of the chain with a branch attached. -/
theorem mem_addJunk (br : RT) : ∀ (ns : List CNode) (x : ℕ) (y : CNode), y ∈ addJunk x br ns →
    y ∈ ns ∨ ∃ n ∈ ns, y = ⟨n.bag, n.junk ++ [br]⟩ := by
  intro ns
  induction ns with
  | nil => intro x y h; simp [addJunk_nil] at h
  | cons n r ih =>
    intro x y h
    cases x with
    | zero =>
      rw [addJunk_cons_zero] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr ⟨n, List.mem_cons_self, rfl⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)
    | succ j =>
      rw [addJunk_cons_succ] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl List.mem_cons_self
      · rcases ih j y h with h1 | ⟨n', hn', rfl⟩
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr ⟨n', List.mem_cons_of_mem _ hn', rfl⟩

theorem mem_addJunk_conv (br : RT) : ∀ (ns : List CNode) (x : ℕ) (n : CNode), n ∈ ns →
    n ∈ addJunk x br ns ∨ (⟨n.bag, n.junk ++ [br]⟩ : CNode) ∈ addJunk x br ns := by
  intro ns
  induction ns with
  | nil => intro x n h; simp at h
  | cons m r ih =>
    intro x n h
    cases x with
    | zero =>
      rw [addJunk_cons_zero]
      rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr List.mem_cons_self
      · exact Or.inl (List.mem_cons_of_mem _ h)
    | succ j =>
      rw [addJunk_cons_succ]
      rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl List.mem_cons_self
      · rcases ih j n h with h1 | h1
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr (List.mem_cons_of_mem _ h1)

theorem br_mem_addJunk (br : RT) : ∀ (ns : List CNode) (x : ℕ) (hx : x < ns.length),
    ∃ y ∈ addJunk x br ns, br ∈ y.junk ∧ ∃ n ∈ ns, y.bag = n.bag ∧ n = ns[x]'hx := by
  intro ns
  induction ns with
  | nil => intro x h; simp at h
  | cons n r ih =>
    intro x h
    cases x with
    | zero =>
      rw [addJunk_cons_zero]
      exact ⟨_, List.mem_cons_self, by simp, n, List.mem_cons_self, rfl, rfl⟩
    | succ j =>
      rw [addJunk_cons_succ]
      obtain ⟨y, hy, h1, n', hn', h2, h3⟩ := ih j (by simpa using h)
      exact ⟨y, List.mem_cons_of_mem _ hy, h1, n', List.mem_cons_of_mem _ hn', h2, by simpa using h3⟩

theorem tc_addJunk (u : ℕ) (br : RT) : ∀ (ns : List CNode) (i : ℕ) (K : List RT) (p : Bool) (h : i < ns.length),
    tc u (AR.chainToRT (addJunk i br ns) K) p =
      tc u (AR.chainToRT ns K) p + tc u br (decide (u ∈ (ns[i]'h).bag)) := by
  intro ns
  induction ns with
  | nil => intro i K p h; simp at h
  | cons n r ih =>
    intro i K p h
    cases i with
    | zero =>
      rw [addJunk_cons_zero]
      cases r with
      | nil =>
        simp only [List.getElem_cons_zero]
        rw [chainToRT_single, chainToRT_single, tc_node, tc_node]
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
      | cons m r' =>
        simp only [List.getElem_cons_zero]
        rw [chainToRT_cons_of_ne (⟨n.bag, n.junk ++ [br]⟩ : CNode) (l := m :: r') (by simp) K,
          chainToRT_cons_of_ne n (l := m :: r') (by simp) K, tc_node, tc_node]
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
    | succ j =>
      rw [addJunk_cons_succ]
      have hj : j < r.length := by simpa using h
      cases r with
      | nil => simp at hj
      | cons m r' =>
        have hne : addJunk j br (m :: r') ≠ [] := by
          intro hh
          have := congrArg List.length hh
          rw [length_addJunk] at this; simp at this
        rw [chainToRT_cons_of_ne n hne K, chainToRT_cons_of_ne n (l := m :: r') (by simp) K, tc_node, tc_node]
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        have := ih j K (decide (u ∈ n.bag)) hj
        simp only [List.getElem_cons_succ]
        omega


theorem nest_sub : ∀ {chain : List (Finset ℕ)} {M top : Finset ℕ}, Nest chain M top →
    (∀ X ∈ chain, X ⊆ top) ∧ M ⊆ top := by
  intro chain
  induction chain with
  | nil => intro M top h; exact ⟨fun X hX => by simp at hX, h⟩
  | cons X rest ih =>
    intro M top h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := ih h2
    refine ⟨fun Y hY => ?_, ih2.trans h1⟩
    rcases List.mem_cons.1 hY with rfl | hY
    · exact h1
    · exact (ih1 Y hY).trans h1

theorem chain_att_TI (v : ℕ) {ns ns2 : List CNode} {K K' : List RT} {i : ℕ} {chain : List (Finset ℕ)}
    {M S : Finset ℕ} (hns : ns ≠ []) (hdup : DupOf ns ns2) (hi : i < ns2.length)
    (hfree : ∀ n ∈ ns, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts)
    (hS : S ⊆ (ns2[i]'hi).bag) (hN : Nest chain M S) (hvS : v ∉ S)
    (hK : List.Forall₂ (TI v) K K') (hKz : tcL v K' false = 0) :
    TI v (AR.chainToRT ns K) (AR.chainToRT (addJunk i (branchRT v chain M) ns2) K') ∧
    ∀ p, tc v (AR.chainToRT (addJunk i (branchRT v chain M) ns2) K') p = 1 := by
  set br := branchRT v chain M with hbr
  have hinfo := hdup.info
  have hsub := hdup.sub
  have hne'' : addJunk i br ns2 ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [length_addJunk] at this
    have h0 : ns2.length = 0 := by simpa using this
    omega
  have hns2 : ns2 ≠ [] := by intro h; rw [h] at hi; simp at hi
  have hb := mem_bags_chainToRT K ns hns
  have hb' := mem_bags_chainToRT K' _ hne''
  obtain ⟨ni, hni, hnib, hnij⟩ := hinfo (ns2[i]'hi) (List.getElem_mem hi)
  have hSni : S ⊆ ni.bag := by rw [← hnib]; exact hS
  have hbagn : ∀ y ∈ addJunk i br ns2, ∃ n0 ∈ ns, y.bag = n0.bag := by
    intro y hy
    rcases mem_addJunk br ns2 i y hy with h | ⟨n, hn, rfl⟩
    · obtain ⟨n0, hn0, hb0, -⟩ := hinfo y h
      exact ⟨n0, hn0, hb0⟩
    · obtain ⟨n0, hn0, hb0, -⟩ := hinfo n hn
      exact ⟨n0, hn0, hb0⟩
  have hjunk : ∀ y ∈ addJunk i br ns2, ∀ J ∈ y.junk, J = br ∨ ∃ n0 ∈ ns, J ∈ n0.junk := by
    intro y hy J hJ
    rcases mem_addJunk br ns2 i y hy with h | ⟨n, hn, rfl⟩
    · obtain ⟨n0, hn0, -, hj0⟩ := hinfo y h
      exact Or.inr ⟨n0, hn0, hj0 J hJ⟩
    · obtain ⟨n0, hn0, -, hj0⟩ := hinfo n hn
      rcases List.mem_append.1 hJ with hJ | hJ
      · exact Or.inr ⟨n0, hn0, hj0 J hJ⟩
      · exact Or.inl (List.mem_singleton.1 hJ)
  have hbrv : ∀ x ∈ br.verts, x = v ∨ x ∈ S := mem_verts_branch v chain M S hN
  have hbrb : ∀ Y ∈ br.bags, v ∈ Y ∨ Y ⊆ S := mem_bags_branch v chain M S hN
  have hSold : ∀ x ∈ S, x ∈ (AR.chainToRT ns K).verts := fun x hx =>
    (mem_verts_chainToRT K ns x).2 (Or.inl ⟨ni, hni, hSni hx⟩)
  have hfree2 : ∀ n ∈ ns2, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts := by
    intro n hn
    obtain ⟨n0, hn0, hbg, hj⟩ := hinfo n hn
    obtain ⟨h1, h2⟩ := hfree n0 hn0
    exact ⟨by rw [hbg]; exact h1, fun J hJ => h2 J (hj J hJ)⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- vsub
    intro x hx
    rw [mem_verts_chainToRT] at hx
    rcases hx with ⟨y, hy, hxy⟩ | ⟨y, hy, J, hJ, hxJ⟩ | ⟨k', hk', hxk⟩
    · obtain ⟨n0, hn0, hb0⟩ := hbagn y hy
      exact Or.inl ((mem_verts_chainToRT K ns x).2 (Or.inl ⟨n0, hn0, by rw [← hb0]; exact hxy⟩))
    · rcases hjunk y hy J hJ with rfl | ⟨n0, hn0, hJ0⟩
      · rcases hbrv x hxJ with h | h
        · exact Or.inr h
        · exact Or.inl (hSold x h)
      · exact Or.inl ((mem_verts_chainToRT K ns x).2 (Or.inr (Or.inl ⟨n0, hn0, J, hJ0, hxJ⟩)))
    · obtain ⟨k, hk, hkk⟩ := forall2_exists_right hK k' hk'
      rcases hkk.vsub x hxk with h | h
      · exact Or.inl ((mem_verts_chainToRT K ns x).2 (Or.inr (Or.inr ⟨k, hk, h⟩)))
      · exact Or.inr h
  · -- vsup
    intro x hx
    rw [mem_verts_chainToRT] at hx ⊢
    rcases hx with ⟨y, hy, hxy⟩ | ⟨y, hy, J, hJ, hxJ⟩ | ⟨k, hk, hxk⟩
    · rcases mem_addJunk_conv br ns2 i y (hsub y hy) with h | h
      · exact Or.inl ⟨y, h, hxy⟩
      · exact Or.inl ⟨_, h, hxy⟩
    · rcases mem_addJunk_conv br ns2 i y (hsub y hy) with h | h
      · exact Or.inr (Or.inl ⟨y, h, J, hJ, hxJ⟩)
      · exact Or.inr (Or.inl ⟨_, h, J, List.mem_append_left _ hJ, hxJ⟩)
    · obtain ⟨k', hk', hkk⟩ := forall2_exists_left hK k hk
      exact Or.inr (Or.inr ⟨k', hk', hkk.vsup x hxk⟩)
  · -- bnew
    intro Y hY
    rcases (hb' Y).1 hY with ⟨y, hy, hYy⟩ | ⟨y, hy, J, hJ, hYJ⟩ | ⟨k', hk', hYk⟩
    · obtain ⟨n0, hn0, hb0⟩ := hbagn y hy
      exact Or.inr ⟨n0.bag, (hb _).2 (Or.inl ⟨n0, hn0, rfl⟩), by rw [hYy, hb0]⟩
    · rcases hjunk y hy J hJ with rfl | ⟨n0, hn0, hJ0⟩
      · rcases hbrb Y hYJ with h | h
        · exact Or.inl h
        · exact Or.inr ⟨ni.bag, (hb _).2 (Or.inl ⟨ni, hni, rfl⟩), h.trans hSni⟩
      · exact Or.inr ⟨Y, (hb Y).2 (Or.inr (Or.inl ⟨n0, hn0, J, hJ0, hYJ⟩)), subset_rfl⟩
    · obtain ⟨k, hk, hkk⟩ := forall2_exists_right hK k' hk'
      rcases hkk.bnew Y hYk with h | ⟨X, hX, hYX⟩
      · exact Or.inl h
      · exact Or.inr ⟨X, (hb X).2 (Or.inr (Or.inr ⟨k, hk, hX⟩)), hYX⟩
  · -- bsup
    intro X hX
    rcases (hb X).1 hX with ⟨y, hy, hXy⟩ | ⟨y, hy, J, hJ, hXJ⟩ | ⟨k, hk, hXk⟩
    · rcases mem_addJunk_conv br ns2 i y (hsub y hy) with h | h
      · exact ⟨X, (hb' X).2 (Or.inl ⟨y, h, hXy⟩), subset_rfl⟩
      · exact ⟨X, (hb' X).2 (Or.inl ⟨_, h, hXy⟩), subset_rfl⟩
    · rcases mem_addJunk_conv br ns2 i y (hsub y hy) with h | h
      · exact ⟨X, (hb' X).2 (Or.inr (Or.inl ⟨y, h, J, hJ, hXJ⟩)), subset_rfl⟩
      · exact ⟨X, (hb' X).2 (Or.inr (Or.inl ⟨_, h, J, List.mem_append_left _ hJ, hXJ⟩)), subset_rfl⟩
    · obtain ⟨k', hk', hkk⟩ := forall2_exists_left hK k hk
      obtain ⟨Y, hY, hXY⟩ := hkk.bsup X hXk
      exact ⟨Y, (hb' Y).2 (Or.inr (Or.inr ⟨k', hk', hY⟩)), hXY⟩
  · -- tcne
    intro u hu p
    rw [tc_addJunk u br ns2 i K' p hi]
    have h0 : tc u br (decide (u ∈ (ns2[i]'hi).bag)) = 0 :=
      tc_branch v u hu chain M S hN _ (fun h => by simp [hS h])
    rw [h0, add_zero, tc_chain_dupOf u hdup]
    exact tc_chain_kids u ns K K' hns (tcL_of_forall2 hK hu) p
  · -- tcv
    intro p
    rw [tc_addJunk v br ns2 i K' p hi, tc_chain_prefix_free v ns2 K' p hns2 hfree2, hKz, zero_add]
    have hdec : decide (v ∈ (ns2[i]'hi).bag) = false := by simp [(hfree2 _ (List.getElem_mem hi)).1]
    rw [hdec]
    by_cases hc : chain = []
    · subst hc
      rw [tc_branch_v_nil]; simp
    · exact tc_branch_v v chain M (fun X hX hvX => hvS ((nest_sub hN).1 X hX hvX)) hc false

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.RealizeAtt` -/

section
/-!
# The attach step realises `attachPlans` (work package C5, part 13)
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- Moving the new branch from the front to the back does not change the normal form (its key is fresh). -/
theorem norm_att_swap {S : Finset ℕ} {y : List ℕ} {ka : List CT} {b : CT} (hk : KidsConn S ka)
    (hb : keep S (norm b) = true) (hbk : ∀ z ∈ ka, key S z ≠ key S b) :
    norm (CT.node S y (b :: ka)) = norm (CT.node S y (ka ++ [b])) := by
  rw [norm_node', norm_node']
  simp only [List.map_cons, List.map_append, List.map_nil, List.filter_append]
  rw [List.filter_cons_of_pos hb]
  have hb2 : [norm b].filter (keep S) = [norm b] := by simp [hb]
  rw [hb2]
  apply normF_perm
  · exact List.perm_append_singleton _ _ |>.symm
  · rw [List.pairwise_append]
    refine ⟨survivors_keys_distinct hk, List.pairwise_singleton _ _, ?_⟩
    intro z hz b' hb'
    rw [List.mem_singleton] at hb'
    subst hb'
    obtain ⟨hz0, hz1⟩ := List.mem_filter.1 hz
    obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hz0
    rw [key_norm, key_norm]
    exact hbk k hk'

theorem verts_pathSubtree_sub (v : ℕ) : ∀ (chain : List (Finset ℕ)) (M top : Finset ℕ), Nest chain M top →
    ∀ x ∈ CT.verts (pathSubtree v chain M), x = v ∨ x ∈ top := by
  intro chain M
  induction chain with
  | nil =>
    intro top hN x hx
    rw [pathSubtree_nil, CT.verts_node] at hx
    rcases Finset.mem_union.1 hx with hx | hx
    · rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (hN hx)
    · simp [CT.vertsL] at hx
  | cons X rest ih =>
    intro top hN x hx
    rw [pathSubtree_cons, CT.verts_node] at hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Or.inr (hN.1 hx)
    · obtain ⟨k, hk, hxk⟩ := CT.mem_vertsL.1 hx
      rw [List.mem_singleton] at hk; subst hk
      rcases ih X hN.2 x hxk with h | h
      · exact Or.inl h
      · exact Or.inr (hN.1 h)

theorem key_pathSubtree {v : ℕ} {S : Finset ℕ} (hvS : v ∉ S) {chain : List (Finset ℕ)} {M : Finset ℕ}
    (hN : Nest chain M S) : key S (pathSubtree v chain M) = (v : WithTop ℕ) := by
  have : CT.verts (pathSubtree v chain M) \ S = {v} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      rcases verts_pathSubtree_sub v chain M S hN x h1 with h | h
      · exact h
      · exact absurd h h2
    · rintro rfl
      exact ⟨verts_pathSubtree_v x chain M, hvS⟩
  unfold key
  rw [this]
  simp


theorem mem_bags_branch_v {v : ℕ} {S : Finset ℕ} (hvS : v ∉ S) : ∀ (chain : List (Finset ℕ)) (M : Finset ℕ),
    Nest chain M S → ∀ Y ∈ (branchRT v chain M).bags, v ∈ Y → Y = insert v M := by
  intro chain M
  induction chain generalizing S with
  | nil =>
    intro hN Y hY hvY
    rw [branchRT_nil, RT.bags_node] at hY
    rcases hY with rfl | ⟨k, hk, _⟩
    · rfl
    · simp at hk
  | cons X rest ih =>
    intro hN Y hY hvY
    rw [branchRT_cons, RT.bags_node] at hY
    rcases hY with rfl | ⟨k, hk, hYk⟩
    · exact absurd (hN.1 hvY) hvS
    · rw [List.mem_singleton] at hk; subst hk
      exact ih (fun h => hvS (hN.1 h)) hN.2 Y hYk hvY

/-- The generic normal-form step of a chain (as inside `region_norm`). -/
theorem chain_step (v : ℕ) (B : Finset ℕ) (C : List CNode) (ℓ : Finset ℕ) (K : List RT) (KQ' : List CT)
    (hC : C ≠ []) (hok : ∀ n ∈ C, n.bag ∩ insert v B = ℓ ∧
      ∀ J ∈ n.junk, keep ℓ (norm (RT.prof (insert v B) J)) = false)
    (hK : KQ'.map norm = (K.map (RT.prof (insert v B))).map norm) :
    norm (RT.prof (insert v B) (AR.chainToRT C K)) = norm (CT.node ℓ (typical (csz C)) KQ') := by
  rw [chain_norm (insert v B) ℓ C K hC hok, norm_node', hK]

theorem csz_exists_two {ns : List CNode} {A Bb : List ℕ} (h : csz ns = A ++ Bb) :
    ∃ L R, ns = L ++ R ∧ csz L = A ∧ csz R = Bb := by
  unfold csz at h
  obtain ⟨L, R, rfl, hL, hR⟩ := List.map_eq_append_iff.1 h
  exact ⟨L, R, rfl, hL, hR⟩

/-- What the realisation of a plan achieves at the run of the plan. -/
structure IRC (v : ℕ) (B : Finset ℕ) (x x' : AR) (r : CT) (N : Finset ℕ) : Prop where
  ti : TI v (AR.toRT x) (AR.toRT x')
  tcv : tc v (AR.toRT x') false = 1
  vin : v ∈ (AR.toRT x').verts
  cov : ∀ u ∈ N, ∃ Y ∈ (AR.toRT x').bags, v ∈ Y ∧ u ∈ Y
  chr : ∃ Q, norm (RT.prof (insert v B) (AR.toRT x')) = norm Q ∧ DomC Q r
  wid : ∀ Y ∈ (AR.toRT x').bags, v ∈ Y → Y.card ≤ maxEntry (norm r)
  vrep : v ∈ CT.verts r


theorem att_topo (v : ℕ) (B S : Finset ℕ) (ns : List CNode) (ks : List AR) (hvB : v ∉ B)
    (hx : RunOk v B (.run S ns ks)) {ns2 : List CNode} {i : ℕ} (hdup : DupOf ns ns2) (hi : i < ns2.length)
    (hSbag : S ⊆ (ns2[i]'hi).bag) {chain : List (Finset ℕ)} {M N : Finset ℕ} (hN : Nest chain M S)
    (hNM : N ⊆ M) :
    TI v (AR.chainToRT ns (ks.map AR.toRT)) (AR.chainToRT (addJunk i (branchRT v chain M) ns2) (ks.map AR.toRT)) ∧
    tc v (AR.chainToRT (addJunk i (branchRT v chain M) ns2) (ks.map AR.toRT)) false = 1 ∧
    v ∈ (AR.chainToRT (addJunk i (branchRT v chain M) ns2) (ks.map AR.toRT)).verts ∧
    (∀ u ∈ N, ∃ Y ∈ (AR.chainToRT (addJunk i (branchRT v chain M) ns2) (ks.map AR.toRT)).bags, v ∈ Y ∧ u ∈ Y) ∧
    (∀ Y ∈ (AR.chainToRT (addJunk i (branchRT v chain M) ns2) (ks.map AR.toRT)).bags, v ∈ Y → Y = insert v M) := by
  obtain ⟨hns, hbase, hkids, hleaf, hkp, hSB, hkfree⟩ := runOk_run hx
  have hvS : v ∉ S := fun h => hvB (hSB h)
  have hfree : ∀ n ∈ ns, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts :=
    fun n hn => ⟨(hbase n hn).2.1, fun J hJ => ((hbase n hn).2.2 J hJ).2⟩
  have hK : List.Forall₂ (TI v) (ks.map AR.toRT) (ks.map AR.toRT) := List.forall₂_same.2 (fun k _ => TI.refl v k)
  have hKz : tcL v (ks.map AR.toRT) false = 0 := by
    rw [tcL_eq_sum, List.sum_eq_zero]
    intro x hx'
    obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hx'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
    exact tc_zero_of_notin v _ false (hkfree k hk)
  obtain ⟨hTI, htc⟩ := chain_att_TI v hns hdup hi hfree hSbag hN hvS hK hKz
  have hinfo := hdup.info
  have hne'' : addJunk i (branchRT v chain M) ns2 ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [length_addJunk] at this
    have h0 : ns2.length = 0 := by simpa using this
    omega
  have hb' := mem_bags_chainToRT (ks.map AR.toRT) _ hne''
  obtain ⟨y, hy, hbrj, -⟩ := br_mem_addJunk (branchRT v chain M) ns2 i hi
  have hleaf' : insert v M ∈ (AR.chainToRT (addJunk i (branchRT v chain M) ns2) (ks.map AR.toRT)).bags :=
    (hb' _).2 (Or.inr (Or.inl ⟨y, hy, _, hbrj, leaf_mem_bags_branch v chain M⟩))
  refine ⟨hTI, htc false, ?_, ?_, ?_⟩
  · exact (RT.mem_verts_iff _ v).2 ⟨insert v M, hleaf', Finset.mem_insert_self _ _⟩
  · intro u hu
    exact ⟨insert v M, hleaf', Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (hNM hu)⟩
  · intro Y hY hvY
    rcases (hb' Y).1 hY with ⟨y, hy, hYy⟩ | ⟨y, hy, J, hJ, hYJ⟩ | ⟨k', hk', hYk⟩
    · exfalso
      rcases mem_addJunk (branchRT v chain M) ns2 i y hy with h | ⟨n, hn, rfl⟩
      · obtain ⟨n0, hn0, hb0, -⟩ := hinfo y h
        exact (hfree n0 hn0).1 (by rw [← hb0, ← hYy]; exact hvY)
      · obtain ⟨n0, hn0, hb0, -⟩ := hinfo n hn
        exact (hfree n0 hn0).1 (by rw [← hb0]; rw [hYy] at hvY; exact hvY)
    · have hJv : v ∈ J.verts := (RT.mem_verts_iff J v).2 ⟨Y, hYJ, hvY⟩
      rcases mem_addJunk (branchRT v chain M) ns2 i y hy with h | ⟨n, hn, rfl⟩
      · obtain ⟨n0, hn0, -, hj0⟩ := hinfo y h
        exact absurd hJv ((hfree n0 hn0).2 J (hj0 J hJ))
      · obtain ⟨n0, hn0, -, hj0⟩ := hinfo n hn
        rcases List.mem_append.1 hJ with hJ | hJ
        · exact absurd hJv ((hfree n0 hn0).2 J (hj0 J hJ))
        · rw [List.mem_singleton] at hJ; subst hJ
          exact mem_bags_branch_v hvS chain M hN Y hYJ hvY
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
      exact absurd ((RT.mem_verts_iff _ v).2 ⟨Y, hYk, hvY⟩) (hkfree k hk)


theorem applyAt_att_none (v : ℕ) (chain : List (Finset ℕ)) (M S : Finset ℕ) (ns : List CNode) (ks : List AR) :
    applyAt v (.att none chain M) (.run S ns ks) =
      .run S (addJunk (ns.length - 1) (branchRT v chain M) ns) ks := rfl

theorem applyAt_att_some (v : ℕ) (chain : List (Finset ℕ)) (M S : Finset ℕ) (ns : List CNode) (ks : List AR)
    (c : Cut) :
    applyAt v (.att (some c) chain M) (.run S ns ks) =
      .run S (addJunk (cutAt (typical (csz ns)) (witnesses (csz ns)) c ns).2 (branchRT v chain M)
        (cutAt (typical (csz ns)) (witnesses (csz ns)) c ns).1) ks := rfl

/-- Old nodes stay prunable-junk-clean after adding `v` to the boundary. -/
theorem chain_ok_of_base {v : ℕ} {B S : Finset ℕ} {ns C : List CNode}
    (hbase : ∀ n0 ∈ ns, n0.bag ∩ B = S ∧ v ∉ n0.bag ∧ ∀ J ∈ n0.junk, Jk B S J ∧ v ∉ J.verts)
    (hC : ∀ n ∈ C, ∃ n0 ∈ ns, n.bag = n0.bag ∧ ∀ J ∈ n.junk, J ∈ n0.junk) :
    ∀ n ∈ C, n.bag ∩ insert v B = S ∧ ∀ J ∈ n.junk, keep S (norm (RT.prof (insert v B) J)) = false := by
  intro n hn
  obtain ⟨n0, hn0, hb, hj⟩ := hC n hn
  obtain ⟨h1, h2, h3⟩ := hbase n0 hn0
  exact ⟨by rw [hb, inter_insert_of_not_mem h2]; exact h1,
    fun J hJ => junk_keep (h3 J (hj J hJ)).1 (h3 J (hj J hJ)).2 subset_rfl⟩

theorem att_none (v : ℕ) (B S : Finset ℕ) (ns : List CNode) (ks : List AR) (hvB : v ∉ B)
    (hx : RunOk v B (.run S ns ks)) (hcn : CT.Conn (CT.node S (typical (csz ns)) (ks.map (AR.charF Finset.card))))
    {chain : List (Finset ℕ)} {M N : Finset ℕ} (hN : Nest chain M S) (hNM : N ⊆ M) :
    IRC v B (.run S ns ks) (applyAt v (.att none chain M) (.run S ns ks))
      (CT.node S (typical (csz ns)) (ks.map (AR.charF Finset.card) ++ [pathSubtree v chain M])) N := by
  obtain ⟨hns, hbase, hkids, hleaf, hkp, hSB, hkfree⟩ := runOk_run hx
  have hvS : v ∉ S := fun h => hvB (hSB h)
  have hi : ns.length - 1 < ns.length := by
    have := List.length_pos_of_ne_nil hns; omega
  have hSbag : S ⊆ (ns[ns.length - 1]'hi).bag := by
    have := (hbase _ (List.getElem_mem hi)).1
    rw [← this]; exact Finset.inter_subset_left
  obtain ⟨hTI, htc, hvin, hcov, hvb⟩ := att_topo v B S ns ks hvB hx (DupOf.refl (ns := ns)) hi hSbag hN hNM
  rw [applyAt_att_none]
  have hxt : AR.toRT (.run S (addJunk (ns.length - 1) (branchRT v chain M) ns) ks) =
      AR.chainToRT (addJunk (ns.length - 1) (branchRT v chain M) ns) (ks.map AR.toRT) := AR.toRT_run _ _ _
  have hxo : AR.toRT (.run S ns ks) = AR.chainToRT ns (ks.map AR.toRT) := AR.toRT_run S ns ks
  have hnS := nest_sub hN
  have hbrQ : RT.prof (insert v B) (branchRT v chain M) = pathSubtree v chain M :=
    prof_branch hvB chain M (fun X hX => (hnS.1 X hX).trans hSB) (hnS.2.trans hSB)
  have hKQ := kids_norm_prof (v := v) (B := B) hkids
  have hkeep : keep S (norm (pathSubtree v chain M)) = true :=
    keep_of_mem_verts (verts_pathSubtree_v v chain M) hvS
  have hnorm : norm (RT.prof (insert v B) (AR.chainToRT ns (branchRT v chain M :: ks.map AR.toRT))) =
      norm (CT.node S (typical (csz ns)) (ks.map (AR.charF Finset.card) ++ [pathSubtree v chain M])) := by
    rw [chain_step v B ns S _ (pathSubtree v chain M :: ks.map (AR.charF Finset.card)) hns
      (chain_ok_of_base hbase (fun n hn => ⟨n, hn, rfl, fun J hJ => hJ⟩)) (by
        simp only [List.map_cons, hbrQ]
        rw [hKQ])]
    apply norm_att_swap ((CT.conn_node).1 hcn) hkeep
    intro z hz hkey
    rw [key_pathSubtree hvS hN] at hkey
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hz
    have := Finset.mem_of_min hkey
    exact hvB (verts_charF_sub k (hkids k hk).canon (Finset.mem_sdiff.1 this).1)
  have hmem : pathSubtree v chain M ∈ ks.map (AR.charF Finset.card) ++ [pathSubtree v chain M] := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxt, hxo]; exact hTI
  · rw [hxt]; exact htc
  · rw [hxt]; exact hvin
  · rw [hxt]; exact hcov
  · refine ⟨_, ?_, DomC.refl _⟩
    rw [hxt, chainToRT_addJunk_last _ _ _ hns]
    exact hnorm
  · intro Y hY hvY
    rw [hxt] at hY
    have := hvb Y hY hvY
    rw [this, Finset.card_insert_of_notMem (fun h => hvB (hSB (hnS.2 h)))]
    exact (entry_pathSubtree hvS chain M hN (fun X hX hvX => hvS (hnS.1 X hX hvX))).trans
      (norm_kid_le (K := ks.map (AR.charF Finset.card) ++ [pathSubtree v chain M]) hmem hkeep)
  · exact CT.mem_verts.2 (Or.inr ⟨_, hmem, verts_pathSubtree_v v chain M⟩)


theorem att_some (v : ℕ) (B S : Finset ℕ) (ns : List CNode) (ks : List AR) (hvB : v ∉ B)
    (hx : RunOk v B (.run S ns ks)) {chain : List (Finset ℕ)} {M N : Finset ℕ} (hN : Nest chain M S)
    (hNM : N ⊆ M) (c : Cut) (hc : c.Valid (typical (csz ns)).length) :
    IRC v B (.run S ns ks) (applyAt v (.att (some c) chain M) (.run S ns ks))
      (CT.node S ((typical (csz ns)).take (cHi c + 1))
        [pathSubtree v chain M, CT.node S ((typical (csz ns)).drop (cLo c)) (ks.map (AR.charF Finset.card))]) N := by
  obtain ⟨hns, hbase, hkids, hleaf, hkp, hSB, hkfree⟩ := runOk_run hx
  have hvS : v ∉ S := fun h => hvB (hSB h)
  have hs : csz ns ≠ [] := by
    intro h; apply hns; unfold csz at h; exact List.map_eq_nil_iff.1 h
  have hlenw : (witnesses (csz ns)).length = (typical (csz ns)).length := (witnesses_cover (csz ns)).len
  have hc' : c.Valid (witnesses (csz ns)).length := by rw [hlenw]; exact hc
  have hdup : DupOf ns (cutAt (typical (csz ns)) (witnesses (csz ns)) c ns).1 := DupOf_cutAt DupOf.refl _ _ c
  have hcsz := csz_cutAt hs hc' (ns := ns) (by simp [csz])
  obtain ⟨L, R, hns2, hcL, hcR⟩ := csz_exists_two hcsz
  have hidx := cutAt_snd (s := csz ns) c ns
  have hla : L.length = cA (csz ns) c := by
    rw [← csz_length L, hcL]
    have := cA_le hs hc'
    simp [List.length_take]; omega
  have hLne : L ≠ [] := by
    intro h; rw [h] at hla; have := cA_pos (s := csz ns) c; simp at hla; omega
  have hRne : R ≠ [] := by
    intro h; rw [h] at hcR
    have hb := cB_lt hs hc'
    have h2 : ((csz ns).drop (cB (csz ns) c)).length = 0 := by rw [← hcR]; simp [csz]
    simp only [List.length_drop] at h2
    omega
  have hi : L.length - 1 < (L ++ R).length := by
    have := List.length_pos_of_ne_nil hLne; simp; omega
  have hidx' : (cutAt (typical (csz ns)) (witnesses (csz ns)) c ns).2 = L.length - 1 := by omega
  have hdup' : DupOf ns (L ++ R) := by rw [← hns2]; exact hdup
  have hinfo := hdup'.info
  have hSbag : S ⊆ ((L ++ R)[L.length - 1]'hi).bag := by
    obtain ⟨n0, hn0, hb0, -⟩ := hinfo _ (List.getElem_mem hi)
    rw [hb0, ← (hbase n0 hn0).1]; exact Finset.inter_subset_left
  obtain ⟨hTI, htc, hvin, hcov, hvb⟩ := att_topo v B S ns ks hvB hx hdup' hi hSbag hN hNM
  rw [applyAt_att_some, hns2, hidx']
  have hxt : AR.toRT (.run S (addJunk (L.length - 1) (branchRT v chain M) (L ++ R)) ks) =
      AR.chainToRT (addJunk (L.length - 1) (branchRT v chain M) (L ++ R)) (ks.map AR.toRT) := AR.toRT_run _ _ _
  have hxo : AR.toRT (.run S ns ks) = AR.chainToRT ns (ks.map AR.toRT) := AR.toRT_run S ns ks
  have hnS := nest_sub hN
  have hbrQ : RT.prof (insert v B) (branchRT v chain M) = pathSubtree v chain M :=
    prof_branch hvB chain M (fun X hX => (hnS.1 X hX).trans hSB) (hnS.2.trans hSB)
  have hKQ := kids_norm_prof (v := v) (B := B) hkids
  have hkeep : keep S (norm (pathSubtree v chain M)) = true :=
    keep_of_mem_verts (verts_pathSubtree_v v chain M) hvS
  have hokL := chain_ok_of_base hbase (C := L) (fun n hn => hinfo n (by simp [hn]))
  have hokR := chain_ok_of_base hbase (C := R) (fun n hn => hinfo n (by simp [hn]))
  have hRnorm : norm (RT.prof (insert v B) (AR.chainToRT R (ks.map AR.toRT))) =
      norm (CT.node S (typical (csz R)) (ks.map (AR.charF Finset.card))) :=
    chain_step v B R S _ _ hRne hokR hKQ
  have hcL' : csz L = (csz ns).take (cA (csz ns) c) := hcL
  have hdomL : Dom (typical (csz L)) ((typical (csz ns)).take (cHi c + 1)) := by
    rw [hcL]; exact dom_left hs hc'
  have hdomR : Dom (typical (csz R)) ((typical (csz ns)).drop (cLo c)) := by
    rw [hcR]; exact dom_right hs hc'
  have hmem : pathSubtree v chain M ∈ [pathSubtree v chain M,
      CT.node S ((typical (csz ns)).drop (cLo c)) (ks.map (AR.charF Finset.card))] := List.mem_cons_self
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxt, hxo]; exact hTI
  · rw [hxt]; exact htc
  · rw [hxt]; exact hvin
  · rw [hxt]; exact hcov
  · refine ⟨CT.node S (typical (csz L)) [pathSubtree v chain M,
      CT.node S (typical (csz R)) (ks.map (AR.charF Finset.card))], ?_, ⟨rfl, hdomL, DomC.refl _, ⟨rfl, hdomR, DomCL.refl _⟩, trivial⟩⟩
    rw [hxt, addJunk_append_left _ L R _ (by have := List.length_pos_of_ne_nil hLne; omega)]
    have hne1 : addJunk (L.length - 1) (branchRT v chain M) L ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [length_addJunk] at this
      exact hLne (List.length_eq_zero_iff.1 (by simpa using this))
    rw [chainToRT_append _ _ _ hne1 hRne, chainToRT_addJunk_last _ _ _ hLne]
    rw [chain_step v B L S _ [pathSubtree v chain M,
      CT.node S (typical (csz R)) (ks.map (AR.charF Finset.card))] hLne hokL (by
        simp only [List.map_cons, List.map_nil, hbrQ, hRnorm])]
  · intro Y hY hvY
    rw [hxt] at hY
    have := hvb Y (by rw [hxt] at *; exact hY) hvY
    rw [this, Finset.card_insert_of_notMem (fun h => hvB (hSB (hnS.2 h)))]
    exact (entry_pathSubtree hvS chain M hN (fun X hX hvX => hvS (hnS.1 X hX hvX))).trans
      (norm_kid_le (K := [pathSubtree v chain M, CT.node S ((typical (csz ns)).drop (cLo c)) (ks.map (AR.charF Finset.card))])
        hmem hkeep)
  · exact CT.mem_verts.2 (Or.inr ⟨_, hmem, verts_pathSubtree_v v chain M⟩)

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.RealizeIR` -/

section
/-!
# The realisation of an introduce plan along a path (work package C5, part 14)

`ir_claim`: every plan of `introPlans v N (charF x)` is realised by `applyRun v plan path x`.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem PRC.irc {v : ℕ} {B : Finset ℕ} {x x' : AR} {rep : CT} {cov N : Finset ℕ} {hp : Bool}
    (h : PRC v B x x' rep cov hp) (hN : N ⊆ cov) : IRC v B x x' rep N :=
  ⟨h.ti, by simpa using h.tcv false, h.vin, fun u hu => h.cov u (hN hu), h.chr, h.wid, h.vrep⟩

theorem wtop_claim (v : ℕ) (B : Finset ℕ) (hvB : v ∉ B) (N : Finset ℕ) :
    ∀ (S : Finset ℕ) (ns : List CNode) (ks : List AR), RunOk v B (.run S ns ks) →
    ∀ (p : Plan) (rep : CT) (cov : Finset ℕ),
      (p, rep, cov) ∈ wtopPlans v (AR.charF Finset.card (.run S ns ks)) → N ⊆ cov →
      IRC v B (.run S ns ks) (applyAt v p (.run S ns ks)) rep N := by
  intro S ns ks hx p rep cov hmem hN
  have hc : AR.charF Finset.card (.run S ns ks) =
      CT.node S (typical (csz ns)) (ks.map (AR.charF Finset.card)) := AR.charF_run _ _ _ _
  rw [hc] at hmem
  simp only [wtopPlans, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at hmem
  rcases hmem with (⟨⟨w, r0, c0⟩, hp, h⟩ | ⟨f, hf, ⟨w, r0, c0⟩, hp, h⟩) | ⟨f, hf, ⟨w, r0, c0⟩, hp, h⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have := win_claim v B hvB (.run S ns ks) hx none w r0 c0 (by simp [PreOk]) (by rw [hc]; simpa [preLo] using hp)
    exact this.irc hN
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hv : PreOk (typical (csz ns)).length (some (Cut.t1 f)) := by simp only [PreOk, CT.Cut.Valid]; exact hf
    have := win_claim v B hvB (.run S ns ks) hx (some (Cut.t1 f)) w r0 c0 hv (by rw [hc]; simpa [preLo, cLo] using hp)
    exact this.irc hN
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hv : PreOk (typical (csz ns)).length (some (Cut.t2 f)) := by simp only [PreOk, CT.Cut.Valid]; omega
    have := win_claim v B hvB (.run S ns ks) hx (some (Cut.t2 f)) w r0 c0 hv (by rw [hc]; simpa [preLo, cLo] using hp)
    exact this.irc hN


theorem att_claim (v : ℕ) (B : Finset ℕ) (hvB : v ∉ B) (N : Finset ℕ) :
    ∀ (S : Finset ℕ) (ns : List CNode) (ks : List AR), RunOk v B (.run S ns ks) →
    CT.Conn (CT.node S (typical (csz ns)) (ks.map (AR.charF Finset.card))) →
    ∀ (p : Plan) (r : CT),
      (p, r) ∈ attachPlans v N (AR.charF Finset.card (.run S ns ks)) →
      IRC v B (.run S ns ks) (applyAt v p (.run S ns ks)) r N := by
  intro S ns ks hx hcn p r hmem
  have hc : AR.charF Finset.card (.run S ns ks) =
      CT.node S (typical (csz ns)) (ks.map (AR.charF Finset.card)) := AR.charF_run _ _ _ _
  rw [hc] at hmem
  simp only [attachPlans, List.mem_flatMap, List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hmem
  obtain ⟨⟨chain, M⟩, hcm, hp⟩ := hmem
  obtain ⟨h1, h2, h3, h4⟩ := mem_allChains.1 hcm
  have hN : Nest chain M S := nest_of_chain chain S h2 (fun X hX => (h1 X (List.mem_of_mem_head? hX)).2) h4
  rcases hp with (h | ⟨f, hf, h⟩) | ⟨f, hf, h⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact att_none v B S ns ks hvB hx hcn hN h3
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hv : (Cut.t1 f).Valid (typical (csz ns)).length := by simp only [CT.Cut.Valid]; exact hf
    exact att_some v B S ns ks hvB hx hN h3 (Cut.t1 f) hv
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hv : (Cut.t2 f).Valid (typical (csz ns)).length := by simp only [CT.Cut.Valid]; omega
    exact att_some v B S ns ks hvB hx hN h3 (Cut.t2 f) hv


/-! ## descending through a kid -/

theorem forall2_TI_mid {v : ℕ} {a b : RT} (h : TI v a b) : ∀ l1 l2 : List RT,
    List.Forall₂ (TI v) (l1 ++ a :: l2) (l1 ++ b :: l2) := by
  intro l1 l2
  induction l1 with
  | nil => exact List.Forall₂.cons h (List.forall₂_same.2 (fun k _ => TI.refl v k))
  | cons k l1 ih => exact List.Forall₂.cons (TI.refl v k) ih

theorem domCL_mid {a b : CT} (h : DomC a b) : ∀ l1 l2 : List CT, DomCL (l1 ++ a :: l2) (l1 ++ b :: l2) := by
  intro l1 l2
  induction l1 with
  | nil => exact ⟨h, DomCL.refl _⟩
  | cons k l1 ih => exact ⟨DomC.refl _, ih⟩

theorem tcL_mid (u : ℕ) (a : RT) (p : Bool) : ∀ l1 l2 : List RT, (∀ z ∈ l1 ++ l2, u ∉ z.verts) →
    tcL u (l1 ++ a :: l2) p = tc u a p := by
  intro l1 l2 h
  rw [tcL_eq_sum, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  have h1 : (l1.map (fun k => tc u k p)).sum = 0 := by
    rw [List.sum_eq_zero]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact tc_zero_of_notin u k p (h k (by simp [hk]))
  have h2 : (l2.map (fun k => tc u k p)).sum = 0 := by
    rw [List.sum_eq_zero]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact tc_zero_of_notin u k p (h k (by simp [hk]))
  rw [h1, h2]; simp

theorem modifyNth_mid {α : Type} (f : α → α) : ∀ (l1 : List α) (a : α) (l2 : List α),
    modifyNth f l1.length (l1 ++ a :: l2) = l1 ++ f a :: l2 := by
  intro l1
  induction l1 with
  | nil => intro a l2; rfl
  | cons k l1 ih => intro a l2; simp only [List.length_cons, List.cons_append, modifyNth]; rw [ih]

theorem kid_descent (v : ℕ) (B S : Finset ℕ) (ns : List CNode) (hvB : v ∉ B)
    (ks1 : List AR) (k0 : AR) (ks2 : List AR) (hx : RunOk v B (.run S ns (ks1 ++ k0 :: ks2)))
    (k0' : AR) (r' : CT) (N : Finset ℕ) (hk : IRC v B k0 k0' r' N) :
    IRC v B (.run S ns (ks1 ++ k0 :: ks2)) (.run S ns (ks1 ++ k0' :: ks2))
      (CT.node S (typical (csz ns)) (ks1.map (AR.charF Finset.card) ++ r' :: ks2.map (AR.charF Finset.card))) N := by
  obtain ⟨hns, hbase, hkids, hleaf, hkp, hSB, hkfree⟩ := runOk_run hx
  have hvS : v ∉ S := fun h => hvB (hSB h)
  have hfree : ∀ n ∈ ns, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts :=
    fun n hn => ⟨(hbase n hn).2.1, fun J hJ => ((hbase n hn).2.2 J hJ).2⟩
  have hkfree1 : ∀ k ∈ ks1, v ∉ (AR.toRT k).verts := fun k hk' => hkfree k (by simp [hk'])
  have hkfree2 : ∀ k ∈ ks2, v ∉ (AR.toRT k).verts := fun k hk' => hkfree k (by simp [hk'])
  have hxt : AR.toRT (.run S ns (ks1 ++ k0' :: ks2)) =
      AR.chainToRT ns ((ks1 ++ k0' :: ks2).map AR.toRT) := AR.toRT_run _ _ _
  have hxo : AR.toRT (.run S ns (ks1 ++ k0 :: ks2)) =
      AR.chainToRT ns ((ks1 ++ k0 :: ks2).map AR.toRT) := AR.toRT_run _ _ _
  have hmapK : ∀ k, (ks1 ++ k :: ks2).map AR.toRT = ks1.map AR.toRT ++ AR.toRT k :: ks2.map AR.toRT := by
    intro k; simp
  rw [hmapK] at hxt hxo
  have hK : List.Forall₂ (TI v) (ks1.map AR.toRT ++ AR.toRT k0 :: ks2.map AR.toRT)
      (ks1.map AR.toRT ++ AR.toRT k0' :: ks2.map AR.toRT) := forall2_TI_mid hk.ti _ _
  have hfreeL : ∀ z ∈ ks1.map AR.toRT ++ ks2.map AR.toRT, v ∉ z.verts := by
    intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hz; exact hkfree1 k hk'
    · obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hz; exact hkfree2 k hk'
  have hne'' : ns ≠ [] := hns
  have hb' := mem_bags_chainToRT (ks1.map AR.toRT ++ AR.toRT k0' :: ks2.map AR.toRT) ns hns
  have hkmem : AR.toRT k0' ∈ ks1.map AR.toRT ++ AR.toRT k0' :: ks2.map AR.toRT := by simp
  have hkeep : keep S (norm r') = true := keep_of_mem_verts hk.vrep hvS
  have hmemr : r' ∈ ks1.map (AR.charF Finset.card) ++ r' :: ks2.map (AR.charF Finset.card) := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxt, hxo]; exact chain_kids_TI v hns hfree hK
  · rw [hxt, tc_chain_prefix_free v ns _ false hns hfree, tcL_mid v _ false _ _ hfreeL]; exact hk.tcv
  · rw [hxt, mem_verts_chainToRT]
    exact Or.inr (Or.inr ⟨_, hkmem, hk.vin⟩)
  · intro u hu
    obtain ⟨Y, hY, hvY, huY⟩ := hk.cov u hu
    rw [hxt]
    exact ⟨Y, (hb' Y).2 (Or.inr (Or.inr ⟨_, hkmem, hY⟩)), hvY, huY⟩
  · obtain ⟨Q0, hQ0, hdom⟩ := hk.chr
    refine ⟨CT.node S (typical (csz ns)) (ks1.map (AR.charF Finset.card) ++ Q0 :: ks2.map (AR.charF Finset.card)),
      ?_, ⟨rfl, Dom.refl _, domCL_mid hdom _ _⟩⟩
    rw [hxt]
    refine (chain_step v B ns S _ _ hns (chain_ok_of_base hbase (fun n hn => ⟨n, hn, rfl, fun J hJ => hJ⟩)) ?_)
    simp only [List.map_append, List.map_cons]
    rw [hQ0]
    have h1 := kids_norm_prof (v := v) (B := B) (ks := ks1) (fun k hk' => hkids k (by simp [hk']))
    have h2 := kids_norm_prof (v := v) (B := B) (ks := ks2) (fun k hk' => hkids k (by simp [hk']))
    simp only [List.map_map] at h1 h2 ⊢
    rw [h1, h2]
  · intro Y hY hvY
    rw [hxt] at hY
    rcases (hb' Y).1 hY with ⟨y, hy, hYy⟩ | ⟨y, hy, J, hJ, hYJ⟩ | ⟨k', hk'', hYk⟩
    · exact absurd (hYy ▸ hvY) (hfree y hy).1
    · exact absurd ((RT.mem_verts_iff J v).2 ⟨Y, hYJ, hvY⟩) ((hfree y hy).2 J hJ)
    · rcases List.mem_append.1 hk'' with hk3 | hk3
      · obtain ⟨k, hk4, rfl⟩ := List.mem_map.1 hk3
        exact absurd ((RT.mem_verts_iff _ v).2 ⟨Y, hYk, hvY⟩) (hkfree1 k hk4)
      · rcases List.mem_cons.1 hk3 with rfl | hk3
        · exact (hk.wid Y hYk hvY).trans (norm_kid_le hmemr hkeep)
        · obtain ⟨k, hk4, rfl⟩ := List.mem_map.1 hk3
          exact absurd ((RT.mem_verts_iff _ v).2 ⟨Y, hYk, hvY⟩) (hkfree2 k hk4)
  · exact CT.mem_verts.2 (Or.inr ⟨_, hmemr, hk.vrep⟩)


theorem introKids_ctx (v : ℕ) (N S : Finset ℕ) (y : List ℕ) : ∀ (kids pre0 : List CT) (path : List ℕ) (plan : Plan) (r : CT),
    (path, plan, r) ∈ introKids v N S y pre0 kids →
    ∃ pre1 k post rest r', kids = pre1 ++ k :: post ∧ path = (pre0 ++ pre1).length :: rest ∧
      (rest, plan, r') ∈ introPlans v N k ∧ r = CT.node S y (pre0 ++ pre1 ++ r' :: post) := by
  intro kids
  induction kids with
  | nil => intro pre0 path plan r h; simp [introKids] at h
  | cons k post ih =>
    intro pre0 path plan r h
    simp only [introKids, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨rest, pl, r'⟩, hp, h⟩ | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨[], k, post, rest, r', by simp, by simp, hp, by simp⟩
    · obtain ⟨pre1, k', post', rest, r', h1, h2, h3, h4⟩ := ih (pre0 ++ [k]) path plan r h
      refine ⟨k :: pre1, k', post', rest, r', by rw [h1]; rfl, ?_, h3, ?_⟩
      · rw [h2]; simp
      · rw [h4]; simp

theorem ir_claim (v : ℕ) (B : Finset ℕ) (hvB : v ∉ B) (N : Finset ℕ) : ∀ x : AR, RunOk v B x →
    CT.Conn (AR.charF Finset.card x) → ∀ (path : List ℕ) (plan : Plan) (r : CT),
      (path, plan, r) ∈ introPlans v N (AR.charF Finset.card x) →
      IRC v B x (applyRun v plan path x) r N := by
  intro x
  induction x using AR.ind with
  | _ S ns ks ih =>
    intro hx hcn path plan r hmem
    have hc : AR.charF Finset.card (.run S ns ks) =
        CT.node S (typical (csz ns)) (ks.map (AR.charF Finset.card)) := AR.charF_run _ _ _ _
    rw [hc] at hmem hcn
    have hmem' := hmem
    simp only [introPlans, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at hmem'
    rcases hmem' with (⟨⟨p, r0, c0⟩, ⟨hp, hNc⟩, h⟩ | h) | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have := wtop_claim v B hvB N S ns ks hx p r0 c0 (by rw [hc]; exact hp) hNc
      simpa [applyRun] using this
    · split_ifs at h with hNS
      · simp only [List.mem_map, Prod.mk.injEq] at h
        obtain ⟨⟨p, r0⟩, hp, rfl, rfl, rfl⟩ := h
        have := att_claim v B hvB N S ns ks hx hcn p r0 (by rw [hc]; exact hp)
        simpa [applyRun] using this
      · simp at h
    · obtain ⟨pre1, k, post, rest, r', h1, h2, h3, h4⟩ := introKids_ctx v N S _ _ [] path plan r h
      simp only [List.nil_append] at h2 h4
      -- lift the decomposition of the kids to the analysis
      obtain ⟨ks1, ks3, rfl, hks1, hks3⟩ := List.map_eq_append_iff.1 h1
      obtain ⟨k0, ks2, rfl, hk0, hks2⟩ := List.map_eq_cons_iff.1 hks3
      subst hk0 hks1 hks2
      have hkids := (runOk_run hx).2.2.1
      have hk0 : k0 ∈ ks1 ++ k0 :: ks2 := by simp
      have hcn' : CT.Conn (AR.charF Finset.card k0) := by
        have := ((CT.ConnL_iff).1 (CT.conn_node.1 hcn).1) (AR.charF Finset.card k0)
          (List.mem_map.2 ⟨k0, hk0, rfl⟩)
        exact this
      have hIH := ih k0 hk0 (hkids k0 hk0) hcn' rest plan r' h3
      have hd := kid_descent v B S ns hvB ks1 k0 ks2 hx (applyRun v plan rest k0) r' N hIH
      have hlen : (ks1.map (AR.charF Finset.card)).length = ks1.length := by simp
      rw [hlen] at h2
      subst h2
      subst h4
      simp only [applyRun]
      rw [modifyNth_mid]
      exact hd

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.RealizeFinal` -/

section
/-!
# `applyPlan_spec`, `realIntro_spec`, `realize_intro` (work package C5)

The realisation of an introduce plan.  **Repair**: all three statements get the hypothesis
`hs : ∀ u ∈ c.under, adj u v = true → adj v u = true` (the neighbours of `v` below are read through `adj v ·` in
`NT.Good`, but the graph of the tree decomposition is the *symmetric* closure `Adj.graph`; without `hs` an edge
`{v, w}` present only as `adj w v` would need a bag containing `v` and `w ∉ c.bag`, which no realisation provides).
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem applyPlan_spec {adj : Adj} {v : ℕ} {c : NT} {k : ℕ} {t : RT} (hg : (NT.intro v c).Good adj)
    (hs : ∀ u ∈ c.under, adj u v = true → adj v u = true)
    (h : PTD adj c k t) {path : List ℕ} {p : Plan} {r : CT}
    (hr : (path, p, r) ∈ CT.introPlans v (nbrs adj v c.bag) (t.char c.bag))
    (hk : (CT.norm r).maxEntry ≤ k + 1) :
    PTD adj (.intro v c) k (applyPlan v (nbrs adj v c.bag) c.bag path p t) ∧
      DomC ((applyPlan v (nbrs adj v c.bag) c.bag path p t).char (insert v c.bag)) (CT.norm r) := by
  have hg' : v ∉ c.bag ∧ (∀ u ∈ c.under, adj v u = true → u ∈ c.bag) ∧ v ∉ c.under ∧ NT.Good adj c := hg
  obtain ⟨hvB, hclos, hvU, hgc⟩ := hg'
  set B := c.bag with hB
  set A := analyze B t with hA
  have hverts : (AR.toRT A).verts = c.under := by rw [hA, verts_toRT_analyze, h.1.verts_eq]
  have hfree : v ∉ (AR.toRT A).verts := by rw [hverts]; exact hvU
  have hx : RunOk v B A := ⟨analyze_canon B t, hfree⟩
  have hchar : t.char B = AR.charF Finset.card A := char_eq_charF B t
  have hcn : CT.Conn (AR.charF Finset.card A) := by
    rw [← hchar]
    exact conn_norm _ (RT.conn_prof B t h.1.conn)
  rw [hchar] at hr
  have hir := ir_claim v B hvB (nbrs adj v B) A hx hcn path p r hr
  unfold applyPlan
  rw [← hA]
  set x' := applyRun v p path A with hx'
  have hti := hir.ti
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · -- vertices
    ext z
    change z ∈ (AR.toRT x').verts ↔ z ∈ insert v c.under
    rw [Finset.mem_insert]
    constructor
    · intro hz
      rcases hti.vsub z hz with h1 | h1
      · rw [hverts] at h1; exact Or.inr h1
      · exact Or.inl h1
    · rintro (rfl | hz)
      · exact hir.vin
      · exact hti.vsup z (by rw [hverts]; exact hz)
  · -- edges
    intro u w huw hu hw
    have hu' : u ∈ insert v c.under := hu
    have hw' : w ∈ insert v c.under := hw
    have hadj : u ≠ w ∧ (adj u w = true ∨ adj w u = true) := by
      simpa [Adj.graph, SimpleGraph.fromRel_adj] using huw
    have hnbr : ∀ z ∈ c.under, adj v z = true → z ∈ nbrs adj v B := by
      intro z hz hvz
      exact Finset.mem_filter.2 ⟨hclos z hz hvz, hvz⟩
    by_cases huv : u = v
    · subst huv
      have hwU : w ∈ c.under := by
        rcases Finset.mem_insert.1 hw' with rfl | h1
        · exact absurd rfl hadj.1
        · exact h1
      have hvw : adj u w = true := by
        rcases hadj.2 with h1 | h1
        · exact h1
        · exact hs w hwU h1
      obtain ⟨Y, hY, hvY, hwY⟩ := hir.cov w (hnbr w hwU hvw)
      exact ⟨Y, hY, hvY, hwY⟩
    · by_cases hwv : w = v
      · subst hwv
        have huU : u ∈ c.under := by
          rcases Finset.mem_insert.1 hu' with rfl | h1
          · exact absurd rfl huv
          · exact h1
        have hvu : adj w u = true := by
          rcases hadj.2 with h1 | h1
          · exact hs u huU h1
          · exact h1
        obtain ⟨Y, hY, hvY, huY⟩ := hir.cov u (hnbr u huU hvu)
        exact ⟨Y, hY, huY, hvY⟩
      · have huU : u ∈ c.under := (Finset.mem_insert.1 hu').resolve_left huv
        have hwU : w ∈ c.under := (Finset.mem_insert.1 hw').resolve_left hwv
        obtain ⟨X, hX, hxu, hxw⟩ := h.1.edges u w huw huU hwU
        obtain ⟨Y, hY, hXY⟩ := hti.bsup X ((mem_bags_toRT_analyze B t X).2 hX)
        exact ⟨Y, hY, hXY hxu, hXY hxw⟩
  · -- connectedness
    rw [conn_iff_tc]
    intro u
    by_cases huv : u = v
    · subst huv; rw [hir.tcv]
    · rw [hti.tcne u huv false]
      exact (conn_iff_tc _).1 (conn_toRT_analyze B t h.1.conn) u
  · -- width
    intro Y hY
    rcases hti.bnew Y hY with hvY | ⟨X, hX, hYX⟩
    · exact (hir.wid Y hY hvY).trans hk
    · exact (Finset.card_le_card hYX).trans (width_toRT_analyze B h.2 X hX)
  · -- the characteristic
    obtain ⟨Q, hQ, hdom⟩ := hir.chr
    have : (AR.toRT x').char (insert v B) = norm (RT.prof (insert v B) (AR.toRT x')) := rfl
    show DomC (RT.char (insert v B) (AR.toRT x')) (norm r)
    unfold RT.char
    rw [hQ]
    exact norm_mono hdom

/-- **Introduce, realised.** -/
theorem realize_intro {adj : Adj} {v : ℕ} {c : NT} {k : ℕ} {t : RT} (hg : (NT.intro v c).Good adj)
    (hs : ∀ u ∈ c.under, adj u v = true → adj v u = true)
    (h : PTD adj c k t) {c' : CT} (hc' : c' ∈ CT.introC (k + 1) v (nbrs adj v c.bag) (t.char c.bag)) :
    ∃ t', PTD adj (.intro v c) k t' ∧ DomC (t'.char (insert v c.bag)) c' := by
  obtain ⟨r, hr, rfl, hk⟩ := mem_introC.1 hc'
  obtain ⟨path, plan, hp⟩ := IR_toPlans v _ hr
  obtain ⟨h1, h2⟩ := applyPlan_spec hg hs h hp hk
  exact ⟨_, h1, h2⟩

/-- **The introduce step of the extraction.** -/
theorem realIntro_spec {adj : Adj} {v : ℕ} {c : NT} {k : ℕ} {t : RT} (hg : (NT.intro v c).Good adj)
    (hs : ∀ u ∈ c.under, adj u v = true → adj v u = true)
    (h : PTD adj c k t) {ca c' : CT} (hca : DomC (t.char c.bag) ca)
    (hc' : c' ∈ CT.introC (k + 1) v (nbrs adj v c.bag) ca) :
    ∃ t', realIntro (k + 1) v (nbrs adj v c.bag) c.bag t c' = some t' ∧ PTD adj (.intro v c) k t' ∧
      DomC (t'.char (insert v c.bag)) c' := by
  obtain ⟨d, hd, hdc⟩ := introC_mono (k + 1) v (nbrs adj v c.bag) hca c' hc'
  obtain ⟨r, hr, rfl, hk⟩ := mem_introC.1 hd
  obtain ⟨path, plan, hp⟩ := IR_toPlans v _ hr
  have hsome : ((CT.introPlans v (nbrs adj v c.bag) (t.char c.bag)).find?
      (fun r => domCB (CT.norm r.2.2) c' && decide ((CT.norm r.2.2).maxEntry ≤ k + 1))).isSome = true :=
    List.find?_isSome.2 ⟨(path, plan, r), hp, by simp [domCB_iff.2 hdc, hk]⟩
  obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 hsome
  have hmem := List.mem_of_find?_eq_some hr0
  have hpred := List.find?_some hr0
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
  obtain ⟨hdom0, hk0⟩ := hpred
  obtain ⟨p1, p2⟩ := applyPlan_spec hg hs h hmem hk0
  refine ⟨_, ?_, p1, DomC.trans p2 (domCB_iff.1 hdom0)⟩
  unfold realIntro
  rw [hr0]; rfl

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.TablesSound` -/

section
/-!
# `tables_sound` and `tables_ne_nil_iff` (work package C6b)

Every table entry is dominated-realised by a partial decomposition.  Induction over the nice tree: leaf (the
empty tree), forget (`char_forget`, `forgetC_mono`), join (`joinC_mono`, `realize_join`), introduce
(`introC_mono`, `realize_intro`).

**Repair** (relative to `proofs-todo/Statements.lean`).  Old statement:

    theorem tables_sound {adj k} : ∀ {nt}, nt.Good adj → ∀ c ∈ tables adj k nt, ∃ t, PTD adj nt k t ∧ DomC (t.char nt.bag) c

New statement: two additional hypotheses `hs : adj.SymmOn W` and `nt.under ⊆ W`.  They are needed only for
`realize_intro`, which itself needs `∀ u ∈ c.under, adj u v = true → adj v u = true` (an edge `{v, w}` visible only as
`adj w v` is not seen by `nbrs adj v _`; see `Wrap/NOTES.md`).  The same two hypotheses are added to
`tables_ne_nil_iff`.  `tables_complete` needs no symmetry.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- `under` is exactly the vertex set of the underlying tree. -/
theorem NT.under_eq_vs : ∀ t : NT, t.under = t.vs := by
  intro t
  refine Finset.Subset.antisymm (NT.under_subset_vs t) ?_
  induction t with
  | leaf => simp
  | intro v c ih =>
    rw [NT.vs_intro]
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact NT.bag_subset_under (NT.intro v c) h
    · exact Finset.mem_insert_of_mem (ih h)
  | forget v c ih =>
    rw [NT.vs_forget]
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact NT.bag_subset_under (NT.forget v c) h
    · exact ih h
  | join a b iha ihb =>
    rw [NT.vs_join]
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact Finset.mem_union_left _ (NT.bag_subset_under a h)
    · rcases Finset.mem_union.1 h with h | h
      · exact Finset.mem_union_left _ (iha h)
      · exact Finset.mem_union_right _ (ihb h)

/-- The empty tree is a partial decomposition of the leaf. -/
theorem ptd_leaf (adj : Adj) (k : ℕ) : PTD adj .leaf k (.node ∅ []) := by
  refine ⟨⟨rfl, fun u v _ hu _ => absurd hu (by simp [NT.under]), by simp [RT.Conn, RT.ConnL]⟩, ?_⟩
  intro X hX
  simp [RT.bags, RT.bagsL] at hX
  simp [hX]

theorem tables_sound {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) :
    ∀ {nt : NT}, nt.Good adj → nt.under ⊆ W → ∀ c ∈ tables adj k nt,
    ∃ t, PTD adj nt k t ∧ DomC (t.char nt.bag) c
  | .leaf, _, _, c, hc => by
    simp only [tables, List.mem_singleton] at hc
    subst hc
    refine ⟨.node ∅ [], ptd_leaf adj k, ?_⟩
    have := char_leaf (adj := adj) (k := k) (.node ∅ []) (ptd_leaf adj k)
    simp only [NT.bag]
    rw [this]
    exact CT.DomC.refl _
  | .forget x c, hg, hW, q, hq => by
    simp only [tables, forgetTable, List.mem_dedup, List.mem_map] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    obtain ⟨t, ht, hd⟩ := tables_sound hs hg.2 hW q0 hq0
    refine ⟨t, ht, ?_⟩
    simp only [NT.bag]
    rw [char_forget c.bag x t ht.1.conn]
    exact forgetC_mono x hd
  | .join a b, hg, hW, q, hq => by
    have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
    obtain ⟨hab, -, hga, hgb, -⟩ := hg'
    have hWa : a.under ⊆ W := fun x hx => hW (Finset.mem_union_left _ hx)
    have hWb : b.under ⊆ W := fun x hx => hW (Finset.mem_union_right _ hx)
    simp only [tables, joinTable, List.mem_dedup, List.mem_flatMap] at hq
    obtain ⟨ca, hca, cb, hcb, hq⟩ := hq
    obtain ⟨ta, hta, hda⟩ := tables_sound hs hga hWa ca hca
    obtain ⟨tb, htb, hdb⟩ := tables_sound hs hgb hWb cb hcb
    rw [← hab] at hdb
    obtain ⟨d, hd, hdq⟩ := joinC_mono (k + 1) hda hdb q hq
    obtain ⟨t, ht, hdt⟩ := realize_join hg hta htb hd
    exact ⟨t, ht, hdt.trans hdq⟩
  | .intro v c, hg, hW, q, hq => by
    have hgc := hg.2.2.2
    have hWc : c.under ⊆ W := fun x hx => hW (Finset.mem_insert_of_mem hx)
    have hvW : v ∈ W := hW (Finset.mem_insert_self _ _)
    simp only [tables, introTable, List.mem_dedup, List.mem_flatMap] at hq
    obtain ⟨q0, hq0, hq⟩ := hq
    obtain ⟨t, ht, hd⟩ := tables_sound hs hgc hWc q0 hq0
    obtain ⟨d, hd', hdq⟩ := introC_mono (k + 1) v (nbrs adj v c.bag) hd q hq
    have hsym : ∀ u ∈ c.under, adj u v = true → adj v u = true := by
      intro u hu h
      rw [← hs u (hWc hu) v hvW]; exact h
    obtain ⟨t', ht', hdt⟩ := realize_intro hg hsym ht hd'
    exact ⟨t', ht', hdt.trans hdq⟩

/-- **The decision** (complete + sound). -/
theorem tables_ne_nil_iff {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) {nt : NT} (hg : nt.Good adj)
    (hW : nt.under ⊆ W) : tables adj k nt ≠ [] ↔ ∃ t, PTD adj nt k t := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨t, ht, -⟩ := tables_sound hs hg hW c hc
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩ h
    obtain ⟨c, hc, -⟩ := tables_complete hg t ht
    rw [h] at hc
    simp at hc

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.Extract` -/

section
/-!
# `extract_spec` (work package C6b): correctness of the extraction

For every table entry `c` of a good nice tree, `extract adj k nt c` returns a real decomposition which is a partial
decomposition of width `≤ k` whose characteristic is dominated by `c`.  Proved by induction on the nice tree,
together with *definedness* (`extract … ≠ none`) and *soundness of every returned value* (the `findSome?` may pick
a different table entry than the one used to prove definedness, so both facts are carried).

**Repair** (relative to `proofs-todo/Statements.lean`): as for `tables_sound`, the extra hypotheses
`hs : adj.SymmOn W` and `nt.under ⊆ W` (needed by `realIntro_spec`).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem findSome_exists {α β : Type} {l : List α} {f : α → Option β} {x : α} (hx : x ∈ l) {t : β}
    (hf : f x = some t) : ∃ t', l.findSome? f = some t' := by
  have : (l.findSome? f).isSome = true := List.findSome?_isSome_iff.2 ⟨x, hx, by simp [hf]⟩
  exact Option.isSome_iff_exists.1 this

theorem findSome_sound {α β : Type} {l : List α} {f : α → Option β} {t : β} (h : l.findSome? f = some t) :
    ∃ x ∈ l, f x = some t := by
  obtain ⟨l₁, a, l₂, rfl, ha, -⟩ := List.findSome?_eq_some_iff.1 h
  exact ⟨a, by simp, ha⟩

theorem extract_all {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) :
    ∀ {nt : NT}, nt.Good adj → nt.under ⊆ W → ∀ c ∈ tables adj k nt,
    (∃ t, extract adj k nt c = some t) ∧
      ∀ t, extract adj k nt c = some t → PTD adj nt k t ∧ DomC (t.char nt.bag) c
  | .leaf, _, _, c, hc => by
    simp only [tables, List.mem_singleton] at hc
    subst hc
    refine ⟨⟨_, rfl⟩, ?_⟩
    intro t ht
    simp only [extract, Option.some.injEq] at ht
    subst ht
    refine ⟨ptd_leaf adj k, ?_⟩
    have := char_leaf (adj := adj) (k := k) (.node ∅ []) (ptd_leaf adj k)
    simp only [NT.bag]
    rw [this]
    exact CT.DomC.refl _
  | .forget x c, hg, hW, q, hq => by
    have hmem := hq
    simp only [tables, forgetTable, List.mem_dedup, List.mem_map] at hmem
    obtain ⟨q0, hq0, hq0e⟩ := hmem
    have key : ∀ q1 t0, PTD adj c k t0 → DomC (t0.char c.bag) q1 → CT.forgetC x q1 = q →
        PTD adj (.forget x c) k t0 ∧ DomC (t0.char (NT.forget x c).bag) q := by
      intro q1 t0 ht0 hd he
      refine ⟨ht0, ?_⟩
      simp only [NT.bag]
      rw [char_forget c.bag x t0 ht0.1.conn, ← he]
      exact forgetC_mono x hd
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨t0, ht0⟩, -⟩ := extract_all hs hg.2 hW q0 hq0
      refine findSome_exists (x := q0) hq0 (t := t0) ?_
      simp [hq0e, ht0]
    · intro t ht
      simp only [extract] at ht
      obtain ⟨q1, hq1, hf⟩ := findSome_sound ht
      by_cases he : CT.forgetC x q1 = q
      · simp only [he, if_true] at hf
        obtain ⟨-, hsp⟩ := extract_all hs hg.2 hW q1 hq1
        obtain ⟨h1, h2⟩ := hsp t hf
        exact key q1 t h1 h2 he
      · simp [he] at hf
  | .join a b, hg, hW, q, hq => by
    have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
    obtain ⟨hab, -, hga, hgb, -⟩ := hg'
    have hWa : a.under ⊆ W := fun x hx => hW (Finset.mem_union_left _ hx)
    have hWb : b.under ⊆ W := fun x hx => hW (Finset.mem_union_right _ hx)
    have hmem := hq
    simp only [tables, joinTable, List.mem_dedup, List.mem_flatMap] at hmem
    obtain ⟨ca, hca, cb, hcb, hq'⟩ := hmem
    -- the step, for any pair of entries
    have step : ∀ ca cb ta tb, ca ∈ tables adj k a → cb ∈ tables adj k b → PTD adj a k ta →
        DomC (ta.char a.bag) ca → PTD adj b k tb → DomC (tb.char b.bag) cb → q ∈ CT.joinC (k + 1) ca cb →
        ∃ t, realJoin (k + 1) a.bag ta tb q = some t ∧ PTD adj (.join a b) k t ∧
          DomC (t.char (NT.join a b).bag) q := by
      intro ca cb ta tb _ _ hta hda htb hdb hqq
      rw [← hab] at hdb
      exact realJoin_spec hg hta htb hda hdb hqq
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨ta, hta⟩, -⟩ := extract_all hs hga hWa ca hca
      obtain ⟨⟨tb, htb⟩, -⟩ := extract_all hs hgb hWb cb hcb
      obtain ⟨-, hspa⟩ := extract_all hs hga hWa ca hca
      obtain ⟨-, hspb⟩ := extract_all hs hgb hWb cb hcb
      obtain ⟨pa, da⟩ := hspa ta hta
      obtain ⟨pb, db⟩ := hspb tb htb
      obtain ⟨t, ht, -⟩ := step ca cb ta tb hca hcb pa da pb db hq'
      have inner : ∃ t', (tables adj k b).findSome? (fun cb => if q ∈ CT.joinC (k + 1) ca cb then
          (extract adj k a ca).bind (fun ta => (extract adj k b cb).bind (fun tb =>
            realJoin (k + 1) a.bag ta tb q)) else none) = some t' := by
        refine findSome_exists (x := cb) hcb (t := t) ?_
        simp [hq', hta, htb, ht]
      obtain ⟨t', ht'⟩ := inner
      refine findSome_exists (x := ca) hca (t := t') ?_
      simpa [extract] using ht'
    · intro t ht
      simp only [extract] at ht
      obtain ⟨ca1, hca1, hf⟩ := findSome_sound ht
      obtain ⟨cb1, hcb1, hf'⟩ := findSome_sound hf
      by_cases he : q ∈ CT.joinC (k + 1) ca1 cb1
      · simp only [he, if_true] at hf'
        obtain ⟨-, hspa⟩ := extract_all hs hga hWa ca1 hca1
        obtain ⟨-, hspb⟩ := extract_all hs hgb hWb cb1 hcb1
        rcases hea : extract adj k a ca1 with _ | ta
        · simp [hea] at hf'
        rcases heb : extract adj k b cb1 with _ | tb
        · simp [hea, heb] at hf'
        simp only [hea, heb, Option.bind_some] at hf'
        obtain ⟨pa, da⟩ := hspa ta hea
        obtain ⟨pb, db⟩ := hspb tb heb
        obtain ⟨t2, ht2, h1, h2⟩ := step ca1 cb1 ta tb hca1 hcb1 pa da pb db he
        rw [ht2] at hf'
        cases hf'
        exact ⟨h1, h2⟩
      · simp [he] at hf'
  | .intro v c, hg, hW, q, hq => by
    have hgc := hg.2.2.2
    have hWc : c.under ⊆ W := fun x hx => hW (Finset.mem_insert_of_mem hx)
    have hvW : v ∈ W := hW (Finset.mem_insert_self _ _)
    have hsym : ∀ u ∈ c.under, adj u v = true → adj v u = true := by
      intro u hu h
      rw [← hs u (hWc hu) v hvW]; exact h
    have hmem := hq
    simp only [tables, introTable, List.mem_dedup, List.mem_flatMap] at hmem
    obtain ⟨q0, hq0, hq'⟩ := hmem
    have step : ∀ q0 t0, q0 ∈ tables adj k c → PTD adj c k t0 → DomC (t0.char c.bag) q0 →
        q ∈ CT.introC (k + 1) v (nbrs adj v c.bag) q0 →
        ∃ t, realIntro (k + 1) v (nbrs adj v c.bag) c.bag t0 q = some t ∧ PTD adj (.intro v c) k t ∧
          DomC (t.char (NT.intro v c).bag) q := by
      intro q0 t0 _ ht0 hd hqq
      exact realIntro_spec hg hsym ht0 hd hqq
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨t0, ht0⟩, hsp⟩ := extract_all hs hgc hWc q0 hq0
      obtain ⟨p0, d0⟩ := hsp t0 ht0
      obtain ⟨t, ht, -⟩ := step q0 t0 hq0 p0 d0 hq'
      refine findSome_exists (x := q0) hq0 (t := t) ?_
      simp [hq', ht0, ht]
    · intro t ht
      simp only [extract] at ht
      obtain ⟨q1, hq1, hf⟩ := findSome_sound ht
      by_cases he : q ∈ CT.introC (k + 1) v (nbrs adj v c.bag) q1
      · simp only [he, if_true] at hf
        obtain ⟨-, hsp⟩ := extract_all hs hgc hWc q1 hq1
        rcases hea : extract adj k c q1 with _ | t0
        · simp [hea] at hf
        simp only [hea, Option.bind_some] at hf
        obtain ⟨p0, d0⟩ := hsp t0 hea
        obtain ⟨t2, ht2, h1, h2⟩ := step q1 t0 hq1 p0 d0 he
        rw [ht2] at hf
        cases hf
        exact ⟨h1, h2⟩
      · simp [he] at hf

/-- **Soundness = correctness of extraction.** -/
theorem extract_spec {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) {nt : NT} (hg : nt.Good adj)
    (hW : nt.under ⊆ W) : ∀ c ∈ tables adj k nt,
    ∃ t, extract adj k nt c = some t ∧ PTD adj nt k t ∧ DomC (t.char nt.bag) c := by
  intro c hc
  obtain ⟨⟨t, ht⟩, hsp⟩ := extract_all hs hg hW c hc
  exact ⟨t, ht, hsp t ht⟩

end Lax117284Proofs.Treewidth.Chars

end
