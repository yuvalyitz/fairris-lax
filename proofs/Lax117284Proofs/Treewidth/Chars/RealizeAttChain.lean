import Lax117284Proofs.Treewidth.Chars.RealizeBranch

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
