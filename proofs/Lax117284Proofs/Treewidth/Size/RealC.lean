import Lax117284Proofs.Treewidth.Size.RealB
import Lax117284Proofs.Treewidth.Size.Plans

/-!
# Size bounds (WP P1), part 9: the cost of the plans of `introPlans`

For a run tree `T` all of whose labels have at most `b` vertices, every plan `pl` of `introPlans v N T` satisfies
`planCost pl ≤ leaves T + b + 3` (`planCost_le_of_mem_introPlans`): a region plan has at most `leaves T` `endAt`'s
(`wcost_le_leaves`) and a new branch has a chain of at most `|S| + 1` sets (`allChains_chain_length_le`).
`leaves` and the labels are invariant under `DomC` (`DomC.leaves_eq`, `DomC.LB`).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

namespace CT

/-! ## labels -/

mutual
/-- Every label has at most `b` vertices. -/
def LB (b : ℕ) : CT → Prop
  | node S _ ks => S.card ≤ b ∧ LBL b ks
def LBL (b : ℕ) : List CT → Prop
  | [] => True
  | k :: ks => LB b k ∧ LBL b ks
end

theorem LBL_iff {b : ℕ} : ∀ {ks : List CT}, LBL b ks ↔ ∀ k ∈ ks, LB b k
  | [] => by simp [LBL]
  | k :: ks => by simp [LBL, LBL_iff (ks := ks)]

theorem LB.kids {b : ℕ} {S : Finset ℕ} {y : List ℕ} {ks : List CT} (h : LB b (node S y ks)) :
    ∀ k ∈ ks, LB b k := LBL_iff.1 h.2

theorem LB.of_good {B : Finset ℕ} : ∀ {t : CT}, Good B t → LB B.card t := by
  intro t
  induction t using CT.ind with
  | h S y ks ih =>
    intro hg
    exact ⟨Finset.card_le_card hg.label_sub, LBL_iff.2 fun k hk => ih k hk (hg.kids k hk)⟩

theorem LB.mono {b b' : ℕ} (h : b ≤ b') : ∀ {t : CT}, LB b t → LB b' t := by
  intro t
  induction t using CT.ind with
  | h S y ks ih =>
    intro hl
    exact ⟨le_trans hl.1 h, LBL_iff.2 fun k hk => ih k hk (hl.kids k hk)⟩

/-! ## `DomC` preserves shape -/

mutual
theorem DomC.leaves_eq : ∀ {a b : CT}, DomC a b → leaves a = leaves b
  | node S y ks, node S' y' ks', h => by
    have hl := DomCL.length_eq h.2.2
    have hs := DomCL.leavesL_eq h.2.2
    simp only [leaves]
    have : ks.isEmpty = ks'.isEmpty := by
      cases ks <;> cases ks' <;> simp_all
    rw [this, hs]
theorem DomCL.leavesL_eq : ∀ {a b : List CT}, DomCL a b → leavesL a = leavesL b
  | [], [], _ => rfl
  | k :: ks, k' :: ks', h => by simp only [leavesL, DomC.leaves_eq h.1, DomCL.leavesL_eq h.2]
end

mutual
theorem DomC.LB_iff : ∀ {a c : CT} {b : ℕ}, DomC a c → (LB b a ↔ LB b c)
  | node S y ks, node S' y' ks', b, h => by
    simp only [LB]
    rw [h.1, DomCL.LBL_iff h.2.2]
theorem DomCL.LBL_iff : ∀ {a c : List CT} {b : ℕ}, DomCL a c → (LBL b a ↔ LBL b c)
  | [], [], _, _ => Iff.rfl
  | k :: ks, k' :: ks', b, h => by
    simp only [LBL]
    rw [DomC.LB_iff h.1, DomCL.LBL_iff h.2]
end

/-! ## leaves -/

theorem leaves_le_of_mem {S : Finset ℕ} {y : List ℕ} {ks : List CT} {k : CT} (hk : k ∈ ks) :
    leaves k ≤ leaves (node S y ks) := by
  have hne : ks ≠ [] := List.ne_nil_of_mem hk
  rw [leaves_node_ne_nil _ _ _ hne]
  have : ∀ ks' : List CT, k ∈ ks' → leaves k ≤ leavesL ks' := by
    intro ks'
    induction ks' with
    | nil => simp
    | cons a l ih =>
      intro h
      simp only [leavesL]
      rcases List.mem_cons.1 h with rfl | h
      · omega
      · have := ih h; omega
  exact this ks hk

theorem leavesL_le_leaves (S : Finset ℕ) (y : List ℕ) (ks : List CT) : leavesL ks ≤ leaves (node S y ks) := by
  by_cases h : ks = []
  · subst h; simp [leavesL]
  · rw [leaves_node_ne_nil _ _ _ h]

/-- **A well-formed characteristic has at most `|B| + 1` leaf runs.** -/
theorem Wf.leaves_le {B : Finset ℕ} {kmax : ℕ} {t : CT} (h : Wf B kmax t) : leaves t ≤ B.card + 1 := by
  by_cases hk : t.kids = []
  · have : leaves t = 1 := by
      cases t with
      | node S y ks => simp only [kids] at hk; subst hk; exact leaves_node_nil _ _
    omega
  · have := leaves_le_of_kids_ne_nil (B := B) t h.good h.conn hk
    have h2 : (t.verts \ t.S).card ≤ B.card := by
      rw [← h.verts_eq]; exact Finset.card_le_card Finset.sdiff_subset
    omega

/-! ## `wcost ≤ leaves` -/

mutual
theorem wcost_le_leaves (v : ℕ) : ∀ (lo : ℕ) (t : CT), ∀ x ∈ winPlans v lo t, wcost x.1 ≤ leaves t
  | lo, node S y ks, x, hx => by
    simp only [winPlans, List.mem_append, List.mem_map] at hx
    rcases hx with (⟨f, _, rfl⟩ | ⟨f, _, rfl⟩) | ⟨combo, hcombo, rfl⟩
    · simp only [wcost]; exact leaves_pos _
    · simp only [wcost]; exact leaves_pos _
    · simp only [wcost]
      exact le_trans (kidChoices_wcost_le v ks combo hcombo) (leavesL_le_leaves S y ks)
theorem kidChoices_wcost_le (v : ℕ) : ∀ (ks : List CT), ∀ combo ∈ kidChoices v ks,
    wcostL (combo.map (·.1)) ≤ leavesL ks
  | [], combo, h => by
    simp only [kidChoices, List.mem_singleton] at h; subst h; simp [wcostL, leavesL]
  | k :: ks, combo, h => by
    simp only [kidChoices, List.mem_flatMap, List.mem_map] at h
    obtain ⟨o, ho, combo', hcombo', rfl⟩ := h
    have h1 := kidChoices_wcost_le v ks combo' hcombo'
    have h2 : wcostO o.1 ≤ leaves k := by
      rcases List.mem_cons.1 ho with rfl | ho
      · simp [wcostO]
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
        simpa [wcostO] using wcost_le_leaves v 0 k p hp
    simp only [List.map_cons, wcostL, leavesL]
    omega
end

theorem chainsGo_chain_length_le (cands : List (Finset ℕ)) : ∀ (fuel : ℕ) (bound : Finset ℕ)
    (chain : List (Finset ℕ)), ∀ x ∈ chainsGo cands fuel bound chain, x.1.length ≤ chain.length + fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro bound chain x hx
    simp only [chainsGo, List.mem_map] at hx
    obtain ⟨M, _, rfl⟩ := hx
    simp
  | succ f ih =>
    intro bound chain x hx
    simp only [chainsGo, List.mem_append, List.mem_map, List.mem_flatMap] at hx
    rcases hx with ⟨M, _, rfl⟩ | ⟨X, _, hx⟩
    · simp
    · have := ih X (chain ++ [X]) x hx
      simp only [List.length_append, List.length_singleton] at this
      omega

theorem allChains_chain_length_le (S N : Finset ℕ) : ∀ x ∈ allChains S N, x.1.length ≤ S.card + 1 := by
  intro x hx
  unfold allChains at hx
  have := chainsGo_chain_length_le _ _ _ _ x hx
  simpa using this

theorem planCost_wtop_le (v : ℕ) (t : CT) : ∀ x ∈ wtopPlans v t, planCost x.1 ≤ leaves t + 1 := by
  intro x hx
  cases t with
  | node S y ks =>
    simp only [wtopPlans, List.mem_append, List.mem_map, List.mem_flatMap] at hx
    rcases hx with (⟨p, hp, rfl⟩ | ⟨f, _, p, hp, rfl⟩) | ⟨f, _, p, hp, rfl⟩
    · have := wcost_le_leaves v 0 _ p hp
      simp only [planCost]; simp; omega
    · have := wcost_le_leaves v f _ p hp
      simp only [planCost]; simp; omega
    · have := wcost_le_leaves v (f + 1) _ p hp
      simp only [planCost]; simp; omega

theorem planCost_att_le (v : ℕ) (N : Finset ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    ∀ x ∈ attachPlans v N (node S y ks), planCost x.1 ≤ S.card + 3 := by
  intro x hx
  simp only [attachPlans, List.mem_flatMap, List.mem_cons, List.mem_append, List.mem_map] at hx
  obtain ⟨⟨chain, M⟩, hcm, hx⟩ := hx
  have hc := allChains_chain_length_le S N _ hcm
  simp only at hc
  rcases hx with (rfl | ⟨f, _, rfl⟩) | ⟨f, _, rfl⟩ <;> simp only [planCost] <;> simp <;> omega

theorem introKids_planCost_le (v : ℕ) (N S : Finset ℕ) (y : List ℕ) (U : ℕ) :
    ∀ (ks pre : List CT), (∀ k ∈ ks, ∀ x ∈ introPlans v N k, planCost x.2.1 ≤ U) →
      ∀ x ∈ introKids v N S y pre ks, planCost x.2.1 ≤ U
  | [], _, _, x, hx => by simp [introKids] at hx
  | k :: post, pre, h, x, hx => by
    simp only [introKids, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨r, hr, rfl⟩ | hx
    · exact h k (by simp) r hr
    · exact introKids_planCost_le v N S y U post (pre ++ [k]) (fun k' hk' => h k' (List.mem_cons_of_mem _ hk')) x hx

/-- **The plans of `introPlans` are cheap.** -/
theorem planCost_le_of_mem_introPlans (v : ℕ) (N : Finset ℕ) {b : ℕ} :
    ∀ (T : CT), LB b T → ∀ x ∈ introPlans v N T, planCost x.2.1 ≤ leaves T + b + 3 := by
  intro T
  induction T using CT.ind with
  | h S y ks ih =>
    intro hl x hx
    simp only [introPlans, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    rcases hx with (⟨p, ⟨hp, -⟩, rfl⟩ | hx) | hx
    · have := planCost_wtop_le v (node S y ks) p hp
      simp only; omega
    · split_ifs at hx
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        have := planCost_att_le v N S y ks p hp
        have := hl.1
        simp only; omega
      · simp at hx
    · refine introKids_planCost_le v N S y _ ks [] ?_ x hx
      intro k hk x' hx'
      have := ih k hk (hl.kids k hk) x' hx'
      have := leaves_le_of_mem (S := S) (y := y) hk
      omega

end CT

end Lax117284Proofs.Treewidth.Chars
