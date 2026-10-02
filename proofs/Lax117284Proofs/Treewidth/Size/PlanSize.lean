import Lax117284Proofs.Treewidth.Size.Cells
import Lax117284Proofs.Treewidth.Size.RealC

/-!
# Size bounds (WP P1), part 12: the size of the (un-normalised) results of `introPlans`

If every run of `t` has at most `b` label vertices and at most `Y ≥ 1` sequence entries then every result `r` of
`introPlans v N t` satisfies `RB (b+1) Y r` and `count r ≤ 2·count t + b + 4`, hence
`vsz r + 1 ≤ (2·count t + b + 4)(2b + 2Y + 8)` (`introPlans_vsz_le`).  This is the size of the input of the `norm` call
inside `introC`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

namespace CT

theorem RB.mono {b b' Y Y' : ℕ} (hb : b ≤ b') (hY : Y ≤ Y') : ∀ {t : CT}, RB b Y t → RB b' Y' t := by
  intro t
  induction t using CT.ind with
  | h S y ks ih =>
    intro h
    exact ⟨le_trans h.1 hb, le_trans h.2.1 hY, RBL_iff.2 fun k hk => ih k hk (h.kids k hk)⟩

theorem countL_append (a b : List CT) : countL (a ++ b) = countL a + countL b := by
  induction a with
  | nil => simp [countL]
  | cons k a ih => simp [countL, ih]; omega

theorem RBL_append {b Y : ℕ} {a c : List CT} : RBL b Y (a ++ c) ↔ RBL b Y a ∧ RBL b Y c := by
  simp only [RBL_iff, List.mem_append]
  constructor
  · intro h; exact ⟨fun k hk => h k (Or.inl hk), fun k hk => h k (Or.inr hk)⟩
  · rintro ⟨h1, h2⟩ k (hk | hk)
    · exact h1 k hk
    · exact h2 k hk

/-! ## chains -/

theorem mem_chainCands_sub {S N : Finset ℕ} (hN : N ⊆ S) {X : Finset ℕ} (hX : X ∈ chainCands S N) : X ⊆ S := by
  unfold chainCands at hX
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hX
  intro x hx
  rcases Finset.mem_union.1 hx with hx | hx
  · exact hN hx
  · have := (List.mem_sublists.1 hc).subset (List.mem_toFinset.1 hx)
    exact (Finset.mem_sdiff.1 ((Finset.mem_sort _).1 this)).1

theorem chainsGo_sub (cands : List (Finset ℕ)) : ∀ (fuel : ℕ) (bound : Finset ℕ) (chain : List (Finset ℕ)),
    ∀ x ∈ chainsGo cands fuel bound chain, x.2 ⊆ bound ∧ ∀ X ∈ x.1, X ∈ chain ∨ X ⊆ bound := by
  intro fuel
  induction fuel with
  | zero =>
    intro bound chain x hx
    simp only [chainsGo, List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    obtain ⟨M, ⟨-, hM⟩, rfl⟩ := hx
    exact ⟨hM, fun X hX => Or.inl hX⟩
  | succ f ih =>
    intro bound chain x hx
    simp only [chainsGo, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_filter, decide_eq_true_eq,
      Bool.and_eq_true, Bool.or_eq_true] at hx
    rcases hx with ⟨M, ⟨-, hM⟩, rfl⟩ | ⟨X, ⟨-, hXb, -⟩, hx⟩
    · exact ⟨hM, fun X hX => Or.inl hX⟩
    · obtain ⟨h1, h2⟩ := ih X (chain ++ [X]) x hx
      refine ⟨h1.trans hXb, fun Y hY => ?_⟩
      rcases h2 Y hY with hY | hY
      · rcases List.mem_append.1 hY with hY | hY
        · exact Or.inl hY
        · right; rw [List.mem_singleton.1 hY]; exact hXb
      · right; exact hY.trans hXb

theorem allChains_sub (S N : Finset ℕ) : ∀ x ∈ allChains S N, x.2 ⊆ S ∧ ∀ X ∈ x.1, X ⊆ S := by
  intro x hx
  unfold allChains at hx
  obtain ⟨h1, h2⟩ := chainsGo_sub _ _ _ _ x hx
  exact ⟨h1, fun X hX => by rcases h2 X hX with h | h <;> simp_all⟩

theorem pathSubtree_RB {v : ℕ} {S : Finset ℕ} {b Y : ℕ} (hY : 1 ≤ Y) (hS : S.card ≤ b) :
    ∀ (chain : List (Finset ℕ)) (M : Finset ℕ), (∀ X ∈ chain, X ⊆ S) → M ⊆ S →
      RB (b + 1) Y (pathSubtree v chain M) ∧ count (pathSubtree v chain M) = chain.length + 1
  | [], M, _, hM => by
    have h1 : (insert v M).card ≤ b + 1 :=
      le_trans (Finset.card_insert_le _ _) (by have := Finset.card_le_card hM; omega)
    have : pathSubtree v [] M = node (insert v M) [M.card + 1] [] := by simp [pathSubtree]
    rw [this]
    exact ⟨⟨h1, by simpa using hY, trivial⟩, by simp [count, countL]⟩
  | X :: chain, M, hX, hM => by
    have ih := pathSubtree_RB (v := v) hY hS chain M (fun Z hZ => hX Z (List.mem_cons_of_mem _ hZ)) hM
    have hXS := hX X (by simp)
    have : pathSubtree v (X :: chain) M = node X [X.card] [pathSubtree v chain M] := by simp [pathSubtree]
    rw [this]
    refine ⟨⟨by have := Finset.card_le_card hXS; omega, by simpa using hY, ?_⟩, ?_⟩
    · exact ⟨ih.1, trivial⟩
    · simp only [count, countL, ih.2]; simp; omega

theorem RBL.mono {b b' Y Y' : ℕ} (hb : b ≤ b') (hY : Y ≤ Y') {ks : List CT} (h : RBL b Y ks) : RBL b' Y' ks :=
  RBL_iff.2 fun k hk => ((RBL_iff.1 h) k hk).mono hb hY

/-! ## region plans -/

mutual
theorem winPlans_res_rec (v : ℕ) {b Y : ℕ} : ∀ (lo : ℕ) (t : CT), RB b Y t →
    ∀ x ∈ winPlans v lo t, RB (b + 1) Y x.2.1 ∧ count x.2.1 ≤ 2 * count t
  | lo, node S y ks, ht, x, hx => by
    obtain ⟨hS, hy, hks⟩ := ht
    have hk : ∀ k ∈ ks, RB b Y k := RBL_iff.1 hks
    have hcnt := count_pos (node S y ks)
    have hks1 : RBL (b + 1) Y ks := hks.mono (by omega) le_rfl
    have hins : (insert v S).card ≤ b + 1 := le_trans (Finset.card_insert_le _ _) (by omega)
    have hcs : count (node S y ks) = 1 + countL ks := rfl
    simp only [winPlans, List.mem_append, List.mem_map] at hx
    rcases hx with (⟨f, _, rfl⟩ | ⟨f, _, rfl⟩) | ⟨combo, hcombo, rfl⟩
    · refine ⟨⟨hins, ?_, ⟨by omega, ?_, hks1⟩, trivial⟩, ?_⟩
      · simp only [plus1, List.length_map, List.length_drop, List.length_take]; omega
      · simp only [List.length_drop]; omega
      · simp only [count, countL]; omega
    · refine ⟨⟨hins, ?_, ⟨by omega, ?_, hks1⟩, trivial⟩, ?_⟩
      · simp only [plus1, List.length_map, List.length_drop, List.length_take]; omega
      · simp only [List.length_drop]; omega
      · simp only [count, countL]; omega
    · obtain ⟨h1, h2⟩ := kidChoices_res_rec v ks hk combo hcombo
      refine ⟨⟨hins, ?_, RBL_iff.2 ?_⟩, ?_⟩
      · simp only [plus1, List.length_map, List.length_drop]; omega
      · intro k' hk'
        obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hk'
        exact h1 o ho
      · simp only [count]
        omega
theorem kidChoices_res_rec (v : ℕ) {b Y : ℕ} : ∀ (ks : List CT), (∀ k ∈ ks, RB b Y k) →
    ∀ combo ∈ kidChoices v ks, (∀ o ∈ combo, RB (b + 1) Y o.2.1) ∧ countL (combo.map (·.2.1)) ≤ 2 * countL ks
  | [], _, combo, h => by
    simp only [kidChoices, List.mem_singleton] at h; subst h; simp [countL]
  | k :: ks, hk, combo, h => by
    simp only [kidChoices, List.mem_flatMap, List.mem_map] at h
    obtain ⟨o, ho, combo', hcombo', rfl⟩ := h
    obtain ⟨h1, h2⟩ := kidChoices_res_rec v ks (fun k' hk' => hk k' (List.mem_cons_of_mem _ hk')) combo' hcombo'
    have hk0 := hk k (by simp)
    have ho' : RB (b + 1) Y o.2.1 ∧ count o.2.1 ≤ 2 * count k := by
      rcases List.mem_cons.1 ho with rfl | ho
      · exact ⟨hk0.mono (by omega) le_rfl, by simp only []; omega⟩
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
        exact winPlans_res_rec v 0 k hk0 p hp
    refine ⟨?_, ?_⟩
    · intro o' hmem
      rcases List.mem_cons.1 hmem with rfl | hmem
      · exact ho'.1
      · exact h1 o' hmem
    · simp only [List.map_cons, countL]
      have := ho'.2
      omega
end

theorem winPlans_res_pair : (type_of% @winPlans_res_rec) ∧ (type_of% @kidChoices_res_rec) :=
  ⟨@winPlans_res_rec, @kidChoices_res_rec⟩

theorem winPlans_res : type_of% @winPlans_res_rec := winPlans_res_pair.1

theorem wtopPlans_res (v : ℕ) {b Y : ℕ} {t : CT} (ht : RB b Y t) :
    ∀ x ∈ wtopPlans v t, RB (b + 1) Y x.2.1 ∧ count x.2.1 ≤ 2 * count t + 1 := by
  intro x hx
  cases t with
  | node S y ks =>
    have ht' := ht
    obtain ⟨hS, hy, hks⟩ := ht
    have hcnt := count_pos (node S y ks)
    simp only [wtopPlans, List.mem_append, List.mem_map, List.mem_flatMap] at hx
    rcases hx with (⟨p, hp, rfl⟩ | ⟨f, _, p, hp, rfl⟩) | ⟨f, _, p, hp, rfl⟩
    · have := winPlans_res v 0 _ ht' p hp
      exact ⟨this.1, le_trans this.2 (by omega)⟩
    · have := winPlans_res v f _ ht' p hp
      refine ⟨⟨by omega, ?_, this.1, trivial⟩, ?_⟩
      · simp only [List.length_take]; omega
      · have := this.2
        simp only [count, countL] at this ⊢
        omega
    · have := winPlans_res v (f + 1) _ ht' p hp
      refine ⟨⟨by omega, ?_, this.1, trivial⟩, ?_⟩
      · simp only [List.length_take]; omega
      · have := this.2
        simp only [count, countL] at this ⊢
        omega

theorem attachPlans_res (v : ℕ) (N : Finset ℕ) {b Y : ℕ} (hY : 1 ≤ Y) {S : Finset ℕ} {y : List ℕ} {ks : List CT}
    (hN : N ⊆ S) (ht : RB b Y (node S y ks)) :
    ∀ x ∈ attachPlans v N (node S y ks), RB (b + 1) Y x.2 ∧ count x.2 ≤ count (node S y ks) + b + 4 := by
  intro x hx
  obtain ⟨hS, hy, hks⟩ := ht
  have hks1 : RBL (b + 1) Y ks := hks.mono (by omega) le_rfl
  simp only [attachPlans, List.mem_flatMap, List.mem_cons, List.mem_append, List.mem_map] at hx
  obtain ⟨⟨chain, M⟩, hcm, hx⟩ := hx
  obtain ⟨hM, hch⟩ := allChains_sub S N _ hcm
  have hlen := allChains_chain_length_le S N _ hcm
  simp only at hM hch hlen
  obtain ⟨hbr, hbc⟩ := pathSubtree_RB (v := v) hY hS chain M hch hM
  have hcs : count (node S y ks) = 1 + countL ks := rfl
  rcases hx with (rfl | ⟨f, _, rfl⟩) | ⟨f, _, rfl⟩
  · refine ⟨⟨by omega, hy, RBL_append.2 ⟨hks1, ⟨hbr, trivial⟩⟩⟩, ?_⟩
    simp only [count, countL_append, countL]
    omega
  · refine ⟨⟨by omega, ?_, hbr, ⟨by omega, ?_, hks1⟩, trivial⟩, ?_⟩
    · simp only [List.length_take]; omega
    · simp only [List.length_drop]; omega
    · simp only [count, countL]; omega
  · refine ⟨⟨by omega, ?_, hbr, ⟨by omega, ?_, hks1⟩, trivial⟩, ?_⟩
    · simp only [List.length_take]; omega
    · simp only [List.length_drop]; omega
    · simp only [count, countL]; omega

theorem introKids_res (v : ℕ) (N S : Finset ℕ) (y : List ℕ) {b Y : ℕ} (hS : S.card ≤ b) (hy : y.length ≤ Y) :
    ∀ (ks pre : List CT), RBL b Y pre → (∀ k ∈ ks, RB b Y k) →
      (∀ k ∈ ks, ∀ x ∈ introPlans v N k, RB (b + 1) Y x.2.2 ∧ count x.2.2 ≤ 2 * count k + b + 4) →
      ∀ x ∈ introKids v N S y pre ks, RB (b + 1) Y x.2.2 ∧
        count x.2.2 ≤ 2 * (1 + countL pre + countL ks) + b + 4
  | [], _, _, _, _, x, hx => by simp [introKids] at hx
  | k :: post, pre, hpre, hk, ih, x, hx => by
    simp only [introKids, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨r, hr, rfl⟩ | hx
    · obtain ⟨h1, h2⟩ := ih k (by simp) r hr
      have hpost : RBL b Y post := RBL_iff.2 fun k' hk' => hk k' (List.mem_cons_of_mem _ hk')
      refine ⟨⟨by omega, hy, RBL_append.2 ⟨hpre.mono (by omega) le_rfl, h1, hpost.mono (by omega) le_rfl⟩⟩, ?_⟩
      simp only [count, countL_append, countL]
      omega
    · have hk' : RB b Y k := hk k (by simp)
      have := introKids_res v N S y hS hy post (pre ++ [k]) (RBL_append.2 ⟨hpre, hk', trivial⟩)
        (fun k' hk'' => hk k' (List.mem_cons_of_mem _ hk''))
        (fun k' hk'' => ih k' (List.mem_cons_of_mem _ hk''))
        x hx
      refine ⟨this.1, ?_⟩
      have h3 := this.2
      simp only [countL_append, countL] at h3 ⊢
      omega

/-- **The size of the plans' results.** -/
theorem introPlans_res (v : ℕ) (N : Finset ℕ) {b Y : ℕ} (hY : 1 ≤ Y) :
    ∀ (t : CT), RB b Y t → ∀ x ∈ introPlans v N t, RB (b + 1) Y x.2.2 ∧ count x.2.2 ≤ 2 * count t + b + 4 := by
  intro t
  induction t using CT.ind with
  | h S y ks ih =>
    intro ht x hx
    have hcnt := count_pos (node S y ks)
    have hcs : count (node S y ks) = 1 + countL ks := rfl
    have ht' := ht
    obtain ⟨hS, hy, hks⟩ := ht
    have hk : ∀ k ∈ ks, RB b Y k := RBL_iff.1 hks
    simp only [introPlans, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    rcases hx with (⟨p, ⟨hp, -⟩, rfl⟩ | hx) | hx
    · have := wtopPlans_res v (b := b) (Y := Y) ht' p hp
      exact ⟨this.1, by simp only []; omega⟩
    · split_ifs at hx with hN
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        have := attachPlans_res v N (b := b) (Y := Y) hY hN ht' p hp
        exact ⟨this.1, by simp only []; omega⟩
      · simp at hx
    · have := introKids_res v N S y hS hy ks [] trivial hk (fun k hk' => ih k hk' (hk k hk')) x hx
      refine ⟨this.1, ?_⟩
      have h3 := this.2
      simp only [countL] at h3
      omega

/-- The size of the input of the `norm` call of `introC`. -/
theorem introPlans_vsz_le (v : ℕ) (N : Finset ℕ) {B : Finset ℕ} {kmax : ℕ} {t : CT} (ht : Wf B kmax t) :
    ∀ x ∈ introPlans v N t, x.2.2.vsz ≤ (2 * runBound B.card + B.card + 4) * (2 * B.card + 4 * kmax + 10) := by
  intro x hx
  have hb := RB.of_good ht.good ht.bounded
  obtain ⟨h1, h2⟩ := introPlans_res v N (b := B.card) (Y := 2 * kmax + 1) (by omega) t hb x hx
  have h3 := count_mul_le h1
  have h4 : count x.2.2 ≤ 2 * runBound B.card + B.card + 4 := by
    have := ht.count_le; omega
  calc x.2.2.vsz ≤ count x.2.2 * (2 * (B.card + 1) + 2 * (2 * kmax + 1) + 6) := h3
    _ ≤ _ := Nat.mul_le_mul h4 (by omega)

/-! ## the size of the plans themselves -/

mutual
/-- Number of constructors of a region plan (`none` counts one). -/
def wsz : WPlan → ℕ
  | .endAt _ => 1
  | .whole ps => 1 + wszL ps
def wszL : List (Option WPlan) → ℕ
  | [] => 0
  | p :: ps => wszO p + wszL ps
def wszO : Option WPlan → ℕ
  | none => 1
  | some p => wsz p
end

mutual
theorem winPlans_wsz_le_rec (v : ℕ) : ∀ (lo : ℕ) (t : CT), ∀ x ∈ winPlans v lo t, wsz x.1 ≤ 2 * count t
  | lo, node S y ks, x, hx => by
    have hc := count_pos (node S y ks)
    simp only [winPlans, List.mem_append, List.mem_map] at hx
    rcases hx with (⟨f, _, rfl⟩ | ⟨f, _, rfl⟩) | ⟨combo, hcombo, rfl⟩
    · simp only [wsz]; omega
    · simp only [wsz]; omega
    · have := kidChoices_wsz_le_rec v ks combo hcombo
      simp only [wsz, count]
      omega
theorem kidChoices_wsz_le_rec (v : ℕ) : ∀ (ks : List CT), ∀ combo ∈ kidChoices v ks,
    wszL (combo.map (·.1)) ≤ 2 * countL ks
  | [], combo, h => by
    simp only [kidChoices, List.mem_singleton] at h; subst h; simp [wszL, countL]
  | k :: ks, combo, h => by
    simp only [kidChoices, List.mem_flatMap, List.mem_map] at h
    obtain ⟨o, ho, combo', hcombo', rfl⟩ := h
    have h1 := kidChoices_wsz_le_rec v ks combo' hcombo'
    have hk := count_pos k
    have h2 : wszO o.1 ≤ 2 * count k := by
      rcases List.mem_cons.1 ho with rfl | ho
      · simp [wszO]; omega
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
        simpa [wszO] using winPlans_wsz_le_rec v 0 k p hp
    simp only [List.map_cons, wszL, countL]
    omega
end

theorem winPlans_wsz_le_pair : (type_of% @winPlans_wsz_le_rec) ∧ (type_of% @kidChoices_wsz_le_rec) :=
  ⟨@winPlans_wsz_le_rec, @kidChoices_wsz_le_rec⟩

/-- A region plan of `winPlans v lo t` has at most `2 · count t` constructors. -/
theorem winPlans_wsz_le : type_of% @winPlans_wsz_le_rec := winPlans_wsz_le_pair.1

/-- The path to the run of a plan is shorter than the number of runs. -/
theorem introPlans_path_le (v : ℕ) (N : Finset ℕ) : ∀ (t : CT), ∀ x ∈ introPlans v N t, x.1.length < count t := by
  intro t
  induction t using CT.ind with
  | h S y ks ih =>
    intro x hx
    have hc : count (node S y ks) = 1 + countL ks := rfl
    simp only [introPlans, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    have hkid : ∀ (pre ks' : List CT), (∀ k ∈ ks', ∀ x ∈ introPlans v N k, x.1.length < count k) →
        ∀ x ∈ introKids v N S y pre ks', x.1.length < 1 + countL ks' := by
      intro pre ks'
      induction ks' generalizing pre with
      | nil => intro _ x hx; simp [introKids] at hx
      | cons k post ihk =>
        intro h x hx
        simp only [introKids, List.mem_append, List.mem_map] at hx
        simp only [countL]
        rcases hx with ⟨r, hr, rfl⟩ | hx
        · have := h k (by simp) r hr
          simp only [List.length_cons]
          have := count_pos k
          omega
        · have := ihk (pre ++ [k]) (fun k' hk' => h k' (List.mem_cons_of_mem _ hk')) x hx
          omega
    rcases hx with (⟨p, _, rfl⟩ | hx) | hx
    · simp only [List.length_nil]; omega
    · split_ifs at hx
      · obtain ⟨p, _, rfl⟩ := List.mem_map.1 hx
        simp only [List.length_nil]; omega
      · simp at hx
    · have := hkid [] ks (fun k hk x hx => ih k hk x hx) x hx
      omega

end CT

end Lax117284Proofs.Treewidth.Chars
