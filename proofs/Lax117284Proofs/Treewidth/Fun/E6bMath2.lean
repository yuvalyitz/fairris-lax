import Lax117284Proofs.Treewidth.Fun.E6bMath1

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6b (4): mathematics of the extraction cost analysis, part 2

Run sequences of the *un-normalised* results of `introPlans` (the inputs of `norm` and `domCB` in `realIntro`) have entries
`≤ maxEntry t + 1` (a region gets the new vertex) or `≤ b + 1` (a new branch: `M ∪ {v}`), so their run sequences have length
`≤ 2 K + 1`, and the plans themselves have size polynomial in `count t` and `b`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT

/-- `node S y ks` has `maxEntry + 1 ≤ K` iff entries and kids are `≤ K - 1` -/
theorem me_succ_iff {S : Finset ℕ} {y : List ℕ} {ks : List CT} {K : ℕ} :
    maxEntry (node S y ks) + 1 ≤ K ↔ K ≥ 1 ∧ (∀ e ∈ y, e + 1 ≤ K) ∧ ∀ k ∈ ks, maxEntry k + 1 ≤ K := by
  constructor
  · intro h
    have h' : maxEntry (node S y ks) ≤ K - 1 := by omega
    obtain ⟨h1, h2⟩ := maxEntry_le_iff.1 h'
    exact ⟨by omega, fun e he => by have := h1 e he; omega, fun k hk => by have := h2 k hk; omega⟩
  · rintro ⟨hK, h1, h2⟩
    have : maxEntry (node S y ks) ≤ K - 1 :=
      maxEntry_le_iff.2 ⟨fun e he => by have := h1 e he; omega, fun k hk => by have := h2 k hk; omega⟩
    omega

mutual
theorem winPlans_me (v : ℕ) {K : ℕ} : ∀ (lo : ℕ) (t : CT), maxEntry t + 1 ≤ K →
    ∀ x ∈ winPlans v lo t, maxEntry x.2.1 ≤ K
  | lo, node S y ks, ht, x, hx => by
    obtain ⟨hK, hy, hks⟩ := me_succ_iff.1 ht
    have hnode : ∀ (y' : List ℕ) (ks' : List CT), (∀ e ∈ y', e ≤ K) → (∀ k ∈ ks', maxEntry k ≤ K) →
        ∀ S', maxEntry (node S' y' ks') ≤ K := fun y' ks' h1 h2 S' => maxEntry_le_iff.2 ⟨h1, h2⟩
    have hks' : ∀ k ∈ ks, maxEntry k ≤ K := fun k hk => by have := hks k hk; omega
    have hy' : ∀ e ∈ y, e ≤ K := fun e he => by have := hy e he; omega
    have hp1 : ∀ (z : List ℕ), (∀ e ∈ z, e ∈ y) → ∀ e ∈ plus1 z, e ≤ K := by
      intro z hz e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      exact hy e0 (hz e0 he0)
    have hdrop : ∀ n, ∀ e ∈ y.drop n, e ∈ y := fun n e he => List.mem_of_mem_drop he
    have hsl : ∀ n m, ∀ e ∈ (y.take n).drop m, e ∈ y := fun n m e he =>
      List.mem_of_mem_take (List.mem_of_mem_drop he)
    simp only [winPlans, List.mem_append, List.mem_map] at hx
    rcases hx with (⟨f, _, rfl⟩ | ⟨f, _, rfl⟩) | ⟨combo, hcombo, rfl⟩
    · refine hnode _ _ (hp1 _ (hsl _ _)) ?_ _
      intro k hk
      simp only [List.mem_singleton] at hk; subst hk
      exact hnode _ _ (fun e he => hy' e (hdrop _ e he)) hks' _
    · refine hnode _ _ (hp1 _ (hsl _ _)) ?_ _
      intro k hk
      simp only [List.mem_singleton] at hk; subst hk
      exact hnode _ _ (fun e he => hy' e (hdrop _ e he)) hks' _
    · have := kidChoices_me v ks hks combo hcombo
      refine hnode _ _ (hp1 _ (fun e he => hdrop _ e he)) ?_ _
      intro k hk
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hk
      exact this o ho
theorem kidChoices_me (v : ℕ) {K : ℕ} : ∀ (ks : List CT), (∀ k ∈ ks, maxEntry k + 1 ≤ K) →
    ∀ combo ∈ kidChoices v ks, ∀ o ∈ combo, maxEntry o.2.1 ≤ K
  | [], _, combo, h => by
    simp only [kidChoices, List.mem_singleton] at h; subst h; simp
  | k :: ks, hk, combo, h => by
    simp only [kidChoices, List.mem_flatMap, List.mem_map] at h
    obtain ⟨o, ho, combo', hcombo', rfl⟩ := h
    have ih := kidChoices_me v ks (fun k' hk' => hk k' (List.mem_cons_of_mem _ hk')) combo' hcombo'
    have hk0 := hk k (by simp)
    have ho' : maxEntry o.2.1 ≤ K := by
      rcases List.mem_cons.1 ho with rfl | ho
      · simp only []; omega
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
        exact winPlans_me v 0 k hk0 p hp
    intro o' hmem
    rcases List.mem_cons.1 hmem with rfl | hmem
    · exact ho'
    · exact ih o' hmem
end

theorem wtopPlans_me (v : ℕ) {K : ℕ} {t : CT} (ht : maxEntry t + 1 ≤ K) :
    ∀ x ∈ wtopPlans v t, maxEntry x.2.1 ≤ K := by
  intro x hx
  cases t with
  | node S y ks =>
    obtain ⟨hK, hy, hks⟩ := me_succ_iff.1 ht
    simp only [wtopPlans, List.mem_append, List.mem_map, List.mem_flatMap] at hx
    rcases hx with (⟨p, hp, rfl⟩ | ⟨f, _, p, hp, rfl⟩) | ⟨f, _, p, hp, rfl⟩
    · exact winPlans_me v 0 _ ht p hp
    · have := winPlans_me v f _ ht p hp
      refine maxEntry_le_iff.2 ⟨fun e he => ?_, ?_⟩
      · have := hy e (List.mem_of_mem_take he); omega
      · intro k hk; simp only [List.mem_singleton] at hk; subst hk; exact this
    · have := winPlans_me v (f + 1) _ ht p hp
      refine maxEntry_le_iff.2 ⟨fun e he => ?_, ?_⟩
      · have := hy e (List.mem_of_mem_take he); omega
      · intro k hk; simp only [List.mem_singleton] at hk; subst hk; exact this

theorem pathSubtree_me {v : ℕ} {S : Finset ℕ} {b : ℕ} (hS : S.card ≤ b) :
    ∀ (chain : List (Finset ℕ)) (M : Finset ℕ), (∀ X ∈ chain, X ⊆ S) → M ⊆ S →
      maxEntry (pathSubtree v chain M) ≤ b + 1
  | [], M, _, hM => by
    have : pathSubtree v [] M = node (insert v M) [M.card + 1] [] := by simp [pathSubtree]
    rw [this]
    refine maxEntry_le_iff.2 ⟨fun e he => ?_, by simp⟩
    simp only [List.mem_singleton] at he; subst he
    have := Finset.card_le_card hM; omega
  | X :: chain, M, hX, hM => by
    have ih := pathSubtree_me (v := v) hS chain M (fun Z hZ => hX Z (List.mem_cons_of_mem _ hZ)) hM
    have hXS := hX X (by simp)
    have : pathSubtree v (X :: chain) M = node X [X.card] [pathSubtree v chain M] := by simp [pathSubtree]
    rw [this]
    refine maxEntry_le_iff.2 ⟨fun e he => ?_, fun k hk => ?_⟩
    · simp only [List.mem_singleton] at he; subst he
      have := Finset.card_le_card hXS; omega
    · simp only [List.mem_singleton] at hk; subst hk; exact ih

theorem attachPlans_me (v : ℕ) (N : Finset ℕ) {b K : ℕ} {S : Finset ℕ} {y : List ℕ} {ks : List CT}
    (hS : S.card ≤ b) (ht : maxEntry (node S y ks) ≤ K) (hb : b + 1 ≤ K) :
    ∀ x ∈ attachPlans v N (node S y ks), maxEntry x.2 ≤ K := by
  intro x hx
  obtain ⟨hy, hks⟩ := maxEntry_le_iff.1 ht
  simp only [attachPlans, List.mem_flatMap, List.mem_cons, List.mem_append, List.mem_map] at hx
  obtain ⟨⟨chain, M⟩, hcm, hx⟩ := hx
  obtain ⟨hM, hch⟩ := allChains_sub S N _ hcm
  simp only at hM hch
  have hbr := pathSubtree_me (v := v) hS chain M hch hM
  have hbr' : maxEntry (pathSubtree v chain M) ≤ K := le_trans hbr hb
  rcases hx with (rfl | ⟨f, _, rfl⟩) | ⟨f, _, rfl⟩
  · refine maxEntry_le_iff.2 ⟨hy, fun k hk => ?_⟩
    rcases List.mem_append.1 hk with hk | hk
    · exact hks k hk
    · simp only [List.mem_singleton] at hk; subst hk; exact hbr'
  · refine maxEntry_le_iff.2 ⟨fun e he => hy e (List.mem_of_mem_take he), fun k hk => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact hbr'
    · exact maxEntry_le_iff.2 ⟨fun e he => hy e (List.mem_of_mem_drop he), hks⟩
  · refine maxEntry_le_iff.2 ⟨fun e he => hy e (List.mem_of_mem_take he), fun k hk => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact hbr'
    · exact maxEntry_le_iff.2 ⟨fun e he => hy e (List.mem_of_mem_drop he), hks⟩

theorem introKids_me (v : ℕ) (N S : Finset ℕ) (y : List ℕ) {K : ℕ} (hy : ∀ e ∈ y, e ≤ K) :
    ∀ (ks pre : List CT), (∀ k ∈ pre, maxEntry k ≤ K) → (∀ k ∈ ks, maxEntry k ≤ K) →
      (∀ k ∈ ks, ∀ x ∈ introPlans v N k, maxEntry x.2.2 ≤ K) →
      ∀ x ∈ introKids v N S y pre ks, maxEntry x.2.2 ≤ K
  | [], _, _, _, _, x, hx => by simp [introKids] at hx
  | c0 :: post, pre, hpre, hk, ih, x, hx => by
    simp only [introKids, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨r, hr, rfl⟩ | hx
    · have h1 := ih c0 (by simp) r hr
      refine maxEntry_le_iff.2 ⟨hy, fun k' hk' => ?_⟩
      simp only [List.mem_append, List.mem_cons] at hk'
      rcases hk' with hk' | rfl | hk'
      · exact hpre k' hk'
      · exact h1
      · exact hk k' (List.mem_cons_of_mem _ hk')
    · exact introKids_me v N S y hy post (pre ++ [c0])
        (fun k' hk' => by
          rcases List.mem_append.1 hk' with h | h
          · exact hpre k' h
          · simp only [List.mem_singleton] at h; rw [h]; exact hk c0 (by simp))
        (fun k' hk' => hk k' (List.mem_cons_of_mem _ hk'))
        (fun k' hk' => ih k' (List.mem_cons_of_mem _ hk')) x hx

/-- the entries of the results of `introPlans`: `≤ K` when `maxEntry t + 1 ≤ K` and the labels have `≤ K - 1` vertices -/
theorem introPlans_me (v : ℕ) (N : Finset ℕ) {b K : ℕ} (hb : b + 1 ≤ K) :
    ∀ t : CT, LB b t → maxEntry t + 1 ≤ K → ∀ x ∈ introPlans v N t, maxEntry x.2.2 ≤ K := by
  intro t
  induction t using CT.ind with
  | h S y ks ih =>
    intro hlb hme x hx
    obtain ⟨hK, hy, hks⟩ := me_succ_iff.1 hme
    have hS : S.card ≤ b := hlb.1
    have hme' : maxEntry (node S y ks) ≤ K := by omega
    simp only [introPlans, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    rcases hx with (⟨p, ⟨hp, -⟩, rfl⟩ | hx) | hx
    · exact wtopPlans_me v hme p hp
    · split_ifs at hx with hN
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        exact attachPlans_me v N hS hme' hb p hp
      · simp at hx
    · refine introKids_me v N S y (fun e he => by have := hy e he; omega) ks [] (by simp)
        (fun k hk => by have := hks k hk; omega) (fun k hk => ?_) x hx
      exact ih k hk (hlb.kids k hk) (hks k hk)

/-! ### sizes of the plans -/

/-- the size bound of a plan (`count t` runs, labels of `≤ b` vertices) -/
def planSzBound (c b : ℕ) : ℕ := 16 * c + (b + 1) * (2 * b + 2) + 2 * b + 11

theorem planSzBound_mono {c c' : ℕ} (b : ℕ) (h : c ≤ c') : planSzBound c b ≤ planSzBound c' b := by
  unfold planSzBound; omega

theorem sz_cut_opt_le (o : Option Cut) : sz o ≤ 5 := by
  cases o with
  | none => simp
  | some c => cases c <;> simp [sz, Val.size]

theorem wtopPlans_plan_sz (v : ℕ) (t : CT) : ∀ x ∈ wtopPlans v t, sz x.1 ≤ 16 * count t + 5 := by
  intro x hx
  cases t with
  | node S y ks =>
    simp only [wtopPlans, List.mem_append, List.mem_map, List.mem_flatMap] at hx
    have key : ∀ (lo : ℕ) (p : WPlan × CT × Finset ℕ), p ∈ winPlans v lo (node S y ks) → ∀ pre : Option Cut,
        sz (Plan.top pre p.1) ≤ 16 * count (node S y ks) + 5 := by
      intro lo p hp pre
      have h1 := winPlans_wsz_le v lo (node S y ks) p hp
      have h2 := sz_wp_le p.1
      have h3 := sz_cut_opt_le pre
      rw [sz_plan_top]; omega
    rcases hx with (⟨p, hp, rfl⟩ | ⟨f, _, p, hp, rfl⟩) | ⟨f, _, p, hp, rfl⟩
    · exact key 0 p hp none
    · exact key f p hp _
    · exact key (f + 1) p hp _

theorem attachPlans_plan_sz (v : ℕ) (N : Finset ℕ) {b : ℕ} {S : Finset ℕ} {y : List ℕ} {ks : List CT}
    (hS : S.card ≤ b) : ∀ x ∈ attachPlans v N (node S y ks), sz x.1 ≤ (b + 1) * (2 * b + 2) + 2 * b + 11 := by
  intro x hx
  simp only [attachPlans, List.mem_flatMap, List.mem_cons, List.mem_append, List.mem_map] at hx
  obtain ⟨⟨chain, M⟩, hcm, hx⟩ := hx
  obtain ⟨hM, hch⟩ := allChains_sub S N _ hcm
  have hlen := allChains_chain_length_le S N _ hcm
  simp only at hM hch hlen
  have hchsz : sz chain ≤ 1 + (b + 1) * (2 * b + 2) := by
    have h1 := sz_list_le (l := chain) (s := 2 * b + 1) (fun X hX => by
      rw [sz_finset]; have := Finset.card_le_card (hch X hX); omega)
    have h2 : chain.length * (2 * b + 1 + 1) ≤ (b + 1) * (2 * b + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hMsz : sz M ≤ 2 * b + 1 := by
    rw [sz_finset]; have := Finset.card_le_card hM; omega
  have key : ∀ c : Option Cut, sz (Plan.att c chain M) ≤ (b + 1) * (2 * b + 2) + 2 * b + 11 := by
    intro c
    have := sz_cut_opt_le c
    rw [sz_plan_att]; omega
  rcases hx with (rfl | ⟨f, _, rfl⟩) | ⟨f, _, rfl⟩
  · exact key none
  · exact key _
  · exact key _

/-- **path and plan of every result of `introPlans` are small** -/
theorem introPlans_plan_sz (v : ℕ) (N : Finset ℕ) {b : ℕ} :
    ∀ t : CT, LB b t → ∀ x ∈ introPlans v N t, sz x.2.1 ≤ planSzBound (count t) b := by
  intro t
  induction t using CT.ind with
  | h S y ks ih =>
    intro hlb x hx
    have hS : S.card ≤ b := hlb.1
    have hcs : count (node S y ks) = 1 + countL ks := rfl
    simp only [introPlans, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    have hkid : ∀ (pre ks' : List CT), (∀ k ∈ ks', LB b k) →
        (∀ k ∈ ks', ∀ x ∈ introPlans v N k, sz x.2.1 ≤ planSzBound (count k) b) →
        ∀ x ∈ introKids v N S y pre ks', sz x.2.1 ≤ planSzBound (countL ks') b := by
      intro pre ks'
      induction ks' generalizing pre with
      | nil => intro _ _ x hx; simp [introKids] at hx
      | cons k post ihk =>
        intro hl h x hx
        simp only [introKids, List.mem_append, List.mem_map] at hx
        simp only [countL]
        rcases hx with ⟨r, hr, rfl⟩ | hx
        · have := h k (by simp) r hr
          refine le_trans this (planSzBound_mono b ?_)
          omega
        · have := ihk (pre ++ [k]) (fun k' hk' => hl k' (List.mem_cons_of_mem _ hk'))
            (fun k' hk' => h k' (List.mem_cons_of_mem _ hk')) x hx
          refine le_trans this (planSzBound_mono b ?_)
          omega
    rcases hx with (⟨p, ⟨hp, -⟩, rfl⟩ | hx) | hx
    · have := wtopPlans_plan_sz v (node S y ks) p hp
      simp only [planSzBound]; omega
    · split_ifs at hx with hN
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        have := attachPlans_plan_sz v N (y := y) (ks := ks) hS p hp
        simp only [planSzBound]; omega
      · simp at hx
    · have := hkid [] ks (fun k hk => hlb.kids k hk) (fun k hk => ih k hk (hlb.kids k hk)) x hx
      refine le_trans this (planSzBound_mono b ?_)
      omega

theorem introPlans_path_sz (v : ℕ) (N : Finset ℕ) (t : CT) : ∀ x ∈ introPlans v N t, sz x.1 ≤ 2 * count t := by
  intro x hx
  have := introPlans_path_le v N t x hx
  rw [sz_list_nat]; omega

/-- the size of a whole plan triple -/
theorem introPlans_sz_le (v : ℕ) (N : Finset ℕ) {b c0 Sct : ℕ} (t : CT) (hlb : LB b t) (hc : count t ≤ c0)
    (hct : ∀ x ∈ introPlans v N t, sz x.2.2 ≤ Sct) :
    ∀ x ∈ introPlans v N t, sz x ≤ 2 * c0 + planSzBound c0 b + Sct + 2 := by
  intro x hx
  have h1 := introPlans_path_sz v N t x hx
  have h2 := introPlans_plan_sz v N t hlb x hx
  have h3 := hct x hx
  have h4 := planSzBound_mono b hc
  have e : sz x = sz x.1 + (sz x.2.1 + sz x.2.2 + 1) + 1 := by
    obtain ⟨a, p, c⟩ := x; simp only [sz_pair]
  omega

end E6b
end Lax117284Proofs.Treewidth.Fun
