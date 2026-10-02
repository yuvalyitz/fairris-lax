import Lax117284Proofs.Treewidth.Chars.RealizeTc
import Lax117284Proofs.Treewidth.Chars.MergeFinal

/-!
# The topology of the realised decomposition (work package C5, part 5)

`TI v t t'` collects what the introduction of the fresh vertex `v` does to a rooted tree `t`, turning it into `t'`
(same tree up to duplicated nodes, `v` added to a connected region, junk branches attached): vertex sets, bags, and the
number of tops of every vertex other than `v`.  We prove `TI` for a chain whose middle segment receives `v`
(`chain_region_TI`) and for a chain whose kids change (`chain_kids_TI`).
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

structure TI (v : ℕ) (t t' : RT) : Prop where
  vsub : ∀ x, x ∈ t'.verts → x ∈ t.verts ∨ x = v
  vsup : ∀ x, x ∈ t.verts → x ∈ t'.verts
  bnew : ∀ Y ∈ t'.bags, v ∈ Y ∨ ∃ X ∈ t.bags, Y ⊆ X
  bsup : ∀ X ∈ t.bags, ∃ Y ∈ t'.bags, X ⊆ Y
  tcne : ∀ u, u ≠ v → ∀ p, tc u t' p = tc u t p

theorem TI.refl (v : ℕ) (t : RT) : TI v t t :=
  ⟨fun x hx => Or.inl hx, fun x hx => hx, fun Y hY => Or.inr ⟨Y, hY, subset_rfl⟩, fun X hX => ⟨X, hX, subset_rfl⟩,
    fun u _ p => rfl⟩

/-! ## lists of kids -/

theorem forall2_exists_right {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → ∀ b ∈ l', ∃ a ∈ l, R a b := by
  intro l l' h
  induction h with
  | nil => intro b hb; simp at hb
  | @cons a b l l' hab _ ih =>
    intro b' hb'
    rcases List.mem_cons.1 hb' with rfl | hb'
    · exact ⟨a, by simp, hab⟩
    · obtain ⟨a', ha', h'⟩ := ih b' hb'
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem forall2_exists_left {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → ∀ a ∈ l, ∃ b ∈ l', R a b := by
  intro l l' h
  induction h with
  | nil => intro a ha; simp at ha
  | @cons a b l l' hab _ ih =>
    intro a' ha'
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact ⟨b, by simp, hab⟩
    · obtain ⟨b', hb', h'⟩ := ih a' ha'
      exact ⟨b', List.mem_cons_of_mem _ hb', h'⟩

theorem tcL_of_forall2 {v : ℕ} {K K' : List RT} (h : List.Forall₂ (TI v) K K') {u : ℕ} (hu : u ≠ v) (p : Bool) :
    tcL u K' p = tcL u K p := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [tcL, hab.tcne u hu p, ih]

theorem tc_chain_kids (u : ℕ) : ∀ (ns : List CNode) (K K' : List RT), ns ≠ [] → (∀ p, tcL u K' p = tcL u K p) →
    ∀ p, tc u (AR.chainToRT ns K') p = tc u (AR.chainToRT ns K) p := by
  intro ns
  induction ns with
  | nil => intro K K' h; exact absurd rfl h
  | cons n r ih =>
    intro K K' _ hK p
    cases r with
    | nil =>
      rw [chainToRT_single, chainToRT_single, tc_node, tc_node]
      simp only [List.map_append, List.sum_append, ← tcL_eq_sum, hK]
    | cons m r' =>
      rw [chainToRT_cons_of_ne n (l := m :: r') (by simp) K', chainToRT_cons_of_ne n (l := m :: r') (by simp) K]
      simp only [tc_node, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil, ih K K' (by simp) hK]

/-! ## duplicated chains -/

theorem DupOf.sub {ns ns' : List CNode} (h : DupOf ns ns') : ∀ n ∈ ns, n ∈ ns' := by
  induction h with
  | refl => intro n hn; exact hn
  | @dup ns' i _ ih =>
    intro n hn
    have := ih n hn
    by_cases hi : i < ns'.length
    · rw [dupAfter_of_lt hi]
      have h2 : n ∈ ns'.take (i + 1) ++ ns'.drop (i + 1) := by rw [List.take_append_drop]; exact this
      rcases List.mem_append.1 h2 with h3 | h3
      · exact List.mem_append_left _ (List.mem_append_left _ h3)
      · exact List.mem_append_right _ h3
    · rw [dupAfter_of_ge (by omega)]; exact this

theorem DupOf.info {ns ns2 : List CNode} (h : DupOf ns ns2) :
    ∀ n ∈ ns2, ∃ n0 ∈ ns, n.bag = n0.bag ∧ ∀ J ∈ n.junk, J ∈ n0.junk := by
  intro n hn
  rcases h.mem n hn with h1 | ⟨n0, h1, rfl⟩
  · exact ⟨n, h1, rfl, fun J hJ => hJ⟩
  · exact ⟨n0, h1, rfl, fun J hJ => by simp at hJ⟩

theorem av_bag (v : ℕ) (n : CNode) : (av v n).bag = insert v n.bag := rfl
theorem av_junk (v : ℕ) (n : CNode) : (av v n).junk = n.junk := rfl

/-! ## a chain whose middle segment receives `v` -/

theorem chain_region_TI (v : ℕ) {ns L M R : List CNode} {K K' : List RT} {chain'' : List CNode} (hns : ns ≠ [])
    (hdup : DupOf ns (L ++ M ++ R)) (hne'' : chain'' ≠ [])
    (hfree : ∀ n ∈ ns, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts)
    (hK : List.Forall₂ (TI v) K K')
    (hc1 : chain'' = L ++ M.map (av v) ++ R)
    (hmap : ∃ g : ℕ → CNode → CNode, (∀ i n, (∀ u, u ≠ v → (u ∈ (g i n).bag ↔ u ∈ n.bag)) ∧
        (g i n).junk = n.junk) ∧ chain'' = (L ++ M ++ R).mapIdx g) :
    TI v (AR.chainToRT ns K) (AR.chainToRT chain'' K') := by
  have hinfo := hdup.info
  have hsub := hdup.sub
  have hb := mem_bags_chainToRT K ns hns
  have hb' := mem_bags_chainToRT K' chain'' hne''
  -- membership in the new chain
  have hmem : ∀ y ∈ chain'', y ∈ (L ++ M ++ R) ∨ (∃ n ∈ M, y = av v n) := by
    intro y hy
    rw [hc1] at hy
    simp only [List.mem_append, List.mem_map] at hy
    rcases hy with (hy | ⟨n, hn, rfl⟩) | hy
    · exact Or.inl (by simp [hy])
    · exact Or.inr ⟨n, hn, rfl⟩
    · exact Or.inl (by simp [hy])
  have hmem' : ∀ n ∈ (L ++ M ++ R), n ∈ chain'' ∨ av v n ∈ chain'' := by
    intro n hn
    rw [hc1]
    simp only [List.mem_append] at hn ⊢
    rcases hn with (hn | hn) | hn
    · exact Or.inl (Or.inl (Or.inl hn))
    · exact Or.inr (Or.inl (Or.inr (List.mem_map.2 ⟨n, hn, rfl⟩)))
    · exact Or.inl (Or.inr hn)
  -- v-freeness of the (duplicated) nodes
  have hfree2 : ∀ n ∈ (L ++ M ++ R), v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts := by
    intro n hn
    obtain ⟨n0, hn0, hbg, hj⟩ := hinfo n hn
    obtain ⟨h1, h2⟩ := hfree n0 hn0
    exact ⟨by rw [hbg]; exact h1, fun J hJ => h2 J (hj J hJ)⟩
  have hMsub : ∀ n ∈ M, n ∈ (L ++ M ++ R) := fun n hn => by simp [hn]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- vsub
    intro x hx
    rw [mem_verts_chainToRT] at hx ⊢
    rcases hx with ⟨y, hy, hxy⟩ | ⟨y, hy, J, hJ, hxJ⟩ | ⟨k', hk', hxk⟩
    · rcases hmem y hy with hn | ⟨n, hn, rfl⟩
      · obtain ⟨n0, hn0, hbg, -⟩ := hinfo y hn
        exact Or.inl (Or.inl ⟨n0, hn0, by rw [← hbg]; exact hxy⟩)
      · obtain ⟨n0, hn0, hbg, -⟩ := hinfo n (hMsub n hn)
        rw [av_bag, Finset.mem_insert] at hxy
        rcases hxy with rfl | hxy
        · exact Or.inr rfl
        · exact Or.inl (Or.inl ⟨n0, hn0, by rw [← hbg]; exact hxy⟩)
    · rcases hmem y hy with hn | ⟨n, hn, rfl⟩
      · obtain ⟨n0, hn0, hbg, hj⟩ := hinfo y hn
        exact Or.inl (Or.inr (Or.inl ⟨n0, hn0, J, hj J hJ, hxJ⟩))
      · obtain ⟨n0, hn0, hbg, hj⟩ := hinfo n (hMsub n hn)
        exact Or.inl (Or.inr (Or.inl ⟨n0, hn0, J, hj J hJ, hxJ⟩))
    · obtain ⟨k, hk, hkk⟩ := forall2_exists_right hK k' hk'
      rcases hkk.vsub x hxk with h | h
      · exact Or.inl (Or.inr (Or.inr ⟨k, hk, h⟩))
      · exact Or.inr h
  · -- vsup
    intro x hx
    rw [mem_verts_chainToRT] at hx ⊢
    rcases hx with ⟨y, hy, hxy⟩ | ⟨y, hy, J, hJ, hxJ⟩ | ⟨k, hk, hxk⟩
    · rcases hmem' y (hsub y hy) with h | h
      · exact Or.inl ⟨y, h, hxy⟩
      · exact Or.inl ⟨av v y, h, by rw [av_bag]; exact Finset.mem_insert_of_mem hxy⟩
    · rcases hmem' y (hsub y hy) with h | h
      · exact Or.inr (Or.inl ⟨y, h, J, hJ, hxJ⟩)
      · exact Or.inr (Or.inl ⟨av v y, h, J, hJ, hxJ⟩)
    · obtain ⟨k', hk', hkk⟩ := forall2_exists_left hK k hk
      exact Or.inr (Or.inr ⟨k', hk', hkk.vsup x hxk⟩)
  · -- bnew
    intro Y hY
    rcases (hb' Y).1 hY with ⟨y, hy, hYy⟩ | ⟨y, hy, J, hJ, hYJ⟩ | ⟨k', hk', hYk⟩
    · rcases hmem y hy with hn | ⟨n, hn, rfl⟩
      · obtain ⟨n0, hn0, hbg, -⟩ := hinfo y hn
        exact Or.inr ⟨n0.bag, (hb _).2 (Or.inl ⟨n0, hn0, rfl⟩), by rw [hYy, hbg]⟩
      · left
        rw [hYy, av_bag]
        exact Finset.mem_insert_self _ _
    · rcases hmem y hy with hn | ⟨n, hn, rfl⟩
      · obtain ⟨n0, hn0, hbg, hj⟩ := hinfo y hn
        exact Or.inr ⟨Y, (hb Y).2 (Or.inr (Or.inl ⟨n0, hn0, J, hj J hJ, hYJ⟩)), subset_rfl⟩
      · obtain ⟨n0, hn0, hbg, hj⟩ := hinfo n (hMsub n hn)
        exact Or.inr ⟨Y, (hb Y).2 (Or.inr (Or.inl ⟨n0, hn0, J, hj J hJ, hYJ⟩)), subset_rfl⟩
    · obtain ⟨k, hk, hkk⟩ := forall2_exists_right hK k' hk'
      rcases hkk.bnew Y hYk with h | ⟨X, hX, hYX⟩
      · exact Or.inl h
      · exact Or.inr ⟨X, (hb X).2 (Or.inr (Or.inr ⟨k, hk, hX⟩)), hYX⟩
  · -- bsup
    intro X hX
    rcases (hb X).1 hX with ⟨y, hy, hXy⟩ | ⟨y, hy, J, hJ, hXJ⟩ | ⟨k, hk, hXk⟩
    · rcases hmem' y (hsub y hy) with h | h
      · exact ⟨y.bag, (hb' _).2 (Or.inl ⟨y, h, rfl⟩), by rw [hXy]⟩
      · exact ⟨(av v y).bag, (hb' _).2 (Or.inl ⟨av v y, h, rfl⟩),
          by rw [hXy, av_bag]; exact Finset.subset_insert _ _⟩
    · rcases hmem' y (hsub y hy) with h | h
      · exact ⟨X, (hb' _).2 (Or.inr (Or.inl ⟨y, h, J, hJ, hXJ⟩)), subset_rfl⟩
      · exact ⟨X, (hb' _).2 (Or.inr (Or.inl ⟨av v y, h, J, hJ, hXJ⟩)), subset_rfl⟩
    · obtain ⟨k', hk', hkk⟩ := forall2_exists_left hK k hk
      obtain ⟨Y, hY, hXY⟩ := hkk.bsup X hXk
      exact ⟨Y, (hb' _).2 (Or.inr (Or.inr ⟨k', hk', hY⟩)), hXY⟩
  · -- tcne
    intro u hu p
    obtain ⟨g, hg, hc2⟩ := hmap
    rw [hc2, tc_chain_mapIdx u _ g (fun i n => ⟨(hg i n).1 u hu, (hg i n).2⟩), tc_chain_dupOf u hdup]
    exact tc_chain_kids u ns K K' hns (tcL_of_forall2 hK hu) p


/-- Only the kids change. -/
theorem chain_kids_TI (v : ℕ) {ns : List CNode} {K K' : List RT} (hns : ns ≠ [])
    (hfree : ∀ n ∈ ns, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts)
    (hK : List.Forall₂ (TI v) K K') :
    TI v (AR.chainToRT ns K) (AR.chainToRT ns K') := by
  have := chain_region_TI v (ns := ns) (L := ns) (M := []) (R := []) (K := K) (K' := K') (chain'' := ns) hns
    (by simpa using DupOf.refl (ns := ns)) hns hfree hK (by simp)
    ⟨fun _ n => n, fun i n => ⟨fun u _ => Iff.rfl, rfl⟩,
      by simp only [List.append_nil]; exact (List.ext_getElem (by simp) (by intro i h1 h2; simp)).symm⟩
  exact this


/-! ## the tops of the new vertex -/

theorem tc_v_MR (v : ℕ) {M R : List CNode} {K' : List RT} (hM : M ≠ [])
    (hMj : ∀ n ∈ M, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts)
    (hR : ∀ n ∈ R, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts)
    (hK1 : R = [] → tcL v K' true = 0) (hK2 : R ≠ [] → tcL v K' false = 0) (p : Bool) :
    tc v (AR.chainToRT (M.map (av v) ++ R) K') p = if p = false then 1 else 0 := by
  have hMfull : ∀ n ∈ M.map (av v), v ∈ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hn
    exact ⟨by rw [av_bag]; exact Finset.mem_insert_self _ _, (hMj m hm).2⟩
  have hMne : M.map (av v) ≠ [] := by simpa using hM
  by_cases hRe : R = []
  · subst hRe
    rw [List.append_nil, tc_chain_full v _ K' p hMne hMfull, hK1 rfl]
    simp
  · rw [chainToRT_append _ _ K' hMne hRe, tc_chain_full v _ [AR.chainToRT R K'] p hMne hMfull]
    have := tc_chain_prefix_free v R K' true hRe hR
    have h2 := hK2 hRe
    simp only [tcL, this, h2]
    simp

theorem tc_v_region (v : ℕ) {L M R : List CNode} {K' : List RT} (hM : M ≠ [])
    (hL : ∀ n ∈ L, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts)
    (hMj : ∀ n ∈ M, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts)
    (hR : ∀ n ∈ R, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts)
    (hK1 : R = [] → tcL v K' true = 0) (hK2 : R ≠ [] → tcL v K' false = 0) (p : Bool) :
    tc v (AR.chainToRT (L ++ M.map (av v) ++ R) K') p = if L = [] ∧ p = true then 0 else 1 := by
  have hMne : M.map (av v) ++ R ≠ [] := fun h => hM (List.map_eq_nil_iff.1 (List.append_eq_nil_iff.1 h).1)
  rw [List.append_assoc]
  by_cases hLe : L = []
  · subst hLe
    rw [List.nil_append, tc_v_MR v hM hMj hR hK1 hK2 p]
    by_cases hp : p = false <;> simp [hp]
  · rw [chainToRT_append _ _ K' hLe hMne, tc_chain_prefix_free v L _ p hLe hL]
    simp only [tcL]
    rw [tc_v_MR v hM hMj hR hK1 hK2 false]
    simp [hLe]

end Lax117284Proofs.Treewidth.Chars
