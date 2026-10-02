import Lax117284Proofs.Treewidth.Chars.RealizeAttChain

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
