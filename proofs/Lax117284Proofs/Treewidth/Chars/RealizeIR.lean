import Lax117284Proofs.Treewidth.Chars.RealizeAtt

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
