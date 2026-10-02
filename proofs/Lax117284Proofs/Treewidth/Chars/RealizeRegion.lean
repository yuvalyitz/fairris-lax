import Lax117284Proofs.Treewidth.Chars.RealizeRun

/-!
# The characteristic of a chain with a region (work package C5, part 6)

`region_norm`: the normal form of the profile (with respect to `insert v B`) of a chain `L ++ M⁺ ++ R` (the middle
segment `M` with `v` added) with kids `K'` equals the normal form of the *nested* raw characteristic
`regionQ` : run `S` (sizes of `L`) above run `S ∪ {v}` (sizes of `M⁺`) above run `S` (sizes of `R`) above the kids.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem bags_free_of_verts {v : ℕ} {t : RT} (h : v ∉ t.verts) : ∀ X ∈ t.bags, v ∉ X := by
  intro X hX hv
  exact h ((RT.mem_verts_iff t v).2 ⟨X, hX, hv⟩)

/-- Junk stays prunable after adding a fresh vertex to the boundary. -/
theorem junk_keep {v : ℕ} {B S σ : Finset ℕ} {J : RT} (hJ : Jk B S J) (hv : v ∉ J.verts) (hσ : S ⊆ σ) :
    keep σ (norm (RT.prof (insert v B) J)) = false := by
  rw [prof_insert_of_free v B J (bags_free_of_verts hv)]
  have h1 : norm (RT.prof B J) = J.char B := rfl
  rw [h1, char_eq_charF, AR.keep_charF]
  obtain ⟨hleaf, hsub⟩ := hJ
  simp [hleaf, hsub.trans hσ]

/-- An unchanged kid keeps its characteristic. -/
theorem norm_prof_kid {v : ℕ} {B : Finset ℕ} {k : AR} (hk : Canon B k) (hv : v ∉ (AR.toRT k).verts) :
    norm (RT.prof (insert v B) (AR.toRT k)) = AR.charF Finset.card k := by
  rw [prof_insert_of_free v B _ (bags_free_of_verts hv)]
  have : norm (RT.prof B (AR.toRT k)) = (AR.toRT k).char B := rfl
  rw [this, char_eq_charF, analyze_toRT B k hk]

/-- The raw nested characteristic of a chain with a region. -/
def regionQ (v : ℕ) (S : Finset ℕ) (L M R : List CNode) (KQ : List CT) : CT :=
  let Rq : List CT := if R = [] then KQ else [CT.node S (typical (csz R)) KQ]
  let Mq : CT := CT.node (insert v S) (typical (csz (M.map (av v)))) Rq
  if L = [] then Mq else CT.node S (typical (csz L)) [Mq]

theorem inter_insert_of_not_mem {v : ℕ} {X B : Finset ℕ} (hv : v ∉ X) : X ∩ insert v B = X ∩ B := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert]
  constructor
  · rintro ⟨h1, rfl | h2⟩
    · exact absurd h1 hv
    · exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr h2⟩

theorem inter_insert_insert {v : ℕ} {X B : Finset ℕ} : insert v X ∩ insert v B = insert v (X ∩ B) := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert]
  tauto

theorem region_norm (v : ℕ) (B S : Finset ℕ) (hvB : v ∉ B) {ns L M R : List CNode} {K' : List RT} (KQ : List CT)
    (hM : M ≠ [])
    (hinfo : ∀ n ∈ L ++ M ++ R, ∃ n0 ∈ ns, n.bag = n0.bag ∧ ∀ J ∈ n.junk, J ∈ n0.junk)
    (hbase : ∀ n0 ∈ ns, n0.bag ∩ B = S ∧ v ∉ n0.bag ∧ ∀ J ∈ n0.junk, Jk B S J ∧ v ∉ J.verts)
    (hKQ : KQ.map norm = (K'.map (RT.prof (insert v B))).map norm) :
    norm (RT.prof (insert v B) (AR.chainToRT (L ++ M.map (av v) ++ R) K')) = norm (regionQ v S L M R KQ) := by
  have hn0 : ∀ n ∈ L ++ M ++ R, n.bag ∩ B = S ∧ v ∉ n.bag ∧ ∀ J ∈ n.junk, Jk B S J ∧ v ∉ J.verts := by
    intro n hn
    obtain ⟨n0, hn0, hb, hj⟩ := hinfo n hn
    obtain ⟨h1, h2, h3⟩ := hbase n0 hn0
    exact ⟨by rw [hb]; exact h1, by rw [hb]; exact h2, fun J hJ => h3 J (hj J hJ)⟩
  have hL : ∀ n ∈ L, n.bag ∩ insert v B = S ∧ ∀ J ∈ n.junk, keep S (norm (RT.prof (insert v B) J)) = false := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := hn0 n (by simp [hn])
    exact ⟨by rw [inter_insert_of_not_mem h2]; exact h1,
      fun J hJ => junk_keep (h3 J hJ).1 (h3 J hJ).2 subset_rfl⟩
  have hR : ∀ n ∈ R, n.bag ∩ insert v B = S ∧ ∀ J ∈ n.junk, keep S (norm (RT.prof (insert v B) J)) = false := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := hn0 n (by simp [hn])
    exact ⟨by rw [inter_insert_of_not_mem h2]; exact h1,
      fun J hJ => junk_keep (h3 J hJ).1 (h3 J hJ).2 subset_rfl⟩
  have hMo : ∀ n ∈ M.map (av v), n.bag ∩ insert v B = insert v S ∧
      ∀ J ∈ n.junk, keep (insert v S) (norm (RT.prof (insert v B) J)) = false := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hn
    obtain ⟨h1, h2, h3⟩ := hn0 m (by simp [hm])
    exact ⟨by rw [av_bag, inter_insert_insert, h1],
      fun J hJ => junk_keep (h3 J hJ).1 (h3 J hJ).2 (Finset.subset_insert _ _)⟩
  have hMne : M.map (av v) ≠ [] := by simpa using hM
  -- generic step
  have step : ∀ (C : List CNode) (ℓ : Finset ℕ) (K : List RT) (KQ' : List CT), C ≠ [] →
      (∀ n ∈ C, n.bag ∩ insert v B = ℓ ∧ ∀ J ∈ n.junk, keep ℓ (norm (RT.prof (insert v B) J)) = false) →
      KQ'.map norm = (K.map (RT.prof (insert v B))).map norm →
      norm (RT.prof (insert v B) (AR.chainToRT C K)) = norm (CT.node ℓ (typical (csz C)) KQ') := by
    intro C ℓ K KQ' hC hok hK
    rw [chain_norm (insert v B) ℓ C K hC hok, norm_node', hK]
  have hRstep : R ≠ [] → norm (RT.prof (insert v B) (AR.chainToRT R K')) =
      norm (CT.node S (typical (csz R)) KQ) := fun hRe => step R S K' KQ hRe hR hKQ
  -- the middle part
  have hMstep : norm (RT.prof (insert v B) (AR.chainToRT (M.map (av v) ++ R) K')) =
      norm (CT.node (insert v S) (typical (csz (M.map (av v)))) (if R = [] then KQ else [CT.node S (typical (csz R)) KQ])) := by
    by_cases hRe : R = []
    · subst hRe
      rw [List.append_nil, if_pos rfl]
      exact step _ _ K' KQ hMne hMo hKQ
    · rw [if_neg hRe, chainToRT_append _ _ K' hMne hRe]
      apply step _ _ [AR.chainToRT R K'] _ hMne hMo
      simp only [List.map_cons, List.map_nil, hRstep hRe]
  have hMne' : M.map (av v) ++ R ≠ [] := fun h => hMne (List.append_eq_nil_iff.1 h).1
  by_cases hLe : L = []
  · subst hLe
    rw [List.nil_append, hMstep]
    simp [regionQ]
  · rw [List.append_assoc, chainToRT_append _ _ K' hLe hMne']
    have := step L S [AR.chainToRT (M.map (av v) ++ R) K'] [CT.node (insert v S) (typical (csz (M.map (av v))))
      (if R = [] then KQ else [CT.node S (typical (csz R)) KQ])] hLe hL (by
        simp only [List.map_cons, List.map_nil, hMstep])
    rw [this]
    simp [regionQ, hLe]


/-- Everything about a chain with a region, in one statement. -/
theorem region_PRC (v : ℕ) (B S : Finset ℕ) (hvB : v ∉ B) {ns L M R : List CNode} {ks : List AR}
    {K' : List RT} (KQ : List CT) {chain'' : List CNode} (hns : ns ≠ []) (hM : M ≠ [])
    (hbase : ∀ n0 ∈ ns, n0.bag ∩ B = S ∧ v ∉ n0.bag ∧ ∀ J ∈ n0.junk, Jk B S J ∧ v ∉ J.verts)
    (hdup : DupOf ns (L ++ M ++ R)) (hchain : chain'' = L ++ M.map (av v) ++ R)
    (hmap : ∃ g : ℕ → CNode → CNode, (∀ i n, (∀ u, u ≠ v → (u ∈ (g i n).bag ↔ u ∈ n.bag)) ∧
        (g i n).junk = n.junk) ∧ chain'' = (L ++ M ++ R).mapIdx g)
    (hK : List.Forall₂ (TI v) (ks.map AR.toRT) K')
    (hK1 : R = [] → tcL v K' true = 0) (hK2 : R ≠ [] → tcL v K' false = 0)
    (hKQ : KQ.map norm = (K'.map (RT.prof (insert v B))).map norm) :
    TI v (AR.chainToRT ns (ks.map AR.toRT)) (AR.chainToRT chain'' K') ∧
    (∀ p, tc v (AR.chainToRT chain'' K') p = if L = [] ∧ p = true then 0 else 1) ∧
    norm (RT.prof (insert v B) (AR.chainToRT chain'' K')) = norm (regionQ v S L M R KQ) ∧
    (∀ Y ∈ (AR.chainToRT chain'' K').bags, v ∈ Y → (∃ m ∈ M, Y = insert v m.bag) ∨ ∃ k' ∈ K', Y ∈ k'.bags) ∧
    (∀ m ∈ M, insert v m.bag ∈ (AR.chainToRT chain'' K').bags) := by
  have hinfo := hdup.info
  have hfree : ∀ n ∈ ns, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts :=
    fun n hn => ⟨(hbase n hn).2.1, fun J hJ => ((hbase n hn).2.2 J hJ).2⟩
  have hfree2 : ∀ n ∈ (L ++ M ++ R), v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts := by
    intro n hn
    obtain ⟨n0, hn0, hbg, hj⟩ := hinfo n hn
    obtain ⟨h1, h2⟩ := hfree n0 hn0
    exact ⟨by rw [hbg]; exact h1, fun J hJ => h2 J (hj J hJ)⟩
  have hne'' : chain'' ≠ [] := by
    obtain ⟨m0, M', rfl⟩ := List.exists_cons_of_ne_nil hM
    rw [hchain]; simp
  have hb' := mem_bags_chainToRT K' chain'' hne''
  refine ⟨chain_region_TI v hns hdup hne'' hfree hK hchain hmap, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [hchain]
    exact tc_v_region v hM (fun n hn => hfree2 n (by simp [hn])) (fun n hn => hfree2 n (by simp [hn]))
      (fun n hn => hfree2 n (by simp [hn])) hK1 hK2 p
  · rw [hchain]
    exact region_norm v B S hvB KQ hM hinfo hbase hKQ
  · intro Y hY hvY
    rcases (hb' Y).1 hY with ⟨y, hy, rfl⟩ | ⟨y, hy, J, hJ, hYJ⟩ | ⟨k', hk', hYk⟩
    · rw [hchain] at hy
      simp only [List.mem_append, List.mem_map] at hy
      rcases hy with (hy | ⟨m, hm, rfl⟩) | hy
      · exact absurd hvY (hfree2 y (by simp [hy])).1
      · exact Or.inl ⟨m, hm, rfl⟩
      · exact absurd hvY (hfree2 y (by simp [hy])).1
    · rw [hchain] at hy
      simp only [List.mem_append, List.mem_map] at hy
      have hJv : v ∈ J.verts := (RT.mem_verts_iff J v).2 ⟨Y, hYJ, hvY⟩
      rcases hy with (hy | ⟨m, hm, rfl⟩) | hy
      · exact absurd hJv ((hfree2 y (by simp [hy])).2 J hJ)
      · exact absurd hJv ((hfree2 m (by simp [hm])).2 J hJ)
      · exact absurd hJv ((hfree2 y (by simp [hy])).2 J hJ)
    · exact Or.inr ⟨k', hk', hYk⟩
  · intro m hm
    rw [hb']
    left
    exact ⟨av v m, by rw [hchain]; exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hm)), rfl⟩

end Lax117284Proofs.Treewidth.Chars
