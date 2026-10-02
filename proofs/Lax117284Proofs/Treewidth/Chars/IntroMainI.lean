import Lax117284Proofs.Treewidth.Chars.IntroMainR

/-!
# The induction step at an unflagged node (work package C4, part 11)

`step_I`: `P = node S e false (pre ++ K0 :: post)` with `K0` the unique occupied kid.  If `K0` is kept on the source side
the option is found inside `K0` (or, in the *merge* shape, inside the merged run); if `K0` is junk on the source side
the new branch is hung at the node (`att`; in the merge shape with the cut at the junction).
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT FT

theorem allChains_N_sub {S N : Finset ℕ} {chain : List (Finset ℕ)} {M : Finset ℕ} (h : (chain, M) ∈ allChains S N) :
    N ⊆ S := by
  rw [mem_allChains] at h
  obtain ⟨h1, -, h3, h4⟩ := h
  refine h3.trans (h4.trans ?_)
  cases hl : chain.getLast? with
  | none =>
    have : chain = [] := List.getLast?_eq_none_iff.1 hl
    subst this; simp
  | some Z =>
    rw [List.getLastD_eq_getLast?, hl]
    exact (h1 Z (List.mem_of_getLast? hl)).2

theorem fT_S (v : ℕ) (K : FT) : (fT v K).S = if K.w then insert v K.S else K.S := by
  cases K; rfl

theorem gA_S (K : FT) : (gA K).S = K.S := by
  unfold gA; rw [S_norm]; cases K; rfl

theorem IR_of_winR (v : ℕ) (N : Finset ℕ) {t r : CT} {c : Finset ℕ} (hw : WinR v t r c) (hN : N ⊆ c) :
    IR v N t r := by
  cases t with
  | node S y ks => exact IR.top (Or.inl hw) hN

theorem fN_of_not_occ (v : ℕ) {K : FT} (h : occ K = false) : fN v K = gA K := by
  unfold fN gA; rw [fT_of_not_occ v K h]

theorem split_kept {S : Finset ℕ} {pre post : List FT} {K0 : FT} (hK0k : keep S (gA K0) = true) :
    ∃ τ1 τ2, order S (pre ++ K0 :: post) = τ1 ++ K0 :: τ2 ∧
      (τ1 ++ τ2).Perm (kept S pre ++ kept S post) := by
  have hk : kept S (pre ++ K0 :: post) = kept S pre ++ K0 :: kept S post := by
    unfold kept
    rw [List.filter_append, List.filter_cons_of_pos (p := fun K => keep S (gA K)) hK0k]
  have hmem : K0 ∈ order S (pre ++ K0 :: post) := by
    rw [(order_perm S _).mem_iff, hk]; simp
  obtain ⟨τ1, τ2, hτ⟩ := List.append_of_mem hmem
  refine ⟨τ1, τ2, hτ, ?_⟩
  have h1 : (τ1 ++ K0 :: τ2).Perm (kept S pre ++ K0 :: kept S post) := by
    rw [← hτ, ← hk]; exact order_perm S _
  have h2 : (τ1 ++ K0 :: τ2).Perm (K0 :: (τ1 ++ τ2)) := List.perm_middle
  have h3 : (kept S pre ++ K0 :: kept S post).Perm (K0 :: (kept S pre ++ kept S post)) := List.perm_middle
  exact (List.Perm.cons_inv ((h2.symm.trans h1).trans h3))

/-- **The induction step at an unflagged node.** -/
theorem step_I (v : ℕ) (N : Finset ℕ) (S : Finset ℕ) (e : ℕ) (pre : List FT) (K0 : FT) (post : List FT)
    (hok : FOk v (FT.node S e false (pre ++ K0 :: post)))
    (hK0 : occ K0 = true) (hpre : occL pre = false) (hpost : occL post = false)
    (hc : Conn (fT v (FT.node S e false (pre ++ K0 :: post))))
    (hN : N ⊆ cov (FT.node S e false (pre ++ K0 :: post)))
    (IHR : K0.w = true → ∃ r c, WinR v (gA K0) r c ∧ cov K0 ⊆ c ∧ DomC (norm r) (fN v K0))
    (IHI : K0.w = false → N ⊆ cov K0 → ∃ r, IR v N (gA K0) r ∧ DomC (norm r) (fN v K0)) :
    ∃ r, IR v N (norm (uT (FT.node S e false (pre ++ K0 :: post)))) r ∧
      DomC (norm r) (norm (fT v (FT.node S e false (pre ++ K0 :: post)))) := by
  have hvS : v ∉ S := hok.1
  have hSe : S.card ≤ e := hok.2.1
  have hkOk : ∀ K ∈ pre ++ K0 :: post, FOk v K := FOkL_iff.1 hok.2.2.2.2
  have hocc_o : ∀ K ∈ pre ++ post, occ K = false := by
    intro K hK
    rcases List.mem_append.1 hK with h | h
    · exact occ_of_occL_false hpre K h
    · exact occ_of_occL_false hpost K h
  have hfN_o : ∀ K ∈ pre ++ post, fN v K = gA K := by
    intro K hK; unfold fN gA; rw [fT_of_not_occ v K (hocc_o K hK)]
  have hN0 : N ⊆ cov K0 := by
    intro x hx
    have hx' := hN hx
    simp [cov] at hx'
    obtain ⟨k, hk, hxk⟩ := mem_covL.1 hx'
    rcases List.mem_append.1 hk with h | h
    · rw [cov_of_not_occ k (occ_of_occL_false hpre k h)] at hxk; simp at hxk
    · rcases List.mem_cons.1 h with e | h
      · rw [e] at hxk; exact hxk
      · rw [cov_of_not_occ k (occ_of_occL_false hpost k h)] at hxk; simp at hxk
  have hkeep0f : keep S (fN v K0) = true := keep_occ v hK0 hvS
  have hfk_o : ∀ K ∈ pre ++ post, keep S (fN v K) = keep S (gA K) := by
    intro K hK; rw [hfN_o K hK]
  have hTeq : norm (fT v (FT.node S e false (pre ++ K0 :: post))) =
      normF S [e] ((fkept v S (pre ++ K0 :: post)).map (fN v)) := by
    rw [T_eq]; rfl
  have hdist : ((fkept v S (pre ++ K0 :: post)).map (fN v)).Pairwise
      (fun a b => key S a ≠ key S b) := by
    have hc' : Conn (CT.node S [e] ((pre ++ K0 :: post).map (fT v))) := by rw [fT_node] at hc; exact hc
    exact T_dist hc'
  have hfkept : fkept v S (pre ++ K0 :: post) = kept S pre ++ K0 :: kept S post := by
    unfold fkept kept
    rw [List.filter_append, List.filter_cons_of_pos (p := fun K => keep S (fN v K)) hkeep0f]
    congr 1
    · exact List.filter_congr (fun K hK => hfk_o K (List.mem_append_left _ hK))
    · congr 1
      exact List.filter_congr (fun K hK => hfk_o K (List.mem_append_right _ hK))
  rw [hTeq]
  by_cases hK0k : keep S (gA K0) = true
  · have hK0k' : keep S (gA K0) = true := hK0k
    have hfk_all : ∀ K ∈ pre ++ K0 :: post, keep S (fN v K) = keep S (gA K) := by
      intro K hK
      rcases List.mem_append.1 hK with h | h
      · exact hfk_o K (List.mem_append_left _ h)
      · rcases List.mem_cons.1 h with rfl | h
        · rw [hkeep0f, hK0k']
        · exact hfk_o K (List.mem_append_right _ h)
    have hfkk : fkept v S (pre ++ K0 :: post) = kept S (pre ++ K0 :: post) := fkept_eq_kept hfk_all
    rw [hfkk]
    have hdist' : ((kept S (pre ++ K0 :: post)).map (fN v)).Pairwise (fun a b => key S a ≠ key S b) := by
      rw [← hfkk]; exact hdist
    obtain ⟨r0, hr0, hd0⟩ : ∃ r0, IR v N (gA K0) r0 ∧ DomC (norm r0) (fN v K0) := by
      by_cases hw : K0.w = true
      · obtain ⟨r, c, h1, h2, h3⟩ := IHR hw
        exact ⟨r, IR_of_winR v N h1 (hN0.trans h2), h3⟩
      · exact IHI (by simpa using hw) hN0
    have hkn : keep S (norm r0) = true := by rw [domC_keep S hd0]; exact hkeep0f
    by_cases hmerge : ∃ K1, kept S (pre ++ K0 :: post) = [K1] ∧ (gA K1).S = S
    · obtain ⟨K1, hσ, hS⟩ := hmerge
      have hK1eq : K1 = K0 := by
        have : K0 ∈ kept S (pre ++ K0 :: post) := mem_kept.2 ⟨by simp, hK0k'⟩
        rw [hσ] at this
        exact (List.mem_singleton.1 this).symm
      rw [hK1eq] at hσ hS
      obtain ⟨yk, kk, hgA⟩ : ∃ yk kk, gA K0 = CT.node S yk kk := by
        cases h : gA K0 with
        | node S' y' ks' =>
          rw [h] at hS
          simp only [CT.S] at hS
          subst hS
          exact ⟨y', ks', rfl⟩
      have hy : yk ≠ [] := by
        have := gA_y_ne K0
        rw [hgA] at this
        exact this
      rw [FT.a_merge S e false _ hσ hS, hgA, hσ]
      simp only [CT.y, CT.kids, List.map_cons, List.map_nil]
      have hDom : DomC (CT.node S (typical ([e] ++ yk)) kk) (CT.node S ([e] ++ yk) kk) :=
        ⟨rfl, (domEquiv_typical _).1, domCL_iff.2 (List.forall₂_same.2 (fun k _ => DomC.refl k))⟩
      by_cases hw : K0.w = true
      · obtain ⟨r1, c0, hW, hcov0, hd1⟩ := IHR hw
        rw [hgA] at hW
        have hWt := wtopR_wrap v S kk (s := [e]) (by simp) hy hW
        have hIR := IR.top hWt (hN0.trans hcov0)
        obtain ⟨r, hr, hd⟩ := IR_mono v N hIR _ hDom
        refine ⟨r, hr, DomC.trans (norm_mono hd) ?_⟩
        have hkn1 : keep S (norm r1) = true := by rw [domC_keep S hd1]; exact hkeep0f
        rw [norm_node']
        simp only [List.map_cons, List.map_nil, List.filter_cons_of_pos hkn1, List.filter_nil]
        exact normF_mono (Dom.refl _) ⟨hd1, trivial⟩
      · have hw' : K0.w = false := by simpa using hw
        obtain ⟨r1, hr1, hd1⟩ := IHI hw' hN0
        rw [hgA] at hr1
        obtain ⟨r', hr', hcases⟩ := IR_prefix v N S kk (s := [e]) (by simp) hy hr1
        rcases hcases with ⟨hr1S, rfl⟩ | ⟨hr1S, -⟩
        · cases r1 with
          | node S1 y1 kids1 =>
            have hS1 : S1 = S := hr1S
            subst hS1
            obtain ⟨r, hr, hd⟩ := IR_mono v N hr' _ hDom
            refine ⟨r, hr, DomC.trans (norm_mono hd) ?_⟩
            exact merge_cmp (S' := S1) (e' := [e]) (by simp) hd1 hkeep0f
        · exfalso
          have h1 := domC_S hd1
          rw [S_norm] at h1
          have h2 : (fN v K0).S = K0.S := by
            unfold fN; rw [S_norm, fT_S, hw']; simp
          have h3 : K0.S = S := by rw [← gA_S K0, hgA]; rfl
          rw [hr1S, h2, h3] at h1
          exact hvS (h1 ▸ Finset.mem_insert_self v S)
    · have hnm : ∀ K1, kept S (pre ++ K0 :: post) = [K1] → (gA K1).S ≠ S :=
        fun K1 h1 h2 => hmerge ⟨K1, h1, h2⟩
      rw [FT.a_nonmerge S e false _ hnm]
      obtain ⟨τ1, τ2, hτ, hτp⟩ := split_kept (S := S) (pre := pre) (post := post) hK0k'
      have hτ12 : ∀ K ∈ τ1 ++ τ2, K ∈ pre ++ post := by
        intro K hK
        have := hτp.subset hK
        rcases List.mem_append.1 this with h | h
        · exact List.mem_append_left _ (mem_kept.1 h).1
        · exact List.mem_append_right _ (mem_kept.1 h).1
      have hτk : ∀ K ∈ order S (pre ++ K0 :: post), K ∈ kept S (pre ++ K0 :: post) :=
        fun K hK => (order_perm _ _).mem_iff.1 hK
      refine ⟨CT.node S [e] (τ1.map gA ++ r0 :: τ2.map gA), ?_, ?_⟩
      · rw [hτ]
        have := IR.kid (v := v) (N := N) (S := S) (y := [e]) (pre := τ1.map gA) (post := τ2.map gA) hr0
        simpa using this
      · rw [norm_node']
        set h1 : FT → CT := fun K => if occ K = true then norm r0 else gA K with hh1
        have hh1f : ∀ K, occ K = false → h1 K = gA K := by intro K h; simp [hh1, h]
        have hh1t : h1 K0 = norm r0 := by simp [hh1, hK0]
        have hA : ∀ K ∈ τ1 ++ τ2, (norm ∘ gA) K = h1 K := by
          intro K hK
          simp only [Function.comp]
          rw [hh1f K (hocc_o K (hτ12 K hK))]
          unfold gA; rw [norm_idem]
        have hkeepA : ∀ K ∈ τ1 ++ τ2, keep S (h1 K) = true := by
          intro K hK
          rw [hh1f K (hocc_o K (hτ12 K hK))]
          have hKo : K ∈ order S (pre ++ K0 :: post) := by
            rw [hτ]
            rcases List.mem_append.1 hK with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
          exact (mem_kept.1 (hτk K hKo)).2
        have hmapL : (τ1.map gA ++ r0 :: τ2.map gA).map norm = (τ1 ++ K0 :: τ2).map h1 := by
          rw [List.map_append, List.map_cons, List.map_append, List.map_cons, hh1t, List.map_map, List.map_map]
          congr 1
          · apply List.map_congr_left
            intro K hK
            exact hA K (List.mem_append_left _ hK)
          · congr 1
            apply List.map_congr_left
            intro K hK
            exact hA K (List.mem_append_right _ hK)
        have hlist : (((τ1.map gA ++ r0 :: τ2.map gA).map norm).filter (keep S)) =
            (order S (pre ++ K0 :: post)).map h1 := by
          rw [hmapL, hτ]
          apply List.filter_eq_self.2
          intro x hx
          obtain ⟨K, hK, rfl⟩ := List.mem_map.1 hx
          rcases List.mem_append.1 hK with h | h
          · exact hkeepA K (List.mem_append_left _ h)
          · rcases List.mem_cons.1 h with rfl | h
            · rw [hh1t]; exact hkn
            · exact hkeepA K (List.mem_append_right _ h)
        rw [hlist]
        refine align' (Dom.refl _) _ h1 (fN v) ((kept S (pre ++ K0 :: post)).map (fN v))
          ((order_perm _ _).map _) ?_ hdist'
        intro K hK
        have hKk := mem_kept.1 (hτk K hK)
        by_cases hocK : occ K = true
        · -- `K` is `K0`
          have hKK0 : K = K0 := by
            rcases List.mem_append.1 hKk.1 with h | h
            · exact absurd (hocc_o K (List.mem_append_left _ h)) (by simp [hocK])
            · rcases List.mem_cons.1 h with h | h
              · exact h
              · exact absurd (hocc_o K (List.mem_append_right _ h)) (by simp [hocK])
          subst hKK0
          rw [hh1t]; exact hd0
        · have hocf : occ K = false := by simpa using hocK
          rw [hh1f K hocf, fN_of_not_occ v hocf]
          exact DomC.refl _
  · have hK0j : keep S (gA K0) = false := by simpa using hK0k
    have hnest0 : Nested S (uT K0) := (keep_norm_false_iff S (uT K0)).1 hK0j
    obtain ⟨chain, M, hcm, hbr⟩ :=
      junk_branch v K0 (hkOk K0 (by simp)) hK0 S hvS hnest0 hN0
    have hNS : N ⊆ S := allChains_N_sub hcm
    have hbrd : DomC (norm (pathSubtree v chain M)) (fN v K0) := by
      have := norm_mono hbr
      rwa [show norm (norm (fT v K0)) = norm (fT v K0) from norm_idem _] at this
    have hbrn : keep S (norm (pathSubtree v chain M)) = true := by
      rw [domC_keep S hbrd]; exact hkeep0f
    have hkept_j : kept S (pre ++ K0 :: post) = kept S pre ++ kept S post := by
      unfold kept
      rw [List.filter_append, List.filter_cons_of_neg (p := fun K => keep S (gA K)) (by simpa using hK0j)]
    have hτocc : ∀ K ∈ kept S (pre ++ K0 :: post), occ K = false := by
      intro K hK
      rw [hkept_j] at hK
      rcases List.mem_append.1 hK with h | h
      · exact hocc_o K (List.mem_append_left _ (mem_kept.1 h).1)
      · exact hocc_o K (List.mem_append_right _ (mem_kept.1 h).1)
    have hpermK : ((kept S (pre ++ K0 :: post)) ++ [K0]).Perm (fkept v S (pre ++ K0 :: post)) := by
      rw [hkept_j, hfkept, List.append_assoc]
      exact List.Perm.append_left _ (List.perm_append_singleton K0 (kept S post))
    by_cases hmerge : ∃ K1, kept S (pre ++ K0 :: post) = [K1] ∧ (gA K1).S = S
    · obtain ⟨K1, hσ, hS⟩ := hmerge
      have hK1mem : K1 ∈ kept S (pre ++ K0 :: post) := by rw [hσ]; simp
      have hK1 := mem_kept.1 hK1mem
      have hocc1 : occ K1 = false := hτocc K1 hK1mem
      obtain ⟨yk, kk, hgA⟩ : ∃ yk kk, gA K1 = CT.node S yk kk := by
        cases h : gA K1 with
        | node S' y' ks' =>
          rw [h] at hS
          simp only [CT.S] at hS
          subst hS
          exact ⟨y', ks', rfl⟩
      have hy : yk ≠ [] := by
        have := gA_y_ne K1
        rw [hgA] at this
        exact this
      rw [FT.a_merge S e false _ hσ hS, hgA]
      simp only [CT.y, CT.kids]
      have hDom : DomC (CT.node S (typical ([e] ++ yk)) kk) (CT.node S ([e] ++ yk) kk) :=
        ⟨rfl, (domEquiv_typical _).1, domCL_iff.2 (List.forall₂_same.2 (fun k _ => DomC.refl k))⟩
      have hIR := IR.att hNS (attR_junction v N S kk (s := [e]) (by simp) hy hcm)
      obtain ⟨r, hr, hd⟩ := IR_mono v N hIR _ hDom
      refine ⟨r, hr, DomC.trans (norm_mono hd) ?_⟩
      have hnk : norm (CT.node S yk kk) = CT.node S yk kk := by rw [← hgA]; unfold gA; exact norm_idem _
      have hkeep1 : keep S (CT.node S yk kk) = true := by rw [← hgA]; exact hK1.2
      set h1 : FT → CT := fun K => if occ K = true then norm (pathSubtree v chain M) else gA K with hh1
      have hh1f : ∀ K, occ K = false → h1 K = gA K := by intro K h; simp [hh1, h]
      have hh1t : h1 K0 = norm (pathSubtree v chain M) := by simp [hh1, hK0]
      rw [norm_node']
      have hlist : (([pathSubtree v chain M, CT.node S yk kk].map norm).filter (keep S)) =
          [K0, K1].map h1 := by
        simp only [List.map_cons, List.map_nil, hnk, hh1t, hh1f K1 hocc1, hgA]
        rw [List.filter_cons_of_pos hbrn, List.filter_cons_of_pos hkeep1, List.filter_nil]
      rw [hlist]
      refine align' (Dom.refl _) [K0, K1] h1 (fN v) ((fkept v S (pre ++ K0 :: post)).map (fN v)) ?_ ?_ hdist
      · have h2 : ([K1] ++ [K0]).Perm (fkept v S (pre ++ K0 :: post)) := by
          rw [← hσ]; exact hpermK
        exact ((List.Perm.swap K1 K0 []).trans h2).map _
      · intro K hK
        rcases List.mem_cons.1 hK with rfl | hK
        · rw [hh1t]; exact hbrd
        · rw [List.mem_singleton] at hK
          subst hK
          rw [hh1f K hocc1, fN_of_not_occ v hocc1]
          exact DomC.refl _
    · have hnm : ∀ K1, kept S (pre ++ K0 :: post) = [K1] → (gA K1).S ≠ S :=
        fun K1 h1 h2 => hmerge ⟨K1, h1, h2⟩
      rw [FT.a_nonmerge S e false _ hnm]
      have hτk : ∀ K ∈ order S (pre ++ K0 :: post), K ∈ kept S (pre ++ K0 :: post) :=
        fun K hK => (order_perm _ _).mem_iff.1 hK
      have hτ_occ : ∀ K ∈ order S (pre ++ K0 :: post), occ K = false := fun K hK => hτocc K (hτk K hK)
      refine ⟨CT.node S [e] ((order S (pre ++ K0 :: post)).map gA ++ [pathSubtree v chain M]),
        IR.att hNS ⟨chain, M, hcm, Or.inl rfl⟩, ?_⟩
      rw [norm_node']
      set h1 : FT → CT := fun K => if occ K = true then norm (pathSubtree v chain M) else gA K with hh1
      have hh1f : ∀ K, occ K = false → h1 K = gA K := by intro K h; simp [hh1, h]
      have hh1t : h1 K0 = norm (pathSubtree v chain M) := by simp [hh1, hK0]
      have hlist : (((order S (pre ++ K0 :: post)).map gA ++ [pathSubtree v chain M]).map norm).filter (keep S) =
          ((order S (pre ++ K0 :: post)) ++ [K0]).map h1 := by
        rw [List.map_append, List.map_map, List.filter_append, List.map_append]
        congr 1
        · rw [List.filter_eq_self.2]
          · apply List.map_congr_left
            intro K hK
            simp only [Function.comp]
            rw [hh1f K (hτ_occ K hK)]
            unfold gA; rw [norm_idem]
          · intro x hx
            obtain ⟨K, hK, rfl⟩ := List.mem_map.1 hx
            simp only [Function.comp]
            unfold gA; rw [norm_idem]
            exact (mem_kept.1 (hτk K hK)).2
        · simp only [List.map_cons, List.map_nil, hh1t]
          rw [List.filter_cons_of_pos hbrn, List.filter_nil]
      rw [hlist]
      refine align' (Dom.refl _) _ h1 (fN v) ((fkept v S (pre ++ K0 :: post)).map (fN v)) ?_ ?_ hdist
      · exact ((order_perm _ _).append_right [K0] |>.trans hpermK).map _
      · intro K hK
        rcases List.mem_append.1 hK with h | h
        · rw [hh1f K (hτ_occ K h), fN_of_not_occ v (hτ_occ K h)]
          exact DomC.refl _
        · rw [List.mem_singleton] at h
          subst h
          rw [hh1t]
          exact hbrd

end Lax117284Proofs.Treewidth.Chars
