import Lax117284Proofs.Treewidth.Chars.IntroSetup

/-!
# The induction step at a flagged node (work package C4, part 10)

`step_R`: `P = node S e true ks` (its region `W` contains the root).  The plan is the *whole* plan: every kept kid is
left alone (unoccupied) or entered (flagged); in the *merge* shape of the source the region continues into, or ends
at, the merged run.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT FT

theorem fkept_map (v : ℕ) (S1 : Finset ℕ) (ks : List FT) :
    (fkept v S1 ks).map (fN v) = ((ks.map (fT v)).map norm).filter (keep S1) := by
  rw [List.map_map]
  show (ks.filter (fun K => keep S1 (fN v K))).map (fN v) = (ks.map (fun K => norm (fT v K))).filter (keep S1)
  rw [List.filter_map]
  rfl

theorem T_dist {v : ℕ} {S1 : Finset ℕ} {ks : List FT} {y : List ℕ}
    (hc : Conn (CT.node S1 y (ks.map (fT v)))) :
    ((fkept v S1 ks).map (fN v)).Pairwise (fun a b => key S1 a ≠ key S1 b) := by
  rw [fkept_map]
  exact survivors_keys_distinct ((conn_node).1 hc)

theorem fkept_eq_kept {v : ℕ} {S S1 : Finset ℕ} {ks : List FT}
    (h : ∀ K ∈ ks, keep S1 (fN v K) = keep S (gA K)) : fkept v S1 ks = kept S ks := by
  unfold fkept kept
  exact List.filter_congr (fun K hK => h K hK)

theorem cov_junk {S : Finset ℕ} {K : FT} (h : keep S (gA K) = false) : cov K ⊆ S := by
  have hn := (keep_norm_false_iff S (uT K)).1 h
  exact (cov_le_verts K).trans ((verts_nested S _ hn).trans (nested_root_sub hn))

theorem winR_shape {v : ℕ} {S : Finset ℕ} {y : List ℕ} {ks : List CT} {r : CT} {c : Finset ℕ}
    (h : WinR v (CT.node S y ks) r c) : ∃ y1 kids1, r = CT.node (insert v S) y1 kids1 := by
  rcases h with ⟨d1, d2, hd, rfl, rfl⟩ | ⟨kids, cv, hk, rfl, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

mutual
theorem yne_uT : ∀ K : FT, YNe (uT K)
  | FT.node S' e w ks => by
    rw [uT]
    exact ⟨by simp, yneL_uTL ks⟩
theorem yneL_uTL : ∀ ks : List FT, YNeL (uTL ks)
  | [] => trivial
  | k :: ks => ⟨yne_uT k, yneL_uTL ks⟩
end

theorem gA_y_ne (K : FT) : (gA K).y ≠ [] := by
  have := yne_norm _ (yne_uT K)
  unfold gA
  revert this
  generalize norm (uT K) = q
  intro this
  cases q with
  | node S' y' ks' => exact this.1

/-- **The induction step at a flagged node.** -/
theorem step_R (v : ℕ) (S : Finset ℕ) (e : ℕ) (ks : List FT)
    (hok : FOk v (node S e true ks))
    (hc : Conn (fT v (node S e true ks)))
    (IH : ∀ K ∈ ks, K.w = true → ∃ r c, WinR v (gA K) r c ∧ cov K ⊆ c ∧ DomC (norm r) (fN v K)) :
    ∃ r c, WinR v (norm (uT (node S e true ks))) r c ∧ cov (node S e true ks) ⊆ c ∧
      DomC (norm r) (norm (fT v (node S e true ks))) := by
  have hvS : v ∉ S := hok.1
  have hSe : S.card ≤ e := hok.2.1
  have hkids := hok.2.2.1 rfl
  have hkOk : ∀ K ∈ ks, FOk v K := FOkL_iff.1 hok.2.2.2.2
  have hflag : ∀ K ∈ ks, K.w = true ∨ occ K = false := by
    intro K hK
    by_cases h : occ K = true
    · exact Or.inl (hkids K hK h)
    · exact Or.inr (by simpa using h)
  have hkeepK : ∀ K ∈ ks, keep (insert v S) (fN v K) = keep S (gA K) :=
    fun K hK => keep_flag v (hkOk K hK) (hflag K hK) S
  have hfk : fkept v (insert v S) ks = kept S ks := fkept_eq_kept hkeepK
  have hTeq : norm (fT v (node S e true ks)) = normF (insert v S) [e + 1] ((kept S ks).map (fN v)) := by
    rw [T_eq, ← hfk]; rfl
  have hdist : ((kept S ks).map (fN v)).Pairwise (fun a b => key (insert v S) a ≠ key (insert v S) b) := by
    rw [← hfk]
    have hc' : Conn (CT.node (insert v S) [e + 1] (ks.map (fT v))) := by rw [fT_node] at hc; exact hc
    exact T_dist hc'
  have hex : ∀ K ∈ ks, ∃ r c, ((K.w = false ∧ r = gA K ∧ c = ∅ ∧ cov K = ∅ ∧ fN v K = gA K)) ∨
      (K.w = true ∧ WinR v (gA K) r c ∧ cov K ⊆ c ∧ DomC (norm r) (fN v K)) := by
    intro K hK
    by_cases hw : K.w = true
    · obtain ⟨r, c, h1, h2, h3⟩ := IH K hK hw
      exact ⟨r, c, Or.inr ⟨hw, h1, h2, h3⟩⟩
    · have hocc : occ K = false := (hflag K hK).resolve_left hw
      exact ⟨gA K, ∅, Or.inl ⟨by simpa using hw, rfl, rfl, cov_of_not_occ K hocc, by unfold fN gA; rw [fT_of_not_occ v K hocc]⟩⟩
  have : Nonempty CT := ⟨CT.start⟩
  choose! rK cK hspec using hex
  have hdom : ∀ K ∈ ks, DomC (norm (rK K)) (fN v K) := by
    intro K hK
    rcases hspec K hK with ⟨-, h1, h2, h3, h4⟩ | ⟨-, -, -, h⟩
    · rw [h1, h4]
      unfold gA; rw [norm_idem]; exact DomC.refl _
    · exact h
  have hopt : ∀ K ∈ ks, (rK K = gA K ∧ cK K = ∅) ∨ WinR v (gA K) (rK K) (cK K) := by
    intro K hK
    rcases hspec K hK with ⟨-, h1, h2, -, -⟩ | ⟨-, h, -, -⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr h
  have hcovK : ∀ K ∈ ks, cov K ⊆ cK K := by
    intro K hK
    rcases hspec K hK with ⟨-, -, h2, h3, -⟩ | ⟨-, -, h, -⟩
    · rw [h3]; exact Finset.empty_subset _
    · exact h
  rw [hTeq]
  by_cases hmerge : ∃ K1, kept S ks = [K1] ∧ (gA K1).S = S
  · obtain ⟨K1, hσ, hS⟩ := hmerge
    have hK1mem : K1 ∈ kept S ks := by rw [hσ]; simp
    have hK1 := mem_kept.1 hK1mem
    have hcases : ∀ K ∈ ks, K = K1 ∨ keep S (gA K) = false := by
      intro K hK
      by_cases hkeep : keep S (gA K) = true
      · have : K ∈ kept S ks := mem_kept.2 ⟨hK, hkeep⟩
        rw [hσ] at this
        exact Or.inl (by simpa using this)
      · exact Or.inr (by simpa using hkeep)
    have hcovle : ∀ c : Finset ℕ, cov K1 ⊆ c → S ⊆ c → cov (node S e true ks) ⊆ c := by
      intro c h1 h2 x hx
      simp only [cov, if_true] at hx
      rcases Finset.mem_union.1 hx with h | h
      · exact h2 h
      · obtain ⟨K, hK, hxK⟩ := mem_covL.1 h
        rcases hcases K hK with rfl | hj
        · exact h1 hxK
        · exact h2 (cov_junk hj hxK)
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
    rw [FT.a_merge S e true ks hσ hS, hσ, hgA]
    simp only [List.map_cons, List.map_nil, CT.y, CT.kids]
    have hDom : DomC (CT.node S (typical ([e] ++ yk)) kk) (CT.node S ([e] ++ yk) kk) :=
      ⟨rfl, (domEquiv_typical _).1, domCL_iff.2 (List.forall₂_same.2 (fun k _ => DomC.refl k))⟩
    by_cases hw1 : K1.w = true
    · -- the region continues into the merged run
      obtain ⟨-, hW, hcov1, hdom1⟩ : K1.w = true ∧ WinR v (gA K1) (rK K1) (cK K1) ∧ cov K1 ⊆ cK K1 ∧
          DomC (norm (rK K1)) (fN v K1) := by
        rcases hspec K1 hK1.1 with ⟨hw', -⟩ | h
        · exact absurd hw' (by simp [hw1])
        · exact h
      rw [hgA] at hW
      obtain ⟨y1, kids1, hr1⟩ := winR_shape hW
      obtain ⟨r'', hW'', hr''⟩ := winR_prefix v S yk kk [e] hW
      obtain ⟨r, hr, hd⟩ := winR_mono v _ _ hDom r'' _ hW''
      refine ⟨r, cK K1, hr, hcovle _ hcov1 (winR_cov_ge hW), ?_⟩
      refine DomC.trans (norm_mono hd) ?_
      rw [hr'', hr1]
      have hk1 : keep (insert v S) (fN v K1) = true := by rw [hkeepK K1 hK1.1]; exact hK1.2
      rw [hr1] at hdom1
      exact merge_cmp (S' := insert v S) (e' := plus1 [e]) (by simp [plus1]) hdom1 hk1
    · -- the region ends at the junction
      have hw1' : K1.w = false := by simpa using hw1
      have hocc : occ K1 = false := (hflag K1 hK1.1).resolve_left hw1
      have hfN : fN v K1 = gA K1 := by unfold fN gA; rw [fT_of_not_occ v K1 hocc]
      have hW' := winR_end v S kk (s := [e]) (by simp) hy
      obtain ⟨r, hr, hd⟩ := winR_mono v _ _ hDom _ _ hW'
      refine ⟨r, S, hr, hcovle S (by rw [cov_of_not_occ K1 hocc]; exact Finset.empty_subset _) subset_rfl, ?_⟩
      refine DomC.trans (norm_mono hd) ?_
      have hnk : norm (CT.node S yk kk) = CT.node S yk kk := by rw [← hgA]; unfold gA; exact norm_idem _
      have hkeep1 : keep (insert v S) (CT.node S yk kk) = true := by
        rw [← hgA, ← hfN, hkeepK K1 hK1.1]; exact hK1.2
      rw [norm_node']
      simp only [List.map_cons, List.map_nil, hnk, List.filter_cons_of_pos hkeep1, List.filter_nil]
      rw [hfN, hgA]
      exact DomC.refl _
  · have hnm : ∀ K1, kept S ks = [K1] → (gA K1).S ≠ S := fun K1 h1 h2 => hmerge ⟨K1, h1, h2⟩
    rw [FT.a_nonmerge S e true ks hnm]
    have hτks : ∀ K ∈ order S ks, K ∈ ks := fun K hK => (mem_kept.1 ((order_perm S ks).mem_iff.1 hK)).1
    obtain ⟨cv, hkid, hsub⟩ := kidR_of_forall v gA rK cK (order S ks) (fun K hK => hopt K (hτks K hK))
    refine ⟨CT.node (insert v S) (plus1 [e]) ((order S ks).map rK), S ∪ cv,
      Or.inr ⟨(order S ks).map rK, cv, hkid, rfl, rfl⟩, ?_, ?_⟩
    · intro x hx
      simp only [cov, if_true] at hx
      rcases Finset.mem_union.1 hx with h | h
      · exact Finset.mem_union_left _ h
      · obtain ⟨K, hK, hxK⟩ := mem_covL.1 h
        by_cases hkeep : keep S (gA K) = true
        · have hKτ : K ∈ order S ks := (order_perm S ks).mem_iff.2 (mem_kept.2 ⟨hK, hkeep⟩)
          exact Finset.mem_union_right _ (hsub K hKτ (hcovK K hK hxK))
        · have : keep S (gA K) = false := by simpa using hkeep
          exact Finset.mem_union_left _ (cov_junk this hxK)
    · rw [norm_node']
      have hτ : ∀ K ∈ order S ks, keep (insert v S) (norm (rK K)) = true := by
        intro K hK
        have hKk := mem_kept.1 ((order_perm S ks).mem_iff.1 hK)
        rw [domC_keep _ (hdom K hKk.1), hkeepK K hKk.1]
        exact hKk.2
      have hfilt : (((order S ks).map rK).map norm).filter (keep (insert v S)) = (order S ks).map (norm ∘ rK) := by
        rw [List.map_map]
        apply List.filter_eq_self.2
        intro x hx
        obtain ⟨K, hK, rfl⟩ := List.mem_map.1 hx
        exact hτ K hK
      rw [hfilt]
      exact align' (Dom.refl _) (order S ks) (norm ∘ rK) (fN v) ((kept S ks).map (fN v))
        ((order_perm S ks).map _) (fun K hK => hdom K (hτks K hK)) hdist

end Lax117284Proofs.Treewidth.Chars
