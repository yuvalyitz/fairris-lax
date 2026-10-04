import Lax117284Proofs.Treewidth.Chars.IntroSetup
import Lax117284Proofs.Treewidth.Chars.Forget
import Lax117284Proofs.Treewidth.Chars.JoinShape
import Lax117284Proofs.Treewidth.Chars.Join
import Lax117284Proofs.Treewidth.Trees.Bridge1Restrict
import Lax117284Proofs.Treewidth.Chars.Leaf
import Lax117284Proofs.Treewidth.Chars.Restrict

/-! ### `Lax117284Proofs.Treewidth.Chars.IntroMainR` -/

section
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
theorem yne_uT_rec : ∀ K : FT, YNe (uT K)
  | FT.node S' e w ks => by
    rw [uT]
    exact ⟨by simp, yneL_uTL_rec ks⟩
theorem yneL_uTL_rec : ∀ ks : List FT, YNeL (uTL ks)
  | [] => trivial
  | k :: ks => ⟨yne_uT_rec k, yneL_uTL_rec ks⟩
end

theorem yne_uT_pair : (type_of% @yne_uT_rec) ∧ (type_of% @yneL_uTL_rec) :=
  ⟨@yne_uT_rec, @yneL_uTL_rec⟩

theorem yne_uT : type_of% @yne_uT_rec := yne_uT_pair.1

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

end

/-! ### `Lax117284Proofs.Treewidth.Chars.IntroMainI` -/

section
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

end

/-! ### `Lax117284Proofs.Treewidth.Chars.IntroMain` -/

section
/-!
# `char_intro_dom` (work package C4, part 12)

`main_intro` — the FT-level statement (one induction on the flagged profile tree); `mkFT` — the flagged profile tree of
a real decomposition; `char_intro_dom` — the assembly.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT FT

/-- **The introduction on flagged profile trees.** -/
theorem main_intro (v : ℕ) : ∀ P : FT, FOk v P → Conn (fT v P) →
    (P.w = true → ∃ r c, WinR v (gA P) r c ∧ cov P ⊆ c ∧ DomC (norm r) (fN v P)) ∧
    (P.w = false → occ P = true → ∀ N : Finset ℕ, N ⊆ cov P →
      ∃ r, IR v N (gA P) r ∧ DomC (norm r) (fN v P)) := by
  intro P
  induction P using FT.ind with
  | _ S e w ks ih =>
    intro hok hc
    have hkOk : ∀ K ∈ ks, FOk v K := FOkL_iff.1 hok.2.2.2.2
    have hkConn : ∀ K ∈ ks, Conn (fT v K) := by
      have hc' : Conn (CT.node (if w then insert v S else S) [if w then e + 1 else e] (ks.map (fT v))) := by
        rw [fT_node] at hc; exact hc
      have := ((conn_node).1 hc').1
      intro K hK
      exact (ConnL_iff.1 this) (fT v K) (List.mem_map.2 ⟨K, hK, rfl⟩)
    have hIH := fun K hK => ih K hK (hkOk K hK) (hkConn K hK)
    refine ⟨?_, ?_⟩
    · intro hw
      have hw' : w = true := hw
      subst hw'
      exact step_R v S e ks hok hc (fun K hK hwK => (hIH K hK).1 hwK)
    · intro hw hocc N hN
      have hw' : w = false := hw
      subst hw'
      rcases hok.2.2.2.1 rfl with hno | ⟨pre, K0, post, hks, hK0, hpre, hpost⟩
      · simp only [occ, Bool.false_or] at hocc
        rw [hno] at hocc; exact absurd hocc (by simp)
      · subst hks
        exact step_I v N S e pre K0 post hok hK0 hpre hpost hc hN
          (fun hwK => (hIH K0 (by simp)).1 hwK)
          (fun hwK hN0 => (hIH K0 (by simp)).2 hwK hK0 N hN0)

/-! ## the flagged profile tree of a real decomposition -/

mutual
/-- Label `X ∩ B`, size `|X ∩ U|`, flag `v ∈ X`. -/
def mkFT (B U : Finset ℕ) (v : ℕ) : RT → FT
  | .node X ks => FT.node (X ∩ B) (X ∩ U).card (decide (v ∈ X)) (mkFTL B U v ks)
def mkFTL (B U : Finset ℕ) (v : ℕ) : List RT → List FT
  | [] => []
  | k :: ks => mkFT B U v k :: mkFTL B U v ks
end

theorem mkFTL_eq (B U : Finset ℕ) (v : ℕ) (ks : List RT) : mkFTL B U v ks = ks.map (mkFT B U v) := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [mkFTL, ih]

theorem mkFT_node (B U : Finset ℕ) (v : ℕ) (X : Finset ℕ) (ks : List RT) :
    mkFT B U v (.node X ks) = FT.node (X ∩ B) (X ∩ U).card (decide (v ∈ X)) (ks.map (mkFT B U v)) := by
  simp [mkFT, mkFTL_eq]

theorem uT_mkFT (B U : Finset ℕ) (v : ℕ) : ∀ t : RT,
    uT (mkFT B U v t) = RT.profF (fun X => (X ∩ U).card) B t := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    rw [mkFT_node, uT_node, RT.profF_node]
    congr 1
    rw [List.map_map]
    exact List.map_congr_left (fun k hk => ih k hk)

theorem fT_mkFT (B U : Finset ℕ) (v : ℕ) (hvU : v ∉ U) (hvB : v ∉ B) : ∀ t : RT,
    (∀ X ∈ t.bags, X ⊆ insert v U) → fT v (mkFT B U v t) = RT.prof (insert v B) t := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro hX
    have hXX : X ⊆ insert v U := hX X ((RT.bags_node X ks).2 (Or.inl rfl))
    rw [mkFT_node, fT_node, RT.prof_node]
    have hlab : (if decide (v ∈ X) = true then insert v (X ∩ B) else X ∩ B) = X ∩ insert v B := by
      by_cases hv : v ∈ X
      · rw [decide_eq_true hv]
        simp only [if_true]
        ext x
        simp only [Finset.mem_insert, Finset.mem_inter]
        constructor
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨hv, Or.inl rfl⟩
          · exact ⟨h1, Or.inr h2⟩
        · rintro ⟨h1, h2 | h2⟩
          · exact Or.inl h2
          · exact Or.inr ⟨h1, h2⟩
      · rw [decide_eq_false hv]
        simp only [Bool.false_eq_true, if_false]
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr h2⟩
        · rintro ⟨h1, h2 | h2⟩
          · exact absurd (h2 ▸ h1) hv
          · exact ⟨h1, h2⟩
    have hsize : (if decide (v ∈ X) = true then (X ∩ U).card + 1 else (X ∩ U).card) = X.card := by
      by_cases hv : v ∈ X
      · rw [decide_eq_true hv]
        simp only [if_true]
        have : X = insert v (X ∩ U) := by
          ext x
          simp only [Finset.mem_insert, Finset.mem_inter]
          constructor
          · intro hx
            by_cases hxv : x = v
            · exact Or.inl hxv
            · rcases Finset.mem_insert.1 (hXX hx) with h | h
              · exact absurd h hxv
              · exact Or.inr ⟨hx, h⟩
          · rintro (rfl | ⟨h1, h2⟩)
            · exact hv
            · exact h1
        conv_rhs => rw [this]
        rw [Finset.card_insert_of_notMem (by simp [hvU])]
      · rw [decide_eq_false hv]
        simp only [Bool.false_eq_true, if_false]
        congr 1
        ext x
        simp only [Finset.mem_inter]
        constructor
        · exact fun h => h.1
        · intro hx
          refine ⟨hx, ?_⟩
          rcases Finset.mem_insert.1 (hXX hx) with h | h
          · exact absurd (h ▸ hx) hv
          · exact h
    have hkids : (ks.map (mkFT B U v)).map (fT v) = ks.map (RT.prof (insert v B)) := by
      rw [List.map_map]
      exact List.map_congr_left (fun k hk => ih k hk
        (fun Y hY => hX Y ((RT.bags_node X ks).2 (Or.inr ⟨k, hk, hY⟩))))
    rw [hlab, hsize, hkids]

theorem w_mkFT (B U : Finset ℕ) (v : ℕ) (k : RT) : (mkFT B U v k).w = decide (v ∈ k.rootBag) := by
  cases k; rfl

theorem occ_mkFT (B U : Finset ℕ) (v : ℕ) : ∀ t : RT, occ (mkFT B U v t) = true ↔ v ∈ t.verts := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    rw [mkFT_node, occ_node, RT.verts_node]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_map, List.any_eq_true, Function.comp]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, hk, (ih k hk).1 h⟩
    · rintro (h | ⟨k, hk, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, hk, (ih k hk).2 h⟩

theorem mem_cov_mkFT (B U : Finset ℕ) (v : ℕ) (x : ℕ) : ∀ t : RT,
    x ∈ cov (mkFT B U v t) ↔ ∃ X ∈ t.bags, v ∈ X ∧ x ∈ X ∧ x ∈ B := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    rw [mkFT_node]
    simp only [cov, Finset.mem_union, mem_covL, List.mem_map, RT.bags_node]
    constructor
    · rintro (h | ⟨k', ⟨k, hk, rfl⟩, h⟩)
      · split_ifs at h with hw
        · have hv : v ∈ X := by simpa using hw
          rw [Finset.mem_inter] at h
          exact ⟨X, Or.inl rfl, hv, h⟩
        · simp at h
      · obtain ⟨Y, hY, h'⟩ := (ih k hk).1 h
        exact ⟨Y, Or.inr ⟨k, hk, hY⟩, h'⟩
    · rintro ⟨Y, hY | ⟨k, hk, hY⟩, hvY, hxY, hxB⟩
      · subst hY
        left
        rw [if_pos (by simpa using hvY)]
        exact Finset.mem_inter.2 ⟨hxY, hxB⟩
      · right
        exact ⟨mkFT B U v k, ⟨k, hk, rfl⟩, (ih k hk).2 ⟨Y, hY, hvY, hxY, hxB⟩⟩

theorem decomp_occ {v : ℕ} : ∀ ks : List RT, ks.Pairwise (fun k1 k2 => v ∈ k1.verts → v ∈ k2.verts → False) →
    (∀ k ∈ ks, v ∉ k.verts) ∨ ∃ pre k post, ks = pre ++ k :: post ∧ v ∈ k.verts ∧
      (∀ k' ∈ pre, v ∉ k'.verts) ∧ (∀ k' ∈ post, v ∉ k'.verts) := by
  intro ks
  induction ks with
  | nil => intro _; left; simp
  | cons k ks ih =>
    intro h
    rw [List.pairwise_cons] at h
    by_cases hk : v ∈ k.verts
    · right
      exact ⟨[], k, ks, rfl, hk, by simp, fun k' hk' hv => h.1 k' hk' hk hv⟩
    · rcases ih h.2 with h1 | ⟨pre, k0, post, rfl, h2, h3, h4⟩
      · left
        intro k' hk'
        rcases List.mem_cons.1 hk' with rfl | hk'
        · exact hk
        · exact h1 k' hk'
      · right
        refine ⟨k :: pre, k0, post, rfl, h2, ?_, h4⟩
        intro k' hk'
        rcases List.mem_cons.1 hk' with rfl | hk'
        · exact hk
        · exact h3 k' hk'

theorem FOk_mkFT (B U : Finset ℕ) (v : ℕ) (hB : B ⊆ U) (hvB : v ∉ B) : ∀ t : RT, t.Conn →
    FOk v (mkFT B U v t) := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro hc
    obtain ⟨h1, h2, h3⟩ := (RT.conn_node_iff X ks).1 hc
    rw [mkFT_node]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h; exact hvB (Finset.mem_inter.1 h).2
    · exact Finset.card_le_card (Finset.inter_subset_inter_left hB)
    · intro hw k' hk' hocc
      have hvX : v ∈ X := by simpa using hw
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
      have hv := (occ_mkFT B U v k).1 hocc
      have := h2 k hk v hvX hv
      rw [w_mkFT]
      simpa using this
    · intro hw
      have hvX : v ∉ X := by simpa using hw
      have hpw : ks.Pairwise (fun k1 k2 => v ∈ k1.verts → v ∈ k2.verts → False) :=
        h3.imp (fun {a b} h hva hvb => hvX (h v hva hvb))
      rcases decomp_occ ks hpw with hno | ⟨pre, k0, post, rfl, hk0, hpre, hpost⟩
      · left
        rw [occL_eq_any, List.any_eq_false]
        intro k' hk'
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
        have := hno k hk
        simpa [occ_mkFT B U v k] using this
      · right
        refine ⟨pre.map (mkFT B U v), mkFT B U v k0, post.map (mkFT B U v), by simp, (occ_mkFT B U v k0).2 hk0, ?_, ?_⟩
        · rw [occL_eq_any, List.any_eq_false]
          intro k' hk'
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
          simpa [occ_mkFT B U v k] using hpre k hk
        · rw [occL_eq_any, List.any_eq_false]
          intro k' hk'
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
          simpa [occ_mkFT B U v k] using hpost k hk
    · rw [FOkL_iff]
      intro k' hk'
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
      exact ih k hk (h1 k hk)

theorem maxEntry_prof_le (B : Finset ℕ) {k : ℕ} : ∀ t : RT, t.Width k → maxEntry (RT.prof B t) ≤ k + 1 := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro hw
    rw [RT.prof_node, maxEntry_le_iff]
    refine ⟨?_, ?_⟩
    · intro e he
      simp only [List.mem_singleton] at he
      subst he
      exact hw X ((RT.bags_node X ks).2 (Or.inl rfl))
    · intro k' hk'
      obtain ⟨k0, hk0, rfl⟩ := List.mem_map.1 hk'
      exact ih k0 hk0 (fun Y hY => hw Y ((RT.bags_node X ks).2 (Or.inr ⟨k0, hk0, hY⟩)))

/-- **Introduce** (exact layer + split transport). -/
theorem char_intro_dom {adj : Adj} {v : ℕ} {c : NT} {k : ℕ} {t : RT} (hg : (NT.intro v c).Good adj)
    (h : PTD adj (.intro v c) k t) :
    ∃ c' ∈ CT.introC (k + 1) v (nbrs adj v c.bag) ((t.restrict c.under).char c.bag),
      DomC c' (t.char (insert v c.bag)) := by
  obtain ⟨hvB, -, hvU, -⟩ := hg
  have hBU : c.bag ⊆ c.under := NT.bag_subset_under c
  have hverts : t.verts = insert v c.under := h.1.verts_eq
  have hbags : ∀ X ∈ t.bags, X ⊆ insert v c.under := by
    intro X hX x hx
    rw [← hverts]
    exact (RT.mem_verts_iff t x).2 ⟨X, hX, hx⟩
  have hconn := h.1.conn
  have hok := FOk_mkFT c.bag c.under v hBU hvB t hconn
  have huT := uT_mkFT c.bag c.under v t
  have hfT := fT_mkFT c.bag c.under v hvU hvB t hbags
  have hcf : Conn (fT v (mkFT c.bag c.under v t)) := by rw [hfT]; exact RT.conn_prof _ t hconn
  have hocc : occ (mkFT c.bag c.under v t) = true := (occ_mkFT c.bag c.under v t).2 (by rw [hverts]; simp)
  have hN : nbrs adj v c.bag ⊆ cov (mkFT c.bag c.under v t) := by
    intro w hw
    obtain ⟨hwB, hadj⟩ := Finset.mem_filter.1 hw
    have hwU := hBU hwB
    have hne : v ≠ w := fun e => hvB (e ▸ hwB)
    have hadjG : adj.graph.Adj v w := by
      simp only [Adj.graph, SimpleGraph.fromRel_adj]; exact ⟨hne, Or.inl hadj⟩
    obtain ⟨X, hX, hvX, hwX⟩ := h.1.edges v w hadjG (by simp [NT.under]) (by simp [NT.under, hwU])
    exact (mem_cov_mkFT c.bag c.under v w t).2 ⟨X, hX, hvX, hwX, hwB⟩
  have key : ∃ r, IR v (nbrs adj v c.bag) (norm (uT (mkFT c.bag c.under v t))) r ∧
      DomC (norm r) (norm (fT v (mkFT c.bag c.under v t))) := by
    by_cases hw : (mkFT c.bag c.under v t).w = true
    · obtain ⟨r, c0, h1, h2, h3⟩ := (main_intro v _ hok hcf).1 hw
      exact ⟨r, IR_of_winR v _ h1 (hN.trans h2), h3⟩
    · exact (main_intro v _ hok hcf).2 (by simpa using hw) hocc _ hN
  obtain ⟨r, hr, hd⟩ := key
  have hchar1 : (t.restrict c.under).char c.bag = norm (uT (mkFT c.bag c.under v t)) := by
    unfold RT.char; rw [RT.prof_restrict hBU, huT]
  have hchar2 : t.char (insert v c.bag) = norm (fT v (mkFT c.bag c.under v t)) := by
    unfold RT.char; rw [hfT]
  refine ⟨norm r, ?_, ?_⟩
  · rw [hchar1]
    refine mem_introC.2 ⟨r, hr, rfl, ?_⟩
    refine (maxEntry_dom_le hd).trans ?_
    rw [hfT]
    exact (maxEntry_norm_le _).trans (maxEntry_prof_le _ _ h.2)
  · rw [hchar2]; exact hd

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.TablesComplete` -/

section
/-!
# `tables_complete` (work package C6a)

Every partial decomposition of a good nice tree is dominated (in the characteristic order) by an entry of `tables`.
Induction over the nice tree: leaf (`char_leaf`), forget (`char_forget`, `forgetC_mono`), join (`char_join_dom`,
`joinC_mono`, restriction), introduce (`char_intro_dom`, `introC_mono`, restriction).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem tables_complete {adj : Adj} {k : ℕ} : ∀ {nt : NT}, nt.Good adj → ∀ t, PTD adj nt k t →
    ∃ c ∈ tables adj k nt, DomC c (t.char nt.bag)
  | .leaf, _, t, h => by
    refine ⟨CT.start, by simp [tables], ?_⟩
    have := char_leaf t h
    simp only [NT.bag]
    rw [this]
    exact CT.DomC.refl _
  | .forget x c, hg, t, h => by
    have hgc := hg.2
    have h' : PTD adj c k t := h
    obtain ⟨c0, hc0, hd⟩ := tables_complete hgc t h'
    refine ⟨CT.forgetC x c0, ?_, ?_⟩
    · simp only [tables, forgetTable, List.mem_dedup, List.mem_map]
      exact ⟨c0, hc0, rfl⟩
    · simp only [NT.bag]
      rw [char_forget c.bag x t h.1.conn]
      exact forgetC_mono x hd
  | .join a b, hg, t, h => by
    have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
    obtain ⟨hab, -, hga, hgb, -⟩ := hg'
    obtain ⟨ca, hca, hda⟩ := tables_complete hga _ (PTD.restrict_join_left hg h)
    obtain ⟨cb, hcb, hdb⟩ := tables_complete hgb _ (PTD.restrict_join_right hg h)
    rw [← hab] at hdb
    obtain ⟨c1, hc1, hd1⟩ := char_join_dom hg h
    obtain ⟨c2, hc2, hd2⟩ := joinC_mono (k + 1) hda hdb c1 hc1
    refine ⟨c2, ?_, hd2.trans hd1⟩
    simp only [tables, joinTable, List.mem_dedup, List.mem_flatMap]
    exact ⟨ca, hca, cb, hcb, hc2⟩
  | .intro v c, hg, t, h => by
    have hgc := hg.2.2.2
    obtain ⟨c0, hc0, hd⟩ := tables_complete hgc _ (PTD.restrict_intro hg h)
    obtain ⟨c1, hc1, hd1⟩ := char_intro_dom hg h
    obtain ⟨c2, hc2, hd2⟩ := introC_mono (k + 1) v (nbrs adj v c.bag) hd c1 hc1
    refine ⟨c2, ?_, hd2.trans hd1⟩
    simp only [tables, introTable, List.mem_dedup, List.mem_flatMap]
    exact ⟨c0, hc0, hc2⟩

end Lax117284Proofs.Treewidth.Chars

end
