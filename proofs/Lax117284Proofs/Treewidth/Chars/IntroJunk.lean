import Lax117284Proofs.Treewidth.Chars.IntroFT
import Lax117284Proofs.Treewidth.Chars.IntroChains
import Lax117284Proofs.Treewidth.Seq.Transport

/-!
# Case (b): the region `W` lies in a junk subtree (work package C4, part 7)

`junk_branch`: if the occupied subtree `K` is junk below a run labelled `σ` (`Nested σ (uT K)`), then `norm (fT v K)` is
a branch of strictly nested labels ending in the leaf `S_w ∪ {v}` — dominating the plan's branch `pathSubtree v chain M`
for some `(chain, M) ∈ allChains σ N`.  (The plan's runs carry the sizes of their *labels*, the real ones are larger.)
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## sequences dominating a singleton -/

theorem dom_singleton_of_forall {c : ℕ} {z : List ℕ} (hz : z ≠ []) (h : ∀ x ∈ z, c ≤ x) : Dom [c] z := by
  have h1 : 1 ≤ z.length := List.length_pos_iff.2 hz
  exact ⟨List.replicate z.length c, z, ext_single_replicate h1, Ext.refl z, leSeq_replicate_left h⟩

theorem forall₂_exists_left {R : ℕ → ℕ → Prop} {a b : List ℕ} (h : List.Forall₂ R a b) :
    ∀ y ∈ b, ∃ x ∈ a, R x y := by
  induction h with
  | nil => intro y hy; simp at hy
  | @cons p q as bs hpq _ ih =>
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨p, List.mem_cons_self, hpq⟩
    · obtain ⟨x, hx, hxy⟩ := ih y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩

theorem dom_singleton_le {c : ℕ} {y : List ℕ} (h : Dom [c] y) : ∀ x ∈ y, c ≤ x := by
  obtain ⟨a', b', ha, hb, hle⟩ := h
  intro x hx
  obtain ⟨p, hp, hpx⟩ := forall₂_exists_left hle x ((hb.mem).2 hx)
  have : p = c := by simpa using (ha.mem).1 hp
  omega

/-! ## induction principle for `FT` -/

mutual
theorem FT.ind {P : FT → Prop} (h : ∀ S e w ks, (∀ k ∈ ks, P k) → P (FT.node S e w ks)) : ∀ K : FT, P K
  | FT.node S e w ks => h S e w ks (FT.indL h ks)
theorem FT.indL {P : FT → Prop} (h : ∀ S e w ks, (∀ k ∈ ks, P k) → P (FT.node S e w ks)) :
    ∀ ks : List FT, ∀ k ∈ ks, P k
  | [] => by intro k hk; simp at hk
  | k :: ks => by
    intro k' hk'
    rcases List.mem_cons.1 hk' with e | hk''
    · exact e ▸ FT.ind h k
    · exact FT.indL h ks k' hk''
end

namespace FT

mutual
theorem cov_of_not_occ : ∀ K : FT, occ K = false → cov K = ∅
  | node S e w ks, h => by
    simp only [occ, Bool.or_eq_false_iff] at h
    obtain ⟨rfl, h2⟩ := h
    simp [cov, covL_of_not_occ ks h2]
theorem covL_of_not_occ : ∀ ks : List FT, occL ks = false → covL ks = ∅
  | [], _ => rfl
  | k :: ks, h => by
    simp only [occL, Bool.or_eq_false_iff] at h
    simp [covL, cov_of_not_occ k h.1, covL_of_not_occ ks h.2]
end

end FT

open FT

/-- Membership in `allChains` is preserved when the bound grows (nonempty chain). -/
theorem mem_allChains_bound {S σ N : Finset ℕ} {chain : List (Finset ℕ)} {M : Finset ℕ} (h : (chain, M) ∈ allChains S N)
    (hSσ : S ⊆ σ) (hne : chain ≠ []) : (chain, M) ∈ allChains σ N := by
  rw [mem_allChains] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun X hX => ⟨(h1 X hX).1, (h1 X hX).2.trans hSσ⟩, h2, h3, ?_⟩
  cases chain with
  | nil => exact absurd rfl hne
  | cons X r =>
    rw [List.getLastD_cons] at h4 ⊢
    exact h4

/-- Put the label of the run on top of the chain. -/
theorem mem_allChains_cons {S σ N : Finset ℕ} {chain : List (Finset ℕ)} {M : Finset ℕ}
    (h : (chain, M) ∈ allChains S N) (hSσ : S ⊆ σ) (hhead : ∀ X ∈ chain.head?, X ≠ S) :
    (S :: chain, M) ∈ allChains σ N := by
  rw [mem_allChains] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hNS : N ⊆ S := by
    refine h3.trans (h4.trans ?_)
    cases chain with
    | nil => simp
    | cons X r =>
      -- the last element of the chain lies inside `S`
      have hall : ∀ Y ∈ X :: r, Y ⊆ S := fun Y hY => (h1 Y hY).2
      rw [List.getLastD_eq_getLast?]
      cases hl : (X :: r).getLast? with
      | none => simp at hl
      | some Z => exact hall Z (List.mem_of_getLast? hl)
  refine ⟨?_, ?_, h3, ?_⟩
  · intro Y hY
    rcases List.mem_cons.1 hY with e | hY'
    · rw [e]; exact ⟨hNS, hSσ⟩
    · exact ⟨(h1 Y hY').1, (h1 Y hY').2.trans hSσ⟩
  · cases chain with
    | nil => exact List.IsChain.singleton S
    | cons X r =>
      have hXS : X ⊆ S := (h1 X (by simp)).2
      have hne : X ≠ S := hhead X rfl
      exact List.IsChain.cons_cons (Finset.ssubset_iff_subset_ne.2 ⟨hXS, hne⟩) h2
  · rw [List.getLastD_cons]; exact h4

theorem pathSubtree_nil (v : ℕ) (M : Finset ℕ) : pathSubtree v [] M = CT.node (insert v M) [M.card + 1] [] := rfl
theorem pathSubtree_cons (v : ℕ) (X : Finset ℕ) (r : List (Finset ℕ)) (M : Finset ℕ) :
    pathSubtree v (X :: r) M = CT.node X [X.card] [pathSubtree v r M] := rfl

/-- **Lemma J.** -/
theorem junk_branch (v : ℕ) {N : Finset ℕ} : ∀ K : FT, FOk v K → occ K = true → ∀ σ : Finset ℕ, v ∉ σ →
    Nested σ (uT K) → N ⊆ cov K →
    ∃ chain M, (chain, M) ∈ allChains σ N ∧ DomC (pathSubtree v chain M) (norm (fT v K)) := by
  intro K
  induction K using FT.ind with
  | _ S e w ks ih =>
    intro hok hocc σ hvσ hnest hN
    have hvS : v ∉ S := hok.1
    have hSe : S.card ≤ e := hok.2.1
    have hnest' : Nested σ (CT.node S [e] (ks.map uT)) := by rw [← uT_node]; exact hnest
    have hSσ : S ⊆ σ := hnest'.1
    cases w with
    | true =>
      have hn : Nested (insert v σ) (fT v (FT.node S e true ks)) :=
        (nested_flag v _ hok (Or.inl rfl) σ).2 hnest
      have hN' : N ⊆ S := by
        have := verts_nested σ (CT.node S [e] (ks.map uT)) hnest'
        exact hN.trans ((cov_le_verts _).trans (by simpa [uT_node, CT.S] using this))
      simp only [fT_node, if_true] at hn ⊢
      rw [norm_of_nested hn]
      refine ⟨[], S, mem_allChains.2 ⟨by simp, List.IsChain.nil, hN', by simpa using hSσ⟩, ?_⟩
      refine ⟨rfl, ?_, trivial⟩
      exact dom_singleton_of_forall (by simp) (by
        intro x hx; simp at hx; subst hx; omega)
    | false =>
      simp only [occ, Bool.false_or] at hocc
      rcases hok.2.2.2.1 rfl with hno | ⟨pre, K0, post, hks, hK0, hpre, hpost⟩
      · rw [hno] at hocc; exact absurd hocc (by simp)
      · subst hks
        have hkidsN : ∀ k ∈ pre ++ K0 :: post, Nested S (uT k) := fun k hk =>
          NestedL_iff.1 hnest'.2 (uT k) (List.mem_map.2 ⟨k, hk, rfl⟩)
        have hkidsOk : ∀ k ∈ pre ++ K0 :: post, FOk v k := fun k hk => FOkL_iff.1 hok.2.2.2.2 k hk
        have hother : ∀ k ∈ pre ++ post, keep S (norm (fT v k)) = false := by
          intro k hk
          have hocck : occ k = false := by
            rcases List.mem_append.1 hk with h | h
            · exact occ_of_occL_false hpre k h
            · exact occ_of_occL_false hpost k h
          rw [fT_of_not_occ v k hocck]
          exact (keep_norm_false_iff S (uT k)).2 (hkidsN k (by
            rcases List.mem_append.1 hk with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)))
        have hkeep0 : keep S (norm (fT v K0)) = true := keep_occ v hK0 hvS
        have hnorm : norm (fT v (FT.node S e false (pre ++ K0 :: post))) = normF S [e] [norm (fT v K0)] := by
          simp only [fT_node, if_false, Bool.false_eq_true]
          rw [norm_node']
          congr 1
          have hk0 : keep S ((norm ∘ fT v) K0) = true := hkeep0
          rw [List.map_map, List.map_append, List.map_cons, List.filter_append, List.filter_cons_of_pos hk0]
          have h1 : (pre.map (norm ∘ fT v)).filter (keep S) = [] := by
            rw [List.filter_eq_nil_iff]
            intro n hn
            obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hn
            simpa using hother k (List.mem_append_left _ hk)
          have h2 : (post.map (norm ∘ fT v)).filter (keep S) = [] := by
            rw [List.filter_eq_nil_iff]
            intro n hn
            obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hn
            simpa using hother k (List.mem_append_right _ hk)
          rw [h1, h2]; rfl
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
        obtain ⟨chain0, M0, hc0, hd0⟩ :=
          ih K0 (List.mem_append_right _ (List.mem_cons_self)) (hkidsOk K0 (by simp)) hK0 S hvS
            (hkidsN K0 (by simp)) hN0
        rw [hnorm]
        generalize hT0 : norm (fT v K0) = T0 at hd0 ⊢
        cases T0 with
        | node S0 y0 kk =>
          by_cases hSS : S0 = S
          · -- merge
            have hSS' : S = S0 := hSS.symm
            subst hSS'
            cases chain0 with
            | nil =>
              rw [pathSubtree_nil] at hd0
              have h1 : insert v M0 = S := hd0.1
              exact absurd (h1 ▸ Finset.mem_insert_self v M0) hvS
            | cons X1 rest =>
              rw [pathSubtree_cons] at hd0
              obtain ⟨hX1, hy0, hk0⟩ := hd0
              have hX1' : X1 = S := hX1
              subst hX1'
              refine ⟨X1 :: rest, M0, mem_allChains_bound hc0 hSσ (by simp), ?_⟩
              rw [normF_single, if_pos (show (CT.node X1 y0 kk).S = X1 from rfl), pathSubtree_cons]
              refine ⟨rfl, ?_, hk0⟩
              simp only [CT.y]
              refine dom_singleton_of_forall (typical_ne_nil (by simp)) ?_
              intro x hx
              rcases List.mem_append.1 (mem_of_mem_typical hx) with h | h
              · simp at h; subst h; exact hSe
              · exact dom_singleton_le hy0 x h
          · -- no merge
            rw [normF_single, if_neg (show ¬ (CT.node S0 y0 kk).S = S from hSS)]
            refine ⟨S :: chain0, M0, mem_allChains_cons hc0 hSσ ?_, ?_⟩
            · intro X hX hXS
              cases chain0 with
              | nil => simp at hX
              | cons X1 rest =>
                simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hX
                subst hX
                rw [pathSubtree_cons] at hd0
                exact hSS (hd0.1.symm.trans hXS |>.symm ▸ rfl)
            · rw [pathSubtree_cons]
              refine ⟨rfl, dom_singleton_of_forall (by simp) (by intro x hx; simp at hx; subst hx; exact hSe), hd0, trivial⟩
end Lax117284Proofs.Treewidth.Chars
