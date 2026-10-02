import Lax117284Proofs.Treewidth.Chars.TablesIntroA

/-!
# `introC` preserves well-formedness (part 3): new branches, top plans, and the whole of `IR`
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem chain_sub {X : Finset ℕ} : ∀ {rest : List (Finset ℕ)}, (X :: rest).IsChain (fun X Y => Y ⊂ X) →
    ∀ Y ∈ rest, Y ⊆ X := by
  intro rest
  induction rest generalizing X with
  | nil => intro _ Y hY; simp at hY
  | cons Z rest ih =>
    intro h Y hY
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.1 hY with rfl | hY
    · exact h.1.subset
    · exact (ih h.2 Y hY).trans h.1.subset

theorem pathSubtree_cons (v : ℕ) (X : Finset ℕ) (rest : List (Finset ℕ)) (M : Finset ℕ) :
    pathSubtree v (X :: rest) M = node X [X.card] [pathSubtree v rest M] := rfl

theorem pathSubtree_nil (v : ℕ) (M : Finset ℕ) : pathSubtree v [] M = node (insert v M) [M.card + 1] [] := rfl

theorem ps_aux (v : ℕ) (B M : Finset ℕ) : ∀ (chain : List (Finset ℕ)) (σ : Finset ℕ),
    (∀ X ∈ chain, X ⊆ σ) → chain.IsChain (fun X Y => Y ⊂ X) → M ⊆ chain.getLastD σ → v ∉ σ → σ ⊆ B →
    Loc (insert v B) (pathSubtree v chain M) ∧ Conn (pathSubtree v chain M) ∧
      verts (pathSubtree v chain M) ⊆ insert v (pathSubtree v chain M).S ∧
      (pathSubtree v chain M).S ⊆ insert v σ ∧ v ∈ verts (pathSubtree v chain M)
  | [], σ, hX, hch, hM, hvσ, hσB => by
    rw [pathSubtree_nil]
    have hMσ : M ⊆ σ := by simpa using hM
    refine ⟨⟨Finset.insert_subset_insert v (hMσ.trans hσB), typical_singleton _, by simp, ?_, trivial⟩, ⟨trivial, by simp, by simp⟩, ?_, ?_, ?_⟩
    · intro e he; simp at he; subst he; exact Finset.card_insert_le _ _
    · intro u hu
      simp only [verts, vertsL, Finset.union_empty] at hu
      show u ∈ insert v (insert v M)
      exact Finset.mem_insert_of_mem hu
    · show insert v M ⊆ insert v σ
      exact Finset.insert_subset_insert v hMσ
    · simp [verts, vertsL]
  | X :: rest, σ, hX, hch, hM, hvσ, hσB => by
    rw [pathSubtree_cons]
    have hXσ : X ⊆ σ := hX X (by simp)
    have hrest : ∀ Y ∈ rest, Y ⊆ X := chain_sub hch
    have hch' : rest.IsChain (fun X Y => Y ⊂ X) := by
      cases rest with
      | nil => exact List.IsChain.nil
      | cons Y r => exact (List.isChain_cons_cons.1 hch).2
    have hM' : M ⊆ rest.getLastD X := by rwa [List.getLastD_cons] at hM
    obtain ⟨l, c, hv1, hs, hvv⟩ := ps_aux v B M rest X hrest hch' hM' (fun h => hvσ (hXσ h)) (hXσ.trans hσB)
    refine ⟨⟨(hXσ.trans hσB).trans (Finset.subset_insert v B), typical_singleton _, by simp, ?_, l, trivial⟩,
      ⟨⟨c, trivial⟩, ?_, by simp⟩, ?_, ?_, ?_⟩
    · intro e he; simp at he; omega
    · intro k hk u hu huk
      rw [List.mem_singleton] at hk; subst hk
      rcases Finset.mem_insert.1 (hv1 huk) with rfl | h
      · exact absurd (hXσ hu) hvσ
      · exact h
    · intro u hu
      simp only [verts, vertsL, Finset.union_empty, Finset.mem_union] at hu
      show u ∈ insert v X
      rcases hu with hu | hu
      · exact Finset.mem_insert_of_mem hu
      · rcases Finset.mem_insert.1 (hv1 hu) with rfl | h
        · exact Finset.mem_insert_self _ _
        · rcases Finset.mem_insert.1 (hs h) with rfl | h'
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem h'
    · exact hXσ.trans (Finset.subset_insert _ _)
    · exact mem_verts.2 (Or.inr ⟨_, List.mem_singleton_self _, hvv⟩)

theorem wtopR_aux (v : ℕ) (B : Finset ℕ) (hvB : v ∉ B) {t r : CT} {c : Finset ℕ} (hw : WtopR v t r c)
    (hl : Loc B t) (hc : Conn t) (hv : v ∉ verts t) :
    Loc (insert v B) r ∧ Conn r ∧ (∀ u, u ∈ verts r ↔ u = v ∨ u ∈ verts t) ∧ t.S ⊆ r.S ∧ r.S ⊆ insert v t.S := by
  cases t with
  | node S y ks =>
    rw [WtopR] at hw
    rcases hw with hw | ⟨d1, d2, X, hsp, hX, rfl⟩
    · obtain ⟨a1, a2, a3, a4⟩ := winR_aux v B hvB _ r c hw hl hc hv
      exact ⟨a1, a2, a3, by rw [a4]; exact Finset.subset_insert _ _, by rw [a4]⟩
    · obtain ⟨hlS, hty, hyne, hyge, hlks⟩ := hl
      obtain ⟨t1, n1, e1, t2, n2, e2⟩ := splits_props hty hyge hsp
      obtain ⟨lX, cX, vX, sX⟩ := winR_aux v B hvB (node S d2 ks) X c hX ⟨hlS, t2, n2, e2, hlks⟩ hc hv
      refine ⟨⟨hlS.trans (Finset.subset_insert _ _), t1, n1, e1, lX, trivial⟩, ⟨⟨cX, trivial⟩, ?_, by simp⟩, ?_,
        Finset.Subset.refl _, Finset.subset_insert _ _⟩
      · intro k hk u hu huk
        rw [List.mem_singleton] at hk; subst hk
        rw [sX]; exact Finset.mem_insert_of_mem hu
      · intro u
        have := vX u
        simp only [verts, vertsL, Finset.union_empty, Finset.mem_union] at this ⊢
        tauto

theorem attR_aux (v : ℕ) (B : Finset ℕ) (hvB : v ∉ B) (N : Finset ℕ) {t r : CT} (hw : AttR v N t r)
    (hl : Loc B t) (hc : Conn t) (hv : v ∉ verts t) :
    Loc (insert v B) r ∧ Conn r ∧ (∀ u, u ∈ verts r ↔ u = v ∨ u ∈ verts t) ∧ t.S ⊆ r.S ∧ r.S ⊆ insert v t.S := by
  cases t with
  | node S y ks =>
    rw [AttR] at hw
    obtain ⟨chain, M, hcm, hr⟩ := hw
    obtain ⟨hlS, hty, hyne, hyge, hlks⟩ := hl
    obtain ⟨hX, hch, hNM, hM⟩ := mem_allChains.1 hcm
    have hvS : v ∉ S := fun h => hvB (hlS h)
    obtain ⟨lbr, cbr, hbrv, hbrS, hvbr⟩ := ps_aux v B M chain S (fun X h => (hX X h).2) hch hM hvS hlS
    set br := pathSubtree v chain M with hbr
    have hcS : KidsConn S ks := hc
    have hvks : ∀ k ∈ ks, v ∉ verts k := fun k hk h => hv (mem_verts.2 (Or.inr ⟨k, hk, h⟩))
    have hbr1 : ∀ u ∈ S, u ∈ verts br → u ∈ br.S := by
      intro u hu hub
      rcases Finset.mem_insert.1 (hbrv hub) with rfl | h
      · exact absurd hu hvS
      · exact h
    have hbr2 : ∀ k ∈ ks, ∀ u, u ∈ verts k → u ∈ verts br → u ∈ S := by
      intro k hk u huk hub
      rcases Finset.mem_insert.1 (hbrv hub) with rfl | h
      · exact absurd huk (hvks k hk)
      · rcases Finset.mem_insert.1 (hbrS h) with rfl | h'
        · exact absurd huk (hvks k hk)
        · exact h'
    have hlks' : ∀ k ∈ ks, Loc (insert v B) k := fun k hk =>
      loc_mono (Finset.subset_insert _ _) k (LocL_iff.1 hlks k hk)
    rcases hr with rfl | ⟨d1, d2, hsp, rfl⟩
    · refine ⟨⟨hlS.trans (Finset.subset_insert _ _), hty, hyne, hyge, ?_⟩, ⟨?_, ?_, ?_⟩, ?_,
        Finset.Subset.refl _, Finset.subset_insert _ _⟩
      · rw [LocL_iff]
        intro k hk
        rcases List.mem_append.1 hk with hk | hk
        · exact hlks' k hk
        · rw [List.mem_singleton] at hk; subst hk; exact lbr
      · rw [ConnL_iff]
        intro k hk
        rcases List.mem_append.1 hk with hk | hk
        · exact (ConnL_iff.1 hcS.1) k hk
        · rw [List.mem_singleton] at hk; subst hk; exact cbr
      · intro k hk u hu huk
        rcases List.mem_append.1 hk with hk | hk
        · exact hcS.2.1 k hk u hu huk
        · rw [List.mem_singleton] at hk; subst hk; exact hbr1 u hu huk
      · rw [List.pairwise_append]
        refine ⟨hcS.2.2, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb u hua hub
        rw [List.mem_singleton] at hb; subst hb
        exact hbr2 a ha u hua hub
      · intro u
        rw [mem_verts, mem_verts]
        constructor
        · rintro (h | ⟨k, hk, huk⟩)
          · exact Or.inr (Or.inl h)
          · rcases List.mem_append.1 hk with hk | hk
            · exact Or.inr (Or.inr ⟨k, hk, huk⟩)
            · rw [List.mem_singleton] at hk; subst hk
              rcases Finset.mem_insert.1 (hbrv huk) with rfl | h
              · exact Or.inl rfl
              · rcases Finset.mem_insert.1 (hbrS h) with rfl | h'
                · exact Or.inl rfl
                · exact Or.inr (Or.inl h')
        · rintro (rfl | h | ⟨k, hk, huk⟩)
          · exact Or.inr ⟨br, List.mem_append_right _ (List.mem_singleton_self _), hvbr⟩
          · exact Or.inl h
          · exact Or.inr ⟨k, List.mem_append_left _ hk, huk⟩
    · obtain ⟨t1, n1, e1, t2, n2, e2⟩ := splits_props hty hyge hsp
      have hk2 : Loc (insert v B) (node S d2 ks) := ⟨hlS.trans (Finset.subset_insert _ _), t2, n2, e2,
        locL_mono (Finset.subset_insert _ _) ks hlks⟩
      refine ⟨⟨hlS.trans (Finset.subset_insert _ _), t1, n1, e1, lbr, hk2, trivial⟩,
        ⟨⟨cbr, hc, trivial⟩, ?_, ?_⟩, ?_, Finset.Subset.refl _, Finset.subset_insert _ _⟩
      · intro k hk u hu huk
        rcases List.mem_cons.1 hk with rfl | hk
        · exact hbr1 u hu huk
        · rw [List.mem_singleton] at hk; subst hk
          exact hu
      · rw [List.pairwise_cons]
        refine ⟨?_, List.pairwise_singleton _ _⟩
        intro b hb u hub hub2
        rw [List.mem_singleton] at hb; subst hb
        rcases Finset.mem_insert.1 (hbrv hub) with rfl | h
        · exact absurd hub2 hv
        · rcases Finset.mem_insert.1 (hbrS h) with rfl | h'
          · exact absurd hub2 hv
          · exact h'
      · intro u
        simp only [verts, vertsL, Finset.union_empty, Finset.mem_union]
        constructor
        · rintro (h | h | h | h)
          · exact Or.inr (Or.inl h)
          · rcases Finset.mem_insert.1 (hbrv h) with rfl | h
            · exact Or.inl rfl
            · rcases Finset.mem_insert.1 (hbrS h) with rfl | h'
              · exact Or.inl rfl
              · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
        · rintro (rfl | h | h)
          · exact Or.inr (Or.inl hvbr)
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr h))

theorem ir_aux (v : ℕ) (B : Finset ℕ) (hvB : v ∉ B) (N : Finset ℕ) {t r : CT} (h : IR v N t r) :
    Loc B t → Conn t → v ∉ verts t →
    Loc (insert v B) r ∧ Conn r ∧ (∀ u, u ∈ verts r ↔ u = v ∨ u ∈ verts t) ∧ t.S ⊆ r.S ∧ r.S ⊆ insert v t.S := by
  induction h with
  | top hw _ => intro hl hc hv; exact wtopR_aux v B hvB hw hl hc hv
  | att _ hw => intro hl hc hv; exact attR_aux v B hvB N hw hl hc hv
  | @kid S y pre k post r' hir ih =>
    intro hl hc hv
    obtain ⟨hlS, hty, hyne, hyge, hlks⟩ := hl
    have hcS : KidsConn S (pre ++ k :: post) := hc
    have hvS : v ∉ S := fun h => hvB (hlS h)
    have hvks : ∀ q ∈ pre ++ k :: post, v ∉ verts q := fun q hq h => hv (mem_verts.2 (Or.inr ⟨q, hq, h⟩))
    have hlk : Loc B k := LocL_iff.1 hlks k (by simp)
    have hck : Conn k := ConnL_iff.1 hcS.1 k (by simp)
    obtain ⟨lr, cr, vr, s1, s2⟩ := ih hlk hck (hvks k (by simp))
    have hlks' : ∀ q ∈ pre ++ k :: post, Loc (insert v B) q := fun q hq =>
      loc_mono (Finset.subset_insert _ _) q (LocL_iff.1 hlks q hq)
    refine ⟨⟨hlS.trans (Finset.subset_insert _ _), hty, hyne, hyge, ?_⟩, ⟨?_, ?_, ?_⟩, ?_,
      Finset.Subset.refl _, Finset.subset_insert _ _⟩
    · rw [LocL_iff]
      intro q hq
      rw [List.mem_append, List.mem_cons] at hq
      rcases hq with hq | rfl | hq
      · exact hlks' q (by simp [hq])
      · exact lr
      · exact hlks' q (by simp [hq])
    · rw [ConnL_iff]
      intro q hq
      rw [List.mem_append, List.mem_cons] at hq
      rcases hq with hq | rfl | hq
      · exact ConnL_iff.1 hcS.1 q (by simp [hq])
      · exact cr
      · exact ConnL_iff.1 hcS.1 q (by simp [hq])
    · intro q hq u hu huq
      rw [List.mem_append, List.mem_cons] at hq
      rcases hq with hq | rfl | hq
      · exact hcS.2.1 q (by simp [hq]) u hu huq
      · rcases (vr u).1 huq with rfl | hh
        · exact absurd hu hvS
        · exact s1 (hcS.2.1 k (by simp) u hu hh)
      · exact hcS.2.1 q (by simp [hq]) u hu huq
    · have hp := hcS.2.2
      rw [List.pairwise_append] at hp ⊢
      obtain ⟨hp1, hp2, hp3⟩ := hp
      rw [List.pairwise_cons] at hp2 ⊢
      refine ⟨hp1, ⟨?_, hp2.2⟩, ?_⟩
      · intro b hb u hur hub
        rcases (vr u).1 hur with rfl | hh
        · exact absurd hub (hvks b (by simp [hb]))
        · exact hp2.1 b hb u hh hub
      · intro a ha b hb u hua hub
        rw [List.mem_cons] at hb
        rcases hb with rfl | hb
        · rcases (vr u).1 hub with rfl | hh
          · exact absurd hua (hvks a (by simp [ha]))
          · exact hp3 a ha k (by simp) u hua hh
        · exact hp3 a ha b (by simp [hb]) u hua hub
    · intro u
      rw [mem_verts, mem_verts]
      constructor
      · rintro (h | ⟨q, hq, huq⟩)
        · exact Or.inr (Or.inl h)
        · rw [List.mem_append, List.mem_cons] at hq
          rcases hq with hq | rfl | hq
          · exact Or.inr (Or.inr ⟨q, by simp [hq], huq⟩)
          · rcases (vr u).1 huq with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr ⟨k, by simp, h⟩)
          · exact Or.inr (Or.inr ⟨q, by simp [hq], huq⟩)
      · rintro (rfl | h | ⟨q, hq, huq⟩)
        · exact Or.inr ⟨r', by simp, (vr _).2 (Or.inl rfl)⟩
        · exact Or.inl h
        · rw [List.mem_append, List.mem_cons] at hq
          rcases hq with hq | rfl | hq
          · exact Or.inr ⟨q, by simp [hq], huq⟩
          · exact Or.inr ⟨r', by simp, (vr _).2 (Or.inr huq)⟩
          · exact Or.inr ⟨q, by simp [hq], huq⟩

end Lax117284Proofs.Treewidth.Chars
