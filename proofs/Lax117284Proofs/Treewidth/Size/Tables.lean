import Lax117284Proofs.Treewidth.Chars.IntroMono
import Lax117284Proofs.Treewidth.Chars.IntroChains
import Lax117284Proofs.Treewidth.Chars.NormGood
import Lax117284Proofs.Treewidth.Chars.NormConn
import Lax117284Proofs.Treewidth.Chars.TablesJoin
import Lax117284Proofs.Treewidth.Chars.CountRuns
import Lax117284Proofs.Treewidth.Chars.TablesComplete
import Lax117284Proofs.Treewidth.Chars.CountTables
import Lax117284Proofs.Treewidth.Size.Plans
import Lax117284Proofs.Treewidth.Size.Join

/-! ### `Lax117284Proofs.Treewidth.Chars.TablesIntroA` -/

section
/-!
# `introC` preserves well-formedness (work package C6a, part 2): the region results

`WinR`/`KidR` results (the replacement subtrees of a region `W`) are `Loc`, connected, and add exactly the new vertex
`v` to the vertex set (`winR_aux`, `kidR_aux`).
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- `k'` is `k` or a version of `k` with `v` added (label between `k.S` and `insert v k.S`). -/
def KR (v : ℕ) (k k' : CT) : Prop :=
  k' = k ∨ (verts k' = insert v (verts k) ∧ k.S ⊆ k'.S ∧ k'.S ⊆ insert v k.S)

theorem mem_verts_of_KR {v : ℕ} {k k' : CT} (h : KR v k k') {u : ℕ} (hu : u ∈ verts k') : u = v ∨ u ∈ verts k := by
  rcases h with rfl | ⟨h, -, -⟩
  · exact Or.inr hu
  · rw [h, Finset.mem_insert] at hu; exact hu

theorem verts_sub_of_KR {v : ℕ} {k k' : CT} (h : KR v k k') : verts k ⊆ verts k' := by
  rcases h with rfl | ⟨h, -, -⟩
  · exact fun _ h => h
  · rw [h]; exact Finset.subset_insert _ _

/-! ## `Loc` is monotone in the boundary -/

mutual
theorem loc_mono {B B' : Finset ℕ} (hB : B ⊆ B') : ∀ q : CT, Loc B q → Loc B' q
  | node S y ks, h => ⟨h.1.trans hB, h.2.1, h.2.2.1, h.2.2.2.1, locL_mono hB ks h.2.2.2.2⟩
theorem locL_mono {B B' : Finset ℕ} (hB : B ⊆ B') : ∀ ks : List CT, LocL B ks → LocL B' ks
  | [], _ => trivial
  | k :: ks, h => ⟨loc_mono hB k h.1, locL_mono hB ks h.2⟩
end

/-! ## splits -/

theorem splits_props {y d1 d2 : List ℕ} {s : ℕ} (hy : typical y = y) (hs : ∀ e ∈ y, s ≤ e)
    (h : (d1, d2) ∈ splits y) :
    typical d1 = d1 ∧ d1 ≠ [] ∧ (∀ e ∈ d1, s ≤ e) ∧ typical d2 = d2 ∧ d2 ≠ [] ∧ (∀ e ∈ d2, s ≤ e) := by
  have hnf : NF y := by rw [← hy]; exact nf_typical y
  have hsp := mem_splits.1 h
  obtain ⟨n1, n2⟩ := nf_of_split hnf hsp
  have hi := isSplit_of_mem_splits h
  refine ⟨typical_of_nf n1, IsSplit.ne_nil_left hi, ?_, typical_of_nf n2, IsSplit.ne_nil_right hi, ?_⟩
  · intro e he
    rcases hsp with ⟨f, -, -, rfl, rfl⟩ | ⟨f, -, -, rfl, rfl⟩ <;> exact hs e (List.mem_of_mem_take he)
  · intro e he
    rcases hsp with ⟨f, -, -, rfl, rfl⟩ | ⟨f, -, -, rfl, rfl⟩ <;> exact hs e (List.mem_of_mem_drop he)

theorem plus1_props {d : List ℕ} {s : ℕ} (h1 : typical d = d) (h2 : d ≠ []) (h3 : ∀ e ∈ d, s ≤ e) :
    typical (plus1 d) = plus1 d ∧ plus1 d ≠ [] ∧ (∀ e ∈ plus1 d, s + 1 ≤ e) := by
  refine ⟨?_, by simpa [plus1] using h2, ?_⟩
  · unfold plus1; rw [typical_map_add, h1]
  · intro e he
    unfold plus1 at he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    have := h3 x hx; omega

theorem vertsL_KR {v : ℕ} {ks kids : List CT} (h : List.Forall₂ (KR v) ks kids) :
    (∀ u, u ∈ vertsL kids → u = v ∨ u ∈ vertsL ks) ∧ (∀ u, u ∈ vertsL ks → u ∈ vertsL kids) := by
  induction h with
  | nil => simp [vertsL]
  | cons hr _ ih =>
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · rw [vertsL, Finset.mem_union] at hu ⊢
      rcases hu with hu | hu
      · rcases mem_verts_of_KR hr hu with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rcases ih.1 u hu with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    · rw [vertsL, Finset.mem_union] at hu ⊢
      rcases hu with hu | hu
      · exact Or.inl (verts_sub_of_KR hr hu)
      · exact Or.inr (ih.2 u hu)

/-! ## the region results -/

mutual
theorem winR_aux_rec (v : ℕ) (B : Finset ℕ) (hvB : v ∉ B) : ∀ (t r : CT) (c : Finset ℕ), WinR v t r c →
    Loc B t → Conn t → v ∉ verts t →
    Loc (insert v B) r ∧ Conn r ∧ (∀ u, u ∈ verts r ↔ u = v ∨ u ∈ verts t) ∧ r.S = insert v t.S
  | node S y ks, r, c, hw, hl, hc, hv => by
    obtain ⟨hlS, hty, hyne, hyge, hlks⟩ := hl
    have hvS : v ∉ S := fun h => hvB (hlS h)
    have hvks : v ∉ vertsL ks := fun h => hv (mem_verts.2 (Or.inr (mem_vertsL.1 h)))
    have hcard : (insert v S).card = S.card + 1 := Finset.card_insert_of_notMem hvS
    rw [WinR] at hw
    rcases hw with ⟨d1, d2, hsp, rfl, rfl⟩ | ⟨kids, cv, hk, rfl, rfl⟩
    · obtain ⟨t1, n1, e1, t2, n2, e2⟩ := splits_props hty hyge hsp
      obtain ⟨p1, p2, p3⟩ := plus1_props t1 n1 e1
      refine ⟨⟨Finset.insert_subset_insert v hlS, p1, p2, fun e he => by have := p3 e he; omega,
        ⟨hlS.trans (Finset.subset_insert _ _), t2, n2, e2, locL_mono (Finset.subset_insert _ _) ks hlks⟩, trivial⟩,
        ⟨⟨hc, trivial⟩, ?_, by simp⟩, ?_, rfl⟩
      · intro k hk u hu huk
        rw [List.mem_singleton] at hk; subst hk
        rw [Finset.mem_insert] at hu
        rcases hu with rfl | hu
        · exact absurd huk hv
        · exact hu
      · intro u
        simp only [verts, vertsL, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
        tauto
    · obtain ⟨hkl, hkc, hkR, hkv⟩ := kidR_aux_rec v B hvB ks kids cv hk hlks hc.1 hvks
      have hp1 := plus1_props hty hyne hyge
      refine ⟨⟨Finset.insert_subset_insert v hlS, hp1.1, hp1.2.1, fun e he => by have := hp1.2.2 e he; omega, hkl⟩,
        ⟨hkc, ?_, ?_⟩, ?_, rfl⟩
      · intro k' hk' u hu hu'
        obtain ⟨k, hk0, hr⟩ := forall₂_mem_right hkR k' hk'
        rw [Finset.mem_insert] at hu
        rcases mem_verts_of_KR hr hu' with rfl | hu2
        · exact hkv k' hk' hu'
        · rcases hu with rfl | hu
          · exact hkv k' hk' hu'
          · have hh := hc.2.1 k hk0 u hu hu2
            rcases hr with rfl | ⟨-, h1, -⟩
            · exact hh
            · exact h1 hh
      · refine forall₂_pairwise (P := fun a b => ∀ u, u ∈ verts a → u ∈ verts b → u ∈ S) ?_ hkR hc.2.2
        intro a b a' b' ha hb hab u h1 h2
        rcases mem_verts_of_KR ha h1 with rfl | h1
        · exact Finset.mem_insert_self _ _
        · rcases mem_verts_of_KR hb h2 with rfl | h2
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hab u h1 h2)
      · intro u
        rw [verts, verts, Finset.mem_union, Finset.mem_union, Finset.mem_insert]
        obtain ⟨h1, h2⟩ := vertsL_KR hkR
        have a1 := h1 u
        have a2 := h2 u
        tauto
theorem kidR_aux_rec (v : ℕ) (B : Finset ℕ) (hvB : v ∉ B) : ∀ (ks kids : List CT) (c : Finset ℕ), KidR v ks kids c →
    LocL B ks → ConnL ks → v ∉ vertsL ks →
    LocL (insert v B) kids ∧ ConnL kids ∧ List.Forall₂ (KR v) ks kids ∧ (∀ k' ∈ kids, v ∈ verts k' → v ∈ k'.S)
  | [], kids, c, hk, _, _, _ => by
    rw [KidR] at hk
    obtain ⟨rfl, -⟩ := hk
    exact ⟨trivial, trivial, List.Forall₂.nil, by simp⟩
  | k :: ks, kids, c, hk, hl, hc, hv => by
    rw [KidR] at hk
    obtain ⟨k', kids', c1, c2, rfl, -, hk1, hk2⟩ := hk
    have hvk : v ∉ verts k := fun h => hv (by rw [vertsL]; exact Finset.mem_union_left _ h)
    have hvks : v ∉ vertsL ks := fun h => hv (by rw [vertsL]; exact Finset.mem_union_right _ h)
    obtain ⟨l2, c2', r2, s2⟩ := kidR_aux_rec v B hvB ks kids' c2 hk2 hl.2 hc.2 hvks
    rcases hk1 with ⟨rfl, -⟩ | hw
    · refine ⟨⟨loc_mono (Finset.subset_insert _ _) _ hl.1, l2⟩, ⟨hc.1, c2'⟩, List.Forall₂.cons (Or.inl rfl) r2, ?_⟩
      intro q hq hvq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact absurd hvq hvk
      · exact s2 q hq hvq
    · obtain ⟨l1, c1', v1, s1⟩ := winR_aux_rec v B hvB k k' c1 hw hl.1 hc.1 hvk
      refine ⟨⟨l1, l2⟩, ⟨c1', c2'⟩, List.Forall₂.cons (Or.inr ⟨?_, ?_, ?_⟩) r2, ?_⟩
      · ext u; rw [Finset.mem_insert]; exact v1 u
      · rw [s1]; exact Finset.subset_insert _ _
      · rw [s1]
      · intro q hq hvq
        rcases List.mem_cons.1 hq with rfl | hq
        · rw [s1]; exact Finset.mem_insert_self _ _
        · exact s2 q hq hvq
end

theorem winR_aux_pair : (type_of% @winR_aux_rec) ∧ (type_of% @kidR_aux_rec) :=
  ⟨@winR_aux_rec, @kidR_aux_rec⟩

theorem winR_aux : type_of% @winR_aux_rec := winR_aux_pair.1

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.TablesIntroB` -/

section
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

end

/-! ### `Lax117284Proofs.Treewidth.Chars.Tables` -/

section
/-!
# `tables_wf` (work package C6a) and the unconditional table-size bounds

* `introC_wf` : introducing a new vertex `v ∉ B` keeps characteristics well-formed (`Wf B kmax → Wf (insert v B) kmax`),
  via the description `IR` of the results and `ir_aux` (`TablesIntroB`), then `good_norm`/`conn_norm`/`verts_norm`.
* `tables_wf`, `tablesWf : TablesWf` (the hypothesis of `CountTables`), and the unconditional
  `tables_length_le'`, `tables_length_le_of_width'`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem CT.introC_wf {B : Finset ℕ} {kmax v : ℕ} {N : Finset ℕ} {a c : CT} (hvB : v ∉ B) (ha : Wf B kmax a)
    (hc : c ∈ introC kmax v N a) : Wf (insert v B) kmax c := by
  obtain ⟨r, hr, rfl, hk⟩ := mem_introC.1 hc
  have hv : v ∉ verts a := by rw [ha.verts_eq]; exact hvB
  obtain ⟨lr, cr, vr, -, -⟩ := ir_aux v B hvB N hr (loc_of_good a ha.good) ha.conn hv
  refine ⟨?_, good_norm r lr cr, conn_norm r cr, hk⟩
  rw [verts_norm]
  ext u
  rw [Finset.mem_insert, vr, ha.verts_eq]

theorem wf_start (kmax : ℕ) : Wf ∅ kmax CT.start := by
  refine ⟨by simp [CT.start, verts, vertsL], ?_, ?_, by simp [CT.start, maxEntry, maxEntryL]⟩
  · refine ⟨Finset.Subset.refl _, typical_singleton 0, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [CT.start, GoodL]
  · simp [CT.start, Conn, ConnL]

/-- **The table entries are well-formed characteristics of the bag.** -/
theorem tables_wf {adj : Adj} {k : ℕ} : ∀ {nt : NT}, nt.Good adj → ∀ c ∈ tables adj k nt,
    CT.Wf nt.bag (k + 1) c
  | .leaf, _, c, hc => by
    simp only [tables, List.mem_singleton] at hc
    subst hc
    exact wf_start _
  | .forget x c, hg, q, hq => by
    simp only [tables, forgetTable, List.mem_dedup, List.mem_map] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    exact CT.forgetC_wf (tables_wf hg.2 q0 hq0)
  | .join a b, hg, q, hq => by
    have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
    obtain ⟨hab, -, hga, hgb, -⟩ := hg'
    simp only [tables, joinTable, List.mem_dedup, List.mem_flatMap] at hq
    obtain ⟨ca, hca, cb, hcb, hq⟩ := hq
    have h1 := tables_wf hga ca hca
    have h2 := tables_wf hgb cb hcb
    rw [← hab] at h2
    exact CT.joinC_wf h1 h2 hq
  | .intro v c, hg, q, hq => by
    obtain ⟨hvB, -, -, hgc⟩ := hg
    simp only [tables, introTable, List.mem_dedup, List.mem_flatMap] at hq
    obtain ⟨q0, hq0, hq⟩ := hq
    exact CT.introC_wf hvB (tables_wf hgc q0 hq0) hq

/-- The hypothesis of the counting results holds. -/
theorem tablesWf : TablesWf := fun hg c hc => tables_wf hg c hc

/-- If a nice tree has width `≤ l`, every table of it is small (unconditional). -/
theorem tables_length_le_of_width' {adj : Adj} {k l : ℕ} {nt : NT} (hg : nt.Good adj) (hw : nt.toRT.Width l) :
    (tables adj k nt).length ≤ charBound (l + 1) (k + 1) :=
  tables_length_le_of_width tablesWf hg hw

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Size.Tables` -/

section
/-!
# Size bounds (WP P1), part 4: table sizes, with the intermediate (pre-`dedup`) lists

`x := k + 2`.  For a good nice tree `nt` all of whose bags have at most `k + 2` vertices:

* `tables_length_le_pow`  : `|tables adj k nt| ≤ 2^(96 x^3)` (`tables` is duplicate-free, so this is the counting bound);
* `introC_length_le`     : `|introC (k+1) v N t| ≤ 2^(64 (b + k + 3)^3)` for `t ∈ tables adj k c`, `b = |c.bag|`;
* `forgetTable_pre_le`, `introTable_pre_le`, `joinTable_pre_le` : the lists *before* `dedup` are at most `2^(2000 x^3)`
  (the quadratic `dedup` then costs at most `2^(4000 x^3)` comparisons).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem pow_mul_pow_le' {a b d : ℕ} (h : a + b ≤ d) : 2 ^ a * 2 ^ b ≤ 2 ^ d := by
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) h

/-- Width hereditary along the children. -/
theorem NT.width_intro {v : ℕ} {c : NT} {w : ℕ} (h : (NT.intro v c).toRT.Width w) : c.toRT.Width w := by
  intro X hX
  exact h X (by simp [NT.toRT, RT.bags, RT.bagsL, hX])

theorem NT.width_forget {v : ℕ} {c : NT} {w : ℕ} (h : (NT.forget v c).toRT.Width w) : c.toRT.Width w := by
  intro X hX
  exact h X (by simp [NT.toRT, RT.bags, RT.bagsL, hX])

theorem NT.width_join_left {a b : NT} {w : ℕ} (h : (NT.join a b).toRT.Width w) : a.toRT.Width w := by
  intro X hX
  exact h X (by simp [NT.toRT, RT.bags, RT.bagsL, hX])

theorem NT.width_join_right {a b : NT} {w : ℕ} (h : (NT.join a b).toRT.Width w) : b.toRT.Width w := by
  intro X hX
  exact h X (by simp [NT.toRT, RT.bags, RT.bagsL, hX])

theorem introC_length_le_plans (kmax v : ℕ) (N : Finset ℕ) (t : CT) :
    (introC kmax v N t).length ≤ (introPlans v N t).length := by
  unfold introC
  exact le_trans (List.length_filter_le _ _) (by simp)

theorem exp_le_96 (k : ℕ) : 16 * (k + 2 + 1) ^ 2 * (k + 2 + (k + 1) + 2) ≤ 96 * (k + 2) ^ 3 := by
  nlinarith [sq_nonneg k, Nat.zero_le k]

theorem charBound_tables_le (k : ℕ) : charBound (k + 2) (k + 1) ≤ 2 ^ (96 * (k + 2) ^ 3) := by
  unfold charBound
  exact Nat.pow_le_pow_right (by norm_num) (exp_le_96 k)

theorem tables_length_le_pow {adj : Adj} {k : ℕ} {nt : NT} (hg : nt.Good adj) (hw : nt.toRT.Width (k + 1)) :
    (tables adj k nt).length ≤ 2 ^ (96 * (k + 2) ^ 3) := by
  have := tables_length_le_of_width' (k := k) hg hw
  exact le_trans this (charBound_tables_le k)

theorem introC_length_le {k v : ℕ} {N B : Finset ℕ} {t : CT} (hB : B.card ≤ k + 2) (hw : t.Wf B (k + 1)) :
    (introC (k + 1) v N t).length ≤ 2 ^ (1728 * (k + 2) ^ 3) := by
  refine le_trans (introC_length_le_plans _ _ _ _) (le_trans (introPlans_length_le hw) ?_)
  apply Nat.pow_le_pow_right (by norm_num)
  have h1 : B.card + (k + 1) + 2 ≤ 3 * (k + 2) := by omega
  have h2 : (B.card + (k + 1) + 2) ^ 3 ≤ (3 * (k + 2)) ^ 3 := Nat.pow_le_pow_left h1 3
  calc 64 * (B.card + (k + 1) + 2) ^ 3 ≤ 64 * (3 * (k + 2)) ^ 3 := Nat.mul_le_mul_left _ h2
    _ = 1728 * (k + 2) ^ 3 := by ring

theorem joinC_length_le_k {k : ℕ} {B : Finset ℕ} {a b : CT} (hB : B.card ≤ k + 2) (ha : a.Wf B (k + 1))
    (hb : b.Wf B (k + 1)) : (joinC (k + 1) a b).length ≤ 2 ^ (432 * (k + 2) ^ 3) := by
  refine le_trans (joinC_length_le ha hb) (Nat.pow_le_pow_right (by norm_num) ?_)
  have h1 : B.card + (k + 1) + 2 ≤ 3 * (k + 2) := by omega
  have h2 : (B.card + (k + 1) + 2) ^ 3 ≤ (3 * (k + 2)) ^ 3 := Nat.pow_le_pow_left h1 3
  calc 16 * (B.card + (k + 1) + 2) ^ 3 ≤ 16 * (3 * (k + 2)) ^ 3 := Nat.mul_le_mul_left _ h2
    _ = 432 * (k + 2) ^ 3 := by ring

/-- The introduce step before `dedup`. -/
theorem introTable_pre_le {adj : Adj} {k v : ℕ} {c : NT} (hg : c.Good adj) (hw : c.toRT.Width (k + 1))
    (N : Finset ℕ) :
    ((tables adj k c).flatMap (CT.introC (k + 1) v N)).length ≤ 2 ^ (1824 * (k + 2) ^ 3) := by
  have hB : c.bag.card ≤ k + 2 := bag_card_le_of_width hw
  have h1 := tables_length_le_pow hg hw
  refine le_trans (length_flatMap_le (n := 2 ^ (1728 * (k + 2) ^ 3)) ?_) ?_
  · intro t ht
    exact introC_length_le hB (tables_wf hg t ht)
  · refine le_trans (Nat.mul_le_mul_right _ h1) ?_
    exact pow_mul_pow_le' (by omega)

end Lax117284Proofs.Treewidth.Chars

end
