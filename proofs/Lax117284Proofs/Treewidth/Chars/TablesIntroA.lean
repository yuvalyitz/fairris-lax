import Lax117284Proofs.Treewidth.Chars.IntroMono
import Lax117284Proofs.Treewidth.Chars.IntroChains
import Lax117284Proofs.Treewidth.Chars.NormGood
import Lax117284Proofs.Treewidth.Chars.NormConn
import Lax117284Proofs.Treewidth.Chars.TablesJoin
import Lax117284Proofs.Treewidth.Chars.CountRuns

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
