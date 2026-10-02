import Lax117284Proofs.Treewidth.Chars.Norm
import Lax117284Proofs.Treewidth.Chars.Dom
import Lax117284Proofs.Treewidth.Seq.Concat

/-!
# `norm` and `relabel` are monotone for `DomC` (work package C1)

`norm_mono : DomC a b → DomC (norm a) (norm b)` — the pruning and the sorting depend on the labels (shared by
`DomC`-related trees), and the sequences are only concatenated, cut to their first entry and made typical
(Lemmas 3.19 and 3.11).
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

/-! ## sequence facts -/

theorem dom_take_one {a b : List ℕ} (h : Dom a b) : Dom (a.take 1) (b.take 1) := by
  obtain ⟨a', b', ha, hb, hle⟩ := h
  cases a with
  | nil =>
    rw [ext_nil_iff] at ha; subst ha
    have : b' = [] := by simpa using hle
    subst this
    rw [ext_nil_right] at hb; subst hb
    exact Dom.refl _
  | cons x a0 =>
    cases b with
    | nil =>
      rw [ext_nil_iff] at hb; subst hb
      have : a' = [] := by simpa using hle
      subst this; exact absurd ha (by simp)
    | cons z b0 =>
      obtain ⟨p, u, rfl, -⟩ := ext_cons_iff.1 ha
      obtain ⟨q, v, rfl, -⟩ := ext_cons_iff.1 hb
      simp only [List.replicate_succ, List.cons_append] at hle
      cases hle with
      | cons hxz _ =>
        exact ⟨[x], [z], by simpa using Ext.refl [x], by simpa using Ext.refl [z],
          List.Forall₂.cons hxz List.Forall₂.nil⟩

namespace CT

/-! ## `DomCL` as `Forall₂` -/

theorem domCL_iff {a b : List CT} : DomCL a b ↔ List.Forall₂ DomC a b := by
  induction a generalizing b with
  | nil => cases b <;> simp [DomCL]
  | cons k ks ih =>
    cases b with
    | nil => simp [DomCL]
    | cons k' ks' => simp [DomCL, ih]

mutual
theorem domC_verts : ∀ {a b : CT}, DomC a b → verts a = verts b
  | node S y ks, node S' y' ks', h => by
    obtain ⟨rfl, -, hk⟩ := h
    simp only [verts_node]; rw [domCL_vertsL hk]
theorem domCL_vertsL : ∀ {a b : List CT}, DomCL a b → vertsL a = vertsL b
  | [], [], _ => rfl
  | k :: ks, k' :: ks', h => by
    simp only [vertsL]; rw [domC_verts h.1, domCL_vertsL h.2]
end

theorem domC_S {a b : CT} (h : DomC a b) : a.S = b.S := by
  cases a; cases b; exact h.1

theorem domC_kids_nil {a b : CT} (h : DomC a b) : a.kids = [] ↔ b.kids = [] := by
  cases a with
  | node S y ks =>
    cases b with
    | node S' y' ks' =>
      have hk := domCL_iff.1 h.2.2
      simp only [CT.kids]
      exact ⟨fun e => by subst e; simpa using hk, fun e => by subst e; simpa using hk.length_eq⟩

theorem domC_keep (S : Finset ℕ) {a b : CT} (h : DomC a b) : keep S a = keep S b := by
  have h1 := domC_S h
  have h2 := domC_kids_nil h
  unfold keep isLeaf
  have : (a.kids.isEmpty) = (b.kids.isEmpty) := by
    rw [Bool.eq_iff_iff]; simp [h2]
  rw [this, h1]

theorem domC_key (S : Finset ℕ) {a b : CT} (h : DomC a b) : key S a = key S b := by
  unfold key; rw [domC_verts h]

theorem domCL_filter (S : Finset ℕ) {K K' : List CT} (h : DomCL K K') :
    DomCL (K.filter (keep S)) (K'.filter (keep S)) := by
  rw [domCL_iff] at h ⊢
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b l l' hab _ ih =>
    rw [List.filter_cons, List.filter_cons, domC_keep S hab]
    split_ifs
    · exact List.Forall₂.cons hab ih
    · exact ih

theorem domCL_sortKids (S : Finset ℕ) {F F' : List CT} (h : DomCL F F') :
    DomCL (sortKids S F) (sortKids S F') := by
  rw [domCL_iff] at h ⊢
  set l := F.zip F' with hl
  have hF : F = l.map Prod.fst := by
    rw [hl, List.map_fst_zip h.length_eq.le]
  have hF' : F' = l.map Prod.snd := by
    rw [hl, List.map_snd_zip h.length_eq.ge]
  have hmem : ∀ p ∈ l, DomC p.1 p.2 := by
    intro ⟨a, b⟩ hp
    rw [hl] at hp
    exact (List.forall₂_iff_zip.1 h).2 hp
  set r : CT × CT → CT × CT → Bool := fun p q => decide (key S p.1 ≤ key S q.1) with hr
  have h1 : (l.mergeSort r).map Prod.fst = sortKids S F := by
    rw [hF]; unfold sortKids
    exact List.map_mergeSort (fun a _ b _ => rfl)
  have h2 : (l.mergeSort r).map Prod.snd = sortKids S F' := by
    rw [hF']; unfold sortKids
    apply List.map_mergeSort
    intro a ha b hb
    simp only [hr]
    rw [domC_key S (hmem a ha), domC_key S (hmem b hb)]
  rw [← h1, ← h2, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  apply List.forall₂_same.2
  intro p hp
  exact hmem p ((List.mem_mergeSort).1 hp)

theorem normF_mono {S : Finset ℕ} {y y' : List ℕ} (hy : Dom y y') :
    ∀ {F F' : List CT}, DomCL F F' → DomC (normF S y F) (normF S y' F')
  | [], [], _ => ⟨rfl, dom_take_one hy, trivial⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | [k], [k'], h => by
    rw [normF_single, normF_single]
    have hS := domC_S h.1
    by_cases hk : k.S = S
    · rw [if_pos hk, if_pos (hS ▸ hk)]
      cases k; cases k'
      obtain ⟨-, hyk, hkids⟩ := h.1
      exact ⟨rfl, dom_typical_iff.1 (Dom.append hy hyk), hkids⟩
    · rw [if_neg hk, if_neg (hS ▸ hk)]
      exact ⟨rfl, hy, h.1, trivial⟩
  | [k], _ :: _ :: _, h => h.2.elim
  | _ :: _ :: _, [k'], h => h.2.elim
  | a :: b :: t, a' :: b' :: t', h => by
    rw [normF_ge2, normF_ge2]
    exact ⟨rfl, hy, domCL_sortKids S h⟩

mutual
theorem norm_mono : ∀ {a b : CT}, DomC a b → DomC (norm a) (norm b)
  | node S y ks, node S' y' ks', h => by
    obtain ⟨rfl, hy, hk⟩ := h
    rw [norm_node', norm_node']
    apply normF_mono hy
    apply domCL_filter
    have := normL_mono hk
    rwa [normL_eq_map, normL_eq_map] at this
theorem normL_mono : ∀ {a b : List CT}, DomCL a b → DomCL (normL a) (normL b)
  | [], [], _ => trivial
  | k :: ks, k' :: ks', h => ⟨norm_mono h.1, normL_mono h.2⟩
end

mutual
theorem relabel_mono (f : Finset ℕ → Finset ℕ) : ∀ {a b : CT}, DomC a b → DomC (relabel f a) (relabel f b)
  | node S y ks, node S' y' ks', h => by
    obtain ⟨rfl, hy, hk⟩ := h
    exact ⟨rfl, hy, relabelL_mono f hk⟩
theorem relabelL_mono (f : Finset ℕ → Finset ℕ) : ∀ {a b : List CT}, DomCL a b → DomCL (relabelL f a) (relabelL f b)
  | [], [], _ => trivial
  | k :: ks, k' :: ks', h => ⟨relabel_mono f h.1, relabelL_mono f h.2⟩
end

/-- **`forgetC` is monotone** for `DomC`. -/
theorem forgetC_mono (x : ℕ) {a b : CT} (h : DomC a b) : DomC (forgetC x a) (forgetC x b) :=
  norm_mono (relabel_mono _ h)

end CT

end Lax117284Proofs.Treewidth.Chars
