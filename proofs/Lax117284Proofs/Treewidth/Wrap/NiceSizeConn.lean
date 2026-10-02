import Lax117284Proofs.Treewidth.Wrap.NiceSize

/-!
# `niceOf_size_le` under connectedness (C8a)

`(niceOf t).size ≤ (|V| + 2) * (size t + 1)` for a connected `t` (the bound of `proofs-todo/Statements.lean`).
The proof charges each parent-child edge `|b \ X| + |X \ b|`, where the forgotten vertices `b \ X` are counted once
overall thanks to connectedness (`Σ_k |V_k \ X| ≤ |V \ X|` by the pairwise clause).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Trees Lax117284Proofs.Treewidth.Trees.NT

theorem sum_card_le {X V : Finset ℕ} : ∀ ks : List RT,
    ks.Pairwise (fun a b => ∀ v, v ∈ a.verts → v ∈ b.verts → v ∈ X) →
    (∀ k ∈ ks, k.verts \ X ⊆ V) → (ks.map (fun k => (k.verts \ X).card)).sum ≤ V.card := by
  intro ks
  induction ks generalizing V with
  | nil => intros; simp
  | cons a ks ih =>
    intro hp hV
    rw [List.pairwise_cons] at hp
    simp only [List.map_cons, List.sum_cons]
    have h1 : (ks.map (fun k => (k.verts \ X).card)).sum ≤ (V \ (a.verts \ X)).card := by
      apply ih hp.2
      intro k hk v hv
      have hvk := Finset.mem_sdiff.1 hv
      refine Finset.mem_sdiff.2 ⟨hV k (List.mem_cons_of_mem _ hk) hv, fun hva => ?_⟩
      have hva' := Finset.mem_sdiff.1 hva
      exact hvk.2 (hp.1 k hk v hva'.1 hvk.1)
    have h2 : (a.verts \ X).card + (V \ (a.verts \ X)).card = V.card :=
      by have := Finset.card_sdiff_add_card_eq_card (hV a (by simp)); omega
    omega

theorem conn_kid_card {b Vk X : Finset ℕ} (hb : b ⊆ Vk) (hX : ∀ v ∈ X, v ∈ Vk → v ∈ b) :
    (b \ X).card + (Vk \ b).card ≤ (Vk \ X).card := by
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro u hu
    simp only [Finset.mem_union, Finset.mem_sdiff] at hu ⊢
    rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hb h1, h2⟩
    · exact ⟨h1, fun hx => h2 (hX u hx h1)⟩
  · rw [Finset.disjoint_left]
    intro u hu hu'
    exact (Finset.mem_sdiff.1 hu').2 (Finset.mem_sdiff.1 hu).1

theorem list_sum_add_const {α : Type} (l : List α) (f : α → ℕ) (c : ℕ) :
    (l.map (fun a => f a + c)).sum = (l.map f).sum + l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

theorem niceOf_size_conn_key : ∀ (c : ℕ) (t : RT), t.Conn → t.verts.card ≤ c →
    (niceOf t).size + c + 1 ≤ c * t.size + t.rootBag.card + 2 * t.nleaves + 2 * (t.verts \ t.rootBag).card := by
  intro c t
  induction t using RT.ind with
  | _ X ks ih =>
    intro hconn hc
    have hXc : X.card ≤ c := (Finset.card_le_card (by
      intro u hu; rw [RT.verts_node]; exact Or.inl hu)).trans hc
    rcases ks with _ | ⟨k, ks'⟩
    · rw [niceOf_size_nil]
      simp [RT.size_node, RT.nleaves_node_nil, RT.rootBag, RT.verts, RT.vertsL]
      omega
    · obtain ⟨hc1, hc2, hc3⟩ := (RT.conn_node_iff X _).1 hconn
      rw [RT.size_node, RT.nleaves_node_cons]
      set l := k :: ks' with hl
      -- per kid
      have hk : ∀ k' ∈ l, (conv X (niceOf k')).size + 1 + c ≤
          c * k'.size + X.card + 2 * (k'.verts \ X).card + 2 * k'.nleaves := by
        intro k' hk'
        have hv : k'.verts.card ≤ c := (Finset.card_le_card (RT.sub_verts hk')).trans hc
        have := ih k' hk' (hc1 k' hk') hv
        rw [conv_size_kid]
        have hcn := conn_kid_card (RT.rootBag_sub_verts k') (hc2 k' hk')
        have h1 := Finset.card_sdiff_add_card_inter k'.rootBag X
        have h2 := Finset.card_sdiff_add_card_inter X k'.rootBag
        rw [Finset.inter_comm X k'.rootBag] at h2
        omega
      have hsum := niceOf_size_cons X k ks'
      have hle := List.sum_le_sum hk
      rw [list_sum_add_const] at hle
      have hdis := sum_card_le (X := X) (V := (RT.node X l).verts \ X) l hc3 (by
        intro k' hk' u hu
        have := Finset.mem_sdiff.1 hu
        exact Finset.mem_sdiff.2 ⟨RT.sub_verts hk' this.1, this.2⟩)
      have hrhs : (l.map (fun k' => c * k'.size + X.card + 2 * (k'.verts \ X).card + 2 * k'.nleaves)).sum =
          c * (l.map RT.size).sum + l.length * X.card + 2 * (l.map (fun k' => (k'.verts \ X).card)).sum +
            2 * (l.map RT.nleaves).sum := by
        induction l with
        | nil => simp
        | cons a l ih2 => simp [ih2]; ring
      rw [hrhs] at hle
      have hn : l.length * X.card ≤ l.length * c := Nat.mul_le_mul_left _ hXc
      have hrb : (RT.node X l).rootBag = X := rfl
      rw [hrb]
      have hsm : ((l.map (fun k' => (conv X (niceOf k')).size + 1)).sum) = (niceOf (.node X l)).size + 1 := hsum.symm
      have : (l.map (fun k' => (conv X (niceOf k')).size + 1)).sum ≤ (l.map (fun k' => (conv X (niceOf k')).size + 1)).sum := le_rfl
      nlinarith

/-- **`niceOf_size_le`** for a connected tree: the bound of `proofs-todo/Statements.lean`. -/
theorem niceOf_size_le {t : RT} (hc : t.Conn) : (niceOf t).size ≤ (t.verts.card + 2) * (t.size + 1) := by
  have := niceOf_size_conn_key t.verts.card t hc le_rfl
  have h1 : t.rootBag.card + 2 * (t.verts \ t.rootBag).card ≤ 2 * t.verts.card := by
    have := Finset.card_sdiff_add_card_inter t.verts t.rootBag
    have := Finset.card_le_card (RT.rootBag_sub_verts t)
    have h3 : (t.verts ∩ t.rootBag).card = t.rootBag.card := by
      rw [Finset.inter_eq_right.2 (RT.rootBag_sub_verts t)]
    omega
  have h2 := RT.nleaves_le_size t
  nlinarith

end Lax117284Proofs.Treewidth.Chars
