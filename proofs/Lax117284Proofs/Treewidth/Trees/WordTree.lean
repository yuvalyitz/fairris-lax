import Lax117284Proofs.Treewidth.Trees.WordDesc

/-!
# The nice tree read off a word (T2)

For a word `D` with `Lay n D`, `ofWord D i` is a well-formed nice tree whose root bag is `bagAt i`, whose nodes
correspond to `desc D i`, and whose `RT.Conn` is the conjunction of the local conditions `Loc` on those nodes.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace Word

open Lax117284.GraphWords

variable {n : ℕ} {D : List ℕ}

lemma Lay.bag_ofWord (L : Lay n D) : ∀ i, i < nodeCount D → (ofWord D i).bag = bagN n D i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    cases i with
    | zero => simp [ofWord_zero, bagN_zero]
    | succ i =>
      have ih' := ih i (by omega) (by omega)
      rcases L.node hi with ⟨h1, h2, h3⟩ | ⟨hkd, hv, -⟩ | ⟨hkd, hv, -⟩ | ⟨hkd, ho, -⟩
      · rw [ofWord_leaf h1 h2 h3, bagN_succ_leaf h1 h2 h3]; rfl
      · rw [ofWord_intro hkd, bagN_succ_intro hkd hv, NT.bag_intro, ih']
      · rw [ofWord_forget hkd, bagN_succ_forget hkd hv, NT.bag_forget, ih']
      · rw [ofWord_join hkd ho, bagN_succ_join hkd, NT.bag_join, ih']

lemma Lay.wf_ofWord (L : Lay n D) : ∀ i, i < nodeCount D → (ofWord D i).Wf := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    cases i with
    | zero => simp [ofWord_zero, NT.Wf]
    | succ i =>
      have ih' := ih i (by omega) (by omega)
      have hb := L.bag_ofWord i (by omega)
      rcases L.node hi with ⟨h1, h2, h3⟩ | ⟨hkd, hv, hn⟩ | ⟨hkd, hv, hn⟩ | ⟨hkd, ho, hbe⟩
      · rw [ofWord_leaf h1 h2 h3]; trivial
      · rw [ofWord_intro hkd]; exact ⟨by rw [hb]; exact hn, ih'⟩
      · rw [ofWord_forget hkd]; exact ⟨by rw [hb]; exact hn, ih'⟩
      · rw [ofWord_join hkd ho]
        refine ⟨?_, ih', ih _ (by omega) (by omega)⟩
        rw [hb, L.bag_ofWord _ (by omega), hbe]

lemma Lay.mem_vs_ofWord (L : Lay n D) : ∀ i, i < nodeCount D → ∀ u,
    u ∈ (ofWord D i).vs ↔ ∃ j ∈ desc D i, u ∈ bagN n D j := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi u
    cases i with
    | zero => simp [ofWord_zero, desc_zero, bagN_zero]
    | succ i =>
      have ih' := ih i (by omega) (by omega) u
      have hb := L.bag_ofWord (i + 1) hi
      rcases L.node hi with ⟨h1, h2, h3⟩ | ⟨hkd, hv, hn⟩ | ⟨hkd, hv, hn⟩ | ⟨hkd, ho, hbe⟩
      · rw [ofWord_leaf h1 h2 h3] at hb ⊢
        rw [desc_leaf h1 h2 h3]
        simp only [NT.vs_leaf, Finset.notMem_empty, Finset.mem_singleton, exists_eq_left, false_iff]
        rw [← hb]; simp
      · rw [ofWord_intro hkd] at hb ⊢
        rw [desc_intro hkd]
        simp only [NT.vs_intro, Finset.mem_union, ih', hb, Finset.mem_insert, exists_eq_or_imp]
      · rw [ofWord_forget hkd] at hb ⊢
        rw [desc_forget hkd]
        simp only [NT.vs_forget, Finset.mem_union, ih', hb, Finset.mem_insert, exists_eq_or_imp]
      · rw [ofWord_join hkd ho]
        rw [desc_join hkd ho]
        have ih'' := ih (other D (i + 1)) (by omega) (by omega) u
        have hbi := L.bag_ofWord i (by omega)
        simp only [NT.vs_join, Finset.mem_union, ih', ih'', Finset.mem_insert,
          or_and_right, exists_or, exists_eq_left, hbi, ← bagN_succ_join hkd]

lemma Lay.mem_bs_ofWord (L : Lay n D) : ∀ i, i < nodeCount D → ∀ X,
    X ∈ (ofWord D i).bs ↔ ∃ j ∈ desc D i, X = bagN n D j := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi X
    cases i with
    | zero => simp [ofWord_zero, desc_zero, bagN_zero]
    | succ i =>
      have ih' := ih i (by omega) (by omega) X
      have hb := L.bag_ofWord (i + 1) hi
      rcases L.node hi with ⟨h1, h2, h3⟩ | ⟨hkd, hv, hn⟩ | ⟨hkd, hv, hn⟩ | ⟨hkd, ho, hbe⟩
      · rw [ofWord_leaf h1 h2 h3] at hb ⊢
        rw [desc_leaf h1 h2 h3]
        simp only [NT.bs_leaf, List.mem_singleton, Finset.mem_singleton, exists_eq_left]
        rw [← hb]; rfl
      · rw [ofWord_intro hkd] at hb ⊢
        rw [desc_intro hkd]
        simp only [NT.bs_intro, List.mem_cons, ih', hb, Finset.mem_insert, exists_eq_or_imp]
      · rw [ofWord_forget hkd] at hb ⊢
        rw [desc_forget hkd]
        simp only [NT.bs_forget, List.mem_cons, ih', hb, Finset.mem_insert, exists_eq_or_imp]
      · rw [ofWord_join hkd ho]
        rw [desc_join hkd ho]
        have ih'' := ih (other D (i + 1)) (by omega) (by omega) X
        have hbi := L.bag_ofWord i (by omega)
        simp only [NT.bs_join, List.mem_cons, List.mem_append, ih', ih'', Finset.mem_insert,
          Finset.mem_union, or_and_right, exists_or, exists_eq_left, hbi, ← bagN_succ_join hkd]

lemma Lay.size_ofWord (L : Lay n D) : ∀ i, i < nodeCount D → (ofWord D i).size = (desc D i).card := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    cases i with
    | zero => simp [ofWord_zero, desc_zero, NT.size]
    | succ i =>
      have ih' := ih i (by omega) (by omega)
      rcases L.node hi with ⟨h1, h2, h3⟩ | ⟨hkd, hv, hn⟩ | ⟨hkd, hv, hn⟩ | ⟨hkd, ho, hbe⟩
      · rw [ofWord_leaf h1 h2 h3, desc_leaf h1 h2 h3]; simp [NT.size]
      · rw [ofWord_intro hkd, desc_intro hkd, Finset.card_insert_of_notMem, NT.size, ih']
        intro h; have := desc_le D i _ h; omega
      · rw [ofWord_forget hkd, desc_forget hkd, Finset.card_insert_of_notMem, NT.size, ih']
        intro h; have := desc_le D i _ h; omega
      · have hnot : i + 1 ∉ desc D i ∪ desc D (other D (i + 1)) := by
          intro h
          rcases Finset.mem_union.1 h with h | h
          · have := desc_le D i _ h; omega
          · have := desc_le D _ _ h; omega
        rw [ofWord_join hkd ho, desc_join hkd ho, Finset.card_insert_of_notMem hnot, NT.size, ih',
          ih (other D (i + 1)) (by omega) (by omega),
          Finset.card_union_of_disjoint (L.desc_disjoint hi hkd ho)]

/-- The local connectedness conditions at node `j`. -/
def Loc (n : ℕ) (D : List ℕ) (j : ℕ) : Prop :=
  (kind D j = 1 → ∀ x ∈ desc D (j - 1), vertex D j ∉ bagN n D x) ∧
  (kind D j = 3 → ∀ x ∈ desc D (j - 1), ∀ y ∈ desc D (other D j), ∀ u,
    u ∈ bagN n D x → u ∈ bagN n D y → u ∈ bagN n D j)

lemma Lay.nconn_ofWord (L : Lay n D) : ∀ i, i < nodeCount D →
    (NT.NConn (ofWord D i) ↔ ∀ j ∈ desc D i, Loc n D j) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    cases i with
    | zero =>
      have : Loc n D 0 := by simp [Loc, kind_zero L]
      simp [ofWord_zero, NT.NConn, desc_zero, this]
    | succ i =>
      have ih' := ih i (by omega) (by omega)
      have hv := L.mem_vs_ofWord i (by omega)
      rcases L.node hi with ⟨h1, h2, h3⟩ | ⟨hkd, hv', hn⟩ | ⟨hkd, hv', hn⟩ | ⟨hkd, ho, hbe⟩
      · rw [ofWord_leaf h1 h2 h3, desc_leaf h1 h2 h3]
        simp [NT.NConn, Loc, h1, h3]
      · have hl : Loc n D (i + 1) ↔ ∀ y ∈ desc D i, vertex D (i + 1) ∉ bagN n D y := by
          simp [Loc, hkd]
        rw [ofWord_intro hkd, desc_intro hkd, NT.NConn, Finset.forall_mem_insert, ih', hl, hv]
        simp only [not_exists, not_and]
      · have hl : Loc n D (i + 1) := by simp [Loc, hkd]
        rw [ofWord_forget hkd, desc_forget hkd, NT.NConn, Finset.forall_mem_insert, ih']
        simp [hl]
      · have ih'' := ih (other D (i + 1)) (by omega) (by omega)
        have hv2 := L.mem_vs_ofWord (other D (i + 1)) (by omega)
        have hbi := L.bag_ofWord i (by omega)
        have hl : Loc n D (i + 1) ↔ ∀ x ∈ desc D i, ∀ y ∈ desc D (other D (i + 1)), ∀ u,
            u ∈ bagN n D x → u ∈ bagN n D y → u ∈ bagN n D i := by
          simp [Loc, hkd, bagN_succ_join hkd]
        rw [ofWord_join hkd ho, desc_join hkd ho, NT.NConn, Finset.forall_mem_insert, ih', ih'', hl]
        rw [hbi]
        have hA : (∀ u, u ∈ (ofWord D i).vs → u ∈ (ofWord D (other D (i + 1))).vs → u ∈ bagN n D i) ↔
            (∀ x ∈ desc D i, ∀ y ∈ desc D (other D (i + 1)), ∀ u,
              u ∈ bagN n D x → u ∈ bagN n D y → u ∈ bagN n D i) := by
          constructor
          · intro h x hx y hy u hux huy
            exact h u ((hv u).2 ⟨x, hx, hux⟩) ((hv2 u).2 ⟨y, hy, huy⟩)
          · intro h u hu1 hu2
            obtain ⟨x, hx, hux⟩ := (hv u).1 hu1
            obtain ⟨y, hy, huy⟩ := (hv2 u).1 hu2
            exact h x hx y hy u hux huy
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨hA.1 h1, fun x hx => (Finset.mem_union.1 hx).elim (h2 x) (h3 x)⟩
        · rintro ⟨h1, h2⟩
          exact ⟨hA.2 h1, fun x hx => h2 x (Finset.mem_union_left _ hx),
            fun x hx => h2 x (Finset.mem_union_right _ hx)⟩

end Word

end Lax117284Proofs.Treewidth.Trees
