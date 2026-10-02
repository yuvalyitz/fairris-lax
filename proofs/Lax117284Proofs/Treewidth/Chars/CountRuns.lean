import Lax117284Proofs.Treewidth.Chars.Defs
import Lax117284Proofs.Treewidth.Chars.Norm

/-!
# Counting characteristics (1): a well-formed characteristic has at most `(2b+2)²` runs

`CT.Wf.count_le : t.count ≤ runBound B.card` (`PLAN.md §d`).  The proof is by a potential argument on the run tree:

* `leaves t` is the number of leaf runs.  A non-root leaf run owns a vertex (`Good`: its label is not inside its
  parent's), the kids of a run own disjoint sets of vertices (`Conn`): `leaves t ≤ |verts t \ t.S|` for a
  non-leaf run `t` (`leaves_le_of_kids_ne_nil`);
* `φ t = |verts t| + |verts t \ t.S|` never increases when going to a kid, and **strictly decreases** when
  going to the only kid of a run (`Good`: its label differs; a vertex leaves, or a vertex enters), because
  `v ∈ S`, `v ∈ verts k` ⇒ `v ∈ k.S` (`Conn`);
* by induction, `count t + (p + 1) ≤ 2 · leaves t · (p + 1)` for all `p ≥ φ t` (`count_add_le`), i.e.
  `count t ≤ (2 L − 1)(φ + 1)`; with `L ≤ b`, `φ ≤ 2b` this is `count ≤ 2b (2b + 1) ≤ (2b + 2)²`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

namespace CT

/-! ## an induction principle and the list views -/

/-- Structural induction over the nested inductive `CT`. -/
theorem ind {P : CT → Prop} (h : ∀ S y ks, (∀ k ∈ ks, P k) → P (.node S y ks)) (t : CT) : P t := by
  refine CT.rec (motive_1 := P) (motive_2 := fun ks => ∀ k ∈ ks, P k) ?_ ?_ ?_ t
  · intro S y ks ih
    exact h S y ks ih
  · intro k hk
    simp at hk
  · intro k ks ihk ihks x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ihk
    · exact ihks x hx

theorem mem_verts_node {S : Finset ℕ} {y : List ℕ} {ks : List CT} {v : ℕ} :
    v ∈ verts (.node S y ks) ↔ v ∈ S ∨ ∃ k ∈ ks, v ∈ verts k := by
  simp [verts, mem_vertsL]

theorem subset_verts (t : CT) : t.S ⊆ t.verts := by
  cases t with
  | node S y ks => intro v hv; exact mem_verts_node.2 (Or.inl hv)

theorem verts_subset_of_mem {S : Finset ℕ} {y : List ℕ} {ks : List CT} {k : CT} (hk : k ∈ ks) :
    k.verts ⊆ (CT.node S y ks).verts := by
  intro v hv
  exact mem_verts_node.2 (Or.inr ⟨k, hk, hv⟩)

theorem goodL_iff {B : Finset ℕ} {ks : List CT} : GoodL B ks ↔ ∀ k ∈ ks, Good B k := by
  induction ks with
  | nil => simp [GoodL]
  | cons k ks ih => simp [GoodL, ih]

theorem connL_iff {ks : List CT} : ConnL ks ↔ ∀ k ∈ ks, Conn k := by
  induction ks with
  | nil => simp [ConnL]
  | cons k ks ih => simp [ConnL, ih]

/-- The local facts of `Good` that the counting uses. -/
theorem Good.leaf_kids {B S : Finset ℕ} {y : List ℕ} {ks : List CT} (h : Good B (.node S y ks)) :
    ∀ k ∈ ks, k.kids = [] → ¬ k.S ⊆ S := by
  unfold Good at h; exact h.2.2.2.2.2.1

theorem Good.single_kid {B S : Finset ℕ} {y : List ℕ} {ks : List CT} (h : Good B (.node S y ks)) :
    ∀ k, ks = [k] → k.S ≠ S := by
  unfold Good at h; exact h.2.2.2.2.2.2.1

theorem Good.kids {B S : Finset ℕ} {y : List ℕ} {ks : List CT} (h : Good B (.node S y ks)) :
    ∀ k ∈ ks, Good B k := by
  unfold Good at h; exact goodL_iff.1 h.2.2.2.2.2.2.2.2

theorem Good.label_sub {B S : Finset ℕ} {y : List ℕ} {ks : List CT} (h : Good B (.node S y ks)) : S ⊆ B := by
  unfold Good at h; exact h.1

theorem Conn.kids {S : Finset ℕ} {y : List ℕ} {ks : List CT} (h : Conn (.node S y ks)) :
    ∀ k ∈ ks, Conn k := by
  unfold Conn at h; exact connL_iff.1 h.1

theorem Conn.down {S : Finset ℕ} {y : List ℕ} {ks : List CT} (h : Conn (.node S y ks)) :
    ∀ k ∈ ks, ∀ v ∈ S, v ∈ verts k → v ∈ k.S := by
  unfold Conn at h; exact h.2.1

theorem Conn.disj {S : Finset ℕ} {y : List ℕ} {ks : List CT} (h : Conn (.node S y ks)) :
    ks.Pairwise (fun k₁ k₂ => ∀ v, v ∈ verts k₁ → v ∈ verts k₂ → v ∈ S) := by
  unfold Conn at h; exact h.2.2

/-! ## leaves -/

mutual
/-- Number of leaf runs. -/
def leaves : CT → ℕ
  | node _ _ ks => if ks.isEmpty then 1 else leavesL ks
def leavesL : List CT → ℕ
  | [] => 0
  | k :: ks => leaves k + leavesL ks
end

theorem leaves_pos (t : CT) : 1 ≤ leaves t := by
  induction t using ind with
  | h S y ks ih =>
    unfold leaves
    cases ks with
    | nil => simp
    | cons k ks =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, leavesL]
      have := ih k (by simp)
      omega

theorem leaves_node_nil (S : Finset ℕ) (y : List ℕ) : leaves (.node S y []) = 1 := by
  simp [leaves]

theorem leaves_node_single (S : Finset ℕ) (y : List ℕ) (k : CT) : leaves (.node S y [k]) = leaves k := by
  simp [leaves, leavesL]

theorem leaves_node_ne_nil (S : Finset ℕ) (y : List ℕ) (ks : List CT) (h : ks ≠ []) :
    leaves (.node S y ks) = leavesL ks := by
  cases ks with
  | nil => exact absurd rfl h
  | cons k ks => simp [leaves]

/-! ### the number of leaves -/

theorem leavesL_le {S : Finset ℕ} : ∀ {ks : List CT},
    ks.Pairwise (fun k₁ k₂ => ∀ v, v ∈ verts k₁ → v ∈ verts k₂ → v ∈ S) →
    (∀ k ∈ ks, leaves k ≤ (k.verts \ S).card) → leavesL ks ≤ ((vertsL ks) \ S).card
  | [], _, _ => by simp [leavesL, vertsL]
  | k :: ks, hp, hl => by
    have hp' := List.pairwise_cons.1 hp
    have h1 := hl k (by simp)
    have h2 := leavesL_le hp'.2 (fun k' hk' => hl k' (by simp [hk']))
    have hdisj : Disjoint (k.verts \ S) ((vertsL ks) \ S) := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      rw [Finset.mem_sdiff] at hv1 hv2
      obtain ⟨k', hk', hv'⟩ := mem_vertsL.1 hv2.1
      exact hv1.2 (hp'.1 k' hk' v hv1.1 hv')
    have hunion : (vertsL (k :: ks)) \ S = (k.verts \ S) ∪ ((vertsL ks) \ S) := by
      simp [vertsL, Finset.union_sdiff_distrib]
    rw [hunion, Finset.card_union_of_disjoint hdisj]
    simp only [leavesL]
    omega

/-- A kid of a run with label `S` has at most as many leaves as vertices it owns. -/
theorem leaves_le_owned {B S : Finset ℕ} {k : CT}
    (hg : Good B k) (hc : Conn k) (hleaf : k.kids = [] → ¬ k.S ⊆ S)
    (hdown : ∀ v ∈ S, v ∈ verts k → v ∈ k.S)
    (hrec : k.kids ≠ [] → leaves k ≤ (k.verts \ k.S).card) :
    leaves k ≤ (k.verts \ S).card := by
  by_cases hk : k.kids = []
  · have hn := hleaf hk
    rw [Finset.subset_iff] at hn
    push Not at hn
    obtain ⟨v, hv, hvS⟩ := hn
    have : 1 ≤ (k.verts \ S).card := by
      apply Finset.card_pos.2
      exact ⟨v, Finset.mem_sdiff.2 ⟨subset_verts k hv, hvS⟩⟩
    have hl : leaves k = 1 := by
      cases k with
      | node S' y ks => simp only [kids] at hk; subst hk; exact leaves_node_nil _ _
    omega
  · refine le_trans (hrec hk) (Finset.card_le_card ?_)
    intro v hv
    rw [Finset.mem_sdiff] at hv ⊢
    exact ⟨hv.1, fun hS => hv.2 (hdown v hS hv.1)⟩

/-- **Leaves are owned**: a non-leaf run has at most as many leaf runs as vertices outside its label. -/
theorem leaves_le_of_kids_ne_nil {B : Finset ℕ} (t : CT) :
    Good B t → Conn t → t.kids ≠ [] → leaves t ≤ (t.verts \ t.S).card := by
  induction t using ind with
  | h S y ks ih =>
    intro hg hc hne
    have hne' : ks ≠ [] := hne
    rw [leaves_node_ne_nil S y ks hne']
    have hkids := fun k hk => leaves_le_owned (S := S) (hg.kids k hk) (hc.kids k hk) (hg.leaf_kids k hk)
      (hc.down k hk) (fun hne2 => ih k hk (hg.kids k hk) (hc.kids k hk) hne2)
    refine le_trans (leavesL_le hc.disj hkids) ?_
    apply Finset.card_le_card
    intro v hv
    rw [Finset.mem_sdiff] at hv ⊢
    refine ⟨?_, hv.2⟩
    obtain ⟨k, hk, hvk⟩ := mem_vertsL.1 hv.1
    exact verts_subset_of_mem hk hvk

/-! ## the potential -/

/-- `φ t = |verts t| + |verts t \ t.S|`. -/
def phi (t : CT) : ℕ := t.verts.card + (t.verts \ t.S).card

theorem phi_kid_le {S : Finset ℕ} {y : List ℕ} {ks : List CT} (hc : Conn (.node S y ks)) {k : CT} (hk : k ∈ ks) :
    phi k ≤ phi (.node S y ks) := by
  unfold phi
  have h1 : k.verts.card ≤ (CT.node S y ks).verts.card := Finset.card_le_card (verts_subset_of_mem hk)
  have h2 : (k.verts \ k.S).card ≤ ((CT.node S y ks).verts \ (CT.node S y ks).S).card := by
    apply Finset.card_le_card
    intro v hv
    rw [Finset.mem_sdiff] at hv ⊢
    refine ⟨verts_subset_of_mem hk hv.1, fun hS => hv.2 (hc.down k hk v hS hv.1)⟩
  omega

theorem phi_single_lt {S : Finset ℕ} {y : List ℕ} {k : CT} (hc : Conn (.node S y [k])) (hne : k.S ≠ S) :
    phi k < phi (.node S y [k]) := by
  have hk : k ∈ [k] := by simp
  have hdown := hc.down k hk
  have hsub2 : k.verts \ k.S ⊆ (CT.node S y [k]).verts \ S := by
    intro v hv
    rw [Finset.mem_sdiff] at hv ⊢
    exact ⟨verts_subset_of_mem hk hv.1, fun hS => hv.2 (hdown v hS hv.1)⟩
  have h1 : k.verts.card ≤ (CT.node S y [k]).verts.card := Finset.card_le_card (verts_subset_of_mem hk)
  unfold phi
  show k.verts.card + (k.verts \ k.S).card <
    (CT.node S y [k]).verts.card + ((CT.node S y [k]).verts \ S).card
  by_cases hout : ∃ v ∈ S, v ∉ k.S
  · obtain ⟨v, hv, hvk⟩ := hout
    have hvt : v ∈ (CT.node S y [k]).verts := mem_verts_node.2 (Or.inl hv)
    have hnk : v ∉ k.verts := fun hvv => hvk (hdown v hv hvv)
    have : k.verts.card < (CT.node S y [k]).verts.card :=
      Finset.card_lt_card ⟨verts_subset_of_mem hk, fun hh => hnk (hh hvt)⟩
    have h2 := Finset.card_le_card hsub2
    omega
  · push Not at hout
    have : ∃ v ∈ k.S, v ∉ S := by
      by_contra hcon
      push Not at hcon
      exact hne (Finset.Subset.antisymm hcon hout)
    obtain ⟨v, hvk, hvS⟩ := this
    have hvt : v ∈ (CT.node S y [k]).verts \ S :=
      Finset.mem_sdiff.2 ⟨verts_subset_of_mem hk (subset_verts k hvk), hvS⟩
    have hnk : v ∉ k.verts \ k.S := fun hh => (Finset.mem_sdiff.1 hh).2 hvk
    have : (k.verts \ k.S).card < ((CT.node S y [k]).verts \ S).card :=
      Finset.card_lt_card ⟨hsub2, fun hh => hnk (hh hvt)⟩
    omega

/-! ## the count -/

theorem count_node (S : Finset ℕ) (y : List ℕ) (ks : List CT) : count (.node S y ks) = 1 + countL ks := rfl

theorem countL_add_le {q : ℕ} : ∀ {ks : List CT}, (∀ k ∈ ks, count k + q ≤ 2 * leaves k * q) →
    countL ks + ks.length * q ≤ 2 * leavesL ks * q
  | [], _ => by simp [countL, leavesL]
  | k :: ks, h => by
    have h1 := h k (by simp)
    have h2 := countL_add_le (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    simp only [countL, leavesL, List.length_cons]
    nlinarith

theorem arith_single {c L p : ℕ} (hL : 1 ≤ L) (_hp : 1 ≤ p) (h : c + p ≤ 2 * L * p) :
    1 + c + (p + 1) ≤ 2 * L * (p + 1) := by
  nlinarith

theorem arith_branch {c L p r : ℕ} (hr : 2 ≤ r) (h : c + r * (p + 1) ≤ 2 * L * (p + 1)) :
    1 + c + (p + 1) ≤ 2 * L * (p + 1) := by
  nlinarith

theorem count_add_le {B : Finset ℕ} (t : CT) :
    Good B t → Conn t → ∀ p, phi t ≤ p → count t + (p + 1) ≤ 2 * leaves t * (p + 1) := by
  induction t using ind with
  | h S y ks ih =>
    intro hg hc p hp
    rw [count_node]
    match ks, ih, hg, hc, hp with
    | [], _, _, _, _ =>
      simp only [countL, leaves_node_nil]
      omega
    | [k], ih, hg, hc, hp =>
      have hne := hg.single_kid k rfl
      have hlt := phi_single_lt hc hne
      have hp1 : 1 ≤ p := by omega
      have := ih k (by simp) (hg.kids k (by simp)) (hc.kids k (by simp)) (p - 1) (by omega)
      have hp' : p - 1 + 1 = p := by omega
      rw [hp'] at this
      rw [leaves_node_single]
      simp only [countL]
      exact arith_single (leaves_pos k) hp1 (by omega)
    | k₁ :: k₂ :: ks, ih, hg, hc, hp =>
      have hall : ∀ k ∈ k₁ :: k₂ :: ks, count k + (p + 1) ≤ 2 * leaves k * (p + 1) := by
        intro k hk
        exact ih k hk (hg.kids k hk) (hc.kids k hk) p
          (le_trans (phi_kid_le hc hk) hp)
      have hsum := countL_add_le hall
      rw [leaves_node_ne_nil _ _ _ (by simp)]
      exact arith_branch (r := (k₁ :: k₂ :: ks).length) (by simp) hsum

theorem Wf.count_le_aux {B : Finset ℕ} {kmax : ℕ} {t : CT} (h : Wf B kmax t) :
    t.count + (t.phi + 1) ≤ 2 * leaves t * (t.phi + 1) :=
  count_add_le t h.good h.conn _ le_rfl

theorem arith_final {c L p b : ℕ} (hL : L ≤ b) (hp : p ≤ 2 * b) (h : c + (p + 1) ≤ 2 * L * (p + 1)) :
    c ≤ runBound b := by
  unfold runBound
  have h1 : 2 * L * (p + 1) ≤ 2 * b * (2 * b + 1) := by
    apply Nat.mul_le_mul
    · omega
    · omega
  nlinarith

/-- **Counting the runs.**  A well-formed characteristic over a boundary of `b` vertices has at most `(2b+2)²`
runs. -/
theorem Wf.count_le {B : Finset ℕ} {kmax : ℕ} {t : CT} (h : Wf B kmax t) : t.count ≤ runBound B.card := by
  by_cases hk : t.kids = []
  · have hc : t.count = 1 := by
      cases t with
      | node S y ks => simp only [kids] at hk; subst hk; simp [count, countL]
    rw [hc]
    unfold runBound
    nlinarith
  · have hL : leaves t ≤ B.card := by
      refine le_trans (leaves_le_of_kids_ne_nil (B := B) t h.good h.conn hk) ?_
      rw [← h.verts_eq]
      exact le_trans (Finset.card_le_card Finset.sdiff_subset) le_rfl
    have hp : t.phi ≤ 2 * B.card := by
      unfold phi
      have h1 : (t.verts \ t.S).card ≤ t.verts.card := Finset.card_le_card Finset.sdiff_subset
      rw [h.verts_eq] at h1 ⊢
      omega
    exact arith_final hL hp h.count_le_aux

end CT

end Lax117284Proofs.Treewidth.Chars
