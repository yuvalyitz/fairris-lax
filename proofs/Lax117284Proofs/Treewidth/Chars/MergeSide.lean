import Lax117284Proofs.Treewidth.Chars.MergeBasic

/-!
# One side of a merged chain (C3)

`PA n K i b` is the set of vertices below and at the `i`-th node of the chain `n` with tail `K` (the junk of the
node itself only if `b`).  The *side lemmas* describe how it changes when the merged path moves from the `i`-th to
the `i'`-th node of this side (`i' = i` or `i' = i + 1`); they are used for both sides of the merge.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- The vertices at and below the `i`-th node (the junk of the node itself only if `b`). -/
def PA (n : List CNode) (K : List RT) (i : ℕ) (b : Bool) : Finset ℕ :=
  cbag n i ∪ (if b then RT.vertsL (cjunk n i) else ∅) ∪ RT.vertsL (succL n K i)

theorem mem_PA {n : List CNode} {K : List RT} {i : ℕ} {b : Bool} {x : ℕ} :
    x ∈ PA n K i b ↔ x ∈ cbag n i ∨ (b = true ∧ x ∈ RT.vertsL (cjunk n i)) ∨ x ∈ RT.vertsL (succL n K i) := by
  unfold PA
  cases b <;> simp [or_assoc]

/-- Moving to the same or the next node. -/
theorem PA_same {n : List CNode} {K : List RT} {i : ℕ} :
    PA n K i false = cbag n i ∪ RT.vertsL (succL n K i) := by
  unfold PA; simp

theorem PA_next {n : List CNode} {K : List RT} {i : ℕ} (hi : i + 1 < n.length) :
    PA n K (i + 1) true = RT.vertsL (succL n K i) := by
  ext x
  rw [mem_PA, vertsL_succL_lt hi]
  simp [or_assoc]

/-- The relation between the sets at `i` and at `i'` ∈ {i, i+1}. -/
theorem PA_step {n : List CNode} {K : List RT} {i i' : ℕ} (hi' : i' < n.length) (h : i' = i ∨ i' = i + 1) (b : Bool) :
    PA n K i b = cbag n i ∪ (if b then RT.vertsL (cjunk n i) else ∅) ∪ PA n K i' (decide (i ≠ i')) := by
  rcases h with rfl | rfl
  · simp only [ne_eq, not_true_eq_false, decide_false]
    rw [PA_same]
    unfold PA
    ext x; simp only [Finset.mem_union]; try tauto
  · have : decide (i ≠ i + 1) = true := by simp
    rw [this, PA_next hi']
    unfold PA
    ext x; simp only [Finset.mem_union]; try tauto

theorem PA_sub_step {n : List CNode} {K : List RT} {i i' : ℕ} (hi' : i' < n.length) (h : i' = i ∨ i' = i + 1) :
    ∀ x ∈ PA n K i' (decide (i ≠ i')), x ∈ cbag n i ∨ x ∈ RT.vertsL (succL n K i) := by
  intro x hx
  rcases h with rfl | rfl
  · simp only [ne_eq, not_true_eq_false, decide_false] at hx
    rw [PA_same] at hx
    exact Finset.mem_union.1 hx
  · have : decide (i ≠ i + 1) = true := by simp
    rw [this, PA_next hi'] at hx
    exact Or.inr hx

/-- Facts of one side used at a merged node. -/
theorem side_conn {n : List CNode} {K : List RT} {i i' : ℕ} (hi : i < n.length) (hi' : i' < n.length)
    (h : i' = i ∨ i' = i + 1)
    (hAr : ∀ K' ∈ cjunk n i ++ succL n K i, ∀ v ∈ cbag n i, v ∈ K'.verts → v ∈ K'.rootBag)
    (hAp : (cjunk n i ++ succL n K i).Pairwise
      (fun k1 k2 => ∀ v, v ∈ k1.verts → v ∈ k2.verts → v ∈ cbag n i)) :
    (∀ v ∈ cbag n i, v ∈ PA n K i' (decide (i ≠ i')) → v ∈ cbag n i') ∧
    (∀ J ∈ cjunk n i, ∀ v ∈ J.verts, v ∈ PA n K i' (decide (i ≠ i')) → v ∈ cbag n i) := by
  constructor
  · intro v hv hvP
    rcases h with rfl | rfl
    · exact hv
    · have : decide (i ≠ i + 1) = true := by simp
      rw [this, PA_next hi', mem_vertsL] at hvP
      obtain ⟨K', hK', hvK⟩ := hvP
      have := hAr K' (List.mem_append_right _ hK') v hv hvK
      rw [succL_of_lt hi', List.mem_singleton] at hK'
      subst hK'
      rw [rootBag_chainToRT_drop n K hi'] at this
      exact this
  · intro J hJ v hvJ hvP
    rcases PA_sub_step hi' h v hvP with h1 | h1
    · exact h1
    · rw [mem_vertsL] at h1
      obtain ⟨K', hK', hvK⟩ := h1
      rw [List.pairwise_append] at hAp
      exact hAp.2.2 J hJ K' hK' v hvJ hvK

/-- Coverage: what is below the `i`-th node is covered by what is at the `i'`-th. -/
theorem side_bags {n : List CNode} {K : List RT} {i i' : ℕ} (hi : i < n.length) (hi' : i' < n.length)
    (h : i' = i ∨ i' = i + 1) :
    ∀ K' ∈ succL n K i, ∀ X ∈ K'.bags,
      X = cbag n i' ∨ ((decide (i ≠ i') = true) ∧ ∃ J ∈ cjunk n i', X ∈ J.bags) ∨ ∃ K'' ∈ succL n K i', X ∈ K''.bags := by
  intro K' hK' X hX
  rcases h with rfl | rfl
  · right; right; exact ⟨K', hK', hX⟩
  · rw [succL_of_lt hi', List.mem_singleton] at hK'
    subst hK'
    rw [chainToRT_drop n K hi', RT.bags_node] at hX
    rcases hX with hX | ⟨J, hJ, hX⟩
    · left; exact hX
    · rcases List.mem_append.1 hJ with hJ | hJ
      · right; left; exact ⟨by simp, J, hJ, hX⟩
      · right; right; exact ⟨J, hJ, hX⟩

/-! ## the `B`-vertices of a side -/

theorem PA_inter_B {n : List CNode} {K : List RT} {B S : Finset ℕ}
    (hbag : ∀ x ∈ n, x.bag ∩ B = S) (hjunk : ∀ x ∈ n, ∀ J ∈ x.junk, J.verts ∩ B ⊆ S)
    {i : ℕ} (hi : i < n.length) (b : Bool) :
    ∀ x ∈ PA n K i b, x ∈ B → x ∈ S ∨ x ∈ RT.vertsL K := by
  intro x hx hxB
  rw [mem_PA] at hx
  have hmem : n[i] ∈ n := List.getElem_mem hi
  rcases hx with hx | ⟨-, hx⟩ | hx
  · left
    have hb : cbag n i = n[i].bag := by unfold cbag; rw [getD_chain hi]
    rw [hb] at hx
    rw [← hbag _ hmem]; exact Finset.mem_inter.2 ⟨hx, hxB⟩
  · left
    have hj' : cjunk n i = n[i].junk := by unfold cjunk; rw [getD_chain hi]
    rw [hj', mem_vertsL] at hx
    obtain ⟨J, hJ, hxJ⟩ := hx
    exact hjunk _ hmem J hJ (Finset.mem_inter.2 ⟨hxJ, hxB⟩)
  · exact reg_verts hbag hjunk hi x hx hxB

theorem S_sub_PA {n : List CNode} {K : List RT} {B S : Finset ℕ} (hbag : ∀ x ∈ n, x.bag ∩ B = S)
    {i : ℕ} (hi : i < n.length) (b : Bool) : S ⊆ PA n K i b := by
  intro x hx
  rw [mem_PA]
  left
  have hmem : n[i] ∈ n := List.getElem_mem hi
  have hb : cbag n i = n[i].bag := by unfold cbag; rw [getD_chain hi]
  rw [hb]
  have := hbag _ hmem
  rw [← this] at hx
  exact (Finset.mem_inter.1 hx).1

theorem vertsL_sub_PA {n : List CNode} {K : List RT} {i : ℕ} (hi : i < n.length) (b : Bool) :
    ∀ x ∈ RT.vertsL K, x ∈ PA n K i b := by
  intro x hx
  rw [mem_PA]
  exact Or.inr (Or.inr (vertsL_sub_succL hi x hx))

theorem succL_verts_sub {n : List CNode} {K : List RT} {U : Finset ℕ} (hbag : ∀ x ∈ n, x.bag ⊆ U)
    (hjunk : ∀ x ∈ n, ∀ J ∈ x.junk, J.verts ⊆ U) (hK : ∀ K' ∈ K, K'.verts ⊆ U) :
    ∀ d i, n.length = i + 1 + d → ∀ x ∈ RT.vertsL (succL n K i), x ∈ U := by
  intro d
  induction d with
  | zero =>
    intro i hi x hx
    rw [succL_of_last (by omega), mem_vertsL] at hx
    obtain ⟨K', hK', hxK⟩ := hx
    exact hK K' hK' hxK
  | succ d ih =>
    intro i hi x hx
    have hlt : i + 1 < n.length := by omega
    rw [vertsL_succL_lt hlt] at hx
    have hmem : n[i + 1] ∈ n := List.getElem_mem hlt
    rcases hx with hx | hx | hx
    · have hb : cbag n (i + 1) = n[i + 1].bag := by unfold cbag; rw [getD_chain hlt]
      rw [hb] at hx
      exact hbag _ hmem hx
    · have hj' : cjunk n (i + 1) = n[i + 1].junk := by unfold cjunk; rw [getD_chain hlt]
      rw [hj', mem_vertsL] at hx
      obtain ⟨J, hJ, hxJ⟩ := hx
      exact hjunk _ hmem J hJ hxJ
    · exact ih (i + 1) (by omega) x hx

theorem PA_sub_U {n : List CNode} {K : List RT} {U : Finset ℕ} (hbag : ∀ x ∈ n, x.bag ⊆ U)
    (hjunk : ∀ x ∈ n, ∀ J ∈ x.junk, J.verts ⊆ U) (hK : ∀ K' ∈ K, K'.verts ⊆ U) {i : ℕ} (hi : i < n.length)
    (b : Bool) : PA n K i b ⊆ U := by
  intro x hx
  have hmem : n[i] ∈ n := List.getElem_mem hi
  rw [mem_PA] at hx
  rcases hx with hx | ⟨-, hx⟩ | hx
  · have hb : cbag n i = n[i].bag := by unfold cbag; rw [getD_chain hi]
    rw [hb] at hx; exact hbag _ hmem hx
  · have hj' : cjunk n i = n[i].junk := by unfold cjunk; rw [getD_chain hi]
    rw [hj', mem_vertsL] at hx
    obtain ⟨J, hJ, hxJ⟩ := hx
    exact hjunk _ hmem J hJ hxJ
  · exact succL_verts_sub hbag hjunk hK (n.length - (i + 1)) i (by omega) x hx

theorem cbag_mem {n : List CNode} {i : ℕ} (hi : i < n.length) : cbag n i = n[i].bag := by
  unfold cbag; rw [getD_chain hi]

theorem cjunk_mem {n : List CNode} {i : ℕ} (hi : i < n.length) : cjunk n i = n[i].junk := by
  unfold cjunk; rw [getD_chain hi]

end Lax117284Proofs.Treewidth.Chars
