import Lax117284Proofs.Treewidth.Fun.E3DefsC
import Lax117284Proofs.Treewidth.Fun.E3B2
import Lax117284Proofs.Treewidth.Fun.E3MathC

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E3C

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars CT

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem xB : E3B.Δ ⊑ Δ' := Ext.trans extB hΔ
theorem xA : E3A.Δ ⊑ Δ' := Ext.trans E3B.extA (xB hΔ)
theorem y1 : Lib1.Δ ⊑ Δ' := Ext.trans Lib.ext1 (Ext.trans E3A.extLib (xA hΔ))
theorem y2 : Lib2.Δ ⊑ Δ' := Ext.trans Lib.ext2 (Ext.trans E3A.extLib (xA hΔ))
theorem y3 : Lib3.Δ ⊑ Δ' := Ext.trans Lib.ext3 (Ext.trans E3A.extLib (xA hΔ))
theorem y4 : Lib4.Δ ⊑ Δ' := Ext.trans Lib.ext4 (Ext.trans E3A.extLib (xA hΔ))

theorem subN_runs (N : Finset ℕ) (pl : CT.Plan) (c : CT) (s : Finset ℕ) (hB : 1 < B) :
    Runs Δ' B fSubN [toVal N, toVal (pl, c, s)] (toVal (decide (N ⊆ s)))
      (60 * (N.card + s.card) + 30) := by
  have h1 := Lib3.subset_runs (y3 hΔ) B hB N s (decide (N ⊆ s)) (by simp)
  refine Runs.mk (hΔ _ _ Δ_subN) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

theorem mk1_runs (pl : CT.Plan) (c : CT) (s : Finset ℕ) (hB : 0 < B) :
    Runs Δ' B fMk1 [Val.nat 0, toVal (pl, c, s)] (toVal ((([] : List ℕ), pl, c) : List ℕ × CT.Plan × CT)) 8 := by
  refine Runs.mk (hΔ _ _ Δ_mk1) ?_
  simp only [toVal_pair, toVal_nil]
  ev_start
  · ev_run
  · omega

theorem mk2_runs (pl : CT.Plan) (c : CT) (hB : 0 < B) :
    Runs Δ' B fMk2 [Val.nat 0, toVal (pl, c)] (toVal ((([] : List ℕ), pl, c) : List ℕ × CT.Plan × CT)) 7 := by
  refine Runs.mk (hΔ _ _ Δ_mk2) ?_
  simp only [toVal_pair, toVal_nil]
  ev_start
  · ev_run
  · omega

theorem kid_runs (S : Finset ℕ) (y : List ℕ) (pre post : List CT) (path : List ℕ) (pl : CT.Plan) (c : CT) :
    Runs Δ' B fKid [toVal (pre.length, S, y, pre, post), toVal (path, pl, c)]
      (toVal (((pre.length :: path, pl, CT.node S y (pre ++ c :: post)) : List ℕ × CT.Plan × CT)))
      (10 * pre.length + 40) := by
  have h1 := append_runs (y1 hΔ) B pre (c :: post)
  simp only [toVal_cons] at h1
  refine Runs.mk (hΔ _ _ Δ_kid) ?_
  simp only [toVal_pair, toVal_cons, toVal_ct]
  ev_start
  · ev_run
  · omega

/-! ### `maxEntry` -/

theorem maxL_runs (l : List ℕ) (hB : 0 < B) :
    Runs Δ' B fMaxL [toVal l] (toVal (l.foldr max 0)) (20 * l.length + 6) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_maxL) ?_
    ev_start
    · ev_run
    · simp
  | cons a l ih =>
    have h1 := max_runs (y1 hΔ) B a (l.foldr max 0)
    refine Runs.mk (hΔ _ _ Δ_maxL) ?_
    simp only [List.foldr_cons]
    ev_start
    · ev_run
    · simp only [List.length_cons]; omega

theorem maxEntryL_runs (hB : 0 < B) : ∀ (ks : List CT),
    (∀ k ∈ ks, Runs Δ' B fMaxEntry [toVal k] (toVal k.maxEntry) (40 * sz k)) →
    Runs Δ' B fMaxEntryL [toVal ks] (toVal (maxEntryL ks)) (40 * sz ks)
  | [], _ => by
    refine Runs.mk (hΔ _ _ Δ_maxEntryL) ?_
    simp only [maxEntryL]
    ev_start
    · ev_run
    · simp
  | k :: ks, h => by
    have h1 := h k (List.mem_cons_self ..)
    have h2 := maxEntryL_runs hB ks (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    have h3 := max_runs (y1 hΔ) B k.maxEntry (maxEntryL ks)
    refine Runs.mk (hΔ _ _ Δ_maxEntryL) ?_
    simp only [maxEntryL, toVal_cons]
    ev_start
    · ev_run
    · rw [sz_cons]; omega

theorem maxEntry_runs (hB : 0 < B) : ∀ (c : CT), Runs Δ' B fMaxEntry [toVal c] (toVal c.maxEntry) (40 * sz c) := by
  intro c
  induction c using CT.ind with
  | h S y ks ih =>
    have h1 := maxL_runs hΔ B y hB
    have h2 := maxEntryL_runs hΔ B hB ks ih
    have h3 := max_runs (y1 hΔ) B (y.foldr max 0) (maxEntryL ks)
    refine Runs.mk (hΔ _ _ Δ_maxEntry) ?_
    simp only [maxEntry, toVal_ct]
    ev_start
    · ev_run
    · rw [sz_ct_node, sz_list_nat y]; omega

end proofs
end E3C
end Lax117284Proofs.Treewidth.Fun
