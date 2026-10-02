import Lax117284Proofs.Treewidth.Fun.E3DefsA
import Lax117284Proofs.Treewidth.Size.Plans
import Lax117284Proofs.Treewidth.Fun.E3Util
import Lax117284Proofs.Treewidth.Fun.E3MathA

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E3A

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem plus1_runs : ∀ (y : List ℕ), mx y + 2 < B →
    Runs Δ' B fPlus1 [toVal y] (toVal (CT.plus1 y)) (12 * y.length + 6) := by
  intro y
  induction y with
  | nil =>
    intro _
    refine Runs.mk (hΔ _ _ Δ_plus1) ?_
    ev_start
    · ev_run
    · simp [CT.plus1]
  | cons a l ih =>
    intro hB
    have hm : mx l + 2 < B := by simp only [mx_cons, mx_nat] at hB; omega
    have ha : a + 1 < B := by simp only [mx_cons, mx_nat] at hB; omega
    have ih := ih hm
    refine Runs.mk (hΔ _ _ Δ_plus1) ?_
    ev_start
    · ev_run
    · simp [CT.plus1]; omega

theorem rangeP_runs : ∀ (n lo : ℕ), lo + n + 2 < B →
    Runs Δ' B fRangeP [toVal lo, toVal n] (toVal (List.range' lo n)) (14 * n + 6) := by
  intro n
  induction n with
  | zero =>
    intro lo _
    refine Runs.mk (hΔ _ _ Δ_rangeP) ?_
    ev_start
    · ev_run
    · simp
  | succ n ih =>
    intro lo hB
    have ih := ih (lo + 1) (by omega)
    refine Runs.mk (hΔ _ _ Δ_rangeP) ?_
    ev_start
    · ev_run
    · simp; omega

theorem x1 : Lib1.Δ ⊑ Δ' := Ext.trans Lib.ext1 (Ext.trans extLib hΔ)
theorem x2 : Lib2.Δ ⊑ Δ' := Ext.trans Lib.ext2 (Ext.trans extLib hΔ)
theorem x3 : Lib3.Δ ⊑ Δ' := Ext.trans Lib.ext3 (Ext.trans extLib hΔ)
theorem x4 : Lib4.Δ ⊑ Δ' := Ext.trans Lib.ext4 (Ext.trans extLib hΔ)

theorem ends1_runs (U v lo f : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT)
    (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hv : v ≤ U) (hlo : lo ≤ U) (hf : f ≤ U)
    (hB : 4 * U + 400 < B) :
    Runs Δ' B fEnds1 [toVal (v, lo, CT.node S y ks), toVal f]
      (toVal (CT.WPlan.endAt (CT.Cut.t1 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop f) ks], S))
      (400 * (U + 1)) := by
  have h1 := Lib3.insert_runs (x3 hΔ) B v S
  have h2 := take_runs (x1 hΔ) B (f + 1) y (by omega)
  have h3 := drop_runs (x1 hΔ) B lo (y.take (f + 1)) (by omega)
  have h4 := drop_runs (x1 hΔ) B f y (by omega)
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have h5 := plus1_runs hΔ B ((y.take (f + 1)).drop lo)
    (by have := mx_drop_le lo (y.take (f + 1)); have := mx_take_le (f + 1) y; omega)
  have h6 : ((y.take (f + 1)).drop lo).length ≤ U := by simp only [List.length_drop, List.length_take]; omega
  have h7 : min lo (y.take (f + 1)).length ≤ U := by omega
  have h8 : min f y.length ≤ U := by omega
  have h9 : min (f + 1) y.length ≤ U := by omega
  refine Runs.mk (hΔ _ _ Δ_ends1) ?_
  simp only [toVal_pair, CT.WPlan.endAt, toVal_wp_endAt, toVal_cut_t1, toVal_ct, toVal_cons, toVal_nil]
  ev_start
  · ev_run
  · omega

theorem ends2_runs (U v lo f : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT)
    (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hv : v ≤ U) (hlo : lo ≤ U) (hf : f ≤ U)
    (hB : 4 * U + 400 < B) :
    Runs Δ' B fEnds2 [toVal (v, lo, CT.node S y ks), toVal f]
      (toVal (CT.WPlan.endAt (CT.Cut.t2 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop (f + 1)) ks], S))
      (400 * (U + 1)) := by
  have h1 := Lib3.insert_runs (x3 hΔ) B v S
  have h2 := take_runs (x1 hΔ) B (f + 1) y (by omega)
  have h3 := drop_runs (x1 hΔ) B lo (y.take (f + 1)) (by omega)
  have h4 := drop_runs (x1 hΔ) B (f + 1) y (by omega)
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have h5 := plus1_runs hΔ B ((y.take (f + 1)).drop lo)
    (by have := mx_drop_le lo (y.take (f + 1)); have := mx_take_le (f + 1) y; omega)
  have h6 : ((y.take (f + 1)).drop lo).length ≤ U := by simp only [List.length_drop, List.length_take]; omega
  have h7 : min lo (y.take (f + 1)).length ≤ U := by omega
  have h8 : min (f + 1) y.length ≤ U := by omega
  refine Runs.mk (hΔ _ _ Δ_ends2) ?_
  simp only [toVal_pair, CT.WPlan.endAt, toVal_wp_endAt, toVal_cut_t2, toVal_ct, toVal_cons, toVal_nil]
  ev_start
  · ev_run
  · omega

theorem fstF_runs (o : Option CT.WPlan) (c : CT) (s : Finset ℕ) :
    Runs Δ' B fFstF [Val.nat 0, toVal (o, c, s)] (toVal o) 2 := by
  refine Runs.mk (hΔ _ _ Δ_fstF) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

theorem sndFstF_runs (o : Option CT.WPlan) (c : CT) (s : Finset ℕ) :
    Runs Δ' B fSndFstF [Val.nat 0, toVal (o, c, s)] (toVal c) 3 := by
  refine Runs.mk (hΔ _ _ Δ_sndFstF) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

theorem unionStep_runs (acc : Finset ℕ) (o : Option CT.WPlan) (c : CT) (s : Finset ℕ) :
    Runs Δ' B fUnionStep [Val.nat 0, toVal acc, toVal (o, c, s)] (toVal (acc ∪ s)) (60 * (acc.card + s.card) + 40) := by
  have h1 := Lib3.union_runs (x3 hΔ) B acc s
  refine Runs.mk (hΔ _ _ Δ_unionStep) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

theorem whole_runs (U v lo : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) (V : Finset ℕ)
    (combo : List (Option CT.WPlan × CT × Finset ℕ))
    (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hv : v ≤ U) (hlo : lo ≤ U)
    (hV : V.card ≤ U) (hSV : S ⊆ V) (hc : ∀ c ∈ combo, c.2.2 ⊆ V) (hlen : combo.length ≤ U)
    (hB : 4 * U + 400 < B) :
    Runs Δ' B fWhole [toVal (v, lo, CT.node S y ks), toVal combo]
      (toVal (CT.WPlan.whole (combo.map (·.1)), CT.node (insert v S) (CT.plus1 (y.drop lo)) (combo.map (·.2.1)),
        combo.foldl (fun a c => a ∪ c.2.2) S))
      (400 * (U + 1) * (U + 1)) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have h1 := Lib3.insert_runs (x3 hΔ) B v S
  have h3 := drop_runs (x1 hΔ) B lo y (by omega)
  have h5 := plus1_runs hΔ B (y.drop lo) (by have := mx_drop_le lo y; omega)
  have h6 : (y.drop lo).length ≤ U := by simp only [List.length_drop]; omega
  have h7 : min lo y.length ≤ U := by omega
  have hm1 := map_runs (x1 hΔ) B fFstF (Val.nat 0) (fun x : Option CT.WPlan × CT × Finset ℕ => x.1) (fun _ => 2)
    combo (fun a _ => by obtain ⟨o, c, s⟩ := a; exact fstF_runs hΔ B o c s)
  have hm2 := map_runs (x1 hΔ) B fSndFstF (Val.nat 0) (fun x : Option CT.WPlan × CT × Finset ℕ => x.2.1) (fun _ => 3)
    combo (fun a _ => by obtain ⟨o, c, s⟩ := a; exact sndFstF_runs hΔ B o c s)
  have hfold := foldl_runs (x1 hΔ) B fUnionStep (Val.nat 0)
    (fun (a : Finset ℕ) (c : Option CT.WPlan × CT × Finset ℕ) => a ∪ c.2.2)
    (fun (a : Finset ℕ) (c : Option CT.WPlan × CT × Finset ℕ) => 60 * (a.card + c.2.2.card) + 40)
    (fun b => b ⊆ V) S combo hSV
    (fun b' a hb ha => Finset.union_subset hb (hc a ha))
    (fun b' a hb ha => by obtain ⟨o, c, s⟩ := a; exact unionStep_runs hΔ B b' o c s)
  have hfc := foldCost_le (fun (a : Finset ℕ) (c : Option CT.WPlan × CT × Finset ℕ) => a ∪ c.2.2)
    (fun (a : Finset ℕ) (c : Option CT.WPlan × CT × Finset ℕ) => 60 * (a.card + c.2.2.card) + 40)
    (fun b => b ⊆ V) (120 * U + 40) combo S hSV
    (fun b' a hb ha => Finset.union_subset hb (hc a ha))
    (fun b' a hb ha => by
      have h1 := Finset.card_le_card hb
      have h2 := Finset.card_le_card (hc a ha)
      show 60 * (b'.card + a.2.2.card) + 40 ≤ 120 * U + 40
      omega)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hm1 hm2
  have hid := ids_lt (B := B) (by omega)
  refine Runs.mk (hΔ _ _ Δ_whole) ?_
  simp only [toVal_pair, CT.WPlan.whole, toVal_wp_whole, toVal_ct, toVal_cons, toVal_nil]
  ev_start
  · ev_run
  · have e1 : combo.length * (120 * U + 40) ≤ U * (120 * U + 40) := Nat.mul_le_mul_right _ hlen
    have e2 : U * (120 * U + 40) + 900 * U + 500 ≤ 400 * (U + 1) * (U + 1) := by nlinarith
    omega

theorem someF_runs (c : CT) (s : Finset ℕ) (p : CT.WPlan) (hB : 1 < B) :
    Runs Δ' B fSomeF [Val.nat 0, toVal (p, c, s)] (toVal ((some p, c, s) : Option CT.WPlan × CT × Finset ℕ)) 12 := by
  refine Runs.mk (hΔ _ _ Δ_someF) ?_
  simp only [toVal_pair, toVal_some]
  ev_start
  · ev_run
  · omega

theorem consF_runs {α : Type} [ToVal α] (o : α) (x : List α) :
    Runs Δ' B fConsF [toVal o, toVal x] (toVal (o :: x)) 3 := by
  refine Runs.mk (hΔ _ _ Δ_consF) ?_
  simp only [toVal_cons]
  ev_start
  · ev_run
  · omega

theorem kcLam_runs {α : Type} [ToVal α] (o : α) (kc : List (List α)) (hB : 300 < B) :
    Runs Δ' B fKcLam [toVal kc, toVal o] (toVal (kc.map (o :: ·))) (23 * kc.length + 12) := by
  have hm := map_runs (x1 hΔ) B fConsF (toVal o) (fun x : List α => o :: x) (fun _ => 3) kc
    (fun a _ => consF_runs hΔ B o a)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hm
  have hid := ids_lt (B := B) (by omega)
  refine Runs.mk (hΔ _ _ Δ_kcLam) ?_
  ev_start
  · ev_run
  · omega

end proofs
end E3A
end Lax117284Proofs.Treewidth.Fun
