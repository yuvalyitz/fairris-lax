import Lax117284Proofs.Treewidth.Fun.E3DefsB
import Lax117284Proofs.Treewidth.Fun.E3A2

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E3B

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars CT

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem xA : E3A.Δ ⊑ Δ' := Ext.trans extA hΔ
theorem y1 : Lib1.Δ ⊑ Δ' := Ext.trans Lib.ext1 (Ext.trans E3A.extLib (xA hΔ))
theorem y2 : Lib2.Δ ⊑ Δ' := Ext.trans Lib.ext2 (Ext.trans E3A.extLib (xA hΔ))
theorem y3 : Lib3.Δ ⊑ Δ' := Ext.trans Lib.ext3 (Ext.trans E3A.extLib (xA hΔ))
theorem y4 : Lib4.Δ ⊑ Δ' := Ext.trans Lib.ext4 (Ext.trans E3A.extLib (xA hΔ))

theorem topDirect_runs (w : CT.WPlan) (c : CT) (s : Finset ℕ) (hB : 2 < B) :
    Runs Δ' B fTopDirect [Val.nat 0, toVal (w, c, s)]
      (toVal ((CT.Plan.top none w, c, s) : CT.Plan × CT × Finset ℕ)) 14 := by
  refine Runs.mk (hΔ _ _ Δ_topDirect) ?_
  simp only [toVal_pair, toVal_plan_top, toVal_none]
  ev_start
  · ev_run
  · omega

theorem pre1In_runs (U f v : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) (w : CT.WPlan) (c : CT) (s : Finset ℕ)
    (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hf : f ≤ U) (hB : 10 * U + 400 < B) :
    Runs Δ' B fPre1In [toVal (f, v, CT.node S y ks), toVal (w, c, s)]
      (toVal ((CT.Plan.top (some (CT.Cut.t1 f)) w, CT.node S (y.take (f + 1)) [c], s) : CT.Plan × CT × Finset ℕ))
      (30 * U + 100) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have h1 := take_runs (y1 hΔ) B (f + 1) y (by omega)
  have h2 : min (f + 1) y.length ≤ U := by omega
  refine Runs.mk (hΔ _ _ Δ_pre1In) ?_
  simp only [toVal_pair, toVal_plan_top, toVal_some, toVal_cut_t1, toVal_ct, toVal_cons, toVal_nil]
  ev_start
  · ev_run
  · omega

theorem pre2In_runs (U f v : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) (w : CT.WPlan) (c : CT) (s : Finset ℕ)
    (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hf : f ≤ U) (hB : 10 * U + 400 < B) :
    Runs Δ' B fPre2In [toVal (f, v, CT.node S y ks), toVal (w, c, s)]
      (toVal ((CT.Plan.top (some (CT.Cut.t2 f)) w, CT.node S (y.take (f + 1)) [c], s) : CT.Plan × CT × Finset ℕ))
      (30 * U + 100) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have h1 := take_runs (y1 hΔ) B (f + 1) y (by omega)
  have h2 : min (f + 1) y.length ≤ U := by omega
  refine Runs.mk (hΔ _ _ Δ_pre2In) ?_
  simp only [toVal_pair, toVal_plan_top, toVal_some, toVal_cut_t2, toVal_ct, toVal_cons, toVal_nil]
  ev_start
  · ev_run
  · omega

omit hΔ in
theorem winPlans_length_pos (v lo : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    1 ≤ (winPlans v lo (CT.node S y ks)).length :=
  le_trans (kidChoices_length_pos v ks) (kidChoices_le_winPlans v lo S y ks)

theorem pre1_runs (U Q : ℕ) (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (P v f : ℕ) (S : Finset ℕ) (y : List ℕ)
    (ks : List CT) (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hv : v ≤ U) (hf : f ≤ U)
    (hB : 10 * U + 400 < B) (hP : Q * (3 * CT.count (CT.node S y ks) - 1) ≤ P) :
    Runs Δ' B fPre1 [toVal (v, CT.node S y ks), toVal f]
      (toVal ((winPlans v f (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t1 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))))
      (8 * (P * (winPlans v f (CT.node S y ks)).length)) := by
  have hcnt := count_pos (CT.node S y ks)
  have hL := winPlans_length_pos v f S y ks
  have hw := (E3A.winPlans_runs (xA hΔ) B U Q hQ v f hv hf (CT.node S y ks) hU hM hB).mono
    (Nat.mul_le_mul_right _ hP)
  have hmap := map_runs (y1 hΔ) B fPre1In (toVal (f, v, CT.node S y ks))
    (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t1 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))
    (fun _ => 30 * U + 100) (winPlans v f (CT.node S y ks))
    (fun p _ => by obtain ⟨w, c, s⟩ := p; exact pre1In_runs hΔ B U f v S y ks w c s hU hM hf hB)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap
  have hid := ids_lt (B := B) (by omega)
  have hid' := E3A.ids_lt (B := B) (by omega)
  refine Runs.mk (hΔ _ _ Δ_pre1) ?_
  simp only [toVal_pair] at hmap ⊢
  ev_start
  · ev_run
  · have hq1 : 1000 * (U + 1) ≤ Q := by nlinarith
    have hq2 : Q * 2 ≤ Q * (3 * CT.count (CT.node S y ks) - 1) := Nat.mul_le_mul_left _ (by omega)
    have hq : 30 * U + 120 ≤ P := by omega
    have e1 : (winPlans v f (CT.node S y ks)).length * (30 * U + 100) ≤
        (winPlans v f (CT.node S y ks)).length * P := Nat.mul_le_mul_left _ (by omega)
    have e2 : P * ((winPlans v f (CT.node S y ks)).length + 1) = P * (winPlans v f (CT.node S y ks)).length + P := by ring
    have e3 : (winPlans v f (CT.node S y ks)).length * P = P * (winPlans v f (CT.node S y ks)).length := Nat.mul_comm _ _
    have e4 : P ≤ P * (winPlans v f (CT.node S y ks)).length := Nat.le_mul_of_pos_right _ hL
    have e5 := Nat.mul_le_mul_left (winPlans v f (CT.node S y ks)).length (show 20 ≤ P by omega)
    omega

theorem pre2_runs (U Q : ℕ) (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (P v f : ℕ) (S : Finset ℕ) (y : List ℕ)
    (ks : List CT) (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hv : v ≤ U) (hf : f + 1 ≤ U)
    (hB : 10 * U + 400 < B) (hP : Q * (3 * CT.count (CT.node S y ks) - 1) ≤ P) :
    Runs Δ' B fPre2 [toVal (v, CT.node S y ks), toVal f]
      (toVal ((winPlans v (f + 1) (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t2 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))))
      (8 * (P * (winPlans v (f + 1) (CT.node S y ks)).length)) := by
  have hcnt := count_pos (CT.node S y ks)
  have hL := winPlans_length_pos v (f + 1) S y ks
  have hw := (E3A.winPlans_runs (xA hΔ) B U Q hQ v (f + 1) hv hf (CT.node S y ks) hU hM hB).mono
    (Nat.mul_le_mul_right _ hP)
  have hmap := map_runs (y1 hΔ) B fPre2In (toVal (f, v, CT.node S y ks))
    (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t2 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))
    (fun _ => 30 * U + 100) (winPlans v (f + 1) (CT.node S y ks))
    (fun p _ => by obtain ⟨w, c, s⟩ := p; exact pre2In_runs hΔ B U f v S y ks w c s hU hM (by omega) hB)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap
  have hid := ids_lt (B := B) (by omega)
  have hid' := E3A.ids_lt (B := B) (by omega)
  refine Runs.mk (hΔ _ _ Δ_pre2) ?_
  simp only [toVal_pair] at hmap ⊢
  ev_start
  · ev_run
  · have hq1 : 1000 * (U + 1) ≤ Q := by nlinarith
    have hq2 : Q * 2 ≤ Q * (3 * CT.count (CT.node S y ks) - 1) := Nat.mul_le_mul_left _ (by omega)
    have hq : 30 * U + 120 ≤ P := by omega
    have e1 : (winPlans v (f + 1) (CT.node S y ks)).length * (30 * U + 100) ≤
        (winPlans v (f + 1) (CT.node S y ks)).length * P := Nat.mul_le_mul_left _ (by omega)
    have e2 : P * ((winPlans v (f + 1) (CT.node S y ks)).length + 1) = P * (winPlans v (f + 1) (CT.node S y ks)).length + P := by ring
    have e3 : (winPlans v (f + 1) (CT.node S y ks)).length * P = P * (winPlans v (f + 1) (CT.node S y ks)).length := Nat.mul_comm _ _
    have e4 : P ≤ P * (winPlans v (f + 1) (CT.node S y ks)).length := Nat.le_mul_of_pos_right _ hL
    have e5 := Nat.mul_le_mul_left (winPlans v (f + 1) (CT.node S y ks)).length (show 20 ≤ P by omega)
    omega

theorem wtopPlans_runs (U Q : ℕ) (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (P v : ℕ) (S : Finset ℕ) (y : List ℕ)
    (ks : List CT) (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hv : v ≤ U)
    (hB : 10 * U + 400 < B) (hP : Q * (3 * CT.count (CT.node S y ks) - 1) ≤ P) :
    Runs Δ' B fWtopPlans [toVal v, toVal (CT.node S y ks)] (toVal (wtopPlans v (CT.node S y ks)))
      (100 * (P * ((wtopPlans v (CT.node S y ks)).length + 1))) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have hcnt := count_pos (CT.node S y ks)
  have hL0 := winPlans_length_pos v 0 S y ks
  have hq1 : 1000 * (U + 1) ≤ Q := by nlinarith
  have hq2 : Q * 2 ≤ Q * (3 * CT.count (CT.node S y ks) - 1) := Nat.mul_le_mul_left _ (by omega)
  have hq : 1000 * (U + 1) ≤ P := le_trans hq1 (le_trans (Nat.le_mul_of_pos_right Q (by norm_num)) (le_trans hq2 hP))
  have hw0 := (E3A.winPlans_runs (xA hΔ) B U Q hQ v 0 hv (Nat.zero_le _) (CT.node S y ks) hU hM hB).mono
    (Nat.mul_le_mul_right _ hP)
  have hmap0 := map_runs (y1 hΔ) B fTopDirect (Val.nat 0)
    (fun p : CT.WPlan × CT × Finset ℕ => ((CT.Plan.top none p.1, p.2.1, p.2.2) : CT.Plan × CT × Finset ℕ))
    (fun _ => 14) (winPlans v 0 (CT.node S y ks))
    (fun p _ => by obtain ⟨w, c, s⟩ := p; exact topDirect_runs hΔ B w c s (by omega))
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap0
  have hlen := length_runs (y1 hΔ) B y (by omega)
  have hr1 := range_runs (y1 hΔ) B y.length (by omega)
  have hr2 := range_runs (y1 hΔ) B (y.length - 1) (by omega)
  have hf1 := flatMap_runs (y1 hΔ) B fPre1 (toVal (v, CT.node S y ks))
    (fun f : ℕ => (winPlans v f (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t1 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ)))
    (fun f => 8 * (P * (winPlans v f (CT.node S y ks)).length)) (List.range y.length)
    (fun f hf => pre1_runs hΔ B U Q hQ P v f S y ks hU hM hv (by rw [List.mem_range] at hf; omega) hB hP)
  have hs1 := flatMap_sum_le
    (fun f : ℕ => (winPlans v f (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t1 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ)))
    (fun f => 8 * (P * (winPlans v f (CT.node S y ks)).length)) (9 * P) (List.range y.length)
    (fun f _ => by
      have hL := winPlans_length_pos v f S y ks
      simp only [List.length_map]
      have := Nat.mul_le_mul_left (winPlans v f (CT.node S y ks)).length (show 30 ≤ P by omega)
      have e : P * (winPlans v f (CT.node S y ks)).length = (winPlans v f (CT.node S y ks)).length * P := Nat.mul_comm _ _
      have e2 : 9 * P * (winPlans v f (CT.node S y ks)).length = 9 * ((winPlans v f (CT.node S y ks)).length * P) := by ring
      omega)
  have hf2 := flatMap_runs (y1 hΔ) B fPre2 (toVal (v, CT.node S y ks))
    (fun f : ℕ => (winPlans v (f + 1) (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t2 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ)))
    (fun f => 8 * (P * (winPlans v (f + 1) (CT.node S y ks)).length)) (List.range (y.length - 1))
    (fun f hf => pre2_runs hΔ B U Q hQ P v f S y ks hU hM hv (by rw [List.mem_range] at hf; omega) hB hP)
  have hs2 := flatMap_sum_le
    (fun f : ℕ => (winPlans v (f + 1) (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t2 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ)))
    (fun f => 8 * (P * (winPlans v (f + 1) (CT.node S y ks)).length)) (9 * P) (List.range (y.length - 1))
    (fun f _ => by
      have hL := winPlans_length_pos v (f + 1) S y ks
      simp only [List.length_map]
      have := Nat.mul_le_mul_left (winPlans v (f + 1) (CT.node S y ks)).length (show 30 ≤ P by omega)
      have e : P * (winPlans v (f + 1) (CT.node S y ks)).length = (winPlans v (f + 1) (CT.node S y ks)).length * P := Nat.mul_comm _ _
      have e2 : 9 * P * (winPlans v (f + 1) (CT.node S y ks)).length = 9 * ((winPlans v (f + 1) (CT.node S y ks)).length * P) := by ring
      omega)
  have ha1 := append_runs (y1 hΔ) B
    ((winPlans v 0 (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ => ((CT.Plan.top none p.1, p.2.1, p.2.2) : CT.Plan × CT × Finset ℕ)))
    ((List.range y.length).flatMap (fun f : ℕ => (winPlans v f (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t1 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))))
  have ha2 := append_runs (y1 hΔ) B
    ((winPlans v 0 (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ => ((CT.Plan.top none p.1, p.2.1, p.2.2) : CT.Plan × CT × Finset ℕ)) ++
    (List.range y.length).flatMap (fun f : ℕ => (winPlans v f (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t1 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))))
    ((List.range (y.length - 1)).flatMap (fun f : ℕ => (winPlans v (f + 1) (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t2 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))))
  have hshow : wtopPlans v (CT.node S y ks) =
      (winPlans v 0 (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ => ((CT.Plan.top none p.1, p.2.1, p.2.2) : CT.Plan × CT × Finset ℕ)) ++
      (List.range y.length).flatMap (fun f : ℕ => (winPlans v f (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t1 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))) ++
      (List.range (y.length - 1)).flatMap (fun f : ℕ => (winPlans v (f + 1) (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t2 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))) := rfl
  have hid := ids_lt (B := B) (by omega)
  have hid' := E3A.ids_lt (B := B) (by omega)
  rw [hshow]
  refine Runs.mk (hΔ _ _ Δ_wtopPlans) ?_
  simp only [toVal_pair, toVal_ct] at hf1 hf2 hw0 ⊢
  ev_start
  · apply EvLe.letE
    · ev_run
    · ev_step
  · simp only [List.length_append, List.length_map] at hs1 hs2 ⊢
    set X0 := (winPlans v 0 (CT.node S y ks)).length with hX0
    set X1 := (List.flatMap (fun f : ℕ => (winPlans v f (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t1 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ)))
        (List.range y.length)).length with hX1
    set X2 := (List.flatMap (fun f : ℕ => (winPlans v (f + 1) (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t2 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ)))
        (List.range (y.length - 1))).length with hX2
    have e0 : P * (X0 + 1) = P * X0 + P := by ring
    have e1 : 9 * P * X1 = 9 * (P * X1) := by ring
    have e2 : 9 * P * X2 = 9 * (P * X2) := by ring
    have e3 : P * (X0 + X1 + X2 + 1) = P * X0 + P * X1 + P * X2 + P := by ring
    have f0 : X0 * 100 ≤ X0 * P := Nat.mul_le_mul_left _ (by omega)
    have f1 : X1 * 100 ≤ X1 * P := Nat.mul_le_mul_left _ (by omega)
    have g0 : X0 * P = P * X0 := Nat.mul_comm _ _
    have g1 : X1 * P = P * X1 := Nat.mul_comm _ _
    have hmul : ∀ a b : ℕ, 100 * (a * b) = 100 * (a * b) := fun _ _ => rfl
    have hy1 : y.length * 100 ≤ P := by omega
    have hp1 : P * X0 ≥ P := Nat.le_mul_of_pos_right _ (by omega)
    omega

end proofs
end E3B
end Lax117284Proofs.Treewidth.Fun
