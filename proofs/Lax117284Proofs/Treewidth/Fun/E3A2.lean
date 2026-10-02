import Lax117284Proofs.Treewidth.Fun.E3A1

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E3A

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars CT

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

mutual
theorem winPlans_runs (U Q : ℕ) (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (v lo : ℕ) (hv : v ≤ U) (hlo : lo ≤ U) :
    ∀ (t : CT), sz t ≤ U → mx t ≤ U → 10 * U + 400 < B →
      Runs Δ' B fWinPlans [toVal v, toVal lo, toVal t] (toVal (winPlans v lo t))
        (Q * (3 * CT.count t - 1) * ((winPlans v lo t).length + 1))
  | CT.node S y ks, hU, hM, hB => by
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
    have hkc := kidChoices_runs U Q hQ v hv ks (by omega) (by omega) hB
    have hQ1 : 1000 ≤ Q := by nlinarith
    have hid := ids_lt (B := B) (by omega)
    have hlen := length_runs (x1 hΔ) B y (by omega)
    have hr1 := rangeP_runs hΔ B (y.length - lo) lo (by omega)
    have hr2 := rangeP_runs hΔ B (y.length - 1 - lo) lo (by omega)
    have hm1 := map_runs (x1 hΔ) B fEnds1 (toVal (v, lo, CT.node S y ks))
      (fun f : ℕ => ((CT.WPlan.endAt (CT.Cut.t1 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop f) ks], S) : CT.WPlan × CT × Finset ℕ))
      (fun _ => 400 * (U + 1)) (List.range' lo (y.length - lo))
      (fun f hf => by
        rw [List.mem_range'_1] at hf
        exact ends1_runs hΔ B U v lo f S y ks hU hM hv hlo (by omega) (by omega))
    have hm2 := map_runs (x1 hΔ) B fEnds2 (toVal (v, lo, CT.node S y ks))
      (fun f : ℕ => ((CT.WPlan.endAt (CT.Cut.t2 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop (f + 1)) ks], S) : CT.WPlan × CT × Finset ℕ))
      (fun _ => 400 * (U + 1)) (List.range' lo (y.length - 1 - lo))
      (fun f hf => by
        rw [List.mem_range'_1] at hf
        exact ends2_runs hΔ B U v lo f S y ks hU hM hv hlo (by omega) (by omega))
    have hV : (CT.node S y ks).verts.card ≤ U := le_trans (card_verts_le_sz _) hU
    have hSV : S ⊆ (CT.node S y ks).verts := CT.subset_verts (CT.node S y ks)
    have hm3 := map_runs (x1 hΔ) B fWhole (toVal (v, lo, CT.node S y ks))
      (fun combo : List (Option CT.WPlan × CT × Finset ℕ) => ((CT.WPlan.whole (combo.map (·.1)), CT.node (insert v S) (CT.plus1 (y.drop lo)) (combo.map (·.2.1)),
        combo.foldl (fun a c => a ∪ c.2.2) S) : CT.WPlan × CT × Finset ℕ))
      (fun _ => 400 * (U + 1) * (U + 1)) (kidChoices v ks)
      (fun combo hc => whole_runs hΔ B U v lo S y ks (CT.node S y ks).verts combo hU hM hv hlo hV hSV
        (fun c hc' w hw => CT.mem_verts_node.2 (Or.inr (CT.mem_vertsL.1 (kidChoices_sub v ks combo hc c hc' hw))))
        (by rw [kidChoices_combo_length v ks combo hc]; exact le_trans (length_le_sz ks) (by omega)) (by omega))
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hm1 hm2 hm3
    have ha1 := append_runs (x1 hΔ) B
      (List.map (fun f : ℕ => ((CT.WPlan.endAt (CT.Cut.t1 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop f) ks], S) : CT.WPlan × CT × Finset ℕ)) (List.range' lo (y.length - lo)))
      (List.map (fun f : ℕ => ((CT.WPlan.endAt (CT.Cut.t2 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop (f + 1)) ks], S) : CT.WPlan × CT × Finset ℕ)) (List.range' lo (y.length - 1 - lo)))
    have ha2 := append_runs (x1 hΔ) B
      (List.map (fun f : ℕ => ((CT.WPlan.endAt (CT.Cut.t1 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop f) ks], S) : CT.WPlan × CT × Finset ℕ)) (List.range' lo (y.length - lo)) ++
       List.map (fun f : ℕ => ((CT.WPlan.endAt (CT.Cut.t2 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop (f + 1)) ks], S) : CT.WPlan × CT × Finset ℕ)) (List.range' lo (y.length - 1 - lo)))
      (List.map (fun combo : List (Option CT.WPlan × CT × Finset ℕ) => ((CT.WPlan.whole (combo.map (·.1)), CT.node (insert v S) (CT.plus1 (y.drop lo)) (combo.map (·.2.1)),
        combo.foldl (fun a c => a ∪ c.2.2) S) : CT.WPlan × CT × Finset ℕ)) (kidChoices v ks))
    have hshow : winPlans v lo (CT.node S y ks) =
        List.map (fun f : ℕ => ((CT.WPlan.endAt (CT.Cut.t1 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop f) ks], S) : CT.WPlan × CT × Finset ℕ)) (List.range' lo (y.length - lo)) ++
        List.map (fun f : ℕ => ((CT.WPlan.endAt (CT.Cut.t2 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop (f + 1)) ks], S) : CT.WPlan × CT × Finset ℕ)) (List.range' lo (y.length - 1 - lo)) ++
        List.map (fun combo : List (Option CT.WPlan × CT × Finset ℕ) => ((CT.WPlan.whole (combo.map (·.1)), CT.node (insert v S) (CT.plus1 (y.drop lo)) (combo.map (·.2.1)),
          combo.foldl (fun a c => a ∪ c.2.2) S) : CT.WPlan × CT × Finset ℕ)) (kidChoices v ks) := rfl
    rw [hshow]
    simp only [toVal_pair, toVal_ct] at hm1 hm2 hm3
    refine Runs.mk (hΔ _ _ Δ_winPlans) ?_
    simp only [toVal_ct]
    ev_start
    · apply EvLe.letE
      · ev_run
      · ev_step
    · simp only [List.length_append, List.length_map, List.length_range']
      have hcnt : CT.count (CT.node S y ks) = 1 + countL ks := rfl
      have q1 : 400 * (U + 1) + 64 ≤ Q := by nlinarith
      have q2 : 400 * (U + 1) * (U + 1) + 32 ≤ Q := by nlinarith
      have q3 : 16 * U + 300 ≤ Q := by nlinarith
      have p1 : (y.length - lo) * (400 * (U + 1) + 64) ≤ (y.length - lo) * Q := Nat.mul_le_mul_left _ q1
      have p2 : (y.length - 1 - lo) * (400 * (U + 1) + 64) ≤ (y.length - 1 - lo) * Q := Nat.mul_le_mul_left _ q1
      have p3 : (kidChoices v ks).length * (400 * (U + 1) * (U + 1) + 32) ≤ (kidChoices v ks).length * Q :=
        Nat.mul_le_mul_left _ q2
      have hKL : (kidChoices v ks).length ≤ (y.length - lo) + (y.length - 1 - lo) + (kidChoices v ks).length := by omega
      have eP : Q * (3 * countL ks + 1) * ((kidChoices v ks).length + 1) ≤
          Q * (3 * countL ks + 1) * ((y.length - lo) + (y.length - 1 - lo) + (kidChoices v ks).length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have eR : Q * (3 * CT.count (CT.node S y ks) - 1) * ((y.length - lo) + (y.length - 1 - lo) + (kidChoices v ks).length + 1) =
          Q * (3 * countL ks + 1) * ((y.length - lo) + (y.length - 1 - lo) + (kidChoices v ks).length + 1) +
          (Q * (y.length - lo) + Q * (y.length - 1 - lo) + Q * (kidChoices v ks).length + Q) := by
        rw [hcnt]
        have : 3 * (1 + countL ks) - 1 = (3 * countL ks + 1) + 1 := by omega
        rw [this]; ring
      have m1 : (y.length - lo) * Q = Q * (y.length - lo) := Nat.mul_comm _ _
      have m2 : (y.length - 1 - lo) * Q = Q * (y.length - 1 - lo) := Nat.mul_comm _ _
      have m3 : (kidChoices v ks).length * Q = Q * (kidChoices v ks).length := Nat.mul_comm _ _
      have m4 : ∀ a b : ℕ, a * (400 * (U + 1) + 64) = a * (400 * (U + 1)) + 64 * a := fun a b => by ring
      have m5 : ∀ a : ℕ, a * (400 * (U + 1) * (U + 1) + 32) = a * (400 * (U + 1) * (U + 1)) + 32 * a := fun a => by ring
      have := m4 (y.length - lo) 0
      have := m4 (y.length - 1 - lo) 0
      have := m5 (kidChoices v ks).length
      omega
theorem kidChoices_runs (U Q : ℕ) (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (v : ℕ) (hv : v ≤ U) :
    ∀ (ks : List CT), sz ks ≤ U → mx ks ≤ U → 10 * U + 400 < B →
      Runs Δ' B fKidChoices [toVal v, toVal ks] (toVal (kidChoices v ks))
        (Q * (3 * CT.countL ks + 1) * ((kidChoices v ks).length + 1))
  | [], hU, hM, hB => by
    have hQ1 : 1000 ≤ Q := by nlinarith
    have hid := ids_lt (B := B) (by omega)
    refine Runs.mk (hΔ _ _ Δ_kidChoices) ?_
    simp only [kidChoices, toVal_cons, toVal_nil]
    ev_start
    · ev_run
    · simp [CT.countL]; omega
  | k :: ks, hU, hM, hB => by
    have hQ1 : 1000 ≤ Q := by nlinarith
    have hid := ids_lt (B := B) (by omega)
    have hU' : sz k ≤ U ∧ sz ks ≤ U := by rw [sz_cons] at hU; omega
    have hM' : mx k ≤ U ∧ mx ks ≤ U := by rw [mx_cons] at hM; omega
    have hw := winPlans_runs U Q hQ v 0 hv (Nat.zero_le _) k hU'.1 hM'.1 hB
    have hkc := kidChoices_runs U Q hQ v hv ks hU'.2 hM'.2 hB
    have hmap := map_runs (x1 hΔ) B fSomeF (Val.nat 0)
      (fun p : CT.WPlan × CT × Finset ℕ => ((some p.1, p.2.1, p.2.2) : Option CT.WPlan × CT × Finset ℕ))
      (fun _ => 12) (winPlans v 0 k)
      (fun p _ => by obtain ⟨w, c, s⟩ := p; exact someF_runs hΔ B c s w (by omega))
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap
    have hfm := flatMap_runs (x1 hΔ) B fKcLam (toVal (kidChoices v ks))
      (fun o : Option CT.WPlan × CT × Finset ℕ => (kidChoices v ks).map (o :: ·))
      (fun _ => 23 * (kidChoices v ks).length + 12)
      ((none, k, ∅) :: (winPlans v 0 k).map (fun p : CT.WPlan × CT × Finset ℕ => ((some p.1, p.2.1, p.2.2) : Option CT.WPlan × CT × Finset ℕ)))
      (fun o _ => kcLam_runs hΔ B o (kidChoices v ks) (by omega))
    have hsum := sum_map_le (fun (a : Option CT.WPlan × CT × Finset ℕ) => (23 * (kidChoices v ks).length + 12) + 10 * ((kidChoices v ks).map (a :: ·)).length + 20) (33 * (kidChoices v ks).length + 32)
      ((none, k, ∅) :: (winPlans v 0 k).map (fun p : CT.WPlan × CT × Finset ℕ => ((some p.1, p.2.1, p.2.2) : Option CT.WPlan × CT × Finset ℕ)))
      (fun a _ => by simp only [List.length_map]; omega)
    have hlen := kidChoices_length_pos v ks
    have hshow : kidChoices v (k :: ks) = ((none, k, ∅) :: (winPlans v 0 k).map (fun p : CT.WPlan × CT × Finset ℕ => ((some p.1, p.2.1, p.2.2) : Option CT.WPlan × CT × Finset ℕ))).flatMap (fun o : Option CT.WPlan × CT × Finset ℕ => (kidChoices v ks).map (o :: ·)) := rfl
    rw [hshow]
    refine Runs.mk (hΔ _ _ Δ_kidChoices) ?_
    simp only [toVal_cons, toVal_pair, toVal_none, toVal_empty_finset]
    ev_start
    · ev_run
    · have hpos := count_pos k
      have hlo : ((none, k, (∅ : Finset ℕ)) :: (winPlans v 0 k).map (fun p : CT.WPlan × CT × Finset ℕ => ((some p.1, p.2.1, p.2.2) : Option CT.WPlan × CT × Finset ℕ))).length = (winPlans v 0 k).length + 1 := by simp
      have hlenout : List.length (List.flatMap (fun o : Option CT.WPlan × CT × Finset ℕ => (kidChoices v ks).map (o :: ·))
          ((none, k, (∅ : Finset ℕ)) :: (winPlans v 0 k).map (fun p : CT.WPlan × CT × Finset ℕ => ((some p.1, p.2.1, p.2.2) : Option CT.WPlan × CT × Finset ℕ))))
          = ((winPlans v 0 k).length + 1) * (kidChoices v ks).length := by
        rw [length_flatMap_eq (n := (kidChoices v ks).length)]
        · rw [hlo]
        · intro o _; simp
      rw [hlo] at hsum
      rw [hlenout]
      have key := kc_arith (3 * count k - 1) (3 * countL ks + 1) (winPlans v 0 k).length
        (kidChoices v ks).length Q hlen hQ1
      have e : 3 * countL (k :: ks) + 1 = (3 * count k - 1) + (3 * countL ks + 1) + 1 := by
        simp only [countL]; omega
      rw [e]
      omega
end

end proofs
end E3A
end Lax117284Proofs.Treewidth.Fun
