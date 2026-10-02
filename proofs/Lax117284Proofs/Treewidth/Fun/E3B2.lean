import Lax117284Proofs.Treewidth.Fun.E3B1
import Lax117284Proofs.Treewidth.Size.PlanSize

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E3B

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars CT

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem candFn_runs (U : ℕ) (N : Finset ℕ) (c : List ℕ) (hN : N.card ≤ U) (hc : c.length ≤ U) :
    Runs Δ' B fCandFn [toVal N, toVal c] (toVal (N ∪ c.toFinset)) (200 * ((U + 1) * (U + 1))) := by
  have h1 := Lib4.toFinset_runs (y4 hΔ) B c
  have h2 := Lib3.union_runs (y3 hΔ) B N c.toFinset
  have hc2 : c.toFinset.card ≤ U := le_trans (List.toFinset_card_le c) hc
  refine Runs.mk (hΔ _ _ Δ_candFn) ?_
  ev_start
  · ev_run
  · have e1 : (c.length + 1) ^ 2 ≤ (U + 1) * (U + 1) := by nlinarith
    have e2 : U + 1 ≤ (U + 1) * (U + 1) := by nlinarith
    omega

theorem chainCands_runs (U : ℕ) (S N : Finset ℕ) (hS : S.card ≤ U) (hN : N.card ≤ U) (hB : 10 * U + 400 < B) :
    Runs Δ' B fChainCands [toVal S, toVal N] (toVal (chainCands S N))
      (500 * ((U + 1) * (U + 1)) * (chainCands S N).length) := by
  have hd := Lib3.sdiff_runs (y3 hΔ) B S N
  have hcard : ((S \ N).sort (· ≤ ·)).length ≤ U := by
    rw [Finset.length_sort]; exact le_trans (Finset.card_le_card Finset.sdiff_subset) hS
  have hsub := Lib4.sublists_runs (y4 hΔ) B (by omega) ((S \ N).sort (· ≤ ·))
  have hmap := map_runs (y1 hΔ) B fCandFn (toVal N)
    (fun c : List ℕ => N ∪ c.toFinset) (fun _ => 200 * ((U + 1) * (U + 1)))
    ((S \ N).sort (· ≤ ·)).sublists
    (fun c hc => candFn_runs hΔ B U N c hN
      (le_trans (List.mem_sublists.1 hc).length_le hcard))
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap
  have hid := ids_lt (B := B) (by omega)
  have hlen : (chainCands S N).length = 2 ^ ((S \ N).sort (· ≤ ·)).length := by
    simp [chainCands, List.length_sublists]
  have hpos : 1 ≤ (chainCands S N).length := by rw [hlen]; exact Nat.one_le_two_pow
  have hshow : chainCands S N = ((S \ N).sort (· ≤ ·)).sublists.map (fun c : List ℕ => N ∪ c.toFinset) := rfl
  rw [hshow] at hlen hpos ⊢
  refine Runs.mk (hΔ _ _ Δ_chainCands) ?_
  ev_start
  · ev_run
  · simp only [List.length_map, List.length_sublists] at hlen hpos ⊢ hmap
    set T := 2 ^ ((S \ N).sort fun x1 x2 => x1 ≤ x2).length with hT
    have hT1 : 1 ≤ T := Nat.one_le_two_pow
    have hf1 : U + 1 ≤ (U + 1) * (U + 1) := by nlinarith
    have e1 : T * (200 * ((U + 1) * (U + 1))) = 200 * (T * ((U + 1) * (U + 1))) := by ring
    have e2 : 500 * ((U + 1) * (U + 1)) * T = 500 * (T * ((U + 1) * (U + 1))) := by ring
    have e3 : (U + 1) * (U + 1) ≤ T * ((U + 1) * (U + 1)) := Nat.le_mul_of_pos_left _ (by omega)
    have e4 : T ≤ T * ((U + 1) * (U + 1)) := Nat.le_mul_of_pos_right _ (by omega)
    omega

theorem subOf_runs (bound X : Finset ℕ) (b : Bool) (hb : b = true ↔ X ⊆ bound) (hB : 1 < B) :
    Runs Δ' B fSubOf [toVal bound, toVal X] (toVal b) (60 * (X.card + bound.card) + 30) := by
  have h1 := Lib3.subset_runs (y3 hΔ) B hB X bound b hb
  refine Runs.mk (hΔ _ _ Δ_subOf) ?_
  ev_start
  · ev_run
  · omega

theorem pairCh_runs (chain : List (Finset ℕ)) (M : Finset ℕ) :
    Runs Δ' B fPairCh [toVal chain, toVal M] (toVal (chain, M)) 3 := by
  refine Runs.mk (hΔ _ _ Δ_pairCh) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

theorem sel_runs (bound X : Finset ℕ) (chain : List (Finset ℕ)) (hB : 1 < B) :
    Runs Δ' B fSel [toVal (bound, chain), toVal X]
      (toVal (decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound))))
      (120 * (X.card + bound.card) + 60) := by
  have h1 := Lib3.subset_runs (y3 hΔ) B hB X bound (decide (X ⊆ bound)) (by simp)
  have h2 := Lib3.subset_runs (y3 hΔ) B hB bound X (decide (bound ⊆ X)) (by simp)
  refine Runs.mk (hΔ _ _ Δ_sel) ?_
  simp only [toVal_pair]
  by_cases hX : X ⊆ bound
  · simp only [hX, decide_true] at h1 ⊢
    cases chain with
    | nil =>
      simp only [toVal_nil, List.isEmpty_nil, Bool.true_or, Bool.and_true, decide_true, toVal_true] 
      ev_start
      · ev_run
      · omega
    | cons c cs =>
      by_cases hb : bound ⊆ X
      · have hne : ¬ X ⊂ bound := fun h => (Finset.ssubset_def.1 h).2 hb
        simp only [hb, decide_true] at h2
        simp only [List.isEmpty_cons, Bool.false_or, Bool.true_and, hne, decide_false, toVal_false]
        ev_start
        · ev_run
        · omega
      · have hss : X ⊂ bound := Finset.ssubset_def.2 ⟨hX, hb⟩
        simp only [hb, decide_false] at h2
        simp only [List.isEmpty_cons, Bool.false_or, Bool.true_and, hss, decide_true, toVal_true]
        ev_start
        · ev_run
        · omega
  · simp only [hX, decide_false, Bool.false_and, toVal_false] at h1 ⊢
    ev_start
    · ev_run
    · omega

theorem goStep_runs (cands : List (Finset ℕ)) (f : ℕ) (chain : List (Finset ℕ)) (X : Finset ℕ)
    (res : List (List (Finset ℕ) × Finset ℕ)) (cc : ℕ)
    (hc : Runs Δ' B fChainsGo [toVal cands, toVal f, toVal X, toVal (chain ++ [X])] (toVal res) cc) (hB : 0 < B) :
    Runs Δ' B fGoStep [toVal (cands, f, chain), toVal X] (toVal res) (cc + 10 * chain.length + 30) := by
  have h1 := append_runs (y1 hΔ) B chain [X]
  simp only [toVal_cons, toVal_nil] at h1
  refine Runs.mk (hΔ _ _ Δ_goStep) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

theorem chainsGo_runs (U Qc : ℕ) (cands : List (Finset ℕ)) (hcands : ∀ X ∈ cands, X.card ≤ U)
    (hQc : 1000 * ((U + 1) * (cands.length + 1)) ≤ Qc) (hB : 10 * U + 400 < B) :
    ∀ (fuel : ℕ) (bound : Finset ℕ) (chain : List (Finset ℕ)), bound.card ≤ U → chain.length + fuel ≤ U →
      Runs Δ' B fChainsGo [toVal cands, toVal fuel, toVal bound, toVal chain]
        (toVal (chainsGo cands fuel bound chain))
        (Qc * (fuel + 1) * (2 * (chainsGo cands fuel bound chain).length + 1)) := by
  have hid := ids_lt (B := B) (by omega)
  have hid' := E3A.ids_lt (B := B) (by omega)
  have arithN : cands.length * (120 * U + 30) + cands.length * (240 * U + 60) + 48 * cands.length + 200
      ≤ 1000 * ((U + 1) * (cands.length + 1)) := by nlinarith
  intro fuel
  induction fuel with
  | zero =>
    intro bound chain hb hf
    have hfil := filter_runs (y1 hΔ) B fSubOf (toVal bound) (fun X : Finset ℕ => decide (X ⊆ bound))
      (fun X => 60 * (X.card + bound.card) + 30) cands
      (fun X _ => subOf_runs hΔ B bound X _ (by simp) (by omega))
    have hsum := sum_map_le (fun X : Finset ℕ => 60 * (X.card + bound.card) + 30) (120 * U + 30) cands
      (fun X hX => by have := hcands X hX; omega)
    have hmap := map_runs (y1 hΔ) B fPairCh (toVal chain) (fun M : Finset ℕ => (chain, M))
      (fun _ => 3) (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound)))
      (fun M _ => pairCh_runs hΔ B chain M)
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap
    have hshow : chainsGo cands 0 bound chain =
        (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound))).map (fun M : Finset ℕ => (chain, M)) := rfl
    rw [hshow]
    refine Runs.mk (hΔ _ _ Δ_chainsGo) ?_
    simp only [List.length_map] 
    ev_start
    · apply EvLe.letE
      · ev_run
      · ev_run
    · set m := (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound))).length with hm
      have e : Qc * (0 + 1) * (2 * m + 1) = 2 * (Qc * m) + Qc := by ring
      have hq : 23 ≤ Qc := by nlinarith
      have hqm : 23 * m ≤ Qc * m := Nat.mul_le_mul_right _ hq
      omega
  | succ f ih =>
    intro bound chain hb hf
    have hfil := filter_runs (y1 hΔ) B fSubOf (toVal bound) (fun X : Finset ℕ => decide (X ⊆ bound))
      (fun X => 60 * (X.card + bound.card) + 30) cands
      (fun X _ => subOf_runs hΔ B bound X _ (by simp) (by omega))
    have hsum := sum_map_le (fun X : Finset ℕ => 60 * (X.card + bound.card) + 30) (120 * U + 30) cands
      (fun X hX => by have := hcands X hX; omega)
    have hmap := map_runs (y1 hΔ) B fPairCh (toVal chain) (fun M : Finset ℕ => (chain, M))
      (fun _ => 3) (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound)))
      (fun M _ => pairCh_runs hΔ B chain M)
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap
    have hsel := filter_runs (y1 hΔ) B fSel (toVal (bound, chain))
      (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound)))
      (fun X => 120 * (X.card + bound.card) + 60) cands
      (fun X _ => sel_runs hΔ B bound X chain (by omega))
    have hsum2 := sum_map_le (fun X : Finset ℕ => 120 * (X.card + bound.card) + 60) (240 * U + 60) cands
      (fun X hX => by have := hcands X hX; omega)
    have hlen12 : (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound)))).length ≤
        (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound))).length :=
      filter_len_le_of_imp _ _ cands (fun X _ h => by simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢; exact h.1)
    have hgo : ∀ X ∈ cands.filter (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound))),
        Runs Δ' B fGoStep [toVal (cands, f, chain), toVal X] (toVal (chainsGo cands f X (chain ++ [X])))
          (2 * (Qc * (f + 1)) * (chainsGo cands f X (chain ++ [X])).length + (Qc * (f + 1) + 10 * U + 30)) := by
      intro X hX
      have hXc : X ∈ cands := (List.mem_filter.1 hX).1
      have hch := ih X (chain ++ [X]) (hcands X hXc) (by simp only [List.length_append, List.length_singleton]; omega)
      have h3 := goStep_runs hΔ B cands f chain X _ _ hch (by omega)
      refine h3.mono ?_
      have e : Qc * (f + 1) * (2 * (chainsGo cands f X (chain ++ [X])).length + 1) =
          2 * (Qc * (f + 1)) * (chainsGo cands f X (chain ++ [X])).length + Qc * (f + 1) := by ring
      omega
    have hfm := flatMap_runs (y1 hΔ) B fGoStep (toVal (cands, f, chain))
      (fun X : Finset ℕ => chainsGo cands f X (chain ++ [X]))
      (fun X => 2 * (Qc * (f + 1)) * (chainsGo cands f X (chain ++ [X])).length + (Qc * (f + 1) + 10 * U + 30))
      (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound)))) hgo
    have hsm := sum_affine_le (fun X : Finset ℕ => chainsGo cands f X (chain ++ [X]))
      (fun X => 2 * (Qc * (f + 1)) * (chainsGo cands f X (chain ++ [X])).length + (Qc * (f + 1) + 10 * U + 30))
      (2 * (Qc * (f + 1)) + 10) (Qc * (f + 1) + 10 * U + 50)
      (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound))))
      (fun X _ => by
        have e : (2 * (Qc * (f + 1)) + 10) * (chainsGo cands f X (chain ++ [X])).length =
            2 * (Qc * (f + 1)) * (chainsGo cands f X (chain ++ [X])).length +
              10 * (chainsGo cands f X (chain ++ [X])).length := by ring
        omega)
    have happ := append_runs (y1 hΔ) B
      ((cands.filter (fun X : Finset ℕ => decide (X ⊆ bound))).map (fun M : Finset ℕ => (chain, M)))
      ((cands.filter (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound)))).flatMap
        (fun X : Finset ℕ => chainsGo cands f X (chain ++ [X])))
    have hshow : chainsGo cands (f + 1) bound chain =
        (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound))).map (fun M : Finset ℕ => (chain, M)) ++
        (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound)))).flatMap
          (fun X : Finset ℕ => chainsGo cands f X (chain ++ [X])) := rfl
    rw [hshow]
    refine Runs.mk (hΔ _ _ Δ_chainsGo) ?_
    simp only [toVal_pair] at hsel hfm
    ev_start
    · apply EvLe.letE
      · ev_run
      · ev_run
    · simp only [List.length_append, List.length_map] at hsm ⊢
      set n := cands.length with hn
      set m := (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound))).length with hm
      set m2 := (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound)))).length with hm2
      set SL := (List.flatMap (fun X : Finset ℕ => chainsGo cands f X (chain ++ [X]))
        (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound))))).length with hSL
      set W := Qc * (f + 1) with hW
      have hW2 : Qc * (f + 1 + 1) = W + Qc := by rw [hW]; ring
      have eR : (W + Qc) * (2 * (m + SL) + 1) = 2 * (W * m) + 2 * (W * SL) + W + 2 * (Qc * m) + 2 * (Qc * SL) + Qc := by ring
      have eA : (2 * W + 10) * SL = 2 * (W * SL) + 10 * SL := by ring
      have eB : (W + 10 * U + 50) * m2 = W * m2 + (10 * U + 50) * m2 := by ring
      have f1 : W * m2 ≤ W * m := Nat.mul_le_mul_left _ hlen12
      have f2 : (10 * U + 50) * m2 ≤ (10 * U + 50) * m := Nat.mul_le_mul_left _ hlen12
      have hq1 : 10 * U + 83 ≤ Qc := by nlinarith
      have hqm : (10 * U + 83) * m ≤ Qc * m := Nat.mul_le_mul_right _ hq1
      have hqs : 10 * SL ≤ Qc * SL := Nat.mul_le_mul_right _ (by omega)
      have hqm2 : (10 * U + 83) * m = (10 * U + 50) * m + 33 * m := by ring
      rw [hW2, eR]
      omega

theorem allChains_runs (U Qc : ℕ) (S N : Finset ℕ) (hNS : N ⊆ S) (hS : S.card + 1 ≤ U)
    (hQc : 1000 * ((U + 1) * ((chainCands S N).length + 1)) ≤ Qc) (hB : 10 * U + 400 < B) :
    Runs Δ' B fAllChains [toVal S, toVal N] (toVal (allChains S N))
      (Qc * (U + 1) * (2 * (allChains S N).length + 2)) := by
  have hid := ids_lt (B := B) (by omega)
  have hcc := chainCands_runs hΔ B U S N (by omega) (le_trans (Finset.card_le_card hNS) (by omega)) hB
  have hlen := Lib4.card_runs (y4 hΔ) B S (by omega)
  have hgo := (chainsGo_runs hΔ B U Qc (chainCands S N)
    (fun X hX => le_trans (Finset.card_le_card (mem_chainCands_sub hNS hX)) (by omega)) hQc hB
    (S.card + 1) S [] (by omega) (by simp; omega)).mono (show Qc * (S.card + 1 + 1) * (2 * (chainsGo (chainCands S N) (S.card + 1) S []).length + 1) ≤
      Qc * (U + 1) * (2 * (chainsGo (chainCands S N) (S.card + 1) S []).length + 1) from
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
  have hshow : allChains S N = chainsGo (chainCands S N) (S.card + 1) S [] := rfl
  rw [hshow]
  refine Runs.mk (hΔ _ _ Δ_allChains) ?_
  ev_start
  · ev_run
  · set L := (chainsGo (chainCands S N) (S.card + 1) S []).length with hL
    set n := (chainCands S N).length with hn
    have e : Qc * (U + 1) * (2 * L + 2) = Qc * (U + 1) * (2 * L + 1) + Qc * (U + 1) := by ring
    have e2 : 500 * ((U + 1) * (U + 1)) * n + 8 * S.card + 100 ≤ Qc * (U + 1) := by nlinarith
    omega

theorem pathStep_runs (U : ℕ) (X : Finset ℕ) (acc : CT) (hX : X.card ≤ U) (hB : 10 * U + 400 < B) :
    Runs Δ' B fPathStep [Val.nat 0, toVal X, toVal acc] (toVal (CT.node X [X.card] [acc])) (8 * U + 30) := by
  have h1 := Lib4.card_runs (y4 hΔ) B X (by omega)
  refine Runs.mk (hΔ _ _ Δ_pathStep) ?_
  simp only [toVal_ct, toVal_cons, toVal_nil]
  ev_start
  · ev_run
  · omega

theorem pathSubtree_runs (U v : ℕ) (chain : List (Finset ℕ)) (M : Finset ℕ) (hch : ∀ X ∈ chain, X.card ≤ U)
    (hlen : chain.length ≤ U) (hM : M.card ≤ U) (hv : v ≤ U) (hB : 10 * U + 400 < B) :
    Runs Δ' B fPathSubtree [toVal v, toVal chain, toVal M] (toVal (pathSubtree v chain M))
      (300 * ((U + 1) * (U + 1))) := by
  have hid := ids_lt (B := B) (by omega)
  have h1 := Lib3.insert_runs (y3 hΔ) B v M
  have h2 := Lib4.card_runs (y4 hΔ) B M (by omega)
  have hfold := Lib2.foldr_runs (y2 hΔ) B fPathStep (Val.nat 0)
    (fun (X : Finset ℕ) (acc : CT) => CT.node X [X.card] [acc])
    (fun (X : Finset ℕ) (acc : CT) => 8 * U + 30) (fun _ => True)
    (CT.node (insert v M) [M.card + 1] []) chain trivial (fun _ _ _ _ => trivial)
    (fun X acc hX _ => pathStep_runs hΔ B U X acc (hch X hX) hB)
  have hfc := foldrCost_le (fun (X : Finset ℕ) (acc : CT) => CT.node X [X.card] [acc])
    (fun (X : Finset ℕ) (acc : CT) => 8 * U + 30) (fun _ => True) (CT.node (insert v M) [M.card + 1] [])
    (8 * U + 30) trivial chain (fun _ _ _ _ => trivial) (fun _ _ _ _ => le_rfl)
  have hshow : pathSubtree v chain M =
      chain.foldr (fun (X : Finset ℕ) (acc : CT) => CT.node X [X.card] [acc]) (CT.node (insert v M) [M.card + 1] []) := rfl
  rw [hshow]
  refine Runs.mk (hΔ _ _ Δ_pathSubtree) ?_
  simp only [toVal_ct, toVal_cons, toVal_nil] at hfold ⊢
  ev_start
  · ev_run
  · have e1 : chain.length * (8 * U + 30) ≤ U * (8 * U + 30) := Nat.mul_le_mul_right _ hlen
    have e2 : U * (8 * U + 30) + 100 * U + 300 ≤ 300 * ((U + 1) * (U + 1)) := by nlinarith
    omega

theorem attIn1_runs (U f : ℕ) (br : CT) (chain : List (Finset ℕ)) (M : Finset ℕ) (S : Finset ℕ) (y : List ℕ)
    (ks : List CT) (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hf : f ≤ U)
    (hB : 10 * U + 400 < B) :
    Runs Δ' B fAttIn1 [toVal (br, (chain, M), CT.node S y ks), toVal f]
      (toVal (((CT.Plan.att (some (CT.Cut.t1 f)) chain M, CT.node S (y.take (f + 1)) [br, CT.node S (y.drop f) ks]) :
        CT.Plan × CT))) (100 * (U + 1)) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have h1 := take_runs (y1 hΔ) B (f + 1) y (by omega)
  have h2 := drop_runs (y1 hΔ) B f y (by omega)
  have h3 : min (f + 1) y.length ≤ U := by omega
  have h4 : min f y.length ≤ U := by omega
  refine Runs.mk (hΔ _ _ Δ_attIn1) ?_
  simp only [toVal_pair, toVal_plan_att, toVal_some, toVal_cut_t1, toVal_ct, toVal_cons, toVal_nil]
  ev_start
  · ev_run
  · omega

theorem attIn2_runs (U f : ℕ) (br : CT) (chain : List (Finset ℕ)) (M : Finset ℕ) (S : Finset ℕ) (y : List ℕ)
    (ks : List CT) (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hf : f ≤ U)
    (hB : 10 * U + 400 < B) :
    Runs Δ' B fAttIn2 [toVal (br, (chain, M), CT.node S y ks), toVal f]
      (toVal (((CT.Plan.att (some (CT.Cut.t2 f)) chain M, CT.node S (y.take (f + 1)) [br, CT.node S (y.drop (f + 1)) ks]) :
        CT.Plan × CT))) (100 * (U + 1)) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have h1 := take_runs (y1 hΔ) B (f + 1) y (by omega)
  have h2 := drop_runs (y1 hΔ) B (f + 1) y (by omega)
  have h3 : min (f + 1) y.length ≤ U := by omega
  refine Runs.mk (hΔ _ _ Δ_attIn2) ?_
  simp only [toVal_pair, toVal_plan_att, toVal_some, toVal_cut_t2, toVal_ct, toVal_cons, toVal_nil]
  ev_start
  · ev_run
  · omega

theorem att_runs (U v : ℕ) (chain : List (Finset ℕ)) (M : Finset ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT)
    (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hv : v ≤ U)
    (hch : ∀ X ∈ chain, X.card ≤ U) (hlen : chain.length ≤ U) (hMc : M.card ≤ U) (hB : 10 * U + 400 < B) :
    Runs Δ' B fAtt [toVal (v, CT.node S y ks), toVal (chain, M)]
      (toVal (((CT.Plan.att none chain M, CT.node S y (ks ++ [pathSubtree v chain M])) ::
        (List.range y.length).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t1 f)) chain M,
            CT.node S (y.take (f + 1)) [pathSubtree v chain M, CT.node S (y.drop f) ks]) : CT.Plan × CT))) ++
        (List.range (y.length - 1)).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t2 f)) chain M,
            CT.node S (y.take (f + 1)) [pathSubtree v chain M, CT.node S (y.drop (f + 1)) ks]) : CT.Plan × CT))))
      (800 * ((U + 1) * (U + 1))) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have hid := ids_lt (B := B) (by omega)
  have hbr := pathSubtree_runs hΔ B U v chain M hch hlen hMc hv hB
  have hks : ks.length ≤ U := le_trans (length_le_sz ks) (by omega)
  have hlenr := length_runs (y1 hΔ) B y (by omega)
  have hr1 := range_runs (y1 hΔ) B y.length (by omega)
  have hr2 := range_runs (y1 hΔ) B (y.length - 1) (by omega)
  have hm1 := map_runs (y1 hΔ) B fAttIn1 (toVal (pathSubtree v chain M, (chain, M), CT.node S y ks))
    (fun f : ℕ => ((CT.Plan.att (some (CT.Cut.t1 f)) chain M,
            CT.node S (y.take (f + 1)) [pathSubtree v chain M, CT.node S (y.drop f) ks]) : CT.Plan × CT))
    (fun _ => 100 * (U + 1)) (List.range y.length)
    (fun f hf => attIn1_runs hΔ B U f _ chain M S y ks hU hM (by rw [List.mem_range] at hf; omega) hB)
  have hm2 := map_runs (y1 hΔ) B fAttIn2 (toVal (pathSubtree v chain M, (chain, M), CT.node S y ks))
    (fun f : ℕ => ((CT.Plan.att (some (CT.Cut.t2 f)) chain M,
            CT.node S (y.take (f + 1)) [pathSubtree v chain M, CT.node S (y.drop (f + 1)) ks]) : CT.Plan × CT))
    (fun _ => 100 * (U + 1)) (List.range (y.length - 1))
    (fun f hf => attIn2_runs hΔ B U f _ chain M S y ks hU hM (by rw [List.mem_range] at hf; omega) hB)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_range] at hm1 hm2
  have hap1 := append_runs (y1 hΔ) B ks [pathSubtree v chain M]
  have hap2 := append_runs (y1 hΔ) B
    ((CT.Plan.att none chain M, CT.node S y (ks ++ [pathSubtree v chain M])) ::
        (List.range y.length).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t1 f)) chain M,
            CT.node S (y.take (f + 1)) [pathSubtree v chain M, CT.node S (y.drop f) ks]) : CT.Plan × CT)))
    ((List.range (y.length - 1)).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t2 f)) chain M,
            CT.node S (y.take (f + 1)) [pathSubtree v chain M, CT.node S (y.drop (f + 1)) ks]) : CT.Plan × CT)))
  simp only [toVal_cons, toVal_nil] at hap1
  refine Runs.mk (hΔ _ _ Δ_att) ?_
  simp only [toVal_pair, toVal_ct, toVal_plan_att, toVal_none, toVal_cons, toVal_nil] at hm1 hm2 hap2 ⊢
  ev_start
  · apply EvLe.letE
    · ev_run
    · ev_run
  · simp only [List.length_cons, List.length_map, List.length_range]
    have e1 : y.length * (100 * (U + 1)) ≤ U * (100 * (U + 1)) := Nat.mul_le_mul_right _ hc2
    have e2 : (y.length - 1) * (100 * (U + 1)) ≤ U * (100 * (U + 1)) := Nat.mul_le_mul_right _ (by omega)
    have e3 : U * (100 * (U + 1)) + U * (100 * (U + 1)) + 300 * ((U + 1) * (U + 1)) + 200 * U + 300 ≤ 800 * ((U + 1) * (U + 1)) := by nlinarith
    clear hm1 hm2 hap1 hap2 hbr hlenr hr1 hr2 hid
    have hs1 : y.length - 1 ≤ y.length := Nat.sub_le _ _
    have hks10 : 10 * ks.length ≤ 10 * U := by omega
    have hs : 24 * (y.length - 1) ≤ 24 * y.length := by omega
    linarith

theorem attachPlans_runs (U Qc v : ℕ) (N S : Finset ℕ) (y : List ℕ) (ks : List CT) (hNS : N ⊆ S)
    (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hv : v ≤ U)
    (hQc : 1000 * ((U + 1) * ((chainCands S N).length + 1)) ≤ Qc) (hB : 10 * U + 400 < B) :
    Runs Δ' B fAttachPlans [toVal v, toVal N, toVal (CT.node S y ks)] (toVal (attachPlans v N (CT.node S y ks)))
      (2 * (Qc * (U + 1) * (2 * (allChains S N).length + 2))) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have hU5 : 5 ≤ U := by
    have := sz_pos ks; have := sz_pos y; have := sz_pos S
    rw [sz_ct_node] at hU; omega
  have hS : S.card + 1 ≤ U := by have := sz_finset S; omega
  have hid := ids_lt (B := B) (by omega)
  have hac := allChains_runs hΔ B U Qc S N hNS hS hQc hB
  have hatt := flatMap_runs (y1 hΔ) B fAtt (toVal (v, CT.node S y ks))
    (fun cm : List (Finset ℕ) × Finset ℕ =>
      ((CT.Plan.att none cm.1 cm.2, CT.node S y (ks ++ [pathSubtree v cm.1 cm.2])) ::
        (List.range y.length).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t1 f)) cm.1 cm.2,
            CT.node S (y.take (f + 1)) [pathSubtree v cm.1 cm.2, CT.node S (y.drop f) ks]) : CT.Plan × CT))) ++
        (List.range (y.length - 1)).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t2 f)) cm.1 cm.2,
            CT.node S (y.take (f + 1)) [pathSubtree v cm.1 cm.2, CT.node S (y.drop (f + 1)) ks]) : CT.Plan × CT)))
    (fun _ => 800 * ((U + 1) * (U + 1))) (allChains S N)
    (fun cm hcm => by
      obtain ⟨chain, M⟩ := cm
      obtain ⟨h1, h2⟩ := allChains_sub S N _ hcm
      have h3 := allChains_chain_length_le S N _ hcm
      exact att_runs hΔ B U v chain M S y ks hU hM hv
        (fun X hX => le_trans (Finset.card_le_card (h2 X hX)) (by omega)) (by simp only at h3; omega)
        (le_trans (Finset.card_le_card h1) (by omega)) hB)
  have hsum := sum_map_le
    (fun cm : List (Finset ℕ) × Finset ℕ => 800 * ((U + 1) * (U + 1)) + 10 *
      (((CT.Plan.att none cm.1 cm.2, CT.node S y (ks ++ [pathSubtree v cm.1 cm.2])) ::
        (List.range y.length).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t1 f)) cm.1 cm.2,
            CT.node S (y.take (f + 1)) [pathSubtree v cm.1 cm.2, CT.node S (y.drop f) ks]) : CT.Plan × CT))) ++
        (List.range (y.length - 1)).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t2 f)) cm.1 cm.2,
            CT.node S (y.take (f + 1)) [pathSubtree v cm.1 cm.2, CT.node S (y.drop (f + 1)) ks]) : CT.Plan × CT))).length + 20)
    (900 * ((U + 1) * (U + 1))) (allChains S N)
    (fun cm _ => by
      simp only [List.length_append, List.length_cons, List.length_map, List.length_range]
      have : U ≤ (U + 1) * (U + 1) := by nlinarith
      omega)
  have hshow : attachPlans v N (CT.node S y ks) = (allChains S N).flatMap
    (fun cm : List (Finset ℕ) × Finset ℕ =>
      ((CT.Plan.att none cm.1 cm.2, CT.node S y (ks ++ [pathSubtree v cm.1 cm.2])) ::
        (List.range y.length).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t1 f)) cm.1 cm.2,
            CT.node S (y.take (f + 1)) [pathSubtree v cm.1 cm.2, CT.node S (y.drop f) ks]) : CT.Plan × CT))) ++
        (List.range (y.length - 1)).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t2 f)) cm.1 cm.2,
            CT.node S (y.take (f + 1)) [pathSubtree v cm.1 cm.2, CT.node S (y.drop (f + 1)) ks]) : CT.Plan × CT))) := rfl
  rw [hshow]
  refine Runs.mk (hΔ _ _ Δ_attachPlans) ?_
  simp only [toVal_pair, toVal_ct] at hatt ⊢
  ev_start
  · apply EvLe.letE
    · ev_run
    · ev_run
  · set A := (allChains S N).length with hA
    have e : Qc * (U + 1) * (2 * A + 2) ≥ 2000 * ((U + 1) * (U + 1)) * (A + 1) := by
      have h1 : 1000 * (U + 1) ≤ Qc := by nlinarith
      have h2 : 1000 * (U + 1) * (U + 1) ≤ Qc * (U + 1) := Nat.mul_le_mul_right _ h1
      nlinarith
    have e2 : A * (900 * ((U + 1) * (U + 1))) + 100 ≤ 2000 * ((U + 1) * (U + 1)) * (A + 1) := by nlinarith
    omega

end proofs
end E3B
end Lax117284Proofs.Treewidth.Fun
