import Lax117284Proofs.Treewidth.Size.RealA
import Lax117284Proofs.Treewidth.Chars.CountRuns

/-!
# Size bounds (WP P1), part 8: sizes of real trees (2): `applyPlan`

`planCost` bounds the growth of `AR.nsz` (= size of the reassembled tree) under `applyRun`:
a first-type cut duplicates one chain node (`dupAfter`), a region plan adds one node per `endAt`, a new branch adds its
`branchRT` (`chain.length + 1` nodes).  For a plan of `introPlans v N T` the number of `endAt`'s is at most the number of
leaf runs of `T` (`wcost_le_leaves`: the `endAt`'s of a plan form an antichain of runs).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## chains -/

theorem chsz_dupAfter_le (i : ℕ) (ns : List CNode) : chsz (dupAfter i ns) ≤ chsz ns + 1 := by
  unfold dupAfter
  split
  · omega
  · rename_i n hn
    have h1 : (ns.take (i + 1) ++ [(⟨n.bag, []⟩ : CNode)] ++ ns.drop (i + 1)).length = ns.length + 1 := by
      simp only [List.length_append, List.length_take, List.length_singleton, List.length_drop]
      have : i + 1 ≤ ns.length := by
        have := (List.getElem?_eq_some_iff.1 hn).1; omega
      omega
    have h2 : ((ns.take (i + 1) ++ [(⟨n.bag, []⟩ : CNode)] ++ ns.drop (i + 1)).map CNode.jsz).sum =
        (ns.map CNode.jsz).sum := by
      have := congrArg (fun l => (l.map CNode.jsz).sum) (List.take_append_drop (i + 1) ns)
      simp only [List.map_append, List.sum_append] at this ⊢
      simp [CNode.jsz]
    unfold chsz
    rw [h1, h2]
    omega

theorem sum_jsz_mapIdx_le (g : ℕ → ℕ) : ∀ (ns : List CNode) (f : ℕ → CNode → CNode),
    (∀ i n, (f i n).jsz ≤ n.jsz + g i) →
    ((ns.mapIdx f).map CNode.jsz).sum ≤ (ns.map CNode.jsz).sum + ∑ i ∈ Finset.range ns.length, g i
  | [], f, _ => by simp
  | n :: r, f, h => by
    have ih := sum_jsz_mapIdx_le (fun i => g (i + 1)) r (fun i => f (i + 1)) (fun i m => h (i + 1) m)
    have h0 := h 0 n
    simp only [List.mapIdx_cons, List.map_cons, List.sum_cons, List.length_cons]
    rw [Finset.sum_range_succ']
    omega

theorem chsz_addV_le (v s : ℕ) (e : Option ℕ) (ns : List CNode) : chsz (addV v s e ns) ≤ chsz ns := by
  unfold addV chsz
  rw [List.length_mapIdx]
  refine Nat.add_le_add_left ((sum_jsz_mapIdx_le (fun _ => 0) ns _ ?_).trans (by simp)) _
  intro i n
  split_ifs <;> simp [CNode.jsz]

theorem chsz_addJunk_le (x : ℕ) (br : RT) (ns : List CNode) : chsz (addJunk x br ns) ≤ chsz ns + br.size := by
  unfold addJunk chsz
  rw [List.length_mapIdx]
  have := sum_jsz_mapIdx_le (fun i => if i = x then br.size else 0) ns
    (fun i n => if i = x then ⟨n.bag, n.junk ++ [br]⟩ else n)
    (by
      intro i n
      split_ifs <;> simp [CNode.jsz, List.sum_append])
  have h2 : ∑ i ∈ Finset.range ns.length, (if i = x then br.size else 0) ≤ br.size := by
    rw [Finset.sum_ite_eq']
    split_ifs <;> omega
  omega

theorem chsz_cutAt_le (y w : List ℕ) (c : Cut) (ns : List CNode) : chsz (cutAt y w c ns).1 ≤ chsz ns + 1 := by
  cases c with
  | t1 f => exact chsz_dupAfter_le _ _
  | t2 f => simp [cutAt]

/-! ## region plans -/

mutual
/-- The number of `endAt`'s of a region plan. -/
def wcost : WPlan → ℕ
  | .endAt _ => 1
  | .whole ps => wcostL ps
def wcostL : List (Option WPlan) → ℕ
  | [] => 0
  | p :: ps => wcostO p + wcostL ps
def wcostO : Option WPlan → ℕ
  | none => 0
  | some p => wcost p
end

mutual
theorem processRun_nsz_le (v : ℕ) (pre : Option Cut) : ∀ (wp : WPlan) (r : AR),
    (processRun v pre wp r).nsz ≤ r.nsz + (if pre.isSome then 1 else 0) + wcost wp
  | wp, .run S ns ks => by
    cases wp with
    | endAt c =>
      simp only [processRun, AR.nsz, wcost]
      rcases pre with _ | c'
      · simp only [Option.isSome_none, Bool.false_eq_true, if_false]
        have h1 := chsz_addV_le v 0 (some (cutAt (typical (ns.map fun n : CNode => n.bag.card))
          (witnesses (ns.map fun n : CNode => n.bag.card)) c ns).2) (cutAt (typical (ns.map fun n : CNode => n.bag.card))
          (witnesses (ns.map fun n : CNode => n.bag.card)) c ns).1
        have h2 := chsz_cutAt_le (typical (ns.map fun n : CNode => n.bag.card)) (witnesses (ns.map fun n : CNode => n.bag.card)) c ns
        omega
      · simp only [Option.isSome_some, if_true]
        refine le_trans (Nat.add_le_add_right (chsz_addV_le _ _ _ _) _) ?_
        have h1 := chsz_cutAt_le (typical (ns.map fun n : CNode => n.bag.card)) (witnesses (ns.map fun n : CNode => n.bag.card)) c' 
          (cutAt (typical (ns.map fun n : CNode => n.bag.card)) (witnesses (ns.map fun n : CNode => n.bag.card)) c ns).1
        have h2 := chsz_cutAt_le (typical (ns.map fun n : CNode => n.bag.card)) (witnesses (ns.map fun n : CNode => n.bag.card)) c ns
        omega
    | whole ps =>
      simp only [processRun, AR.nsz, wcost]
      have h3 := applyKids_nszL_le v ps ks
      rcases pre with _ | c'
      · simp only [Option.isSome_none, Bool.false_eq_true, if_false]
        have h1 := chsz_addV_le v 0 none ns
        omega
      · simp only [Option.isSome_some, if_true]
        refine le_trans (Nat.add_le_add_right (chsz_addV_le _ _ _ _) _) ?_
        have h1 := chsz_cutAt_le (typical (ns.map fun n : CNode => n.bag.card)) (witnesses (ns.map fun n : CNode => n.bag.card)) c' ns
        omega
theorem applyKids_nszL_le (v : ℕ) : ∀ (ps : List (Option WPlan)) (ks : List AR),
    AR.nszL (applyKids v ps ks) ≤ AR.nszL ks + wcostL ps
  | [], ks => by simp [applyKids, wcostL]
  | _ :: _, [] => by simp [applyKids, AR.nszL]
  | p :: ps, k :: ks => by
    have h1 := applyOpt_nsz_le v p k
    have h2 := applyKids_nszL_le v ps ks
    simp only [applyKids, AR.nszL, wcostL]
    omega
theorem applyOpt_nsz_le (v : ℕ) : ∀ (p : Option WPlan) (k : AR), (applyOpt v p k).nsz ≤ k.nsz + wcostO p
  | none, k => by simp [applyOpt, wcostO]
  | some p, k => by
    have := processRun_nsz_le v none p k
    simpa [applyOpt, wcostO] using this
end

/-! ## plans -/

/-- The growth of the reassembled tree under a plan. -/
def planCost : Plan → ℕ
  | .att c chain _ => (if c.isSome then 1 else 0) + chain.length + 1
  | .top pre w => (if pre.isSome then 1 else 0) + wcost w

theorem branchRT_size (v : ℕ) (chain : List (Finset ℕ)) (M : Finset ℕ) :
    (branchRT v chain M).size = chain.length + 1 := by
  induction chain with
  | nil => simp [branchRT, size_node']
  | cons X chain ih =>
    have : branchRT v (X :: chain) M = RT.node X [branchRT v chain M] := by simp [branchRT]
    rw [this, size_node']
    simp [ih]
    omega

theorem applyAt_nsz_le (v : ℕ) : ∀ (p : Plan) (r : AR), (applyAt v p r).nsz ≤ r.nsz + planCost p
  | .att c chain M, .run S ns ks => by
    simp only [applyAt, AR.nsz, planCost]
    refine le_trans (Nat.add_le_add_right (chsz_addJunk_le _ _ _) _) ?_
    rw [branchRT_size]
    rcases c with _ | ct
    · simp only [Option.isSome_none, Bool.false_eq_true, if_false]
      omega
    · simp only [Option.isSome_some, if_true]
      have := chsz_cutAt_le (typical (ns.map fun n : CNode => n.bag.card))
        (witnesses (ns.map fun n : CNode => n.bag.card)) ct ns
      omega
  | .top pre w, r => by
    simpa [applyAt, planCost, add_assoc] using processRun_nsz_le v pre w r

theorem modifyNth_nszL_le {f : AR → AR} {d : ℕ} (hf : ∀ r, (f r).nsz ≤ r.nsz + d) :
    ∀ (i : ℕ) (ks : List AR), AR.nszL (modifyNth f i ks) ≤ AR.nszL ks + d
  | _, [] => by simp [modifyNth, AR.nszL]
  | 0, k :: ks => by
    have := hf k
    simp only [modifyNth, AR.nszL]; omega
  | i + 1, k :: ks => by
    have := modifyNth_nszL_le hf i ks
    simp only [modifyNth, AR.nszL]; omega

theorem applyRun_nsz_le (v : ℕ) (p : Plan) : ∀ (path : List ℕ) (r : AR),
    (applyRun v p path r).nsz ≤ r.nsz + planCost p
  | [], r => by simpa [applyRun] using applyAt_nsz_le v p r
  | i :: rest, .run S ns ks => by
    have := modifyNth_nszL_le (f := applyRun v p rest) (d := planCost p)
      (fun r => applyRun_nsz_le v p rest r) i ks
    simp only [applyRun, AR.nsz]
    omega

/-- **`applyPlan` grows the tree by at most `planCost`.** -/
theorem applyPlan_size_le (v : ℕ) (N B : Finset ℕ) (path : List ℕ) (p : Plan) (t : RT) :
    (applyPlan v N B path p t).size ≤ t.size + planCost p := by
  unfold applyPlan
  rw [toRT_size]
  have h1 := applyRun_nsz_le v p path (analyze B t)
  have h2 := analyze_nsz_le B t
  omega

end Lax117284Proofs.Treewidth.Chars
