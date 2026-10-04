import Lax117284Proofs.Treewidth.Chars.Extract
import Lax117284Proofs.Treewidth.Chars.CountRuns
import Lax117284Proofs.Treewidth.Size.Plans

/-! ### `Lax117284Proofs.Treewidth.Size.RealA` -/

section
/-!
# Size bounds (WP P1), part 7: sizes of real trees (1): the measure `AR.nsz`

`AR.nsz` counts the nodes of `AR.toRT`: `chsz` of the chains (a chain node plus the size of its junk subtrees; an empty chain
still yields one node) plus the `w` of the kids.

* `toRT_size`      : `(AR.toRT r).size = r.nsz`;
* `analyze_w_le`   : `(analyze B t).w ≤ t.size` (so `(analyze B t).toRT.size ≤ t.size`).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem sizeL_eq' : ∀ ks : List RT, RT.sizeL ks = (ks.map RT.size).sum
  | [] => rfl
  | k :: ks => by simp [RT.sizeL, sizeL_eq' ks]

theorem size_node' (X : Finset ℕ) (ks : List RT) : (RT.node X ks).size = 1 + (ks.map RT.size).sum := by
  simp [RT.size, sizeL_eq']

/-- Size of the junk of a chain node. -/
def CNode.jsz (n : CNode) : ℕ := (n.junk.map RT.size).sum

/-- Nodes contributed by a chain: one per chain node (at least one), plus the junk. -/
def chsz (ns : List CNode) : ℕ := max 1 ns.length + (ns.map CNode.jsz).sum

mutual
/-- The number of nodes of `toRT`. -/
def AR.nsz : AR → ℕ
  | .run _ c ks => chsz c + AR.nszL ks
def AR.nszL : List AR → ℕ
  | [] => 0
  | k :: ks => AR.nsz k + AR.nszL ks
end

theorem AR.nszL_eq : ∀ ks : List AR, AR.nszL ks = (ks.map AR.nsz).sum
  | [] => rfl
  | k :: ks => by simp [AR.nszL, AR.nszL_eq ks]

theorem chainToRT_size : ∀ (c : List CNode) (ks : List RT),
    (AR.chainToRT c ks).size = chsz c + (ks.map RT.size).sum
  | [], ks => by simp [AR.chainToRT, size_node', chsz]
  | [n], ks => by
    simp [AR.chainToRT, size_node', chsz, CNode.jsz, List.sum_append]
    omega
  | n :: m :: r, ks => by
    have ih := chainToRT_size (m :: r) ks
    simp only [AR.chainToRT, size_node', List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, ih] 
    simp only [chsz, List.length_cons, List.map_cons, List.sum_cons, CNode.jsz]
    omega

mutual
theorem toRT_size_rec : ∀ r : AR, r.toRT.size = r.nsz
  | .run S c ks => by
    rw [AR.toRT_run, chainToRT_size, AR.nsz, ← AR.toRTL_eq, toRTL_size_rec ks]
theorem toRTL_size_rec : ∀ ks : List AR, ((AR.toRTL ks).map RT.size).sum = AR.nszL ks
  | [] => rfl
  | k :: ks => by
    simp only [AR.toRTL, List.map_cons, List.sum_cons, AR.nszL, toRT_size_rec k, toRTL_size_rec ks]
end

theorem toRT_size_pair : (type_of% @toRT_size_rec) ∧ (type_of% @toRTL_size_rec) :=
  ⟨@toRT_size_rec, @toRTL_size_rec⟩

theorem toRT_size : type_of% @toRT_size_rec := toRT_size_pair.1

theorem sum_filter_split {α : Type} (l : List α) (p : α → Bool) (f : α → ℕ) :
    ((l.filter p).map f).sum + ((l.filter (fun a => !p a)).map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a = true
    · simp [List.filter_cons, h, ih.symm]; omega
    · simp only [Bool.not_eq_true] at h
      simp [List.filter_cons, h, ih.symm]; omega

theorem sortAR_nsz (S : Finset ℕ) (l : List AR) : ((sortAR S l).map AR.nsz).sum = (l.map AR.nsz).sum := by
  unfold sortAR
  exact ((List.mergeSort_perm _ _).map _).sum_eq

theorem analyzeNode_gen (S : Finset ℕ) (X : Finset ℕ) (kids : List (RT × AR)) (pr : RT × AR → Bool)
    (hk : ∀ p ∈ kids, p.2.nsz ≤ p.1.size) :
    (match (kids.filter (fun p => !pr p)).map Prod.snd with
      | [] => AR.run S [⟨X, (kids.filter pr).map Prod.fst⟩] []
      | [k] => if k.S = S then AR.run S (⟨X, (kids.filter pr).map Prod.fst⟩ :: k.chain) k.kids
               else AR.run S [⟨X, (kids.filter pr).map Prod.fst⟩] [k]
      | ks => AR.run S [⟨X, (kids.filter pr).map Prod.fst⟩] (sortAR S ks)).nsz ≤
      1 + (kids.map (fun p => p.1.size)).sum := by
  have hsplit := sum_filter_split kids pr (fun p => p.1.size)
  have hQ : (((kids.filter (fun p => !pr p)).map Prod.snd).map AR.nsz).sum ≤
      ((kids.filter (fun p => !pr p)).map (fun p => p.1.size)).sum := by
    rw [List.map_map]
    apply List.sum_le_sum
    intro p hp
    exact hk p (List.mem_of_mem_filter hp)
  have hJ : ((((kids.filter pr).map Prod.fst).map RT.size).sum) =
      ((kids.filter pr).map (fun p => p.1.size)).sum := by
    rw [List.map_map]; rfl
  split
  · rename_i hc
    rw [hc] at hQ
    simp only [AR.nsz, chsz, CNode.jsz, AR.nszL, List.length_singleton, List.map_singleton, List.sum_singleton,
      List.sum_nil, List.map_nil] at *
    omega
  · rename_i k hc
    rw [hc] at hQ
    simp only [List.map_singleton, List.sum_singleton] at hQ
    rcases k with ⟨S', c, ks'⟩
    simp only [AR.S, AR.chain, AR.kids]
    by_cases hS : S' = S
    · simp only [hS, ↓reduceIte]
      simp only [AR.nsz, chsz, CNode.jsz, List.length_cons, List.map_cons, List.sum_cons] at *
      omega
    · simp only [hS, ↓reduceIte]
      simp only [AR.nsz, chsz, CNode.jsz, AR.nszL, List.length_singleton, List.map_singleton,
        List.sum_singleton, add_zero] at *
      omega
  · rename_i hne hne1
    simp only [AR.nsz, chsz, CNode.jsz, List.length_singleton, List.map_singleton, List.sum_singleton,
      AR.nszL_eq, sortAR_nsz] at *
    omega

theorem analyze_nsz_le (B : Finset ℕ) : ∀ t : RT, (analyze B t).nsz ≤ t.size := by
  intro t
  induction t using RT.ind with
  | h X ks ih =>
    rw [analyze_node, size_node']
    have hk : ∀ p ∈ ks.map (fun k => (k, analyze B k)), p.2.nsz ≤ p.1.size := by
      intro p hp
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
      exact ih k hk
    have hks : (ks.map RT.size).sum = ((ks.map (fun k => (k, analyze B k))).map (fun p => p.1.size)).sum := by
      rw [List.map_map]; rfl
    rw [hks]
    exact analyzeNode_gen (X ∩ B) X _ (fun p => p.2.isLeaf && decide (p.2.S ⊆ X ∩ B)) hk

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Size.RealB` -/

section
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
theorem processRun_nsz_le_rec (v : ℕ) (pre : Option Cut) : ∀ (wp : WPlan) (r : AR),
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
      have h3 := applyKids_nszL_le_rec v ps ks
      rcases pre with _ | c'
      · simp only [Option.isSome_none, Bool.false_eq_true, if_false]
        have h1 := chsz_addV_le v 0 none ns
        omega
      · simp only [Option.isSome_some, if_true]
        refine le_trans (Nat.add_le_add_right (chsz_addV_le _ _ _ _) _) ?_
        have h1 := chsz_cutAt_le (typical (ns.map fun n : CNode => n.bag.card)) (witnesses (ns.map fun n : CNode => n.bag.card)) c' ns
        omega
theorem applyKids_nszL_le_rec (v : ℕ) : ∀ (ps : List (Option WPlan)) (ks : List AR),
    AR.nszL (applyKids v ps ks) ≤ AR.nszL ks + wcostL ps
  | [], ks => by simp [applyKids, wcostL]
  | _ :: _, [] => by simp [applyKids, AR.nszL]
  | p :: ps, k :: ks => by
    have h1 := applyOpt_nsz_le_rec v p k
    have h2 := applyKids_nszL_le_rec v ps ks
    simp only [applyKids, AR.nszL, wcostL]
    omega
theorem applyOpt_nsz_le_rec (v : ℕ) : ∀ (p : Option WPlan) (k : AR), (applyOpt v p k).nsz ≤ k.nsz + wcostO p
  | none, k => by simp [applyOpt, wcostO]
  | some p, k => by
    have := processRun_nsz_le_rec v none p k
    simpa [applyOpt, wcostO] using this
end

theorem processRun_nsz_le_pair : (type_of% @processRun_nsz_le_rec) ∧ (type_of% @applyKids_nszL_le_rec) ∧ (type_of% @applyOpt_nsz_le_rec) :=
  ⟨@processRun_nsz_le_rec, @applyKids_nszL_le_rec, @applyOpt_nsz_le_rec⟩

theorem processRun_nsz_le : type_of% @processRun_nsz_le_rec := processRun_nsz_le_pair.1

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

end

/-! ### `Lax117284Proofs.Treewidth.Size.RealC` -/

section
/-!
# Size bounds (WP P1), part 9: the cost of the plans of `introPlans`

For a run tree `T` all of whose labels have at most `b` vertices, every plan `pl` of `introPlans v N T` satisfies
`planCost pl ≤ leaves T + b + 3` (`planCost_le_of_mem_introPlans`): a region plan has at most `leaves T` `endAt`'s
(`wcost_le_leaves`) and a new branch has a chain of at most `|S| + 1` sets (`allChains_chain_length_le`).
`leaves` and the labels are invariant under `DomC` (`DomC.leaves_eq`, `DomC.LB`).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

namespace CT

/-! ## labels -/

mutual
/-- Every label has at most `b` vertices. -/
def LB (b : ℕ) : CT → Prop
  | node S _ ks => S.card ≤ b ∧ LBL b ks
def LBL (b : ℕ) : List CT → Prop
  | [] => True
  | k :: ks => LB b k ∧ LBL b ks
end

theorem LBL_iff {b : ℕ} : ∀ {ks : List CT}, LBL b ks ↔ ∀ k ∈ ks, LB b k
  | [] => by simp [LBL]
  | k :: ks => by simp [LBL, LBL_iff (ks := ks)]

theorem LB.kids {b : ℕ} {S : Finset ℕ} {y : List ℕ} {ks : List CT} (h : LB b (node S y ks)) :
    ∀ k ∈ ks, LB b k := LBL_iff.1 h.2

theorem LB.of_good {B : Finset ℕ} : ∀ {t : CT}, Good B t → LB B.card t := by
  intro t
  induction t using CT.ind with
  | h S y ks ih =>
    intro hg
    exact ⟨Finset.card_le_card hg.label_sub, LBL_iff.2 fun k hk => ih k hk (hg.kids k hk)⟩

/-! ## `DomC` preserves shape -/

mutual
theorem DomC.leaves_eq_rec : ∀ {a b : CT}, DomC a b → leaves a = leaves b
  | node S y ks, node S' y' ks', h => by
    have hl := DomCL.length_eq h.2.2
    have hs := DomCL.leavesL_eq_rec h.2.2
    simp only [leaves]
    have : ks.isEmpty = ks'.isEmpty := by
      cases ks <;> cases ks' <;> simp_all
    rw [this, hs]
theorem DomCL.leavesL_eq_rec : ∀ {a b : List CT}, DomCL a b → leavesL a = leavesL b
  | [], [], _ => rfl
  | k :: ks, k' :: ks', h => by simp only [leavesL, DomC.leaves_eq_rec h.1, DomCL.leavesL_eq_rec h.2]
end

theorem DomC.leaves_eq_pair : (type_of% @DomC.leaves_eq_rec) ∧ (type_of% @DomCL.leavesL_eq_rec) :=
  ⟨@DomC.leaves_eq_rec, @DomCL.leavesL_eq_rec⟩

theorem DomC.leaves_eq : type_of% @DomC.leaves_eq_rec := DomC.leaves_eq_pair.1

mutual
theorem DomC.LB_iff_rec : ∀ {a c : CT} {b : ℕ}, DomC a c → (LB b a ↔ LB b c)
  | node S y ks, node S' y' ks', b, h => by
    simp only [LB]
    rw [h.1, DomCL.LBL_iff_rec h.2.2]
theorem DomCL.LBL_iff_rec : ∀ {a c : List CT} {b : ℕ}, DomCL a c → (LBL b a ↔ LBL b c)
  | [], [], _, _ => Iff.rfl
  | k :: ks, k' :: ks', b, h => by
    simp only [LBL]
    rw [DomC.LB_iff_rec h.1, DomCL.LBL_iff_rec h.2]
end

theorem DomC.LB_iff_pair : (type_of% @DomC.LB_iff_rec) ∧ (type_of% @DomCL.LBL_iff_rec) :=
  ⟨@DomC.LB_iff_rec, @DomCL.LBL_iff_rec⟩

theorem DomC.LB_iff : type_of% @DomC.LB_iff_rec := DomC.LB_iff_pair.1

/-! ## leaves -/

theorem leaves_le_of_mem {S : Finset ℕ} {y : List ℕ} {ks : List CT} {k : CT} (hk : k ∈ ks) :
    leaves k ≤ leaves (node S y ks) := by
  have hne : ks ≠ [] := List.ne_nil_of_mem hk
  rw [leaves_node_ne_nil _ _ _ hne]
  have : ∀ ks' : List CT, k ∈ ks' → leaves k ≤ leavesL ks' := by
    intro ks'
    induction ks' with
    | nil => simp
    | cons a l ih =>
      intro h
      simp only [leavesL]
      rcases List.mem_cons.1 h with rfl | h
      · omega
      · have := ih h; omega
  exact this ks hk

theorem leavesL_le_leaves (S : Finset ℕ) (y : List ℕ) (ks : List CT) : leavesL ks ≤ leaves (node S y ks) := by
  by_cases h : ks = []
  · subst h; simp [leavesL]
  · rw [leaves_node_ne_nil _ _ _ h]

/-- **A well-formed characteristic has at most `|B| + 1` leaf runs.** -/
theorem Wf.leaves_le {B : Finset ℕ} {kmax : ℕ} {t : CT} (h : Wf B kmax t) : leaves t ≤ B.card + 1 := by
  by_cases hk : t.kids = []
  · have : leaves t = 1 := by
      cases t with
      | node S y ks => simp only [kids] at hk; subst hk; exact leaves_node_nil _ _
    omega
  · have := leaves_le_of_kids_ne_nil (B := B) t h.good h.conn hk
    have h2 : (t.verts \ t.S).card ≤ B.card := by
      rw [← h.verts_eq]; exact Finset.card_le_card Finset.sdiff_subset
    omega

/-! ## `wcost ≤ leaves` -/

mutual
theorem wcost_le_leaves_rec (v : ℕ) : ∀ (lo : ℕ) (t : CT), ∀ x ∈ winPlans v lo t, wcost x.1 ≤ leaves t
  | lo, node S y ks, x, hx => by
    simp only [winPlans, List.mem_append, List.mem_map] at hx
    rcases hx with (⟨f, _, rfl⟩ | ⟨f, _, rfl⟩) | ⟨combo, hcombo, rfl⟩
    · simp only [wcost]; exact leaves_pos _
    · simp only [wcost]; exact leaves_pos _
    · simp only [wcost]
      exact le_trans (kidChoices_wcost_le_rec v ks combo hcombo) (leavesL_le_leaves S y ks)
theorem kidChoices_wcost_le_rec (v : ℕ) : ∀ (ks : List CT), ∀ combo ∈ kidChoices v ks,
    wcostL (combo.map (·.1)) ≤ leavesL ks
  | [], combo, h => by
    simp only [kidChoices, List.mem_singleton] at h; subst h; simp [wcostL, leavesL]
  | k :: ks, combo, h => by
    simp only [kidChoices, List.mem_flatMap, List.mem_map] at h
    obtain ⟨o, ho, combo', hcombo', rfl⟩ := h
    have h1 := kidChoices_wcost_le_rec v ks combo' hcombo'
    have h2 : wcostO o.1 ≤ leaves k := by
      rcases List.mem_cons.1 ho with rfl | ho
      · simp [wcostO]
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
        simpa [wcostO] using wcost_le_leaves_rec v 0 k p hp
    simp only [List.map_cons, wcostL, leavesL]
    omega
end

theorem wcost_le_leaves_pair : (type_of% @wcost_le_leaves_rec) ∧ (type_of% @kidChoices_wcost_le_rec) :=
  ⟨@wcost_le_leaves_rec, @kidChoices_wcost_le_rec⟩

theorem wcost_le_leaves : type_of% @wcost_le_leaves_rec := wcost_le_leaves_pair.1

theorem chainsGo_chain_length_le (cands : List (Finset ℕ)) : ∀ (fuel : ℕ) (bound : Finset ℕ)
    (chain : List (Finset ℕ)), ∀ x ∈ chainsGo cands fuel bound chain, x.1.length ≤ chain.length + fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro bound chain x hx
    simp only [chainsGo, List.mem_map] at hx
    obtain ⟨M, _, rfl⟩ := hx
    simp
  | succ f ih =>
    intro bound chain x hx
    simp only [chainsGo, List.mem_append, List.mem_map, List.mem_flatMap] at hx
    rcases hx with ⟨M, _, rfl⟩ | ⟨X, _, hx⟩
    · simp
    · have := ih X (chain ++ [X]) x hx
      simp only [List.length_append, List.length_singleton] at this
      omega

theorem allChains_chain_length_le (S N : Finset ℕ) : ∀ x ∈ allChains S N, x.1.length ≤ S.card + 1 := by
  intro x hx
  unfold allChains at hx
  have := chainsGo_chain_length_le _ _ _ _ x hx
  simpa using this

theorem planCost_wtop_le (v : ℕ) (t : CT) : ∀ x ∈ wtopPlans v t, planCost x.1 ≤ leaves t + 1 := by
  intro x hx
  cases t with
  | node S y ks =>
    simp only [wtopPlans, List.mem_append, List.mem_map, List.mem_flatMap] at hx
    rcases hx with (⟨p, hp, rfl⟩ | ⟨f, _, p, hp, rfl⟩) | ⟨f, _, p, hp, rfl⟩
    · have := wcost_le_leaves v 0 _ p hp
      simp only [planCost]; simp; omega
    · have := wcost_le_leaves v f _ p hp
      simp only [planCost]; simp; omega
    · have := wcost_le_leaves v (f + 1) _ p hp
      simp only [planCost]; simp; omega

theorem planCost_att_le (v : ℕ) (N : Finset ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    ∀ x ∈ attachPlans v N (node S y ks), planCost x.1 ≤ S.card + 3 := by
  intro x hx
  simp only [attachPlans, List.mem_flatMap, List.mem_cons, List.mem_append, List.mem_map] at hx
  obtain ⟨⟨chain, M⟩, hcm, hx⟩ := hx
  have hc := allChains_chain_length_le S N _ hcm
  simp only at hc
  rcases hx with (rfl | ⟨f, _, rfl⟩) | ⟨f, _, rfl⟩ <;> simp only [planCost] <;> simp <;> omega

theorem introKids_planCost_le (v : ℕ) (N S : Finset ℕ) (y : List ℕ) (U : ℕ) :
    ∀ (ks pre : List CT), (∀ k ∈ ks, ∀ x ∈ introPlans v N k, planCost x.2.1 ≤ U) →
      ∀ x ∈ introKids v N S y pre ks, planCost x.2.1 ≤ U
  | [], _, _, x, hx => by simp [introKids] at hx
  | k :: post, pre, h, x, hx => by
    simp only [introKids, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨r, hr, rfl⟩ | hx
    · exact h k (by simp) r hr
    · exact introKids_planCost_le v N S y U post (pre ++ [k]) (fun k' hk' => h k' (List.mem_cons_of_mem _ hk')) x hx

/-- **The plans of `introPlans` are cheap.** -/
theorem planCost_le_of_mem_introPlans (v : ℕ) (N : Finset ℕ) {b : ℕ} :
    ∀ (T : CT), LB b T → ∀ x ∈ introPlans v N T, planCost x.2.1 ≤ leaves T + b + 3 := by
  intro T
  induction T using CT.ind with
  | h S y ks ih =>
    intro hl x hx
    simp only [introPlans, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    rcases hx with (⟨p, ⟨hp, -⟩, rfl⟩ | hx) | hx
    · have := planCost_wtop_le v (node S y ks) p hp
      simp only; omega
    · split_ifs at hx
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        have := planCost_att_le v N S y ks p hp
        have := hl.1
        simp only; omega
      · simp at hx
    · refine introKids_planCost_le v N S y _ ks [] ?_ x hx
      intro k hk x' hx'
      have := ih k hk (hl.kids k hk) x' hx'
      have := leaves_le_of_mem (S := S) (y := y) hk
      omega

end CT

end Lax117284Proofs.Treewidth.Chars

end
