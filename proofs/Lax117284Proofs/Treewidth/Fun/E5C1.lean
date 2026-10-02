import Lax117284Proofs.Treewidth.Fun.E5B

/-!
# WP E5 (layer C1): chain surgery — `dupAfter`, `cutAt`, `addV`, `addJunk`, `branchRT`

Ids `470 …`:

| id | function | arguments |
|---|---|---|
| 470 `fDupAfter` | `dupAfter` | `[i, ns]` |
| 471 `fCutAt` | `cutAt` | `[y, w, c, ns]` |
| 472 `fInRng` | `decide (s ≤ i) && e.elim true (fun e => decide (i ≤ e))` | `[s, e, i]` |
| 473 `fAddVAux` | `addV` with a running index (`addVL`) | `[v, s, e, i, ns]` |
| 474 `fAddV` | `addV` | `[v, s, e, ns]` |
| 475 `fAddJunkAux` | `addJunk` with a running index (`addJunkL`) | `[x, br, i, ns]` |
| 476 `fAddJunk` | `addJunk` | `[x, br, ns]` |
| 477 `fBranchRT` | `branchRT` | `[v, chain, M]` |
| 478 `fNxt` | `l.getD (f + 1) 0`, computed by `drop` (no arithmetic on `f`) | `[f, l]` |

The Lean `mapIdx` is replaced by the recursion with a running index (`addVL`, `addJunkL`; `addV_eq`, `addJunk_eq`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E5C1

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5 E5A

abbrev fDupAfter : ℕ := 470
abbrev fCutAt : ℕ := 471
abbrev fInRng : ℕ := 472
abbrev fAddVAux : ℕ := 473
abbrev fAddV : ℕ := 474
abbrev fAddJunkAux : ℕ := 475
abbrev fAddJunk : ℕ := 476
abbrev fBranchRT : ℕ := 477
abbrev fNxt : ℕ := 478

/-- `a ≤ b` as a term (`1 - (b < a)`) -/
abbrev leT (a b : Tm) : Tm := .sub (.lit 1) (.lt b a)

/-! ## the Lean side: `addV`, `addJunk` with a running index -/

/-- the test of `addV` -/
abbrev inRng (s : ℕ) (e : Option ℕ) (i : ℕ) : Bool := decide (s ≤ i) && e.elim true (fun e => decide (i ≤ e))

def addVL (v s : ℕ) (e : Option ℕ) : ℕ → List CNode → List CNode
  | _, [] => []
  | i, n :: ns => (if inRng s e i then (⟨insert v n.bag, n.junk⟩ : CNode) else n) :: addVL v s e (i + 1) ns

def addJunkL (x : ℕ) (br : RT) : ℕ → List CNode → List CNode
  | _, [] => []
  | i, n :: ns => (if i = x then (⟨n.bag, n.junk ++ [br]⟩ : CNode) else n) :: addJunkL x br (i + 1) ns

theorem mapIdx_addVL (v s : ℕ) (e : Option ℕ) : ∀ (ns : List CNode) (i : ℕ),
    ns.mapIdx (fun j n => if inRng s e (i + j) then (⟨insert v n.bag, n.junk⟩ : CNode) else n) = addVL v s e i ns
  | [], i => by simp [addVL]
  | n :: ns, i => by
    rw [List.mapIdx_cons, addVL]
    simp only [Nat.add_zero]
    congr 1
    have := mapIdx_addVL v s e ns (i + 1)
    rw [← this]
    congr 1
    funext j m
    rw [show i + (j + 1) = i + 1 + j by omega]

theorem addV_eq (v s : ℕ) (e : Option ℕ) (ns : List CNode) : addV v s e ns = addVL v s e 0 ns := by
  have := mapIdx_addVL v s e ns 0
  simp only [Nat.zero_add] at this
  exact this

theorem mapIdx_addJunkL (x : ℕ) (br : RT) : ∀ (ns : List CNode) (i : ℕ),
    ns.mapIdx (fun j n => if i + j = x then (⟨n.bag, n.junk ++ [br]⟩ : CNode) else n) = addJunkL x br i ns
  | [], i => by simp [addJunkL]
  | n :: ns, i => by
    rw [List.mapIdx_cons, addJunkL]
    simp only [Nat.add_zero]
    congr 1
    have := mapIdx_addJunkL x br ns (i + 1)
    rw [← this]
    congr 1
    funext j m
    rw [show i + (j + 1) = i + 1 + j by omega]

theorem addJunk_eq (x : ℕ) (br : RT) (ns : List CNode) : addJunk x br ns = addJunkL x br 0 ns := by
  have := mapIdx_addJunkL x br ns 0
  simp only [Nat.zero_add] at this
  exact this

/-! ## the terms -/

def dupAfterTm : Tm :=
  .ite (.lt (V 0) (.call fLength [V 1]))
    (.call fAppend
      [.call fAppend [.call fTake [.add (V 0) (.lit 1), V 1],
        .cons (.cons (.fst (.call fNthD [V 1, V 0, .lit 0])) (.lit 0)) (.lit 0)],
       .call fDrop [.add (V 0) (.lit 1), V 1]])
    (V 1)

/-- `l.getD (f + 1) 0` without computing `f + 1`; `[f, l]` -/
def nxtTm : Tm :=
  .letE (.call fDrop [V 0, V 1])
    (.ite (.isNat (V 0)) (.lit 0) (.ite (.isNat (.snd (V 0))) (.lit 0) (.fst (.snd (V 0)))))

/-- environment `[y, w, c, ns]` -/
def cutAtTm : Tm :=
  .ite (.eq (.fst (V 2)) (.lit 1))
    (.letE (.call fNthD [V 1, .snd (V 2), .lit 0])
      (.cons (.call fDupAfter [V 0, V 4]) (V 0)))
    (.cons (V 3)
      (.ite (.lt (.call fNthD [V 0, .snd (V 2), .lit 0]) (.call fNxt [.snd (V 2), V 0]))
        (.call fNthD [V 1, .snd (V 2), .lit 0])
        (.sub (.call fNxt [.snd (V 2), V 1]) (.lit 1))))

/-- `[s, e, i]` -/
def inRngTm : Tm :=
  .mul (leT (V 0) (V 2)) (.ite (.isNat (V 1)) (.lit 1) (leT (V 2) (.snd (V 1))))

/-- `[v, s, e, i, ns]` -/
def addVAuxTm : Tm :=
  .ite (.isNat (V 4)) (V 4)
    (.cons
      (.ite (.call fInRng [V 1, V 2, V 3])
        (.cons (.call Lib3.fInsertS [V 0, .fst (.fst (V 4))]) (.snd (.fst (V 4))))
        (.fst (V 4)))
      (.call fAddVAux [V 0, V 1, V 2, .add (V 3) (.lit 1), .snd (V 4)]))

def addVTm : Tm := .call fAddVAux [V 0, V 1, V 2, .lit 0, V 3]

/-- `[x, br, i, ns]` -/
def addJunkAuxTm : Tm :=
  .ite (.isNat (V 3)) (V 3)
    (.cons
      (.ite (.eq (V 2) (V 0))
        (.cons (.fst (.fst (V 3))) (.call fAppend [.snd (.fst (V 3)), .cons (V 1) (.lit 0)]))
        (.fst (V 3)))
      (.call fAddJunkAux [V 0, V 1, .add (V 2) (.lit 1), .snd (V 3)]))

def addJunkTm : Tm := .call fAddJunkAux [V 0, V 1, .lit 0, V 2]

/-- `[v, chain, M]` -/
def branchRTTm : Tm :=
  .ite (.isNat (V 1)) (.cons (.call Lib3.fInsertS [V 0, V 2]) (.lit 0))
    (.cons (.fst (V 1)) (.cons (.call fBranchRT [V 0, .snd (V 1), V 2]) (.lit 0)))

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 470 => some dupAfterTm | 471 => some cutAtTm | 472 => some inRngTm | 473 => some addVAuxTm
  | 474 => some addVTm | 475 => some addJunkAuxTm | 476 => some addJunkTm | 477 => some branchRTTm
  | 478 => some nxtTm
  | _ => none

def Δ : ℕ → Option Tm := layerΔ E5B.Δ 470 tbl

abbrev size : ℕ := 479

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 479 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h470 : 470 ≤ f := by omega
    simp only [h470, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem extB : E5B.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E5B.Δ_lt h; simp [E5B.size] at this; omega)
theorem extA : E5A.Δ ⊑ Δ := Ext.trans E5B.extA extB
theorem extE1 : E1.e1Δ ⊑ Δ := Ext.trans E5B.extE1 extB

theorem Δ_dupAfter : Δ fDupAfter = some dupAfterTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fDupAfter by decide)]; rfl
theorem Δ_cutAt : Δ fCutAt = some cutAtTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fCutAt by decide)]; rfl
theorem Δ_inRng : Δ fInRng = some inRngTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fInRng by decide)]; rfl
theorem Δ_addVAux : Δ fAddVAux = some addVAuxTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fAddVAux by decide)]; rfl
theorem Δ_addV : Δ fAddV = some addVTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fAddV by decide)]; rfl
theorem Δ_addJunkAux : Δ fAddJunkAux = some addJunkAuxTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fAddJunkAux by decide)]; rfl
theorem Δ_addJunk : Δ fAddJunk = some addJunkTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fAddJunk by decide)]; rfl
theorem Δ_branchRT : Δ fBranchRT = some branchRTTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fBranchRT by decide)]; rfl
theorem Δ_nxt : Δ fNxt = some nxtTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fNxt by decide)]; rfl

/-! ## sizes -/

theorem sz_dupAfter_le (i : ℕ) (ns : List CNode) : sz (dupAfter i ns) ≤ 2 * sz ns + 3 := by
  unfold dupAfter
  split
  · omega
  · rename_i n hn
    obtain ⟨b, j⟩ := n
    have hmem : (CNode.mk b j) ∈ ns := List.mem_of_getElem? hn
    have h1 := sz_mem_lt hmem
    have h2 := sz_append (ns.take (i + 1)) [CNode.mk b []]
    have h3 := sz_append (ns.take (i + 1) ++ [CNode.mk b []]) (ns.drop (i + 1))
    have h4 := sz_append (ns.take (i + 1)) (ns.drop (i + 1))
    rw [List.take_append_drop] at h4
    have h6 : sz [CNode.mk b []] = sz b + 4 := by
      simp only [sz_cons, sz_cnode]; have : sz ([] : List RT) = 1 := rfl; have : sz ([] : List CNode) = 1 := rfl; omega
    rw [sz_cnode] at h1
    dsimp only
    omega

theorem sz_cutAt_le (y w : List ℕ) (c : CT.Cut) (ns : List CNode) : sz (cutAt y w c ns).1 ≤ 2 * sz ns + 3 := by
  cases c with
  | t1 f => simp only [cutAt]; exact sz_dupAfter_le _ _
  | t2 f => simp only [cutAt]; omega

theorem sz_addVL_le (v s : ℕ) (e : Option ℕ) : ∀ (i : ℕ) (ns : List CNode),
    sz (addVL v s e i ns) ≤ sz ns + 2 * ns.length
  | i, [] => by simp [addVL]
  | i, n :: ns => by
    obtain ⟨b, j⟩ := n
    have ih := sz_addVL_le v s e (i + 1) ns
    have := sz_insert_le v b
    simp only [addVL, List.length_cons, sz_cons, sz_cnode]
    split_ifs <;> simp only [sz_cons, sz_cnode] <;> omega

theorem sz_addV_le (v s : ℕ) (e : Option ℕ) (ns : List CNode) : sz (addV v s e ns) ≤ 2 * sz ns := by
  rw [addV_eq]
  have := sz_addVL_le v s e 0 ns
  have := sz_chain_ge ns
  omega

theorem addJunkL_of_lt (x : ℕ) (br : RT) : ∀ (i : ℕ) (ns : List CNode), x < i → addJunkL x br i ns = ns
  | i, [], _ => by simp [addJunkL]
  | i, n :: ns, h => by
    simp only [addJunkL, if_neg (show ¬ i = x by omega)]
    rw [addJunkL_of_lt x br (i + 1) ns (by omega)]

theorem sz_addJunkL_le (x : ℕ) (br : RT) : ∀ (i : ℕ) (ns : List CNode),
    sz (addJunkL x br i ns) ≤ sz ns + sz br + 2
  | i, [] => by simp [addJunkL]
  | i, n :: ns => by
    obtain ⟨b, j⟩ := n
    have ih := sz_addJunkL_le x br (i + 1) ns
    have := sz_append j [br]
    have h2 : sz [br] = sz br + 2 := by rw [sz_cons]; simp
    by_cases hix : i = x
    · rw [addJunkL, if_pos hix, addJunkL_of_lt x br (i + 1) ns (by omega)]
      simp only [sz_cons, sz_cnode]
      omega
    · rw [addJunkL, if_neg hix]
      simp only [sz_cons, sz_cnode]
      omega

theorem sz_addJunk_le (x : ℕ) (br : RT) (ns : List CNode) : sz (addJunk x br ns) ≤ sz ns + sz br + 2 := by
  rw [addJunk_eq]; exact sz_addJunkL_le x br 0 ns

theorem sz_branchRT_le (v : ℕ) (chain : List (Finset ℕ)) (M : Finset ℕ) :
    sz (branchRT v chain M) ≤ 3 * sz chain + sz M + 4 := by
  induction chain with
  | nil =>
    have := sz_insert_le v M
    simp only [branchRT, List.foldr_nil, sz_rt_node, sz_cons]
    have : sz ([] : List RT) = 1 := rfl
    have : sz ([] : List (Finset ℕ)) = 1 := rfl
    omega
  | cons X chain ih =>
    simp only [branchRT, List.foldr_cons, sz_rt_node, sz_cons] at ih ⊢
    have : sz ([] : List RT) = 1 := rfl
    have := sz_pos X; have := sz_pos chain
    omega

/-! ## the lemmas -/

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem nthD_in_runs {α : Type} [ToVal α] (hB : 1 < B) (xs : List α) (i : ℕ) (d : Val) (hi : i < xs.length) :
    Runs Δ' B fNthD [toVal xs, toVal i, d] (toVal xs[i]) (16 * i + 12) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    have hΔA : E5A.Δ ⊑ Δ' := Ext.trans extA hΔ
    refine Runs.mk (hΔA _ _ E5A.Δ_nthD) ?_
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      ev_start
      · ev_run
      · omega
    | succ i =>
      have h1 := ih i (by simpa using hi)
      simp only [List.getElem_cons_succ]
      ev_start
      · ev_run
      · omega

theorem dupAfter_runs (i : ℕ) (ns : List CNode) (hB : 1000 + 100 * (sz ns + 1) < B) :
    Runs Δ' B fDupAfter [toVal i, toVal ns] (toVal (dupAfter i ns)) (40 * sz ns + 100) := by
  have hE1 := Ext.trans extE1 hΔ
  have hlen := length_le_sz ns
  have hc := sz_chain_ge ns
  have h1 := Lib1.length_runs (l1 hE1) B ns (by omega)
  by_cases hi : i < ns.length
  · have hn := nthD_in_runs hΔ B (by omega) ns i (Val.nat 0) hi
    have h2 := Lib1.take_runs (l1 hE1) B (i + 1) ns (by omega)
    have h3 := Lib1.drop_runs (l1 hE1) B (i + 1) ns (by omega)
    have hd : dupAfter i ns = ns.take (i + 1) ++ [(⟨(ns[i]).bag, []⟩ : CNode)] ++ ns.drop (i + 1) := by
      simp only [dupAfter, List.getElem?_eq_getElem hi]
    have h4 := Lib1.append_runs (l1 hE1) B (ns.take (i + 1)) [(⟨(ns[i]).bag, []⟩ : CNode)]
    have h5 := Lib1.append_runs (l1 hE1) B (ns.take (i + 1) ++ [(⟨(ns[i]).bag, []⟩ : CNode)]) (ns.drop (i + 1))
    have hm1 : min (i + 1) ns.length ≤ ns.length := min_le_right _ _
    have hm2 : (ns.take (i + 1)).length ≤ ns.length := by simp
    refine Runs.mk (hΔ _ _ Δ_dupAfter) ?_
    rw [hd]
    ev_start
    · ev_run
    · simp only [List.length_append, List.length_singleton] at *
      omega
  · have hd : dupAfter i ns = ns := by
      simp only [dupAfter, List.getElem?_eq_none (by omega : ns.length ≤ i)]
    refine Runs.mk (hΔ _ _ Δ_dupAfter) ?_
    rw [hd]
    ev_start
    · ev_run
    · omega

omit hΔ in
theorem getD_succ_eq (l : List ℕ) (f : ℕ) :
    l.getD (f + 1) 0 = (match l.drop f with | [] => 0 | [_] => 0 | _ :: y :: _ => y) := by
  rw [← show (l.drop f).getD 1 0 = l.getD (f + 1) 0 by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  rcases l.drop f with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> simp

theorem nxt_runs (f : ℕ) (l : List ℕ) (hB : 1 < B) :
    Runs Δ' B fNxt [toVal f, toVal l] (toVal (l.getD (f + 1) 0)) (20 * l.length + 30) := by
  have hE1 := Ext.trans extE1 hΔ
  have h1 := Lib1.drop_runs (l1 hE1) B f l hB
  have hm : min f l.length ≤ l.length := min_le_right _ _
  rw [getD_succ_eq]
  refine Runs.mk (hΔ _ _ Δ_nxt) ?_
  rcases hd : l.drop f with _ | ⟨x, _ | ⟨y, r⟩⟩
  · rw [hd] at h1
    simp only []
    ev_start
    · ev_run
    · omega
  · rw [hd] at h1
    simp only []
    ev_start
    · ev_run
    · omega
  · rw [hd] at h1
    simp only []
    ev_start
    · ev_run
    · omega

theorem cutAt_runs (y w : List ℕ) (c : CT.Cut) (ns : List CNode) (s : ℕ) (hy : y.length ≤ s) (hw : w.length ≤ s)
    (hns : sz ns ≤ s) (hB : 1000 + 100 * (2 * s + 1) < B) :
    Runs Δ' B fCutAt [toVal y, toVal w, toVal c, toVal ns] (toVal (cutAt y w c ns)) (100 * s + 400) := by
  have hE1 := Ext.trans extE1 hΔ
  have hΔA : E5A.Δ ⊑ Δ' := Ext.trans extA hΔ
  have hB1 : 1 < B := by omega
  have hkd : fDupAfter < B := by show 470 < B; omega
  have hkn : fNxt < B := by show 478 < B; omega
  cases c with
  | t1 f =>
    have hw1 := E5A.nthD_runs hΔA B hB1 w f 0
    have hd := dupAfter_runs hΔ B (w.getD f 0) ns (by omega)
    refine Runs.mk (hΔ _ _ Δ_cutAt) ?_
    simp only [cutAt, toVal_pair, toVal_cut_t1]
    ev_start
    · ev_run
    · have := length_le_sz ns
      omega
  | t2 f =>
    have hy1 := E5A.nthD_runs hΔA B hB1 y f 0
    have hy2 := nxt_runs hΔ B f y hB1
    have hw1 := E5A.nthD_runs hΔA B hB1 w f 0
    have hw2 := nxt_runs hΔ B f w hB1
    refine Runs.mk (hΔ _ _ Δ_cutAt) ?_
    simp only [cutAt, toVal_pair, toVal_cut_t2]
    by_cases hlt : y.getD f 0 < y.getD (f + 1) 0
    · simp only [hlt, if_true]
      ev_start
      · ev_run
      · omega
    · simp only [hlt, if_false]
      ev_start
      · ev_run
      · omega

theorem inRng_runs (s : ℕ) (e : Option ℕ) (i : ℕ) (hB : 1 < B) :
    Runs Δ' B fInRng [toVal s, toVal e, toVal i] (toVal (inRng s e i)) 20 := by
  refine Runs.mk (hΔ _ _ Δ_inRng) ?_
  cases e with
  | none =>
    by_cases h1 : s ≤ i
    · have : inRng s none i = true := by simp [inRng, h1]
      rw [this]
      have h1' : ¬ i < s := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1']; done) | (simp [h1']; omega))
      · omega
    · have : inRng s none i = false := by simp [inRng, h1]
      rw [this]
      have h1' : i < s := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1']; done) | (simp [h1']; omega))
      · omega
  | some e0 =>
    by_cases h1 : s ≤ i <;> by_cases h2 : i ≤ e0
    · have : inRng s (some e0) i = true := by simp [inRng, h1, h2]
      rw [this]
      have h1' : ¬ i < s := by omega
      have h2' : ¬ e0 < i := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1', h2']; done) | (simp [h1', h2']; omega))
      · omega
    · have : inRng s (some e0) i = false := by simp [inRng, h1, h2]
      rw [this]
      have h1' : ¬ i < s := by omega
      have h2' : e0 < i := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1', h2']; done) | (simp [h1', h2']; omega))
      · omega
    · have : inRng s (some e0) i = false := by simp [inRng, h1, h2]
      rw [this]
      have h1' : i < s := by omega
      have h2' : ¬ e0 < i := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1', h2']; done) | (simp [h1', h2']; omega))
      · omega
    · have : inRng s (some e0) i = false := by simp [inRng, h1, h2]
      rw [this]
      have h1' : i < s := by omega
      have h2' : e0 < i := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1', h2']; done) | (simp [h1', h2']; omega))
      · omega

theorem addVAux_runs (v s : ℕ) (e : Option ℕ) : ∀ (ns : List CNode) (i : ℕ), i + sz ns + 1000 < B →
    Runs Δ' B fAddVAux [toVal v, toVal s, toVal e, toVal i, toVal ns] (toVal (addVL v s e i ns)) (80 * sz ns + 8)
  | [], i, hB => by
    refine Runs.mk (hΔ _ _ Δ_addVAux) ?_
    simp only [addVL]
    ev_start
    · ev_run
    · simp
  | n :: ns, i, hB => by
    obtain ⟨b, j⟩ := n
    have hE1 := Ext.trans extE1 hΔ
    have hs : sz (CNode.mk b j :: ns) = sz b + sz j + 1 + sz ns + 1 := by rw [sz_cons, sz_cnode]
    have hc1 := card_le_sz b
    have hb1 := sz_pos j
    have hin := inRng_runs hΔ B s e i (by omega)
    have hi2 := Lib3.insert_runs (l3 hE1) B v b
    have ih := addVAux_runs v s e ns (i + 1) (by omega)
    have hk : fInRng < B := by show 472 < B; omega
    have hk2 : fAddVAux < B := by show 473 < B; omega
    refine Runs.mk (hΔ _ _ Δ_addVAux) ?_
    simp only [toVal_cons, toVal_cnode]
    by_cases hc : inRng s e i = true
    · simp only [hc] at hin
      simp only [addVL, hc, if_true, toVal_cons, toVal_cnode]
      ev_start
      · ev_run
      · have hsb := sz_finset b
        omega
    · simp only [Bool.not_eq_true] at hc
      simp only [hc] at hin
      simp only [addVL, hc, Bool.false_eq_true, if_false, toVal_cons, toVal_cnode]
      ev_start
      · ev_run
      · omega

theorem addV_runs (v s : ℕ) (e : Option ℕ) (ns : List CNode) (hB : sz ns + 1000 < B) :
    Runs Δ' B fAddV [toVal v, toVal s, toVal e, toVal ns] (toVal (addV v s e ns)) (80 * sz ns + 20) := by
  have h1 := addVAux_runs hΔ B v s e ns 0 (by omega)
  have hk : fAddVAux < B := by show 473 < B; omega
  refine Runs.mk (hΔ _ _ Δ_addV) ?_
  rw [addV_eq]
  ev_start
  · ev_run
  · omega

theorem addJunkAux_runs (x : ℕ) (br : RT) : ∀ (ns : List CNode) (i : ℕ), i + sz ns + 1000 < B →
    Runs Δ' B fAddJunkAux [toVal x, toVal br, toVal i, toVal ns] (toVal (addJunkL x br i ns)) (60 * sz ns + 8)
  | [], i, hB => by
    refine Runs.mk (hΔ _ _ Δ_addJunkAux) ?_
    simp only [addJunkL]
    ev_start
    · ev_run
    · simp
  | n :: ns, i, hB => by
    obtain ⟨b, j⟩ := n
    have hE1 := Ext.trans extE1 hΔ
    have hs : sz (CNode.mk b j :: ns) = sz b + sz j + 1 + sz ns + 1 := by rw [sz_cons, sz_cnode]
    have hb1 := sz_pos b
    have hj1 := length_le_sz j
    have ih := addJunkAux_runs x br ns (i + 1) (by omega)
    have hk2 : fAddJunkAux < B := by show 475 < B; omega
    refine Runs.mk (hΔ _ _ Δ_addJunkAux) ?_
    simp only [toVal_cons, toVal_cnode]
    by_cases hix : i = x
    · have ha := Lib1.append_runs (l1 hE1) B j [br]
      simp only [addJunkL, hix, if_true, toVal_cons, toVal_cnode]
      subst hix
      ev_start
      · ev_run
      · omega
    · simp only [addJunkL, hix, if_false, toVal_cons, toVal_cnode]
      ev_start
      · ev_run
      · omega

theorem addJunk_runs (x : ℕ) (br : RT) (ns : List CNode) (hB : sz ns + 1000 < B) :
    Runs Δ' B fAddJunk [toVal x, toVal br, toVal ns] (toVal (addJunk x br ns)) (60 * sz ns + 20) := by
  have h1 := addJunkAux_runs hΔ B x br ns 0 (by omega)
  have hk : fAddJunkAux < B := by show 475 < B; omega
  refine Runs.mk (hΔ _ _ Δ_addJunk) ?_
  rw [addJunk_eq]
  ev_start
  · ev_run
  · omega

theorem branchRT_runs (v : ℕ) (chain : List (Finset ℕ)) (M : Finset ℕ) (hB : 1000 + 100 * (sz chain + sz M + 1) < B) :
    Runs Δ' B fBranchRT [toVal v, toVal chain, toVal M] (toVal (branchRT v chain M))
      (40 * sz chain + 40 * sz M + 100) := by
  have hE1 := Ext.trans extE1 hΔ
  induction chain with
  | nil =>
    have hi := Lib3.insert_runs (l3 hE1) B v M
    have hc := card_le_sz M
    refine Runs.mk (hΔ _ _ Δ_branchRT) ?_
    simp only [branchRT, List.foldr_nil, toVal_rt, toVal_nil]
    ev_start
    · ev_run
    · have : sz ([] : List (Finset ℕ)) = 1 := rfl
      omega
  | cons X chain ih =>
    have ih := ih (by simp only [sz_cons] at hB; omega)
    have hk : fBranchRT < B := by show 477 < B; omega
    refine Runs.mk (hΔ _ _ Δ_branchRT) ?_
    simp only [branchRT, List.foldr_cons, toVal_rt, toVal_cons, toVal_nil] at ih ⊢
    ev_start
    · ev_run
    · simp only [sz_cons]
      have := sz_pos X
      omega

end proofs
end E5C1
end Lax117284Proofs.Treewidth.Fun

