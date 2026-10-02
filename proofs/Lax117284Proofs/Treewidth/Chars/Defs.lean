import Lax117284Proofs.Treewidth.Trees.Basic
import Lax117284Proofs.Treewidth.Trees.Bridge1Restrict
import Lax117284Proofs.Treewidth.Seq.Stack
import Lax117284Proofs.Treewidth.Seq.Dom
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset

/-!
# Characteristics: rooted run trees and the four transitions (definitions only)

The computable core of the Bodlaender–Kloks algorithm as designed in `blueprint/BP3_Chars.lean` and tested in
`reference/chars.py`.  Every definition is a total, computable Lean function (no `sorry`, no axioms, no
`noncomputable`); the theorems about them are *statements* in `proofs-todo/Statements.lean`, proved elsewhere.

A *characteristic* of a partial decomposition relative to its boundary `B` is a rooted tree of **runs**:

* `S ⊆ B`  the restricted bag (`bag ∩ B`), shared by all tree nodes of the run;
* `y`      the typical sequence of the bag sizes along the run (a chain of tree nodes with the same `S`);
* `kids`   the runs hanging below the last tree node of the run, in canonical order.

Normal form (`norm`): (i) a leaf run whose label is contained in its parent's label is junk; (ii) a run whose only
kid has the same label is merged with it (`τ` of the concatenation); (iii) a run without kids keeps only its first
entry.  Kids are sorted by the least vertex they *own* (`key`).

Deviations from the blueprint (all definitional-equality or harmless, see the delivery report):
`norm` is split as `normNode S y (normL ks)` (`norm_node` is `rfl`); `ringTypList` is the projection of a lattice DP
that also records one witness path per state (needed by the extraction's `findPath`); `joinC` deduplicates its run
sequences (the Python reference builds a set); `allChains` uses `sublists` of the sorted list instead of
`Finset.powerset.toList` (the latter is noncomputable).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

/-! ## the characteristic trees -/

/-- A characteristic (a rooted tree of runs). -/
inductive CT where
  | node (S : Finset ℕ) (y : List ℕ) (kids : List CT)

mutual
/-- Decidable equality (the `deriving` handler does not support this nested inductive). -/
def decEqCT : (a b : CT) → Decidable (a = b)
  | .node S y ks, .node S' y' ks' =>
    match decEq S S' with
    | isFalse h => isFalse (fun e => h (by cases e; rfl))
    | isTrue h₁ =>
      match decEq y y' with
      | isFalse h => isFalse (fun e => h (by cases e; rfl))
      | isTrue h₂ =>
        match decEqCTL ks ks' with
        | isFalse h => isFalse (fun e => h (by cases e; rfl))
        | isTrue h₃ => isTrue (by subst h₁ h₂ h₃; rfl)
def decEqCTL : (a b : List CT) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | k :: ks, k' :: ks' =>
    match decEqCT k k' with
    | isFalse h => isFalse (fun e => h (by cases e; rfl))
    | isTrue h₁ =>
      match decEqCTL ks ks' with
      | isFalse h => isFalse (fun e => h (by cases e; rfl))
      | isTrue h₂ => isTrue (by subst h₁ h₂; rfl)
end

instance : DecidableEq CT := decEqCT

namespace CT

def S : CT → Finset ℕ | node S _ _ => S
def y : CT → List ℕ | node _ y _ => y
def kids : CT → List CT | node _ _ ks => ks

mutual
/-- All boundary vertices occurring in the labels of the runs. -/
def verts : CT → Finset ℕ
  | node S _ ks => S ∪ vertsL ks
def vertsL : List CT → Finset ℕ
  | [] => ∅
  | k :: ks => verts k ∪ vertsL ks
end

mutual
/-- The largest entry of any run sequence. -/
def maxEntry : CT → ℕ
  | node _ y ks => max (y.foldr max 0) (maxEntryL ks)
def maxEntryL : List CT → ℕ
  | [] => 0
  | k :: ks => max (maxEntry k) (maxEntryL ks)
end

mutual
/-- Number of runs. -/
def count : CT → ℕ
  | node _ _ ks => 1 + countL ks
def countL : List CT → ℕ
  | [] => 0
  | k :: ks => count k + countL ks
end

mutual
/-- Apply `f` to every label. -/
def relabel (f : Finset ℕ → Finset ℕ) : CT → CT
  | node S y ks => node (f S) y (relabelL f ks)
def relabelL (f : Finset ℕ → Finset ℕ) : List CT → List CT
  | [] => []
  | k :: ks => relabel f k :: relabelL f ks
end

def isLeaf (t : CT) : Bool := t.kids.isEmpty

/-- The least vertex owned by a kid (present in its subtree, absent from the parent label). -/
def key (S : Finset ℕ) (k : CT) : WithTop ℕ := (k.verts \ S).min

/-- Sort kids by `key` (stable). -/
def sortKids (S : Finset ℕ) (ks : List CT) : List CT :=
  ks.mergeSort (fun a b => decide (key S a ≤ key S b))

/-- One step of the normal form, given the already normalised kids. -/
def normNode (S : Finset ℕ) (y : List ℕ) (ks : List CT) : CT :=
  match ks.filter (fun k => !(k.isLeaf && decide (k.S ⊆ S))) with
  | [] => node S (y.take 1) []
  | [k] => if k.S = S then node S (typical (y ++ k.y)) k.kids else node S y [k]
  | ks' => node S y (sortKids S ks')

mutual
/-- The normal form (i)–(iii). -/
def norm : CT → CT
  | node S y ks => normNode S y (normL ks)
def normL : List CT → List CT
  | [] => []
  | k :: ks => norm k :: normL ks
end

theorem norm_node (S : Finset ℕ) (y : List ℕ) (ks : List CT) : norm (node S y ks) = normNode S y (normL ks) := rfl

/-- The initial characteristic (leaf of a nice decomposition, empty boundary). -/
def start : CT := node ∅ [0] []

/-- **Forget** `x`. -/
def forgetC (x : ℕ) (t : CT) : CT := norm (relabel (fun S => S.erase x) t)

/-! ### join -/

/-- A state of the lattice dynamic programme: the `τ` of the sums along a path, and (reversed) that path. -/
abbrev LState := List ℕ × List (ℕ × ℕ)

/-- Keep the first state for every `τ`-prefix. -/
def dedupKey (l : List LState) : List LState :=
  l.foldl (fun acc s => if acc.any (fun t => decide (t.1 = s.1)) then acc else acc ++ [s]) []

/-- The states of cell `(i, j)` (whose entry is `z = a_i + b_j`) from those of the three predecessors. -/
def cellOf (i j z : ℕ) (up left diag : List LState) : List LState :=
  dedupKey ((up ++ left ++ diag).map (fun s => (push s.1 z, (i, j) :: s.2)))

/-- One row `i` of the lattice (`x = a_i`): `ups` the row above, `diag` the state list of the up-left neighbour,
`left` that of the left neighbour. -/
def rowCells (i x : ℕ) : List ℕ → ℕ → List (List LState) → List LState → List LState → List (List LState)
  | [], _, _, _, _ => []
  | y :: b, j, ups, diag, left =>
    let c := cellOf i j (x + y) (ups.headD []) left diag
    c :: rowCells i x b (j + 1) ups.tail (ups.headD []) c

/-- Process the rows `a_i, a_{i+1}, …` (`prev` the row above); returns the last row.  The first row starts from the
seed state `([], [])` at cell `(0,0)`. -/
def latticeRows (b : List ℕ) : ℕ → List ℕ → List (List LState) → List (List LState)
  | _, [], prev => prev
  | i, x :: a, prev =>
    latticeRows b (i + 1) a (rowCells i x b 0 prev (if i = 0 then [([], [])] else []) [])

/-- The states of the final cell `(|a|-1, |b|-1)`: one state per typical ring sum `τ c`, `c ∈ a ⊕ b`, with the
first lattice path (reversed) that reaches it.  (`reference/typical.py: ring`, `real.py: find_path`.) -/
def latticeStates (a b : List ℕ) : List LState :=
  match a, b with
  | [], _ => []
  | _, [] => []
  | _, _ => (latticeRows b 0 a []).getLast?.getD []

/-- The typical ring sums as a computable list (dynamic programme over the lattice of pairs, with `τ` of the prefix
as state; `reference/typical.py: ring`). -/
def ringTypList (a b : List ℕ) : List (List ℕ) := (latticeStates a b).map Prod.fst

mutual
/-- **Join.**  All characteristics of joins of decompositions with characteristics `t₁`, `t₂` (same shape).  The
sizes of the two sides add, the restricted bag being counted once; entries above `kmax` are discarded. -/
def joinC (kmax : ℕ) : CT → CT → List CT
  | node S y ks, node S' y' ks' =>
    if S = S' ∧ ks.length = ks'.length then
      let ys := (((ringTypList y y').map (fun d => d.map (· - S.card))).dedup).filter (fun d => d.all (· ≤ kmax))
      (joinKids kmax ks ks').flatMap (fun kk => ys.map (fun d => node S d kk))
    else []
def joinKids (kmax : ℕ) : List CT → List CT → List (List CT)
  | k :: ks, k' :: ks' => (joinC kmax k k').flatMap (fun c => (joinKids kmax ks ks').map (c :: ·))
  | [], [] => [[]]
  | _, _ => []
end

/-! ### introduce -/

def plus1 (y : List ℕ) : List ℕ := y.map (· + 1)

/-- A cut of a typical sequence: first type at `f` (the entry `y_f` is duplicated), second type after `f`. -/
inductive Cut where
  | t1 (f : ℕ)
  | t2 (f : ℕ)
  deriving DecidableEq

def Cut.isT1 : Cut → Bool
  | .t1 _ => true
  | .t2 _ => false

/-- How the new vertex's region `W` sits in a run whose first tree node is in `W`: it ends inside the run, or it
covers the whole run and continues (or not) into each kid run. -/
inductive WPlan where
  | endAt (c : Cut)
  | whole (kids : List (Option WPlan))

/-- An option for the introduction of a vertex: a new leaf branch hanging at a tree node of a run (case (b)), or a
region `W` meeting the core with its topmost tree node inside a run (case (a)). -/
inductive Plan where
  | att (c : Option Cut) (chain : List (Finset ℕ)) (M : Finset ℕ)
  | top (pre : Option Cut) (w : WPlan)

mutual
/-- Case (a): `W` contains the first tree node of the run, entered at typical index `lo`.
Returns (plan, replacement subtree, vertices of `B` covered by `W`). -/
def winPlans (v : ℕ) (lo : ℕ) : CT → List (WPlan × CT × Finset ℕ)
  | node S y ks =>
    let S1 := insert v S
    let s := y.length
    let ends1 := (List.range' lo (s - lo)).map fun f =>
      (WPlan.endAt (Cut.t1 f), node S1 (plus1 ((y.take (f + 1)).drop lo)) [node S (y.drop f) ks], S)
    let ends2 := (List.range' lo (s - 1 - lo)).map fun f =>
      (WPlan.endAt (Cut.t2 f), node S1 (plus1 ((y.take (f + 1)).drop lo)) [node S (y.drop (f + 1)) ks], S)
    let whole := (kidChoices v ks).map fun combo =>
      (WPlan.whole (combo.map (·.1)), node S1 (plus1 (y.drop lo)) (combo.map (·.2.1)),
        combo.foldl (fun a c => a ∪ c.2.2) S)
    ends1 ++ ends2 ++ whole
/-- Per kid: leave it (`none`, covering nothing) or let `W` continue into it. -/
def kidChoices (v : ℕ) : List CT → List (List (Option WPlan × CT × Finset ℕ))
  | [] => [[]]
  | k :: ks =>
    let opts : List (Option WPlan × CT × Finset ℕ) :=
      (none, k, ∅) :: (winPlans v 0 k).map (fun p => (some p.1, p.2.1, p.2.2))
    opts.flatMap fun o => (kidChoices v ks).map (o :: ·)
end

/-- Case (a) with an optional pre-cut: `W`'s topmost tree node lies inside the run. -/
def wtopPlans (v : ℕ) : CT → List (Plan × CT × Finset ℕ)
  | t@(node S y _) =>
    let s := y.length
    let direct := (winPlans v 0 t).map fun p => (Plan.top none p.1, p.2.1, p.2.2)
    let pre1 := (List.range s).flatMap fun f =>
      (winPlans v f t).map fun p => (Plan.top (some (Cut.t1 f)) p.1, node S (y.take (f + 1)) [p.2.1], p.2.2)
    let pre2 := (List.range (s - 1)).flatMap fun f =>
      (winPlans v (f + 1) t).map fun p => (Plan.top (some (Cut.t2 f)) p.1, node S (y.take (f + 1)) [p.2.1], p.2.2)
    direct ++ pre1 ++ pre2

/-- The candidate leaf labels / chain elements for a branch hanging at a run with label `S` (needs `N ⊆ S`):
`N ∪ c` for every subset `c` of `S \ N`. -/
def chainCands (S N : Finset ℕ) : List (Finset ℕ) :=
  (((S \ N).sort (· ≤ ·)).sublists).map (fun c => N ∪ c.toFinset)

/-- The enumeration of chains, with fuel: at each level output the leaf labels `M ⊆ bound`, and extend the chain by a
candidate `X ⊆ bound` (strictly below `bound` once the chain is non-empty). -/
def chainsGo (cands : List (Finset ℕ)) :
    ℕ → Finset ℕ → List (Finset ℕ) → List (List (Finset ℕ) × Finset ℕ)
  | 0, bound, chain => (cands.filter (· ⊆ bound)).map (fun M => (chain, M))
  | fuel + 1, bound, chain =>
    (cands.filter (· ⊆ bound)).map (fun M => (chain, M)) ++
    (cands.filter (fun X => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound)))).flatMap
      (fun X => chainsGo cands fuel X (chain ++ [X]))

/-- The shapes of a new branch hanging at a run with label `S` (needs `N ⊆ S`): a strictly decreasing chain of
subsets of `S` containing `N`, then a leaf labelled `M ∪ {v}`, `N ⊆ M` below the last chain element.
(`reference/chars.py: all_chains`; *all* nested chains are needed — this corrects a tempting simplification.)
The fuel `|S| + 1` bounds the chain length. -/
def allChains (S N : Finset ℕ) : List (List (Finset ℕ) × Finset ℕ) :=
  chainsGo (chainCands S N) (S.card + 1) S []

/-- The branch subtree: the chain of nested labels ending in the leaf `M ∪ {v}`. -/
def pathSubtree (v : ℕ) (chain : List (Finset ℕ)) (M : Finset ℕ) : CT :=
  chain.foldr (fun X acc => node X [X.card] [acc]) (node (insert v M) [M.card + 1] [])

/-- Case (b): hang a new branch at (a tree node of) the run `node S y ks`; with an optional cut of the run first. -/
def attachPlans (v : ℕ) (N : Finset ℕ) : CT → List (Plan × CT)
  | node S y ks =>
    (allChains S N).flatMap fun cm =>
      let br := pathSubtree v cm.1 cm.2
      (Plan.att none cm.1 cm.2, node S y (ks ++ [br])) ::
      ((List.range y.length).map fun f =>
        (Plan.att (some (Cut.t1 f)) cm.1 cm.2, node S (y.take (f + 1)) [br, node S (y.drop f) ks])) ++
      ((List.range (y.length - 1)).map fun f =>
        (Plan.att (some (Cut.t2 f)) cm.1 cm.2, node S (y.take (f + 1)) [br, node S (y.drop (f + 1)) ks]))

mutual
/-- All options (path to the run, plan, un-normalised result) for introducing `v` with neighbours `N`. -/
def introPlans (v : ℕ) (N : Finset ℕ) : CT → List (List ℕ × Plan × CT)
  | t@(node S y ks) =>
    ((wtopPlans v t).filter (fun p => decide (N ⊆ p.2.2))).map (fun p => ([], p.1, p.2.1)) ++
    (if N ⊆ S then (attachPlans v N t).map (fun p => ([], p.1, p.2)) else []) ++
    introKids v N S y [] ks
def introKids (v : ℕ) (N S : Finset ℕ) (y : List ℕ) (pre : List CT) : List CT → List (List ℕ × Plan × CT)
  | [] => []
  | k :: post =>
    (introPlans v N k).map (fun r => (pre.length :: r.1, r.2.1, node S y (pre ++ r.2.2 :: post))) ++
    introKids v N S y (pre ++ [k]) post
end

/-- **Introduce** `v` (with neighbours `N` in the boundary): the normalised results of all options. -/
def introC (kmax : ℕ) (v : ℕ) (N : Finset ℕ) (t : CT) : List CT :=
  ((introPlans v N t).map (fun r => norm r.2.2)).filter (fun c => decide (c.maxEntry ≤ kmax))

/-! ### dominance -/

mutual
/-- `DomC a b`: same shape, run-wise `Dom`  ("`a` is at least as good as `b`"). -/
def DomC : CT → CT → Prop
  | node S y ks, node S' y' ks' => S = S' ∧ Dom y y' ∧ DomCL ks ks'
def DomCL : List CT → List CT → Prop
  | [], [] => True
  | k :: ks, k' :: ks' => DomC k k' ∧ DomCL ks ks'
  | _, _ => False
end

mutual
/-- The decision procedure for `DomC` (`domCB_iff` in `proofs-todo/Statements.lean`). -/
def domCB : CT → CT → Bool
  | node S y ks, node S' y' ks' => decide (S = S') && domB y y' && domCBL ks ks'
def domCBL : List CT → List CT → Bool
  | [], [] => true
  | k :: ks, k' :: ks' => domCB k k' && domCBL ks ks'
  | _, _ => false
end

/-! ### well-formed characteristics -/

mutual
/-- Local shape invariants of a run (label inside `B`, typical sequence at least `|S|`, a leaf run has one entry, no
prunable leaf kid, a single kid has a different label, kids strictly ordered by `key`), recursively. -/
def Good (B : Finset ℕ) : CT → Prop
  | node S y ks =>
    S ⊆ B ∧ typical y = y ∧ y ≠ [] ∧ (∀ e ∈ y, S.card ≤ e) ∧ (ks = [] → y.length = 1) ∧
    (∀ k ∈ ks, k.kids = [] → ¬ k.S ⊆ S) ∧ (∀ k, ks = [k] → k.S ≠ S) ∧
    ks.Pairwise (fun a b => key S a < key S b) ∧ GoodL B ks
def GoodL (B : Finset ℕ) : List CT → Prop
  | [] => True
  | k :: ks => Good B k ∧ GoodL B ks
end

mutual
/-- Occurrences of every vertex form a connected subtree of runs (as `RT.Conn`). -/
def Conn : CT → Prop
  | node S _ ks => ConnL ks ∧ (∀ k ∈ ks, ∀ v ∈ S, v ∈ verts k → v ∈ k.S) ∧
      ks.Pairwise (fun k₁ k₂ => ∀ v, v ∈ verts k₁ → v ∈ verts k₂ → v ∈ S)
def ConnL : List CT → Prop
  | [] => True
  | k :: ks => Conn k ∧ ConnL ks
end

/-- Well-formed characteristics over the boundary `B` with sizes `≤ kmax`: every boundary vertex occurs
(`verts = B`), local invariants, connectedness. -/
structure Wf (B : Finset ℕ) (kmax : ℕ) (t : CT) : Prop where
  verts_eq : t.verts = B
  good : Good B t
  conn : Conn t
  bounded : t.maxEntry ≤ kmax

/-- `count ≤ M(b)` for a characteristic on `b` boundary vertices: at most `b` non-root leaf runs (each owns a
vertex), at most `b` branching runs, and at most `2b + 1` runs on a path of single-kid runs (each vertex enters and
leaves once): `count ≤ (2b + 2)(2b + 2)`. -/
def runBound (b : ℕ) : ℕ := (2 * b + 2) * (2 * b + 2)

end CT

end Lax117284Proofs.Treewidth.Chars

/-! ## the characteristic of a real rooted decomposition -/

namespace Lax117284Proofs.Treewidth.Trees.RT

open Lax117284Proofs.Treewidth.Chars

mutual
/-- The un-normalised profile of a rooted tree relative to the boundary `B`: label `bag ∩ B`, size `|bag|`. -/
def prof (B : Finset ℕ) : RT → CT
  | .node X ks => .node (X ∩ B) [X.card] (profL B ks)
def profL (B : Finset ℕ) : List RT → List CT
  | [] => []
  | k :: ks => prof B k :: profL B ks
end

/-- **The characteristic of a rooted partial decomposition** relative to `B`. -/
def char (B : Finset ℕ) (t : RT) : CT := CT.norm (t.prof B)

-- `RT.restrict U t` (intersect every bag with `U`) is `Lax117284Proofs.Treewidth.Trees.RT.restrict`, from `Trees/Bridge1Restrict`.

end Lax117284Proofs.Treewidth.Trees.RT
