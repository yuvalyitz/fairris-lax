import Lax117284Proofs.Treewidth.Chars.Defs

/-!
# The algorithm: tables (phase A), extraction (phase B), niceification, `improve`, `decompose`

Images of `blueprint/BP4_Tables.lean`, `BP5_Extract.lean`, `BP6_Count.lean` and of `reference/{dp,real,improve}.py`.
Everything is a total computable Lean function; theorems about it are *statements* in `proofs-todo/Statements.lean`.

**Real trees.**  The Python reference mutates an arena of nodes.  Here the real decomposition is the inductive `RT`,
and the "analysis" of an `RT` relative to a boundary `B` is the annotated run tree `AR` (`analyze`): every run
carries its chain of tree nodes (`CNode`: the bag and the *junk* subtrees hanging at that node, i.e. those children
that are not part of the core), and its kids.  `AR.toRT` reassembles an `RT` (child order is irrelevant to `IsTD`,
`Width`, `char`).  `applyPlan` = analyse, apply the plan to the `AR` (cut / duplicate a chain node, add `v` to the
region, hang the branch as junk), reassemble.  `mergeReal` = analyse both trees, walk a lattice path per run, take
bag unions along the path and the junk of both sides at the first visit of each node, reassemble.

Deviations from the blueprint: see the delivery report (`mergeReal` takes a *join option* and `realJoin` does the
search that `realize_join` of the reference does, because `extract` calls it with a table entry, not with an element
of `joinC` of the *actual* characteristics; `Adj`, `NT.under`, `NT.Good`, `PTD`, `nbrs` are here).
-/

namespace Lax117284Proofs.Treewidth.Trees.NT

/-- The vertices below a node (`V⁺` of the paper). -/
def under : NT → Finset ℕ
  | leaf => ∅
  | intro v c => insert v c.under
  | forget _ c => c.under
  | join a b => a.under ∪ b.under

end Lax117284Proofs.Treewidth.Trees.NT

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## graphs, partial decompositions -/

/-- A graph as a Boolean adjacency function (computable); `Adj.graph` is the `SimpleGraph` it denotes. -/
abbrev Adj := ℕ → ℕ → Bool

def Adj.graph (adj : Adj) : SimpleGraph ℕ := SimpleGraph.fromRel (fun u v => adj u v = true)

end Lax117284Proofs.Treewidth.Chars

namespace Lax117284Proofs.Treewidth.Trees.NT

open Lax117284Proofs.Treewidth.Chars

/-- The "nice" side conditions that make the tables meaningful for the graph `adj`: shapes; *closedness* (a vertex is
introduced with all its neighbours below already in the bag: forgotten vertices have no neighbours outside);
*separation* (the two sides of a join meet only in the bag, and no edge joins the two sides outside the bag:
the last conjunct of `join`, added because without it the tables are unsound — a graph with an edge between the
two sides of a join satisfies all the other clauses).  Both follow from being a tree decomposition
(`good_of_isNiceTD`). -/
def Good (adj : Adj) : NT → Prop
  | leaf => True
  | intro v c => v ∉ c.bag ∧ (∀ u ∈ c.under, adj v u = true → u ∈ c.bag) ∧ v ∉ c.under ∧ Good adj c
  | forget v c => v ∈ c.bag ∧ Good adj c
  | join a b => a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ Good adj a ∧ Good adj b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag)

end Lax117284Proofs.Treewidth.Trees.NT

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- A partial decomposition at a nice node: a tree decomposition of `G[V⁺]` of width `≤ k`. -/
def PTD (adj : Adj) (nt : NT) (k : ℕ) (t : RT) : Prop := t.IsTD adj.graph nt.under ∧ t.Width k

/-! ## phase A: the tables -/

/-- Neighbours of `v` in the boundary. -/
def nbrs (adj : Adj) (v : ℕ) (B : Finset ℕ) : Finset ℕ := B.filter (fun w => adj v w = true)

/-- Forget step on a table. -/
def forgetTable (x : ℕ) (T : List CT) : List CT := (T.map (CT.forgetC x)).dedup

/-- Introduce step on a table. -/
def introTable (kmax v : ℕ) (N : Finset ℕ) (T : List CT) : List CT := (T.flatMap (CT.introC kmax v N)).dedup

/-- Join step on two tables. -/
def joinTable (kmax : ℕ) (Ta Tb : List CT) : List CT :=
  (Ta.flatMap fun ca => Tb.flatMap fun cb => CT.joinC kmax ca cb).dedup

/-- **The tables.**  `k` is the target width; sizes are bounded by `k + 1`.  There is no dominance pruning. -/
def tables (adj : Adj) (k : ℕ) : NT → List CT
  | .leaf => [CT.start]
  | .intro v c => introTable (k + 1) v (nbrs adj v c.bag) (tables adj k c)
  | .forget x c => forgetTable x (tables adj k c)
  | .join a b => joinTable (k + 1) (tables adj k a) (tables adj k b)

/-! ## phase B: analysis of a real tree -/

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A node of a chain of a run: its bag and the junk subtrees hanging at it (children outside the core). -/
structure CNode where
  bag : Finset ℕ
  junk : List RT

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The analysis of a real tree relative to a boundary: a run tree whose runs carry their chains of tree nodes. -/
inductive AR where
  | run (S : Finset ℕ) (chain : List CNode) (kids : List AR)

namespace AR

def S : AR → Finset ℕ | run S _ _ => S
def chain : AR → List CNode | run _ c _ => c
def kids : AR → List AR | run _ _ ks => ks
def isLeaf (r : AR) : Bool := r.kids.isEmpty

mutual
/-- The characteristic read off the analysis (`analyze_char`: it is `RT.char`). -/
def char : AR → CT
  | run S c ks => CT.node S (typical (c.map (fun n => n.bag.card))) (charL ks)
def charL : List AR → List CT
  | [] => []
  | k :: ks => char k :: charL ks
end

/-- A chain with the runs below its last node, reassembled as a real tree (junk first, the core successor last). -/
def chainToRT : List CNode → List RT → RT
  | [], ks => .node ∅ ks
  | [n], ks => .node n.bag (n.junk ++ ks)
  | n :: m :: r, ks => .node n.bag (n.junk ++ [chainToRT (m :: r) ks])

mutual
/-- Reassemble the real tree. -/
def toRT : AR → RT
  | run _ c ks => chainToRT c (toRTL ks)
def toRTL : List AR → List RT
  | [] => []
  | k :: ks => toRT k :: toRTL ks
end

end AR

/-- Sort the kids of a run with label `S` by the key of their characteristic (as `CT.sortKids`). -/
def sortAR (S : Finset ℕ) (ks : List AR) : List AR :=
  ks.mergeSort (fun a b => decide (CT.key S a.char ≤ CT.key S b.char))

/-- One step of the analysis (the normal form of `CT.norm` on annotated trees), given the analysed kids together with
the real subtrees they came from (a pruned kid becomes junk of the node). -/
def analyzeNode (B X : Finset ℕ) (kids : List (RT × AR)) : AR :=
  let S := X ∩ B
  let pruned := fun (p : RT × AR) => p.2.isLeaf && decide (p.2.S ⊆ S)
  let junk := (kids.filter pruned).map Prod.fst
  let core := (kids.filter (fun p => !pruned p)).map Prod.snd
  match core with
  | [] => .run S [⟨X, junk⟩] []
  | [k] => if k.S = S then .run S (⟨X, junk⟩ :: k.chain) k.kids else .run S [⟨X, junk⟩] [k]
  | ks => .run S [⟨X, junk⟩] (sortAR S ks)

mutual
/-- **The analysis of a real tree** relative to the boundary `B` (Python `analyze`). -/
def analyze (B : Finset ℕ) : RT → AR
  | .node X ks => analyzeNode B X (analyzeL B ks)
def analyzeL (B : Finset ℕ) : List RT → List (RT × AR)
  | [] => []
  | k :: ks => (k, analyze B k) :: analyzeL B ks
end

/-! ## phase B: surgery on the analysis -/

/-- Witness positions: the indices in the exact sequence of the entries of its typical sequence (a stack of
`(value, index)` pairs mirroring `Seq.push`; a repeated top value keeps its first index). -/
def wpush : List (ℕ × ℕ) → ℕ → ℕ → List (ℕ × ℕ)
  | [], y, j => [(y, j)]
  | (x, i) :: t, y, j =>
    if t.all (fun z => decide (InR z.1 x y)) then
      (if t.isEmpty && decide (x = y) then [(x, i)] else [(x, i), (y, j)])
    else (x, i) :: wpush t y j

def witnessesAux : ℕ → List (ℕ × ℕ) → List ℕ → List (ℕ × ℕ)
  | _, st, [] => st
  | j, st, y :: a => witnessesAux (j + 1) (wpush st y j) a

/-- `witnesses a`: indices `w₁ < … < w_s` into `a` of the entries of `typical a`. -/
def witnesses (a : List ℕ) : List ℕ := (witnessesAux 0 [] a).map Prod.snd

/-- Duplicate the chain node `i` (the copy has the same bag, no junk, and takes over the successor). -/
def dupAfter (i : ℕ) (ns : List CNode) : List CNode :=
  match ns[i]? with
  | none => ns
  | some n => ns.take (i + 1) ++ [⟨n.bag, []⟩] ++ ns.drop (i + 1)

/-- Cut the chain `ns` (with typical sequence `y` and witnesses `w`) at `c`: returns the new chain and the index
`c'` such that the left piece is `ns'[0..c']`; a first-type cut duplicates the witness node. -/
def cutAt (y w : List ℕ) : Cut → List CNode → List CNode × ℕ
  | .t1 f, ns => (dupAfter (w.getD f 0) ns, w.getD f 0)
  | .t2 f, ns =>
    (ns, if y.getD f 0 < y.getD (f + 1) 0 then w.getD f 0 else w.getD (f + 1) 0 - 1)

/-- Add `v` to the bags of the chain nodes with index in `[s, e]` (`e = none`: to the end). -/
def addV (v s : ℕ) (e : Option ℕ) (ns : List CNode) : List CNode :=
  ns.mapIdx fun i n => if decide (s ≤ i) && e.elim true (fun e => decide (i ≤ e)) then ⟨insert v n.bag, n.junk⟩ else n

/-- Hang a subtree at the chain node `x` (as junk). -/
def addJunk (x : ℕ) (br : RT) (ns : List CNode) : List CNode :=
  ns.mapIdx fun i n => if i = x then ⟨n.bag, n.junk ++ [br]⟩ else n

/-- The new branch of a case-(b) plan as a real tree: the nested chain, then the leaf `M ∪ {v}`. -/
def branchRT (v : ℕ) (chain : List (Finset ℕ)) (M : Finset ℕ) : RT :=
  chain.foldr (fun X acc => RT.node X [acc]) (RT.node (insert v M) [])

mutual
/-- Apply a region plan to a run (`process` of `real.py`): the region contains the first node of the run after the
optional pre-cut `pre`; `w` says where it ends / into which kids it continues. -/
def processRun (v : ℕ) (pre : Option Cut) : WPlan → AR → AR
  | w, .run S ns ks =>
    let sizes := ns.map (fun n => n.bag.card)
    let y := typical sizes
    let wp := witnesses sizes
    let endStep : List CNode × Option ℕ := match w with
      | .endAt c => ((cutAt y wp c ns).1, some (cutAt y wp c ns).2)
      | .whole _ => (ns, none)
    let preStep : List CNode × ℕ × Option ℕ := match pre with
      | none => (endStep.1, 0, endStep.2)
      | some c => ((cutAt y wp c endStep.1).1, (cutAt y wp c endStep.1).2 + 1,
          if c.isT1 then endStep.2.map (· + 1) else endStep.2)
    let ns' := addV v preStep.2.1 preStep.2.2 preStep.1
    let ks' := match w with
      | .endAt _ => ks
      | .whole ps => applyKids v ps ks
    .run S ns' ks'
def applyKids (v : ℕ) : List (Option WPlan) → List AR → List AR
  | [], ks => ks
  | _ :: _, [] => []
  | p :: ps, k :: ks => applyOpt v p k :: applyKids v ps ks
def applyOpt (v : ℕ) : Option WPlan → AR → AR
  | none, k => k
  | some p, k => processRun v none p k
end

/-- Apply a plan to the run at the end of the path. -/
def applyAt (v : ℕ) : Plan → AR → AR
  | .att c chain M, .run S ns ks =>
    let sizes := ns.map (fun n => n.bag.card)
    let y := typical sizes
    let wp := witnesses sizes
    let cutRes : List CNode × ℕ := match c with
      | none => (ns, ns.length - 1)
      | some ct => cutAt y wp ct ns
    .run S (addJunk cutRes.2 (branchRT v chain M) cutRes.1) ks
  | .top pre w, r => processRun v pre w r

/-- Modify the `i`-th element of a list. -/
def modifyNth {α : Type} (f : α → α) : ℕ → List α → List α
  | _, [] => []
  | 0, a :: l => f a :: l
  | i + 1, a :: l => a :: modifyNth f i l

/-- Walk down the path (indices of kids) and apply the plan. -/
def applyRun (v : ℕ) (p : Plan) : List ℕ → AR → AR
  | [], r => applyAt v p r
  | i :: rest, .run S ns ks => .run S ns (modifyNth (applyRun v p rest) i ks)

/-- Apply an introduce plan (found in `introPlans v N (t.char B)` at `path`) to the real tree `t`: locate the run at
`path` in the *analysis* of `t`; cut the chain(s) at the witnesses of the typical sequence (a first-type cut
duplicates a node; second-type cuts assign the entries between two witnesses to the side where they are dominated);
add `v` to the bags of the region; or hang the new branch (bags = the chain sets, and `M ∪ {v}` for the leaf).
Python: `reference/real.py: apply_plan`.  (`N` is unused: the plan already encodes everything.) -/
def applyPlan (v : ℕ) (_N B : Finset ℕ) (path : List ℕ) (p : Plan) (t : RT) : RT :=
  (applyRun v p path (analyze B t)).toRT

/-- The introduce step of the realisation: the first plan whose result is dominated by the target. -/
def realIntro (kmax v : ℕ) (N B : Finset ℕ) (t : RT) (target : CT) : Option RT :=
  ((CT.introPlans v N (t.char B)).find?
      (fun r => domCB (CT.norm r.2.2) target && decide ((CT.norm r.2.2).maxEntry ≤ kmax))).map
    (fun r => applyPlan v N B r.1 r.2.1 t)

/-! ## phase B: merging two real trees along lattice paths (join) -/

/-- A monotone lattice path over the exact size sequences `sa`, `sb` whose `τ`-sum minus `|S|` is dominated by
`want` (first found; Python `find_path`). -/
def findPath (sa sb : List ℕ) (c : ℕ) (want : List ℕ) : Option (List (ℕ × ℕ)) :=
  ((latticeStates sa sb).find? (fun s => domB (s.1.map (· - c)) want)).map (fun s => s.2.reverse)

/-- The merged chain along a path: bag = union of the two bags; junk of a node of either side at its first visit. -/
def mergeChain (na nb : List CNode) : Option (ℕ × ℕ) → List (ℕ × ℕ) → List CNode
  | _, [] => []
  | prev, (i, j) :: rest =>
    let newI := prev.elim true (fun p => decide (p.1 ≠ i))
    let newJ := prev.elim true (fun p => decide (p.2 ≠ j))
    let a := na.getD i ⟨∅, []⟩
    let b := nb.getD j ⟨∅, []⟩
    ⟨a.bag ∪ b.bag, (if newI then a.junk else []) ++ (if newJ then b.junk else [])⟩ ::
      mergeChain na nb (some (i, j)) rest

mutual
/-- Merge two analysed runs along the target run tree `target` (a join option): a lattice path per run. -/
def mergeAR : AR → AR → CT → Option AR
  | .run S na ka, .run _ nb kb, .node _ ty tk =>
    match findPath (na.map (fun n => n.bag.card)) (nb.map (fun n => n.bag.card)) S.card ty with
    | none => none
    | some path => (mergeKids ka kb tk).map (fun ks => .run S (mergeChain na nb none path) ks)
def mergeKids : List AR → List AR → List CT → Option (List AR)
  | [], [], [] => some []
  | a :: as, b :: bs, t :: ts => (mergeAR a b t).bind fun r => (mergeKids as bs ts).map (r :: ·)
  | _, _, _ => none
end

/-- Merge two real trees whose characteristics have the same shape, along lattice paths chosen per run so that the
`τ`-sums are dominated by the run sequences of the *join option* `target`.  `none` if some run has no such path.
Python: `merge_runs`. -/
def mergeReal (B : Finset ℕ) (ta tb : RT) (target : CT) : Option RT :=
  (mergeAR (analyze B ta) (analyze B tb) target).map AR.toRT

/-- The join step of the realisation: the first option of `joinC` of the actual characteristics that is dominated by
the target, merged (Python `realize_join`). -/
def realJoin (kmax : ℕ) (B : Finset ℕ) (ta tb : RT) (target : CT) : Option RT :=
  ((CT.joinC kmax (ta.char B) (tb.char B)).find? (fun d => domCB d target)).bind (mergeReal B ta tb)

/-! ## phase B: extraction -/

/-- Build a real decomposition of `nt` whose characteristic is dominated by the table entry `target`. -/
def extract (adj : Adj) (k : ℕ) : NT → CT → Option RT
  | .leaf, _ => some (.node ∅ [])
  | .forget x c, target =>
      (tables adj k c).findSome? (fun cq => if CT.forgetC x cq = target then extract adj k c cq else none)
  | .intro v c, target =>
      (tables adj k c).findSome? (fun cq =>
        if target ∈ CT.introC (k + 1) v (nbrs adj v c.bag) cq then
          (extract adj k c cq).bind (fun t => realIntro (k + 1) v (nbrs adj v c.bag) c.bag t target)
        else none)
  | .join a b, target =>
      (tables adj k a).findSome? (fun ca => (tables adj k b).findSome? (fun cb =>
        if target ∈ CT.joinC (k + 1) ca cb then
          (extract adj k a ca).bind (fun ta => (extract adj k b cb).bind (fun tb =>
            realJoin (k + 1) a.bag ta tb target))
        else none))

/-! ## Kloks: from a rooted decomposition to a nice one -/

def forgetMany (l : List ℕ) (t : NT) : NT := l.foldl (fun acc x => .forget x acc) t
def introMany (l : List ℕ) (t : NT) : NT := l.foldl (fun acc x => .intro x acc) t

mutual
/-- A nice tree with the same root bag: below each child, forget what the child has extra and introduce what it lacks;
join the children (binary, left to right); a leaf becomes `introMany` of its bag over an empty leaf. -/
def niceOf : RT → NT
  | .node X ks =>
    match niceKids X ks with
    | [] => introMany (X.sort (· ≤ ·)) .leaf
    | t :: ts => ts.foldl NT.join t
def niceKids (X : Finset ℕ) : List RT → List NT
  | [] => []
  | k :: ks =>
    (let t := niceOf k
     introMany ((X \ t.bag).sort (· ≤ ·)) (forgetMany ((t.bag \ X).sort (· ≤ ·)) t)) :: niceKids X ks
end

/-! ## T1 and T2 -/

/-- `G[U]` has a tree decomposition of width `≤ k`. -/
def HasTW (adj : Adj) (U : Finset ℕ) (k : ℕ) : Prop := ∃ t : RT, t.IsTD adj.graph U ∧ t.Width k

/-- **`improve`**: given a nice decomposition of `G[U]` (of any width), a nice decomposition of width `≤ k`, or `none`. -/
def improve (adj : Adj) (k : ℕ) (nt : NT) : Option NT :=
  match tables adj k nt with
  | [] => none
  | c :: _ => (extract adj k nt c).map niceOf

/-- The vertex-by-vertex wrapper: vertices `0 … i-1`, one at a time: add `i` to every bag of the current nice
decomposition (width `k + 1`), then `improve`. -/
def decompose (adj : Adj) (k : ℕ) : ℕ → Option NT
  | 0 => some .leaf
  | i + 1 => (decompose adj k i).bind (fun t => improve adj k (NT.addEverywhere i t))

/-! ## counting (BP6) -/

/-- The bound on the number of characteristics. -/
def charBound (b kmax : ℕ) : ℕ := 2 ^ (16 * (b + 1) ^ 2 * (b + kmax + 2))

/-- Number of primitive steps of the algorithm, as an abstract count (list operations of the definitions each cost
`≤ poly(ℓ)` primitive steps on the encoded objects): the tables cost `≤ |nt| · charBound² · poly(ℓ)` (join is the
quadratic term: pairs of table entries), extraction costs `≤ |nt| · poly(ℓ) · (|V| + |nt|)`, niceification `O(size)`. -/
def stepBound (l k nodes verts : ℕ) : ℕ :=
  nodes * (charBound (l + 1) (k + 1)) ^ 2 * (l + 2) ^ 8 + (nodes + verts) ^ 3 * (l + 2) ^ 4

end Lax117284Proofs.Treewidth.Chars
