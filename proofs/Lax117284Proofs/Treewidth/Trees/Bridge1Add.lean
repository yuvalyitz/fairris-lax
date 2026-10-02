import Lax117284Proofs.Treewidth.Trees.Basic
import Lax117284Proofs.Treewidth.Trees.Bridge1Rt

/-!
# Adding a vertex to every bag

`RT.addAll v t` inserts `v` into every bag of `t`.  If `t` decomposes `G[U]` with width `≤ k`, then
`addAll v t` decomposes `G[U ∪ {v}]` with width `≤ k + 1` (for arbitrary neighbours of `v`): the RT-level
statement of the wrapper's step (PLAN §e).
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace RT

mutual
/-- Insert `v` into every bag. -/
def addAll (v : ℕ) : RT → RT
  | .node b ks => .node (insert v b) (addAllL v ks)
def addAllL (v : ℕ) : List RT → List RT
  | [] => []
  | k :: ks => addAll v k :: addAllL v ks
end

end RT

end Lax117284Proofs.Treewidth.Trees
