import Lax117284Proofs.Treewidth.Trees.Basic
import Lax117284Proofs.Treewidth.Trees.Bridge1To
import Lax117284Proofs.Treewidth.Trees.Bridge1From
import Lax117284Proofs.Treewidth.Trees.Bridge1Restrict

/-!
# Bridge 1: `RT ↔ Lax228581.Treewidth.TreeDecomposition`

* `hasTreewidthAtMost_iff_rt` : the concept's `HasTreewidthAtMost` in terms of `RT`.
  (→) roots the abstract tree (`exists_rooting`: parent function and depth from the distance to the root) and
  folds it into an `RT` by induction on the descendant sets (`exists_rt_sub`); `Conn` follows from the
  connectedness of the occurrence sets via the *exit lemma*.
  (←) builds the abstract tree on the nodes-as-paths of the `RT` (`RT.paths`), parent = drop the last step;
  connectedness of an occurrence set follows from its top element (`RT.top_exists`).
* `hasTreewidthAtMost_prefix` : monotonicity under induced subgraphs on initial segments, via `RT.restrict`.

Files: `Bridge1Root` (parent-function trees), `Bridge1Rt` (basic `RT` facts), `Bridge1To`, `Bridge1Paths`,
`Bridge1From`, `Bridge1Restrict`.
-/

namespace Lax117284Proofs.Treewidth.Trees

open Lax228581.Treewidth

/-- **Bridge 1 (statement side).**  `HasTreewidthAtMost` of the concept package, in terms of `RT`. -/
theorem hasTreewidthAtMost_iff_rt {n : ℕ} (G : SimpleGraph (Fin n)) (w : ℕ) :
    HasTreewidthAtMost G w ↔ ∃ t : RT, t.IsTD (liftGraph G) (Finset.range n) ∧ t.Width w :=
  ⟨rt_of_hasTreewidthAtMost, fun ⟨_, h1, h2⟩ => hasTreewidthAtMost_of_rt h1 h2⟩

end Lax117284Proofs.Treewidth.Trees
