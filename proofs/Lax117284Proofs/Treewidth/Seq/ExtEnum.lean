import Lax117284Proofs.Treewidth.Seq.Ext
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Card

/-!
# Enumerating extensions of a fixed length (Lemma 3.16)
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- All extensions of `a` of length exactly `k` (computable). -/
def extLen : List ℕ → ℕ → Finset (List ℕ)
  | [], 0 => {[]}
  | [], _ + 1 => ∅
  | _ :: _, 0 => ∅
  | x :: a, k + 1 => ((extLen (x :: a) k) ∪ (extLen a k)).image (List.cons x)

end Lax117284Proofs.Treewidth.Seq
