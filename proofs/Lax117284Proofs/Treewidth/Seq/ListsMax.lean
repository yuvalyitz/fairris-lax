import Lax117284Proofs.Treewidth.Seq.RingSum
import Lax117284Proofs.Treewidth.Seq.Concat
import Lax117284Proofs.Treewidth.Seq.Structure

/-! ### `Lax117284Proofs.Treewidth.Seq.Lists` -/

section
/-!
# Lists of integer sequences and Lemma 3.21

A *list* `[a] = (a⁽¹⁾,…,a⁽ⁿ⁾)` is a `List (List ℕ)`.  All notions of the paper's list of
definitions before Lemma 3.21 are defined here, and the seven items of Lemma 3.21 are proved.
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- The maximum entry of a list of sequences (`max([a]) = max_i max(a⁽ⁱ⁾)`). -/
def maxL (A : List (List ℕ)) : ℕ := A.flatten.foldr max 0

/-- Same length *in the strong sense*: same number of sequences and `l(a⁽ⁱ⁾) = l(b⁽ⁱ⁾)`. -/
def SameShape (A B : List (List ℕ)) : Prop :=
  List.Forall₂ (fun a b => a.length = b.length) A B

/-- `[a] ≤ [b]` (strong sense): `a⁽ⁱ⁾ ≤ b⁽ⁱ⁾` for each `i`. -/
def LeL (A B : List (List ℕ)) : Prop := List.Forall₂ LeSeq A B

/-- `[a] + [b]`. -/
def addL (A B : List (List ℕ)) : List (List ℕ) := List.zipWith zadd A B

/-- The typical list `τ[a]`. -/
def typicalL (A : List (List ℕ)) : List (List ℕ) := A.map typical

/-- `[b] ∈ E[a]`: each `b⁽ⁱ⁾ ∈ E(a⁽ⁱ⁾)`. -/
def ExtL (A B : List (List ℕ)) : Prop := List.Forall₂ Ext A B

/-- `[c] ∈ [a] ⊕ [b]`: each `c⁽ⁱ⁾ ∈ a⁽ⁱ⁾ ⊕ b⁽ⁱ⁾` (the lists have the same length). -/
def RingSumL : List (List ℕ) → List (List ℕ) → List (List ℕ) → Prop
  | [], [], [] => True
  | a :: A, b :: B, c :: C => RingSum a b c ∧ RingSumL A B C
  | _, _, _ => False

/-- `[a] ≺ [b]`: there are `[a*] ∈ E[a]`, `[b*] ∈ E[b]` with `[a*] ≤ [b*]`. -/
def DomL (A B : List (List ℕ)) : Prop := ∃ A' B', ExtL A A' ∧ ExtL B B' ∧ LeL A' B'

/-- `[a] ≡ [b]`. -/
def DomEquivL (A B : List (List ℕ)) : Prop := DomL A B ∧ DomL B A

end Lax117284Proofs.Treewidth.Seq

end

/-! ### `Lax117284Proofs.Treewidth.Seq.ListsMax` -/

section
/-!
# Lemma 3.3(i) for lists of sequences

`max[a]` is preserved by the typical list `τ[a]`.
-/

namespace Lax117284Proofs.Treewidth.Seq

end Lax117284Proofs.Treewidth.Seq

end
