import Lax117284Proofs.Treewidth.Seq.Ext

/-!
# `Ext` is the paper's Def. 3.6

The paper writes `E(a) = {a* | ∃ 1 = t₁ < t₂ < … < t_{n+1} ∀ i ∀ t_i ≤ k < t_{i+1} [a*(k) = a(i)]}`
(with `t_{n+1} = l(a*) + 1`).  In `0`-based form this is `ExtIdx`; `ext_iff_extIdx` shows that it
coincides with the recursive `Ext`.
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- The paper's definition of `a' ∈ E(a)`, `0`-indexed: breakpoints `t 0 = 0 < t 1 < … < t n =
l(a')` such that `a'` is constantly `a_i` on `[t i, t (i+1))`. -/
def ExtIdx (a w : List ℕ) : Prop :=
  ∃ t : ℕ → ℕ, t 0 = 0 ∧ (∀ i, i < a.length → t i < t (i + 1)) ∧ t a.length = w.length ∧
    ∀ i, i < a.length → ∀ k, t i ≤ k → k < t (i + 1) → ent w k = ent a i

end Lax117284Proofs.Treewidth.Seq
