import Lax117284Proofs.Treewidth.Seq.Lists
import Lax117284Proofs.Treewidth.Seq.Structure

/-!
# Lemma 3.3(i) for lists of sequences

`max[a]` is preserved by the typical list `τ[a]`.
-/

namespace Lax117284Proofs.Treewidth.Seq

theorem maxL_eq (A : List (List ℕ)) : maxL A = maxOf A.flatten := rfl

/-- `max τ[a] = max [a]` (Lemma 3.3(i), list version). -/
theorem maxL_typicalL (A : List (List ℕ)) : maxL (typicalL A) = maxL A := by
  unfold maxL typicalL
  change maxOf _ = maxOf _
  apply le_antisymm
  · apply maxOf_le
    intro x hx
    apply le_maxOf
    obtain ⟨a', ha', hx'⟩ := List.mem_flatten.mp hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    exact List.mem_flatten.mpr ⟨a, ha, mem_of_mem_typical hx'⟩
  · apply maxOf_le
    intro x hx
    obtain ⟨a, ha, hxa⟩ := List.mem_flatten.mp hx
    have := (typical_upper_iff a (maxOf (A.map typical).flatten)).mp (by
      intro y hy
      exact le_maxOf (List.mem_flatten.mpr ⟨typical a, List.mem_map.mpr ⟨a, ha, rfl⟩, hy⟩))
    exact this x hxa

end Lax117284Proofs.Treewidth.Seq
