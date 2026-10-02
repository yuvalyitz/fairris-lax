import Lax117284Proofs.Treewidth.Fun.E3MathA

/-!
# WP E3: facts about `wtopPlans` used by the cost analysis of `introPlans`
-/

namespace Lax117284Proofs.Treewidth.Fun

open ToVal Lax117284Proofs.Treewidth.Chars CT

/-- every vertex set in the output of `wtopPlans` lies in `verts` -/
theorem wtopPlans_sub (v : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    ∀ x ∈ wtopPlans v (node S y ks), x.2.2 ⊆ (node S y ks).verts := by
  intro x hx
  simp only [wtopPlans, List.mem_append, List.mem_map, List.mem_flatMap] at hx
  rcases hx with (⟨p, hp, rfl⟩ | ⟨f, _, p, hp, rfl⟩) | ⟨f, _, p, hp, rfl⟩
  · exact winPlans_sub v 0 _ p hp
  · exact winPlans_sub v f _ p hp
  · exact winPlans_sub v (f + 1) _ p hp

end Lax117284Proofs.Treewidth.Fun
