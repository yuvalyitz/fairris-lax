import Lax117284Proofs.Treewidth.Size.Statements
import Lax117284Proofs.Treewidth.Chars.Extract
import Lax117284Proofs.Treewidth.Fun.ToValAlgSize

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6b (3): mathematics of the extraction cost analysis, part 1

* `char_wf` : the characteristic of a connected real tree covering the boundary is a well-formed characteristic
  (`Wf B (w+1)`) when the tree has width `w`.  (`extract` calls `realIntro`/`realJoin` on `t.char B` for the *real* trees
  it built, not on table entries, so the size bounds of the tables do not apply to them directly.)
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT

mutual
theorem loc_prof (B : Finset ℕ) : ∀ t : RT, Loc B (RT.prof B t)
  | .node X ks => by
    rw [RT.prof_node]
    refine ⟨Finset.inter_subset_right, typical_singleton _, by simp, ?_, ?_⟩
    · intro e he
      simp only [List.mem_singleton] at he
      subst he
      exact Finset.card_le_card Finset.inter_subset_left
    · rw [← RT.profL_eq_map B ks]
      exact locL_profL B ks
theorem locL_profL (B : Finset ℕ) : ∀ ks : List RT, LocL B (RT.profL B ks)
  | [] => trivial
  | k :: ks => ⟨loc_prof B k, locL_profL B ks⟩
end

/-- the characteristic of a connected real tree of width `w` covering `B` is well formed -/
theorem char_wf {B : Finset ℕ} {t : RT} {w : ℕ} (hc : t.Conn) (hB : B ⊆ t.verts) (hw : t.Width w) :
    (t.char B).Wf B (w + 1) := by
  unfold RT.char
  refine ⟨?_, good_norm _ (loc_prof B t) (RT.conn_prof B t hc), conn_norm _ (RT.conn_prof B t hc), ?_⟩
  · rw [verts_norm]
    ext u
    rw [RT.mem_verts_prof]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨hB h, h⟩
  · exact le_trans (maxEntry_norm_le _) (maxEntry_prof_le B t hw)

end E6b
end Lax117284Proofs.Treewidth.Fun
