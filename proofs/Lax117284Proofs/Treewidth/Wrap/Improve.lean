import Lax117284Proofs.Treewidth.Chars.Extract
import Lax117284Proofs.Treewidth.Chars.Restrict
import Lax117284Proofs.Treewidth.Wrap.Nice
import Lax117284Proofs.Treewidth.Wrap.Decompose

/-!
# `improve_correct` and the unconditional `decompose` (work package C6b)

* `improve_correct` : `improve adj k nt` is `none` iff `G[U]` has no tree decomposition of width `≤ k`, and otherwise
  a nice decomposition of `G[U]` of width `≤ k`.  Proof: `good_of_isNiceTD`, `tables_ne_nil_iff` (decision),
  `extract_spec` (a real decomposition), `niceOf_spec` (Kloks).
* `improveSpec` : `ImproveSpec adj W` holds whenever `adj.SymmOn W`.
* `decompose_correct_final`, `decompose_words_final` : the wrapper's specification without the `himp` hypothesis.

**Repair** (relative to `proofs-todo/Statements.lean`): `improve_correct` gets `hs : adj.SymmOn W` and `hU : U ⊆ W`
(a nice decomposition of `G[U]` only refers to vertices of `U`; see `Wrap/NOTES.md`: without symmetry it is false).
`decompose_words_final` needs no new hypothesis beyond the printed `hadj` (which implies symmetry on `range n`).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Trees Lax117284Proofs.Treewidth.Trees.NT

theorem improve_correct {adj : Adj} {W : Finset ℕ} (hs : adj.SymmOn W) {U : Finset ℕ} (hU : U ⊆ W) {nt : NT}
    {l : ℕ} (hnt : nt.IsNiceTD adj.graph U l) (k : ℕ) :
    (improve adj k nt = none ↔ ¬ HasTW adj U k) ∧
    (∀ t', improve adj k nt = some t' → t'.IsNiceTD adj.graph U k) := by
  have hg : nt.Good adj := good_of_isNiceTD hnt
  have hunder : nt.under = U := by rw [NT.under_eq_vs]; exact hnt.2.1.verts_eq
  have hW : nt.under ⊆ W := hunder ▸ hU
  have hptd : ∀ t, PTD adj nt k t ↔ (t.IsTD adj.graph U ∧ t.Width k) := by
    intro t; unfold PTD; rw [hunder]
  have hne := tables_ne_nil_iff (k := k) hs hg hW
  have hhas : HasTW adj U k ↔ ∃ t, PTD adj nt k t := by
    unfold HasTW; simp only [hptd]
  refine ⟨?_, ?_⟩
  · rw [hhas, ← hne]
    unfold improve
    cases hT : tables adj k nt with
    | nil => simp
    | cons c cs =>
      obtain ⟨t, ht, -⟩ := extract_spec (k := k) hs hg hW c (by simp [hT])
      simp [ht]
  · intro t' ht'
    unfold improve at ht'
    cases hT : tables adj k nt with
    | nil => simp [hT] at ht'
    | cons c cs =>
      obtain ⟨t, ht, hp, -⟩ := extract_spec (k := k) hs hg hW c (by simp [hT])
      simp only [hT, ht, Option.map_some, Option.some.injEq] at ht'
      subst ht'
      have := (hptd t).1 hp
      exact niceOf_spec this.1 this.2

theorem improveSpec {adj : Adj} {W : Finset ℕ} (hs : adj.SymmOn W) : ImproveSpec adj W :=
  fun _ _ _ k hU hnt => improve_correct hs hU hnt k

theorem decompose_correct_final (adj : Adj) (W : Finset ℕ) (hs : adj.SymmOn W) (k : ℕ) :
    ∀ i, Finset.range i ⊆ W →
    (decompose adj k i = none ↔ ¬ HasTW adj (Finset.range i) k) ∧
    (∀ t, decompose adj k i = some t → t.IsNiceTD adj.graph (Finset.range i) k) :=
  decompose_correct adj W (improveSpec hs) k

/-- **The word-level statement of `decompose`, unconditional** (only the encoding hypothesis `hadj`). -/
theorem decompose_words_final {n : ℕ} (G : SimpleGraph (Fin n)) (adj : Adj)
    (hadj : ∀ u v : Fin n, adj u.val v.val = true ↔ G.Adj u v ∨ G.Adj v u) (k : ℕ) :
    (decompose adj k n = none ↔ ¬ Lax228581.Treewidth.HasTreewidthAtMost G k) ∧
    (∀ t, decompose adj k n = some t → Lax117284.GraphWords.NiceDecomposition G k t.encode) :=
  decompose_words G adj hadj (improveSpec (symmOn_of_encodes hadj)) k

end Lax117284Proofs.Treewidth.Chars
