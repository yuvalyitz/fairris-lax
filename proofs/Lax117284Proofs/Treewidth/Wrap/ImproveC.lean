import Lax117284Proofs.Treewidth.Chars.Extract
import Lax117284Proofs.Treewidth.Chars.Restrict
import Lax117284Proofs.Treewidth.Wrap.Nice
import Lax117284Proofs.Treewidth.Wrap.Decompose
import Lax117284Proofs.Treewidth.Wrap.CompressSize

/-! ### `Lax117284Proofs.Treewidth.Wrap.Improve` -/

section
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

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Wrap.ImproveC` -/

section
/-!
# `improveC`, `decomposeC`: the polynomial-size wrapper (work package P0)

`improveC` is `improve` with a `compress` between `extract` and `niceOf`.  The machine layer runs
`improveC` / `decomposeC` (not `improve` / `decompose`): the latter feed an arbitrary extracted tree to the
next round, so the nice trees grow by a factor ≈ 2.2 per round.

* `improveC_correct`       : as `improve_correct`, plus the size bound `(|U| + 2)²` of the result;
* `decomposeC_correct_final`, `decomposeC_words_final` : as for `decompose` (same conclusions);
* `decomposeC_size_le`     : after round `i` the nice tree has at most `(i + 2)²` nodes.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Trees Lax117284Proofs.Treewidth.Trees.NT

/-- **`improveC`**: `improve` with the extracted decomposition compressed before Kloks' conversion. -/
def improveC (adj : Adj) (k : ℕ) (nt : NT) : Option NT :=
  match tables adj k nt with
  | [] => none
  | c :: _ => (extract adj k nt c).map (fun t => niceOf (compress t))

/-- The vertex-by-vertex wrapper with `improveC`. -/
def decomposeC (adj : Adj) (k : ℕ) : ℕ → Option NT
  | 0 => some .leaf
  | i + 1 => (decomposeC adj k i).bind (fun t => improveC adj k (NT.addEverywhere i t))

theorem improveC_correct {adj : Adj} {W : Finset ℕ} (hs : adj.SymmOn W) {U : Finset ℕ} (hU : U ⊆ W) {nt : NT}
    {l : ℕ} (hnt : nt.IsNiceTD adj.graph U l) (k : ℕ) :
    (improveC adj k nt = none ↔ ¬ HasTW adj U k) ∧
    (∀ t', improveC adj k nt = some t' →
      t'.IsNiceTD adj.graph U k ∧ t'.size ≤ (U.card + 2) * (U.card + 2)) := by
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
    unfold improveC
    cases hT : tables adj k nt with
    | nil => simp
    | cons c cs =>
      obtain ⟨t, ht, -⟩ := extract_spec (k := k) hs hg hW c (by simp [hT])
      simp [ht]
  · intro t' ht'
    unfold improveC at ht'
    cases hT : tables adj k nt with
    | nil => simp [hT] at ht'
    | cons c cs =>
      obtain ⟨t, ht, hp, -⟩ := extract_spec (k := k) hs hg hW c (by simp [hT])
      simp only [hT, ht, Option.map_some, Option.some.injEq] at ht'
      subst ht'
      have := (hptd t).1 hp
      have hc := compress_isTD this.1
      refine ⟨niceOf_spec hc (compress_width this.2), ?_⟩
      have h1 := niceOf_size_le hc.conn
      have h2 := compress_size_le this.1.conn
      have hv : (compress t).verts = U := hc.verts_eq
      rw [hv] at h1
      have hv' : t.verts = U := this.1.verts_eq
      rw [hv'] at h2
      calc (niceOf (compress t)).size ≤ (U.card + 2) * ((compress t).size + 1) := h1
        _ ≤ (U.card + 2) * (U.card + 2) := Nat.mul_le_mul_left _ (by omega)

/-- The conclusion of `improveC_correct`, for all vertex sets inside `W`. -/
def ImproveCSpec (adj : Adj) (W : Finset ℕ) : Prop :=
  ∀ (U : Finset ℕ) (nt : NT) (l k : ℕ), U ⊆ W → nt.IsNiceTD adj.graph U l →
    (improveC adj k nt = none ↔ ¬ HasTW adj U k) ∧
    (∀ t', improveC adj k nt = some t' → t'.IsNiceTD adj.graph U k ∧ t'.size ≤ (U.card + 2) * (U.card + 2))

/-- Correctness and the size bound of `decomposeC`, on `range i ⊆ W`. -/
theorem decomposeC_correct_final (adj : Adj) (W : Finset ℕ) (hs : adj.SymmOn W) (k : ℕ) :
    ∀ i, Finset.range i ⊆ W →
    (decomposeC adj k i = none ↔ ¬ HasTW adj (Finset.range i) k) ∧
    (∀ t, decomposeC adj k i = some t → t.IsNiceTD adj.graph (Finset.range i) k ∧
      t.size ≤ (i + 2) * (i + 2)) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨by simp [decomposeC, hasTW_empty], ?_⟩
    intro t ht
    simp only [decomposeC, Option.some.injEq] at ht
    subst ht
    refine ⟨⟨trivial, ⟨rfl, fun u v _ hu _ => absurd hu (by simp), by simp [NT.toRT, RT.Conn, RT.ConnL]⟩,
      by intro X hX; simp [NT.toRT, RT.bags, RT.bagsL] at hX; simp [hX]⟩, by simp [NT.size]⟩
  | succ i ih =>
    intro hW
    have hWi : Finset.range i ⊆ W := (Finset.range_subset_range.2 (Nat.le_succ i)).trans hW
    obtain ⟨ih1, ih2⟩ := ih hWi
    cases hd : decomposeC adj k i with
    | none =>
      have hn : ¬ HasTW adj (Finset.range i) k := ih1.1 hd
      refine ⟨by simp [decomposeC, hd]; exact fun h => hn (hasTW_mono (Finset.range_subset_range.2 (Nat.le_succ i)) h),
        by simp [decomposeC, hd]⟩
    | some t =>
      have ht := (ih2 t hd).1
      have hadd := addEverywhere_isNiceTD (v := i) ht (by simp)
      rw [← Finset.range_add_one] at hadd
      obtain ⟨j1, j2⟩ := improveC_correct hs hW hadd k
      simp only [decomposeC, hd, Option.bind_some]
      refine ⟨j1, fun t' ht' => ?_⟩
      obtain ⟨a, b⟩ := j2 t' ht'
      refine ⟨a, ?_⟩
      simpa using b

/-- **The word-level statement of `decomposeC`**: the same conclusion as `decompose_words_final`. -/
theorem decomposeC_words_final {n : ℕ} (G : SimpleGraph (Fin n)) (adj : Adj)
    (hadj : ∀ u v : Fin n, adj u.val v.val = true ↔ G.Adj u v ∨ G.Adj v u) (k : ℕ) :
    (decomposeC adj k n = none ↔ ¬ Lax228581.Treewidth.HasTreewidthAtMost G k) ∧
    (∀ t, decomposeC adj k n = some t → Lax117284.GraphWords.NiceDecomposition G k t.encode) := by
  obtain ⟨h1, h2⟩ := decomposeC_correct_final adj (Finset.range n) (symmOn_of_encodes hadj) k n
    (Finset.Subset.refl _)
  refine ⟨by rw [h1, hasTW_iff_hasTreewidthAtMost hadj], fun t ht => ?_⟩
  have := (h2 t ht).1
  have hcong : ∀ u ∈ Finset.range n, ∀ v ∈ Finset.range n, adj.graph.Adj u v ↔ (liftGraph G).Adj u v :=
    fun u hu v hv => graph_adj_of_encodes hadj (Finset.mem_range.1 hu) (Finset.mem_range.1 hv)
  exact niceDecomposition_encode ⟨this.1, (isTD_congr hcong).1 this.2.1, this.2.2⟩

end Lax117284Proofs.Treewidth.Chars

end
