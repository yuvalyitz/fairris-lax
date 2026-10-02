import Lax117284Proofs.Treewidth.Chars.TablesIntroB
import Lax117284Proofs.Treewidth.Chars.TablesComplete
import Lax117284Proofs.Treewidth.Chars.CountTables

/-!
# `tables_wf` (work package C6a) and the unconditional table-size bounds

* `introC_wf` : introducing a new vertex `v ∉ B` keeps characteristics well-formed (`Wf B kmax → Wf (insert v B) kmax`),
  via the description `IR` of the results and `ir_aux` (`TablesIntroB`), then `good_norm`/`conn_norm`/`verts_norm`.
* `tables_wf`, `tablesWf : TablesWf` (the hypothesis of `CountTables`), and the unconditional
  `tables_length_le'`, `tables_length_le_of_width'`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem CT.introC_wf {B : Finset ℕ} {kmax v : ℕ} {N : Finset ℕ} {a c : CT} (hvB : v ∉ B) (ha : Wf B kmax a)
    (hc : c ∈ introC kmax v N a) : Wf (insert v B) kmax c := by
  obtain ⟨r, hr, rfl, hk⟩ := mem_introC.1 hc
  have hv : v ∉ verts a := by rw [ha.verts_eq]; exact hvB
  obtain ⟨lr, cr, vr, -, -⟩ := ir_aux v B hvB N hr (loc_of_good a ha.good) ha.conn hv
  refine ⟨?_, good_norm r lr cr, conn_norm r cr, hk⟩
  rw [verts_norm]
  ext u
  rw [Finset.mem_insert, vr, ha.verts_eq]

theorem wf_start (kmax : ℕ) : Wf ∅ kmax CT.start := by
  refine ⟨by simp [CT.start, verts, vertsL], ?_, ?_, by simp [CT.start, maxEntry, maxEntryL]⟩
  · refine ⟨Finset.Subset.refl _, typical_singleton 0, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [CT.start, GoodL]
  · simp [CT.start, Conn, ConnL]

/-- **The table entries are well-formed characteristics of the bag.** -/
theorem tables_wf {adj : Adj} {k : ℕ} : ∀ {nt : NT}, nt.Good adj → ∀ c ∈ tables adj k nt,
    CT.Wf nt.bag (k + 1) c
  | .leaf, _, c, hc => by
    simp only [tables, List.mem_singleton] at hc
    subst hc
    exact wf_start _
  | .forget x c, hg, q, hq => by
    simp only [tables, forgetTable, List.mem_dedup, List.mem_map] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    exact CT.forgetC_wf (tables_wf hg.2 q0 hq0)
  | .join a b, hg, q, hq => by
    have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
    obtain ⟨hab, -, hga, hgb, -⟩ := hg'
    simp only [tables, joinTable, List.mem_dedup, List.mem_flatMap] at hq
    obtain ⟨ca, hca, cb, hcb, hq⟩ := hq
    have h1 := tables_wf hga ca hca
    have h2 := tables_wf hgb cb hcb
    rw [← hab] at h2
    exact CT.joinC_wf h1 h2 hq
  | .intro v c, hg, q, hq => by
    obtain ⟨hvB, -, -, hgc⟩ := hg
    simp only [tables, introTable, List.mem_dedup, List.mem_flatMap] at hq
    obtain ⟨q0, hq0, hq⟩ := hq
    exact CT.introC_wf hvB (tables_wf hgc q0 hq0) hq

/-- The hypothesis of the counting results holds. -/
theorem tablesWf : TablesWf := fun hg c hc => tables_wf hg c hc

/-- If a nice tree has width `≤ l`, every table of it is small (unconditional). -/
theorem tables_length_le_of_width' {adj : Adj} {k l : ℕ} {nt : NT} (hg : nt.Good adj) (hw : nt.toRT.Width l) :
    (tables adj k nt).length ≤ charBound (l + 1) (k + 1) :=
  tables_length_le_of_width tablesWf hg hw

end Lax117284Proofs.Treewidth.Chars
