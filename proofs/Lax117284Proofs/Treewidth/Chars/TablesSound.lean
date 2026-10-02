import Lax117284Proofs.Treewidth.Chars.RealizeFinal
import Lax117284Proofs.Treewidth.Chars.TablesComplete
import Lax117284Proofs.Treewidth.Chars.IntroMono
import Lax117284Proofs.Treewidth.Chars.Join
import Lax117284Proofs.Treewidth.Chars.Forget
import Lax117284Proofs.Treewidth.Chars.Leaf
import Lax117284Proofs.Treewidth.Wrap.Decompose

/-!
# `tables_sound` and `tables_ne_nil_iff` (work package C6b)

Every table entry is dominated-realised by a partial decomposition.  Induction over the nice tree: leaf (the
empty tree), forget (`char_forget`, `forgetC_mono`), join (`joinC_mono`, `realize_join`), introduce
(`introC_mono`, `realize_intro`).

**Repair** (relative to `proofs-todo/Statements.lean`).  Old statement:

    theorem tables_sound {adj k} : ∀ {nt}, nt.Good adj → ∀ c ∈ tables adj k nt, ∃ t, PTD adj nt k t ∧ DomC (t.char nt.bag) c

New statement: two additional hypotheses `hs : adj.SymmOn W` and `nt.under ⊆ W`.  They are needed only for
`realize_intro`, which itself needs `∀ u ∈ c.under, adj u v = true → adj v u = true` (an edge `{v, w}` visible only as
`adj w v` is not seen by `nbrs adj v _`; see `Wrap/NOTES.md`).  The same two hypotheses are added to
`tables_ne_nil_iff`.  `tables_complete` needs no symmetry.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- `under` is exactly the vertex set of the underlying tree. -/
theorem NT.under_eq_vs : ∀ t : NT, t.under = t.vs := by
  intro t
  refine Finset.Subset.antisymm (NT.under_subset_vs t) ?_
  induction t with
  | leaf => simp
  | intro v c ih =>
    rw [NT.vs_intro]
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact NT.bag_subset_under (NT.intro v c) h
    · exact Finset.mem_insert_of_mem (ih h)
  | forget v c ih =>
    rw [NT.vs_forget]
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact NT.bag_subset_under (NT.forget v c) h
    · exact ih h
  | join a b iha ihb =>
    rw [NT.vs_join]
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact Finset.mem_union_left _ (NT.bag_subset_under a h)
    · rcases Finset.mem_union.1 h with h | h
      · exact Finset.mem_union_left _ (iha h)
      · exact Finset.mem_union_right _ (ihb h)

/-- The empty tree is a partial decomposition of the leaf. -/
theorem ptd_leaf (adj : Adj) (k : ℕ) : PTD adj .leaf k (.node ∅ []) := by
  refine ⟨⟨rfl, fun u v _ hu _ => absurd hu (by simp [NT.under]), by simp [RT.Conn, RT.ConnL]⟩, ?_⟩
  intro X hX
  simp [RT.bags, RT.bagsL] at hX
  simp [hX]

theorem tables_sound {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) :
    ∀ {nt : NT}, nt.Good adj → nt.under ⊆ W → ∀ c ∈ tables adj k nt,
    ∃ t, PTD adj nt k t ∧ DomC (t.char nt.bag) c
  | .leaf, _, _, c, hc => by
    simp only [tables, List.mem_singleton] at hc
    subst hc
    refine ⟨.node ∅ [], ptd_leaf adj k, ?_⟩
    have := char_leaf (adj := adj) (k := k) (.node ∅ []) (ptd_leaf adj k)
    simp only [NT.bag]
    rw [this]
    exact CT.DomC.refl _
  | .forget x c, hg, hW, q, hq => by
    simp only [tables, forgetTable, List.mem_dedup, List.mem_map] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    obtain ⟨t, ht, hd⟩ := tables_sound hs hg.2 hW q0 hq0
    refine ⟨t, ht, ?_⟩
    simp only [NT.bag]
    rw [char_forget c.bag x t ht.1.conn]
    exact forgetC_mono x hd
  | .join a b, hg, hW, q, hq => by
    have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
    obtain ⟨hab, -, hga, hgb, -⟩ := hg'
    have hWa : a.under ⊆ W := fun x hx => hW (Finset.mem_union_left _ hx)
    have hWb : b.under ⊆ W := fun x hx => hW (Finset.mem_union_right _ hx)
    simp only [tables, joinTable, List.mem_dedup, List.mem_flatMap] at hq
    obtain ⟨ca, hca, cb, hcb, hq⟩ := hq
    obtain ⟨ta, hta, hda⟩ := tables_sound hs hga hWa ca hca
    obtain ⟨tb, htb, hdb⟩ := tables_sound hs hgb hWb cb hcb
    rw [← hab] at hdb
    obtain ⟨d, hd, hdq⟩ := joinC_mono (k + 1) hda hdb q hq
    obtain ⟨t, ht, hdt⟩ := realize_join hg hta htb hd
    exact ⟨t, ht, hdt.trans hdq⟩
  | .intro v c, hg, hW, q, hq => by
    have hgc := hg.2.2.2
    have hWc : c.under ⊆ W := fun x hx => hW (Finset.mem_insert_of_mem hx)
    have hvW : v ∈ W := hW (Finset.mem_insert_self _ _)
    simp only [tables, introTable, List.mem_dedup, List.mem_flatMap] at hq
    obtain ⟨q0, hq0, hq⟩ := hq
    obtain ⟨t, ht, hd⟩ := tables_sound hs hgc hWc q0 hq0
    obtain ⟨d, hd', hdq⟩ := introC_mono (k + 1) v (nbrs adj v c.bag) hd q hq
    have hsym : ∀ u ∈ c.under, adj u v = true → adj v u = true := by
      intro u hu h
      rw [← hs u (hWc hu) v hvW]; exact h
    obtain ⟨t', ht', hdt⟩ := realize_intro hg hsym ht hd'
    exact ⟨t', ht', hdt.trans hdq⟩

/-- **The decision** (complete + sound). -/
theorem tables_ne_nil_iff {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) {nt : NT} (hg : nt.Good adj)
    (hW : nt.under ⊆ W) : tables adj k nt ≠ [] ↔ ∃ t, PTD adj nt k t := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨t, ht, -⟩ := tables_sound hs hg hW c hc
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩ h
    obtain ⟨c, hc, -⟩ := tables_complete hg t ht
    rw [h] at hc
    simp at hc

end Lax117284Proofs.Treewidth.Chars
