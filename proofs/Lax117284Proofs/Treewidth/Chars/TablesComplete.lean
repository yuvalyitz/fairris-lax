import Lax117284Proofs.Treewidth.Chars.IntroMain
import Lax117284Proofs.Treewidth.Chars.Join
import Lax117284Proofs.Treewidth.Chars.Forget
import Lax117284Proofs.Treewidth.Chars.Leaf
import Lax117284Proofs.Treewidth.Chars.Restrict

/-!
# `tables_complete` (work package C6a)

Every partial decomposition of a good nice tree is dominated (in the characteristic order) by an entry of `tables`.
Induction over the nice tree: leaf (`char_leaf`), forget (`char_forget`, `forgetC_mono`), join (`char_join_dom`,
`joinC_mono`, restriction), introduce (`char_intro_dom`, `introC_mono`, restriction).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem tables_complete {adj : Adj} {k : ℕ} : ∀ {nt : NT}, nt.Good adj → ∀ t, PTD adj nt k t →
    ∃ c ∈ tables adj k nt, DomC c (t.char nt.bag)
  | .leaf, _, t, h => by
    refine ⟨CT.start, by simp [tables], ?_⟩
    have := char_leaf t h
    simp only [NT.bag]
    rw [this]
    exact CT.DomC.refl _
  | .forget x c, hg, t, h => by
    have hgc := hg.2
    have h' : PTD adj c k t := h
    obtain ⟨c0, hc0, hd⟩ := tables_complete hgc t h'
    refine ⟨CT.forgetC x c0, ?_, ?_⟩
    · simp only [tables, forgetTable, List.mem_dedup, List.mem_map]
      exact ⟨c0, hc0, rfl⟩
    · simp only [NT.bag]
      rw [char_forget c.bag x t h.1.conn]
      exact forgetC_mono x hd
  | .join a b, hg, t, h => by
    have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
    obtain ⟨hab, -, hga, hgb, -⟩ := hg'
    obtain ⟨ca, hca, hda⟩ := tables_complete hga _ (PTD.restrict_join_left hg h)
    obtain ⟨cb, hcb, hdb⟩ := tables_complete hgb _ (PTD.restrict_join_right hg h)
    rw [← hab] at hdb
    obtain ⟨c1, hc1, hd1⟩ := char_join_dom hg h
    obtain ⟨c2, hc2, hd2⟩ := joinC_mono (k + 1) hda hdb c1 hc1
    refine ⟨c2, ?_, hd2.trans hd1⟩
    simp only [tables, joinTable, List.mem_dedup, List.mem_flatMap]
    exact ⟨ca, hca, cb, hcb, hc2⟩
  | .intro v c, hg, t, h => by
    have hgc := hg.2.2.2
    obtain ⟨c0, hc0, hd⟩ := tables_complete hgc _ (PTD.restrict_intro hg h)
    obtain ⟨c1, hc1, hd1⟩ := char_intro_dom hg h
    obtain ⟨c2, hc2, hd2⟩ := introC_mono (k + 1) v (nbrs adj v c.bag) hd c1 hc1
    refine ⟨c2, ?_, hd2.trans hd1⟩
    simp only [tables, introTable, List.mem_dedup, List.mem_flatMap]
    exact ⟨c0, hc0, hc2⟩

end Lax117284Proofs.Treewidth.Chars
