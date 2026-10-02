import Lax117284Proofs.Treewidth.Fun.E6bMath2

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6b (11): the first-hit facts of the extraction (from `extract_all`, `realIntro_spec`, `realJoin_spec`)

The Lean `findSome?` stops at the first candidate for which the branch condition holds *and* the recursive extraction succeeds.
These lemmas say that the second requirement is automatic: whenever the condition holds, the candidate returns `some`.  Hence
in the cost analysis the recursive calls happen for one candidate only (per side).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT

/-- extraction of a table entry succeeds -/
theorem extract_some {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) {nt : NT} (hg : nt.Good adj)
    (hW : nt.under ⊆ W) {c : CT} (hc : c ∈ tables adj k nt) :
    ∃ t, extract adj k nt c = some t ∧ PTD adj nt k t := by
  obtain ⟨⟨t, ht⟩, hsp⟩ := extract_all hs hg hW c hc
  exact ⟨t, ht, (hsp t ht).1⟩

theorem intro_hit_facts {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) {v : ℕ} {c : NT}
    (hg : (NT.intro v c).Good adj) (hW : (NT.intro v c).under ⊆ W) {cq target : CT} (hcq : cq ∈ tables adj k c)
    (hhit : target ∈ introC (k + 1) v (nbrs adj v c.bag) cq) :
    ∃ t0, extract adj k c cq = some t0 ∧ PTD adj c k t0 ∧
      (realIntro (k + 1) v (nbrs adj v c.bag) c.bag t0 target).isSome = true := by
  have hgc := hg.2.2.2
  have hWc : c.under ⊆ W := fun x hx => hW (Finset.mem_insert_of_mem hx)
  have hvW : v ∈ W := hW (Finset.mem_insert_self _ _)
  have hsym : ∀ u ∈ c.under, adj u v = true → adj v u = true := by
    intro u hu h
    rw [← hs u (hWc hu) v hvW]; exact h
  obtain ⟨⟨t0, ht0⟩, hsp⟩ := extract_all hs hgc hWc cq hcq
  obtain ⟨p0, d0⟩ := hsp t0 ht0
  obtain ⟨t', ht', -⟩ := realIntro_spec hg hsym p0 d0 hhit
  exact ⟨t0, ht0, p0, by simp [ht']⟩

theorem join_hit_facts {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) {a b : NT}
    (hg : (NT.join a b).Good adj) (hW : (NT.join a b).under ⊆ W) {ca cb target : CT}
    (hca : ca ∈ tables adj k a) (hcb : cb ∈ tables adj k b) (hhit : target ∈ CT.joinC (k + 1) ca cb) :
    ∃ ta tb, extract adj k a ca = some ta ∧ extract adj k b cb = some tb ∧ PTD adj a k ta ∧ PTD adj b k tb ∧
      (realJoin (k + 1) a.bag ta tb target).isSome = true := by
  have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
    (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
  obtain ⟨hab, -, hga, hgb, -⟩ := hg'
  have hWa : a.under ⊆ W := fun x hx => hW (Finset.mem_union_left _ hx)
  have hWb : b.under ⊆ W := fun x hx => hW (Finset.mem_union_right _ hx)
  obtain ⟨⟨ta, hta⟩, hspa⟩ := extract_all hs hga hWa ca hca
  obtain ⟨⟨tb, htb⟩, hspb⟩ := extract_all hs hgb hWb cb hcb
  obtain ⟨pa, da⟩ := hspa ta hta
  obtain ⟨pb, db⟩ := hspb tb htb
  rw [← hab] at db
  obtain ⟨t, ht, -⟩ := realJoin_spec hg pa pb da db hhit
  exact ⟨ta, tb, hta, htb, pa, pb, by simp [ht]⟩

end E6b
end Lax117284Proofs.Treewidth.Fun
