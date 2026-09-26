import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Card
import Lax228581.Treewidth

/-!
Trees given by a parent function. A finite type with a root, a parent for every node but the
root, and a depth that drops when passing to the parent, is a tree once every node is joined
to its parent; and a set of nodes that contains the parent of each of its members but one is
connected. These are the two facts a tree decomposition built by hand needs, and the archive's
notion of a tree decomposition (an abstract tree with an acyclicity proof) cannot be
exhibited without them.
-/

namespace Lax117284Proofs.ParentTree

open SimpleGraph

variable {V : Type} (r : V) (par : V → V) (depth : V → ℕ)

/-- The graph joining every node other than the root to its parent. -/
def graph : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => u ≠ r ∧ par u = v

variable {r par depth}

theorem adj_iff (hd : ∀ v, v ≠ r → depth (par v) < depth v) {u v : V} :
    (graph r par).Adj u v ↔ (u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u) := by
  simp only [graph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with ⟨hu, h⟩ | ⟨hu, h⟩ <;>
      exact absurd (hd u hu) (by rw [h]; exact lt_irrefl _)

theorem adj_par (hd : ∀ v, v ≠ r → depth (par v) < depth v) {v : V} (hv : v ≠ r) :
    (graph r par).Adj v (par v) := (adj_iff hd).2 (Or.inl ⟨hv, rfl⟩)

/-- Every node reaches the root by following parents. -/
theorem reachable_root (hd : ∀ v, v ≠ r → depth (par v) < depth v) :
    ∀ n, ∀ v, depth v = n → (graph r par).Reachable v r := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    by_cases hvr : v = r
    · rw [hvr]
    · have h1 := (adj_par hd hvr).reachable
      have h2 := ih (depth (par v)) (by rw [← hv]; exact hd v hvr) (par v) rfl
      exact h1.trans h2

theorem connected (hd : ∀ v, v ≠ r → depth (par v) < depth v) : (graph r par).Connected := by
  haveI : Nonempty V := ⟨r⟩
  exact ⟨fun a b => (reachable_root hd _ a rfl).trans (reachable_root hd _ b rfl).symm⟩

/-- **A parent function makes a tree.** -/
theorem isTree [Finite V] (hd : ∀ v, v ≠ r → depth (par v) < depth v) :
    (graph r par).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨connected hd, ?_⟩
  have hpar : ∀ v, v ≠ r → par v ≠ v := fun v hv h =>
    absurd (hd v hv) (by rw [h]; exact lt_irrefl _)
  let f : {v : V // v ≠ r} → (graph r par).edgeSet := fun v =>
    ⟨s(v.1, par v.1), (adj_par hd v.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨v, hv⟩ ⟨w, hw⟩ h
      have h' : s(v, par v) = s(w, par w) := congrArg Subtype.val h
      rcases Sym2.eq_iff.1 h' with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact Subtype.ext h1
      · exfalso
        have := hd v hv
        have := hd w hw
        rw [h2] at *
        rw [h1] at *
        omega
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ a b =>
        rcases (adj_iff hd).1 (by simpa using he) with ⟨ha, hab⟩ | ⟨hb, hba⟩
        · exact ⟨⟨a, ha⟩, Subtype.ext (by simp [f, hab])⟩
        · exact ⟨⟨b, hb⟩, Subtype.ext (by simp [f, hba, Sym2.eq_swap])⟩
  have h1 : Nat.card (graph r par).edgeSet = Nat.card {v : V // v ≠ r} :=
    (Nat.card_congr (Equiv.ofBijective f hf)).symm
  have h2 : Nat.card {v : V // v ≠ r} + 1 = Nat.card V := by
    have := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq r]
    have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨r⟩
    omega
  omega

/-- **A set containing the parent of each of its members but one is connected**, as a
subgraph of the tree. -/
theorem induce_connected (hd : ∀ v, v ≠ r → depth (par v) < depth v) {S : Set V} {t : V}
    (ht : t ∈ S) (hS : ∀ s ∈ S, s ≠ t → s ≠ r ∧ par s ∈ S) :
    ((graph r par).induce S).Connected := by
  have : Nonempty S := ⟨⟨t, ht⟩⟩
  have key : ∀ n, ∀ s : S, depth s.1 = n → ((graph r par).induce S).Reachable s ⟨t, ht⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hs
      by_cases hst : s.1 = t
      · have : s = ⟨t, ht⟩ := Subtype.ext hst
        rw [this]
      · obtain ⟨hsr, hps⟩ := hS s.1 s.2 hst
        have hadj : ((graph r par).induce S).Adj s ⟨par s.1, hps⟩ := by
          simpa using adj_par hd hsr
        have := ih (depth (par s.1)) (by rw [← hs]; exact hd s.1 hsr) ⟨par s.1, hps⟩ rfl
        exact hadj.reachable.trans this
  exact ⟨fun a b => (key _ a rfl).trans (key _ b rfl).symm⟩

end Lax117284Proofs.ParentTree
