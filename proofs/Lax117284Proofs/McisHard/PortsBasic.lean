import Lax117284Proofs.McisHard.Defs

/-!
# WP2 (Ports), Part 1: the Gadget Facts and the Adjacency Description of `portGraph`
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Proved

open Lax117284Proofs.McisHard

theorem gad_deg : ∀ t < 7, ((Finset.range 7).filter (gadAdj t)).card = if t = 0 then 4 else 5 := by
  decide

theorem gad_alpha : ∀ s : Finset ℕ, s ⊆ Finset.range 7 → (∀ a ∈ s, ∀ b ∈ s, ¬ gadAdj a b) →
    s.card ≤ 2 := by
  intro s hs
  have : s ∈ (Finset.range 7).powerset := Finset.mem_powerset.2 hs
  revert s
  have key : ∀ s ∈ (Finset.range 7).powerset,
      (∀ a ∈ s, ∀ b ∈ s, ¬ gadAdj a b) → s.card ≤ 2 := by decide +kernel
  intro s hs h1 h2
  exact key s h1 h2


theorem portAdjN_symm {S : ℕ} {R : ℕ → ℕ → ℕ → ℕ → Prop} (h : IsPortRel S R) {u v : ℕ}
    (huv : portAdjN R u v) : portAdjN R v u := by
  unfold portAdjN at huv ⊢
  rcases huv with ⟨h1, h2, j, j', hR⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ |
    ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h2, h1, j', j, h.symm hR⟩
  · exact Or.inr (Or.inr (Or.inl ⟨h2, h1, h3.symm, h4, h5⟩))
  · exact Or.inr (Or.inl ⟨h2, h1, h3.symm, h4, h5⟩)
  · refine Or.inr (Or.inr (Or.inr ⟨h2, h1, ?_⟩))
    rcases h3 with ⟨a, b, c⟩ | ⟨a, b, c⟩
    · exact Or.inl ⟨a.symm, b.symm, gadAdj_symm c⟩
    · exact Or.inr ⟨b, a, h.symm c⟩

theorem portAdjN_irrefl {S : ℕ} {R : ℕ → ℕ → ℕ → ℕ → Prop} (h : IsPortRel S R) (u : ℕ) :
    ¬ portAdjN R u u := by
  unfold portAdjN
  rintro (⟨-, -, j, j', hR⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨-, -, ⟨-, -, hg⟩ | ⟨-, -, hR⟩⟩)
  · exact h.ne hR rfl
  · exact h2 h1
  · exact h1 h2
  · exact (by unfold gadAdj at hg; omega : ¬ gadAdj _ _) hg
  · exact h.ne hR rfl

theorem portGraph_adj {R : ℕ → ℕ → ℕ → ℕ → Prop} {S : ℕ} (h : IsPortRel S R)
    (u v : Fin (S * 36)) : (portGraph R S).Adj u v ↔ portAdjN R u.val v.val := by
  unfold portGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h1 | h1⟩
    · exact h1
    · exact portAdjN_symm h h1
  · intro h1
    refine ⟨fun e => portAdjN_irrefl h u.val (by rw [← e] at h1; exact h1), Or.inl h1⟩

end Lax117284Proofs.McisHard.Proved
