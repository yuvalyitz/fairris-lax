import Lax117284Proofs.Treewidth.Seq.RingTyp

/-!
# Realising a typical ring sum on exact sequences (S1)

`ringTyp (τ a) (τ b)` is computed from the *typical* forms; every element `d` of it is realised, up to
`≺`, by a genuine element `c ∈ a ⊕ b` of the exact sequences: `τ c ≺ d`.  This is
Lemma 3.13 applied to `a ≡ τ a`, `b ≡ τ b` (compare `ringTyp_cover_right`).
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- **Ring-sum realisation.**  If `d ∈ ringTyp (τ a) (τ b)` then some `c ∈ a ⊕ b` has `τ c ≺ d`.
(For `a = []` the hypothesis is void, since `ringTyp [] _ = ∅`.) -/
theorem ringSum_realise {a b d : List ℕ} (h : d ∈ ringTyp (typical a) (typical b)) :
    ∃ c, RingSum a b c ∧ Dom (typical c) d := by
  by_cases ha : a = []
  · subst ha
    simp [ringTyp, typical] at h
  · obtain ⟨c, hc, hd⟩ := ringTyp_cover_right ha h
    obtain ⟨c₀, hc₀, rfl⟩ := (mem_ringTyp ha).mp hc
    exact ⟨c₀, hc₀, hd⟩

end Lax117284Proofs.Treewidth.Seq
