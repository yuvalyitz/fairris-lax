import Lax117284Proofs.ClientsILPRaw

/-!
Independence of a subset for a type, position by position: the condition of `indepB` for all
`a, b < n` is the condition for all positions `q < n * n`.
-/

namespace Lax117284Proofs.ClientsILP

/-- The pair of positions is a violation at position `q = a * n + b`. -/
def badQ (n t S q : ℕ) : Prop :=
  q / n ≠ q % n ∧ S.testBit (q / n) = true ∧ S.testBit (q % n) = true ∧ t.testBit q = true

instance (n t S q : ℕ) : Decidable (badQ n t S q) := by unfold badQ; infer_instance

theorem indepB_iff_q (n t S : ℕ) :
    indepB n t S = true ↔ ∀ q < n * n, ¬ badQ n t S q := by
  simp only [indepB, decide_eq_true_eq, badQ]
  constructor
  · intro h q hq ⟨h1, h2, h3, h4⟩
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp at hq
      · exact h0
    have := h (q / n) (Nat.div_lt_of_lt_mul hq) (q % n) (Nat.mod_lt _ hn) h1 h2 h3
    have hq' : q / n * n + q % n = q := by
      have := Nat.div_add_mod q n; rw [Nat.mul_comm] at this; exact this
    rw [hq'] at this
    rw [this] at h4; exact absurd h4 (by simp)
  · intro h a ha b hb hab hsa hsb
    by_contra hcon
    have hcon' : t.testBit (a * n + b) = true := by simpa using hcon
    have hq : a * n + b < n * n := by
      have : (a + 1) * n ≤ n * n := Nat.mul_le_mul_right _ ha
      nlinarith
    have hn : 0 < n := by omega
    have e1 : (a * n + b) / n = a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb]; simp
    have e2 : (a * n + b) % n = b := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
    exact h (a * n + b) hq ⟨by rw [e1, e2]; exact hab, by rw [e1]; exact hsa,
      by rw [e2]; exact hsb, hcon'⟩

end Lax117284Proofs.ClientsILP
