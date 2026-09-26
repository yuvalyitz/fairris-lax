import Lax117284.Lemma14
import Lax117284.Theorem7

/-!
The shape of the two gadget instances: how many days they have, that the processing times of
Theorem 7's instance are all equal, and that no fairness parameter of Lemma 14's instance
exceeds its number of days.
-/

namespace Lax117284Proofs.Structural

open Lax117284.Scheduling

/--
---
conclusion: Lax117284.Theorem7.inst_days
---
The construction names three days.
-/
theorem inst_days (φ : Lax117284.BoundedSat.Formula) :
    (Lax117284.Theorem7.inst φ).days = 3 := rfl

/--
---
conclusion: Lax117284.Theorem7.inst_p_eq
---
Every processing time of the construction is `2`.
-/
theorem inst_p_eq (φ : Lax117284.BoundedSat.Formula)
    (i i' : Fin (Lax117284.Theorem7.inst φ).days)
    (j j' : Fin (Lax117284.Theorem7.inst φ).clients) :
    (Lax117284.Theorem7.inst φ).p i j = (Lax117284.Theorem7.inst φ).p i' j' := rfl

/--
---
conclusion: Lax117284.Lemma14.kvec_le_days
---
The dummy client is required on every day, the two interaction clients on half the edge
days each, and every other client once; a client other than those three exists only if the
graph has a colour class, and then the instance has a day.
-/
theorem kvec_le_days (G : Lax117284.MulticolouredIndepSet.Instance)
    (j : Fin (Lax117284.Lemma14.inst G).clients) :
    Lax117284.Lemma14.kvec G j ≤ (Lax117284.Lemma14.inst G).days := by
  show (if (j : ℕ) = 0 then Lax117284.Lemma14.dayCount G
      else if (j : ℕ) = 1 ∨ (j : ℕ) = 2 then G.edgeCount / 2 else 1)
    ≤ Lax117284.Lemma14.dayCount G
  have hd : Lax117284.Lemma14.dayCount G = G.colours * (G.size + 1) + G.edgeCount := rfl
  split_ifs with h1 h2
  · exact Nat.le_refl _
  · have := Nat.div_le_self G.edgeCount 2
    omega
  · have hj : (j : ℕ) < 3 + G.colours + G.vertices + G.vertices * Lax117284.Lemma14.deg G :=
      j.isLt
    have hv : G.vertices = G.colours * G.size := rfl
    have hpos : 0 < G.colours := by
      rcases Nat.eq_zero_or_pos G.colours with h0 | h0
      · rw [h0, Nat.zero_mul] at hv
        rw [hv, Nat.zero_mul] at hj
        omega
      · exact h0
    have h1' : 1 ≤ G.colours * (G.size + 1) :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    omega

end Lax117284Proofs.Structural
