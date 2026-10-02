import Lax117284Proofs.McisHard.Machine.FinalLayout

/-!
# The Cost of the Reduction to `H` Is Polynomial (WP9, Part 3)

`KaccM Sz l ≤ 4·10⁸ · (Sz + 1) · (l + 1)^5`.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Final

open Lax117284Proofs.McisHard Lax117284Proofs.McisHard.Acc Lax117284Proofs.McisHard.Print
open Lax117284Proofs.McisHard.Bit

theorem Kpoly (Sz l : ℕ) : KaccM Sz l ≤ 400000000 * (Sz + 1) * (l + 1) ^ 5 := by
  unfold KaccM KprintM Kbit
  obtain ⟨u, hu⟩ : ∃ u, u = l + 1 := ⟨_, rfl⟩
  rw [← hu]
  have hl : l ≤ u := by omega
  have hu1 : 1 ≤ u := by omega
  have p2 : u ≤ u ^ 2 := Nat.le_self_pow (by omega) u
  have p3 : u ^ 2 ≤ u ^ 3 := Nat.pow_le_pow_right hu1 (by omega)
  have p5 : u ^ 3 ≤ u ^ 5 := Nat.pow_le_pow_right hu1 (by omega)
  obtain ⟨V, hV⟩ : ∃ V, V = 400 * u ^ 2 := ⟨_, rfl⟩
  rw [← hV]
  have hX : 128 * l + 1500 + 2 + 10 + 4 ≤ 1644 * u := by omega
  have hA : (128 * l + 1500 + 2 + 10 + 4) * V + 6 + 10 + 4 ≤ 657620 * u ^ 3 := by
    have h1 : (128 * l + 1500 + 2 + 10 + 4) * V ≤ (1644 * u) * (400 * u ^ 2) := by
      rw [hV]; exact Nat.mul_le_mul hX le_rfl
    nlinarith
  have hB : (((128 * l + 1500 + 2 + 10 + 4) * V + 6 + 10 + 4) * V + 6) ≤ 263048006 * u ^ 5 := by
    have h1 : ((128 * l + 1500 + 2 + 10 + 4) * V + 6 + 10 + 4) * V ≤ (657620 * u ^ 3) * V :=
      Nat.mul_le_mul hA le_rfl
    have h2 : (657620 * u ^ 3) * V = 263048000 * u ^ 5 := by rw [hV]; ring
    nlinarith
  have hC : (120 + 64 * l + 4) * l + 6 ≤ 190 * u ^ 2 := by nlinarith
  have hs : 1 ≤ (Sz + 1) := by omega
  have hD : 200 + ((120 + 64 * l + 4) * l + 6) + (40 + (48 * Sz + 50) + (48 * Sz + 50) +
      (((128 * l + 1500 + 2 + 10 + 4) * V + 6 + 10 + 4) * V + 6)) ≤
      (263048006 + 190 + 400) * (Sz + 1) * u ^ 5 + 200 * (Sz + 1) := by nlinarith
  nlinarith

/-- **The reduction to normal-form Multicoloured Independent Set is polynomial-time computable**: a word RAM
program on the zeros and ones of its input (tokenizer, the check of the positions, and the matrix of `H`,
bit by bit, each bit from the ports of the two vertices), transferred to a Turing machine. -/
theorem reduceMcis_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id id reduceMcis) :=
  Lax117284Proofs.Machine.WrapTFinal.polyTimeE W layoutM com_ok rfl (by simp [layoutM]) 400000000 5
    (by omega) (fun Sz l => Kpoly Sz l) (fun Sz => by
      show 1 ≤ 400000000 * (Sz + 1)
      omega)

end Lax117284Proofs.McisHard.Final
