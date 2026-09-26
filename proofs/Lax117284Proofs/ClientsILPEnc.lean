import Lax117284Proofs.ClientsILPFeas

/-!
Day types and subsets of the clients as numbers: the bijections with `Fin (2 ^ (n * n))` and
`Fin (2 ^ n)`, and the sums re-indexed along them.
-/

namespace Lax117284Proofs.ClientsILP

open Finset

variable (n : ℕ)

/-- The type (conflict relation) whose bit `a * n + b` is that of `r`. -/
def tyOf (r : ℕ) : Fin n → Fin n → Bool := fun a b => r.testBit (a.val * n + b.val)

/-- The bit function of a type. -/
def tyBits (σ : Fin n → Fin n → Bool) (q : ℕ) : Bool :=
  if h : q < n * n then σ ⟨q / n, Nat.div_lt_of_lt_mul h⟩ ⟨q % n, Nat.mod_lt _ (by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · simp at h
    · exact h0)⟩ else false

/-- The number of a type. -/
def numOf (σ : Fin n → Fin n → Bool) : ℕ := bitsNum (tyBits n σ) (n * n)

theorem numOf_lt (σ : Fin n → Fin n → Bool) : numOf n σ < nT n := bitsNum_lt _ _

theorem tyOf_numOf (σ : Fin n → Fin n → Bool) : tyOf n (numOf n σ) = σ := by
  funext a b
  simp only [tyOf, numOf, testBit_bitsNum]
  have hn : 0 < n := a.pos
  have hq : a.val * n + b.val < n * n := by
    have : (a.val + 1) * n ≤ n * n := Nat.mul_le_mul_right _ a.isLt
    nlinarith [b.isLt]
  rw [if_pos hq]
  simp only [tyBits, dif_pos hq]
  have e1 : (a.val * n + b.val) / n = a.val := by
    rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt b.isLt]; simp
  have e2 : (a.val * n + b.val) % n = b.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]
  congr 1 <;> exact Fin.ext (by simp [e1, e2])

theorem numOf_tyOf {r : ℕ} (hr : r < nT n) : numOf n (tyOf n r) = r := by
  have h1 := eq_bitsNum (x := r) (P := n * n) hr
  refine Eq.trans ?_ h1.symm
  refine bitsNum_congr fun q hq => ?_
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at hq
    · exact h0
  simp only [tyBits, dif_pos hq, tyOf]
  have : q / n * n + q % n = q := by
    have := Nat.div_add_mod q n
    rw [Nat.mul_comm] at this; exact this
  simp [this]

/-- The subset whose members are the clients `j` with bit `j` of `s` set. -/
def setOf (s : ℕ) : Finset (Fin n) := Finset.univ.filter fun j => s.testBit j.val

/-- The bit function of a subset. -/
def setBits (S : Finset (Fin n)) (q : ℕ) : Bool := decide (∃ h : q < n, (⟨q, h⟩ : Fin n) ∈ S)

/-- The number of a subset. -/
def numSet (S : Finset (Fin n)) : ℕ := bitsNum (setBits n S) n

theorem numSet_lt (S : Finset (Fin n)) : numSet n S < nZ n := bitsNum_lt _ _

theorem setOf_numSet (S : Finset (Fin n)) : setOf n (numSet n S) = S := by
  ext j
  simp only [setOf, numSet, Finset.mem_filter, Finset.mem_univ, true_and, testBit_bitsNum,
    setBits, if_pos j.isLt]
  simp

theorem numSet_setOf {s : ℕ} (hs : s < nZ n) : numSet n (setOf n s) = s := by
  have h1 := eq_bitsNum (x := s) (P := n) hs
  refine Eq.trans ?_ h1.symm
  refine bitsNum_congr fun q hq => ?_
  simp [setBits, setOf, hq]

/-- Types are numbers below `nT n`. -/
def eqT : (Fin n → Fin n → Bool) ≃ Fin (nT n) where
  toFun σ := ⟨numOf n σ, numOf_lt n σ⟩
  invFun r := tyOf n r.val
  left_inv σ := tyOf_numOf n σ
  right_inv r := Fin.ext (numOf_tyOf n r.isLt)

/-- Subsets are numbers below `nZ n`. -/
def eqS : Finset (Fin n) ≃ Fin (nZ n) where
  toFun S := ⟨numSet n S, numSet_lt n S⟩
  invFun s := setOf n s.val
  left_inv S := setOf_numSet n S
  right_inv s := Fin.ext (numSet_setOf n s.isLt)

theorem sum_types (F : (Fin n → Fin n → Bool) → ℕ) :
    ∑ σ : Fin n → Fin n → Bool, F σ = ∑ r ∈ range (nT n), F (tyOf n r) := by
  rw [← Fintype.sum_equiv (eqT n).symm (fun r => F ((eqT n).symm r)) F (fun r => rfl)]
  rw [← Fin.sum_univ_eq_sum_range (fun r => F (tyOf n r))]
  rfl

theorem sum_sets (G : Finset (Fin n) → ℕ) :
    ∑ S : Finset (Fin n), G S = ∑ s ∈ range (nZ n), G (setOf n s) := by
  rw [← Fintype.sum_equiv (eqS n).symm (fun s => G ((eqS n).symm s)) G (fun r => rfl)]
  rw [← Fin.sum_univ_eq_sum_range (fun s => G (setOf n s))]
  rfl

end Lax117284Proofs.ClientsILP
