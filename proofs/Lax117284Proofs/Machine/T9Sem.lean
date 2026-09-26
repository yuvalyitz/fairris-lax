import Lax117284Proofs.Machine.BlockSem
import Lax117284.Theorem9

/-!
The reduction of Theorem 9 on the numbers of a stream: the word of the formula of an instance,
clause by clause, with the numbers of every clause computed from its index.
-/

namespace Lax117284Proofs.Machine.T9Sem

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime Lax117284.TwoSatisfiability
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.BlockSem

/-- The jobs of clients `j₁` and `j₂` on day `i` conflict, read off an array of numbers. -/
def confG (arr : List ℕ) (n i j₁ j₂ : ℕ) : Prop :=
  arr.getD (2 + 2 * (i * n + j₁) + 1) 0 - arr.getD (2 + 2 * (i * n + j₁)) 0 <
      arr.getD (2 + 2 * (i * n + j₂) + 1) 0 ∧
    arr.getD (2 + 2 * (i * n + j₂) + 1) 0 - arr.getD (2 + 2 * (i * n + j₂)) 0 <
      arr.getD (2 + 2 * (i * n + j₁) + 1) 0

instance (arr : List ℕ) (n i j₁ j₂ : ℕ) : Decidable (confG arr n i j₁ j₂) := by
  unfold confG; infer_instance

/-- The variables and the signs of the two literals of clause `c`. -/
def clauseG (arr : List ℕ) (n m c : ℕ) : ℕ × Bool × ℕ × Bool :=
  if c < m * n * n then
    (if c % (n * n) / n ≠ c % (n * n) % n ∧ confG arr n (c / (n * n)) (c % (n * n) / n)
        (c % (n * n) % n) then
      (c / (n * n) * n + c % (n * n) / n, false, c / (n * n) * n + c % (n * n) % n, false)
    else (c / (n * n) * n + c % (n * n) / n, true, c / (n * n) * n + c % (n * n) / n, false))
  else
    (if (c - m * n * n) % (m * m) / m ≠ (c - m * n * n) % (m * m) % m then
      ((c - m * n * n) % (m * m) / m * n + (c - m * n * n) / (m * m), true,
        (c - m * n * n) % (m * m) % m * n + (c - m * n * n) / (m * m), true)
    else ((c - m * n * n) % (m * m) / m * n + (c - m * n * n) / (m * m), true,
        (c - m * n * n) % (m * m) / m * n + (c - m * n * n) / (m * m), false))

/-- The word of clause `c`. -/
def clW (arr : List ℕ) (n m c : ℕ) : Word :=
  encodeNat (clauseG arr n m c).1 ++ [(clauseG arr n m c).2.1] ++
    encodeNat (clauseG arr n m c).2.2.1 ++ [(clauseG arr n m c).2.2.2]

/-- The word of the formula. -/
def outT9 (arr : List ℕ) (n m : ℕ) : Word :=
  encodeNat (m * n + 1) ++ encodeNat (m * n * n + n * m * m) ++
    (List.range (m * n * n + n * m * m)).flatMap (clW arr n m)

section Formula

variable (ns : List ℕ) (hv : Valid ns)

lemma varIdx_val {i j : ℕ} (hi : i < ns.getD 1 0) (hj : j < ns.getD 0 0) :
    ((Lax117284.Theorem9.varIdx (instOf ns hv) i j : Fin _) : ℕ) = i * ns.getD 0 0 + j := by
  unfold Lax117284.Theorem9.varIdx
  have := cell_lt hi hj
  show min (i * ns.getD 0 0 + j) (ns.getD 1 0 * ns.getD 0 0) = _
  exact min_eq_left this.le

lemma conflictAt_iff_confG {i j₁ j₂ : ℕ} (hi : i < ns.getD 1 0) (h1 : j₁ < ns.getD 0 0)
    (h2 : j₂ < ns.getD 0 0) :
    (instOf ns hv).ConflictAt i j₁ j₂ ↔ confG ns (ns.getD 0 0) i j₁ j₂ := by
  unfold Instance.ConflictAt confG
  rw [inst_d ns hv _ _ hi h1, inst_d ns hv _ _ hi h2, inst_p ns hv _ _ hi h1,
    inst_p ns hv _ _ hi h2]

/-- **A literal of the formula.** -/
theorem lit_val (α : Fin 2) {c : ℕ}
    (hc : c < ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0 + ns.getD 0 0 * ns.getD 1 0 * ns.getD 1 0) :
    (((Lax117284.Theorem9.clauseLit (instOf ns hv) c α).1 : Fin _) : ℕ) =
        (if α = 0 then (clauseG ns (ns.getD 0 0) (ns.getD 1 0) c).1
          else (clauseG ns (ns.getD 0 0) (ns.getD 1 0) c).2.2.1) ∧
      (Lax117284.Theorem9.clauseLit (instOf ns hv) c α).2 =
        (if α = 0 then (clauseG ns (ns.getD 0 0) (ns.getD 1 0) c).2.1
          else (clauseG ns (ns.getD 0 0) (ns.getD 1 0) c).2.2.2) := by
  unfold Lax117284.Theorem9.clauseLit clauseG
  simp only [show (instOf ns hv).clients = ns.getD 0 0 from rfl,
    show (instOf ns hv).days = ns.getD 1 0 from rfl]
  by_cases hc1 : c < ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0
  · have hn : 0 < ns.getD 0 0 := by
      rcases Nat.eq_zero_or_pos (ns.getD 0 0) with h | h
      · rw [h] at hc1; simp at hc1
      · exact h
    have hnn : 0 < ns.getD 0 0 * ns.getD 0 0 := Nat.mul_pos hn hn
    have hi : c / (ns.getD 0 0 * ns.getD 0 0) < ns.getD 1 0 := by
      rw [Nat.div_lt_iff_lt_mul hnn, ← Nat.mul_assoc]; exact hc1
    have hr : c % (ns.getD 0 0 * ns.getD 0 0) < ns.getD 0 0 * ns.getD 0 0 := Nat.mod_lt _ hnn
    have hj1 : c % (ns.getD 0 0 * ns.getD 0 0) / ns.getD 0 0 < ns.getD 0 0 := by
      rw [Nat.div_lt_iff_lt_mul hn]; exact hr
    have hj2 : c % (ns.getD 0 0 * ns.getD 0 0) % ns.getD 0 0 < ns.getD 0 0 := Nat.mod_lt _ hn
    have e1 := varIdx_val ns hv hi hj1
    have e2 := varIdx_val ns hv hi hj2
    rw [if_pos hc1, if_pos hc1]
    by_cases hcf : c % (ns.getD 0 0 * ns.getD 0 0) / ns.getD 0 0 ≠
        c % (ns.getD 0 0 * ns.getD 0 0) % ns.getD 0 0 ∧
      confG ns (ns.getD 0 0) (c / (ns.getD 0 0 * ns.getD 0 0))
        (c % (ns.getD 0 0 * ns.getD 0 0) / ns.getD 0 0)
        (c % (ns.getD 0 0 * ns.getD 0 0) % ns.getD 0 0)
    · have hcf' : c % (ns.getD 0 0 * ns.getD 0 0) / ns.getD 0 0 ≠
          c % (ns.getD 0 0 * ns.getD 0 0) % ns.getD 0 0 ∧
        (instOf ns hv).ConflictAt (c / (ns.getD 0 0 * ns.getD 0 0))
          (c % (ns.getD 0 0 * ns.getD 0 0) / ns.getD 0 0)
          (c % (ns.getD 0 0 * ns.getD 0 0) % ns.getD 0 0) :=
        ⟨hcf.1, (conflictAt_iff_confG ns hv hi hj1 hj2).2 hcf.2⟩
      rw [if_pos hcf', if_pos hcf]
      by_cases hα : α = 0
      · simp only [hα, if_true, eq_self_iff_true, decide_true, e1, e2, and_self]
      · simp only [hα, if_false, decide_false, e1, e2, and_self]
    · have hcf' : ¬ (c % (ns.getD 0 0 * ns.getD 0 0) / ns.getD 0 0 ≠
          c % (ns.getD 0 0 * ns.getD 0 0) % ns.getD 0 0 ∧
        (instOf ns hv).ConflictAt (c / (ns.getD 0 0 * ns.getD 0 0))
          (c % (ns.getD 0 0 * ns.getD 0 0) / ns.getD 0 0)
          (c % (ns.getD 0 0 * ns.getD 0 0) % ns.getD 0 0)) :=
        fun h => hcf ⟨h.1, (conflictAt_iff_confG ns hv hi hj1 hj2).1 h.2⟩
      rw [if_neg hcf', if_neg hcf]
      by_cases hα : α = 0
      · simp only [hα, if_true, eq_self_iff_true, decide_true, e1, and_self]
      · simp only [hα, if_false, decide_false, e1, and_self]
  · have hc2 : c - ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0 <
        ns.getD 0 0 * ns.getD 1 0 * ns.getD 1 0 := by omega
    have hm : 0 < ns.getD 1 0 := by
      rcases Nat.eq_zero_or_pos (ns.getD 1 0) with h | h
      · rw [h] at hc2; simp at hc2
      · exact h
    have hmm : 0 < ns.getD 1 0 * ns.getD 1 0 := Nat.mul_pos hm hm
    have hj : (c - ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0) / (ns.getD 1 0 * ns.getD 1 0) <
        ns.getD 0 0 := by
      rw [Nat.div_lt_iff_lt_mul hmm]
      have : ns.getD 0 0 * ns.getD 1 0 * ns.getD 1 0 =
          ns.getD 0 0 * (ns.getD 1 0 * ns.getD 1 0) := Nat.mul_assoc _ _ _
      omega
    have hr : (c - ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0) % (ns.getD 1 0 * ns.getD 1 0) <
        ns.getD 1 0 * ns.getD 1 0 := Nat.mod_lt _ hmm
    have hi1 : (c - ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0) % (ns.getD 1 0 * ns.getD 1 0) /
        ns.getD 1 0 < ns.getD 1 0 := by
      rw [Nat.div_lt_iff_lt_mul hm]; exact hr
    have hi2 : (c - ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0) % (ns.getD 1 0 * ns.getD 1 0) %
        ns.getD 1 0 < ns.getD 1 0 := Nat.mod_lt _ hm
    have e1 := varIdx_val ns hv hi1 hj
    have e2 := varIdx_val ns hv hi2 hj
    rw [if_neg hc1, if_neg hc1]
    by_cases hd : (c - ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0) % (ns.getD 1 0 * ns.getD 1 0) /
        ns.getD 1 0 ≠ (c - ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0) %
          (ns.getD 1 0 * ns.getD 1 0) % ns.getD 1 0
    · rw [if_pos hd, if_pos hd]
      by_cases hα : α = 0
      · simp only [hα, if_true, eq_self_iff_true, decide_true, e1, e2, and_self]
      · simp only [hα, if_false, decide_false, e1, e2, and_self]
    · rw [if_neg hd, if_neg hd]
      by_cases hα : α = 0
      · simp only [hα, if_true, eq_self_iff_true, decide_true, e1, and_self]
      · simp only [hα, if_false, decide_false, e1, and_self]

/-- **The word of the formula of an instance.** -/
theorem encodeFormula_eq :
    encodeFormula (Lax117284.Theorem9.formula (instOf ns hv)) =
      outT9 ns (ns.getD 0 0) (ns.getD 1 0) := by
  unfold encodeFormula outT9
  show encodeNat (ns.getD 1 0 * ns.getD 0 0 + 1) ++
      encodeNat (ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0 + ns.getD 0 0 * ns.getD 1 0 * ns.getD 1 0) ++
      (List.finRange (ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0 +
        ns.getD 0 0 * ns.getD 1 0 * ns.getD 1 0)).flatMap (fun c =>
      (List.finRange 2).flatMap fun α =>
        encodeNat ((Lax117284.Theorem9.formula (instOf ns hv)).lit c α).1 ++
          [((Lax117284.Theorem9.formula (instOf ns hv)).lit c α).2]) = _
  congr 1
  refine (flatMap_finRange _ _).trans ?_
  refine List.flatMap_congr fun c hc => ?_
  have hc' := List.mem_range.mp hc
  rw [dif_pos hc']
  have hf2 : List.finRange 2 = [0, 1] := by decide
  rw [hf2]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  obtain ⟨a0, b0⟩ := lit_val ns hv 0 hc'
  obtain ⟨a1, b1⟩ := lit_val ns hv 1 hc'
  show encodeNat ((Lax117284.Theorem9.clauseLit (instOf ns hv) c 0).1 : ℕ) ++
      [(Lax117284.Theorem9.clauseLit (instOf ns hv) c 0).2] ++
      (encodeNat ((Lax117284.Theorem9.clauseLit (instOf ns hv) c 1).1 : ℕ) ++
      [(Lax117284.Theorem9.clauseLit (instOf ns hv) c 1).2]) = _
  rw [a0, b0, a1, b1]
  simp [clW]

end Formula

/-- **The gate of the reduction, on streams.** -/
theorem t9_gate (w : Word) :
    (∃ (I : Instance) (k : ℕ), encodeUniform I k = w ∧ k + 1 = I.days) ↔
      ∃ ns : List ℕ, w = numCode ns ∧ Shape eU ns ∧ Valid ns ∧ paramOf ns + 1 = ns.getD 1 0 := by
  constructor
  · rintro ⟨I, k, hw, hk⟩
    obtain ⟨ns, hw', hs, hv, hpos⟩ := (uniform_iff w).1 ⟨I, k, hw, by omega⟩
    refine ⟨ns, hw', hs, hv, ?_⟩
    have hI : encodeUniform (instOf ns hv) (paramOf ns) = numCode ns := by
      rw [encodeUniform, encodeInstance_eq]
      conv_rhs => rw [← instToks_instOf ns hv hs]
      rw [numCode_append]
      simp [numCode]
    have := Injectivity.encodeUniform_inj (I := instOf ns hv) (I' := I) (k := paramOf ns)
      (k' := k) (hI.trans (hw'.symm.trans hw.symm))
    obtain ⟨rfl, rfl⟩ := this
    exact hk
  · rintro ⟨ns, hw, hs, hv, hk⟩
    refine ⟨instOf ns hv, paramOf ns, ?_, hk⟩
    rw [hw, encodeUniform, encodeInstance_eq]
    conv_rhs => rw [← instToks_instOf ns hv hs]
    rw [numCode_append]
    simp [numCode]

/-- **The reduction writes the word of the formula.** -/
theorem t9_eq (ns : List ℕ) (hv : Valid ns) (hs : Shape eU ns) (hk : paramOf ns + 1 = ns.getD 1 0) :
    Lax117284.Theorem9.reduce (numCode ns) = outT9 ns (ns.getD 0 0) (ns.getD 1 0) := by
  classical
  have hI : encodeUniform (instOf ns hv) (paramOf ns) = numCode ns := by
    rw [encodeUniform, encodeInstance_eq]
    conv_rhs => rw [← instToks_instOf ns hv hs]
    rw [numCode_append]
    simp [numCode]
  have hg : ∃ (I : Instance) (k : ℕ), encodeUniform I k = numCode ns ∧ k + 1 = I.days :=
    ⟨instOf ns hv, paramOf ns, hI, hk⟩
  unfold Lax117284.Theorem9.reduce
  rw [dif_pos hg]
  have key : ∀ (I' : Instance) (k' : ℕ), encodeUniform I' k' = numCode ns →
      encodeFormula (Lax117284.Theorem9.formula I') = outT9 ns (ns.getD 0 0) (ns.getD 1 0) := by
    intro I' k' h'
    obtain ⟨rfl, rfl⟩ := Injectivity.encodeUniform_inj (h'.trans hI.symm)
    exact encodeFormula_eq ns hv
  exact key _ _ hg.choose_spec.choose_spec.1 |>.trans rfl

/-- **A word that is not the code of an accepted stream goes to the unsatisfiable formula.** -/
theorem t9_rej (w : Word)
    (h : ¬ ∃ ns : List ℕ, w = numCode ns ∧ Shape eU ns ∧ Valid ns ∧
      paramOf ns + 1 = ns.getD 1 0) :
    Lax117284.Theorem9.reduce w = encodeFormula unsatisfiable := by
  classical
  unfold Lax117284.Theorem9.reduce
  rw [dif_neg (fun hg => h ((t9_gate w).1 hg))]

end Lax117284Proofs.Machine.T9Sem
