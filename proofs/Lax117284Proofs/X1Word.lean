import Lax117284Proofs.Theorem9
import Lax117284Proofs.ExtremeFairness
import Lax117284Proofs.WordCorrect
import Lax117284Proofs.Injectivity
import Lax117284Proofs.SourceInjectivity
import Lax117284.Theorem9
import Lax117284.Theorem1

/-!
The three tractable values of the fairness parameter, as one reduction to 2-satisfiability: a word
encoding an instance with the parameter one below its number of days goes to the formula of
Theorem 9; one whose parameter is its number of days goes to a formula that forbids every
conflict and asks for every variable; and one whose parameter is zero goes to a satisfiable
formula.
-/

namespace Lax117284Proofs.X1Word

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime Lax117284.TwoSatisfiability
open Lax117284.Theorem9 (varIdx clauseLit)
open Lax117284Proofs.WordCorrect (uniform_mem_encode)
open Lax117284Proofs.Theorem9 (conflictSlot conflictSlot_lt conflictSlot_div conflictSlot_mod
  clauseLit_conflict clauseLit_conflict_taut)

/-- The parameters of the tractable cases. -/
def extremeC : Instance → ℕ → Prop := fun I k => k = 0 ∨ k + 1 = I.days ∨ k = I.days

/-- **The formula for the parameter equal to the number of days**: the conflict clauses of
Theorem 9, then one clause for every variable asking for it to be true. -/
def formulaU (I : Instance) : Formula where
  vars := I.days * I.clients + 1
  clauses := I.days * I.clients * I.clients + I.days * I.clients
  lit c α :=
    if hc : (c : ℕ) < I.days * I.clients * I.clients then clauseLit I c α
    else (⟨(c : ℕ) - I.days * I.clients * I.clients, by have := c.isLt; omega⟩, true)

/-- **A satisfiable formula**: one variable and no clause. -/
def satF : Formula where
  vars := 1
  clauses := 0
  lit c _ := c.elim0

theorem satF_satisfiable : satF.Satisfiable := ⟨fun _ => true, fun c => c.elim0⟩

lemma twoSat_mem_encode {φ : Formula} : encodeFormula φ ∈ TwoSat ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨φ', h, hS⟩
    have := SourceInjectivity.twoSat_encode_inj h
    subst this
    exact hS
  · intro hS
    exact ⟨φ, rfl, hS⟩

lemma cell_lt' {m n i j : ℕ} (hi : i < m) (hj : j < n) : i * n + j < m * n := by
  have h1 : (i + 1) * n ≤ m * n := Nat.mul_le_mul_right _ hi
  have h2 : (i + 1) * n = i * n + n := by ring
  omega

set_option maxHeartbeats 800000 in
/-- **The formula asks for every variable and forbids every conflict**, so it is satisfiable
exactly when the instance is free of conflicts. -/
theorem formulaU_satisfiable_iff (I : Instance) : (formulaU I).Satisfiable ↔ I.ConflictFree := by
  classical
  constructor
  · rintro ⟨a, ha⟩ i j j' hne hconf
    have hall : ∀ (i : Fin I.days) (j : Fin I.clients), a (varIdx I i j) = true := by
      intro i j
      have hcell := cell_lt' i.isLt j.isLt
      have hlt : I.days * I.clients * I.clients + ((i : ℕ) * I.clients + j) <
          (formulaU I).clauses := by
        show _ < I.days * I.clients * I.clients + I.days * I.clients
        omega
      obtain ⟨α, hα⟩ := ha ⟨_, hlt⟩
      have hnot : ¬ (I.days * I.clients * I.clients + ((i : ℕ) * I.clients + j) <
          I.days * I.clients * I.clients) := by omega
      have hv : (⟨I.days * I.clients * I.clients + ((i : ℕ) * I.clients + j) -
          I.days * I.clients * I.clients, by omega⟩ : Fin (I.days * I.clients + 1)) =
          varIdx I i j := by
        apply Fin.ext
        rw [Lax117284Proofs.Theorem9.varIdx_val i.isLt j.isLt]
        simp
      simp only [formulaU, dif_neg hnot] at hα
      rw [hv] at hα
      exact hα
    have hclt : conflictSlot I i j j' < I.days * I.clients * I.clients :=
      conflictSlot_lt i.isLt j.isLt j'.isLt
    have hdiv := conflictSlot_div (I := I) i.isLt j.isLt j'.isLt
    obtain ⟨hm1, hm2⟩ := conflictSlot_mod (I := I) i.isLt j.isLt j'.isLt
    have hadm : conflictSlot I i j j' % (I.clients * I.clients) / I.clients ≠
        conflictSlot I i j j' % (I.clients * I.clients) % I.clients ∧
        I.ConflictAt (conflictSlot I i j j' / (I.clients * I.clients))
          (conflictSlot I i j j' % (I.clients * I.clients) / I.clients)
          (conflictSlot I i j j' % (I.clients * I.clients) % I.clients) := by
      rw [hdiv, hm1, hm2]
      exact ⟨fun h => hne (Fin.ext h), (Instance.conflictAt_iff (I := I) i j j').2 hconf⟩
    obtain ⟨hl0, hl1⟩ := clauseLit_conflict (I := I) hclt hadm
    obtain ⟨α, hα⟩ := ha ⟨conflictSlot I i j j', by
      show _ < I.days * I.clients * I.clients + I.days * I.clients
      omega⟩
    have hlit : ∀ β : Fin 2, (formulaU I).lit ⟨conflictSlot I i j j', by
        show _ < I.days * I.clients * I.clients + I.days * I.clients
        omega⟩ β = clauseLit I (conflictSlot I i j j') β := fun β => dif_pos hclt
    rw [hlit] at hα
    rcases (by omega : (α : ℕ) = 0 ∨ (α : ℕ) = 1) with h | h
    · have hα0 : α = 0 := Fin.ext (by simpa using h)
      rw [hα0, hl0, hdiv, hm1] at hα
      rw [hall i j] at hα
      exact Bool.noConfusion hα
    · have hα1 : α = 1 := Fin.ext (by simpa using h)
      rw [hα1, hl1, hdiv, hm2] at hα
      rw [hall i j'] at hα
      exact Bool.noConfusion hα
  · intro hcf
    refine ⟨fun _ => true, fun c => ?_⟩
    by_cases hc : (c : ℕ) < I.days * I.clients * I.clients
    · have hlit : ∀ β : Fin 2, (formulaU I).lit c β = clauseLit I c β := fun β => dif_pos hc
      have hcpos : 0 < I.clients := by
        rcases Nat.eq_zero_or_pos I.clients with h | h
        · rw [h] at hc; simp at hc
        · exact h
      have hcomm : I.clients * I.clients * I.days = I.days * I.clients * I.clients := by ring
      have hr : (c : ℕ) % (I.clients * I.clients) < I.clients * I.clients :=
        Nat.mod_lt _ (Nat.mul_pos hcpos hcpos)
      have hi : (c : ℕ) / (I.clients * I.clients) < I.days :=
        Nat.div_lt_of_lt_mul (by omega)
      have hj1 : (c : ℕ) % (I.clients * I.clients) / I.clients < I.clients :=
        Nat.div_lt_of_lt_mul hr
      have hj2 : (c : ℕ) % (I.clients * I.clients) % I.clients < I.clients :=
        Nat.mod_lt _ hcpos
      have hadm : ¬ ((c : ℕ) % (I.clients * I.clients) / I.clients ≠
          (c : ℕ) % (I.clients * I.clients) % I.clients ∧
          I.ConflictAt ((c : ℕ) / (I.clients * I.clients))
            ((c : ℕ) % (I.clients * I.clients) / I.clients)
            ((c : ℕ) % (I.clients * I.clients) % I.clients)) := by
        rintro ⟨hne, hca⟩
        exact hcf ⟨_, hi⟩ ⟨_, hj1⟩ ⟨_, hj2⟩ (fun h => hne (by simpa using congrArg Fin.val h))
          ((Instance.conflictAt_iff (I := I) ⟨_, hi⟩ ⟨_, hj1⟩ ⟨_, hj2⟩).1 hca)
      obtain ⟨hl0, -⟩ := clauseLit_conflict_taut (I := I) hc hadm
      exact ⟨0, by rw [hlit, hl0]⟩
    · exact ⟨0, by simp only [formulaU, dif_neg hc]⟩

/-- The formula of a tractable case. -/
def caseFormula (I : Instance) (k : ℕ) : Word :=
  if k + 1 = I.days then encodeFormula (Lax117284.Theorem9.formula I)
  else if k = I.days then encodeFormula (formulaU I) else encodeFormula satF

open Classical in
/-- **The reduction**, as a map on words: a word encoding an instance with one of the three
tractable parameters goes to the code of the formula of its case, every other word to the code
of an unsatisfiable formula. -/
noncomputable def reduceX (w : Word) : Word :=
  if h : ∃ (I : Instance) (k : ℕ), encodeUniform I k = w ∧ extremeC I k then
    caseFormula h.choose h.choose_spec.choose
  else encodeFormula unsatisfiable

theorem reduceX_code (I : Instance) (k : ℕ) (hk : extremeC I k) :
    reduceX (encodeUniform I k) = caseFormula I k := by
  classical
  have hg : ∃ (I' : Instance) (k' : ℕ), encodeUniform I' k' = encodeUniform I k ∧ extremeC I' k' :=
    ⟨I, k, rfl, hk⟩
  unfold reduceX
  rw [dif_pos hg]
  obtain ⟨e1, e2⟩ := Injectivity.encodeUniform_inj hg.choose_spec.choose_spec.1
  congr 1

/-- **The reduction is correct.** -/
theorem reduceX_correct (w : Word) :
    w ∈ Uniform extremeC ↔ reduceX w ∈ TwoSat := by
  classical
  by_cases h : ∃ (I : Instance) (k : ℕ), encodeUniform I k = w ∧ extremeC I k
  · obtain ⟨I, k, hw, hk⟩ := h
    subst hw
    rw [reduceX_code I k hk, uniform_mem_encode]
    unfold caseFormula
    by_cases h1 : k + 1 = I.days
    · rw [if_pos h1, twoSat_mem_encode]
      exact ⟨(fun h => (Lax117284.Theorem9.correct I k h1).1 h.2),
        (fun hS => ⟨hk, (Lax117284.Theorem9.correct I k h1).2 hS⟩)⟩
    · by_cases h2 : k = I.days
      · rw [if_neg h1, if_pos h2, twoSat_mem_encode, formulaU_satisfiable_iff]
        subst h2
        exact ⟨(fun h => (ExtremeFairness.hasKFairSchedule_days_iff I).1 h.2),
          (fun hS => ⟨hk, (ExtremeFairness.hasKFairSchedule_days_iff I).2 hS⟩)⟩
      · have h0 : k = 0 := by rcases hk with h | h | h <;> first | exact h | exact absurd h ‹_›
        rw [if_neg h1, if_neg h2, twoSat_mem_encode]
        subst h0
        exact ⟨(fun _ => satF_satisfiable), (fun _ => ⟨hk, ExtremeFairness.hasKFairSchedule_zero I⟩)⟩
  · unfold reduceX
    rw [dif_neg h]
    constructor
    · rintro ⟨I, k, hw, hk, -⟩
      exact absurd ⟨I, k, hw, hk⟩ h
    · rintro ⟨φ, hφ, hS⟩
      have := SourceInjectivity.twoSat_encode_inj hφ
      subst this
      exact absurd hS Injectivity.not_satisfiable_unsatisfiable

end Lax117284Proofs.X1Word
