import Lax117284Proofs.Injectivity
import Lax117284Proofs.SourceInjectivity
import Lax117284.Lemma14
import Lax117284.Lemma15
import Lax117284.Theorem7
import Lax117284.Theorem9
import Lax117284.Theorem11
import Lax117284.Corollary8
import Lax117284Proofs.Corollary8

/-!
The reductions, as maps on words, are correct: a word is a yes-instance of the source exactly
when its image is one of the target. Every reduction is a case split on whether the word
encodes an instance of the source — the maps are written with a choice among the instances a
word encodes, and the code is prefix-free, so there is only one — after which correctness of
the construction is the statement about instances.
-/

namespace Lax117284Proofs.WordCorrect

open Lax117284.Scheduling Lax117284.Problems
open Lax434930.PolynomialTime

/-- An instance without clients has a fair schedule for every parameter: the empty one. -/
theorem hasKFair_of_clients_zero (I : Instance) (h : I.clients = 0) (k : ℕ) :
    I.HasKFairSchedule k :=
  ⟨fun _ => ∅, fun _ => by simp [Set.pairwise_empty], fun j => absurd j.isLt (by omega)⟩

theorem hasFair_of_clients_zero (I : Instance) (h : I.clients = 0) (k : Fin I.clients → ℕ) :
    I.HasFairSchedule k :=
  ⟨fun _ => ∅, fun _ => by simp [Set.pairwise_empty], fun j => absurd j.isLt (by omega)⟩

theorem dayIndepP_of_clients_zero (I : Instance) (h : I.clients = 0) : I.DayIndepP :=
  fun _ _ j => absurd j.isLt (by omega)

/-! ### Membership of a code -/

theorem uniform_mem_encode {C : Instance → ℕ → Prop} {I : Instance} {k : ℕ} :
    encodeUniform I k ∈ Uniform C ↔ C I k ∧ I.HasKFairSchedule k := by
  constructor
  · rintro ⟨I', k', h, hC, hF⟩
    obtain ⟨rfl, rfl⟩ := Injectivity.encodeUniform_inj h
    exact ⟨hC, hF⟩
  · rintro ⟨hC, hF⟩
    exact ⟨I, k, rfl, hC, hF⟩

theorem perClient_mem_encode {C : (I : Instance) → (Fin I.clients → ℕ) → Prop}
    {I : Instance} {k : Fin I.clients → ℕ} :
    encodePerClient I k ∈ PerClient C ↔ C I k ∧ I.HasFairSchedule k := by
  constructor
  · rintro ⟨I', k', h, hC, hF⟩
    obtain ⟨rfl, hk⟩ := Injectivity.encodePerClient_inj h
    obtain rfl := eq_of_heq hk
    exact ⟨hC, hF⟩
  · rintro ⟨hC, hF⟩
    exact ⟨I, k, rfl, hC, hF⟩

/-! ### Lemma 14 -/

open Lax117284.MulticolouredIndepSet in
/--
---
conclusion: Lax117284.Lemma14.reduce_correct
---
A word encoding an instance in normal form is sent to the code of the constructed instance, and the code determines the instance, so the question about the word is the question about the instance; every other word goes to the rejected word, which is in no language, and is not in the language of the normal form.
-/
theorem lemma14_reduce_correct (w : Word) :
    w ∈ NormalMulticolouredIndepSet ↔
      Lax117284.Lemma14.reduce w ∈ PerClient
        fun I k => Lax117284.ConflictGraph.treewidth I ≤ 4 ∧ ∀ j, k j ≤ I.days := by
  classical
  by_cases h : ∃ G : Lax117284.MulticolouredIndepSet.Instance,
      encodeInstance G = w ∧ G.Normal
  · unfold Lax117284.Lemma14.reduce
    rw [dif_pos h]
    obtain ⟨hG, hN⟩ := h.choose_spec
    rw [perClient_mem_encode]
    have hc := Lax117284.Lemma14.correct h.choose hN
    constructor
    · rintro ⟨G', hG', hN', hI⟩
      have hGG : G' = h.choose := SourceInjectivity.mis_encode_inj (hG'.trans hG.symm)
      subst hGG
      exact ⟨⟨Lax117284.Lemma14.treewidth_le _, fun j => Lax117284.Lemma14.kvec_le_days _ j⟩,
        hc.1 hI⟩
    · rintro ⟨-, hF⟩
      exact ⟨h.choose, hG, hN, hc.2 hF⟩
  · unfold Lax117284.Lemma14.reduce
    rw [dif_neg h]
    constructor
    · rintro ⟨G, hG, hN, -⟩
      exact absurd ⟨G, hG, hN⟩ h
    · intro hmem
      exact absurd hmem (Injectivity.rejectedPerClient_notMem _)

/-! ### Lemma 15 -/

/--
---
conclusion: Lax117284.Lemma15.reduce_correct
---
A word whose parameters do not exceed its number of days is sent to the code of the constructed instance with the parameter `m`, and the construction preserves the answer; every other word goes to the rejected word, which is in no language, and is in no per-client language of parameters below the days either.
-/
theorem lemma15_reduce_correct (w : Word) :
    w ∈ PerClient (fun I k => ∀ j, k j ≤ I.days) ↔
      Lax117284.Lemma15.reduce w ∈ Uniform any := by
  classical
  by_cases h : ∃ (I : Instance) (k : Fin I.clients → ℕ),
      encodePerClient I k = w ∧ ∀ j, k j ≤ I.days
  · unfold Lax117284.Lemma15.reduce
    rw [dif_pos h]
    obtain ⟨hw, hk⟩ := h.choose_spec.choose_spec
    have e : w ∈ PerClient (fun I k => ∀ j, k j ≤ I.days) ↔
        encodePerClient h.choose h.choose_spec.choose ∈ PerClient (fun I k => ∀ j, k j ≤ I.days) := by
      rw [hw]
    by_cases hc0 : h.choose.clients = 0
    · rw [if_pos hc0, uniform_mem_encode, e, perClient_mem_encode]
      exact ⟨fun _ => ⟨trivial, hasKFair_of_clients_zero (Lax117284.Corollary8.noClients 0) rfl 0⟩,
        fun _ => ⟨hk, hasFair_of_clients_zero h.choose hc0 _⟩⟩
    rw [if_neg hc0, uniform_mem_encode, e, perClient_mem_encode]
    have hc := Lax117284.Lemma15.correct h.choose h.choose_spec.choose hk
    constructor
    · rintro ⟨-, hF⟩
      exact ⟨trivial, hc.1 hF⟩
    · rintro ⟨-, hF⟩
      exact ⟨hk, hc.2 hF⟩
  · unfold Lax117284.Lemma15.reduce
    rw [dif_neg h]
    constructor
    · rintro ⟨I, k, hw, hk, -⟩
      exact absurd ⟨I, k, hw, hk⟩ h
    · intro hmem
      exact absurd hmem (Injectivity.rejected_notMem _)

/-! ### Theorem 7 -/

/--
---
conclusion: Lax117284.Theorem7.reduce_correct
---
A word encoding a formula is sent to the code of the constructed instance, which has three days and equal processing times, and the code determines the instance; every other word goes to the rejected word.
-/
theorem theorem7_reduce_correct (w : Word) :
    w ∈ Lax117284.BoundedSat.BoundedSat ↔
      Lax117284.Theorem7.reduce w ∈
        Uniform fun I k => I.days = 3 ∧ k = 1 ∧ I.DayIndepP := by
  classical
  by_cases h : ∃ φ : Lax117284.BoundedSat.Formula,
      Lax117284.BoundedSat.encodeFormula φ = w ∧ φ.vars ≤ Lax117284.BoundedSat.slots φ
  · unfold Lax117284.Theorem7.reduce
    rw [dif_pos h]
    rw [uniform_mem_encode]
    have hc := Lax117284.Theorem7.correct h.choose
    have hd := Lax117284.Theorem7.inst_days h.choose
    have hp : (Lax117284.Theorem7.inst h.choose).DayIndepP := fun i i' j =>
      Lax117284.Theorem7.inst_p_eq h.choose i i' j j
    constructor
    · rintro ⟨φ, hφ, -, hS⟩
      have : φ = h.choose :=
        SourceInjectivity.boundedSat_encode_inj (hφ.trans h.choose_spec.1.symm)
      subst this
      exact ⟨⟨hd, rfl, hp⟩, hc.1 hS⟩
    · rintro ⟨-, hF⟩
      exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, hc.2 hF⟩
  · unfold Lax117284.Theorem7.reduce
    rw [dif_neg h]
    constructor
    · rintro ⟨φ, hφ, hle, -⟩
      exact absurd ⟨φ, hφ, hle⟩ h
    · intro hmem
      exact absurd hmem (Injectivity.rejected_notMem _)

/-! ### Theorem 9 -/

/--
---
conclusion: Lax117284.Theorem9.reduce_correct
---
A word encoding an instance one parameter below its number of days is sent to the code of its formula; every other word goes to the code of an unsatisfiable formula, and the code determines the formula.
-/
theorem theorem9_reduce_correct (w : Word) :
    w ∈ Uniform (fun I k => k + 1 = I.days) ↔
      Lax117284.Theorem9.reduce w ∈ Lax117284.TwoSatisfiability.TwoSat := by
  classical
  by_cases h : ∃ (I : Instance) (k : ℕ), encodeUniform I k = w ∧ k + 1 = I.days
  · unfold Lax117284.Theorem9.reduce
    rw [dif_pos h]
    obtain ⟨hw, hk⟩ := h.choose_spec.choose_spec
    have hc := Lax117284.Theorem9.correct h.choose h.choose_spec.choose hk
    have e : w ∈ Uniform (fun I k => k + 1 = I.days) ↔
        encodeUniform h.choose h.choose_spec.choose ∈ Uniform (fun I k => k + 1 = I.days) := by
      rw [hw]
    rw [e, uniform_mem_encode]
    constructor
    · rintro ⟨-, hF⟩
      exact ⟨_, rfl, hc.1 hF⟩
    · rintro ⟨φ, hφ, hS⟩
      have := SourceInjectivity.twoSat_encode_inj hφ
      subst this
      exact ⟨hk, hc.2 hS⟩
  · unfold Lax117284.Theorem9.reduce
    rw [dif_neg h]
    constructor
    · rintro ⟨I, k, hw, hk, -⟩
      exact absurd ⟨I, k, hw, hk⟩ h
    · rintro ⟨φ, hφ, hS⟩
      have := SourceInjectivity.twoSat_encode_inj hφ
      subst this
      exact absurd hS Injectivity.not_satisfiable_unsatisfiable

/-! ### Theorem 11 -/

/--
---
conclusion: Lax117284.Theorem11.reduce_correct
---
A word encoding an instance of `R || ∑ Z` is sent to the code of the constructed instance, which has day-independent due dates; every other word goes to the rejected word.
-/
theorem theorem11_reduce_correct (w : Word) :
    w ∈ Lax117284.JustInTime.AllJIT ↔
      Lax117284.Theorem11.reduce w ∈ Uniform fun I _ => I.DayIndepD := by
  classical
  by_cases h : ∃ R : Lax117284.JustInTime.Instance, Lax117284.JustInTime.encodeInstance R = w
  · unfold Lax117284.Theorem11.reduce
    rw [dif_pos h]
    rw [uniform_mem_encode]
    have hc := Lax117284.Theorem11.correct h.choose
    have hd := Lax117284.Theorem11.inst_dayIndepD h.choose
    constructor
    · rintro ⟨R, hR, hJ⟩
      have : R = h.choose := SourceInjectivity.jit_encode_inj (hR.trans h.choose_spec.symm)
      subst this
      exact ⟨hd, hc.1 hJ⟩
    · rintro ⟨-, hF⟩
      exact ⟨h.choose, h.choose_spec, hc.2 hF⟩
  · unfold Lax117284.Theorem11.reduce
    rw [dif_neg h]
    constructor
    · rintro ⟨R, hR, -⟩
      exact absurd ⟨R, hR⟩ h
    · intro hmem
      exact absurd hmem (Injectivity.rejected_notMem _)

/-! ### Corollary 8 -/

theorem dayIndepP_of_addFreeDay {J : Instance}
    (h : (Lax117284.Corollary8.addFreeDay J).DayIndepP) : J.DayIndepP := fun i i' j => by
  have := h i.castSucc i'.castSucc j
  rwa [Lax117284Proofs.Corollary8.free_p_castSucc, Lax117284Proofs.Corollary8.free_p_castSucc]
    at this

theorem dayIndepP_of_addBlockingDay {J : Instance}
    (h : (Lax117284.Corollary8.addBlockingDay J).DayIndepP) : J.DayIndepP := fun i i' j => by
  have := h i.castSucc i'.castSucc j.castSucc
  rwa [Lax117284Proofs.Corollary8.block_p_castSucc_castSucc,
    Lax117284Proofs.Corollary8.block_p_castSucc_castSucc] at this

/--
---
conclusion: Lax117284.Corollary8.reduceFreeDay_correct
---
The image of a word encoding an instance with `m` days and parameter `k` is the code of the instance with a day added and the parameter `k + 1`; conversely the days, the parameter and the day-independence of the image give those of the word.
-/
theorem corollary8_free_correct (m k : ℕ) (hm : 0 < m) (w : Word) :
    w ∈ Uniform (fun I k' => I.days = m ∧ k' = k ∧ I.DayIndepP) ↔
      Lax117284.Corollary8.reduceFreeDay w ∈
        Uniform fun I k' => I.days = m + 1 ∧ k' = k + 1 ∧ I.DayIndepP := by
  classical
  by_cases h : ∃ (I : Instance) (k : ℕ), encodeUniform I k = w ∧ 0 < I.days
  · unfold Lax117284.Corollary8.reduceFreeDay
    rw [dif_pos h]
    obtain ⟨hw, hpos⟩ := h.choose_spec.choose_spec
    have e : w ∈ Uniform (fun I k' => I.days = m ∧ k' = k ∧ I.DayIndepP) ↔
        encodeUniform h.choose h.choose_spec.choose ∈
          Uniform (fun I k' => I.days = m ∧ k' = k ∧ I.DayIndepP) := by rw [hw]
    rw [e, uniform_mem_encode, uniform_mem_encode]
    have hc := Lax117284.Corollary8.addFreeDay_correct h.choose hpos h.choose_spec.choose
    have hd : (Lax117284.Corollary8.addFreeDay h.choose).days = h.choose.days + 1 := rfl
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, hF⟩
      exact ⟨⟨by omega, by omega, Lax117284.Corollary8.addFreeDay_dayIndepP h3⟩, hc.1 hF⟩
    · rintro ⟨⟨h1, h2, h3⟩, hF⟩
      exact ⟨⟨by omega, by omega, dayIndepP_of_addFreeDay h3⟩, hc.2 hF⟩
  · unfold Lax117284.Corollary8.reduceFreeDay
    rw [dif_neg h]
    constructor
    · rintro ⟨I, k', hw, hC, -⟩
      exact absurd ⟨I, k', hw, by omega⟩ h
    · intro hmem
      exact absurd hmem (Injectivity.rejected_notMem _)

/--
---
conclusion: Lax117284.Corollary8.reduceBlockingDay_correct
---
The image of a word encoding an instance with `m` days and parameter `1` is the code of the instance with a blocking client and a blocking day added; a word with another parameter is rejected, so the parameter of the word is `1` whenever its image is a yes-instance.
-/
theorem corollary8_blocking_correct (m : ℕ) (hm : 0 < m) (w : Word) :
    w ∈ Uniform (fun I k' => I.days = m ∧ k' = 1 ∧ I.DayIndepP) ↔
      Lax117284.Corollary8.reduceBlockingDay w ∈
        Uniform fun I k' => I.days = m + 1 ∧ k' = 1 ∧ I.DayIndepP := by
  classical
  by_cases h : ∃ (I : Instance) (k : ℕ), encodeUniform I k = w ∧ 0 < I.days ∧ k = 1
  · unfold Lax117284.Corollary8.reduceBlockingDay
    rw [dif_pos h]
    obtain ⟨hw, hpos, hk1⟩ := h.choose_spec.choose_spec
    have e : w ∈ Uniform (fun I k' => I.days = m ∧ k' = 1 ∧ I.DayIndepP) ↔
        encodeUniform h.choose h.choose_spec.choose ∈
          Uniform (fun I k' => I.days = m ∧ k' = 1 ∧ I.DayIndepP) := by rw [hw]
    by_cases hc0 : h.choose.clients = 0
    · rw [if_pos hc0, e, uniform_mem_encode, uniform_mem_encode]
      have hd : (Lax117284.Corollary8.noClients (h.choose.days + 1)).days = h.choose.days + 1 := rfl
      have hF := hasKFair_of_clients_zero h.choose hc0 1
      have hF' := hasKFair_of_clients_zero (Lax117284.Corollary8.noClients (h.choose.days + 1))
        rfl 1
      have hdi := dayIndepP_of_clients_zero h.choose hc0
      have hdi' := dayIndepP_of_clients_zero (Lax117284.Corollary8.noClients (h.choose.days + 1))
        rfl
      rw [hk1]
      constructor
      · rintro ⟨⟨h1, h2, h3⟩, -⟩
        exact ⟨⟨by omega, rfl, hdi'⟩, hF'⟩
      · rintro ⟨⟨h1, h2, h3⟩, -⟩
        exact ⟨⟨by omega, rfl, hdi⟩, hF⟩
    rw [if_neg hc0, e, uniform_mem_encode, uniform_mem_encode]
    have hc := Lax117284.Corollary8.addBlockingDay_correct h.choose hpos
    have hd : (Lax117284.Corollary8.addBlockingDay h.choose).days = h.choose.days + 1 := rfl
    rw [hk1]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, hF⟩
      exact ⟨⟨by omega, rfl, Lax117284.Corollary8.addBlockingDay_dayIndepP h3⟩, hc.1 hF⟩
    · rintro ⟨⟨h1, h2, h3⟩, hF⟩
      exact ⟨⟨by omega, rfl, dayIndepP_of_addBlockingDay h3⟩, hc.2 hF⟩
  · unfold Lax117284.Corollary8.reduceBlockingDay
    rw [dif_neg h]
    constructor
    · rintro ⟨I, k', hw, ⟨h1, h2, -⟩, -⟩
      exact absurd ⟨I, k', hw, by omega, h2⟩ h
    · intro hmem
      exact absurd hmem (Injectivity.rejected_notMem _)

end Lax117284Proofs.WordCorrect
