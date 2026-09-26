import Lax117284Proofs.WordCorrect
import Lax117284Proofs.Compose
import Lax117284Proofs.BoundedSatProved
import Lax117284Proofs.McisHard.Final
import Lax117284.Theorem1
import Lax117284.Theorem2
import Lax117284.Theorem3
import Lax117284.Theorem4

/-!
The hardness statements, assembled from the reductions and the hardness of the sources.
Every reduction is correct on all words and its output is either the code of the constructed
instance or a word in no language, so hardness passes to any language between the two, and
to a class of instances that contains what the construction produces.
-/

namespace Lax117284Proofs.Hardness

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime
open Lax434930.NondeterministicPolynomialTime Lax429075.Reductions
open Lax117284Proofs.Compose Lax117284Proofs.WordCorrect

/-! ### The steps, as many-one reductions -/

/--
---
conclusion: Lax117284.Lemma14.perClient_npHard
---
Compose the hardness of the source with the reduction.
-/
theorem perClient_npHard : NPHard (PerClient fun I k =>
    Lax117284.ConflictGraph.treewidth I ≤ 4 ∧ ∀ j, k j ≤ I.days) :=
  npHard_of_manyOne Lax117284Proofs.McisHard.normalMulticolouredIndepSet_npHard_proved
    ⟨Lax117284.Lemma14.reduce, Lax117284.Lemma14.reduce_polyTime, lemma14_reduce_correct⟩

/--
---
conclusion: Lax117284.Corollary8.manyOne_freeDay
---
-/
theorem manyOne_freeDay (m k : ℕ) (hm : 0 < m) :
    ManyOne (Uniform fun I k' => I.days = m ∧ k' = k ∧ I.DayIndepP)
      (Uniform fun I k' => I.days = m + 1 ∧ k' = k + 1 ∧ I.DayIndepP) :=
  ⟨Lax117284.Corollary8.reduceFreeDay, Lax117284.Corollary8.reduceFreeDay_polyTime,
    corollary8_free_correct m k hm⟩

/--
---
conclusion: Lax117284.Corollary8.manyOne_blockingDay
---
-/
theorem manyOne_blockingDay (m : ℕ) (hm : 0 < m) :
    ManyOne (Uniform fun I k' => I.days = m ∧ k' = 1 ∧ I.DayIndepP)
      (Uniform fun I k' => I.days = m + 1 ∧ k' = 1 ∧ I.DayIndepP) :=
  ⟨Lax117284.Corollary8.reduceBlockingDay, Lax117284.Corollary8.reduceBlockingDay_polyTime,
    corollary8_blocking_correct m hm⟩

/--
---
conclusion: Lax117284.Lemma15.perClient_manyOne_uniform
---
-/
theorem perClient_manyOne_uniform :
    ManyOne (PerClient fun I k => ∀ j, k j ≤ I.days) (Uniform any) :=
  ⟨Lax117284.Lemma15.reduce, Lax117284.Lemma15.reduce_polyTime, lemma15_reduce_correct⟩

/--
---
conclusion: Lax117284.Theorem9.manyOne_twoSat
---
-/
theorem manyOne_twoSat :
    ManyOne (Uniform fun I k => k + 1 = I.days) Lax117284.TwoSatisfiability.TwoSat :=
  ⟨Lax117284.Theorem9.reduce, Lax117284.Theorem9.reduce_polyTime, theorem9_reduce_correct⟩

/--
---
conclusion: Lax117284.Theorem11.allJIT_manyOne_dayIndepD
---
-/
theorem allJIT_manyOne_dayIndepD :
    ManyOne Lax117284.JustInTime.AllJIT (Uniform fun I _ => I.DayIndepD) :=
  ⟨Lax117284.Theorem11.reduce, Lax117284.Theorem11.reduce_polyTime, theorem11_reduce_correct⟩

/--
---
conclusion: Lax117284.Theorem7.uniform_three_one_npHard
---
-/
theorem uniform_three_one_npHard :
    NPHard (Uniform fun I k => I.days = 3 ∧ k = 1 ∧ I.DayIndepP) :=
  npHard_of_manyOne Lax117284Proofs.BoundedSatProved.boundedSat_npHard_proved
    ⟨Lax117284.Theorem7.reduce, Lax117284.Theorem7.reduce_polyTime, theorem7_reduce_correct⟩

/--
---
conclusion: Lax117284.Theorem3.uniform_dayIndepD_npHard
---
-/
theorem uniform_dayIndepD_npHard : NPHard (Uniform fun I _ => I.DayIndepD) :=
  npHard_of_manyOne Lax117284.JustInTime.allJIT_npHard allJIT_manyOne_dayIndepD


/-! ### Classes that contain what the construction produces -/

/-- **The reduction of Theorem 7 is correct into any class containing its instances.** -/
theorem reduce7_correct_in (C : Instance → ℕ → Prop)
    (hC : ∀ φ, C (Lax117284.Theorem7.inst φ) 1) (x : Word) :
    x ∈ Lax117284.BoundedSat.BoundedSat ↔ Lax117284.Theorem7.reduce x ∈ Uniform C := by
  classical
  by_cases h : ∃ φ : Lax117284.BoundedSat.Formula,
      Lax117284.BoundedSat.encodeFormula φ = x ∧ φ.vars ≤ Lax117284.BoundedSat.slots φ
  · unfold Lax117284.Theorem7.reduce
    rw [dif_pos h, uniform_mem_encode]
    have hc := Lax117284.Theorem7.correct h.choose
    constructor
    · rintro ⟨φ, hφ, -, hS⟩
      have : φ = h.choose :=
        SourceInjectivity.boundedSat_encode_inj (hφ.trans h.choose_spec.1.symm)
      subst this
      exact ⟨hC _, hc.1 hS⟩
    · rintro ⟨-, hF⟩
      exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, hc.2 hF⟩
  · unfold Lax117284.Theorem7.reduce
    rw [dif_neg h]
    constructor
    · rintro ⟨φ, hφ, hle, -⟩
      exact absurd ⟨φ, hφ, hle⟩ h
    · intro hmem
      exact absurd hmem (Injectivity.rejected_notMem _)

theorem boundedSat_manyOne (C : Instance → ℕ → Prop)
    (hC : ∀ φ, C (Lax117284.Theorem7.inst φ) 1) :
    ManyOne Lax117284.BoundedSat.BoundedSat (Uniform C) :=
  ⟨Lax117284.Theorem7.reduce, Lax117284.Theorem7.reduce_polyTime, reduce7_correct_in C hC⟩

/--
---
conclusion: Lax117284.Theorem2.uniform_dayIndepP_npHard
---
The construction of Theorem 7 has equal processing times, so the reduction of the source
lands in the instances with day-independent processing times.
-/
theorem uniform_dayIndepP_npHard : NPHard (Uniform fun I _ => I.DayIndepP) :=
  npHard_of_manyOne Lax117284Proofs.BoundedSatProved.boundedSat_npHard_proved
    (boundedSat_manyOne _ fun φ i i' j => Lax117284.Theorem7.inst_p_eq φ i i' j j)

/-! ### Theorem 4 -/

theorem reduce14_eq {G : Lax117284.MulticolouredIndepSet.Instance} {x : Word}
    (hG : Lax117284.MulticolouredIndepSet.encodeInstance G = x) (hN : G.Normal) :
    Lax117284.Lemma14.reduce x
      = encodePerClient (Lax117284.Lemma14.inst G) (Lax117284.Lemma14.kvec G) := by
  classical
  have h : ∃ G' : Lax117284.MulticolouredIndepSet.Instance,
      Lax117284.MulticolouredIndepSet.encodeInstance G' = x ∧ G'.Normal := ⟨G, hG, hN⟩
  unfold Lax117284.Lemma14.reduce
  rw [dif_pos h]
  have : h.choose = G := SourceInjectivity.mis_encode_inj (h.choose_spec.1.trans hG.symm)
  rw [this]

theorem reduce15_eq {I : Instance} {k : Fin I.clients → ℕ} (hk : ∀ j, k j ≤ I.days)
    (hc : 0 < I.clients) :
    Lax117284.Lemma15.reduce (encodePerClient I k)
      = encodeUniform (Lax117284.Lemma15.inst I k) I.days := by
  classical
  have h : ∃ (I' : Instance) (k' : Fin I'.clients → ℕ),
      encodePerClient I' k' = encodePerClient I k ∧ ∀ j, k' j ≤ I'.days := ⟨I, k, rfl, hk⟩
  unfold Lax117284.Lemma15.reduce
  rw [dif_pos h]
  have key : ∀ (I' : Instance) (k' : Fin I'.clients → ℕ),
      encodePerClient I' k' = encodePerClient I k →
      (if I'.clients = 0 then encodeUniform (Lax117284.Corollary8.noClients 0) 0
        else encodeUniform (Lax117284.Lemma15.inst I' k') I'.days)
        = encodeUniform (Lax117284.Lemma15.inst I k) I.days := by
    intro I' k' h'
    obtain ⟨rfl, hk'⟩ := Injectivity.encodePerClient_inj h'
    obtain rfl := eq_of_heq hk'
    rw [if_neg (by omega)]
  exact key _ _ h.choose_spec.choose_spec.1

theorem uniform_mono {C C' : Instance → ℕ → Prop} (h : ∀ I k, C I k → C' I k) {w : Word}
    (hw : w ∈ Uniform C) : w ∈ Uniform C' := by
  obtain ⟨I, k, hw, hC, hF⟩ := hw
  exact ⟨I, k, hw, h I k hC, hF⟩

/--
---
conclusion: Lax117284.Theorem4.uniform_treewidth_npHard
---
Compose the two reductions of Lemmas 14 and 15. The image of the first is the code of an
instance of treewidth at most four whose parameters are at most its number of days, or the
rejected word; the second raises the treewidth by at most two.
-/
theorem uniform_treewidth_npHard :
    NPHard (Uniform fun I _ => Lax117284.ConflictGraph.treewidth I ≤ 6) := by
  refine npHard_of_manyOne Lax117284Proofs.McisHard.normalMulticolouredIndepSet_npHard_proved ?_
  obtain ⟨hf⟩ := Lax117284.Lemma14.reduce_polyTime
  obtain ⟨hg⟩ := Lax117284.Lemma15.reduce_polyTime
  refine ⟨Lax117284.Lemma15.reduce ∘ Lax117284.Lemma14.reduce,
    Lax434930Proofs.PolynomialComposition.comp hf hg, fun x => ?_⟩
  classical
  by_cases h : ∃ G : Lax117284.MulticolouredIndepSet.Instance,
      Lax117284.MulticolouredIndepSet.encodeInstance G = x ∧ G.Normal
  · obtain ⟨G, hG, hN⟩ := h
    have hk := Lax117284.Lemma14.kvec_le_days G
    simp only [Function.comp]
    rw [reduce14_eq hG hN, reduce15_eq hk (by
      show 0 < Lax117284.Lemma14.clientCount G
      unfold Lax117284.Lemma14.clientCount; omega), uniform_mem_encode]
    have hc14 := Lax117284.Lemma14.correct G hN
    have hc15 := Lax117284.Lemma15.correct (Lax117284.Lemma14.inst G)
      (Lax117284.Lemma14.kvec G) hk
    have htw14 := Lax117284.Lemma14.treewidth_le G
    have htw15 := Lax117284.Lemma15.treewidth_le (Lax117284.Lemma14.inst G)
      (Lax117284.Lemma14.kvec G)
    constructor
    · rintro ⟨G', hG', -, hI⟩
      have : G' = G := SourceInjectivity.mis_encode_inj (hG'.trans hG.symm)
      subst this
      exact ⟨by omega, hc15.1 (hc14.1 hI)⟩
    · rintro ⟨-, hF⟩
      exact ⟨G, hG, hN, hc14.2 (hc15.2 hF)⟩
  · have h14 : Lax117284.Lemma14.reduce x = rejectedPerClient := by
      unfold Lax117284.Lemma14.reduce
      rw [dif_neg h]
    simp only [Function.comp]
    rw [h14]
    constructor
    · rintro ⟨G, hG, hN, -⟩
      exact absurd ⟨G, hG, hN⟩ h
    · intro hmem
      have h15 := lemma15_reduce_correct rejectedPerClient
      have hmem' : Lax117284.Lemma15.reduce rejectedPerClient ∈ Uniform any :=
        uniform_mono (fun _ _ _ => trivial) hmem
      exact absurd (h15.2 hmem') (Injectivity.rejectedPerClient_notMem _)


/-! ### Theorem 1

The two steps of Corollary 8 are correct for the instances of a given number of days and a
given fairness parameter, whether or not the processing times are day-independent: nothing
about the answer depends on it. Starting from the instances of three days and parameter one
that Theorem 7 gives, a number of steps of the second kind reach every number of days above
`k + 1`, and `k - 1` of the first kind then raise the parameter to `k`. -/

theorem free_general (m k : ℕ) (hm : 0 < m) (w : Word) :
    w ∈ Uniform (fun I k' => I.days = m ∧ k' = k) ↔
      Lax117284.Corollary8.reduceFreeDay w ∈ Uniform fun I k' => I.days = m + 1 ∧ k' = k + 1 := by
  classical
  by_cases h : ∃ (I : Instance) (k : ℕ), encodeUniform I k = w ∧ 0 < I.days
  · unfold Lax117284.Corollary8.reduceFreeDay
    rw [dif_pos h]
    obtain ⟨hw, hpos⟩ := h.choose_spec.choose_spec
    have e : w ∈ Uniform (fun I k' => I.days = m ∧ k' = k) ↔
        encodeUniform h.choose h.choose_spec.choose ∈
          Uniform (fun I k' => I.days = m ∧ k' = k) := by rw [hw]
    rw [e, uniform_mem_encode, uniform_mem_encode]
    have hc := Lax117284.Corollary8.addFreeDay_correct h.choose hpos h.choose_spec.choose
    have hd : (Lax117284.Corollary8.addFreeDay h.choose).days = h.choose.days + 1 := rfl
    constructor
    · rintro ⟨⟨h1, h2⟩, hF⟩
      exact ⟨⟨by omega, by omega⟩, hc.1 hF⟩
    · rintro ⟨⟨h1, h2⟩, hF⟩
      exact ⟨⟨by omega, by omega⟩, hc.2 hF⟩
  · unfold Lax117284.Corollary8.reduceFreeDay
    rw [dif_neg h]
    constructor
    · rintro ⟨I, k', hw, hC, -⟩
      exact absurd ⟨I, k', hw, by omega⟩ h
    · intro hmem
      exact absurd hmem (Injectivity.rejected_notMem _)

theorem blocking_general (m : ℕ) (hm : 0 < m) (w : Word) :
    w ∈ Uniform (fun I k' => I.days = m ∧ k' = 1) ↔
      Lax117284.Corollary8.reduceBlockingDay w ∈ Uniform fun I k' => I.days = m + 1 ∧ k' = 1 := by
  classical
  by_cases h : ∃ (I : Instance) (k : ℕ), encodeUniform I k = w ∧ 0 < I.days ∧ k = 1
  · unfold Lax117284.Corollary8.reduceBlockingDay
    rw [dif_pos h]
    obtain ⟨hw, hpos, hk1⟩ := h.choose_spec.choose_spec
    have e : w ∈ Uniform (fun I k' => I.days = m ∧ k' = 1) ↔
        encodeUniform h.choose h.choose_spec.choose ∈
          Uniform (fun I k' => I.days = m ∧ k' = 1) := by rw [hw]
    by_cases hc0 : h.choose.clients = 0
    · rw [if_pos hc0, e, uniform_mem_encode, uniform_mem_encode]
      have hF := hasKFair_of_clients_zero h.choose hc0 1
      have hF' := hasKFair_of_clients_zero (Lax117284.Corollary8.noClients (h.choose.days + 1))
        rfl 1
      rw [hk1]
      constructor
      · rintro ⟨⟨h1, h2⟩, -⟩
        exact ⟨⟨by show h.choose.days + 1 = m + 1; omega, rfl⟩, hF'⟩
      · rintro ⟨⟨h1, h2⟩, -⟩
        exact ⟨⟨by change h.choose.days + 1 = m + 1 at h1; omega, rfl⟩, hF⟩
    rw [if_neg hc0, e, uniform_mem_encode, uniform_mem_encode]
    have hc := Lax117284.Corollary8.addBlockingDay_correct h.choose hpos
    have hd : (Lax117284.Corollary8.addBlockingDay h.choose).days = h.choose.days + 1 := rfl
    rw [hk1]
    constructor
    · rintro ⟨⟨h1, h2⟩, hF⟩
      exact ⟨⟨by omega, rfl⟩, hc.1 hF⟩
    · rintro ⟨⟨h1, h2⟩, hF⟩
      exact ⟨⟨by omega, rfl⟩, hc.2 hF⟩
  · unfold Lax117284.Corollary8.reduceBlockingDay
    rw [dif_neg h]
    constructor
    · rintro ⟨I, k', hw, ⟨h1, h2⟩, -⟩
      exact absurd ⟨I, k', hw, by omega, h2⟩ h
    · intro hmem
      exact absurd hmem (Injectivity.rejected_notMem _)

/-- Hardness at `m` days and fairness parameter `k`, for the source of Theorem 7. -/
def HardAt (m k : ℕ) : Prop :=
  ManyOne Lax117284.BoundedSat.BoundedSat (Uniform fun I k' => I.days = m ∧ k' = k)

theorem hardAt_three_one : HardAt 3 1 :=
  boundedSat_manyOne _ fun φ => ⟨Lax117284.Theorem7.inst_days φ, rfl⟩

theorem hardAt_block {m : ℕ} (hm : 0 < m) (h : HardAt m 1) : HardAt (m + 1) 1 :=
  manyOne_trans h ⟨Lax117284.Corollary8.reduceBlockingDay,
    Lax117284.Corollary8.reduceBlockingDay_polyTime, blocking_general m hm⟩

theorem hardAt_free {m k : ℕ} (hm : 0 < m) (h : HardAt m k) : HardAt (m + 1) (k + 1) :=
  manyOne_trans h ⟨Lax117284.Corollary8.reduceFreeDay,
    Lax117284.Corollary8.reduceFreeDay_polyTime, free_general m k hm⟩

theorem hardAt_blocks : ∀ n : ℕ, HardAt (3 + n) 1
  | 0 => hardAt_three_one
  | n + 1 => hardAt_block (m := 3 + n) (by omega) (hardAt_blocks n)

theorem hardAt_frees {m : ℕ} (hm : 0 < m) (h : HardAt m 1) : ∀ j : ℕ, HardAt (m + j) (1 + j)
  | 0 => h
  | j + 1 => by
      have := hardAt_free (by omega : 0 < m + j) (hardAt_frees hm h j)
      rwa [show m + (j + 1) = m + j + 1 by omega, show 1 + (j + 1) = 1 + j + 1 by omega]

/--
---
conclusion: Lax117284.Theorem1.uniform_npHard
---
From the instances of three days and parameter one of Theorem 7, `m - k - 2` steps of the
blocking day and then `k - 1` of the free day reach `m` days and parameter `k`.
-/
theorem uniform_npHard (m k : ℕ) (hm : 3 ≤ m) (hk : 0 < k) (hk' : k + 1 < m) :
    NPHard (Uniform fun I k' => I.days = m ∧ k' = k) := by
  refine npHard_of_manyOne Lax117284Proofs.BoundedSatProved.boundedSat_npHard_proved ?_
  have h1 := hardAt_blocks (m - k - 2)
  have h2 := hardAt_frees (by omega : 0 < 3 + (m - k - 2)) h1 (k - 1)
  rwa [show 3 + (m - k - 2) + (k - 1) = m by omega, show 1 + (k - 1) = k by omega] at h2

end Lax117284Proofs.Hardness
