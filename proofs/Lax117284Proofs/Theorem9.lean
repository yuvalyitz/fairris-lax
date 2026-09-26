import Lax117284Proofs.Bridge
import Lax117284.Theorem9

/-!
The fairness parameter one below the number of days, as a 2-CNF formula. The clauses of the
concept are numbered rather than enumerated, so the argument is carried out on the numbering
directly: a slot is admissible exactly when the pair it decodes to is one the source's
construction names, and an inadmissible slot carries a tautology.
-/

namespace Lax117284Proofs.Theorem9

open Lax117284.Scheduling Lax117284.TwoSatisfiability Lax117284.Theorem9

variable {I : Instance}

/-! ### The numbering of the variables -/

theorem varIdx_val {i j : ℕ} (hi : i < I.days) (hj : j < I.clients) :
    ((varIdx I i j : Fin (I.days * I.clients + 1)) : ℕ) = i * I.clients + j := by
  have hlt : i * I.clients + j < I.days * I.clients := by
    calc i * I.clients + j < i * I.clients + I.clients := by omega
      _ = (i + 1) * I.clients := by ring
      _ ≤ I.days * I.clients := Nat.mul_le_mul_right _ (by omega)
  simp [varIdx, Nat.min_eq_left (le_of_lt hlt)]

theorem varIdx_inj {i i' j j' : ℕ} (hi : i < I.days) (hj : j < I.clients)
    (hi' : i' < I.days) (hj' : j' < I.clients)
    (h : (varIdx I i j : Fin (I.days * I.clients + 1)) = varIdx I i' j') :
    i = i' ∧ j = j' := by
  have hc : 0 < I.clients := by omega
  have he : i * I.clients + j = i' * I.clients + j' := by
    rw [← varIdx_val hi hj, ← varIdx_val hi' hj', h]
  have hi'' : i = i' := by
    rcases Nat.lt_trichotomy i i' with h1 | h1 | h1
    · have : (i + 1) * I.clients ≤ i' * I.clients := Nat.mul_le_mul_right _ (by omega)
      have hexp : (i + 1) * I.clients = i * I.clients + I.clients := by ring
      omega
    · exact h1
    · have : (i' + 1) * I.clients ≤ i * I.clients := Nat.mul_le_mul_right _ (by omega)
      have hexp : (i' + 1) * I.clients = i' * I.clients + I.clients := by ring
      omega
  exact ⟨hi'', by rw [hi''] at he; omega⟩

/-! ### The numbering of the clauses -/

/-- The number of the conflict clause of a day and an ordered pair of clients. -/
def conflictSlot (I : Instance) (i j₁ j₂ : ℕ) : ℕ :=
  (j₂ + I.clients * j₁) + I.clients * I.clients * i

/-- The number of the validation clause of a client and an ordered pair of days. -/
def validSlot (I : Instance) (j i₁ i₂ : ℕ) : ℕ :=
  I.days * I.clients * I.clients + ((i₂ + I.days * i₁) + I.days * I.days * j)

theorem conflictSlot_lt {i j₁ j₂ : ℕ} (hi : i < I.days) (h1 : j₁ < I.clients)
    (h2 : j₂ < I.clients) : conflictSlot I i j₁ j₂ < I.days * I.clients * I.clients := by
  have hc : 0 < I.clients := by omega
  have hj : j₂ + I.clients * j₁ < I.clients * I.clients := by
    have : I.clients * (j₁ + 1) ≤ I.clients * I.clients := Nat.mul_le_mul_left _ (by omega)
    have hexp : I.clients * (j₁ + 1) = I.clients * j₁ + I.clients := by ring
    omega
  have hmul : I.clients * I.clients * (i + 1) ≤ I.clients * I.clients * I.days :=
    Nat.mul_le_mul_left _ (by omega)
  have hexp : I.clients * I.clients * (i + 1)
      = I.clients * I.clients * i + I.clients * I.clients := by ring
  have hcomm : I.clients * I.clients * I.days = I.days * I.clients * I.clients := by ring
  simp only [conflictSlot]
  omega

theorem conflictSlot_div {i j₁ j₂ : ℕ} (hi : i < I.days) (h1 : j₁ < I.clients)
    (h2 : j₂ < I.clients) : conflictSlot I i j₁ j₂ / (I.clients * I.clients) = i := by
  have hc : 0 < I.clients := by omega
  have hj : j₂ + I.clients * j₁ < I.clients * I.clients := by
    have : I.clients * (j₁ + 1) ≤ I.clients * I.clients := Nat.mul_le_mul_left _ (by omega)
    have hexp : I.clients * (j₁ + 1) = I.clients * j₁ + I.clients := by ring
    omega
  simp only [conflictSlot]
  rw [Nat.add_mul_div_left _ _ (Nat.mul_pos hc hc), Nat.div_eq_of_lt hj]
  omega

theorem conflictSlot_mod {i j₁ j₂ : ℕ} (hi : i < I.days) (h1 : j₁ < I.clients)
    (h2 : j₂ < I.clients) :
    conflictSlot I i j₁ j₂ % (I.clients * I.clients) / I.clients = j₁ ∧
      conflictSlot I i j₁ j₂ % (I.clients * I.clients) % I.clients = j₂ := by
  have hc : 0 < I.clients := by omega
  have hj : j₂ + I.clients * j₁ < I.clients * I.clients := by
    have : I.clients * (j₁ + 1) ≤ I.clients * I.clients := Nat.mul_le_mul_left _ (by omega)
    have hexp : I.clients * (j₁ + 1) = I.clients * j₁ + I.clients := by ring
    omega
  have hmod : conflictSlot I i j₁ j₂ % (I.clients * I.clients) = j₂ + I.clients * j₁ := by
    simp only [conflictSlot]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  refine ⟨?_, ?_⟩
  · rw [hmod, Nat.add_mul_div_left _ _ hc, Nat.div_eq_of_lt h2]
    omega
  · rw [hmod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]

theorem validSlot_not_lt {j i₁ i₂ : ℕ} (hj : j < I.clients) (h1 : i₁ < I.days)
    (h2 : i₂ < I.days) : ¬ validSlot I j i₁ i₂ < I.days * I.clients * I.clients := by
  simp only [validSlot]
  omega

theorem validSlot_sub {j i₁ i₂ : ℕ} :
    validSlot I j i₁ i₂ - I.days * I.clients * I.clients
      = (i₂ + I.days * i₁) + I.days * I.days * j := by
  simp only [validSlot]
  omega

theorem validSlot_decode {j i₁ i₂ : ℕ} (hj : j < I.clients) (h1 : i₁ < I.days)
    (h2 : i₂ < I.days) :
    (validSlot I j i₁ i₂ - I.days * I.clients * I.clients) / (I.days * I.days) = j ∧
      (validSlot I j i₁ i₂ - I.days * I.clients * I.clients) % (I.days * I.days)
          / I.days = i₁ ∧
      (validSlot I j i₁ i₂ - I.days * I.clients * I.clients) % (I.days * I.days)
          % I.days = i₂ := by
  have hd : 0 < I.days := by omega
  have hi : i₂ + I.days * i₁ < I.days * I.days := by
    have : I.days * (i₁ + 1) ≤ I.days * I.days := Nat.mul_le_mul_left _ (by omega)
    have hexp : I.days * (i₁ + 1) = I.days * i₁ + I.days := by ring
    omega
  have hmod : (validSlot I j i₁ i₂ - I.days * I.clients * I.clients) % (I.days * I.days)
      = i₂ + I.days * i₁ := by
    rw [validSlot_sub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  refine ⟨?_, ?_, ?_⟩
  · rw [validSlot_sub, Nat.add_mul_div_left _ _ (Nat.mul_pos hd hd), Nat.div_eq_of_lt hi]
    omega
  · rw [hmod, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt h2]
    omega
  · rw [hmod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]

theorem validSlot_lt {j i₁ i₂ : ℕ} (hj : j < I.clients) (h1 : i₁ < I.days)
    (h2 : i₂ < I.days) :
    validSlot I j i₁ i₂ <
      I.days * I.clients * I.clients + I.clients * I.days * I.days := by
  have hd : 0 < I.days := by omega
  have hi : i₂ + I.days * i₁ < I.days * I.days := by
    have : I.days * (i₁ + 1) ≤ I.days * I.days := Nat.mul_le_mul_left _ (by omega)
    have hexp : I.days * (i₁ + 1) = I.days * i₁ + I.days := by ring
    omega
  have hmul : I.days * I.days * (j + 1) ≤ I.days * I.days * I.clients :=
    Nat.mul_le_mul_left _ (by omega)
  have hexp : I.days * I.days * (j + 1) = I.days * I.days * j + I.days * I.days := by ring
  have hcomm : I.days * I.days * I.clients = I.clients * I.days * I.days := by ring
  simp only [validSlot]
  omega


/-! ### Counting the days a client is served -/

theorem served_add_two_le {σ : I.Schedule} {j : Fin I.clients} {i₁ i₂ : Fin I.days}
    (hne : i₁ ≠ i₂) (h1 : j ∉ σ i₁) (h2 : j ∉ σ i₂) :
    Instance.served σ j + 2 ≤ I.days := by
  classical
  have hsub : (Finset.univ.filter fun i => j ∈ σ i)
      ⊆ Finset.univ \ ({i₁, i₂} : Finset (Fin I.days)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact h1 hi
    · exact h2 hi
  have hcard := Finset.card_le_card hsub
  have hpair : ({i₁, i₂} : Finset (Fin I.days)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have huniv : (Finset.univ : Finset (Fin I.days)).card = I.days := by
    simp
  have hdiff : (Finset.univ \ ({i₁, i₂} : Finset (Fin I.days))).card
      + ({i₁, i₂} : Finset (Fin I.days)).card = (Finset.univ : Finset (Fin I.days)).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
  have h2le : 2 ≤ I.days := by
    have := i₁.isLt
    have := i₂.isLt
    have : (i₁ : ℕ) ≠ (i₂ : ℕ) := fun h => hne (Fin.ext h)
    omega
  simp only [Instance.served]
  omega

theorem days_le_served_add_one {σ : I.Schedule} {j : Fin I.clients}
    (h : ∀ i₁ i₂ : Fin I.days, j ∉ σ i₁ → j ∉ σ i₂ → i₁ = i₂) :
    I.days ≤ Instance.served σ j + 1 := by
  classical
  have hsplit : (Finset.univ.filter fun i : Fin I.days => j ∈ σ i).card
      + (Finset.univ.filter fun i : Fin I.days => ¬ j ∈ σ i).card
      = (Finset.univ : Finset (Fin I.days)).card :=
    Finset.card_filter_add_card_filter_not _
  have hone : (Finset.univ.filter fun i : Fin I.days => ¬ j ∈ σ i).card ≤ 1 := by
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact h a b ha hb
  have huniv : (Finset.univ : Finset (Fin I.days)).card = I.days := by simp
  simp only [Instance.served]
  omega

/-! ### Schedules and assignments -/

open Classical in
/-- The assignment read off a schedule: the variable of a day and a client holds exactly
when that client is served on that day. -/
noncomputable def assign (σ : I.Schedule) : (formula I).Assignment :=
  fun v => decide (∃ (i : Fin I.days) (j : Fin I.clients),
    (varIdx I i j : Fin (I.days * I.clients + 1)) = v ∧ j ∈ σ i)

theorem assign_apply {σ : I.Schedule} (i : Fin I.days) (j : Fin I.clients) :
    assign σ (varIdx I i j) = true ↔ j ∈ σ i := by
  classical
  simp only [assign, decide_eq_true_eq]
  refine ⟨?_, fun h => ⟨i, j, rfl, h⟩⟩
  rintro ⟨i', j', hv, hm⟩
  obtain ⟨hi, hj⟩ := varIdx_inj (I := I) i'.isLt j'.isLt i.isLt j.isLt hv
  rwa [Fin.ext hi, Fin.ext hj] at hm

/-- The schedule read off an assignment. -/
noncomputable def sched (a : (formula I).Assignment) : I.Schedule :=
  fun i => Finset.univ.filter fun j => a (varIdx I i j) = true

theorem mem_sched {a : (formula I).Assignment} (i : Fin I.days) (j : Fin I.clients) :
    j ∈ sched a i ↔ a (varIdx I i j) = true := by
  simp [sched]


/-! ### The formula is satisfiable exactly when the instance is a yes-instance -/

theorem clients_pos_of_clause {c : ℕ}
    (hc : c < I.days * I.clients * I.clients + I.clients * I.days * I.days) :
    0 < I.clients ∧ 0 < I.days := by
  rcases Nat.eq_zero_or_pos I.clients with h | h
  · rw [h] at hc; simp at hc
  rcases Nat.eq_zero_or_pos I.days with h' | h'
  · rw [h'] at hc; simp at hc
  exact ⟨h, h'⟩

/-- The two literals of an admissible conflict slot forbid the two clients it names. -/
theorem clauseLit_conflict {c : ℕ} (hc : c < I.days * I.clients * I.clients)
    (hadm : c % (I.clients * I.clients) / I.clients ≠ c % (I.clients * I.clients) % I.clients ∧
      I.ConflictAt (c / (I.clients * I.clients)) (c % (I.clients * I.clients) / I.clients)
        (c % (I.clients * I.clients) % I.clients)) :
    clauseLit I c 0 = (varIdx I (c / (I.clients * I.clients))
        (c % (I.clients * I.clients) / I.clients), false) ∧
      clauseLit I c 1 = (varIdx I (c / (I.clients * I.clients))
        (c % (I.clients * I.clients) % I.clients), false) := by
  constructor <;> simp only [clauseLit, if_pos hc] <;> rw [if_pos hadm] <;> simp

/-- An inadmissible conflict slot carries a tautology on the variable it names. -/
theorem clauseLit_conflict_taut {c : ℕ} (hc : c < I.days * I.clients * I.clients)
    (hadm : ¬ (c % (I.clients * I.clients) / I.clients ≠
        c % (I.clients * I.clients) % I.clients ∧
      I.ConflictAt (c / (I.clients * I.clients)) (c % (I.clients * I.clients) / I.clients)
        (c % (I.clients * I.clients) % I.clients))) :
    clauseLit I c 0 = (varIdx I (c / (I.clients * I.clients))
        (c % (I.clients * I.clients) / I.clients), true) ∧
      clauseLit I c 1 = (varIdx I (c / (I.clients * I.clients))
        (c % (I.clients * I.clients) / I.clients), false) := by
  constructor <;> simp only [clauseLit, if_pos hc] <;> rw [if_neg hadm] <;> simp

/-- The two literals of an admissible validation slot ask for one of the two days. -/
theorem clauseLit_valid {c : ℕ} (hc : ¬ c < I.days * I.clients * I.clients)
    (hne : (c - I.days * I.clients * I.clients) % (I.days * I.days) / I.days ≠
      (c - I.days * I.clients * I.clients) % (I.days * I.days) % I.days) :
    clauseLit I c 0 = (varIdx I ((c - I.days * I.clients * I.clients) % (I.days * I.days)
          / I.days)
        ((c - I.days * I.clients * I.clients) / (I.days * I.days)), true) ∧
      clauseLit I c 1 = (varIdx I ((c - I.days * I.clients * I.clients) % (I.days * I.days)
          % I.days)
        ((c - I.days * I.clients * I.clients) / (I.days * I.days)), true) := by
  constructor <;> simp only [clauseLit, if_neg hc] <;> rw [if_pos hne] <;> simp

/-- An inadmissible validation slot carries a tautology on the variable it names. -/
theorem clauseLit_valid_taut {c : ℕ} (hc : ¬ c < I.days * I.clients * I.clients)
    (hne : ¬ (c - I.days * I.clients * I.clients) % (I.days * I.days) / I.days ≠
      (c - I.days * I.clients * I.clients) % (I.days * I.days) % I.days) :
    clauseLit I c 0 = (varIdx I ((c - I.days * I.clients * I.clients) % (I.days * I.days)
          / I.days)
        ((c - I.days * I.clients * I.clients) / (I.days * I.days)), true) ∧
      clauseLit I c 1 = (varIdx I ((c - I.days * I.clients * I.clients) % (I.days * I.days)
          / I.days)
        ((c - I.days * I.clients * I.clients) / (I.days * I.days)), false) := by
  constructor <;> simp only [clauseLit, if_neg hc] <;> rw [if_neg hne] <;> simp

/-- The assignment read off a feasible schedule serving every client on all but one day
satisfies every clause. -/
theorem satisfies_assign {σ : I.Schedule} {k : ℕ} (hk : k + 1 = I.days)
    (hfeas : Instance.Feasible σ) (hfair : Instance.Fair (fun _ => k) σ) :
    (formula I).Satisfies (assign σ) := by
  classical
  intro c
  obtain ⟨hcpos, hdpos⟩ := clients_pos_of_clause (I := I) c.isLt
  show ∃ α, assign σ (clauseLit I (c : ℕ) α).1 = (clauseLit I (c : ℕ) α).2
  by_cases hc : (c : ℕ) < I.days * I.clients * I.clients
  · have hcomm : I.clients * I.clients * I.days = I.days * I.clients * I.clients := by ring
    have hr : (c : ℕ) % (I.clients * I.clients) < I.clients * I.clients :=
      Nat.mod_lt _ (Nat.mul_pos hcpos hcpos)
    have hi : (c : ℕ) / (I.clients * I.clients) < I.days :=
      Nat.div_lt_of_lt_mul (by omega)
    have hj1 : (c : ℕ) % (I.clients * I.clients) / I.clients < I.clients :=
      Nat.div_lt_of_lt_mul hr
    have hj2 : (c : ℕ) % (I.clients * I.clients) % I.clients < I.clients :=
      Nat.mod_lt _ hcpos
    by_cases hadm : (c : ℕ) % (I.clients * I.clients) / I.clients ≠
        (c : ℕ) % (I.clients * I.clients) % I.clients ∧
        I.ConflictAt ((c : ℕ) / (I.clients * I.clients))
          ((c : ℕ) % (I.clients * I.clients) / I.clients)
          ((c : ℕ) % (I.clients * I.clients) % I.clients)
    · obtain ⟨hl0, hl1⟩ := clauseLit_conflict (I := I) hc hadm
      have hne : (⟨_, hj1⟩ : Fin I.clients) ≠ ⟨_, hj2⟩ := fun h =>
        hadm.1 (by simpa using congrArg Fin.val h)
      have hconf : I.Conflict (⟨_, hi⟩ : Fin I.days) ⟨_, hj1⟩ ⟨_, hj2⟩ :=
        (Instance.conflictAt_iff (I := I) ⟨_, hi⟩ ⟨_, hj1⟩ ⟨_, hj2⟩).1 hadm.2
      have hnot : ¬ ((⟨_, hj1⟩ : Fin I.clients) ∈ σ ⟨_, hi⟩ ∧
          (⟨_, hj2⟩ : Fin I.clients) ∈ σ ⟨_, hi⟩) := by
        rintro ⟨hm1, hm2⟩
        exact hfeas ⟨_, hi⟩ (Finset.mem_coe.2 hm1) (Finset.mem_coe.2 hm2) hne hconf
      rcases not_and_or.1 hnot with hm | hm
      · refine ⟨0, ?_⟩
        rw [hl0]
        simpa using fun h => hm ((assign_apply (I := I) ⟨_, hi⟩ ⟨_, hj1⟩).1 h)
      · refine ⟨1, ?_⟩
        rw [hl1]
        simpa using fun h => hm ((assign_apply (I := I) ⟨_, hi⟩ ⟨_, hj2⟩).1 h)
    · obtain ⟨hl0, hl1⟩ := clauseLit_conflict_taut (I := I) hc hadm
      by_cases hv : assign σ (varIdx I ((c : ℕ) / (I.clients * I.clients))
          ((c : ℕ) % (I.clients * I.clients) / I.clients)) = true
      · exact ⟨0, by rw [hl0]; exact hv⟩
      · exact ⟨1, by rw [hl1]; simpa using hv⟩
  · have hcomm : I.days * I.days * I.clients = I.clients * I.days * I.days := by ring
    have hsub : (c : ℕ) - I.days * I.clients * I.clients < I.clients * I.days * I.days := by
      have hcl : (formula I).clauses
          = I.days * I.clients * I.clients + I.clients * I.days * I.days := rfl
      have := c.isLt
      omega
    have hr : ((c : ℕ) - I.days * I.clients * I.clients) % (I.days * I.days)
        < I.days * I.days := Nat.mod_lt _ (Nat.mul_pos hdpos hdpos)
    have hj : ((c : ℕ) - I.days * I.clients * I.clients) / (I.days * I.days) < I.clients :=
      Nat.div_lt_of_lt_mul (by omega)
    have hi1 : ((c : ℕ) - I.days * I.clients * I.clients) % (I.days * I.days) / I.days
        < I.days := Nat.div_lt_of_lt_mul hr
    have hi2 : ((c : ℕ) - I.days * I.clients * I.clients) % (I.days * I.days) % I.days
        < I.days := Nat.mod_lt _ hdpos
    by_cases hne : ((c : ℕ) - I.days * I.clients * I.clients) % (I.days * I.days) / I.days ≠
        ((c : ℕ) - I.days * I.clients * I.clients) % (I.days * I.days) % I.days
    · obtain ⟨hl0, hl1⟩ := clauseLit_valid (I := I) hc hne
      have hne' : (⟨_, hi1⟩ : Fin I.days) ≠ ⟨_, hi2⟩ := fun h =>
        hne (by simpa using congrArg Fin.val h)
      have hmem : (⟨_, hj⟩ : Fin I.clients) ∈ σ ⟨_, hi1⟩ ∨
          (⟨_, hj⟩ : Fin I.clients) ∈ σ ⟨_, hi2⟩ := by
        by_contra hcon
        rcases not_or.1 hcon with ⟨h1, h2⟩
        have hcount := served_add_two_le (I := I) hne' h1 h2
        have hf : k ≤ Instance.served σ ⟨_, hj⟩ := hfair ⟨_, hj⟩
        omega
      rcases hmem with hm | hm
      · exact ⟨0, by rw [hl0]; exact (assign_apply (I := I) ⟨_, hi1⟩ ⟨_, hj⟩).2 hm⟩
      · exact ⟨1, by rw [hl1]; exact (assign_apply (I := I) ⟨_, hi2⟩ ⟨_, hj⟩).2 hm⟩
    · obtain ⟨hl0, hl1⟩ := clauseLit_valid_taut (I := I) hc hne
      by_cases hv : assign σ (varIdx I
          (((c : ℕ) - I.days * I.clients * I.clients) % (I.days * I.days) / I.days)
          (((c : ℕ) - I.days * I.clients * I.clients) / (I.days * I.days))) = true
      · exact ⟨0, by rw [hl0]; exact hv⟩
      · exact ⟨1, by rw [hl1]; simpa using hv⟩


/-- A satisfying assignment gives a feasible schedule serving every client on all but one
day. -/
theorem hasKFairSchedule_of_satisfies {a : (formula I).Assignment}
    (ha : (formula I).Satisfies a) {k : ℕ} (hk : k + 1 = I.days) :
    I.HasKFairSchedule k := by
  classical
  have hcl : (formula I).clauses
      = I.days * I.clients * I.clients + I.clients * I.days * I.days := rfl
  refine ⟨sched a, ?_, fun j => ?_⟩
  · intro i x hx y hy hne hconf
    have hx' : a (varIdx I i x) = true := (mem_sched i x).1 (Finset.mem_coe.1 hx)
    have hy' : a (varIdx I i y) = true := (mem_sched i y).1 (Finset.mem_coe.1 hy)
    have hclt : conflictSlot I i x y < I.days * I.clients * I.clients :=
      conflictSlot_lt i.isLt x.isLt y.isLt
    have hdiv := conflictSlot_div (I := I) i.isLt x.isLt y.isLt
    obtain ⟨hm1, hm2⟩ := conflictSlot_mod (I := I) i.isLt x.isLt y.isLt
    have hadm : conflictSlot I i x y % (I.clients * I.clients) / I.clients ≠
        conflictSlot I i x y % (I.clients * I.clients) % I.clients ∧
        I.ConflictAt (conflictSlot I i x y / (I.clients * I.clients))
          (conflictSlot I i x y % (I.clients * I.clients) / I.clients)
          (conflictSlot I i x y % (I.clients * I.clients) % I.clients) := by
      rw [hdiv, hm1, hm2]
      exact ⟨fun h => hne (Fin.ext h), (Instance.conflictAt_iff (I := I) i x y).2 hconf⟩
    obtain ⟨hl0, hl1⟩ := clauseLit_conflict (I := I) hclt hadm
    obtain ⟨α, hα⟩ := ha ⟨conflictSlot I i x y, by omega⟩
    have hlit : ∀ β : Fin 2, (formula I).lit ⟨conflictSlot I i x y, by omega⟩ β
        = clauseLit I (conflictSlot I i x y) β := fun _ => rfl
    rw [hlit] at hα
    rcases (by omega : (α : ℕ) = 0 ∨ (α : ℕ) = 1) with h | h
    · have hα0 : α = 0 := Fin.ext (by simpa using h)
      rw [hα0, hl0, hdiv, hm1] at hα
      rw [hx'] at hα
      exact Bool.noConfusion hα
    · have hα1 : α = 1 := Fin.ext (by simpa using h)
      rw [hα1, hl1, hdiv, hm2] at hα
      rw [hy'] at hα
      exact Bool.noConfusion hα
  · show k ≤ Instance.served (sched a) j
    have huniq : ∀ i₁ i₂ : Fin I.days, j ∉ sched a i₁ → j ∉ sched a i₂ → i₁ = i₂ := by
      intro i₁ i₂ h1 h2
      by_contra hne
      have hclt : ¬ validSlot I j i₁ i₂ < I.days * I.clients * I.clients :=
        validSlot_not_lt j.isLt i₁.isLt i₂.isLt
      obtain ⟨hdj, hdi1, hdi2⟩ := validSlot_decode (I := I) j.isLt i₁.isLt i₂.isLt
      have hne' : (validSlot I j i₁ i₂ - I.days * I.clients * I.clients) % (I.days * I.days)
          / I.days ≠
          (validSlot I j i₁ i₂ - I.days * I.clients * I.clients) % (I.days * I.days)
          % I.days := by
        rw [hdi1, hdi2]
        exact fun h => hne (Fin.ext h)
      obtain ⟨hl0, hl1⟩ := clauseLit_valid (I := I) hclt hne'
      have hb : validSlot I j i₁ i₂ < (formula I).clauses := by
        have := validSlot_lt (I := I) j.isLt i₁.isLt i₂.isLt
        omega
      obtain ⟨α, hα⟩ := ha ⟨validSlot I j i₁ i₂, hb⟩
      have hlit : ∀ β : Fin 2, (formula I).lit ⟨validSlot I j i₁ i₂, hb⟩ β
          = clauseLit I (validSlot I j i₁ i₂) β := fun _ => rfl
      rw [hlit] at hα
      rcases (by omega : (α : ℕ) = 0 ∨ (α : ℕ) = 1) with h | h
      · have hα0 : α = 0 := Fin.ext (by simpa using h)
        rw [hα0, hl0, hdi1, hdj] at hα
        exact h1 ((mem_sched i₁ j).2 hα)
      · have hα1 : α = 1 := Fin.ext (by simpa using h)
        rw [hα1, hl1, hdi2, hdj] at hα
        exact h2 ((mem_sched i₂ j).2 hα)
    have := days_le_served_add_one (I := I) huniq
    omega

/--
---
conclusion: Lax117284.Theorem9.correct
---
The variable of a day and a client says that the client is served on that day. The conflict
clauses are exactly feasibility, and the validation clauses say that no client is rejected
on two days, which at this fairness parameter is fairness.
-/
theorem correct (I : Instance) (k : ℕ) (hk : k + 1 = I.days) :
    I.HasKFairSchedule k ↔ (formula I).Satisfiable := by
  refine ⟨?_, ?_⟩
  · rintro ⟨σ, hfeas, hfair⟩
    exact ⟨assign σ, satisfies_assign hk hfeas hfair⟩
  · rintro ⟨a, ha⟩
    exact hasKFairSchedule_of_satisfies ha hk

end Lax117284Proofs.Theorem9
