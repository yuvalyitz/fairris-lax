import Lax117284Proofs.ClientsILPInst

/-!
The regrouped integer program has a solution exactly when the integer program of `Theorem4ILP`
does.
-/

namespace Lax117284Proofs.ClientsILP

open Finset Lax117284.Scheduling

/-- `S` is independent for `t`. -/
def IndepF {n : ℕ} (t : Fin n → Fin n → Bool) (S : Finset (Fin n)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → t a b = false

instance {n : ℕ} (t : Fin n → Fin n → Bool) (S : Finset (Fin n)) : Decidable (IndepF t S) := by
  unfold IndepF; infer_instance

theorem mem_setOf {n s : ℕ} {j : Fin n} : j ∈ setOf n s ↔ s.testBit j.val = true := by
  simp [setOf]

theorem indepB_iff (n r s : ℕ) : indepB n r s = true ↔ IndepF (tyOf n r) (setOf n s) := by
  simp only [indepB, decide_eq_true_eq, IndepF, tyOf, mem_setOf]
  constructor
  · intro h a ha b hb hab
    exact h a.val a.isLt b.val b.isLt (fun e => hab (Fin.ext e)) ha hb
  · intro h a ha b hb hab hsa hsb
    exact h ⟨a, ha⟩ hsa ⟨b, hb⟩ hsb (fun e => hab (congrArg Fin.val e))

theorem sum_cover (n : ℕ) (F : (Fin n → Fin n → Bool) → Finset (Fin n) → ℕ) (j : Fin n) :
    ∑ σ : Fin n → Fin n → Bool, ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => j ∈ S), F σ S =
      ∑ r ∈ range (nT n), ∑ s ∈ range (nZ n),
        (if s.testBit j.val = true then F (tyOf n r) (setOf n s) else 0) := by
  rw [sum_types]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_filter, sum_sets]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [mem_setOf]

/-- The weights of the independent pairs, added up. -/
def totW (n : ℕ) (w : ℕ → ℕ → ℕ) : ℕ :=
  ∑ r ∈ range (nT n), ∑ s ∈ range (nZ n), (if indepB n r s then w r s else 0)

/-- The weights of the independent pairs whose subset contains client `j`. -/
def coverW (n : ℕ) (w : ℕ → ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ r ∈ range (nT n), ∑ s ∈ range (nZ n),
    (if indepB n r s = true ∧ s.testBit j = true then w r s else 0)

/-- The weights of the independent pairs whose subset misses client `j`. -/
def uncoverW (n : ℕ) (w : ℕ → ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ r ∈ range (nT n), ∑ s ∈ range (nZ n),
    (if indepB n r s = true ∧ s.testBit j = false then w r s else 0)

theorem cover_add_uncover (n : ℕ) (w : ℕ → ℕ → ℕ) (j : ℕ) :
    coverW n w j + uncoverW n w j = totW n w := by
  simp only [coverW, uncoverW, totW, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  by_cases h : indepB n r s = true <;> by_cases h2 : s.testBit j = true <;> simp [h, h2]

/-- The problem of `Theorem4ILP`, for the numbered instance. -/
def ILPx (I : Instance) (k : ℕ) : Prop :=
  ∃ x : (Fin I.clients → Fin I.clients → Bool) → Finset (Fin I.clients) → ℕ,
    (∀ t S, ¬ IndepF t S → x t S = 0) ∧
    (∀ t, ∑ S : Finset (Fin I.clients), x t S =
      (Finset.univ.filter fun i : Fin I.days => dtype I i = t).card) ∧
    (∀ j : Fin I.clients, k ≤ ∑ t : Fin I.clients → Fin I.clients → Bool,
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin I.clients) => j ∈ S), x t S)

theorem hasILP_iff (I : Instance) (k : ℕ) : (Bridge.model I).HasILPSolution k ↔ ILPx I k := Iff.rfl

theorem tot_eq (I : Instance) {w : ℕ → ℕ → ℕ}
    (h1 : ∀ r < nT I.clients, ∑ s ∈ range (nZ I.clients), (if indepB I.clients r s then w r s else 0) = cntN I r) :
    totW I.clients w = I.days := by
  rw [← sum_cntN I, totW]
  exact Finset.sum_congr rfl fun r hr => h1 r (Finset.mem_range.mp hr)

theorem feas'_to_ilpx (I : Instance) (k : ℕ) (hk : k ≤ I.days ∨ I.clients = 0) :
    Feas' I.clients I.days k (cntN I) → ILPx I k := by
  rintro ⟨w, sl, h1, h2⟩
  have hT := tot_eq I h1
  let x : (Fin I.clients → Fin I.clients → Bool) → Finset (Fin I.clients) → ℕ :=
    fun σ S => if IndepF σ S then w (numOf I.clients σ) (numSet I.clients S) else 0
  have hx : ∀ r < nT I.clients, ∀ s < nZ I.clients,
      x (tyOf I.clients r) (setOf I.clients s) = if indepB I.clients r s then w r s else 0 := by
    intro r hr s hs
    simp only [x, numOf_tyOf _ hr, numSet_setOf _ hs]
    by_cases h : indepB I.clients r s = true
    · rw [if_pos ((indepB_iff _ _ _).mp h), if_pos h]
    · rw [if_neg (fun h' => h ((indepB_iff _ _ _).mpr h')), if_neg h]
  refine ⟨x, fun t S hS => by simp [x, hS], fun σ => ?_, fun j => ?_⟩
  · have hr : numOf I.clients σ < nT I.clients := numOf_lt _ _
    have hσ : σ = tyOf I.clients (numOf I.clients σ) := (tyOf_numOf _ _).symm
    conv_lhs => rw [hσ]
    rw [sum_sets]
    rw [Finset.sum_congr rfl (fun s hs => hx _ hr s (Finset.mem_range.mp hs))]
    rw [h1 _ hr, cntN_eq I hr, ← hσ]
  · have hkj : k ≤ I.days := by
      rcases hk with hk | hk
      · exact hk
      · exact absurd j.isLt (by omega)
    rw [sum_cover]
    have : ∑ r ∈ range (nT I.clients), ∑ s ∈ range (nZ I.clients),
        (if s.testBit j.val = true then x (tyOf I.clients r) (setOf I.clients s) else 0) =
        coverW I.clients w j.val := by
      refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun s hs => ?_
      rw [hx r (Finset.mem_range.mp hr) s (Finset.mem_range.mp hs)]
      by_cases h : indepB I.clients r s = true <;> by_cases h2 : s.testBit j.val = true <;>
        simp [h, h2]
    rw [this]
    have hu := h2 j.val j.isLt
    have hcu := cover_add_uncover I.clients w j.val
    have hunc : uncoverW I.clients w j.val + sl j.val = I.days - k := hu
    omega

theorem ilpx_to_feas' (I : Instance) (k : ℕ) : ILPx I k → Feas' I.clients I.days k (cntN I) := by
  rintro ⟨x, hx0, hxs, hxc⟩
  let w : ℕ → ℕ → ℕ := fun r s => x (tyOf I.clients r) (setOf I.clients s)
  have hw : ∀ r s, (if indepB I.clients r s then w r s else 0) = w r s := by
    intro r s
    by_cases h : indepB I.clients r s = true
    · rw [if_pos h]
    · rw [if_neg h]
      exact (hx0 _ _ (fun h' => h ((indepB_iff _ _ _).mpr h'))).symm
  have h1 : ∀ r < nT I.clients,
      ∑ s ∈ range (nZ I.clients), (if indepB I.clients r s then w r s else 0) = cntN I r := by
    intro r hr
    rw [cntN_eq I hr, ← hxs, sum_sets]
    exact Finset.sum_congr rfl fun s _ => hw r s
  have hT : totW I.clients w = I.days := by
    rw [← sum_cntN I, totW]
    exact Finset.sum_congr rfl fun r hr => h1 r (Finset.mem_range.mp hr)
  have hcov : ∀ j : Fin I.clients, k ≤ coverW I.clients w j.val := by
    intro j
    have := hxc j
    rw [sum_cover] at this
    refine le_trans this (le_of_eq ?_)
    refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun s hs => ?_
    by_cases h2 : s.testBit j.val = true
    · have := hw r s
      by_cases h : indepB I.clients r s = true
      · simp [h, h2, w]
      · simp only [h, if_false] at this
        simp [h, h2, w, ← this]
    · simp [h2]
  refine ⟨w, fun j => (I.days - k) - uncoverW I.clients w j, h1, fun j hj => ?_⟩
  have hcu := cover_add_uncover I.clients w j
  have hc := hcov ⟨j, hj⟩
  simp only [] at hc
  show uncoverW I.clients w j + (I.days - k - uncoverW I.clients w j) = I.days - k
  omega

theorem feas'_iff (I : Instance) (k : ℕ) (hk : k ≤ I.days ∨ I.clients = 0) :
    Feas' I.clients I.days k (cntN I) ↔ ILPx I k :=
  ⟨feas'_to_ilpx I k hk, ilpx_to_feas' I k⟩

open Lax117284.IlpClients (decodeILP) in
/-- **The word of the integer program is feasible exactly when a `k`-fair schedule exists.** -/
theorem zList_feasible_iff (I : Instance) (k : ℕ) (hk : k ≤ I.days ∨ I.clients = 0) :
    (decodeILP (zList I.clients I.days k (cntN I))).Feasible ↔ I.HasKFairSchedule k := by
  rw [feasible_iff_nat, ilpNat_iff, feas'_iff I k hk, ← hasILP_iff,
    ← Model.Instance.hasKFairSchedule_iff_hasILPSolution, Bridge.hasKFairSchedule_iff]

end Lax117284Proofs.ClientsILP
