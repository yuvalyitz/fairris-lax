import Lax117284Proofs.Defs

/-!
# The three easy slices of the dichotomy

Theorem 1 says `1 | rep | min_j ∑_i Z_{i,j}` is polynomial-time solvable exactly when
`k ∈ {0, m-1, m}`. Two of those three cases, and the range `k > m` that the paper dismisses
in half a sentence, are settled here; `k = m - 1` is the substantial one and is
`Theorem9_TwoSat.lean`.

> *"it is clear that the cases where `k = 0` and `k ≥ m` are straightforward. When `k = 0`
> every feasible schedule `j` and `i` is `k`-fair, making it trivially a YES instance.
> When `k = m`, only conflict-free instances are classified as YES instances, as every job
> of every client must be scheduled (instances where `k > m` are as well trivially NO
> instances)."* — Section 3

Each is an `iff` against a condition that is decidable by inspection of the instance, so
each is a polynomial-time decision procedure in the only sense this repository can state
one without a machine model; `FairRIS.lean` §2 packages them as such.
-/


namespace Lax117284Proofs.Model

namespace Instance

variable {I : Instance}

/-! ## 1. `k = 0` -/

/-- **`k = 0` is trivially a yes-instance.** The empty schedule witnesses it. -/
@[simp] theorem hasKFairSchedule_zero : I.HasKFairSchedule 0 :=
  ⟨fun _ => ∅, feasible_empty, fun _ => Nat.zero_le _⟩

/-! ## 2. `k = m` -/

variable (I) in
/-- An instance is **conflict-free** when no two distinct clients ever conflict. The
paper's characterization of the yes-instances at `k = m`. -/
def ConflictFree : Prop := ∀ i j j', j ≠ j' → ¬ I.Conflict i j j'

/-- A client served on `numDays` days is served on *every* day. -/
lemma mem_of_served_eq_numDays {σ : I.Schedule} {j : I.Client}
    (h : I.numDays ≤ served σ j) (i : I.Day) : j ∈ σ i := by
  by_contra hmem
  have hsub : (Finset.univ.filter fun i => j ∈ σ i) ⊆ Finset.univ.erase i := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    exact Finset.mem_erase.2 ⟨fun hxi => hmem (hxi ▸ hx.2), Finset.mem_univ x⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] at this
  have hpos : 0 < Fintype.card I.Day := Fintype.card_pos_iff.2 ⟨i⟩
  simp only [served] at h
  simp only [numDays] at h
  omega

/-- **`k = m` is a yes-instance exactly for the conflict-free instances.** Every job of
every client must run, so the whole of every day must be conflict-free — and then running
everything every day works. -/
theorem hasKFairSchedule_numDays_iff :
    I.HasKFairSchedule I.numDays ↔ I.ConflictFree := by
  constructor
  · rintro ⟨σ, hfeas, hfair⟩ i j j' hne
    exact hfeas i j (mem_of_served_eq_numDays (hfair j) i) j'
      (mem_of_served_eq_numDays (hfair j') i) hne
  · intro hcf
    refine ⟨fun _ => Finset.univ, fun i j _ j' _ hne => hcf i j j' hne, fun j => ?_⟩
    simp only [served, Finset.mem_univ, Finset.filter_true_of_mem, implies_true,
      Finset.card_univ, numDays, le_refl]

/-! ## 3. `k > m` -/

/-- **`k > m` is trivially a no-instance**, as soon as there is a client to serve: a client
cannot be served on more days than there are. -/
theorem not_hasKFairSchedule_of_gt {k : ℕ} (hk : I.numDays < k) (j : I.Client) :
    ¬ I.HasKFairSchedule k := by
  rintro ⟨σ, -, hfair⟩
  exact absurd (le_trans (hfair j) (served_le_numDays σ j)) (Nat.not_le.2 hk)

end Instance

end Lax117284Proofs.Model
