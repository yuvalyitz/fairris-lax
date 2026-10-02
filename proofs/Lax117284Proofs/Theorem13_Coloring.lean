import Mathlib.Data.Fintype.EquivFin
import Lax117284Proofs.IntervalColoring

/-!
# Theorem 13: Day-Independent Due Dates *and* Processing Times

> **Theorem 13.** The `1 | rep, d_{i,j} = d_j, p_{i,j} = p_j | min_j ∑_i Z_{i,j}` problem is
> solvable in `O(n log n)` time.
>
> *Proof.* Let `G = (V, E)` be the conflict graph of a given instance. […] We show that
> there exists a feasible `k`-fair schedule for our given instance if and only if
> `k · χ ≤ m`.

When both the processing times and the due dates are day-independent, *every day is the
same day*: each client's job occupies the same interval on all `m` days, so all `m` daily
conflict graphs coincide (`dayGraph_eq_of_dayIndep`). The problem collapses to a counting
question about that one interval graph, and `hasKFairSchedule_iff_mul_cliqueNum_le` is the
answer:

* if `k · χ ≤ m`, take a proper `χ`-colouring, run each of the `χ` colour classes — each an
  independent set, hence a feasible day — on `k` days of its own, and every client is
  served exactly `k` times;
* if `k · χ > m`, the graph has a clique `K` with `|K| = χ` (this is where perfectness
  enters, and `IntervalColoring.lean` proves it rather than citing it), no day can serve
  two members of `K`, so the `|K|` clients of `K` need `k · |K| = k · χ > m` days between
  them, which there are not.

Stated with `cliqueNum` (`ω`) rather than `chromaticNumber` (`χ`), since `ω` is a plain `ℕ`
and the two are equal for these graphs; `hasKFairSchedule_iff_mul_chromaticNumber_le`
restates it with `χ` for direct comparison with the paper.

The `O(n log n)` running time — Gavril's algorithm [26] for colouring an interval graph
given its interval representation — is a resource claim, and lives with the other resource
claims in `FairRIS.lean`.
-/


namespace Lax117284Proofs.Model

namespace Instance

variable {I : Instance}

/-! ## 1. One instance, one graph -/

/-- With day-independent due dates and processing times, every day's conflict graph is the
same graph. -/
theorem dayGraph_eq_of_dayIndep (hd : I.DayIndepD) (hp : I.DayIndepP) (i i' : I.Day) :
    I.dayGraph i = I.dayGraph i' := by
  have hstart : ∀ j, I.start i j = I.start i' j := fun j => by
    simp only [start, hd i i' j, hp i i' j]
  ext j j'
  simp only [dayGraph_adj, Conflict, hstart, hd i i']

/-! ## 2. The criterion -/

/-- **Theorem 13's criterion.** With day-independent due dates and processing times, a
feasible `k`-fair schedule exists exactly when `k · ω ≤ m`, where `ω` is the largest clique
of the (single) conflict graph — equivalently, by `chromaticNumber_dayGraph`, when
`k · χ ≤ m`. -/
theorem hasKFairSchedule_iff_mul_cliqueNum_le (hd : I.DayIndepD) (hp : I.DayIndepP)
    (i₀ : I.Day) (k : ℕ) :
    I.HasKFairSchedule k ↔ k * (I.dayGraph i₀).cliqueNum ≤ I.numDays := by
  classical
  constructor
  · rintro ⟨σ, hfeas, hfair⟩
    obtain ⟨K, hK, hKcard⟩ := (I.dayGraph i₀).exists_isNClique_cliqueNum
    have hKall : ∀ i, (I.dayGraph i).IsClique (K : Set I.Client) := fun i => by
      rw [dayGraph_eq_of_dayIndep hd hp i i₀]; exact hK
    have hsum := sum_served_le_numDays hfeas hKall
    have hlow : k * K.card ≤ ∑ j ∈ K, served σ j := by
      calc k * K.card = ∑ _j ∈ K, k := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ j ∈ K, served σ j := Finset.sum_le_sum fun j _ => hfair j
    rw [hKcard] at hlow
    omega
  · intro hle
    -- a proper colouring with `ω` colours
    obtain ⟨C⟩ := dayGraph_colorable_cliqueNum I i₀
    -- `k` days of its own for each colour class
    have hcard : Fintype.card (Fin (I.dayGraph i₀).cliqueNum × Fin k) ≤
        Fintype.card I.Day := by
      simpa [Fintype.card_prod, mul_comm, numDays] using hle
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
    refine ⟨fun i => Finset.univ.filter fun j => ∃ r : Fin k, f (C j, r) = i, ?_, ?_⟩
    · intro i j hj j' hj' hne hc
      simp only [Finset.mem_filter] at hj hj'
      obtain ⟨r, hr⟩ := hj.2
      obtain ⟨r', hr'⟩ := hj'.2
      have : (C j, r) = (C j', r') := f.injective (hr.trans hr'.symm)
      have hCeq : C j = C j' := congrArg Prod.fst this
      have : (I.dayGraph i₀).Adj j j' := by
        rw [dayGraph_eq_of_dayIndep hd hp i₀ i]; exact ⟨hne, hc⟩
      exact C.valid this hCeq
    · intro j
      have himg : (Finset.univ.filter fun i => j ∈
          Finset.univ.filter fun j' => ∃ r : Fin k, f (C j', r) = i)
          = Finset.univ.image fun r : Fin k => f (C j, r) := by
        ext i
        simp
      rw [served, himg, Finset.card_image_of_injective _ (fun a b hab =>
        congrArg Prod.snd (f.injective hab))]
      simp

/-- Theorem 13's criterion in the paper's own words: `k · χ ≤ m`. -/
theorem hasKFairSchedule_iff_mul_chromaticNumber_le (hd : I.DayIndepD) (hp : I.DayIndepP)
    (i₀ : I.Day) (k : ℕ) :
    I.HasKFairSchedule k ↔ (k : ℕ∞) * (I.dayGraph i₀).chromaticNumber ≤ I.numDays := by
  rw [hasKFairSchedule_iff_mul_cliqueNum_le hd hp i₀ k, chromaticNumber_dayGraph]
  exact_mod_cast Iff.rfl

end Instance

end Lax117284Proofs.Model
