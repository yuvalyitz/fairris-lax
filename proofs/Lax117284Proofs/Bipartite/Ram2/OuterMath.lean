import Lax117284Proofs.Bipartite.Maximum
import Lax117284Proofs.Bipartite.Ram2.SearchAbs

/-!
The mathematics of the outer loop over left vertices: the machine keeps a matching
`μ : ℕ → Option ℕ`; here it is read on the `Fin` types (`muF`), where `Maximum.lean`'s
maximality argument lives.

`MatchInv adjB n m l μ` is what the loop keeps after processing the left vertices `0 .. l - 1`:
`μ` is a matching whose left endpoints are below `l` and whose support is below `m`, and every
processed left vertex is `Matched` or `Failed`. A successful search preserves it by
`failed_stable`, a failed one by turning the machine's `FailCert` into `Failed`. At the end
(`l = n`) the matching has the size of Kuhn's result (`MatchInv.size_eq_kuhn`), and the count
of matched right vertices is that size (`size_muF_eq`).
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching Lax117284Proofs.Bipartite.Maximum
open scoped Classical

/-- A relation on `ℕ`, restricted to the `Fin` types. -/
def adjF (adjB : ℕ → ℕ → Prop) (n m : ℕ) : Fin n → Fin m → Prop := fun i j => adjB i.val j.val

/-- The support of `μ` lies below `m`. -/
def SuppLt (μ : ℕ → Option ℕ) (m : ℕ) : Prop := ∀ j l, μ j = some l → j < m

section Transfer

variable {adjB : ℕ → ℕ → Prop} {n m : ℕ} {μ : ℕ → Option ℕ}

/-- The matching `μ`, restricted to the `Fin` types. -/
noncomputable def muF (n m : ℕ) (μ : ℕ → Option ℕ) : Fin m → Option (Fin n) := fun j =>
  match μ j.val with
  | none => none
  | some l => if h : l < n then some ⟨l, h⟩ else none

theorem muF_eq_some (hbd : ∀ j l, μ j = some l → l < n) {j : Fin m} {l : Fin n} :
    muF n m μ j = some l ↔ μ j.val = some l.val := by
  unfold muF
  rcases hμ : μ j.val with _ | l'
  · simp
  · have := hbd _ _ hμ
    simp only [dif_pos this, Option.some.injEq]
    constructor
    · intro h; rw [← h]
    · intro h; exact Fin.ext h

theorem matched_muF (hbd : ∀ j l, μ j = some l → l < n) (hsupp : SuppLt μ m) {l : Fin n} :
    Matched (muF n m μ) l ↔ Matched μ l.val := by
  constructor
  · rintro ⟨r, hr⟩; exact ⟨r.val, (muF_eq_some hbd).1 hr⟩
  · rintro ⟨r, hr⟩; exact ⟨⟨r, hsupp r _ hr⟩, (muF_eq_some hbd).2 hr⟩

theorem isMatching_muF (hres : Respects adjB μ) (hinj : InjOnSupport μ)
    (hbd : ∀ j l, μ j = some l → l < n) : IsMatching (adjF adjB n m) (muF n m μ) := by
  refine ⟨fun r l h => hres r.val l.val ((muF_eq_some hbd).1 h), fun r r' l h h' => ?_⟩
  exact Fin.ext (hinj r.val r'.val l.val ((muF_eq_some hbd).1 h) ((muF_eq_some hbd).1 h'))

/-- A good result on `ℕ` is a good result on the `Fin` types. -/
theorem goodResult_muF {μ' : ℕ → Option ℕ} (hbd : ∀ j l, μ j = some l → l < n)
    (hbd' : ∀ j l, μ' j = some l → l < n) (hsupp : SuppLt μ m) (hsupp' : SuppLt μ' m) {l₀ : ℕ}
    (hl₀ : l₀ < n) (hG : GoodResult adjB μ ∅ l₀ μ') :
    GoodResult (adjF adjB n m) (muF n m μ) ∅ ⟨l₀, hl₀⟩ (muF n m μ') := by
  obtain ⟨hres', hinj', hM', hIff, -⟩ := hG
  refine ⟨(isMatching_muF hres' hinj' hbd').1, (isMatching_muF hres' hinj' hbd').2, ?_, ?_, ?_⟩
  · exact (matched_muF hbd' hsupp').2 hM'
  · intro l hl
    rw [matched_muF hbd hsupp, matched_muF hbd' hsupp']
    exact hIff l.val (fun h => hl (Fin.ext h))
  · intro r hr; simp at hr

/-- **A failure certificate is a `Failed` on the `Fin` types**: every reached left vertex is
closed, so every reached right vertex is visited, hence occupied. -/
theorem failed_of_failCert (hbd : ∀ j l, μ j = some l → l < n) (hsupp : SuppLt μ m) {l₀ : ℕ}
    (hl₀ : l₀ < n) (hunm : ¬ Matched μ l₀) {visB : ℕ → Prop}
    (hF : FailCert adjB μ m l₀ visB) :
    Failed (adjF adjB n m) (muF n m μ) ⟨l₀, hl₀⟩ := by
  obtain ⟨hC, hO⟩ := hF
  refine ⟨fun h => hunm ((matched_muF hbd hsupp).1 h), ?_⟩
  have hReach : ∀ l', ReachL (adjF adjB n m) (muF n m μ) ⟨l₀, hl₀⟩ l' →
      ∀ j < m, adjB l'.val j → visB j := by
    intro l' hl'
    unfold ReachL at hl'
    induction hl' with
    | refl => exact hC
    | @tail l l'' hprev hstep ih =>
        obtain ⟨r, hadjr, hocc⟩ := hstep
        have hv : visB r.val := ih r.val r.2 hadjr
        obtain ⟨l3, hl3, hcl3⟩ := hO r.val r.2 hv
        rw [muF_eq_some hbd] at hocc
        rw [hocc] at hl3
        cases hl3
        exact hcl3
  rintro r ⟨l, hl, hlr⟩
  have hv : visB r.val := hReach l hl r.val r.2 hlr
  obtain ⟨l3, hl3, -⟩ := hO r.val r.2 hv
  exact ⟨⟨l3, hbd _ _ hl3⟩, (muF_eq_some hbd).2 hl3⟩

/-- The size of the `Fin` matching is the number of matched right indices below `m`. -/
theorem size_muF_eq (hbd : ∀ j l, μ j = some l → l < n) :
    size (muF n m μ) = ((Finset.range m).filter (fun j => (μ j).isSome)).card := by
  unfold size
  refine Finset.card_bij (fun (j : Fin m) _ => j.val) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨j.2, ?_⟩
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hj
    exact Option.isSome_iff_exists.2 ⟨l.val, (muF_eq_some hbd).1 hl⟩
  · intro j _ j' _ h; exact Fin.ext h
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hj.2
    refine ⟨⟨j, hj.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Option.isSome_iff_exists.2 ⟨⟨l, hbd _ _ hl⟩, (muF_eq_some hbd).2 hl⟩

end Transfer

/-! ### The invariant of the outer loop -/

/-- **What the outer loop maintains** after processing the left vertices below `l`. -/
structure MatchInv (adjB : ℕ → ℕ → Prop) (n m l : ℕ) (μ : ℕ → Option ℕ) : Prop where
  res : Respects adjB μ
  inj : InjOnSupport μ
  bd : ∀ j l', μ j = some l' → l' < l
  supp : SuppLt μ m
  done : ∀ l' : Fin n, l'.val < l →
    Matched (muF n m μ) l' ∨ Failed (adjF adjB n m) (muF n m μ) l'

section Inv

variable {adjB : ℕ → ℕ → Prop} {n m l : ℕ} {μ : ℕ → Option ℕ}

theorem MatchInv.zero (adjB : ℕ → ℕ → Prop) (n m : ℕ) : MatchInv adjB n m 0 (fun _ => none) :=
  ⟨fun _ _ h => by simp at h, fun _ _ _ h => by simp at h, fun _ _ h => by simp at h,
    fun _ _ h => by simp at h, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem MatchInv.unm (h : MatchInv adjB n m l μ) : ¬ Matched μ l := by
  rintro ⟨j, hj⟩
  exact absurd (h.bd j l hj) (lt_irrefl l)

theorem MatchInv.hμn (h : MatchInv adjB n m l μ) (hl : l ≤ n) :
    ∀ j l', μ j = some l' → l' < n :=
  fun j l' hj => lt_of_lt_of_le (h.bd j l' hj) hl

/-- **A successful search extends the invariant.** -/
theorem MatchInv.succ_good {μ' : ℕ → Option ℕ} (h : MatchInv adjB n m l μ) (hl : l < n)
    (hG : GoodResult adjB μ ∅ l μ') (hsupp' : SuppLt μ' m) : MatchInv adjB n m (l + 1) μ' := by
  obtain ⟨hRes, hInj, hM, hIff, -⟩ := hG
  have hbd' : ∀ j l', μ' j = some l' → l' < l + 1 := by
    intro j l' hj
    by_cases hll : l' = l
    · omega
    · have hm : Matched μ' l' := ⟨j, hj⟩
      obtain ⟨j', hj'⟩ := (hIff l' hll).2 hm
      have := h.bd j' l' hj'
      omega
  have hbdn := h.hμn (by omega)
  have hbdn' : ∀ j l', μ' j = some l' → l' < n := fun j l' hj =>
    lt_of_lt_of_le (hbd' j l' hj) hl
  have hGF := goodResult_muF hbdn hbdn' h.supp hsupp' hl ⟨hRes, hInj, hM, hIff, fun r hr => by
    simp at hr⟩
  refine ⟨hRes, hInj, hbd', hsupp', fun l' hl' => ?_⟩
  by_cases hll : l'.val = l
  · left
    have : l' = ⟨l, hl⟩ := Fin.ext hll
    rw [this]; exact hGF.2.2.1
  · have hne : l' ≠ ⟨l, hl⟩ := fun he => hll (congrArg Fin.val he)
    rcases h.done l' (by omega) with hM' | hF'
    · left; exact (hGF.2.2.2.1 l' hne).1 hM'
    · right
      exact failed_stable (isMatching_muF h.res h.inj hbdn) hF' hne.symm
        (fun hm => h.unm ((matched_muF hbdn h.supp).1 hm)) hGF

/-- **A failed search extends the invariant**, the matching unchanged. -/
theorem MatchInv.succ_fail (h : MatchInv adjB n m l μ) (hl : l < n) {visB : ℕ → Prop}
    (hF : FailCert adjB μ m l visB) : MatchInv adjB n m (l + 1) μ := by
  have hbdn := h.hμn (by omega)
  refine ⟨h.res, h.inj, fun j l' hj => by have := h.bd j l' hj; omega, h.supp,
    fun l' hl' => ?_⟩
  by_cases hll : l'.val = l
  · right
    have : l' = ⟨l, hl⟩ := Fin.ext hll
    rw [this]; exact failed_of_failCert hbdn h.supp hl h.unm hF
  · exact h.done l' (by omega)

/-- **At the end the matching is maximum**: it has the size of Kuhn's result. -/
theorem MatchInv.size_eq_kuhn (h : MatchInv adjB n m n μ) :
    size (muF n m μ) = size (kuhn (adjF adjB n m)) := by
  have hbdn := h.hμn le_rfl
  have hM := isMatching_muF (m := m) h.res h.inj hbdn
  have hall : ∀ l' : Fin n, Matched (muF n m μ) l' ∨ Failed (adjF adjB n m) (muF n m μ) l' :=
    fun l' => h.done l' l'.2
  have hK := kuhn_maximum (adjF adjB n m)
  exact le_antisymm (hK.2 _ hM) (size_le_of_saturating hM hall hK.1)

end Inv

end Lax117284Proofs.Bipartite.Ram2
