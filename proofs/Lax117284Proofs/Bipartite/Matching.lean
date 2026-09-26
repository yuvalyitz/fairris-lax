import Lax117284.BipartiteKuhn
import Mathlib.Data.Set.Card

/-!
A generic finite bipartite matching, decided by an augmenting-path search: process the left
vertices one at a time, and for each, search for an augmenting path among the right vertices not
yet visited on this search, re-augmenting whoever currently holds a visited right vertex.

This is Kuhn's algorithm, whose definitions (`nbrs`, `Respects`, `InjOnSupport`, `Matched`,
`size`, `step`, `tryAugment`, `runAll`, `kuhn`) are the concept package's `Lax117284.BipartiteKuhn`. This
file proves the correctness of one augmenting search in the clean, non-computational style, once,
for any finite bipartite relation.
-/

namespace Lax117284Proofs.Bipartite.Matching

open Lax117284.BipartiteKuhn

variable {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-! ### Correctness of one augmenting search -/

/-- **A successful augment is exactly right**: it respects the graph, stays injective, newly
matches `l`, every other left vertex's matched status is unchanged, and no right vertex already
in `visited` is touched (this is what lets a displaced vertex's own search, one level up, know
its old slot was left alone). -/
def GoodResult (adj : L → R → Prop) (μ : R → Option L) (visited : Finset R) (l : L)
    (μ' : R → Option L) : Prop :=
  Respects adj μ' ∧ InjOnSupport μ' ∧ Matched μ' l ∧
    (∀ l₀, l₀ ≠ l → (Matched μ l₀ ↔ Matched μ' l₀)) ∧
    ∀ r ∈ visited, μ' r = μ r

omit [Fintype L] [DecidableEq L] [Fintype R] in
/-- **Clearing a right vertex's match keeps every invariant, and only unmatches its old
occupant.** -/
lemma respects_update_none (adj : L → R → Prop) {μ : R → Option L} (hRes : Respects adj μ)
    (r : R) : Respects adj (Function.update μ r none) := by
  intro r' l' h
  by_cases hr : r' = r
  · rw [hr, Function.update_self] at h; cases h
  · rw [Function.update_of_ne hr] at h; exact hRes r' l' h

omit [Fintype L] [DecidableEq L] [Fintype R] in
lemma injOnSupport_update_none {μ : R → Option L} (hInj : InjOnSupport μ) (r : R) :
    InjOnSupport (Function.update μ r none) := by
  intro r₁ r₂ l' h1 h2
  by_cases hr1 : r₁ = r
  · rw [hr1, Function.update_self] at h1; cases h1
  · by_cases hr2 : r₂ = r
    · rw [hr2, Function.update_self] at h2; cases h2
    · rw [Function.update_of_ne hr1] at h1; rw [Function.update_of_ne hr2] at h2
      exact hInj r₁ r₂ l' h1 h2

omit [Fintype L] [DecidableEq L] [Fintype R] in
/-- **Adding a fresh match at a neighbour of `l` is a good result**, given `l` was unmatched, the
neighbour was free, and (needed only for the final clause) the neighbour is not in `visited`. -/
lemma goodResult_fresh (adj : L → R → Prop) {μ : R → Option L} {visited : Finset R} {l : L}
    {r : R} (hRes : Respects adj μ) (hInj : InjOnSupport μ) (hUnm : ¬ Matched μ l)
    (hFree : μ r = none) (hAdj : adj l r) (hvis : r ∉ visited) :
    GoodResult adj μ visited l (Function.update μ r (some l)) := by
  refine ⟨?_, ?_, ⟨r, Function.update_self r (some l) μ⟩, ?_, ?_⟩
  · intro r' l'' h
    by_cases hr : r' = r
    · subst hr; rw [Function.update_self] at h; cases h; exact hAdj
    · rw [Function.update_of_ne hr] at h; exact hRes r' l'' h
  · intro r₁ r₂ l'' h1 h2
    by_cases hr1 : r₁ = r <;> by_cases hr2 : r₂ = r
    · rw [hr1, hr2]
    · exfalso; subst hr1; rw [Function.update_self] at h1; cases h1
      rw [Function.update_of_ne hr2] at h2; exact hUnm ⟨r₂, h2⟩
    · exfalso; subst hr2; rw [Function.update_self] at h2; cases h2
      rw [Function.update_of_ne hr1] at h1; exact hUnm ⟨r₁, h1⟩
    · rw [Function.update_of_ne hr1] at h1; rw [Function.update_of_ne hr2] at h2
      exact hInj r₁ r₂ l'' h1 h2
  · intro l₀ hl₀
    constructor
    · rintro ⟨r₀, h0⟩
      have hr0 : r₀ ≠ r := by rintro rfl; rw [hFree] at h0; cases h0
      exact ⟨r₀, by rw [Function.update_of_ne hr0]; exact h0⟩
    · rintro ⟨r₀, h0⟩
      have hr0 : r₀ ≠ r := by
        rintro rfl
        rw [Function.update_self] at h0
        exact hl₀ (Option.some.inj h0).symm
      rw [Function.update_of_ne hr0] at h0
      exact ⟨r₀, h0⟩
  · intro r' hr'
    have hne : r' ≠ r := by rintro rfl; exact hvis hr'
    rw [Function.update_of_ne hne]

omit [Fintype L] [DecidableEq L] [Fintype R] in
/-- **Displacing the occupant of a neighbour of `l` and re-augmenting it elsewhere is a good
result**, given a good result for the displaced vertex's own search (from the cleared matching,
with the neighbour added to its `visited`). -/
lemma goodResult_displaced (adj : L → R → Prop) {μ : R → Option L} {visited : Finset R}
    {l l' : L} {r : R} (hUnm : ¬ Matched μ l) (hAdj : adj l r) (hOcc : μ r = some l')
    (hvis : r ∉ visited) {μ'' : R → Option L}
    (hGood : GoodResult adj (Function.update μ r none) (insert r visited) l' μ'') :
    GoodResult adj μ visited l (Function.update μ'' r (some l)) := by
  obtain ⟨hRes'', hInj'', hMatch'', hIff'', hPres''⟩ := hGood
  have hll' : l' ≠ l := by rintro rfl; exact hUnm ⟨r, hOcc⟩
  have hμcr : Function.update μ r none r = none := Function.update_self r none μ
  have hμ''r : μ'' r = none := by
    rw [hPres'' r (Finset.mem_insert_self r visited), hμcr]
  have hμcOfNe : ∀ r' : R, r' ≠ r → Function.update μ r none r' = μ r' := fun r' hr' =>
    Function.update_of_ne hr' none μ
  have hMatchedUpdNoneL : ¬ Matched (Function.update μ r none) l := by
    rintro ⟨r₀, h0⟩
    by_cases hr0 : r₀ = r
    · rw [hr0, hμcr] at h0; cases h0
    · rw [hμcOfNe r₀ hr0] at h0; exact hUnm ⟨r₀, h0⟩
  have hNotMatched'' : ¬ Matched μ'' l := by
    rw [← hIff'' l hll'.symm]; exact hMatchedUpdNoneL
  refine ⟨?_, ?_, ⟨r, Function.update_self r (some l) μ''⟩, ?_, ?_⟩
  · intro r' l₂ h
    by_cases hr : r' = r
    · subst hr; rw [Function.update_self] at h; cases h; exact hAdj
    · rw [Function.update_of_ne hr] at h; exact hRes'' r' l₂ h
  · intro r₁ r₂ l₂ h1 h2
    by_cases hr1 : r₁ = r <;> by_cases hr2 : r₂ = r
    · rw [hr1, hr2]
    · exfalso; subst hr1; rw [Function.update_self] at h1; cases h1
      rw [Function.update_of_ne hr2] at h2; exact hNotMatched'' ⟨r₂, h2⟩
    · exfalso; subst hr2; rw [Function.update_self] at h2; cases h2
      rw [Function.update_of_ne hr1] at h1; exact hNotMatched'' ⟨r₁, h1⟩
    · rw [Function.update_of_ne hr1] at h1; rw [Function.update_of_ne hr2] at h2
      exact hInj'' r₁ r₂ l₂ h1 h2
  · intro l₀ hl₀
    by_cases hl₀l' : l₀ = l'
    · subst hl₀l'
      constructor
      · intro _
        obtain ⟨r₀, h0⟩ := hMatch''
        have hr0 : r₀ ≠ r := by rintro rfl; rw [hμ''r] at h0; cases h0
        exact ⟨r₀, by rw [Function.update_of_ne hr0]; exact h0⟩
      · intro _; exact ⟨r, hOcc⟩
    · constructor
      · intro hM
        have hMc : Matched (Function.update μ r none) l₀ := by
          obtain ⟨r₀, h0⟩ := hM
          have hr0 : r₀ ≠ r := by rintro rfl; rw [hOcc] at h0; exact hl₀l' (Option.some.inj h0).symm
          exact ⟨r₀, by rw [hμcOfNe r₀ hr0]; exact h0⟩
        obtain ⟨r₀, h0⟩ := (hIff'' l₀ hl₀l').1 hMc
        have hr0 : r₀ ≠ r := by rintro rfl; rw [hμ''r] at h0; cases h0
        exact ⟨r₀, by rw [Function.update_of_ne hr0]; exact h0⟩
      · intro hM
        obtain ⟨r₀, h0⟩ := hM
        have hr0 : r₀ ≠ r := by rintro rfl; rw [Function.update_self] at h0; exact hl₀ (Option.some.inj h0).symm
        rw [Function.update_of_ne hr0] at h0
        have hMc : Matched (Function.update μ r none) l₀ := (hIff'' l₀ hl₀l').2 ⟨r₀, h0⟩
        obtain ⟨r₁, h1⟩ := hMc
        have hr1 : r₁ ≠ r := by rintro rfl; rw [hμcr] at h1; cases h1
        exact ⟨r₁, by rw [hμcOfNe r₁ hr1] at h1; exact h1⟩
  · intro r' hr'
    have hne : r' ≠ r := by rintro rfl; exact hvis hr'
    rw [Function.update_of_ne hne, hPres'' r' (Finset.mem_insert_of_mem hr'), hμcOfNe r' hne]

/-! ### Full matchings -/

/-- **The bipartite graph has a matching saturating every left vertex.** -/
def HasFullMatching (adj : L → R → Prop) : Prop :=
  ∃ f : L → R, Function.Injective f ∧ ∀ l, adj l (f l)

/-! ### Completeness: if a full matching exists, the search succeeds

The remaining, hard direction. A matching `μ` missing `l` fails to find an augmenting path from
`l` only if every right vertex reachable from `l` by alternating exploration is already matched;
but then the left vertices so reached outnumber the right vertices so reached by exactly one
(`l` itself), which is impossible once a full matching of the whole left side exists (Hall's
condition, applied to this one reached set). -/

/-- **The left vertices reachable from `l₀` by alternating exploration**: `l₀` itself, and
whoever currently holds a right vertex adjacent to an already-reached left vertex. -/
def ReachL (adj : L → R → Prop) (μ : R → Option L) (l₀ : L) : L → Prop :=
  Relation.ReflTransGen (fun l l' => ∃ r, adj l r ∧ μ r = some l') l₀

omit [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
theorem ReachL.start {adj : L → R → Prop} {μ : R → Option L} {l₀ : L} : ReachL adj μ l₀ l₀ :=
  Relation.ReflTransGen.refl

omit [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
theorem ReachL.step {adj : L → R → Prop} {μ : R → Option L} {l₀ l l' : L} {r : R}
    (h : ReachL adj μ l₀ l) (hadj : adj l r) (hμ : μ r = some l') : ReachL adj μ l₀ l' :=
  Relation.ReflTransGen.tail h ⟨r, hadj, hμ⟩

/-- **The right vertices reachable from `l₀`**: adjacent to some reached left vertex. -/
def ReachR (adj : L → R → Prop) (μ : R → Option L) (l₀ : L) (r : R) : Prop :=
  ∃ l, ReachL adj μ l₀ l ∧ adj l r

omit [DecidableEq L] [DecidableEq R] in
/-- **If every right vertex reachable from an unmatched `l₀` is already matched, no full
matching of the graph exists.** -/
theorem not_hasFullMatching_of_saturated (adj : L → R → Prop) {μ : R → Option L} {l₀ : L}
    (hInj : InjOnSupport μ) (hUnm : ¬ Matched μ l₀)
    (hSat : ∀ r, ReachR adj μ l₀ r → ∃ l, μ r = some l) : ¬ HasFullMatching adj := by
  classical
  rintro ⟨f, hfInj, hfAdj⟩
  set S : Set L := {l | ReachL adj μ l₀ l} with hS
  set V : Set R := {r | ReachR adj μ l₀ r} with hV
  have hl₀S : l₀ ∈ S := ReachL.start
  -- The occupant of a saturated reached right vertex is well defined and lands back in `S`.
  choose g hg using fun r (hr : r ∈ V) => hSat r hr
  have hgS : ∀ r (hr : r ∈ V), g r hr ∈ S \ {l₀} := by
    intro r hr
    obtain ⟨l, hl, hlr⟩ := hr
    have hr' : r ∈ V := ⟨l, hl, hlr⟩
    refine ⟨ReachL.step hl hlr (hg r hr'), ?_⟩
    simp only [Set.mem_singleton_iff]
    intro he
    exact hUnm ⟨r, he ▸ hg r hr'⟩
  have hgInj : ∀ r₁ (hr₁ : r₁ ∈ V) r₂ (hr₂ : r₂ ∈ V), g r₁ hr₁ = g r₂ hr₂ → r₁ = r₂ := by
    intro r₁ hr₁ r₂ hr₂ he
    exact hInj r₁ r₂ (g r₁ hr₁) (hg r₁ hr₁) (he ▸ hg r₂ hr₂)
  have hgSurj : ∀ l' ∈ S \ {l₀}, ∃ r, ∃ hr : r ∈ V, g r hr = l' := by
    rintro l' ⟨hl', hne⟩
    simp only [Set.mem_singleton_iff] at hne
    have hl'R : Relation.ReflTransGen (fun l l' => ∃ r, adj l r ∧ μ r = some l') l₀ l' := hl'
    cases hl'R with
    | refl => exact absurd rfl hne
    | @tail l _ hl hstep =>
      obtain ⟨r, hlr, hr⟩ := hstep
      have hr' : r ∈ V := ⟨l, hl, hlr⟩
      exact ⟨r, hr', Option.some.inj ((hg r hr').symm.trans hr)⟩
  have hbij : Set.BijOn (fun r : R => if hr : r ∈ V then g r hr else l₀) V (S \ {l₀}) := by
    refine ⟨fun r hr => by simp only [dif_pos hr]; exact hgS r hr,
      fun r₁ hr₁ r₂ hr₂ he => ?_, fun l' hl' => ?_⟩
    · simp only [dif_pos hr₁, dif_pos hr₂] at he
      exact hgInj r₁ hr₁ r₂ hr₂ he
    · obtain ⟨r, hr, hrl'⟩ := hgSurj l' hl'
      exact ⟨r, hr, by simp only [dif_pos hr]; exact hrl'⟩
  have hVfin : V.Finite := Set.toFinite V
  have hcard : V.ncard + 1 = S.ncard := by
    rw [hbij.ncard_eq, Set.ncard_sdiff_singleton_add_one hl₀S]
  have hle : S.ncard ≤ V.ncard :=
    Set.ncard_le_ncard_of_injOn f (fun l _ => ⟨l, ‹ReachL adj μ l₀ l›, hfAdj l⟩)
      (fun l₁ _ l₂ _ he => hfInj he) hVfin
  omega

end Lax117284Proofs.Bipartite.Matching
