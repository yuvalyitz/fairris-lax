import Lax117284Proofs.Bipartite.Matching
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
Kuhn's algorithm, run over **every** left vertex and continuing past the vertices it cannot
augment, outputs a **maximum** matching.

Two things are proved about a single search `Matching.tryAugment` here (the package's machine
layer proves the same two facts for its explicit-stack search, not for this recursive one):

* **soundness** (`tryAugment_some`): a successful search is a `GoodResult`;
* **completeness** (`tryAugment_none`): a failed search, from an unmatched `l₀` with enough fuel,
  leaves every right vertex reachable from `l₀` by alternating exploration matched — `l₀` is
  `Failed`.

Then the maximality argument, which avoids Berge's lemma: being `Failed` is **stable** under
later augmentations from other unmatched vertices (`failed_stable`), so at the end every left
vertex is matched or `Failed`; and a matching with that property is maximum
(`size_le_of_saturating`), by counting: with `F` the unmatched left vertices, `S` everything
reachable from `F` and `V` the neighbours of `S`, `μ` puts `V` in bijection with `S \ F`, while any
matching matches at most `|V|` vertices of `S`.
-/

namespace Lax117284Proofs.Bipartite.Maximum

open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching

variable {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-! ### The algorithm is the concept's `Lax117284.BipartiteKuhn.kuhn` -/

/-- `μ` is a matching of the graph `adj`: it respects the graph and is injective. -/
def IsMatching (adj : L → R → Prop) (μ : R → Option L) : Prop :=
  Respects adj μ ∧ InjOnSupport μ

/-- **`l₀` failed**: it is unmatched, and every right vertex reachable from it by alternating
exploration is matched. This is exactly what a failed search certifies. -/
def Failed (adj : L → R → Prop) (μ : R → Option L) (l₀ : L) : Prop :=
  ¬ Matched μ l₀ ∧ ∀ r, ReachR adj μ l₀ r → ∃ l, μ r = some l

omit [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
lemma mem_nbrs {adj : L → R → Prop} [DecidableRel adj] {l : L} {r : R}
    [Fintype R] : r ∈ nbrs adj l ↔ adj l r := by
  simp [nbrs]

/-! ### The fold inside one search -/

section Fold

variable {adj : L → R → Prop} [DecidableRel adj] {μ : R → Option L} {l : L}
  {T : (R → Option L) → Finset R → L → Option (R → Option L)}

omit [Fintype L] [DecidableEq L] [Fintype R] in
lemma step_of_some {acc : Option (R → Option L) × Finset R} {ν : R → Option L}
    (h : acc.1 = some ν) (r : R) : step adj μ l T acc r = acc := by
  unfold step; simp [h]

omit [Fintype L] [DecidableEq L] [Fintype R] in
lemma foldl_step_of_some (rs : List R) (acc : Option (R → Option L) × Finset R)
    {ν : R → Option L} (h : acc.1 = some ν) : rs.foldl (step adj μ l T) acc = acc := by
  induction rs with
  | nil => rfl
  | cons r rs ih => rw [List.foldl_cons, step_of_some h]; exact ih

omit [Fintype L] [DecidableEq L] [Fintype R] in
/-- **What a successful fold did**: some candidate `r` was taken, either fresh or by displacing
its occupant `l'` and re-augmenting `l'` from a visited set extending the current one. -/
lemma foldl_step_some :
    ∀ (rs : List R) (W : Finset R) {μ' : R → Option L},
      (rs.foldl (step adj μ l T) (none, W)).1 = some μ' →
      ∃ r ∈ rs, ∃ W' : Finset R, W ⊆ W' ∧
        ((μ r = none ∧ μ' = Function.update μ r (some l)) ∨
          ∃ l' μ'', μ r = some l' ∧ T (Function.update μ r none) (insert r W') l' = some μ'' ∧
            μ' = Function.update μ'' r (some l))
  | [], W, μ', h => by simp at h
  | r :: rs, W, μ', h => by
      rw [List.foldl_cons] at h
      rcases hμr : μ r with _ | l'
      · have hs : step adj μ l T (none, W) r =
            (some (Function.update μ r (some l)), insert r W) := by
          simp [step, hμr]
        rw [hs, foldl_step_of_some _ _ rfl] at h
        simp only at h
        exact ⟨r, List.mem_cons_self, W, subset_refl _, Or.inl ⟨hμr, (Option.some.inj h).symm⟩⟩
      · rcases hT : T (Function.update μ r none) (insert r W) l' with _ | μ''
        · have hs : step adj μ l T (none, W) r = (none, insert r W) := by
            simp [step, hμr, hT]
          rw [hs] at h
          obtain ⟨r', hr', W', hW', hcase⟩ := foldl_step_some rs (insert r W) h
          exact ⟨r', List.mem_cons_of_mem _ hr', W', (Finset.subset_insert _ _).trans hW', hcase⟩
        · have hs : step adj μ l T (none, W) r =
              (some (Function.update μ'' r (some l)), insert r W) := by
            simp [step, hμr, hT]
          rw [hs, foldl_step_of_some _ _ rfl] at h
          simp only at h
          exact ⟨r, List.mem_cons_self, W, subset_refl _,
            Or.inr ⟨l', μ'', hμr, hT, (Option.some.inj h).symm⟩⟩

end Fold

omit [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
/-- A good result relative to a larger visited set is one relative to a smaller. -/
lemma goodResult_mono_visited {adj : L → R → Prop} {μ μ' : R → Option L} {W W' : Finset R}
    {l : L} (h : W ⊆ W') (hg : GoodResult adj μ W' l μ') : GoodResult adj μ W l μ' :=
  ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, fun r hr => hg.2.2.2.2 r (h hr)⟩

/-! ### Soundness of one search -/

omit [Fintype L] [DecidableEq L] in
/-- **A successful search is a good result.** -/
theorem tryAugment_some (adj : L → R → Prop) [DecidableRel adj] :
    ∀ (fuel : ℕ) (μ : R → Option L) (W : Finset R) (l : L) (μ' : R → Option L),
      Respects adj μ → InjOnSupport μ → ¬ Matched μ l → tryAugment adj fuel μ W l = some μ' →
      GoodResult adj μ W l μ'
  | 0, _, _, _, _, _, _, _, h => by simp [tryAugment] at h
  | fuel + 1, μ, W, l, μ', hRes, hInj, hUnm, h => by
      have h' : ((nbrs adj l \ W).toList.foldl (step adj μ l (tryAugment adj fuel))
          (none, W)).1 = some μ' := h
      obtain ⟨r, hr, W', hWW', hcase⟩ := foldl_step_some _ W h'
      have hr' := Finset.mem_sdiff.1 (Finset.mem_toList.1 hr)
      have hadj : adj l r := mem_nbrs.1 hr'.1
      have hvis : r ∉ W := hr'.2
      rcases hcase with ⟨hfree, rfl⟩ | ⟨l', μ'', hOcc, hinner, rfl⟩
      · exact goodResult_fresh adj hRes hInj hUnm hfree hadj hvis
      · have hUnm' : ¬ Matched (Function.update μ r none) l' := by
          rintro ⟨r', hr'⟩
          by_cases hrr : r' = r
          · subst hrr; rw [Function.update_self] at hr'; cases hr'
          · rw [Function.update_of_ne hrr] at hr'
            exact hrr (hInj r' r l' hr' hOcc)
        have hgood := tryAugment_some adj fuel _ _ _ _ (respects_update_none adj hRes r)
          (injOnSupport_update_none hInj r) hUnm' hinner
        exact goodResult_displaced adj hUnm hadj hOcc hvis
          (goodResult_mono_visited (Finset.insert_subset_insert r hWW') hgood)

/-! ### Completeness of one search -/

/-- **Left vertices reachable from `l₀` by alternating exploration avoiding `W`**. -/
def ReachV (adj : L → R → Prop) (μ : R → Option L) (W : Finset R) (l₀ : L) : L → Prop :=
  Relation.ReflTransGen (fun l l' => ∃ r, r ∉ W ∧ adj l r ∧ μ r = some l') l₀

/-- **Every right vertex outside `W` reachable from `l₀` avoiding `W` is matched.** -/
def Sat (adj : L → R → Prop) (μ : R → Option L) (W : Finset R) (l₀ : L) : Prop :=
  ∀ l, ReachV adj μ W l₀ l → ∀ r, adj l r → r ∉ W → μ r ≠ none

section Reach

variable {adj : L → R → Prop} {μ μ₁ μ₂ : R → Option L} {W W' : Finset R} {l₀ l : L}

omit [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
lemma ReachV.mono (h : W ⊆ W') (hr : ReachV adj μ W' l₀ l) : ReachV adj μ W l₀ l :=
  Relation.ReflTransGen.mono
    (fun _ _ ⟨r, hrW, hadj, hμ⟩ => ⟨r, fun hr => hrW (h hr), hadj, hμ⟩) _ _ hr

omit [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
lemma Sat.mono (h : W ⊆ W') (hs : Sat adj μ W l₀) : Sat adj μ W' l₀ :=
  fun l hl r hadj hrW' => hs l (ReachV.mono h hl) r hadj (fun hrW => hrW' (h hrW))

omit [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
lemma ReachV.congr (h : ∀ r, r ∉ W → μ₁ r = μ₂ r) (hr : ReachV adj μ₁ W l₀ l) :
    ReachV adj μ₂ W l₀ l :=
  Relation.ReflTransGen.mono
    (fun _ _ ⟨r, hrW, hadj, hμ⟩ => ⟨r, hrW, hadj, (h r hrW).symm.trans hμ⟩) _ _ hr

omit [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
lemma Sat.congr (h : ∀ r, r ∉ W → μ₁ r = μ₂ r) (hs : Sat adj μ₁ W l₀) : Sat adj μ₂ W l₀ := by
  intro l hl r hadj hrW
  rw [← h r hrW]
  exact hs l (ReachV.congr (fun r hr => (h r hr).symm) hl) r hadj hrW

omit [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
/-- **The last visit to `P`**: a path from the occupant `l₁` of `r₁ ∈ P` that avoids `W` can be
cut at the last right vertex of `P` it passes through; what remains starts at that vertex's
occupant and avoids all of `P` (`W ⊆ P` is not even needed). -/
lemma reachV_last {P : Finset R} {r₁ : R} {l₁ : L} (hr₁P : r₁ ∈ P)
    (hr₁W : r₁ ∉ W) (hμ₁ : μ r₁ = some l₁) :
    ∀ l, ReachV adj μ W l₁ l →
      ∃ r ∈ P, r ∉ W ∧ ∃ l', μ r = some l' ∧ ReachV adj μ P l' l := by
  intro l h
  unfold ReachV at h
  induction h with
  | refl => exact ⟨r₁, hr₁P, hr₁W, l₁, hμ₁, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
    obtain ⟨r, hrW, hadj, hμ⟩ := hstep
    by_cases hrP : r ∈ P
    · exact ⟨r, hrP, hrW, _, hμ, Relation.ReflTransGen.refl⟩
    · obtain ⟨r', hr'P, hr'W, l', hμ', hreach⟩ := ih
      exact ⟨r', hr'P, hr'W, l', hμ', Relation.ReflTransGen.tail hreach ⟨r, hrP, hadj, hμ⟩⟩

end Reach

omit [Fintype L] [DecidableEq L] in
lemma card_sdiff_insert_lt {W : Finset R} {r : R} (hr : r ∉ W) :
    (Finset.univ \ insert r W).card < (Finset.univ \ W).card := by
  rw [Finset.sdiff_insert]
  exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hr⟩)

omit [Fintype L] [DecidableEq L] in
/-- **The invariant of a failing fold.** `V₀` is the visited set the whole search started from;
the accumulator's visited set `W` extends it by the candidates tried so far, each of which is
matched and whose occupant's re-search failed, certifying `Sat` relative to the current `W`. -/
lemma foldl_step_none (adj : L → R → Prop) [DecidableRel adj] {fuel : ℕ} {μ : R → Option L}
    {l₀ : L} {V₀ : Finset R}
    (IH : ∀ (ν : R → Option L) (W : Finset R) (l : L), (Finset.univ \ W).card < fuel →
      tryAugment adj fuel ν W l = none → Sat adj ν W l) :
    ∀ (rs : List R) (W : Finset R), rs.Nodup → (∀ r ∈ rs, r ∉ W) →
      (Finset.univ \ W).card ≤ fuel →
      (∀ r ∈ W, r ∉ V₀ → μ r ≠ none) →
      (∀ r ∈ W, r ∉ V₀ → ∀ l', μ r = some l' → Sat adj μ W l') →
      (rs.foldl (step adj μ l₀ (tryAugment adj fuel)) (none, W)).1 = none →
      ∃ W', W ⊆ W' ∧ (∀ r ∈ rs, r ∈ W') ∧ (∀ r ∈ W', r ∉ V₀ → μ r ≠ none) ∧
        (∀ r ∈ W', r ∉ V₀ → ∀ l', μ r = some l' → Sat adj μ W' l')
  | [], W, _, _, _, hmat, hsat, _ => ⟨W, subset_refl _, fun r hr => by simp at hr, hmat, hsat⟩
  | r :: rs, W, hnd, hnotin, hfuel, hmat, hsat, hfold => by
      obtain ⟨hrrs, hnd'⟩ := List.nodup_cons.1 hnd
      have hrW : r ∉ W := hnotin r List.mem_cons_self
      rw [List.foldl_cons] at hfold
      rcases hμr : μ r with _ | l'
      · exfalso
        have hs : step adj μ l₀ (tryAugment adj fuel) (none, W) r =
            (some (Function.update μ r (some l₀)), insert r W) := by
          simp [step, hμr]
        rw [hs, foldl_step_of_some _ _ rfl] at hfold
        simp at hfold
      · rcases hT : tryAugment adj fuel (Function.update μ r none) (insert r W) l' with _ | μ''
        · have hs : step adj μ l₀ (tryAugment adj fuel) (none, W) r = (none, insert r W) := by
            simp [step, hμr, hT]
          rw [hs] at hfold
          have hcard : (Finset.univ \ insert r W).card < (Finset.univ \ W).card :=
            card_sdiff_insert_lt hrW
          have hsat' : Sat adj μ (insert r W) l' := by
            refine Sat.congr (μ₁ := Function.update μ r none) (fun r' hr' => ?_)
              (IH _ _ _ (lt_of_lt_of_le hcard hfuel) hT)
            have hne : r' ≠ r := by rintro rfl; exact hr' (Finset.mem_insert_self _ _)
            exact Function.update_of_ne hne none μ
          obtain ⟨W', hWW', hmem, hmat', hsat''⟩ := foldl_step_none adj IH rs (insert r W) hnd'
            (fun r' hr' => by
              rw [Finset.mem_insert]
              rintro (rfl | h)
              · exact hrrs hr'
              · exact hnotin r' (List.mem_cons_of_mem _ hr') h)
            (le_trans (Finset.card_le_card
              (Finset.sdiff_subset_sdiff (subset_refl _) (Finset.subset_insert _ _))) hfuel)
            (fun r' hr' hV => by
              rcases Finset.mem_insert.1 hr' with rfl | h
              · rw [hμr]; exact Option.some_ne_none _
              · exact hmat r' h hV)
            (fun r' hr' hV l'' hμ => by
              rcases Finset.mem_insert.1 hr' with rfl | h
              · rw [hμr] at hμ; cases hμ; exact hsat'
              · exact Sat.mono (Finset.subset_insert _ _) (hsat r' h hV l'' hμ))
            hfold
          refine ⟨W', (Finset.subset_insert _ _).trans hWW', fun r' hr' => ?_, hmat', hsat''⟩
          rcases List.mem_cons.1 hr' with rfl | h
          · exact hWW' (Finset.mem_insert_self _ _)
          · exact hmem r' h
        · exfalso
          have hs : step adj μ l₀ (tryAugment adj fuel) (none, W) r =
              (some (Function.update μ'' r (some l₀)), insert r W) := by
            simp [step, hμr, hT]
          rw [hs, foldl_step_of_some _ _ rfl] at hfold
          simp at hfold

omit [Fintype L] [DecidableEq L] in
/-- **A failed search certifies saturation**: with fuel exceeding the number of unvisited right
vertices, every right vertex reachable from `l₀` avoiding `W` (and outside `W`) is matched. -/
theorem tryAugment_none (adj : L → R → Prop) [DecidableRel adj] :
    ∀ (fuel : ℕ) (μ : R → Option L) (W : Finset R) (l₀ : L),
      (Finset.univ \ W).card < fuel → tryAugment adj fuel μ W l₀ = none → Sat adj μ W l₀
  | 0, _, _, _, hfuel, _ => absurd hfuel (Nat.not_lt_zero _)
  | fuel + 1, μ, W, l₀, hfuel, hnone => by
      have hfold : ((nbrs adj l₀ \ W).toList.foldl (step adj μ l₀ (tryAugment adj fuel))
          (none, W)).1 = none := hnone
      obtain ⟨W', hWW', hmem, hmat, hsat⟩ := foldl_step_none adj (V₀ := W)
        (tryAugment_none adj fuel) (nbrs adj l₀ \ W).toList W (Finset.nodup_toList _)
        (fun r hr => (Finset.mem_sdiff.1 (Finset.mem_toList.1 hr)).2) (Nat.lt_succ_iff.1 hfuel)
        (fun r hr hrW => absurd hr hrW) (fun r hr hrW => absurd hr hrW) hfold
      intro l hl r hadj hrW
      have hnb : ∀ {l' : L} {r' : R}, adj l' r' → r' ∉ W → l' = l₀ → r' ∈ W' := by
        rintro l' r' hadj' hr'W rfl
        exact hmem r' (Finset.mem_toList.2 (Finset.mem_sdiff.2 ⟨mem_nbrs.2 hadj', hr'W⟩))
      rcases Relation.ReflTransGen.cases_head hl with heq | ⟨l₁, ⟨r₁, hr₁W, hadj₁, hμ₁⟩, hreach⟩
      · exact hmat r (hnb hadj hrW heq.symm) hrW
      · have hr₁W' : r₁ ∈ W' := hnb hadj₁ hr₁W rfl
        obtain ⟨r₂, hr₂W', hr₂W, l₂, hμ₂, hreach₂⟩ := reachV_last hr₁W' hr₁W hμ₁ l hreach
        by_cases hrW'' : r ∈ W'
        · exact hmat r hrW'' hrW
        · exact hsat r₂ hr₂W' hr₂W l₂ hμ₂ l hreach₂ r hadj hrW''

omit [Fintype L] [DecidableEq L] in
/-- **A failed search from an unmatched `l₀`, with enough fuel and nothing visited, means `l₀`
failed.** -/
theorem failed_of_tryAugment_none (adj : L → R → Prop) [DecidableRel adj] {fuel : ℕ}
    (hfuel : Fintype.card R < fuel) {μ : R → Option L} {l₀ : L} (hUnm : ¬ Matched μ l₀)
    (h : tryAugment adj fuel μ ∅ l₀ = none) : Failed adj μ l₀ := by
  have hsat : Sat adj μ ∅ l₀ :=
    tryAugment_none adj fuel μ ∅ l₀ (by rwa [Finset.sdiff_empty, Finset.card_univ]) h
  refine ⟨hUnm, fun r ⟨l, hl, hadj⟩ => ?_⟩
  have hl' : ReachV adj μ ∅ l₀ l :=
    Relation.ReflTransGen.mono
      (fun _ _ ⟨r, hadj, hμ⟩ => ⟨r, Finset.notMem_empty r, hadj, hμ⟩) _ _ hl
  exact Option.ne_none_iff_exists'.1 (hsat l hl' r hadj (Finset.notMem_empty r))

/-! ### Stability of failure -/

/-- **Failure is stable**: if `l₀` failed in a matching `μ`, then after a good augmentation of
`μ` from any other unmatched `l₁`, `l₀` has still failed. The reached sets `S` (left) and `V`
(right) from `l₀` in `μ` satisfy `|V| ≤ |S \ {l₀}|`; after the augmentation every vertex of
`S \ {l₀}` is still matched, into `V`, injectively — so all of `V` is matched, into `S \ {l₀}`,
which keeps the exploration from `l₀` inside `S` and `V`. -/
theorem failed_stable {adj : L → R → Prop} {μ μ' : R → Option L} {l₀ l₁ : L}
    (hM : IsMatching adj μ) (hF : Failed adj μ l₀) (hne : l₁ ≠ l₀) (hUnm₁ : ¬ Matched μ l₁)
    (hG : GoodResult adj μ ∅ l₁ μ') : Failed adj μ' l₀ := by
  classical
  obtain ⟨hRes, hInj⟩ := hM
  obtain ⟨hUnm₀, hSat⟩ := hF
  obtain ⟨hRes', hInj', hM₁', hIff, -⟩ := hG
  set S : Finset L := Finset.univ.filter (ReachL adj μ l₀) with hS
  set V : Finset R := Finset.univ.filter (ReachR adj μ l₀) with hV
  have hmemS : ∀ l, l ∈ S ↔ ReachL adj μ l₀ l := by intro l; simp [hS]
  have hmemV : ∀ r, r ∈ V ↔ ReachR adj μ l₀ r := by intro r; simp [hV]
  -- (a) the occupant of a reached right vertex is a reached left vertex other than `l₀`
  have hA : ∀ r ∈ V, ∃ l ∈ S.erase l₀, μ r = some l := by
    intro r hr
    obtain ⟨l, hl, hlr⟩ := (hmemV r).1 hr
    obtain ⟨l', hl'⟩ := hSat r ⟨l, hl, hlr⟩
    refine ⟨l', Finset.mem_erase.2 ⟨?_, (hmemS l').2 (ReachL.step hl hlr hl')⟩, hl'⟩
    rintro rfl; exact hUnm₀ ⟨r, hl'⟩
  -- (b) every reached left vertex other than `l₀` occupies a reached right vertex
  have hB : ∀ l ∈ S.erase l₀, ∃ r ∈ V, μ r = some l := by
    intro l hl
    obtain ⟨hne0, hlS⟩ := Finset.mem_erase.1 hl
    have hreach : ReachL adj μ l₀ l := (hmemS l).1 hlS
    rcases Relation.ReflTransGen.cases_tail hreach with heq | ⟨l₂, h₂, r, hadj, hμ⟩
    · exact absurd heq hne0
    · exact ⟨r, (hmemV r).2 ⟨l₂, h₂, hadj⟩, hμ⟩
  have hcard1 : V.card ≤ (S.erase l₀).card :=
    Finset.card_le_card_of_forall_subsingleton (fun r l => μ r = some l) hA
      (fun l _ r₁ hr₁ r₂ hr₂ => hInj r₁ r₂ l hr₁.2 hr₂.2)
  -- in `μ'`, every vertex of `S \ {l₀}` is still matched, into `V`
  have hB' : ∀ l ∈ S.erase l₀, ∃ r ∈ V, μ' r = some l := by
    intro l hl
    obtain ⟨r, hr, hμ⟩ := hB l hl
    have hne1 : l ≠ l₁ := by rintro rfl; exact hUnm₁ ⟨r, hμ⟩
    obtain ⟨r', hr'⟩ := (hIff l hne1).1 ⟨r, hμ⟩
    exact ⟨r', (hmemV r').2 ⟨l, (hmemS l).1 (Finset.mem_erase.1 hl).2, hRes' r' l hr'⟩, hr'⟩
  -- hence every vertex of `V` is matched in `μ'`, into `S \ {l₀}`
  have hA' : ∀ r ∈ V, ∃ l ∈ S.erase l₀, μ' r = some l := by
    intro r₀ hr₀
    by_contra hcon
    have h1 : (S.erase l₀).card ≤ (V.erase r₀).card :=
      Finset.card_le_card_of_forall_subsingleton (fun l r => μ' r = some l)
        (fun l hl => by
          obtain ⟨r, hr, hμ⟩ := hB' l hl
          refine ⟨r, Finset.mem_erase.2 ⟨?_, hr⟩, hμ⟩
          rintro rfl; exact hcon ⟨l, hl, hμ⟩)
        (fun r _ l₁ hl₁ l₂ hl₂ => Option.some.inj (hl₁.2.symm.trans hl₂.2))
    have h2 := Finset.card_erase_lt_of_mem hr₀
    omega
  -- the exploration from `l₀` in `μ'` stays inside `S`
  have hclosed : ∀ l, ReachL adj μ' l₀ l → l ∈ S := by
    intro l h
    unfold ReachL at h
    induction h with
    | refl => exact (hmemS l₀).2 ReachL.start
    | tail _ hstep ih =>
      obtain ⟨r, hadj, hμ⟩ := hstep
      have hrV : r ∈ V := (hmemV r).2 ⟨_, (hmemS _).1 ih, hadj⟩
      obtain ⟨l'', hl'', hμ''⟩ := hA' r hrV
      rw [hμ] at hμ''
      cases hμ''
      exact (Finset.mem_erase.1 hl'').2
  refine ⟨fun h => hUnm₀ ((hIff l₀ hne.symm).2 h), ?_⟩
  rintro r ⟨l, hl, hadj⟩
  have hrV : r ∈ V := (hmemV r).2 ⟨l, (hmemS l).1 (hclosed l hl), hadj⟩
  obtain ⟨l', _, hμ'⟩ := hA' r hrV
  exact ⟨l', hμ'⟩

/-! ### The invariant of the whole run -/

/-- **The run's invariant**: the current matching is a matching; every left vertex is matched,
or failed, or still to be processed; the vertices still to be processed are unmatched. At the end
every left vertex is matched or failed. -/
theorem runAll_spec (adj : L → R → Prop) [DecidableRel adj] {fuel : ℕ}
    (hfuel : Fintype.card R < fuel) :
    ∀ (ls : List L) (μ : R → Option L), ls.Nodup → IsMatching adj μ →
      (∀ l ∈ ls, ¬ Matched μ l) → (∀ l, Matched μ l ∨ Failed adj μ l ∨ l ∈ ls) →
      IsMatching adj (runAll adj fuel ls μ) ∧
        ∀ l, Matched (runAll adj fuel ls μ) l ∨ Failed adj (runAll adj fuel ls μ) l
  | [], μ, _, hM, _, hall => ⟨hM, fun l => by
      rcases hall l with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · simp at h⟩
  | l :: ls, μ, hnd, hM, hunm, hall => by
      obtain ⟨hlls, hnd'⟩ := List.nodup_cons.1 hnd
      have hl : ¬ Matched μ l := hunm l List.mem_cons_self
      simp only [runAll]
      rcases h : tryAugment adj fuel μ ∅ l with _ | μ'
      · have hF : Failed adj μ l := failed_of_tryAugment_none adj hfuel hl h
        refine runAll_spec adj hfuel ls μ hnd' hM
          (fun l' hl' => hunm l' (List.mem_cons_of_mem _ hl')) (fun l' => ?_)
        rcases hall l' with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · rcases List.mem_cons.1 h3 with rfl | h3
          · exact Or.inr (Or.inl hF)
          · exact Or.inr (Or.inr h3)
      · have hG : GoodResult adj μ ∅ l μ' := tryAugment_some adj fuel μ ∅ l μ' hM.1 hM.2 hl h
        have hIff := hG.2.2.2.1
        refine runAll_spec adj hfuel ls μ' hnd' ⟨hG.1, hG.2.1⟩ (fun l' hl' hm => ?_)
          (fun l' => ?_)
        · have hne : l' ≠ l := fun he => hlls (he ▸ hl')
          exact hunm l' (List.mem_cons_of_mem _ hl') ((hIff l' hne).2 hm)
        · by_cases hne : l' = l
          · subst hne; exact Or.inl hG.2.2.1
          · rcases hall l' with h1 | h2 | h3
            · exact Or.inl ((hIff l' hne).1 h1)
            · exact Or.inr (Or.inl (failed_stable hM h2 (Ne.symm hne) hl hG))
            · rcases List.mem_cons.1 h3 with h3 | h3
              · exact absurd h3 hne
              · exact Or.inr (Or.inr h3)

/-- **What Kuhn's algorithm outputs**: a matching in which every left vertex is matched or
failed. -/
theorem kuhn_spec (adj : L → R → Prop) [DecidableRel adj] :
    IsMatching adj (kuhn adj) ∧ ∀ l, Matched (kuhn adj) l ∨ Failed adj (kuhn adj) l :=
  runAll_spec adj (Nat.lt_succ_self _) Finset.univ.toList (fun _ => none)
    (Finset.nodup_toList _) ⟨fun _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩
    (fun _ _ ⟨_, h⟩ => by simp at h)
    (fun l => Or.inr (Or.inr (Finset.mem_toList.2 (Finset.mem_univ l))))

/-! ### Counting -/

open Classical in
/-- The matched left vertices. -/
noncomputable def matchedL (μ : R → Option L) : Finset L := Finset.univ.filter (Matched μ)

open Classical in
/-- The unmatched left vertices. -/
noncomputable def unmatchedL (μ : R → Option L) : Finset L :=
  Finset.univ.filter fun l => ¬ Matched μ l

open Classical in
/-- The left vertices reachable by alternating exploration from some unmatched left vertex. -/
noncomputable def reachSet (adj : L → R → Prop) (μ : R → Option L) : Finset L :=
  Finset.univ.filter fun l => ∃ l₀ ∈ unmatchedL μ, ReachL adj μ l₀ l

open Classical in
/-- The right neighbours of a set of left vertices. -/
noncomputable def nbrSet (adj : L → R → Prop) (S : Finset L) : Finset R :=
  Finset.univ.filter fun r => ∃ l ∈ S, adj l r

omit [DecidableEq L] [Fintype R] [DecidableEq R] in
lemma mem_matchedL {μ : R → Option L} {l : L} : l ∈ matchedL μ ↔ Matched μ l := by
  simp [matchedL]

omit [DecidableEq L] [Fintype R] [DecidableEq R] in
lemma mem_unmatchedL {μ : R → Option L} {l : L} : l ∈ unmatchedL μ ↔ ¬ Matched μ l := by
  simp [unmatchedL]

omit [DecidableEq L] [Fintype R] [DecidableEq R] in
lemma mem_reachSet {adj : L → R → Prop} {μ : R → Option L} {l : L} :
    l ∈ reachSet adj μ ↔ ∃ l₀ ∈ unmatchedL μ, ReachL adj μ l₀ l := by
  simp only [reachSet, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype L] [DecidableEq L] [DecidableEq R] in
lemma mem_nbrSet {adj : L → R → Prop} {S : Finset L} {r : R} :
    r ∈ nbrSet adj S ↔ ∃ l ∈ S, adj l r := by
  simp only [nbrSet, Finset.mem_filter, Finset.mem_univ, true_and]

omit [DecidableEq L] [Fintype R] [DecidableEq R] in
open Classical in
lemma card_matchedL_add_card_unmatchedL (μ : R → Option L) :
    (matchedL μ).card + (unmatchedL μ).card = Fintype.card L := by
  unfold matchedL unmatchedL
  rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]

omit [DecidableEq L] [DecidableEq R] in
/-- An injective `μ` matches as many right vertices as left vertices. -/
lemma size_eq_card_matchedL {μ : R → Option L} (hInj : InjOnSupport μ) :
    size μ = (matchedL μ).card := by
  apply le_antisymm
  · exact Finset.card_le_card_of_forall_subsingleton (fun r l => μ r = some l)
      (fun r hr => by
        obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 (Finset.mem_filter.1 hr).2
        exact ⟨l, mem_matchedL.2 ⟨r, hl⟩, hl⟩)
      (fun l _ r₁ hr₁ r₂ hr₂ => hInj r₁ r₂ l hr₁.2 hr₂.2)
  · exact Finset.card_le_card_of_forall_subsingleton (fun l r => μ r = some l)
      (fun l hl => by
        obtain ⟨r, hr⟩ := mem_matchedL.1 hl
        exact ⟨r, Finset.mem_filter.2 ⟨Finset.mem_univ _, Option.isSome_iff_exists.2 ⟨l, hr⟩⟩, hr⟩)
      (fun r _ l₁ hl₁ l₂ hl₂ => Option.some.inj (hl₁.2.symm.trans hl₂.2))

omit [DecidableEq R] in
/-- **A matching in which every left vertex is matched or failed is maximum.** -/
theorem size_le_of_saturating {adj : L → R → Prop} {μ : R → Option L} (hM : IsMatching adj μ)
    (hall : ∀ l, Matched μ l ∨ Failed adj μ l) {μ' : R → Option L} (hM' : IsMatching adj μ') :
    size μ' ≤ size μ := by
  classical
  obtain ⟨hRes, hInj⟩ := hM
  obtain ⟨hRes', hInj'⟩ := hM'
  set F := unmatchedL μ with hF
  set S := reachSet adj μ with hS
  set V := nbrSet adj S with hV
  have hFS : F ⊆ S := fun l hl => mem_reachSet.2 ⟨l, hl, ReachL.start⟩
  -- every neighbour of `S` is matched, into `S \ F`
  have hi : ∀ r ∈ V, ∃ l ∈ S \ F, μ r = some l := by
    intro r hr
    obtain ⟨l, hlS, hadj⟩ := mem_nbrSet.1 hr
    obtain ⟨l₀, hl₀F, hreach⟩ := mem_reachSet.1 hlS
    have hfail : Failed adj μ l₀ := (hall l₀).resolve_left (mem_unmatchedL.1 hl₀F)
    obtain ⟨l', hl'⟩ := hfail.2 r ⟨l, hreach, hadj⟩
    refine ⟨l', Finset.mem_sdiff.2 ⟨mem_reachSet.2 ⟨l₀, hl₀F, ReachL.step hreach hadj hl'⟩, ?_⟩,
      hl'⟩
    intro hl'F; exact mem_unmatchedL.1 hl'F ⟨r, hl'⟩
  have hc1 : V.card ≤ (S \ F).card :=
    Finset.card_le_card_of_forall_subsingleton (fun r l => μ r = some l) hi
      (fun l _ r₁ h₁ r₂ h₂ => hInj r₁ r₂ l h₁.2 h₂.2)
  have hSF : (S \ F).card + F.card = S.card := Finset.card_sdiff_add_card_eq_card hFS
  have hsize : size μ + F.card = Fintype.card L := by
    rw [size_eq_card_matchedL hInj]; exact card_matchedL_add_card_unmatchedL μ
  have hsize' : size μ' = (matchedL μ').card := size_eq_card_matchedL hInj'
  -- the vertices `μ'` matches: those in `S`, at most `|V|` of them, and those outside `S`
  have hsplit : (matchedL μ').card ≤ (S.filter (Matched μ')).card + (Fintype.card L - S.card) := by
    have h1 : matchedL μ' ⊆ S.filter (Matched μ') ∪ (Finset.univ \ S) := by
      intro l hl
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
      by_cases hlS : l ∈ S
      · exact Or.inl ⟨hlS, mem_matchedL.1 hl⟩
      · exact Or.inr ⟨Finset.mem_univ _, hlS⟩
    calc (matchedL μ').card ≤ (S.filter (Matched μ') ∪ (Finset.univ \ S)).card :=
          Finset.card_le_card h1
      _ ≤ (S.filter (Matched μ')).card + (Finset.univ \ S).card := Finset.card_union_le _ _
      _ = _ := by rw [Finset.card_univ_sdiff]
  have hSV : (S.filter (Matched μ')).card ≤ V.card :=
    Finset.card_le_card_of_forall_subsingleton (fun l r => μ' r = some l)
      (fun l hl => by
        obtain ⟨hlS, r, hr⟩ := Finset.mem_filter.1 hl
        exact ⟨r, mem_nbrSet.2 ⟨l, hlS, hRes' r l hr⟩, hr⟩)
      (fun r _ l₁ h₁ l₂ h₂ => Option.some.inj (h₁.2.symm.trans h₂.2))
  have hSL : S.card ≤ Fintype.card L := Finset.card_le_univ S
  omega

/-! ### The theorems -/

/-- **Kuhn's algorithm outputs a maximum matching.** -/
theorem kuhn_maximum (adj : L → R → Prop) [DecidableRel adj] :
    IsMatching adj (kuhn adj) ∧ ∀ μ, IsMatching adj μ → size μ ≤ size (kuhn adj) :=
  let h := kuhn_spec adj
  ⟨h.1, fun _ hμ => size_le_of_saturating h.1 h.2 hμ⟩

/-- **Kuhn's algorithm saturates the left side iff a full matching exists.** -/
theorem kuhn_full_iff (adj : L → R → Prop) [DecidableRel adj] :
    (∀ l, Matched (kuhn adj) l) ↔ HasFullMatching adj := by
  obtain ⟨⟨hRes, hInj⟩, hall⟩ := kuhn_spec adj
  constructor
  · intro h
    choose f hf using h
    refine ⟨f, fun l₁ l₂ he => ?_, fun l => hRes _ _ (hf l)⟩
    have h₂ := hf l₂
    rw [← he] at h₂
    exact Option.some.inj ((hf l₁).symm.trans h₂)
  · intro hfull l
    by_contra hl
    obtain ⟨hUnm, hSat⟩ := (hall l).resolve_left hl
    exact not_hasFullMatching_of_saturated adj hInj hUnm hSat hfull

end Lax117284Proofs.Bipartite.Maximum
