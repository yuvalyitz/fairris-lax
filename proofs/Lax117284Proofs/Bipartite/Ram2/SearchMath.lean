import Lax117284Proofs.Bipartite.StackSearchCorrect

/-!
The mathematics of the array-based backtracking search, with no machine in sight.

The machine keeps the stack in three parallel arrays `stkL`, `stkR`, `stkX`; here they are three
functions `Ls Rs : ℕ → ℕ` (the third, the resume column, is pure machine bookkeeping and plays no
role in correctness). Frame `k` places left vertex `Ls k` by trying right vertex `Rs k`; frame
`k + 1` exists because `Rs k` was occupied by `Ls (k + 1)`.

`PathA` is the *flat* well-formedness of the first `t` frames: everything that
`StackSearchCorrect.StackWF` says, minus its lists of not-yet-tried candidates (this search finds
its candidates lazily, by scanning, so there are none to record). `success_good` then shows that
when one more frame finds a free right vertex, applying every frame's choice, bottom to top, is a
`GoodResult` — by *reusing* `StackSearchCorrect.collapse_free`, with each frame's `rest` left
empty.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching Lax117284Proofs.Bipartite.StackSearch Lax117284Proofs.Bipartite.StackSearchCorrect

/-- The frames `Ls 0, Rs 0` up to `Ls (k-1), Rs (k-1)` as a `StackSearch` stack: head = top. -/
def framesOf (Ls Rs : ℕ → ℕ) : ℕ → List (Frame ℕ ℕ)
  | 0 => []
  | k + 1 => ⟨Ls k, Rs k, []⟩ :: framesOf Ls Rs k

/-- Apply the first `k` frames' choices to `μ`, bottom to top (frame `0` first). -/
def applyN (μ : ℕ → Option ℕ) (Ls Rs : ℕ → ℕ) : ℕ → ℕ → Option ℕ
  | 0 => μ
  | k + 1 => Function.update (applyN μ Ls Rs k) (Rs k) (some (Ls k))

/-- **The first `t` frames are a well-formed path**: the bottom frame places `l₀`, every frame
chose an edge of its own left vertex, each chosen right vertex (but the last frame's) is occupied
by the next frame's left vertex, and no right vertex is chosen twice. -/
structure PathA (adjB : ℕ → ℕ → Prop) (μ₀ : ℕ → Option ℕ) (l₀ : ℕ) (Ls Rs : ℕ → ℕ) (t : ℕ) :
    Prop where
  start : Ls 0 = l₀
  adj : ∀ k < t, adjB (Ls k) (Rs k)
  link : ∀ k, k + 1 < t → μ₀ (Rs k) = some (Ls (k + 1))
  distinct : ∀ i k, i < k → k < t → Rs i ≠ Rs k

theorem mem_framesOf {Ls Rs : ℕ → ℕ} {f : Frame ℕ ℕ} :
    ∀ {k : ℕ}, f ∈ framesOf Ls Rs k → ∃ i < k, f.r = Rs i
  | 0, h => by simp [framesOf] at h
  | k + 1, h => by
      rw [framesOf, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨k, Nat.lt_succ_self k, rfl⟩
      · obtain ⟨i, hi, hr⟩ := mem_framesOf h
        exact ⟨i, by omega, hr⟩

theorem mem_belowVisited_framesOf {Ls Rs : ℕ → ℕ} {x : ℕ} :
    ∀ {k : ℕ}, x ∈ belowVisited (∅ : Finset ℕ) (framesOf Ls Rs k) ↔ ∃ i < k, Rs i = x
  | 0 => by simp [framesOf, belowVisited]
  | k + 1 => by
      rw [framesOf, belowVisited, Finset.mem_insert, mem_belowVisited_framesOf]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨k, Nat.lt_succ_self k, rfl⟩
        · exact ⟨i, by omega, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
        · exact Or.inr ⟨i, h, rfl⟩
        · exact Or.inl rfl

/-- **A flat path is a `StackWF` stack** (with every `rest` empty). -/
theorem stackWF_of_pathA {adjB : ℕ → ℕ → Prop} [DecidableRel adjB] {μ₀ : ℕ → Option ℕ}
    {l₀ : ℕ} {Ls Rs : ℕ → ℕ} :
    ∀ t, PathA adjB μ₀ l₀ Ls Rs (t + 1) → StackWF adjB μ₀ ∅ l₀ (framesOf Ls Rs (t + 1))
  | 0, h => by
      show StackWF adjB μ₀ ∅ l₀ [⟨Ls 0, Rs 0, []⟩]
      refine ⟨h.start, fun x hx => ?_⟩
      have : x = Rs 0 := by simpa using hx
      subst this
      exact ⟨h.adj 0 (by omega), by simp⟩
  | t + 1, h => by
      have h' : PathA adjB μ₀ l₀ Ls Rs (t + 1) :=
        ⟨h.start, fun k hk => h.adj k (by omega), fun k hk => h.link k (by omega),
          fun i k hik hk => h.distinct i k hik (by omega)⟩
      have hne : ∀ f' ∈ framesOf Ls Rs t, f'.r ≠ Rs t := fun f' hf' => by
        obtain ⟨i, hi, hr⟩ := mem_framesOf hf'
        rw [hr]; exact h.distinct i t hi (by omega)
      show StackWF adjB μ₀ ∅ l₀
        (⟨Ls (t + 1), Rs (t + 1), []⟩ :: ⟨Ls t, Rs t, []⟩ :: framesOf Ls Rs t)
      refine ⟨stackWF_of_pathA t h', ?_, fun x hx => ?_⟩
      · show belowMatching μ₀ (framesOf Ls Rs t) (Rs t) = some (Ls (t + 1))
        rw [belowMatching_eq_of_notMem μ₀ (Rs t) (framesOf Ls Rs t) hne]
        exact h.link t (by omega)
      · have hx' : x = Rs (t + 1) := by simpa using hx
        subst hx'
        refine ⟨h.adj (t + 1) (by omega), fun hmem => ?_⟩
        rcases Finset.mem_insert.mp hmem with h1 | h1
        · exact h.distinct t (t + 1) (by omega) (by omega) h1.symm
        · obtain ⟨i, hi, hr⟩ := mem_belowVisited_framesOf.mp h1
          exact h.distinct i (t + 1) (by omega) (by omega) hr

theorem applyN_update_comm (Ls Rs : ℕ → ℕ) (r : ℕ) (v : Option ℕ) :
    ∀ (k : ℕ) (μ : ℕ → Option ℕ), (∀ i < k, Rs i ≠ r) →
      applyN (Function.update μ r v) Ls Rs k = Function.update (applyN μ Ls Rs k) r v
  | 0, _, _ => rfl
  | k + 1, μ, h => by
      show Function.update (applyN (Function.update μ r v) Ls Rs k) (Rs k) (some (Ls k)) =
        Function.update (Function.update (applyN μ Ls Rs k) (Rs k) (some (Ls k))) r v
      rw [applyN_update_comm Ls Rs r v k μ (fun i hi => h i (by omega)),
        Function.update_comm (h k (by omega)).symm]

/-- **The stack's own fold is the bottom-to-top application**, since the keys are distinct. -/
theorem fold_framesOf (Ls Rs : ℕ → ℕ) :
    ∀ (k : ℕ) (μ : ℕ → Option ℕ), (∀ i j, i < j → j < k → Rs i ≠ Rs j) →
      fold μ (framesOf Ls Rs k) = applyN μ Ls Rs k
  | 0, _, _ => rfl
  | k + 1, μ, h => by
      show fold (Function.update μ (Rs k) (some (Ls k))) (framesOf Ls Rs k) =
        Function.update (applyN μ Ls Rs k) (Rs k) (some (Ls k))
      rw [fold_framesOf Ls Rs k _ (fun i j hij hj => h i j hij (by omega)),
        applyN_update_comm Ls Rs (Rs k) _ k μ (fun i hi => h i k hi (by omega))]

/-- **Extending a path by one frame** that chose a fresh edge. -/
theorem PathA.extend {adjB : ℕ → ℕ → Prop} {μ₀ : ℕ → Option ℕ} {l₀ : ℕ} {Ls Rs : ℕ → ℕ} {t j : ℕ}
    (hP : PathA adjB μ₀ l₀ Ls Rs t) (hlink : ∀ k < t, μ₀ (Rs k) = some (Ls (k + 1)))
    (hadj : adjB (Ls t) j) (hd : ∀ i < t, Rs i ≠ j) :
    PathA adjB μ₀ l₀ Ls (Function.update Rs t j) (t + 1) := by
  refine ⟨hP.start, fun k hk => ?_, fun k hk => ?_, fun i k hik hk => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
    · rw [Function.update_of_ne (by omega)]; exact hP.adj k h
    · rw [Function.update_self]; exact hadj
  · have : k < t := by omega
    rw [Function.update_of_ne (by omega)]; exact hlink k this
  · have hit : i ≠ t := by omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
    · rw [Function.update_of_ne hit, Function.update_of_ne (by omega)]
      exact hP.distinct i k hik h
    · rw [Function.update_of_ne hit, Function.update_self]
      exact hd i hik

/-- **Soundness of a successful search.** `t` frames form a path, the next frame (left vertex
`Ls t`) found an unmatched neighbour `j` not chosen by any of them: applying all `t + 1`
choices, bottom to top, is a `GoodResult` for `l₀`. -/
theorem success_good {adjB : ℕ → ℕ → Prop} [DecidableRel adjB] {μ₀ : ℕ → Option ℕ} {l₀ : ℕ}
    {Ls Rs : ℕ → ℕ} {t j : ℕ} (hRes : Respects adjB μ₀) (hInj : InjOnSupport μ₀)
    (hUnm : ¬ Matched μ₀ l₀) (hP : PathA adjB μ₀ l₀ Ls Rs t)
    (hlink : ∀ k < t, μ₀ (Rs k) = some (Ls (k + 1))) (hadj : adjB (Ls t) j)
    (hd : ∀ i < t, Rs i ≠ j) (hfree : μ₀ j = none) :
    GoodResult adjB μ₀ ∅ l₀ (applyN μ₀ Ls (Function.update Rs t j) (t + 1)) := by
  have hP' := hP.extend hlink hadj hd
  have hwf := stackWF_of_pathA t hP'
  have hfree' : belowMatching μ₀ (framesOf Ls (Function.update Rs t j) t) j = none := by
    rw [belowMatching_eq_of_notMem μ₀ j (framesOf Ls (Function.update Rs t j) t)]
    · exact hfree
    · intro f' hf'
      obtain ⟨i, hi, hr⟩ := mem_framesOf hf'
      rw [hr, Function.update_of_ne (by omega)]
      exact hd i hi
  have hcf := collapse_free adjB hRes hInj hUnm
    (⟨Ls t, Function.update Rs t j t, []⟩ : Frame ℕ ℕ)
    (framesOf Ls (Function.update Rs t j) t) hwf
    (by rw [Function.update_self]; exact hfree')
  have hfold := fold_framesOf Ls (Function.update Rs t j) (t + 1) μ₀ hP'.distinct
  exact hfold ▸ hcf

end Lax117284Proofs.Bipartite.Ram2
