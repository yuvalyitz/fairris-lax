import Lax117284Proofs.Bipartite.StackSearch

/-!
The stack-of-frames reading of `Matching.tryAugment`'s nested recursion, and the lemma that
lets a machine search over an explicit stack reuse the recursive correctness proof. The stack
is read as a snapshot of `Matching.tryAugment`'s own nested recursion: each frame is one
suspended level of that recursion, and reading downward (towards the bottom of the stack)
reconstructs the matching and visited-set that level's own search was conducted under, by
undoing (clearing) the choices every shallower frame has made so far. `StackWF` pins down that
this reconstruction is faithful, and `collapse_free` says a well-formed stack whose top choice
is free collapses to a `GoodResult`.
-/

namespace Lax117284Proofs.Bipartite.StackSearchCorrect

open Lax117284.BipartiteKuhn
open Lax117284Proofs.Bipartite.Matching
open Lax117284Proofs.Bipartite.StackSearch

variable {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- The visited set in effect when the frames in `below` were, one by one, pushed on top of
whatever `visited₀` already was: each frame's own `r`, accumulated. -/
def belowVisited (visited₀ : Finset R) : List (Frame L R) → Finset R
  | [] => visited₀
  | f :: rest => insert f.r (belowVisited visited₀ rest)

/-- The matching in effect when the frames in `below` were pushed: `μ₀` with every one of their
chosen right vertices cleared (order does not matter — see `belowMatching_comm`). -/
def belowMatching (μ₀ : R → Option L) : List (Frame L R) → R → Option L
  | [] => μ₀
  | f :: rest => Function.update (belowMatching μ₀ rest) f.r none

/-- **A stack is well-formed** relative to the search's original `μ₀`/`visited₀`/`l₀`: reading
bottom-to-top, the bottom frame's `l` is `l₀`, and every one of its remaining candidates —
current and not-yet-tried alike — is a genuine neighbour of `l₀`, fresh relative to `visited₀`;
each frame above is there because the frame below it, under its own context matching, is
occupied by exactly this frame's `l`, and every one of its own remaining candidates is a genuine
neighbour of its own `l`, fresh relative to what the frames below it have already claimed.
Stating this for the *whole* remaining candidate list, not just the current head, is what lets
a search advance to the next candidate for free: it is already known good, being a member of
the very same list. -/
def StackWF (adj : L → R → Prop) [DecidableRel adj] (μ₀ : R → Option L) (visited₀ : Finset R)
    (l₀ : L) : List (Frame L R) → Prop
  | [] => False
  | [f] => f.l = l₀ ∧ ∀ x ∈ f.r :: f.rest, adj f.l x ∧ x ∉ visited₀
  | f :: f2 :: rest =>
      StackWF adj μ₀ visited₀ l₀ (f2 :: rest) ∧
      belowMatching μ₀ rest f2.r = some f.l ∧
      ∀ x ∈ f.r :: f.rest, adj f.l x ∧ x ∉ insert f2.r (belowVisited visited₀ rest)

omit [Fintype L] [DecidableEq L] [Fintype R] in
/-- **Every frame in `below` contributed its own `r` to `belowVisited`.** -/
lemma mem_belowVisited (visited₀ : Finset R) :
    ∀ (below : List (Frame L R)) {f' : Frame L R}, f' ∈ below → f'.r ∈ belowVisited visited₀ below
  | f :: rest, f', hf' => by
      rw [List.mem_cons] at hf'
      rcases hf' with rfl | hf'
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (mem_belowVisited visited₀ rest hf')

omit [Fintype L] [DecidableEq L] [Fintype R] in
/-- **A frame's own choice is a genuine neighbour of its own `l`, and is fresh relative to what
the frames below it have already claimed.** -/
lemma frame_adj_and_fresh (adj : L → R → Prop) [DecidableRel adj] {μ₀ : R → Option L}
    {visited₀ : Finset R} {l₀ : L} :
    ∀ (f : Frame L R) (below : List (Frame L R)), StackWF adj μ₀ visited₀ l₀ (f :: below) →
      adj f.l f.r ∧ f.r ∉ belowVisited visited₀ below
  | _, [], hwf => hwf.2 _ List.mem_cons_self
  | _, _ :: _, hwf => hwf.2.2 _ List.mem_cons_self

omit [Fintype L] [DecidableEq L] [Fintype R] in
/-- **Every `r` chosen by a frame in `below` differs from every other's.** -/
lemma frame_pairwise_ne (adj : L → R → Prop) [DecidableRel adj] {μ₀ : R → Option L}
    {visited₀ : Finset R} {l₀ : L} :
    ∀ (f : Frame L R) (below : List (Frame L R)), StackWF adj μ₀ visited₀ l₀ (f :: below) →
      ∀ f' ∈ below, f'.r ≠ f.r
  | f, f2 :: rest, hwf, f', hf' => by
      have hfresh := (frame_adj_and_fresh adj f (f2 :: rest) hwf).2
      intro he
      exact hfresh (he ▸ mem_belowVisited visited₀ (f2 :: rest) hf')

omit [Fintype L] [DecidableEq L] [Fintype R] in
/-- **The context a frame's own choices were made in respects the graph, stays injective, and
leaves its own `l` unmatched** — exactly the hypotheses `GoodResult`-style lemmas need. -/
lemma stackWF_context (adj : L → R → Prop) [DecidableRel adj] {μ₀ : R → Option L}
    {visited₀ : Finset R} {l₀ : L} (hRes : Respects adj μ₀) (hInj : InjOnSupport μ₀)
    (hUnm : ¬ Matched μ₀ l₀) :
    ∀ (f : Frame L R) (below : List (Frame L R)), StackWF adj μ₀ visited₀ l₀ (f :: below) →
      Respects adj (belowMatching μ₀ below) ∧ InjOnSupport (belowMatching μ₀ below) ∧
        ¬ Matched (belowMatching μ₀ below) f.l
  | f, [], hwf => by
      obtain ⟨hfl, -⟩ := hwf
      subst hfl
      exact ⟨hRes, hInj, hUnm⟩
  | f, f2 :: rest, hwf => by
      obtain ⟨hwf', hocc, -⟩ := hwf
      obtain ⟨hRes2, hInj2, hUnm2⟩ := stackWF_context adj hRes hInj hUnm f2 rest hwf'
      refine ⟨respects_update_none adj hRes2 f2.r, injOnSupport_update_none hInj2 f2.r, ?_⟩
      rintro ⟨r₀, h0⟩
      simp only [belowMatching] at h0
      by_cases hr0 : r₀ = f2.r
      · rw [hr0, Function.update_self] at h0; cases h0
      · rw [Function.update_of_ne hr0] at h0
        exact hr0 (hInj2 r₀ f2.r f.l h0 hocc)

/-- Apply every frame's `(r, l)` choice, left to right, as an update onto `μ`. -/
abbrev fold (μ : R → Option L) (frames : List (Frame L R)) : R → Option L :=
  frames.foldl (fun μ' fr => Function.update μ' fr.r (some fr.l)) μ

omit [Fintype L] [DecidableEq L] [Fintype R] in
/-- **Every frame in a well-formed stack differs from every other's `r`.** -/
lemma below_pairwise (adj : L → R → Prop) [DecidableRel adj] {μ₀ : R → Option L}
    {visited₀ : Finset R} {l₀ : L} :
    ∀ (below : List (Frame L R)), StackWF adj μ₀ visited₀ l₀ below →
      below.Pairwise (fun a b => a.r ≠ b.r)
  | [], hwf => hwf.elim
  | [_], _ => List.pairwise_singleton _ _
  | f :: f2 :: rest, hwf =>
      List.pairwise_cons.mpr
        ⟨fun f' hf' => (frame_pairwise_ne adj f (f2 :: rest) hwf f' hf').symm,
          below_pairwise adj (f2 :: rest) hwf.1⟩

omit [Fintype L] [DecidableEq L] [Fintype R] in
/-- **An update at a key none of `below`'s frames use commutes past folding `below` in.** -/
lemma fold_update_comm (below : List (Frame L R)) (μ : R → Option L) (r0 : R) (v : Option L)
    (hr0 : ∀ f' ∈ below, f'.r ≠ r0) :
    fold (Function.update μ r0 v) below = Function.update (fold μ below) r0 v := by
  induction below generalizing μ with
  | nil => rfl
  | cons f2 rest ih =>
      have hne : r0 ≠ f2.r := fun h => hr0 f2 List.mem_cons_self h.symm
      have hrest : ∀ f' ∈ rest, f'.r ≠ r0 := fun f' hf' => hr0 f' (List.mem_cons_of_mem f2 hf')
      show fold (Function.update (Function.update μ r0 v) f2.r (some f2.l)) rest =
        Function.update (fold (Function.update μ f2.r (some f2.l)) rest) r0 v
      rw [Function.update_comm hne, ih (Function.update μ f2.r (some f2.l)) hrest]

omit [Fintype L] [DecidableEq L] [Fintype R] in
/-- **Folding `below` in starting from its own reconstructed context matching lands in the same
place as folding it in from scratch**: the fold re-sets exactly the keys the context cleared. -/
lemma fold_belowMatching_eq (μ₀ : R → Option L) :
    ∀ (below : List (Frame L R)), below.Pairwise (fun a b => a.r ≠ b.r) →
      fold (belowMatching μ₀ below) below = fold μ₀ below
  | [], _ => rfl
  | f2 :: rest, hpw => by
      have hrest_pw : rest.Pairwise (fun a b => a.r ≠ b.r) := (List.pairwise_cons.mp hpw).2
      have hfresh : ∀ f' ∈ rest, f'.r ≠ f2.r := fun f' hf' =>
        ((List.pairwise_cons.mp hpw).1 f' hf').symm
      show fold
          (Function.update (Function.update (belowMatching μ₀ rest) f2.r none) f2.r (some f2.l)) rest =
        fold (Function.update μ₀ f2.r (some f2.l)) rest
      rw [Function.update_idem, fold_update_comm rest (belowMatching μ₀ rest) f2.r (some f2.l) hfresh,
        fold_belowMatching_eq μ₀ rest hrest_pw,
        ← fold_update_comm rest μ₀ f2.r (some f2.l) hfresh]

omit [Fintype L] [DecidableEq L] [Fintype R] in
/-- **Propagation**: a good result at the top frame's own level, folded down through every frame
below it, is a good result for the whole search's original `l₀`. This is `goodResult_displaced`
applied once per frame below the top, from the top down to the bottom. -/
theorem propagate (adj : L → R → Prop) [DecidableRel adj] {μ₀ : R → Option L}
    {visited₀ : Finset R} {l₀ : L} (hRes : Respects adj μ₀) (hInj : InjOnSupport μ₀)
    (hUnm : ¬ Matched μ₀ l₀) :
    ∀ (f : Frame L R) (below : List (Frame L R)), StackWF adj μ₀ visited₀ l₀ (f :: below) →
      ∀ (topResult : R → Option L),
        GoodResult adj (belowMatching μ₀ below) (belowVisited visited₀ below) f.l topResult →
        GoodResult adj μ₀ visited₀ l₀ (fold topResult below)
  | f, [], hwf, topResult, hgood => by
      have hfl : f.l = l₀ := hwf.1
      show GoodResult adj μ₀ visited₀ l₀ topResult
      rw [← hfl]; exact hgood
  | f, f2 :: rest, hwf, topResult, hgood => by
      have hwf' : StackWF adj μ₀ visited₀ l₀ (f2 :: rest) := hwf.1
      have hocc : belowMatching μ₀ rest f2.r = some f.l := hwf.2.1
      obtain ⟨hRes2, hInj2, hUnm2⟩ := stackWF_context adj hRes hInj hUnm f2 rest hwf'
      obtain ⟨hadj_f2, hvis_f2⟩ := frame_adj_and_fresh adj f2 rest hwf'
      have hgood2 : GoodResult adj (belowMatching μ₀ rest) (belowVisited visited₀ rest) f2.l
          (Function.update topResult f2.r (some f2.l)) :=
        goodResult_displaced adj hUnm2 hadj_f2 hocc hvis_f2 hgood
      show GoodResult adj μ₀ visited₀ l₀ (fold (Function.update topResult f2.r (some f2.l)) rest)
      exact propagate adj hRes hInj hUnm f2 rest hwf'
        (Function.update topResult f2.r (some f2.l)) hgood2

omit [Fintype L] [DecidableEq L] [Fintype R] in
/-- **A well-formed stack whose top frame's current candidate is free collapses to a good
result** for the whole search's original `l₀`: build the fresh match at the top
(`goodResult_fresh`), then fold it down through the rest of the stack (`propagate`). -/
theorem collapse_free (adj : L → R → Prop) [DecidableRel adj] {μ₀ : R → Option L}
    {visited₀ : Finset R} {l₀ : L} (hRes : Respects adj μ₀) (hInj : InjOnSupport μ₀)
    (hUnm : ¬ Matched μ₀ l₀) :
    ∀ (f : Frame L R) (below : List (Frame L R)), StackWF adj μ₀ visited₀ l₀ (f :: below) →
      belowMatching μ₀ below f.r = none →
      GoodResult adj μ₀ visited₀ l₀ (fold μ₀ (f :: below))
  | f, [], hwf, hfree => by
      have hfl : f.l = l₀ := hwf.1
      have hadj : adj f.l f.r := (hwf.2 _ List.mem_cons_self).1
      have hvis : f.r ∉ visited₀ := (hwf.2 _ List.mem_cons_self).2
      have hUnmfl : ¬ Matched μ₀ f.l := by rw [hfl]; exact hUnm
      show GoodResult adj μ₀ visited₀ l₀ (Function.update μ₀ f.r (some f.l))
      rw [← hfl]
      exact goodResult_fresh adj hRes hInj hUnmfl hfree hadj hvis
  | f, f2 :: rest, hwf, hfree => by
      have hbelowWF : StackWF adj μ₀ visited₀ l₀ (f2 :: rest) := hwf.1
      obtain ⟨hRes', hInj', hUnm'⟩ := stackWF_context adj hRes hInj hUnm f (f2 :: rest) hwf
      obtain ⟨hadj, hvis⟩ := frame_adj_and_fresh adj f (f2 :: rest) hwf
      have hgoodtop : GoodResult adj (belowMatching μ₀ (f2 :: rest))
          (belowVisited visited₀ (f2 :: rest)) f.l
          (Function.update (belowMatching μ₀ (f2 :: rest)) f.r (some f.l)) :=
        goodResult_fresh adj hRes' hInj' hUnm' hfree hadj hvis
      have hprop := propagate adj hRes hInj hUnm f (f2 :: rest) hwf
        (Function.update (belowMatching μ₀ (f2 :: rest)) f.r (some f.l)) hgoodtop
      have hpw : (f2 :: rest).Pairwise (fun a b => a.r ≠ b.r) := below_pairwise adj (f2 :: rest) hbelowWF
      have hfresh : ∀ f' ∈ (f2 :: rest), f'.r ≠ f.r := fun f' hf' hf'r =>
        hvis (hf'r ▸ mem_belowVisited visited₀ (f2 :: rest) hf')
      have heq : fold (Function.update (belowMatching μ₀ (f2 :: rest)) f.r (some f.l)) (f2 :: rest) =
          fold (Function.update μ₀ f.r (some f.l)) (f2 :: rest) := by
        rw [fold_update_comm (f2 :: rest) (belowMatching μ₀ (f2 :: rest)) f.r (some f.l) hfresh,
          fold_belowMatching_eq μ₀ (f2 :: rest) hpw,
          fold_update_comm (f2 :: rest) μ₀ f.r (some f.l) hfresh]
      show GoodResult adj μ₀ visited₀ l₀ (fold (Function.update μ₀ f.r (some f.l)) (f2 :: rest))
      rw [← heq]
      exact hprop

omit [Fintype L] [DecidableEq L] [Fintype R] in
/-- **Clearing only keys outside `below`'s own choices is a no-op.** -/
lemma belowMatching_eq_of_notMem (μ₀ : R → Option L) (r0 : R) :
    ∀ (below : List (Frame L R)), (∀ f' ∈ below, f'.r ≠ r0) →
      belowMatching μ₀ below r0 = μ₀ r0
  | [], _ => rfl
  | f :: rest, h => by
      have hne : f.r ≠ r0 := h f List.mem_cons_self
      have hrest : ∀ f' ∈ rest, f'.r ≠ r0 := fun f' hf' => h f' (List.mem_cons_of_mem f hf')
      show Function.update (belowMatching μ₀ rest) f.r none r0 = μ₀ r0
      rw [Function.update_of_ne hne.symm, belowMatching_eq_of_notMem μ₀ r0 rest hrest]

end Lax117284Proofs.Bipartite.StackSearchCorrect
