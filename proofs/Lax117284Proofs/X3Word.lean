import Lax117284Proofs.ExtremeFairness
import Lax117284Proofs.Tractable
import Lax117284Proofs.WordCorrect
import Lax117284Proofs.Injectivity
import Lax117284Proofs.SourceInjectivity
import Lax117284.Theorem3
import Lax117284.Theorem13
import Lax117284.TwoSatisfiability

/-!
Day-independent due dates and processing times, as a count: the clique number of a day's conflict
graph is the largest number of jobs that run at the instant one of them starts.
-/

namespace Lax117284Proofs.X3Word

open Lax117284.Scheduling Lax117284.ConflictGraph

/-- The instant a job starts. -/
def startAt (I : Instance) (i j : ℕ) : ℕ := I.dAt i j - I.pAt i j

/-- The job of client `j'` is running at the instant the job of client `j` starts. -/
def RunsAt (I : Instance) (i j j' : ℕ) : Prop :=
  startAt I i j' ≤ startAt I i j ∧ startAt I i j < I.dAt i j'

instance (I : Instance) (i j j' : ℕ) : Decidable (RunsAt I i j j') := by
  unfold RunsAt; infer_instance

/-- The number of jobs that run at the instant the job of client `j` starts. -/
def depthAt (I : Instance) (i j : ℕ) : ℕ :=
  (List.range I.clients).countP fun j' => decide (RunsAt I i j j')

/-- The largest depth. -/
def omegaT (I : Instance) (i : ℕ) : ℕ :=
  (List.range I.clients).foldl (fun a j => max a (depthAt I i j)) 0

lemma foldl_max_ge {f : ℕ → ℕ} : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl (fun a j => max a (f j)) a
  | [], a => le_rfl
  | x :: l, a => le_trans (le_max_left _ _) (foldl_max_ge l _)

lemma le_foldl_max {f : ℕ → ℕ} : ∀ (l : List ℕ) (a x : ℕ), x ∈ l →
    f x ≤ l.foldl (fun a j => max a (f j)) a
  | [], a, x, h => absurd h (by simp)
  | y :: l, a, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (le_max_right _ _) (foldl_max_ge l _)
    · exact le_foldl_max l _ x h

lemma foldl_max_le {f : ℕ → ℕ} {c : ℕ} : ∀ (l : List ℕ) (a : ℕ), a ≤ c → (∀ x ∈ l, f x ≤ c) →
    l.foldl (fun a j => max a (f j)) a ≤ c
  | [], a, ha, _ => ha
  | x :: l, a, ha, h => foldl_max_le l _ (max_le ha (h x (by simp))) (fun y hy => h y (by simp [hy]))

lemma countP_range_eq_sum (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    (List.range n).countP (fun x => decide (p x)) = ∑ i ∈ Finset.range n, if p i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, Finset.sum_range_succ]
    simp

lemma countP_range_eq_card (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    (List.range n).countP (fun x => decide (p x)) =
      (Finset.univ.filter (fun x : Fin n => p x)).card := by
  rw [countP_range_eq_sum, Finset.card_filter, ← Fin.sum_univ_eq_sum_range (fun i => if p i then 1 else 0)]

lemma startAt_lt_dAt (I : Instance) (i j : ℕ) : startAt I i j < I.dAt i j := by
  have h1 := I.pAt_pos i j
  have h2 := I.pAt_le_dAt i j
  unfold startAt; omega

/-- The clients whose jobs run at the instant the job of client `j` starts. -/
def runners (I : Instance) (i : ℕ) (j : ℕ) : Finset (Fin I.clients) :=
  Finset.univ.filter fun j' => RunsAt I i j j'

lemma depthAt_eq_card (I : Instance) (i j : ℕ) : depthAt I i j = (runners I i j).card :=
  countP_range_eq_card (fun j' => RunsAt I i j j') I.clients

lemma conflictAt_iff_start (I : Instance) (i : ℕ) (a b : ℕ) :
    I.ConflictAt i a b ↔ startAt I i a < I.dAt i b ∧ startAt I i b < I.dAt i a := Iff.rfl

lemma runners_isClique (I : Instance) (i : Fin I.days) (j : Fin I.clients) :
    (dayGraph I i).IsClique (↑(runners I i j) : Set (Fin I.clients)) := by
  intro a ha b hb hab
  simp only [runners, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
  refine ⟨hab, (Instance.conflictAt_iff (I := I) i a b).1 ?_⟩
  rw [conflictAt_iff_start]
  exact ⟨lt_of_le_of_lt ha.1 hb.2, lt_of_le_of_lt hb.1 ha.2⟩

theorem cliqueNum_eq (I : Instance) (i : Fin I.days) :
    (dayGraph I i).cliqueNum = omegaT I i := by
  classical
  apply le_antisymm
  · obtain ⟨K, hK⟩ := (dayGraph I i).exists_isNClique_cliqueNum
    rcases K.eq_empty_or_nonempty with hne | hne
    · rw [← hK.card_eq, hne]; simp
    · obtain ⟨j, hjK, hmax⟩ := Finset.exists_max_image K (fun j : Fin I.clients => startAt I i j) hne
      have hsub : K ⊆ runners I i j := by
        intro j' hj'
        simp only [runners, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hmax j' hj', ?_⟩
        by_cases he : j' = j
        · subst he; exact startAt_lt_dAt I i j'
        · have hadj := hK.isClique hjK hj' (Ne.symm he)
          have := (Instance.conflictAt_iff (I := I) i j j').2 hadj.2
          rw [conflictAt_iff_start] at this
          exact this.1
      calc (dayGraph I i).cliqueNum = K.card := hK.card_eq.symm
        _ ≤ (runners I i j).card := Finset.card_le_card hsub
        _ = depthAt I i j := (depthAt_eq_card I i j).symm
        _ ≤ omegaT I i := le_foldl_max (f := fun j => depthAt I i j) (List.range I.clients) 0 j
            (List.mem_range.2 j.isLt)
  · unfold omegaT
    refine foldl_max_le (f := fun j => depthAt I i j) _ 0 (Nat.zero_le _) fun j hj => ?_
    have hj' := List.mem_range.1 hj
    rw [depthAt_eq_card]
    have := (runners_isClique I i ⟨j, hj'⟩).card_le_cliqueNum
    simpa [runners] using this

/-- The number the fairness parameter is multiplied by: the largest depth, and the number of
clients when there is no day. -/
def omegaD (I : Instance) : ℕ := if I.days = 0 then I.clients else omegaT I 0

/-- **With day-independent data, a fair schedule exists exactly when `k` times the largest depth
is at most the number of days.** -/
theorem hasKFair_iff_omegaD {I : Instance} (hd : I.DayIndepD) (hp : I.DayIndepP) (k : ℕ) :
    I.HasKFairSchedule k ↔ k * omegaD I ≤ I.days := by
  by_cases h0 : I.days = 0
  · unfold omegaD
    rw [if_pos h0, h0]
    constructor
    · intro hk
      by_contra hne
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; simp at hne
        · exact h
      have hc : 0 < I.clients := by
        rcases Nat.eq_zero_or_pos I.clients with h | h
        · rw [h] at hne; simp at hne
        · exact h
      exact ExtremeFairness.not_hasKFairSchedule_of_days_lt (by omega) hc hk
    · intro h
      rcases Nat.mul_eq_zero.1 (Nat.le_zero.1 h) with h | h
      · subst h; exact ExtremeFairness.hasKFairSchedule_zero I
      · exact WordCorrect.hasKFair_of_clients_zero I h k
  · unfold omegaD
    rw [if_neg h0]
    have hpos : 0 < I.days := Nat.pos_of_ne_zero h0
    rw [Tractable.hasKFairSchedule_iff_mul_cliqueNum_le hd hp ⟨0, hpos⟩ k]
    rw [cliqueNum_eq I ⟨0, hpos⟩]

end Lax117284Proofs.X3Word
