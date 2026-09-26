import Lax117284.JustInTime
import Lax496464.HittingSet
import Mathlib.Tactic

/-!
# From Hitting Set to just-in-time scheduling on unrelated machines

An instance of Hitting Set with universe `n`, `m` sets and required size `k ≤ n` becomes an
instance of `R || ∑ Z_j` with `n` machines, one per element, and three kinds of jobs.

* `n` *guards*, due at `1` with processing time `1` on every machine: two guards overlap on
  a machine, so every machine holds exactly one guard, occupying `(0, 1]`.
* One *set job* per set `s`, due at `2 + s`; its processing time is `1` on the machines of
  the set, where it occupies `(1 + s, 2 + s]`, and `2 + s` elsewhere, where it would occupy
  `(0, 2 + s]` and collide with the guard.
* `n - k` *fillers*, due at `m + 2` with processing time `m + 1`, occupying `(1, m + 2]`:
  fillers collide with each other and with every set job, so they block `n - k` machines
  and the set jobs live on at most `k` machines, which hit every set.
-/

namespace Lax117284Proofs.FromHittingSet

open Lax117284.JustInTime Lax496464.HittingSet

variable (P : Lax496464.HittingSet.Instance) (k : ℕ)

/-- The number of jobs: `n` guards, `m` set jobs, `n - k` fillers. -/
def jobs : ℕ := P.n + P.m + (P.n - k)

/-- Machine `i` is eligible for set `s`. -/
def Elig (i s : ℕ) : Prop := ∃ (hi : i < P.n) (hs : s < P.m), (⟨i, hi⟩ : Fin P.n) ∈ P.F ⟨s, hs⟩

instance (i s : ℕ) : Decidable (Elig P i s) := by unfold Elig; infer_instance

/-- The due date of job `j`. -/
def due (j : ℕ) : ℕ :=
  if j < P.n then 1 else if j < P.n + P.m then 2 + (j - P.n) else P.m + 2

/-- The processing time of job `j` on machine `i`. -/
def proc (i j : ℕ) : ℕ :=
  if j < P.n then 1
  else if j < P.n + P.m then (if Elig P i (j - P.n) then 1 else 2 + (j - P.n))
  else P.m + 1

/-- The instance of `R || ∑ Z_j`. -/
def R : Lax117284.JustInTime.Instance where
  jobs := jobs P k
  machines := P.n
  p := fun i j => proc P i j
  d := fun j => due P j
  p_pos := fun _ j => by unfold proc; split_ifs <;> omega
  p_le_d := fun _ j => by unfold proc due; split_ifs <;> omega

/-! ### The three kinds of jobs -/

def guardIdx (a : Fin P.n) : Fin (jobs P k) := ⟨a, by unfold jobs; omega⟩
def setIdx (s : Fin P.m) : Fin (jobs P k) := ⟨P.n + s, by unfold jobs; omega⟩
def fillIdx (t : Fin (P.n - k)) : Fin (jobs P k) := ⟨P.n + P.m + t, by unfold jobs; omega⟩

theorem kinds (j : Fin (jobs P k)) :
    (∃ a, j = guardIdx P k a) ∨ (∃ s, j = setIdx P k s) ∨ ∃ t, j = fillIdx P k t := by
  obtain ⟨j, hj⟩ := j
  unfold jobs at hj
  by_cases h1 : j < P.n
  · exact Or.inl ⟨⟨j, h1⟩, rfl⟩
  by_cases h2 : j < P.n + P.m
  · exact Or.inr (Or.inl ⟨⟨j - P.n, by omega⟩, Fin.ext (by simp [setIdx]; omega)⟩)
  · exact Or.inr (Or.inr ⟨⟨j - (P.n + P.m), by omega⟩, Fin.ext (by simp [fillIdx]; omega)⟩)

/-- Overlap, unfolded: a common time point of the two intervals. -/
theorem overlap_iff (i : Fin P.n) (j j' : Fin (jobs P k)) :
    (R P k).Overlap i j j' ↔
      ∃ t, (due P j - proc P i j < t ∧ t ≤ due P j) ∧ (due P j' - proc P i j' < t ∧ t ≤ due P j') := by
  unfold Instance.Overlap Instance.job
  simp only [Set.Nonempty, Set.mem_inter_iff, Set.mem_Ioc]
  rfl

theorem due_guard (a : Fin P.n) : due P (guardIdx P k a) = 1 := by simp [due, guardIdx]
theorem proc_guard (i : ℕ) (a : Fin P.n) : proc P i (guardIdx P k a) = 1 := by
  simp [proc, guardIdx]
theorem due_set (s : Fin P.m) : due P (setIdx P k s) = 2 + (s : ℕ) := by
  simp [due, setIdx]
theorem proc_set (i : ℕ) (s : Fin P.m) :
    proc P i (setIdx P k s) = if Elig P i s then 1 else 2 + (s : ℕ) := by
  simp [proc, setIdx]
theorem due_fill (t : Fin (P.n - k)) : due P (fillIdx P k t) = P.m + 2 := by
  simp [due, fillIdx] <;> omega
theorem proc_fill (i : ℕ) (t : Fin (P.n - k)) : proc P i (fillIdx P k t) = P.m + 1 := by
  simp [proc, fillIdx] <;> omega

theorem elig_iff (i : Fin P.n) (s : Fin P.m) : Elig P i s ↔ i ∈ P.F s := by
  unfold Elig
  constructor
  · rintro ⟨hi, hs, h⟩; exact h
  · intro h; exact ⟨i.isLt, s.isLt, h⟩

/-! ### Which pairs overlap -/

theorem ov_guard_guard (i : Fin P.n) (a b : Fin P.n) :
    (R P k).Overlap i (guardIdx P k a) (guardIdx P k b) := by
  rw [overlap_iff]; exact ⟨1, by simp [due_guard, proc_guard], by simp [due_guard, proc_guard]⟩

theorem nov_guard_set (i : Fin P.n) (a : Fin P.n) (s : Fin P.m)
    (h : Elig P i s) : ¬ (R P k).Overlap i (guardIdx P k a) (setIdx P k s) := by
  rw [overlap_iff, due_guard, proc_guard, due_set, proc_set, if_pos h]
  rintro ⟨t, h1, h2⟩; omega

theorem ov_guard_set (i : Fin P.n) (a : Fin P.n) (s : Fin P.m)
    (h : ¬ Elig P i s) : (R P k).Overlap i (guardIdx P k a) (setIdx P k s) := by
  rw [overlap_iff, due_guard, proc_guard, due_set, proc_set, if_neg h]
  exact ⟨1, by omega, by omega⟩

theorem nov_guard_fill (i : Fin P.n) (a : Fin P.n) (t : Fin (P.n - k)) :
    ¬ (R P k).Overlap i (guardIdx P k a) (fillIdx P k t) := by
  rw [overlap_iff, due_guard, proc_guard, due_fill, proc_fill]
  rintro ⟨x, h1, h2⟩; omega

theorem nov_set_set (i : Fin P.n) (s s' : Fin P.m) (hne : s ≠ s')
    (h : Elig P i s) (h' : Elig P i s') : ¬ (R P k).Overlap i (setIdx P k s) (setIdx P k s') := by
  rw [overlap_iff, due_set, proc_set, if_pos h, due_set, proc_set, if_pos h']
  rintro ⟨t, h1, h2⟩
  exact hne (Fin.ext (by omega))

theorem ov_set_fill (i : Fin P.n) (s : Fin P.m) (t : Fin (P.n - k))
    (h : Elig P i s) : (R P k).Overlap i (setIdx P k s) (fillIdx P k t) := by
  rw [overlap_iff, due_set, proc_set, if_pos h, due_fill, proc_fill]
  exact ⟨2 + s, by omega, by have := s.isLt; omega⟩

theorem ov_fill_fill (i : Fin P.n) (t t' : Fin (P.n - k)) :
    (R P k).Overlap i (fillIdx P k t) (fillIdx P k t') := by
  rw [overlap_iff, due_fill, proc_fill, due_fill, proc_fill]
  exact ⟨P.m + 2, by omega, by omega⟩

theorem overlap_symm {i : Fin P.n} {j j' : Fin (jobs P k)}
    (h : (R P k).Overlap i j j') : (R P k).Overlap i j' j := by
  rw [overlap_iff] at h ⊢; obtain ⟨t, h1, h2⟩ := h; exact ⟨t, h2, h1⟩

theorem guardIdx_ne_setIdx (a : Fin P.n) (s : Fin P.m) : guardIdx P k a ≠ setIdx P k s := by
  intro h; have := Fin.mk.inj_iff.mp h; have := a.isLt; omega
theorem guardIdx_ne_fillIdx (a : Fin P.n) (t : Fin (P.n - k)) : guardIdx P k a ≠ fillIdx P k t := by
  intro h; have := Fin.mk.inj_iff.mp h; have := a.isLt; omega
theorem setIdx_ne_fillIdx (s : Fin P.m) (t : Fin (P.n - k)) : setIdx P k s ≠ fillIdx P k t := by
  intro h; have := Fin.mk.inj_iff.mp h; have := s.isLt; omega
theorem guardIdx_inj {a b : Fin P.n} (h : guardIdx P k a = guardIdx P k b) : a = b :=
  Fin.ext (Fin.mk.inj_iff.mp h)
theorem setIdx_inj {s s' : Fin P.m} (h : setIdx P k s = setIdx P k s') : s = s' :=
  Fin.ext (by have := Fin.mk.inj_iff.mp h; omega)
theorem fillIdx_inj {t t' : Fin (P.n - k)} (h : fillIdx P k t = fillIdx P k t') : t = t' :=
  Fin.ext (by have := Fin.mk.inj_iff.mp h; omega)

/-! ### From a hitting set to a schedule -/

section Forward

variable {P k} (H : Finset (Fin P.n)) (ch : Fin P.m → Fin P.n)
  (hch : ∀ s, ch s ∈ H ∧ ch s ∈ P.F s)
  (e : Fin (P.n - k) → Fin P.n) (he : Function.Injective e) (heH : ∀ t, e t ∉ H)

/-- The assignment: guards to their own machine, set jobs to the chosen element `ch s` of
their set in `H`, fillers along `e`. -/
def assign : Fin (jobs P k) → Fin P.n := fun j =>
  if hg : (j : ℕ) < P.n then ⟨j, hg⟩
  else if hs : (j : ℕ) < P.n + P.m then ch ⟨j - P.n, by omega⟩
  else e ⟨j - (P.n + P.m), by have := j.isLt; unfold jobs at this; omega⟩

theorem assign_guard (a : Fin P.n) : assign ch e (guardIdx P k a) = a := by
  simp [assign, guardIdx]

theorem assign_set (s : Fin P.m) : assign ch e (setIdx P k s) = ch s := by
  have h1 : ¬ ((setIdx P k s : ℕ) < P.n) := by simp only [setIdx]; omega
  have h2 : (setIdx P k s : ℕ) < P.n + P.m := by simp only [setIdx]; omega
  simp only [assign, h1, ↓reduceDIte, h2]
  congr 1
  apply Fin.ext; simp only [setIdx]; omega

theorem assign_fill (t : Fin (P.n - k)) : assign ch e (fillIdx P k t) = e t := by
  have h1 : ¬ ((fillIdx P k t : ℕ) < P.n) := by simp only [fillIdx]; omega
  have h2 : ¬ ((fillIdx P k t : ℕ) < P.n + P.m) := by simp only [fillIdx]; omega
  simp only [assign, h1, ↓reduceDIte, h2]
  congr 1
  apply Fin.ext; simp only [fillIdx]; omega

include hch in
theorem assign_set_mem (s : Fin P.m) : assign ch e (setIdx P k s) ∈ H := by
  rw [assign_set]; exact (hch s).1
include hch in
theorem assign_set_elig (s : Fin P.m) : Elig P (assign ch e (setIdx P k s)) s := by
  rw [elig_iff, assign_set]; exact (hch s).2

include hch he heH in
/-- The schedule is just in time. -/
theorem allJIT_of_hittingSet : (R P k).AllJustInTime := by
  refine ⟨assign ch e, fun j j' hne heq => ?_⟩
  rcases kinds P k j with ⟨a, rfl⟩ | ⟨s, rfl⟩ | ⟨t, rfl⟩ <;>
    rcases kinds P k j' with ⟨b, rfl⟩ | ⟨s', rfl⟩ | ⟨t', rfl⟩
  · exact absurd (congrArg (guardIdx P k) (by rwa [assign_guard, assign_guard] at heq)) hne
  · refine nov_guard_set P k _ a s' ?_
    have := assign_set_elig H ch hch e s'; rwa [← heq] at this
  · exact nov_guard_fill P k _ a t'
  · exact fun h => nov_guard_set P k _ b s (assign_set_elig H ch hch e s) (overlap_symm P k h)
  · refine nov_set_set P k _ s s' (fun h => hne (by rw [h])) ?_ ?_
    · exact assign_set_elig H ch hch e s
    · have := assign_set_elig H ch hch e s'; rwa [← heq] at this
  · exfalso
    have h1 := assign_set_mem H ch hch e s
    rw [heq, assign_fill] at h1
    exact heH t' h1
  · exact fun h => nov_guard_fill P k _ b t (overlap_symm P k h)
  · exfalso
    have h1 := assign_set_mem H ch hch e s'
    rw [← heq, assign_fill] at h1
    exact heH t h1
  · rw [assign_fill, assign_fill] at heq
    exact absurd (congrArg (fillIdx P k) (he heq)) hne

end Forward

/-! ### From a schedule to a hitting set -/

section Backward

variable {P k} (f : Fin (jobs P k) → Fin P.n)
  (hf : ∀ j j', j ≠ j' → f j = f j' → ¬ (R P k).Overlap (f j) j j')

include hf in
theorem guard_inj : Function.Injective fun a => f (guardIdx P k a) := by
  intro a b h
  by_contra hne
  exact hf _ _ (fun h' => hne (guardIdx_inj P k h')) h (ov_guard_guard P k _ a b)

include hf in
theorem set_elig (s : Fin P.m) : Elig P (f (setIdx P k s)) s := by
  obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.mp (guard_inj f hf)) (f (setIdx P k s))
  by_contra h
  exact hf _ _ (guardIdx_ne_setIdx P k a s) (by simpa using ha)
    (by rw [show f (guardIdx P k a) = f (setIdx P k s) from ha]; exact ov_guard_set P k _ a s h)

include hf in
theorem fill_inj : Function.Injective fun t => f (fillIdx P k t) := by
  intro t t' h
  by_contra hne
  exact hf _ _ (fun h' => hne (fillIdx_inj P k h')) h (ov_fill_fill P k _ t t')

include hf in
theorem set_ne_fill (s : Fin P.m) (t : Fin (P.n - k)) : f (setIdx P k s) ≠ f (fillIdx P k t) :=
  fun h => hf _ _ (setIdx_ne_fillIdx P k s t) h (ov_set_fill P k _ s t (set_elig f hf s))

include hf in
theorem hittingSet_of_allJIT (hk : k ≤ P.n) : P.HasHittingSet k := by
  classical
  let MS : Finset (Fin P.n) := Finset.univ.image fun s => f (setIdx P k s)
  let MF : Finset (Fin P.n) := Finset.univ.image fun t => f (fillIdx P k t)
  have hMF : MF.card = P.n - k := by
    rw [Finset.card_image_of_injective _ (fill_inj f hf), Finset.card_univ, Fintype.card_fin]
  have hdisj : Disjoint MS MF := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, -, h⟩ := Finset.mem_image.mp hx'
    exact set_ne_fill f hf s t h.symm
  have hcard : MS.card + (P.n - k) ≤ P.n := by
    rw [← hMF, ← Finset.card_union_of_disjoint hdisj]
    exact le_trans (Finset.card_le_univ _) (by rw [Fintype.card_fin])
  have hMSk : MS.card ≤ k := by omega
  obtain ⟨C, hMC, -, hC⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ MS) hMSk
    (by rw [Finset.card_univ, Fintype.card_fin]; exact hk)
  refine ⟨C, hC, fun s => ⟨f (setIdx P k s), hMC (Finset.mem_image_of_mem _ (Finset.mem_univ s)), ?_⟩⟩
  exact (elig_iff P _ s).mp (set_elig f hf s)

end Backward

/-- **The reduction is correct**: for `k ≤ n`, the Hitting Set instance has a hitting set of
size `k` exactly when every job of the shop can be just in time. -/
theorem correct (hk : k ≤ P.n) : P.HasHittingSet k ↔ (R P k).AllJustInTime := by
  classical
  constructor
  · rintro ⟨H, hcard, hH⟩
    have hcc : Hᶜ.card = P.n - k := by rw [Finset.card_compl, Fintype.card_fin, hcard]
    let e : Fin (P.n - k) → Fin P.n := fun t => (Hᶜ.equivFin.symm (Fin.cast hcc.symm t)).1
    have he : Function.Injective e := fun t t' h => by
      have := Hᶜ.equivFin.symm.injective (Subtype.ext h)
      exact Fin.ext (by simpa using congrArg Fin.val this)
    have heH : ∀ t, e t ∉ H := fun t =>
      Finset.mem_compl.mp (Hᶜ.equivFin.symm (Fin.cast hcc.symm t)).2
    choose ch hch using hH
    exact allJIT_of_hittingSet H ch hch e he heH
  · rintro ⟨f, hf⟩
    exact hittingSet_of_allJIT f hf hk

end Lax117284Proofs.FromHittingSet
