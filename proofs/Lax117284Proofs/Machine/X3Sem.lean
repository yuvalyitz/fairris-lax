import Lax117284Proofs.Machine.InstSem
import Lax117284Proofs.Machine.X1Sem
import Lax117284Proofs.X3Word
import Lax117284Proofs.X1Word

/-!
Day-independent due dates and processing times, on the numbers of a stream: the table is the same
on every day, and the parameter times the largest depth of the first day is at most the number of
days.
-/

namespace Lax117284Proofs.Machine.X3Sem

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime Lax117284.TwoSatisfiability
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.X3Word
open Lax117284Proofs.X1Word (satF twoSat_mem_encode satF_satisfiable)

/-- The instant the job of client `j` of the first day starts. -/
def sRow (ns : List ℕ) (j : ℕ) : ℕ := ns.getD (3 + 2 * j) 0 - ns.getD (2 + 2 * j) 0

/-- The number of jobs of the first day that run at the instant the job of client `j` starts. -/
def cntN (ns : List ℕ) (j : ℕ) : ℕ :=
  (List.range (ns.getD 0 0)).countP fun j' =>
    decide (sRow ns j' ≤ sRow ns j ∧ sRow ns j < ns.getD (3 + 2 * j') 0)

/-- The largest such number. -/
def omegaN (ns : List ℕ) : ℕ :=
  (List.range (ns.getD 0 0)).foldl (fun a j => max a (cntN ns j)) 0

/-- Every cell of the table equals the cell of its client on the first day. -/
def DI (ns : List ℕ) : Prop :=
  ∀ t < ns.getD 1 0 * ns.getD 0 0,
    ns.getD (2 + 2 * t) 0 = ns.getD (2 + 2 * (t % ns.getD 0 0)) 0 ∧
    ns.getD (2 + 2 * t + 1) 0 = ns.getD (2 + 2 * (t % ns.getD 0 0) + 1) 0

/-- The number the parameter is multiplied by. -/
def omegaS (ns : List ℕ) : ℕ := if ns.getD 1 0 = 0 then ns.getD 0 0 else omegaN ns

/-- The streams that are mapped to the satisfiable formula. -/
def goodD (ns : List ℕ) : Prop :=
  Valid ns ∧ DI ns ∧ paramOf ns * omegaS ns ≤ ns.getD 1 0

lemma foldl_max_congr {f g : ℕ → ℕ} : ∀ (l : List ℕ) (a : ℕ), (∀ x ∈ l, f x = g x) →
    l.foldl (fun a j => max a (f j)) a = l.foldl (fun a j => max a (g j)) a
  | [], a, _ => rfl
  | x :: l, a, h => by
    simp only [List.foldl_cons]
    rw [h x (by simp)]
    exact foldl_max_congr l _ (fun y hy => h y (by simp [hy]))

section Link

variable (ns : List ℕ) (hv : Valid ns)

lemma inst_row (hm : 0 < ns.getD 1 0) {j : ℕ} (hj : j < ns.getD 0 0) :
    (instOf ns hv).pAt 0 j = ns.getD (2 + 2 * j) 0 ∧
    (instOf ns hv).dAt 0 j = ns.getD (3 + 2 * j) 0 := by
  have hlt : j < ns.getD 1 0 * ns.getD 0 0 := lt_of_lt_of_le hj (Nat.le_mul_of_pos_left _ hm)
  have h := instOf_pAt ns hv hlt
  have h1 : j / ns.getD 0 0 = 0 := Nat.div_eq_of_lt hj
  have h2 : j % ns.getD 0 0 = j := Nat.mod_eq_of_lt hj
  rw [h1, h2] at h
  exact ⟨h.1, by have e : 3 + 2 * j = 2 + 2 * j + 1 := by omega
                 rw [e]; exact h.2⟩

lemma depth_link (hm : 0 < ns.getD 1 0) {j : ℕ} (hj : j < ns.getD 0 0) :
    depthAt (instOf ns hv) 0 j = cntN ns j := by
  unfold depthAt cntN
  show (List.range (ns.getD 0 0)).countP _ = _
  refine List.countP_congr fun j' hj' => ?_
  have hj'' := List.mem_range.1 hj'
  have a := inst_row ns hv hm hj
  have b := inst_row ns hv hm hj''
  simp only [RunsAt, startAt, sRow, a.1, a.2, b.1, b.2]
  simp

lemma omega_link : omegaD (instOf ns hv) = omegaS ns := by
  unfold omegaD omegaS
  have hd : (instOf ns hv).days = ns.getD 1 0 := rfl
  have hc : (instOf ns hv).clients = ns.getD 0 0 := rfl
  rw [hd, hc]
  by_cases hm : ns.getD 1 0 = 0
  · rw [if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm]
    have hm' : 0 < ns.getD 1 0 := Nat.pos_of_ne_zero hm
    unfold omegaT omegaN
    show (List.range (ns.getD 0 0)).foldl _ 0 = _
    exact foldl_max_congr _ _ (fun j hj => by
      rw [depth_link ns hv hm' (List.mem_range.1 hj)])

lemma di_iff : ((instOf ns hv).DayIndepD ∧ (instOf ns hv).DayIndepP) ↔ DI ns := by
  constructor
  · rintro ⟨hd, hp⟩ t ht
    have hn : 0 < ns.getD 0 0 := by
      rcases Nat.eq_zero_or_pos (ns.getD 0 0) with h | h
      · rw [h] at ht; simp at ht
      · exact h
    have hi : t / ns.getD 0 0 < ns.getD 1 0 := by rw [Nat.div_lt_iff_lt_mul hn]; exact ht
    have hj : t % ns.getD 0 0 < ns.getD 0 0 := Nat.mod_lt _ hn
    have hm : 0 < ns.getD 1 0 := lt_of_le_of_lt (Nat.zero_le _) hi
    have e : t / ns.getD 0 0 * ns.getD 0 0 + t % ns.getD 0 0 = t := by
      have := Nat.div_add_mod t (ns.getD 0 0)
      rw [Nat.mul_comm] at this
      omega
    have h1 := hp ⟨t / ns.getD 0 0, hi⟩ ⟨0, hm⟩ ⟨t % ns.getD 0 0, hj⟩
    have h2 := hd ⟨t / ns.getD 0 0, hi⟩ ⟨0, hm⟩ ⟨t % ns.getD 0 0, hj⟩
    simp only [instOf] at h1 h2
    rw [e] at h1 h2
    simp only [zero_mul, zero_add] at h1 h2
    exact ⟨h1, h2⟩
  · intro hdi
    have key : ∀ (i : ℕ) (j : ℕ), i < ns.getD 1 0 → j < ns.getD 0 0 →
        ns.getD (2 + 2 * (i * ns.getD 0 0 + j)) 0 = ns.getD (2 + 2 * j) 0 ∧
        ns.getD (2 + 2 * (i * ns.getD 0 0 + j) + 1) 0 = ns.getD (2 + 2 * j + 1) 0 := by
      intro i j hi hj
      have hcell := cell_lt hi hj
      have h := hdi _ hcell
      have hmod : (i * ns.getD 0 0 + j) % ns.getD 0 0 = j := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
      rw [hmod] at h
      exact h
    refine ⟨fun i i' j => ?_, fun i i' j => ?_⟩
    · exact (key i j i.isLt j.isLt).2.trans (key i' j i'.isLt j.isLt).2.symm
    · exact (key i j i.isLt j.isLt).1.trans (key i' j i'.isLt j.isLt).1.symm

end Link

open Classical in
/-- **The reduction**, as a map on words: an instance with day-independent data and a fair
schedule goes to a satisfiable formula, every other word to an unsatisfiable one. -/
noncomputable def reduceD (w : Word) : Word :=
  if w ∈ Uniform (fun I _ => I.DayIndepD ∧ I.DayIndepP) then encodeFormula satF
  else encodeFormula unsatisfiable

/-- **The reduction is correct.** -/
theorem reduceD_correct (w : Word) :
    w ∈ Uniform (fun I _ => I.DayIndepD ∧ I.DayIndepP) ↔ reduceD w ∈ TwoSat := by
  classical
  unfold reduceD
  by_cases h : w ∈ Uniform (fun I _ => I.DayIndepD ∧ I.DayIndepP)
  · rw [if_pos h, twoSat_mem_encode]
    exact ⟨fun _ => satF_satisfiable, fun _ => h⟩
  · rw [if_neg h]
    constructor
    · intro h'; exact absurd h' h
    · intro hT
      exact absurd ((twoSat_mem_encode).1 hT) Injectivity.not_satisfiable_unsatisfiable

/-- **The words of the language are the good streams.** -/
theorem uniform_iff_good (w : Word) :
    w ∈ Uniform (fun I _ => I.DayIndepD ∧ I.DayIndepP) ↔
      ∃ ns : List ℕ, w = numCode ns ∧ Shape eU ns ∧ goodD ns := by
  constructor
  · rintro ⟨I, k, hw, hC, hF⟩
    obtain ⟨ns, hw', hs, hv⟩ := (Lax117284Proofs.Machine.X1Sem.uniform_iff' w).1 ⟨I, k, hw⟩
    refine ⟨ns, hw', hs, hv, ?_⟩
    have hI : encodeUniform (instOf ns hv) (paramOf ns) = numCode ns := by
      rw [encodeUniform, encodeInstance_eq]
      conv_rhs => rw [← instToks_instOf ns hv hs]
      rw [numCode_append]
      simp [numCode]
    have := Injectivity.encodeUniform_inj (I := instOf ns hv) (I' := I) (k := paramOf ns)
      (k' := k) (hI.trans (hw'.symm.trans hw.symm))
    obtain ⟨rfl, rfl⟩ := this
    refine ⟨(di_iff ns hv).1 hC, ?_⟩
    have := (hasKFair_iff_omegaD hC.1 hC.2 (paramOf ns)).1 hF
    rw [omega_link ns hv] at this
    exact this
  · rintro ⟨ns, hw, hs, hv, hdi, hk⟩
    have hC := (di_iff ns hv).2 hdi
    refine ⟨instOf ns hv, paramOf ns, ?_, hC, ?_⟩
    · rw [hw, encodeUniform, encodeInstance_eq]
      conv_rhs => rw [← instToks_instOf ns hv hs]
      rw [numCode_append]
      simp [numCode]
    · rw [hasKFair_iff_omegaD hC.1 hC.2, omega_link ns hv]
      exact hk

end Lax117284Proofs.Machine.X3Sem
