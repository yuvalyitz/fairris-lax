import Lax117284Proofs.Machine.InstSem
import Lax117284Proofs.Machine.X1Sem
import Lax117284Proofs.Machine.D3Client
import Lax117284Proofs.D3Prog
import Lax117284Proofs.D3Congr
import Lax117284Proofs.X1Word

/-!
Day-independent due dates, with a fixed number of days, on the numbers of a stream: every cell's
due date equals the due date of the same client on the first day, and the number of days is the
fixed number.
-/

namespace Lax117284Proofs.Machine.D3Sem

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime Lax117284.TwoSatisfiability
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.D3DP Lax117284Proofs.D3Rank Lax117284Proofs.D3Code Lax117284Proofs.D3Tab
open Lax117284Proofs.D3Prog Lax117284Proofs.D3Congr
open Lax117284Proofs.X1Word (satF twoSat_mem_encode satF_satisfiable)

/-- Every cell's due date equals the due date of the same client on the first day. -/
def DID (ns : List ℕ) : Prop :=
  ∀ t < ns.getD 1 0 * ns.getD 0 0,
    ns.getD (2 + 2 * t + 1) 0 = ns.getD (2 + 2 * (t % ns.getD 0 0) + 1) 0

section Link

variable (ns : List ℕ) (hv : Valid ns)

/-- **The numbers are day-independent in their due dates exactly when the instance is.** -/
theorem did_iff : (instOf ns hv).DayIndepD ↔ DID ns := by
  constructor
  · intro hd t ht
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
    have h2 := hd ⟨t / ns.getD 0 0, hi⟩ ⟨0, hm⟩ ⟨t % ns.getD 0 0, hj⟩
    simp only [instOf] at h2
    rw [e] at h2
    simpa using h2
  · intro hdid i i' j
    have key : ∀ (i : ℕ) (j : ℕ), i < ns.getD 1 0 → j < ns.getD 0 0 →
        ns.getD (2 + 2 * (i * ns.getD 0 0 + j) + 1) 0 = ns.getD (2 + 2 * j + 1) 0 := by
      intro i j hi hj
      have hcell := cell_lt hi hj
      have h := hdid _ hcell
      have hmod : (i * ns.getD 0 0 + j) % ns.getD 0 0 = j := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
      rwa [hmod] at h
    exact (key i j i.isLt j.isLt).trans (key i' j i'.isLt j.isLt).symm

end Link

/-- The class the fixed number of days singles out, on the numbers of a valid stream. -/
def goodM (m : ℕ) (ns : List ℕ) : Prop := DID ns ∧ ns.getD 1 0 = m

open Classical in
/-- **The reduction**, as a map on words, for a fixed number `m` of days: an instance with
day-independent due dates and `m` days that has a fair schedule goes to a satisfiable formula,
every other word to an unsatisfiable one. -/
noncomputable def reduceM (m : ℕ) (w : Word) : Word :=
  if w ∈ Uniform (fun I _ => I.DayIndepD ∧ I.days = m) then encodeFormula satF
  else encodeFormula unsatisfiable

/-- **The reduction is correct.** -/
theorem reduceM_correct (m : ℕ) (w : Word) :
    w ∈ Uniform (fun I _ => I.DayIndepD ∧ I.days = m) ↔ reduceM m w ∈ TwoSat := by
  classical
  unfold reduceM
  by_cases h : w ∈ Uniform (fun I _ => I.DayIndepD ∧ I.days = m)
  · rw [if_pos h, twoSat_mem_encode]
    exact ⟨fun _ => satF_satisfiable, fun _ => h⟩
  · rw [if_neg h]
    constructor
    · intro h'; exact absurd h' h
    · intro hT
      exact absurd ((twoSat_mem_encode).1 hT) Injectivity.not_satisfiable_unsatisfiable

/-- **The words of the language are the streams whose instance has a fair schedule.** -/
theorem uniform_iff_good (m : ℕ) (w : Word) :
    w ∈ Uniform (fun I _ => I.DayIndepD ∧ I.days = m) ↔
      ∃ ns : List ℕ, w = numCode ns ∧ Shape eU ns ∧ ∃ hv : Valid ns, goodM m ns ∧
        (instOf ns hv).HasKFairSchedule (paramOf ns) := by
  constructor
  · rintro ⟨I, k, hw, ⟨hC, hm⟩, hF⟩
    obtain ⟨ns, hw', hs, hv⟩ := (Lax117284Proofs.Machine.X1Sem.uniform_iff' w).1 ⟨I, k, hw⟩
    have hI : encodeUniform (instOf ns hv) (paramOf ns) = numCode ns := by
      rw [encodeUniform, encodeInstance_eq]
      conv_rhs => rw [← instToks_instOf ns hv hs]
      rw [numCode_append]; simp [numCode]
    obtain ⟨rfl, rfl⟩ := Injectivity.encodeUniform_inj (I := instOf ns hv) (I' := I)
      (k := paramOf ns) (k' := k) (hI.trans (hw'.symm.trans hw.symm))
    exact ⟨ns, hw', hs, hv, ⟨(did_iff ns hv).1 hC, hm⟩, hF⟩
  · rintro ⟨ns, hw, hs, hv, ⟨hdid, hm⟩, hF⟩
    refine ⟨instOf ns hv, paramOf ns, ?_, ⟨(did_iff ns hv).2 hdid, hm⟩, hF⟩
    rw [hw, encodeUniform, encodeInstance_eq]
    conv_rhs => rw [← instToks_instOf ns hv hs]
    rw [numCode_append]; simp [numCode]

/-- The position of `i * n + j` in the table, for `j < n`: the quotient is `i` and the
remainder is `j`. -/
lemma divmod_row {n i j : ℕ} (hn : 0 < n) (hj : j < n) :
    (i * n + j) / n = i ∧ (i * n + j) % n = j := by
  have e : i * n + j = j + n * i := by ring
  rw [e, Nat.add_mul_div_left _ _ hn, Nat.add_mul_mod_self_left]
  simp [Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]

/-- **The processing time of the client at a position, on the array's own order, is the one of
the dynamic program.** -/
theorem qF_eq_qI {ns R0 : List ℕ} (hv : Valid ns) {n m PK i c : ℕ} (hn : ns.getD 0 0 = n)
    (hm : ns.getD 1 0 = m) (hi : i < m) (hc : c < n)
    (hR0 : R0.getD (PK + c) 0 = D3Prog.ordI (instOf ns hv) c) :
    Lax117284Proofs.Machine.D3Client.qF ns R0 PK n i c = D3Prog.qI (instOf ns hv) i c := by
  have hordlt : D3Prog.ordI (instOf ns hv) c < n := by
    have h0 : D3Prog.ordI (instOf ns hv) c < (instOf ns hv).clients :=
      D3Prog.ordI_lt (I := instOf ns hv) (c := c) (by show c < ns.getD 0 0; rw [hn]; exact hc)
    have h0' : D3Prog.ordI (instOf ns hv) c < ns.getD 0 0 := h0
    omega
  have hn0 : 0 < n := by omega
  have ht : i * n + D3Prog.ordI (instOf ns hv) c < ns.getD 1 0 * ns.getD 0 0 := by
    rw [hn, hm]
    have h1 : (i + 1) * n ≤ m * n := Nat.mul_le_mul_right _ hi
    have h2 : (i + 1) * n = i * n + n := by ring
    omega
  have hp := (instOf_pAt ns hv ht).1
  obtain ⟨hdiv, hmod⟩ := divmod_row hn0 hordlt
  rw [hn, hdiv, hmod] at hp
  show ns.getD (2 + 2 * (i * n + R0.getD (PK + c) 0)) 0 = _
  rw [hR0]
  exact hp.symm

/-- **The due date of the client at a position, on the array's own order, is the one of the
dynamic program.** -/
theorem eOrd_eq_eI {ns R0 : List ℕ} (hv : Valid ns) {m n PK c : ℕ} (hn : ns.getD 0 0 = n)
    (hm : ns.getD 1 0 = m) (hm0 : 0 < m) (hn0 : 0 < n) (hc : c < n)
    (hR0 : R0.getD (PK + c) 0 = D3Prog.ordI (instOf ns hv) c) :
    Lax117284Proofs.Machine.D3Sweep.eOrd ns R0 PK c = D3Prog.eI (instOf ns hv) c := by
  have hordlt : D3Prog.ordI (instOf ns hv) c < n := by
    have h0 : D3Prog.ordI (instOf ns hv) c < (instOf ns hv).clients :=
      D3Prog.ordI_lt (I := instOf ns hv) (c := c) (by show c < ns.getD 0 0; rw [hn]; exact hc)
    have h0' : D3Prog.ordI (instOf ns hv) c < ns.getD 0 0 := h0
    omega
  have ht : D3Prog.ordI (instOf ns hv) c < ns.getD 1 0 * ns.getD 0 0 := by
    rw [hn, hm]
    calc D3Prog.ordI (instOf ns hv) c < n := hordlt
      _ ≤ m * n := Nat.le_mul_of_pos_left _ hm0
  have hd := (instOf_pAt ns hv ht).2
  have hdiv : D3Prog.ordI (instOf ns hv) c / ns.getD 0 0 = 0 := by
    rw [hn]; exact Nat.div_eq_of_lt hordlt
  have hmod : D3Prog.ordI (instOf ns hv) c % ns.getD 0 0 = D3Prog.ordI (instOf ns hv) c := by
    rw [hn]; exact Nat.mod_eq_of_lt hordlt
  rw [hdiv, hmod] at hd
  show ns.getD (3 + 2 * R0.getD (PK + c) 0) 0 = _
  rw [hR0, show 3 + 2 * D3Prog.ordI (instOf ns hv) c = 2 + 2 * D3Prog.ordI (instOf ns hv) c + 1
    from by omega]
  unfold D3Prog.eI D3Prog.ddI
  rw [hd]

/-- **The due date of a client below `n`, read off the array, is the one of the instance.** -/
theorem ddA_eq_ddI {ns : List ℕ} (hv : Valid ns) {n m : ℕ} (hn : ns.getD 0 0 = n)
    (hm : ns.getD 1 0 = m) (hm0 : 0 < m) {j : ℕ} (hj : j < n) :
    Lax117284Proofs.Machine.D3Rk.ddA ns j = D3Prog.ddI (instOf ns hv) j := by
  have ht : j < ns.getD 1 0 * ns.getD 0 0 := by
    rw [hn, hm]
    calc j < n := by omega
      _ ≤ m * n := Nat.le_mul_of_pos_left _ hm0
  have hd := (instOf_pAt ns hv ht).2
  have hdiv : j / ns.getD 0 0 = 0 := by rw [hn]; exact Nat.div_eq_of_lt (by omega)
  have hmod : j % ns.getD 0 0 = j := by rw [hn]; exact Nat.mod_eq_of_lt (by omega)
  rw [hdiv, hmod] at hd
  unfold D3Prog.ddI
  show ns.getD (3 + 2 * j) 0 = _
  rw [show 3 + 2 * j = 2 + 2 * j + 1 from by omega]
  exact hd.symm

end Lax117284Proofs.Machine.D3Sem
