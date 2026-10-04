import Lax117284Proofs.ComputableBounds
import Lax117284.Theorem4
import Lax117284.IlpClients
import Lax117284Proofs.Machine.ClRedSpec
import Lax117284Proofs.Machine.ClMainCost
import Lax117284Proofs.ExtremeFairness
import Lax117284Proofs.IlpClientsBridge

/-!
Theorem 4, third bullet, the reduction: the problem parameterized by the number of clients
fpt-reduces to the feasibility of the integer programs of the family `ilpClients`, parameterized by
the number of variables.
-/

namespace Lax117284Proofs.Theorem4ClientsReduction

open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes Lax808846Proofs.Compile
open Lax117284.InstanceEncoding Lax117284.ParameterizedComplexity Lax117284.Scheduling
open Lax117284.IlpClients (decodeILP ilpClients)
open Lax117284Proofs.ClientsILP Lax117284Proofs.Machine.ClBuild Lax117284Proofs.Machine.ClMain
open Lax117284Proofs.Machine.ClRed

variable {x : List ℕ} {I : Instance} {k : ℕ}

theorem param_eq (hx : x ∈ UniformInstances) :
    Lax117284.Theorem4.byClients.param x = x.getD 0 0 := by
  obtain ⟨I, k, hdec⟩ := hx
  have hx0 := ClientsWord.x0 hdec
  show (decode x.dropLast).clients = _
  rw [decode_dropLast hdec, hx0]

/-- The fixed word `0 · x = 1` is infeasible. -/
theorem reject_infeasible : ¬ (decodeILP [1, 1, 0, 1]).Feasible := by
  rintro ⟨y, hy⟩
  have hM : 0 < (decodeILP [1, 1, 0, 1]).M := by decide
  have := hy ⟨0, hM⟩
  have h0 : ∑ i, (decodeILP [1, 1, 0, 1]).a ⟨0, hM⟩ i * y i = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : i.val = 0 := by
      have := i.isLt
      simp [decodeILP] at this
      omega
    simp [decodeILP, hi]
  rw [h0] at this
  simp [decodeILP] at this

/-! ### The fitting condition -/

/-- The fitting condition, in terms of the largest entry, for any nonempty word. -/
theorem fits_Mx' {c w : ℕ} {y : List ℕ} (hy : y ≠ []) (hf : Fits c w y) :
    c * (y.length + Mx y + 1) ^ c ≤ 2 ^ w := by
  rcases Mx_mem_or_zero y with hm | hm
  · exact hf _ hm
  · obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil y hy
    have := hf v hv
    rw [hm]
    have : c * (y.length + 0 + 1) ^ c ≤ c * (y.length + v + 1) ^ c :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega

/-- The constant of the reduction. -/
def cR : ℕ := 2 * (24 + layoutR.scalars.length) + 2

/-- The function of the parameter that bounds the cost. -/
def gR (n : ℕ) : ℕ := 10000 * (zLen n + 1) ^ 2

theorem bound_of {S a b c w : ℕ} (hc : 48 + 2 * S ≤ c) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h1 : c * a ^ c ≤ 2 ^ w) (h2 : c * b ^ c ≤ 2 ^ w) :
    max (a + b) (12 + 2 + S + 10 * (a + b)) ≤ 2 ^ w := by
  rcases le_total a b with hab | hab
  · have e1 : b ≤ b ^ c := Nat.le_self_pow (by omega) b
    have e2 : c * b ≤ c * b ^ c := Nat.mul_le_mul_left _ e1
    have e3 : (48 + 2 * S) * b ≤ c * b := Nat.mul_le_mul_right _ hc
    have e4 : 14 + S + 20 * b ≤ (48 + 2 * S) * b := by nlinarith
    rw [max_le_iff]; constructor <;> omega
  · have e1 : a ≤ a ^ c := Nat.le_self_pow (by omega) a
    have e2 : c * a ≤ c * a ^ c := Nat.mul_le_mul_left _ e1
    have e3 : (48 + 2 * S) * a ≤ c * a := Nat.mul_le_mul_right _ hc
    have e4 : 14 + S + 20 * a ≤ (48 + 2 * S) * a := by nlinarith
    rw [max_le_iff]; constructor <;> omega

theorem fRed_ne (hx : x ∈ UniformInstances) : fRed x ≠ [] := by
  obtain ⟨I, k, hdec⟩ := hx
  rw [fRed_eq hdec]
  intro h
  have := fI_length I k
  rw [h] at this
  simp at this

theorem fitsWords {w : ℕ} (hx : x ∈ UniformInstances) (hf : Fits cR w x)
    (hf' : Fits cR w (fRed x)) : layoutR.FitsWords (BR x) w := by
  have hxne : x ≠ [] := by
    obtain ⟨I, k, hdec⟩ := hx
    have := ClientsWord.len_eq hdec
    intro h; rw [h, List.length_nil] at this; omega
  have h1 := fits_Mx' hxne hf
  have h2 := fits_Mx' (fRed_ne hx) hf'
  refine fitsWords_of_max_le (by unfold BR; omega) ?_
  have hspan : layoutR.span (BR x) = 12 + 2 + layoutR.scalars.length + 10 * BR x := by
    have ht : layoutR.temps = 12 := rfl
    have ha : layoutR.arrays.length = 10 := rfl
    simp only [Layout.span, ht, ha]
  rw [hspan]
  unfold BR
  exact bound_of (by unfold cR; omega) (by omega) (by omega) h1 h2

/-! ### The cost -/

theorem arith0 (L c g : ℕ) (hc : 2 ≤ c) (hg : 1 ≤ g) :
    10 * ((24 * L + 60) + (20 + (4 + (8 + (4 + 8))))) + 1 ≤ c * (10000 * g) * (L + 1) ^ c := by
  have h1 : L + 1 ≤ (L + 1) ^ c := Nat.le_self_pow (by omega) _
  have h2 : 2 * (10000 * 1) * (L + 1) ≤ c * (10000 * g) * (L + 1) ^ c :=
    Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.mul_le_mul_left _ hg)) h1
  omega

theorem arith1 (N L c bc : ℕ) (hc : 2 ≤ c) (hB : bc ≤ 1000 * (N + L + 1) ^ 2) :
    10 * ((24 * L + 60) + (20 + (4 + (8 + (4 + (bc + (11 * N + 6))))))) + 1 ≤
      c * (10000 * (N + 1) ^ 2) * (L + 1) ^ c := by
  have h1 : (L + 1) ^ 2 ≤ (L + 1) ^ c := Nat.pow_le_pow_right (by omega) hc
  have h2 : N + L + 1 ≤ (N + 1) * (L + 1) := by nlinarith
  have h3 : (N + L + 1) ^ 2 ≤ ((N + 1) * (L + 1)) ^ 2 := Nat.pow_le_pow_left h2 2
  rw [mul_pow] at h3
  have h4 : 2 * (10000 * (N + 1) ^ 2) * (L + 1) ^ 2 ≤ c * (10000 * (N + 1) ^ 2) * (L + 1) ^ c :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ hc) h1
  have h5 : N + L + 1 ≤ (N + 1) ^ 2 * (L + 1) ^ 2 := by
    calc N + L + 1 ≤ (N + 1) * (L + 1) := h2
      _ ≤ (N + 1) ^ 2 * (L + 1) ^ 2 := by
        apply Nat.mul_le_mul <;> exact Nat.le_self_pow (by omega) _
  nlinarith

theorem time_le (hx : x ∈ UniformInstances) :
    10 * KR x + 1 ≤ cR * gR (x.getD 0 0) * (x.length + 1) ^ cR := by
  obtain ⟨I, k, hdec⟩ := hx
  have hl := ClientsWord.len_eq hdec
  have hn := ClientsWord.x0 hdec
  have hc : 2 ≤ cR := by unfold cR; omega
  unfold KR gR
  rw [decode_dropLast hdec, hn]
  unfold redK
  by_cases hn0 : I.clients = 0
  · rw [bK, if_pos hn0]
    exact arith0 _ _ _ hc (Nat.one_le_pow _ _ (by omega))
  · rw [bK, if_neg hn0]
    have hmn : I.days ≤ x.length := by
      have : I.days ≤ I.days * I.clients := Nat.le_mul_of_pos_right _ (by omega)
      omega
    obtain ⟨hT, hZ, hV, -, -, hnn, -, -⟩ := sizes_le_zLen I.clients
    have hbc : buildCost I ≤ 1000 * (zLen I.clients + x.length + 1) ^ 2 :=
      bcNM_le (n := I.clients) (m := I.days) (N := zLen I.clients + x.length)
        (by omega) (by omega) (by omega) (by omega)
    exact arith1 _ _ _ _ hc hbc

/-! ### The theorem -/

/--
The reduction is the map that sends the word of an instance with `n` clients, `m` days and
parameter `k` to the word of the integer program of Theorem 21 of the source (`zList`): one
variable per pair of a type of day (a conflict relation on the clients) and a set of clients, which
says how many days of that type serve exactly that set, one slack variable per client, one
constraint per type fixing the number of days of the type, and one per client saying the days it
is not served on are at most `m - k`; `2 ^ (n² + n) + n` variables in all, a function of `n`
alone. When `k > m` and there is a client the answer is `no` outright, and the map sends the word
to the fixed infeasible program `0 · x = 1`. The program is computed by a word RAM program that
reads the word, tests these two conditions, builds the word of the integer program in an array by
the same program as `fpt_byClients` and prints it; without a client it prints the program
`1 · x = m` directly, which is the integer program of the instance and whose cost does not depend
on `m`. Its cost is `24 |x|` plus a polynomial in the size of the integer program times `|x|`,
which is within `c · g(n) · (|x| + 1)^c`; its values are bounded by the lengths and largest
entries of the word and of its image, which fit into the word length by the fitting conditions
on both. Correctness is the equivalence of the integer program with the existence of a `k`-fair
schedule (`zList_feasible_iff`), which holds when `k ≤ m` or there is no client.
-/
theorem machine_reduction : MachineReduction
    Lax117284.Theorem4.byClients Lax117284.IlpClients.ilpClients
    fRed (compileProgram layoutR redCom) cR gR nN := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the image is a word of the family (or the fixed word)
    rintro x ⟨I, k, hdec⟩
    rw [fRed_eq hdec]
    unfold fI
    split_ifs
    · exact Lax117284Proofs.IlpClientsBridge.fixed_mem_domain
    · exact Lax117284Proofs.IlpClientsBridge.zList_mem_domain _ _ _ _
  · -- correctness
    rintro x ⟨I, k, hdec⟩
    show (decode x.dropLast).HasKFairSchedule (parameter x) ↔ (decodeILP (fRed x)).Feasible
    rw [fRed_eq hdec, decode_dropLast hdec, parameter_eq hdec]
    unfold fI
    split_ifs with hc
    · exact ⟨fun h => absurd h (ExtremeFairness.not_hasKFairSchedule_of_days_lt hc.1 hc.2),
        fun h => absurd h reject_infeasible⟩
    · exact (zList_feasible_iff I k (by omega)).symm
  · -- the parameter
    rintro x ⟨I, k, hdec⟩
    show (decodeILP (fRed x)).N ≤ nN (decode x.dropLast).clients
    rw [fRed_eq hdec, decode_dropLast hdec]
    unfold fI
    split_ifs
    · have := nN_pos I.clients
      show [1, 1, 0, 1].getD 0 0 ≤ nN I.clients
      simp; omega
    · rw [decode_N]
  · -- the running time
    intro w
    have hs : Solves layoutR redCom
        {x | x ∈ Lax117284.Theorem4.byClients.Domain ∧ Fits cR w x ∧ Fits cR w (fRed x)}
        fRed BR KR :=
      ⟨solves.ok, fun x hx => solves.inp x hx.1, fun x hx => solves.run x hx.1⟩
    refine computesInTime_of_solves hs ?_ ?_
    · rintro x ⟨hx, hf, hf'⟩
      exact fitsWords hx hf hf'
    · rintro x ⟨hx, -, -⟩
      rw [param_eq hx]
      show 10 * KR x + 1 ≤ _
      exact time_le hx

/--
---
conclusion: Lax117284.Theorem4.byClients_fptReduces_ilp
---
The verified reduction satisfies the archive's shared FPT-reduction definition.
-/
theorem byClients_fptReduces_ilp :
    FptReduces Lax117284.Theorem4.byClients Lax117284.IlpClients.ilpClients := by
  have hr := machine_reduction
  have hn : Computable nN := by
    unfold nN nV nT nZ
    bound_computable
  have hg : Computable gR := by
    unfold gR zLen nM nN nV nT nZ
    bound_computable
  refine ⟨fRed, ⟨hr.maps_domain, hr.correct⟩, ⟨nN, hn, hr.param_le⟩, ?_⟩
  apply Lax117284Proofs.FptBridge.of_machine hg hr.time
  refine ⟨fun n => zLen n + 2, 1, ?_, ?_⟩
  · unfold zLen nM nN nV nT nZ
    bound_computable
  · intro x hx v hv
    obtain ⟨I, k, hdec⟩ := hx
    have hp : Lax117284.Theorem4.byClients.param x = I.clients := by
      show (decode x.dropLast).clients = _
      rw [decode_dropLast hdec]
    rw [hp, pow_one]
    change v < 2 ^ ((zLen I.clients + 2) * (Lax759944.BinaryWordEncoding.bitSize x + 1))
    have hm : I.days < 2 ^ Lax759944.BinaryWordEncoding.bitSize x := by
      rw [← ClientsWord.x1 hdec]
      have hl := ClientsWord.len_eq hdec
      exact Lax496464Proofs.WHierarchy.Machine.SizeFacts.lt_two_pow_bitSize
        (by rw [List.getD_eq_getElem _ _ (by omega : 1 < x.length)]; exact List.getElem_mem _)
    have hz : zLen I.clients < 2 ^ ((zLen I.clients + 2) * (Lax759944.BinaryWordEncoding.bitSize x + 1)) :=
      Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (by nlinarith))
    have hm' : I.days < 2 ^ ((zLen I.clients + 2) * (Lax759944.BinaryWordEncoding.bitSize x + 1)) :=
      hm.trans_le (Nat.pow_le_pow_right (by omega) (by nlinarith))
    rw [fRed_eq hdec] at hv
    unfold fI at hv
    split_ifs at hv
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      have hpos : 1 < 2 ^ ((zLen I.clients + 2) * (Lax759944.BinaryWordEncoding.bitSize x + 1)) :=
        (by norm_num : 1 < 2 ^ 1).trans_le (Nat.pow_le_pow_right (by omega) (by nlinarith))
      rcases hv with rfl | rfl | rfl | rfl <;> omega
    · have hle := mem_zList_le I k hv
      exact hle.trans_lt (max_lt hz hm')

end Lax117284Proofs.Theorem4ClientsReduction
