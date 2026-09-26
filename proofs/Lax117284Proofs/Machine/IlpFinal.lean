import Lax117284Proofs.Machine.IlpLayout
import Lax117284Proofs.IlpClientsBridge
import Lax808846Proofs.Transfer

/-!
The solver solves the integer programs of the family within the word RAM cost model.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax808846Proofs.Transfer
open Lax117284Proofs.IlpClients Classical Finset

noncomputable section

/-- The largest entry of a word. -/
def mxl (x : List ℕ) : ℕ := x.foldr max 0

theorem le_mxl {x : List ℕ} {v : ℕ} (h : v ∈ x) : v ≤ mxl x := by
  induction x with
  | nil => simp at h
  | cons a l ih =>
    simp only [mxl, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact le_trans (ih h') (le_max_right _ _)

theorem mxl_mem {x : List ℕ} (h : x ≠ []) : mxl x ∈ x := by
  induction x with
  | nil => exact absurd rfl h
  | cons a l ih =>
    simp only [mxl, List.foldr_cons]
    by_cases hl : l = []
    · subst hl; simp
    · have := ih hl
      rcases le_total a (l.foldr max 0) with h1 | h1
      · rw [max_eq_right h1]; exact List.mem_cons_of_mem _ this
      · rw [max_eq_left h1]; exact List.mem_cons_self

/-- The bound of the machine. -/
def Bx (x : List ℕ) : ℕ := (x.length + mxl x + 1) ^ 17 + 1

/-- The cost of the solver on a word with `N` variables. -/
def Kx' (N : ℕ) : ℕ := 100 + ∑ m ∈ range (N + 1), Kfam m

/-- The cost of the solver. -/
def Kx (x : List ℕ) : ℕ := Kx' (x.getD 0 0)

/-- What the solver answers. -/
def fAns (x : List ℕ) : List ℕ :=
  if (Lax117284.IlpClients.decodeILP x).Feasible then [1] else [0]

theorem lt_Bx {x : List ℕ} {v : ℕ} (h : v ∈ x) : v < Bx x := by
  have h1 := le_mxl h
  have h2 : 1 ≤ x.length + mxl x + 1 := by omega
  have h3 : x.length + mxl x + 1 ≤ (x.length + mxl x + 1) ^ 17 := by
    calc x.length + mxl x + 1 = (x.length + mxl x + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right h2 (by omega)
  unfold Bx; omega

theorem five_lt_Bx {x : List ℕ} (h : 5 ≤ x.length + 1) : 5 < Bx x := by
  have h2 : 1 ≤ x.length + mxl x + 1 := by omega
  have h3 : x.length + mxl x + 1 ≤ (x.length + mxl x + 1) ^ 17 := by
    calc x.length + mxl x + 1 = (x.length + mxl x + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right h2 (by omega)
  unfold Bx; omega

theorem getD_mem' (l : List ℕ) (i : ℕ) (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

theorem hyp_of_family (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (hn : 1 ≤ n) :
    Hyp n cnt bb (mxl (ilpWord n cnt bb)) (Bx (ilpWord n cnt bb)) := by
  have hlen := ilpWord_length n cnt bb
  refine ⟨hn, ?_, ?_, ?_⟩
  · intro t ht
    have hM : t < nM n := by unfold nM; omega
    have := ilpWord_rhs n cnt bb hM
    have hi : 2 + nM n * nN n + t < (ilpWord n cnt bb).length := by rw [hlen]; unfold zLen; omega
    have hm := le_mxl (getD_mem' _ _ hi)
    rw [this] at hm
    unfold rhs at hm
    rwa [if_pos ht] at hm
  · have hT : nT n < nM n := by unfold nM; omega
    have := ilpWord_rhs n cnt bb hT
    have hi : 2 + nM n * nN n + nT n < (ilpWord n cnt bb).length := by rw [hlen]; unfold zLen; omega
    have hm := le_mxl (getD_mem' _ _ hi)
    rw [this] at hm
    unfold rhs at hm
    rwa [if_neg (lt_irrefl _)] at hm
  · unfold Ub Bx
    rw [hlen]; omega

theorem n_le_nN (n : ℕ) : n ≤ nN n := by unfold nN; omega

theorem Kfam_le_Kx' (n N : ℕ) (h : n ≤ N) : Kfam n ≤ Kx' N := by
  unfold Kx'
  have : Kfam n ≤ ∑ m ∈ range (N + 1), Kfam m :=
    Finset.single_le_sum (f := Kfam) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  omega

theorem fAns_of_iff (x : List ℕ) (P : Prop) [Decidable P]
    (h : (Lax117284.IlpClients.decodeILP x).Feasible ↔ P) : [if P then 1 else 0] = fAns x := by
  unfold fAns
  by_cases hP : P
  · rw [if_pos hP, if_pos (h.mpr hP)]
  · rw [if_neg hP, if_neg (fun hf => hP (h.mp hf))]

theorem feasible_small (a b : ℕ) :
    (Lax117284.IlpClients.decodeILP [1, 1, a, b]).Feasible ↔ (a = 0 → b = 0) ∧ (0 < a → a ∣ b) :=
  feasible_one_by_one a b

/-- **The solver runs on every word of the domain.** -/
theorem ilp_run {x : List ℕ} (hx : x ∈ Lax117284.IlpClients.ilpClients.Domain) :
    ∃ (ext : String → ℕ) (σ' : Env), Run (Bx x) ilpCom (initEnv ext x) σ' (Kx x) ∧
      σ'.out = fAns x := by
  rcases hx with ⟨n, cnt, bb, hxe⟩ | hxe
  · have hxe' : x = ilpWord n cnt bb := by
      rw [hxe]; exact (IlpClientsBridge.ilpWord_eq n cnt bb)
    subst hxe'
    by_cases hn : n = 0
    · subst hn
      rw [ilpWord_zero]
      have hmem : ∀ v ∈ ([1, 1, 1, cnt 0] : List ℕ), v < Bx [1, 1, 1, cnt 0] := fun v hv => lt_Bx hv
      have h5 : 5 < Bx [1, 1, 1, cnt 0] := five_lt_Bx (by simp)
      obtain ⟨σ', hr, hout⟩ := ilpSmall_run (B := Bx [1, 1, 1, cnt 0]) 1 (cnt 0) (hmem 1 (by simp))
        (hmem (cnt 0) (by simp)) h5
      refine ⟨extI 0 4, σ', hr.mono (by unfold Kx Kx'; simp), ?_⟩
      rw [hout]
      exact fAns_of_iff _ _ (feasible_small 1 (cnt 0))
    · have hn1 : 1 ≤ n := by omega
      have hb := hyp_of_family n cnt bb hn1
      have hxle : ∀ v ∈ ilpWord n cnt bb, v ≤ mxl (ilpWord n cnt bb) := fun v hv => le_mxl hv
      obtain ⟨σ', hr, hout⟩ := ilpFamily_run hb hxle
      have hlen := ilpWord_length n cnt bb
      have h0 : (ilpWord n cnt bb).getD 0 0 = nN n := by
        rw [ilpWord_getD, if_pos (by have := zLen_ge n; omega)]; simp [wordFun]
      refine ⟨extI n (zLen n), σ', hr.mono ?_, ?_⟩
      · unfold Kx
        rw [h0]
        exact Kfam_le_Kx' n (nN n) (n_le_nN n)
      · rw [hout]
        exact fAns_of_iff _ _ (IlpClientsBridge.feasible_iff _)
  · subst hxe
    have hmem : ∀ v ∈ ([1, 1, 0, 1] : List ℕ), v < Bx [1, 1, 0, 1] := fun v hv => lt_Bx hv
    have h5 : 5 < Bx [1, 1, 0, 1] := five_lt_Bx (by simp)
    obtain ⟨σ', hr, hout⟩ := ilpSmall_run (B := Bx [1, 1, 0, 1]) 0 1 (hmem 0 (by simp))
      (hmem 1 (by simp)) h5
    refine ⟨extI 0 4, σ', hr.mono (by unfold Kx Kx'; simp), ?_⟩
    rw [hout]
    exact fAns_of_iff _ _ (feasible_small 0 1)

theorem ilp_solves : Solves layoutI ilpCom Lax117284.IlpClients.ilpClients.Domain fAns Bx Kx where
  ok := layoutI_ok
  inp := fun x _ v hv => lt_Bx hv
  run := fun x hx => ilp_run hx

/-- The scalars of the layout. -/
def SI : ℕ := layoutI.scalars.length

/-- The constant of the solver. -/
def cI : ℕ := 30 + SI

/-- The function of the parameter. -/
def gI (N : ℕ) : ℕ := 10 * Kx' N + 1

theorem domain_len_ge {x : List ℕ} (hx : x ∈ Lax117284.IlpClients.ilpClients.Domain) : 4 ≤ x.length := by
  rcases hx with ⟨n, cnt, bb, hxe⟩ | hxe
  · have h' : x = ilpWord n cnt bb := by rw [hxe]; exact (IlpClientsBridge.ilpWord_eq n cnt bb)
    rw [h', ilpWord_length]; exact zLen_ge n
  · rw [hxe]; simp

theorem domain_ne_nil {x : List ℕ} (hx : x ∈ Lax117284.IlpClients.ilpClients.Domain) : x ≠ [] := by
  intro h
  have := domain_len_ge hx
  rw [h] at this; simp at this

set_option maxRecDepth 100000 in
theorem fits_layout {x : List ℕ} {w : ℕ} (hx : x ∈ Lax117284.IlpClients.ilpClients.Domain)
    (hf : Lax117284.ParameterizedComplexity.Fits cI w x) : layoutI.FitsWords (Bx x) w := by
  have hne := domain_ne_nil hx
  have h4 := domain_len_ge hx
  have h1 := hf _ (mxl_mem hne)
  have hspan : layoutI.span (Bx x) = 12 + 2 + SI + 10 * Bx x := by
    have ha : layoutI.arrays.length = 10 := rfl
    have ht : layoutI.temps = 12 := rfl
    unfold Layout.span
    rw [ha, ht]
    rfl
  have hB : Bx x = (x.length + mxl x + 1) ^ 17 + 1 := rfl
  obtain ⟨U, hU⟩ : ∃ U, U = x.length + mxl x + 1 := ⟨_, rfl⟩
  rw [← hU] at h1 hB
  have hU5 : 5 ≤ U := by omega
  have hpow : U ^ 17 ≤ U ^ cI := Nat.pow_le_pow_right (by omega) (by unfold cI; omega)
  obtain ⟨P, hP⟩ : ∃ P, P = U ^ 17 := ⟨_, rfl⟩
  have hP5 : 5 ≤ P := by
    rw [hP]
    calc 5 ≤ U := hU5
      _ = U ^ 1 := (pow_one _).symm
      _ ≤ U ^ 17 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [← hP] at hB hpow
  have h2 : cI * P ≤ cI * U ^ cI := Nat.mul_le_mul_left _ hpow
  have h3 : 24 + SI + 10 * P ≤ cI * P := by
    unfold cI
    nlinarith
  refine fitsWords_of_max_le (by rw [hB]; omega) ?_
  rw [max_le_iff]
  constructor
  · rw [hB]; omega
  · rw [hspan, hB]; omega

theorem time_bound {x : List ℕ} (hx : x ∈ Lax117284.IlpClients.ilpClients.Domain) :
    (10 : ℕ) * Kx x + 1 ≤ cI * gI (x.getD 0 0) * (x.length + 1) ^ cI := by
  have h1 : 1 ≤ (x.length + 1) ^ cI := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ cI := by unfold cI; omega
  have : gI (x.getD 0 0) = 10 * Kx x + 1 := rfl
  rw [← this]
  calc gI (x.getD 0 0) ≤ cI * gI (x.getD 0 0) := Nat.le_mul_of_pos_left _ h2
    _ ≤ cI * gI (x.getD 0 0) * (x.length + 1) ^ cI := Nat.le_mul_of_pos_right _ h1

/--
---
conclusion: Lax117284.IlpClients.ilpClients_fpt
---
The integer programs of the family are solved by a word RAM program that reads the word, with `N`
variables and `M` constraints, and decides at once whether it is the program `a x = b` of one variable
(the fixed word `[1, 1, 0, 1]` and the program of no client), which it solves by a division. Otherwise
it finds the number `n` of clients from `M`, and enumerates all the numbers below `(K + 1) ^ D`, where
`K = (n + 1) ^ (n + 1) + 1` and `D = N + 2 n² + 1`, by an odometer whose digits are the entries of a
certificate: a digit for every variable, the two matrices of an integer left inverse of the
difference vectors of the large variables, and a common denominator. For every certificate it
decodes a candidate solution (sums of the small digits per type, the base of each type, the values of
the extras by the integer left inverse, the values of the bases by what is left of the demand of the
type) and tests it against the program stored in the word, row by row. The program is feasible if and
only if some certificate is accepted, by the completeness of the certificates (the shifting lemma,
the kernel bound of the family by Siegel's lemma, the bound `n` on the number of extras) and the
soundness of the test. Every number is at most a fixed power of the length of the word plus its largest
entry, so the running time is a function of the number of variables alone times a constant.
-/
theorem ilpClients_fpt_proved : Lax117284.ParameterizedComplexity.FPT Lax117284.IlpClients.ilpClients := by
  refine ⟨compileProgram layoutI ilpCom, cI, gI, fun w => ?_⟩
  have hs : Solves layoutI ilpCom
      {x | x ∈ Lax117284.IlpClients.ilpClients.Domain ∧ Lax117284.ParameterizedComplexity.Fits cI w x}
      fAns Bx Kx :=
    ⟨ilp_solves.ok, fun x hx => ilp_solves.inp x hx.1, fun x hx => ilp_solves.run x hx.1⟩
  refine computesInTime_of_solves hs ?_ ?_
  · rintro x ⟨hx, hf⟩
    exact fits_layout hx hf
  · rintro x ⟨hx, hf⟩
    exact time_bound hx

end

end Lax117284Proofs.Machine.Ilp

example : type_of% @Lax117284.IlpClients.ilpClients_fpt := Lax117284Proofs.Machine.Ilp.ilpClients_fpt_proved

