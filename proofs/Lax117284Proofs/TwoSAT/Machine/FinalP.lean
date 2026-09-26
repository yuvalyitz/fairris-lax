import Lax117284Proofs.TwoSAT.Machine.Final
import Lax391470Proofs.RamBridge
import Lax117284.TwoSatInP

/-!
2-SAT is in P: the program on the length-prefixed word is a polynomial-time word RAM
computation of the decision on the zeros and ones of the word, in the sense of `lax-759944`,
and `ToP.lean` carries that to the class.
-/

namespace Lax117284Proofs.TwoSAT.Machine.FinalP

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax429075.CNF Lax117284.TwoSatCNF Lax117284Proofs.TwoSAT.Machine.Scan Lax117284Proofs.TwoSAT.Machine.Main
open Lax117284Proofs.TwoSAT.Machine.Final Lax117284Proofs.TwoSAT.Machine.Language Lax117284Proofs.TwoSAT.Machine.ToP
open Lax391470Proofs.ReadAll Lax391470Proofs.Bits
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax391470Proofs.BitSize
open scoped Classical

/-- The largest entry of a word. -/
def Mx (y : List ℕ) : ℕ := y.foldr max 0

lemma le_Mx {y : List ℕ} {v : ℕ} (hv : v ∈ y) : v ≤ Mx y := by
  induction y with
  | nil => cases hv
  | cons a t ih =>
    simp only [Mx, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp hv with rfl | h
    · omega
    · have := ih h; omega

lemma Mx_mem_or_zero (y : List ℕ) : Mx y ∈ y ∨ Mx y = 0 := by
  induction y with
  | nil => right; rfl
  | cons a t ih =>
    simp only [Mx, List.foldr_cons] at ih ⊢
    rcases Nat.le_total a (List.foldr max 0 t) with h | h
    · rw [Nat.max_eq_right h]
      rcases ih with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · right; exact h'
    · rw [Nat.max_eq_left h]; exact Or.inl List.mem_cons_self

/-- The value bound on an arbitrary word. -/
def Bd2 (y : List ℕ) : ℕ := 5 * y.length + 25 + Mx y

/-- The cost of the program on the length-prefixed word. -/
noncomputable def KPre (y : List ℕ) : ℕ := (12 * y.length + 10) + Kbody y

lemma wvars_readAll : readAll.wvars = ["L", "rt", "rv", "rt"] := by
  simp [readAll, readLoop, readBody, Com.wvars]
lemma warrs_readAll : readAll.warrs = ["a"] := by
  simp [readAll, readLoop, readBody, Com.warrs]

/-- **The program on the length-prefixed word.** -/
theorem mainPre_run (y : List ℕ) :
    ∃ σ', Run (Bd2 y) mainPre (initEnv (ext y) (y.length :: y)) σ' (KPre y) ∧
      σ'.out = decBits y := by
  have hB : 5 * y.length + 24 < Bd2 y := by unfold Bd2; omega
  have hyB : ∀ v ∈ y, v < Bd2 y := fun v hv => by have := le_Mx hv; unfold Bd2; omega
  set σ0 := initEnv (ext y) (y.length :: y) with hσ0
  obtain ⟨σ1, r1, ⟨hL1, ha1, hout1, -⟩, fv1, fa1, -, -⟩ :=
    (readAll_spec (B := Bd2 y) (y := y) hyB (by unfold Bd2; omega)).frame.run (σ := σ0)
      ⟨rfl, rfl, by simp [hσ0, initEnv, ext]⟩
  have hpost : ReadPost y (ext y) σ1 := by
    refine ⟨hL1, ha1, hout1, ?_, ?_⟩
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      rw [fv1 z (by rw [wvars_readAll]; simp; tauto)]
      rfl
    · intro b hb
      rw [fa1 b (by rw [warrs_readAll]; simp [hb])]
      rfl
  obtain ⟨σ2, r2, hout⟩ := (body_spec (B := Bd2 y) hB hyB).run hpost
  refine ⟨σ2, (r1.seq r2).mono (by unfold KPre; omega), ?_⟩
  rw [hout, decBits_eq]
  split <;> rfl

/-! ### The machine program -/

/-- The physical inputs: a word preceded by its length. -/
def Shape : Set (List ℕ) := {y | y ≠ [] ∧ y.headD 0 = y.tail.length}

lemma shape_eq {y : List ℕ} (h : y ∈ Shape) : y = y.tail.length :: y.tail := by
  obtain ⟨hne, hh⟩ := h
  rcases y with _ | ⟨a, t⟩
  · exact absurd rfl hne
  · simp only [List.headD_cons, List.tail_cons] at hh ⊢
    rw [hh]

theorem solves : Solves layout mainPre Shape (fun x => decBits x.tail)
    (fun x => Bd2 x.tail) (fun x => KPre x.tail) where
  ok := mainPre_ok
  inp := by
    intro x hx v hv
    rw [shape_eq hx] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · unfold Bd2; omega
    · have := le_Mx hv'; unfold Bd2; omega
  run := by
    intro x hx
    obtain ⟨σ', hrun, hout⟩ := mainPre_run x.tail
    rw [← shape_eq hx] at hrun
    exact ⟨_, σ', hrun, hout⟩

def prog : Program := compileProgram layout mainPre

theorem prog_runs (w : ℕ) (x : List ℕ) (hfit : 56 + 12 * Bd2 x ≤ 2 ^ w) :
    ∃ t ≤ 10 * KPre x + 1, RunsTo w prog (x.length :: x) (decBits x) t := by
  have hs : Solves layout mainPre {z | z = x.length :: x} (fun z => decBits z.tail)
      (fun z => Bd2 z.tail) (fun z => KPre z.tail) :=
    ⟨solves.ok, fun z hz => solves.inp z (by rw [hz]; exact ⟨by simp, by simp⟩),
      fun z hz => solves.run z (by rw [hz]; exact ⟨by simp, by simp⟩)⟩
  have h := computesInTime_of_solves (w := w) (T := fun z => 10 * KPre z.tail + 1) hs
    (fun z hz => by
      rw [hz]; simp only [List.tail_cons]
      refine fitsWords_of_max_le (by unfold Bd2; omega) ?_
      simp only [Layout.span, layout, List.length_cons, List.length_nil, max_le_iff]
      omega)
    (fun z hz => by simp [Layout.const])
  obtain ⟨t, ht, hrun⟩ := h (x.length :: x) rfl
  exact ⟨t, by simpa using ht, by simpa [prog] using hrun⟩

/-! ### Fitting into a word, and the polynomial -/

/-- The constant of the fitting condition. -/
def cfit : ℕ := 900

lemma fit_of (w : ℕ) (x : List ℕ)
    (h : ∀ v ∈ (x.length :: x), cfit * ((x.length + 1) + v + 1) ^ 2 ≤ 2 ^ w) :
    56 + 12 * Bd2 x ≤ 2 ^ w := by
  obtain ⟨v, hv, hT⟩ : ∃ v ∈ (x.length :: x), x.length + Mx x + 2 ≤ (x.length + 1) + v + 1 := by
    rcases Mx_mem_or_zero x with hm | hm
    · exact ⟨Mx x, List.mem_cons_of_mem _ hm, by omega⟩
    · exact ⟨x.length, List.mem_cons_self, by omega⟩
  have hpow := Nat.pow_le_pow_left hT 2
  have hc := Nat.mul_le_mul_left cfit hpow
  refine le_trans ?_ (le_trans hc (h v hv))
  set T := x.length + Mx x + 2 with hTdef
  have hTT : T ≤ T * T := Nat.le_mul_of_pos_left _ (by omega)
  have e : cfit * T ^ 2 = 900 * (T * T) := by unfold cfit; ring
  rw [e]
  unfold Bd2
  omega

/-- The scale of the time bound. -/
def sc : ℕ := 8000

lemma KPre_le (x : List ℕ) : 10 * KPre x + 1 ≤ sc * (bitSize x + 1) ^ 2 := by
  have hlen := length_le_bitSize x
  have h1 := KRaw_le x
  have hv : Lax117284.TwoSatRunningTime.wordVarCount x ≤ x.length := by
    unfold Lax117284.TwoSatRunningTime.wordVarCount
    rw [bitsOf_eq, Lax391470Proofs.CnfScan.decodeCNF_eq]
    split
    · next h =>
      have := varCount_le (formulaOf x)
      have := (sizes_le (y := x) h).1
      show varCount (formulaOf x) ≤ x.length
      omega
    · simp
  have hK : KPre x ≤ KRaw x := by unfold KPre KRaw; omega
  have h2 : c0 * (x.length + 1) * (Lax117284.TwoSatRunningTime.wordVarCount x + 1) ≤
      c0 * (bitSize x + 1) * (bitSize x + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e : sc * (bitSize x + 1) ^ 2 = c0 * (bitSize x + 1) * (bitSize x + 1) := by
    unfold sc c0; ring
  rw [e]
  calc 10 * KPre x + 1 ≤ 10 * KRaw x + 2 := by omega
    _ ≤ c0 * (x.length + 1) * (Lax117284.TwoSatRunningTime.wordVarCount x + 1) := h1
    _ ≤ c0 * (bitSize x + 1) * (bitSize x + 1) := h2

/-- **The decision is a polynomial-time word RAM computation on the bits.** -/
theorem ramPolytime_decBits : RamPolytime decBits := by
  have hK : cfit * 4 ^ 2 ≤ 2 ^ (16 * cfit).size := by
    have := Nat.lt_size_self (16 * cfit)
    omega
  refine Lax391470Proofs.RamBridge.ramPolytime_of_poly (c := cfit) (d := 2)
    (K := (16 * cfit).size) (prog := prog)
    (Polynomial.C sc * (Polynomial.X + Polynomial.C 1) ^ 2)
    (by omega) hK ?_ ?_
  · intro x v hv
    have h1 : v ≤ 1 := by
      rw [decBits_eq] at hv
      split at hv <;> simp at hv <;> omega
    have h2 : 2 ≤ 2 ^ (2 * bitSize x + (16 * cfit).size) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by omega)
        (show 1 ≤ 2 * bitSize x + (16 * cfit).size by
          have : 0 < 16 * cfit := by unfold cfit; omega
          have := Nat.size_pos.mpr this
          omega))
    omega
  · intro w x hfits
    obtain ⟨t, ht, hrun⟩ := prog_runs w x (fit_of w x hfits)
    refine ⟨t, ?_, hrun⟩
    have := KPre_le x
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    omega

/--
---
conclusion: Lax117284.TwoSatInP.twoSAT_mem_P
---
The program on the length-prefixed word is a polynomial-time word RAM computation of the
decision on the zeros and ones of the word, with all values polynomially bounded; the RAM/Turing
equivalence of `lax-759944` and the two translations of `lax-391470` give a polynomial-time Turing
machine on the binary word, and a machine writing the one bit of the answer is a machine for the
class.
-/
theorem twoSAT_mem_P : TwoSAT ∈ Lax434930.PolynomialTime.P :=
  mem_P_of_ram ramPolytime_decBits

end Lax117284Proofs.TwoSAT.Machine.FinalP
