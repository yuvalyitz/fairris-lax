import Lax117284Proofs.Machine.TwIntro

/-!
The program of an introduce node, continued: the size, the parameters of the table, and the table.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

lemma bpow (P : Params) (s : ℕ) : (2 ^ P.I.days) ^ s = 2 ^ (P.m * s) := by
  rw [← pow_mul]; rfl

lemma pow_le_tabs (P : Params) {s : ℕ} (hs : s ≤ P.wid) : 2 ^ (P.m * s) ≤ P.tabs := by
  unfold Params.tabs Params.bs
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hs)

section Tbv

variable {I : Lax117284.Scheduling.Instance} {kk : ℕ} {D : List ℕ} {j e : ℕ}

lemma tbv_one (h : TB I kk D j e) : tbv I kk D j e = 1 := by unfold tbv; simp [h]

lemma tbv_zero (h : ¬ TB I kk D j e) : tbv I kk D j e = 0 := by unfold tbv; simp [h]

lemma tbv_le_one : tbv I kk D j e ≤ 1 := by
  by_cases h : TB I kk D j e
  · rw [tbv_one h]
  · rw [tbv_zero h]; omega

/-- **The table entry of an introduce node**, as a number. -/
lemma tbv_intro {i : ℕ} (hk : kind D (i + 1) = 1) :
    tbv I kk D (i + 1) e = if violE I kk (bagL D (i + 1)) e = 0 then
      tbv I kk D i (rmN (2 ^ I.days) (pos (bagL D i) (vertex D (i + 1))) e) else 0 := by
  by_cases h : violE I kk (bagL D (i + 1)) e = 0
  · rw [if_pos h]
    have h1 := (violE_eq_zero I kk _ e).1 h
    by_cases h2 : TB I kk D i (rmN (2 ^ I.days) (pos (bagL D i) (vertex D (i + 1))) e)
    · rw [tbv_one ((TB_intro hk).2 ⟨h1.1, h1.2, h2⟩), tbv_one h2]
    · rw [tbv_zero (fun h' => h2 ((TB_intro hk).1 h').2.2), tbv_zero h2]
  · rw [if_neg h]
    exact tbv_zero (fun h' => h ((violE_eq_zero I kk _ e).2
      ⟨((TB_intro hk).1 h').1, ((TB_intro hk).1 h').2.1⟩))

end Tbv

/-! ### The size and the parameters of the table -/

/-- Store the size, and set the parameters of the fill of the table. -/
def introMid : Com := seqs
  [ .store "SZ" (V "i") (V "s1"),
    .assign "Pp" (.bin .shiftl (L 1) (mul (V "m") (V "p"))),
    .assign "shp1" (mul (V "m") (add (V "p") (L 1))),
    .assign "cbase" (mul (V "c") (V "Tm")),
    .assign "off" (V "iw"),
    .assign "vs" (V "s1"),
    .assign "bs" (mul (V "i") (V "Tm")),
    .assign "fn" (.bin .shiftl (L 1) (mul (V "m") (V "s1"))) ]

/-- The state after `introMid`. -/
def midState (P : Params) (i0 : ℕ) (σ : Env) : Env :=
  (((((((σ.setArr "SZ" (i0 + 1) ((bagL P.D i0).length + 1)).setVar "Pp"
    (2 ^ (P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1))))).setVar "shp1"
    (P.m * (pos (bagL P.D i0) (vertex P.D (i0 + 1)) + 1))).setVar "cbase" (i0 * P.tabs)).setVar
    "off" ((i0 + 1) * P.wid)).setVar "vs" ((bagL P.D i0).length + 1)).setVar "bs"
    ((i0 + 1) * P.tabs)).setVar "fn" (2 ^ (P.m * ((bagL P.D i0).length + 1)))

theorem introMid_run {i0 : ℕ} (h : HQ P B i0 σ) :
    ∃ σ', Run B introMid σ σ' 100 ∧ σ' = midState P i0 σ := by
  have hC := h.C
  have hiN := h.iN
  have hl1 := bagL_intro_len P h.k_
  have hle1 := bagL_len_le P (j := i0 + 1) h.iN
  have hb1 := hC.b1
  have hb9 := hC.b9
  have hb3 := hC.b3
  have hb2 := hC.b2
  have hiw : (i0 + 1) * P.wid ≤ P.N * P.wid := Nat.mul_le_mul_right _ (by omega)
  have hpl : pos (bagL P.D i0) (vertex P.D (i0 + 1)) ≤ (bagL P.D i0).length := pos_le_length
  have hlenSZ := hC.lenSZ
  have hNt : (i0 + 2) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ h.iN
  have hi2 : (i0 + 2) * P.tabs = i0 * P.tabs + P.tabs + P.tabs := by ring
  have hi1 : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
  have hp1 : 2 ^ (P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1))) ≤ P.tabs :=
    pow_le_tabs P (by omega)
  have hp2 : 2 ^ (P.m * ((bagL P.D i0).length + 1)) ≤ P.tabs := pow_le_tabs P (by omega)
  have hmp : P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1)) ≤ P.m * P.wid :=
    Nat.mul_le_mul_left _ (by omega)
  have hmp1 : P.m * (pos (bagL P.D i0) (vertex P.D (i0 + 1)) + 1) ≤ P.m * P.wid :=
    Nat.mul_le_mul_left _ (by omega)
  have hms1 : P.m * ((bagL P.D i0).length + 1) ≤ P.m * P.wid := Nat.mul_le_mul_left _ (by omega)
  have hmw : P.m * (P.wid + 1) = P.m * P.wid + P.m := by ring
  have hct : i0 * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ (by omega)
  unfold introMid seqs
  run_vcg
  all_goals (try nrmA)
  all_goals try (first | omega | (simp only [h.i_, h.s1_, hC.m_, h.p_, hC.Tm_, h.c_, h.iw_, one_mul]; omega))
  all_goals (try simp only [midState, h.i_, h.s1_, hC.m_, h.p_, hC.Tm_, h.c_, h.iw_, one_mul])

end Lax117284Proofs.Machine.TwNode
