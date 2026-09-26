import Lax117284Proofs.Machine.TwForget1

/-!
The program of a forget node: the size and the parameters of the table, and the table's loop
over the forgotten digit.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- Store the size, and set the parameters of the fill of the table. -/
def forgetMid : Com := seqs
  [ .store "SZ" (V "i") (V "s1"),
    .assign "Pp" (.bin .shiftl (L 1) (mul (V "m") (V "p"))),
    .assign "shp1" (mul (V "m") (V "p")),
    .assign "cbase" (mul (V "c") (V "Tm")),
    .assign "bs" (mul (V "i") (V "Tm")),
    .assign "fn" (.bin .shiftl (L 1) (mul (V "m") (V "s1"))) ]

/-- The state after `forgetMid`. -/
def midStateF (P : Params) (i0 : ℕ) (σ : Env) : Env :=
  ((((σ.setArr "SZ" (i0 + 1) ((bagL P.D i0).length - 1)).setVar "Pp"
    (2 ^ (P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1))))).setVar "shp1"
    (P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1)))).setVar "cbase" (i0 * P.tabs)).setVar
    "bs" ((i0 + 1) * P.tabs) |>.setVar "fn" (2 ^ (P.m * ((bagL P.D i0).length - 1)))

theorem forgetMid_run {i0 : ℕ} (h : HQf P B i0 σ) :
    ∃ σ', Run B forgetMid σ σ' 100 ∧ σ' = midStateF P i0 σ := by
  have hC := h.C
  have hiN := h.iN
  have hl1 := bagL_forget_len P h.iN h.k_
  have hpl := bagL_forget_facts P h.iN h.k_
  have hle0 := bagL_len_le P (j := i0) (by omega)
  have hb1 := hC.b1
  have hb9 := hC.b9
  have hb3 := hC.b3
  have hb2 := hC.b2
  have hlenSZ := hC.lenSZ
  have hNt : (i0 + 2) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ h.iN
  have hi2 : (i0 + 2) * P.tabs = i0 * P.tabs + P.tabs + P.tabs := by ring
  have hi1 : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
  have hp1 : 2 ^ (P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1))) ≤ P.tabs :=
    pow_le_tabs P (by omega)
  have hp2 : 2 ^ (P.m * ((bagL P.D i0).length - 1)) ≤ P.tabs := pow_le_tabs P (by omega)
  have hmp : P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1)) ≤ P.m * P.wid :=
    Nat.mul_le_mul_left _ (by omega)
  have hms1 : P.m * ((bagL P.D i0).length - 1) ≤ P.m * P.wid := Nat.mul_le_mul_left _ (by omega)
  have hmw : P.m * (P.wid + 1) = P.m * P.wid + P.m := by ring
  have hct : i0 * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ (by omega)
  unfold forgetMid seqs
  run_vcg
  all_goals (try nrmA)
  all_goals try (first | omega | (simp only [h.i_, h.s1_, hC.m_, h.p_, hC.Tm_, h.c_, one_mul]; omega))
  all_goals (try simp only [midStateF, h.i_, h.s1_, hC.m_, h.p_, hC.Tm_, h.c_, one_mul])

/-! ### The loop over the forgotten digit -/

lemma lor_le_one {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : Nat.lor a b ≤ 1 := by
  interval_cases a <;> interval_cases b <;> decide

/-- **The fold of `or` over the digits is the existence of a one.** -/
lemma or_fold (N : ℕ) (T : ℕ → ℕ) (hT : ∀ j < N, T j ≤ 1) : ∀ M ≤ N,
    (List.range M).foldl (fun a j => if j < N then Nat.lor a (T j) else a) 0 =
      if ∃ j < M, T j = 1 then 1 else 0
  | 0, _ => by simp
  | M + 1, hM => by
    rw [List.range_succ, List.foldl_append, or_fold N T hT M (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, if_pos (show M < N by omega)]
    have h1 := hT M (by omega)
    by_cases hex : ∃ j < M, T j = 1
    · have hex' : ∃ j < M + 1, T j = 1 := by
        obtain ⟨j, hj, e⟩ := hex; exact ⟨j, by omega, e⟩
      rw [if_pos hex, if_pos hex']
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h | h <;> simp [h]
    · rw [if_neg hex]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h | h
      · have : ¬ ∃ j < M + 1, T j = 1 := by
          rintro ⟨j, hj, e⟩
          by_cases hjm : j < M
          · exact hex ⟨j, hjm, e⟩
          · have : j = M := by omega
            subst this; omega
        rw [if_neg this]; simp [h]
      · rw [if_pos ⟨M, by omega, h⟩]; simp [h]

/-- One step of the loop over the forgotten digit. -/
def forgetBody : Com :=
  .seq (.assign "ix" (add (add (V "lo") (mul (V "so") (V "Pp"))) (V "hi")))
    (.assign "ac" (.bin .or (V "ac") (G "TB" (add (V "cbase") (V "ix")))))

theorem forgetBody_run (σ : Env)
    (hidx : σ.vars "cbase" + (σ.vars "lo" + σ.vars "so" * σ.vars "Pp" + σ.vars "hi") <
      (σ.arrs "TB").length)
    (hixB : σ.vars "cbase" + (σ.vars "lo" + σ.vars "so" * σ.vars "Pp" + σ.vars "hi") < B)
    (hac : σ.vars "ac" ≤ 1)
    (hT : (σ.arrs "TB").getD (σ.vars "cbase" +
      (σ.vars "lo" + σ.vars "so" * σ.vars "Pp" + σ.vars "hi")) 0 ≤ 1) (hB : 2 < B)
    (hso : σ.vars "so" < B) (hPp : σ.vars "Pp" < B) :
    ∃ σ', Run B forgetBody σ σ' 30 ∧
      σ'.vars "ac" = Nat.lor (σ.vars "ac") ((σ.arrs "TB").getD (σ.vars "cbase" +
        (σ.vars "lo" + σ.vars "so" * σ.vars "Pp" + σ.vars "hi")) 0) ∧
      Agr ["ix", "ac"] σ σ' ∧ σ'.vars "so" = σ.vars "so" ∧ σ'.out = σ.out := by
  have hlor := lor_le_one hac hT
  unfold forgetBody
  run_vcg
  all_goals try (nrmA; first | omega | exact lt_of_le_of_lt hlor (by omega))
  refine ⟨?_, ⟨rfl, fun y hy => ?_⟩, ?_, rfl⟩
  · nrmA
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [Env.setVar, hy.1, hy.2]
  · nrmA

end Lax117284Proofs.Machine.TwNode
