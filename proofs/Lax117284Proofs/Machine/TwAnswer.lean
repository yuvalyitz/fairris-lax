import Lax117284Proofs.Machine.TwLoop3

/-!
The answer: some restriction is in the table of the last node.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- One step of the search for a one in the last row of the table. -/
def orBody : Com := .assign "ac" (.bin .or (V "ac") (G "TB" (add (V "bs") (V "so"))))

theorem orBody_run (σ : Env) (hidx : σ.vars "bs" + σ.vars "so" < (σ.arrs "TB").length)
    (hixB : σ.vars "bs" + σ.vars "so" < B) (hac : σ.vars "ac" ≤ 1)
    (hT : (σ.arrs "TB").getD (σ.vars "bs" + σ.vars "so") 0 ≤ 1) (hB : 2 < B)
    (hso : σ.vars "so" < B) (hbs : σ.vars "bs" < B) :
    ∃ σ', Run B orBody σ σ' 20 ∧
      σ'.vars "ac" = Nat.lor (σ.vars "ac") ((σ.arrs "TB").getD (σ.vars "bs" + σ.vars "so") 0) ∧
      Agr ["ac"] σ σ' ∧ σ'.vars "so" = σ.vars "so" ∧ σ'.out = σ.out := by
  have hlor := lor_le_one hac hT
  unfold orBody
  run_vcg
  all_goals try (nrmA; first | omega | exact lt_of_le_of_lt hlor (by omega))
  refine ⟨?_, ⟨rfl, fun y hy => ?_⟩, ?_, rfl⟩
  · nrmA
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [Env.setVar, hy]
  · nrmA

/-- The loop over the last row of the table. -/
def orLoop : Com := fLoop "so" "fn" orBody

/-- The preparation of the answer: the last node, its size, the search range. -/
def answerPre : Com := seqs
  [ .assign "c" (sub (V "N") (L 1)),
    .assign "s" (G "SZ" (V "c")),
    .assign "bs" (mul (V "c") (V "Tm")),
    .assign "fn" (.bin .shiftl (L 1) (mul (V "m") (V "s"))),
    .assign "ac" (L 0) ]

/-- **The answer.** -/
def answerCom : Com := .seq answerPre (.seq orLoop (.write (V "ac")))

/-- The state after `answerPre`. -/
def preState (P : Params) (σ : Env) : Env :=
  ((((σ.setVar "c" (P.N - 1)).setVar "s" (bagL P.D (P.N - 1)).length).setVar "bs"
    ((P.N - 1) * P.tabs)).setVar "fn" (2 ^ (P.m * (bagL P.D (P.N - 1)).length))).setVar "ac" 0

theorem answerPre_run (hC : NC P B σ) (hN : NI P.I P.kk P.D P.wid P.tabs P.N σ) :
    ∃ σ1, Run B answerPre σ σ1 60 ∧ σ1 = preState P σ := by
  have hNpos : 0 < P.N := P.hD.nonempty
  have hsz := hN.sz (P.N - 1) (by omega)
  have hle := bagL_len_le P (j := P.N - 1) (by omega)
  have hb1 := hC.b1
  have hb3 := hC.b3
  have hb9 := hC.b9
  have hb2 := hC.b2
  have hNt : (P.N - 1) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ (by omega)
  have hpt : 2 ^ (P.m * (bagL P.D (P.N - 1)).length) ≤ P.tabs := pow_le_tabs P hle
  have hms : P.m * (bagL P.D (P.N - 1)).length ≤ P.m * P.wid := Nat.mul_le_mul_left _ hle
  have hmw : P.m * (P.wid + 1) = P.m * P.wid + P.m := by ring
  have hlenSZ := hC.lenSZ
  unfold answerPre seqs
  run_vcg
  all_goals (try nrmA)
  all_goals try (first | omega | (simp only [hC.N_, hC.Tm_, hC.m_, hsz, one_mul]; omega))
  all_goals (try simp only [preState, hC.N_, hC.Tm_, hC.m_, hsz, one_mul])

end Lax117284Proofs.Machine.TwNode
