import Lax117284Proofs.Machine.ClBuildOk2

/-!
The word of the program, entry by entry: the entry at position `idx` is the count, a coefficient,
or a right-hand side, by the formula `zFunRaw`.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The coefficient of variable `fc` in constraint `fr`, into `cf`. -/
def coefCom : Com := seqs [
  asg "cf" (lit 0),
  .ite (.lt (V "fc") (V "Vv"))
    (.ite (.eq (.get "okt" (V "fc")) (lit 1))
      (.ite (.lt (V "fr") (V "T"))
        (.ite (.eq (V "ct") (V "fr")) (asg "cf" (lit 1)) .skip)
        (.ite (.eq (bitE (V "cs") (sub (V "fr") (V "T"))) (lit 0)) (asg "cf" (lit 1)) .skip))
      .skip)
    (.ite (.lt (V "fr") (V "T")) .skip
      (.ite (.eq (sub (V "fc") (V "Vv")) (sub (V "fr") (V "T"))) (asg "cf" (lit 1)) .skip))]

/-- The position `fq` of the matrix, as row `fr` and column `fc`, the column as type and subset. -/
def idxCom : Com := seqs [
  asg "fq" (sub (V "idx") (lit 2)), asg "fr" (dv (V "fq") (V "N")),
  asg "fc" (sub (V "fq") (mul (V "fr") (V "N"))),
  asg "ct" (dv (V "fc") (V "Z")), asg "cs" (sub (V "fc") (mul (V "ct") (V "Z")))]

/-- Store `cf` into the word. -/
def zStore : Com := .store "z" (V "idx") (V "cf")

/-- A coefficient. -/
def coefPart : Com := .seq idxCom (.seq coefCom zStore)

/-- The right-hand side into `cf`. -/
def rhsCom : Com := seqs [
  asg "fr" (sub (sub (V "idx") (lit 2)) (mul (V "M") (V "N"))),
  .ite (.lt (V "fr") (V "T")) (asg "cf" (.get "cnt" (V "fr"))) (asg "cf" (sub (V "m") (V "k")))]

/-- A right-hand side. -/
def rhsPart : Com := .seq rhsCom zStore

/-- One entry of the word. -/
def zBody : Com :=
  .ite (.eq (V "idx") (lit 0)) (.store "z" (V "idx") (V "N"))
    (.ite (.eq (V "idx") (lit 1)) (.store "z" (V "idx") (V "M"))
      (.ite (.lt (V "idx") (add (lit 2) (mul (V "M") (V "N")))) coefPart rhsPart))

/-- The word. -/
def fillCom : Com := seqs [asg "idx" (lit 0), .while (.lt (V "idx") (V "zl")) (.seq zBody (asg "idx" (add (V "idx") (lit 1))))]

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The state at the coefficient: the table of independent pairs and the coordinates. -/
def CoefPre (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ (σ.arrs "okt").length = nV I.clients ∧
    (∀ c < nV I.clients, (σ.arrs "okt").getD c 0 =
      if indepB I.clients (c / nZ I.clients) (c % nZ I.clients) = true then 1 else 0) ∧
    σ.vars "ct" = σ.vars "fc" / nZ I.clients ∧ σ.vars "cs" = σ.vars "fc" % nZ I.clients ∧
    σ.vars "fr" < nM I.clients ∧ σ.vars "fc" < nN I.clients

set_option maxHeartbeats 3200000 in
theorem coefCom_spec (h : Bh I x k B) :
    Spec B (CoefPre I x k) coefCom
      (fun σ σ' => σ'.vars "cf" = coefRaw I.clients (σ.vars "fr") (σ.vars "fc") ∧
        AgreeOff ["cf"] σ σ') 100 := by
  have hV := h.nT_lt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hB3 : 2 < B := by have := h.mn_le; omega
  run_vcg
  all_goals
    obtain ⟨hC, hS, hlen, hok, hct, hcs, hfr, hfc⟩ := ‹CoefPre I x k _›
    have hd1 : σ.vars "fc" / nZ I.clients ≤ σ.vars "fc" := Nat.div_le_self _ _
    have hd2 : σ.vars "fc" % nZ I.clients ≤ σ.vars "fc" := Nat.mod_le _ _
    have hd5 : σ.vars "fc" % nZ I.clients / 2 ^ (σ.vars "fr" - nT I.clients) ≤ σ.vars "fc" % nZ I.clients := Nat.div_le_self _ _
    have hd3 : σ.vars "fr" < B := by omega
    have hd4 : σ.vars "fc" < B := by omega
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
  all_goals try
    refine ⟨?_, rfl, rfl, rfl, fun y hy => ?_⟩
  all_goals try
    (simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
     simp [Env.setVar, hy])
  all_goals try simp [Env.setVar, coefRaw, hS.Vv, hS.T, hS.Z, hct, hcs, Nat.testBit_eq_decide_div_mod_eq]
  all_goals try simp_all [coefRaw, hS.Vv, hS.T, hS.Z, hct, hcs, hok, Nat.testBit_eq_decide_div_mod_eq]
  all_goals try omega
  all_goals try (split_ifs <;> simp_all <;> omega)

end Lax117284Proofs.Machine.ClBuild
