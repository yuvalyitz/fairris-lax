import Lax117284Proofs.Machine.MisPrint
import Lax117284Proofs.Machine.MisChk
import Lax117284Proofs.Machine.FreeAccept

/-!
The whole of the reduction of Lemma 14 after the tokenizer has accepted: read the counts off the
array, check the matrix, derive the numbers of the image, and write the image or the rejected word.
-/

namespace Lax117284Proofs.Machine.MisAccept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.MisBlk Lax117284Proofs.Machine.MisSem
open Lax117284Proofs.Machine.MisPrint Lax117284Proofs.Machine.MisChk
open Lax117284Proofs.Machine.SatOps (asg_tkl)
open Lax117284Proofs.Machine.FreeAccept (rejectPrint rejectPrint_run)
open Lax117284Proofs.Machine.MisJob (Mag)
open Lax117284Proofs.Machine.MisFormat (VM)

variable {B : ℕ}

/-- Read the counts off the array. -/
def prepM : Com :=
  .seq (.assign "nn" (.get "TK" (.lit 1)))
  (.seq (.assign "lc" (.get "TK" (.lit 0)))
  (.seq (.assign "V" (.bin .mul (V "lc") (V "nn")))
        (.assign "VV" (.bin .mul (V "V") (V "V")))))

/-- The fairness degree of the vertex `0`. -/
def dgM : Com := .ite (.lt (V "rr") (.lit 1)) (.assign "dg" (.lit 1)) (.assign "dg" (V "rr"))

/-- The rest of the numbers of the image, from the degree. -/
def postTail : Com :=
  .seq (.assign "S2" (.bin .add (.bin .add (.bin .add (.lit 2) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg"))))
  (.seq (.assign "CC" (.bin .add (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg"))))
  (.seq (.assign "B3" (.bin .add (.lit 3) (V "lc")))
  (.seq (.assign "B4" (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")))
  (.seq (.assign "dn" (.bin .mul (V "dg") (V "nn")))
  (.seq (.assign "nn1" (.bin .add (V "nn") (.lit 1)))
  (.seq (.assign "LB" (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))))
  (.seq (.assign "DD" (.bin .add (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))) (V "EE")))
  (.seq (.assign "E2" (.bin .div (V "EE") (.lit 2)))
        (.assign "DC" (.bin .mul (.bin .add (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))) (V "EE")) (.bin .add (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg")))))))))))))

/-- Derive the numbers of the image from the check. -/
def postM : Com := .seq dgM postTail

/-- The scalars the derivation assigns, apart from the degree. -/
def APT : List String := ["S2", "CC", "B3", "B4", "dn", "nn1", "LB", "DD", "E2", "DC"]

/-- The whole of the reduction, after the tokenizer has accepted. -/
def acceptM : Com :=
  .seq prepM (.seq checkCom (.ite (.eq (V "ok") (.lit 1)) (.seq postM printM) rejectPrint))

set_option maxHeartbeats 12800000 in
/-- The rest of the numbers, on plain numbers. -/
theorem postTail_run (σ : Env) (l n Vn E d : ℕ) (hnn : σ.vars "nn" = n) (hlc : σ.vars "lc" = l)
    (hV : σ.vars "V" = Vn) (hEE : σ.vars "EE" = E) (hdg : σ.vars "dg" = d)
    (b0 : d < B) (b1 : Vn * d < B) (b2 : 3 + l + Vn + Vn * d < B) (b3 : d * n < B) (b4 : n + 1 < B)
    (b5 : l * (n + 1) + E < B) (b6 : (l * (n + 1) + E) * (3 + l + Vn + Vn * d) < B) :
    ∃ σ', Run B postTail σ σ' 300 ∧ σ'.vars "S2" = 2 + l + Vn + Vn * d ∧
      σ'.vars "CC" = 3 + l + Vn + Vn * d ∧ σ'.vars "B3" = 3 + l ∧ σ'.vars "B4" = 3 + l + Vn ∧
      σ'.vars "dn" = d * n ∧ σ'.vars "nn1" = n + 1 ∧ σ'.vars "LB" = l * (n + 1) ∧
      σ'.vars "DD" = l * (n + 1) + E ∧ σ'.vars "E2" = E / 2 ∧
      σ'.vars "DC" = (l * (n + 1) + E) * (3 + l + Vn + Vn * d) ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ ∀ y, y ∉ APT → σ'.vars y = σ.vars y := by
  have nn0_ := hnn
  have lc0_ := hlc
  have V0_ := hV
  have EE0_ := hEE
  have dg0_ := hdg
  have s1 := asgE (B := B) "S2" (.bin .add (.bin .add (.bin .add (.lit 2) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg"))) σ (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, nn0_, lc0_, V0_, EE0_, dg0_]; omega)
  set σ1 := σ.setVar "S2" (den σ (.bin .add (.bin .add (.bin .add (.lit 2) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg")))) with hσ1
  have v1_ : σ1.vars "S2" = 2 + l + Vn + Vn * d := by
    simp only [hσ1, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, Env.setVar, nn0_, lc0_, V0_, EE0_, dg0_, if_true]
  have nn1_ : σ1.vars "nn" = n := by simp [hσ1, Env.setVar, nn0_]
  have lc1_ : σ1.vars "lc" = l := by simp [hσ1, Env.setVar, lc0_]
  have V1_ : σ1.vars "V" = Vn := by simp [hσ1, Env.setVar, V0_]
  have EE1_ : σ1.vars "EE" = E := by simp [hσ1, Env.setVar, EE0_]
  have dg1_ : σ1.vars "dg" = d := by simp [hσ1, Env.setVar, dg0_]
  have s2 := asgE (B := B) "CC" (.bin .add (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg"))) σ1 (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, nn1_, lc1_, V1_, EE1_, dg1_]; omega)
  set σ2 := σ1.setVar "CC" (den σ1 (.bin .add (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg")))) with hσ2
  have v2_ : σ2.vars "CC" = 3 + l + Vn + Vn * d := by
    simp only [hσ2, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, Env.setVar, nn1_, lc1_, V1_, EE1_, dg1_, if_true]
  have nn2_ : σ2.vars "nn" = n := by simp [hσ2, Env.setVar, nn1_]
  have lc2_ : σ2.vars "lc" = l := by simp [hσ2, Env.setVar, lc1_]
  have V2_ : σ2.vars "V" = Vn := by simp [hσ2, Env.setVar, V1_]
  have EE2_ : σ2.vars "EE" = E := by simp [hσ2, Env.setVar, EE1_]
  have dg2_ : σ2.vars "dg" = d := by simp [hσ2, Env.setVar, dg1_]
  have s3 := asgE (B := B) "B3" (.bin .add (.lit 3) (V "lc")) σ2 (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, nn2_, lc2_, V2_, EE2_, dg2_]; omega)
  set σ3 := σ2.setVar "B3" (den σ2 (.bin .add (.lit 3) (V "lc"))) with hσ3
  have v3_ : σ3.vars "B3" = 3 + l := by
    simp only [hσ3, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, Env.setVar, nn2_, lc2_, V2_, EE2_, dg2_, if_true]
  have nn3_ : σ3.vars "nn" = n := by simp [hσ3, Env.setVar, nn2_]
  have lc3_ : σ3.vars "lc" = l := by simp [hσ3, Env.setVar, lc2_]
  have V3_ : σ3.vars "V" = Vn := by simp [hσ3, Env.setVar, V2_]
  have EE3_ : σ3.vars "EE" = E := by simp [hσ3, Env.setVar, EE2_]
  have dg3_ : σ3.vars "dg" = d := by simp [hσ3, Env.setVar, dg2_]
  have s4 := asgE (B := B) "B4" (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")) σ3 (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, nn3_, lc3_, V3_, EE3_, dg3_]; omega)
  set σ4 := σ3.setVar "B4" (den σ3 (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V"))) with hσ4
  have v4_ : σ4.vars "B4" = 3 + l + Vn := by
    simp only [hσ4, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, Env.setVar, nn3_, lc3_, V3_, EE3_, dg3_, if_true]
  have nn4_ : σ4.vars "nn" = n := by simp [hσ4, Env.setVar, nn3_]
  have lc4_ : σ4.vars "lc" = l := by simp [hσ4, Env.setVar, lc3_]
  have V4_ : σ4.vars "V" = Vn := by simp [hσ4, Env.setVar, V3_]
  have EE4_ : σ4.vars "EE" = E := by simp [hσ4, Env.setVar, EE3_]
  have dg4_ : σ4.vars "dg" = d := by simp [hσ4, Env.setVar, dg3_]
  have s5 := asgE (B := B) "dn" (.bin .mul (V "dg") (V "nn")) σ4 (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, nn4_, lc4_, V4_, EE4_, dg4_]; omega)
  set σ5 := σ4.setVar "dn" (den σ4 (.bin .mul (V "dg") (V "nn"))) with hσ5
  have v5_ : σ5.vars "dn" = d * n := by
    simp only [hσ5, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, Env.setVar, nn4_, lc4_, V4_, EE4_, dg4_, if_true]
  have nn5_ : σ5.vars "nn" = n := by simp [hσ5, Env.setVar, nn4_]
  have lc5_ : σ5.vars "lc" = l := by simp [hσ5, Env.setVar, lc4_]
  have V5_ : σ5.vars "V" = Vn := by simp [hσ5, Env.setVar, V4_]
  have EE5_ : σ5.vars "EE" = E := by simp [hσ5, Env.setVar, EE4_]
  have dg5_ : σ5.vars "dg" = d := by simp [hσ5, Env.setVar, dg4_]
  have s6 := asgE (B := B) "nn1" (.bin .add (V "nn") (.lit 1)) σ5 (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, nn5_, lc5_, V5_, EE5_, dg5_]; omega)
  set σ6 := σ5.setVar "nn1" (den σ5 (.bin .add (V "nn") (.lit 1))) with hσ6
  have v6_ : σ6.vars "nn1" = n + 1 := by
    simp only [hσ6, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, Env.setVar, nn5_, lc5_, V5_, EE5_, dg5_, if_true]
  have nn6_ : σ6.vars "nn" = n := by simp [hσ6, Env.setVar, nn5_]
  have lc6_ : σ6.vars "lc" = l := by simp [hσ6, Env.setVar, lc5_]
  have V6_ : σ6.vars "V" = Vn := by simp [hσ6, Env.setVar, V5_]
  have EE6_ : σ6.vars "EE" = E := by simp [hσ6, Env.setVar, EE5_]
  have dg6_ : σ6.vars "dg" = d := by simp [hσ6, Env.setVar, dg5_]
  have s7 := asgE (B := B) "LB" (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))) σ6 (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, nn6_, lc6_, V6_, EE6_, dg6_]; omega)
  set σ7 := σ6.setVar "LB" (den σ6 (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1)))) with hσ7
  have v7_ : σ7.vars "LB" = l * (n + 1) := by
    simp only [hσ7, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, Env.setVar, nn6_, lc6_, V6_, EE6_, dg6_, if_true]
  have nn7_ : σ7.vars "nn" = n := by simp [hσ7, Env.setVar, nn6_]
  have lc7_ : σ7.vars "lc" = l := by simp [hσ7, Env.setVar, lc6_]
  have V7_ : σ7.vars "V" = Vn := by simp [hσ7, Env.setVar, V6_]
  have EE7_ : σ7.vars "EE" = E := by simp [hσ7, Env.setVar, EE6_]
  have dg7_ : σ7.vars "dg" = d := by simp [hσ7, Env.setVar, dg6_]
  have s8 := asgE (B := B) "DD" (.bin .add (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))) (V "EE")) σ7 (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, nn7_, lc7_, V7_, EE7_, dg7_]; omega)
  set σ8 := σ7.setVar "DD" (den σ7 (.bin .add (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))) (V "EE"))) with hσ8
  have v8_ : σ8.vars "DD" = l * (n + 1) + E := by
    simp only [hσ8, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, Env.setVar, nn7_, lc7_, V7_, EE7_, dg7_, if_true]
  have nn8_ : σ8.vars "nn" = n := by simp [hσ8, Env.setVar, nn7_]
  have lc8_ : σ8.vars "lc" = l := by simp [hσ8, Env.setVar, lc7_]
  have V8_ : σ8.vars "V" = Vn := by simp [hσ8, Env.setVar, V7_]
  have EE8_ : σ8.vars "EE" = E := by simp [hσ8, Env.setVar, EE7_]
  have dg8_ : σ8.vars "dg" = d := by simp [hσ8, Env.setVar, dg7_]
  have s9 := asgE (B := B) "E2" (.bin .div (V "EE") (.lit 2)) σ8 (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, nn8_, lc8_, V8_, EE8_, dg8_]; omega)
  set σ9 := σ8.setVar "E2" (den σ8 (.bin .div (V "EE") (.lit 2))) with hσ9
  have v9_ : σ9.vars "E2" = E / 2 := by
    simp only [hσ9, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, Env.setVar, nn8_, lc8_, V8_, EE8_, dg8_, if_true]
  have nn9_ : σ9.vars "nn" = n := by simp [hσ9, Env.setVar, nn8_]
  have lc9_ : σ9.vars "lc" = l := by simp [hσ9, Env.setVar, lc8_]
  have V9_ : σ9.vars "V" = Vn := by simp [hσ9, Env.setVar, V8_]
  have EE9_ : σ9.vars "EE" = E := by simp [hσ9, Env.setVar, EE8_]
  have dg9_ : σ9.vars "dg" = d := by simp [hσ9, Env.setVar, dg8_]
  have s10 := asgE (B := B) "DC" (.bin .mul (.bin .add (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))) (V "EE")) (.bin .add (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg")))) σ9 (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, nn9_, lc9_, V9_, EE9_, dg9_]; omega)
  set σ10 := σ9.setVar "DC" (den σ9 (.bin .mul (.bin .add (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))) (V "EE")) (.bin .add (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg"))))) with hσ10
  have v10_ : σ10.vars "DC" = (l * (n + 1) + E) * (3 + l + Vn + Vn * d) := by
    simp only [hσ10, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, Env.setVar, nn9_, lc9_, V9_, EE9_, dg9_, if_true]
  have nn10_ : σ10.vars "nn" = n := by simp [hσ10, Env.setVar, nn9_]
  have lc10_ : σ10.vars "lc" = l := by simp [hσ10, Env.setVar, lc9_]
  have V10_ : σ10.vars "V" = Vn := by simp [hσ10, Env.setVar, V9_]
  have EE10_ : σ10.vars "EE" = E := by simp [hσ10, Env.setVar, EE9_]
  have dg10_ : σ10.vars "dg" = d := by simp [hσ10, Env.setVar, dg9_]
  have A10 : σ10.arrs = σ.arrs := by simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have O10 : σ10.out = σ.out := by simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have w1_ : σ10.vars "S2" = 2 + l + Vn + Vn * d := by simp only [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, Env.setVar]; simp [v1_]
  have w2_ : σ10.vars "CC" = 3 + l + Vn + Vn * d := by simp only [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, Env.setVar]; simp [v2_]
  have w3_ : σ10.vars "B3" = 3 + l := by simp only [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, Env.setVar]; simp [v3_]
  have w4_ : σ10.vars "B4" = 3 + l + Vn := by simp only [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, Env.setVar]; simp [v4_]
  have w5_ : σ10.vars "dn" = d * n := by simp only [hσ10, hσ9, hσ8, hσ7, hσ6, Env.setVar]; simp [v5_]
  have w6_ : σ10.vars "nn1" = n + 1 := by simp only [hσ10, hσ9, hσ8, hσ7, Env.setVar]; simp [v6_]
  have w7_ : σ10.vars "LB" = l * (n + 1) := by simp only [hσ10, hσ9, hσ8, Env.setVar]; simp [v7_]
  have w8_ : σ10.vars "DD" = l * (n + 1) + E := by simp only [hσ10, hσ9, Env.setVar]; simp [v8_]
  have w9_ : σ10.vars "E2" = E / 2 := by simp only [hσ10, Env.setVar]; simp [v9_]
  have w10_ : σ10.vars "DC" = (l * (n + 1) + E) * (3 + l + Vn + Vn * d) := v10_
  have F10 : ∀ y, y ∉ APT → σ10.vars y = σ.vars y := by
    intro y hy
    simp only [APT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.1, hy.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.2]
  exact ⟨σ10, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq s10))))))))).mono
    (by simp [Expr.size]),
    w1_, w2_, w3_, w4_, w5_, w6_, w7_, w8_, w9_, w10_, A10, O10, F10⟩

end Lax117284Proofs.Machine.MisAccept
