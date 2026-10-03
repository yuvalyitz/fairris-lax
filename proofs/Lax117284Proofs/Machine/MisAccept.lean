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

/-- The five inputs of the derivation: the assignments leave them alone. -/
def Key (n l Vn E d : ℕ) (τ : Env) : Prop :=
  τ.vars "nn" = n ∧ τ.vars "lc" = l ∧ τ.vars "V" = Vn ∧ τ.vars "EE" = E ∧ τ.vars "dg" = d

theorem Key.set {n l Vn E d : ℕ} {τ : Env} (h : Key n l Vn E d τ) {z : String} (hz : z ∈ APT)
    (v : ℕ) : Key n l Vn E d (τ.setVar z v) := by
  simp only [APT, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simpa [Key, Env.setVar] using h

/-- One assignment of the derivation: the run, and the inputs still in place. -/
theorem postStep {n l Vn E d : ℕ} (τ : Env) (K : Key n l Vn E d τ) (z : String) (hz : z ∈ APT)
    (e : Expr) (v : ℕ) (hs : small B τ e) (hd : den τ e = v) :
    Run B (.assign z e) τ (τ.setVar z v) (1 + e.size) ∧ Key n l Vn E d (τ.setVar z v) := by
  refine ⟨?_, K.set hz v⟩
  rw [← hd]
  exact asgE z e τ hs

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
  have K0 : Key n l Vn E d σ := ⟨hnn, hlc, hV, hEE, hdg⟩
  obtain ⟨r1, K1⟩ := postStep (B := B) (σ) K0 "S2" (by decide) (.bin .add (.bin .add (.bin .add (.lit 2) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg"))) (2 + l + Vn + Vn * d)
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K0.1, K0.2.1, K0.2.2.1, K0.2.2.2.1, K0.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K0.1, K0.2.1, K0.2.2.1, K0.2.2.2.1, K0.2.2.2.2])
  generalize hσ1 : (σ).setVar "S2" (2 + l + Vn + Vn * d) = σ1 at r1 K1
  obtain ⟨r2, K2⟩ := postStep (B := B) (σ1) K1 "CC" (by decide) (.bin .add (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg"))) (3 + l + Vn + Vn * d)
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K1.1, K1.2.1, K1.2.2.1, K1.2.2.2.1, K1.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K1.1, K1.2.1, K1.2.2.1, K1.2.2.2.1, K1.2.2.2.2])
  generalize hσ2 : (σ1).setVar "CC" (3 + l + Vn + Vn * d) = σ2 at r2 K2
  obtain ⟨r3, K3⟩ := postStep (B := B) (σ2) K2 "B3" (by decide) (.bin .add (.lit 3) (V "lc")) (3 + l)
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K2.1, K2.2.1, K2.2.2.1, K2.2.2.2.1, K2.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K2.1, K2.2.1, K2.2.2.1, K2.2.2.2.1, K2.2.2.2.2])
  generalize hσ3 : (σ2).setVar "B3" (3 + l) = σ3 at r3 K3
  obtain ⟨r4, K4⟩ := postStep (B := B) (σ3) K3 "B4" (by decide) (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")) (3 + l + Vn)
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K3.1, K3.2.1, K3.2.2.1, K3.2.2.2.1, K3.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K3.1, K3.2.1, K3.2.2.1, K3.2.2.2.1, K3.2.2.2.2])
  generalize hσ4 : (σ3).setVar "B4" (3 + l + Vn) = σ4 at r4 K4
  obtain ⟨r5, K5⟩ := postStep (B := B) (σ4) K4 "dn" (by decide) (.bin .mul (V "dg") (V "nn")) (d * n)
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K4.1, K4.2.1, K4.2.2.1, K4.2.2.2.1, K4.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K4.1, K4.2.1, K4.2.2.1, K4.2.2.2.1, K4.2.2.2.2])
  generalize hσ5 : (σ4).setVar "dn" (d * n) = σ5 at r5 K5
  obtain ⟨r6, K6⟩ := postStep (B := B) (σ5) K5 "nn1" (by decide) (.bin .add (V "nn") (.lit 1)) (n + 1)
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K5.1, K5.2.1, K5.2.2.1, K5.2.2.2.1, K5.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K5.1, K5.2.1, K5.2.2.1, K5.2.2.2.1, K5.2.2.2.2])
  generalize hσ6 : (σ5).setVar "nn1" (n + 1) = σ6 at r6 K6
  obtain ⟨r7, K7⟩ := postStep (B := B) (σ6) K6 "LB" (by decide) (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))) (l * (n + 1))
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K6.1, K6.2.1, K6.2.2.1, K6.2.2.2.1, K6.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K6.1, K6.2.1, K6.2.2.1, K6.2.2.2.1, K6.2.2.2.2])
  generalize hσ7 : (σ6).setVar "LB" (l * (n + 1)) = σ7 at r7 K7
  obtain ⟨r8, K8⟩ := postStep (B := B) (σ7) K7 "DD" (by decide) (.bin .add (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))) (V "EE")) (l * (n + 1) + E)
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K7.1, K7.2.1, K7.2.2.1, K7.2.2.2.1, K7.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K7.1, K7.2.1, K7.2.2.1, K7.2.2.2.1, K7.2.2.2.2])
  generalize hσ8 : (σ7).setVar "DD" (l * (n + 1) + E) = σ8 at r8 K8
  obtain ⟨r9, K9⟩ := postStep (B := B) (σ8) K8 "E2" (by decide) (.bin .div (V "EE") (.lit 2)) (E / 2)
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K8.1, K8.2.1, K8.2.2.1, K8.2.2.2.1, K8.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K8.1, K8.2.1, K8.2.2.1, K8.2.2.2.1, K8.2.2.2.2])
  generalize hσ9 : (σ8).setVar "E2" (E / 2) = σ9 at r9 K9
  obtain ⟨r10, K10⟩ := postStep (B := B) (σ9) K9 "DC" (by decide) (.bin .mul (.bin .add (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))) (V "EE")) (.bin .add (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg")))) ((l * (n + 1) + E) * (3 + l + Vn + Vn * d))
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K9.1, K9.2.1, K9.2.2.1, K9.2.2.2.1, K9.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K9.1, K9.2.1, K9.2.2.1, K9.2.2.2.1, K9.2.2.2.2])
  generalize hσ10 : (σ9).setVar "DC" ((l * (n + 1) + E) * (3 + l + Vn + Vn * d)) = σ10 at r10 K10
  refine ⟨σ10, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq r10))))))))).mono
    (by simp [Expr.size]), ?_⟩
  subst hσ10 hσ9 hσ8 hσ7 hσ6 hσ5 hσ4 hσ3 hσ2 hσ1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try simp [Env.setVar]
  intro y hy
  simp only [APT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hy
  simp [Env.setVar, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

end Lax117284Proofs.Machine.MisAccept
