import Lax117284Proofs.Machine.MisChk
import Lax117284Proofs.Machine.MisBlk

/-!
The processing time and the due date of a job of the constructed instance, as a command: the case
analysis of the construction on the day and the client.
-/

namespace Lax117284Proofs.Machine.MisJob

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.MisBlk Lax117284Proofs.Machine.MisSem
open Lax117284Proofs.Machine.MisFormat (VM)

variable {B : ℕ}

abbrev V (s : String) : Expr := .var s
abbrev lit (n : ℕ) : Expr := .lit n
abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev div (e f : Expr) : Expr := .bin .div e f

/-- The processing time and the due date, computed independently. -/
def pdCom (e1 e2 : Expr) : Com := .seq (.assign "pv" e1) (.assign "dv" e2)

/-- The scalars a job assigns, apart from those of the scans it runs. -/
def AJ : List String := ["pv", "dv", "vb", "va", "ee"]

/-- Nothing changed but the scalars a job assigns. -/
def JStep (X : List String) (σ σ' : Env) : Prop :=
  σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ ∀ y, y ∉ X → σ'.vars y = σ.vars y

lemma JStep.trans {X} {σ σ' σ'' : Env} (h : JStep X σ σ') (h' : JStep X σ' σ'') : JStep X σ σ'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, fun y hy => (h'.2.2 y hy).trans (h.2.2 y hy)⟩

lemma JStep.setVar {X} (σ : Env) (z : String) (v : ℕ) (hz : z ∈ X) : JStep X σ (σ.setVar z v) :=
  ⟨rfl, rfl, fun y hy => by
    have : y ≠ z := fun h => hy (h ▸ hz)
    simp [Env.setVar, this]⟩

lemma JStep.mono {X Y} (hXY : ∀ y, y ∈ X → y ∈ Y) {σ σ' : Env} (h : JStep X σ σ') : JStep Y σ σ' :=
  ⟨h.1, h.2.1, fun y hy => h.2.2 y (fun hx => hy (hXY y hx))⟩

/-- **The two assignments of a job.** -/
theorem pd_run (e1 e2 : Expr) (σ : Env) (h1 : small B σ e1)
    (h2 : small B (σ.setVar "pv" (den σ e1)) e2) :
    ∃ σ', Run B (pdCom e1 e2) σ σ' (2 + e1.size + e2.size) ∧ σ'.vars "pv" = den σ e1 ∧
      σ'.vars "dv" = den (σ.setVar "pv" (den σ e1)) e2 ∧ JStep AJ σ σ' := by
  have r1 := asgE (B := B) "pv" e1 σ h1
  have r2 := asgE (B := B) "dv" e2 (σ.setVar "pv" (den σ e1)) h2
  refine ⟨_, (r1.seq r2).mono (by omega), ?_, ?_, ?_⟩
  · simp [Env.setVar]
  · simp [Env.setVar]
  · exact (JStep.setVar σ "pv" _ (by simp [AJ])).trans (JStep.setVar _ "dv" _ (by simp [AJ]))

/-- What the job commands read. -/
structure JC (ns : List ℕ) (i c : ℕ) (σ : Env) : Prop where
  vdi : σ.vars "di" = i
  vcc : σ.vars "cc" = c
  vnn : σ.vars "nn" = nN ns
  vlc : σ.vars "lc" = lN ns
  vV : σ.vars "V" = VM ns
  vdg : σ.vars "dg" = degN ns
  vS2 : σ.vars "S2" = spanN ns
  vB3 : σ.vars "B3" = 3 + lN ns
  vB4 : σ.vars "B4" = 3 + lN ns + VM ns
  vdn : σ.vars "dn" = degN ns * nN ns
  vn1 : σ.vars "nn1" = nN ns + 1
  vLB : σ.vars "LB" = lN ns * (nN ns + 1)

/-- The number of the vertex and the selection clients depends on the vertex day. -/
def vertexCom : Com :=
  .ite (.eq (V "cc") (lit 0)) (pdCom (V "S2") (add (V "dg") (V "S2")))
    (.ite (.eq (V "cc") (add (V "B3") (add (mul (V "vb") (V "nn")) (V "va"))))
      (pdCom (V "dg") (V "dg"))
      (.ite (.eq (V "cc") (add (lit 3) (V "vb")))
        (pdCom (V "dg") (V "dg"))
        (pdCom (lit 1) (add (V "dg") (V "cc")))))

/-- The words of the magnitude of every value a job computes. -/
def Mag (ns : List ℕ) : ℕ := 2 * spanN ns + degN ns * nN ns + degN ns + 100

lemma VM_le_span (ns : List ℕ) : VM ns ≤ spanN ns := by
  unfold spanN; omega

lemma lN_le_span (ns : List ℕ) : lN ns ≤ spanN ns := by
  unfold spanN; omega

lemma span_ge (ns : List ℕ) : 2 + lN ns + VM ns ≤ spanN ns := by
  unfold spanN; omega

lemma span_eq (ns : List ℕ) : spanN ns = 2 + lN ns + VM ns + VM ns * degN ns := rfl

lemma Vdg_le (ns : List ℕ) : VM ns * degN ns ≤ spanN ns := by
  unfold spanN; omega

lemma cl_le (ns : List ℕ) : clN ns = spanN ns + 1 := by unfold clN spanN; omega

set_option maxHeartbeats 3200000 in
/-- **A job of a vertex day.** -/
theorem vertexCom_run (ns : List ℕ) (i c b a : ℕ) (σ : Env) (hj : JC ns i c σ)
    (hb : σ.vars "vb" = b) (ha : σ.vars "va" = a) (han : a < nN ns) (hw0 : b * nN ns + a < VM ns)
    (hcl : c < clN ns) (hM : Mag ns < B) :
    ∃ σ', Run B vertexCom σ σ' 40 ∧
      σ'.vars "pv" = (vertexDayN ns (b * nN ns + a) c).1 ∧
      σ'.vars "dv" = (vertexDayN ns (b * nN ns + a) c).2 ∧ JStep AJ σ σ' := by
  have hsp := VM_le_span ns
  have hlc := lN_le_span ns
  have hcls := cl_le ns
  have hspg := span_ge ns
  unfold Mag at hM
  have hdiv : (b * nN ns + a) / nN ns = b := by
    have hn : 0 < nN ns := by omega
    rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt han, Nat.add_zero]
  obtain ⟨hdi, hcc, hnn, hlc', hV, hdg, hS2, hB3, hB4, hdn, hn1, hLB⟩ := hj
  have hdg1 : 1 ≤ degN ns := by unfold degN; omega
  have hbn : b * nN ns ≤ b * nN ns + a := by omega
  have hbb : b ≤ b * nN ns := Nat.le_mul_of_pos_right _ (by omega)
  have hnn_le : nN ns ≤ degN ns * nN ns := Nat.le_mul_of_pos_left _ hdg1
  have small_cc : small B σ (V "cc") := by simp [small, hcc]; omega
  have small0 : small B σ (lit 0) := by simp [small]; omega
  by_cases h0 : c = 0
  · have hT : (Cond.eq (V "cc") (lit 0)).evalB B σ = some true :=
      condEq_true _ _ σ small_cc small0 (by simp [den, hcc, h0])
    obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (V "S2") (add (V "dg") (V "S2")) σ
      (by simp [small, hS2]; omega) (by simp [small, den, Env.setVar, hS2, hdg]; omega)
    refine ⟨σ', (Run.ite_true hT r).mono (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
    · rw [e1]; unfold vertexDayN; rw [if_pos h0]; simp [den, hS2]
    · rw [e2]; unfold vertexDayN; rw [if_pos h0]; simp [den, Env.setVar, hS2, hdg]
  · have hF : (Cond.eq (V "cc") (lit 0)).evalB B σ = some false :=
      condEq_false _ _ σ small_cc small0 (by simp [den, hcc]; omega)
    have hsm1 : small B σ (add (V "B3") (add (mul (V "vb") (V "nn")) (V "va"))) := by
      simp [small, den, hB3, hb, hnn, ha]
      omega
    by_cases h1 : c = 3 + lN ns + (b * nN ns + a)
    · have hT : (Cond.eq (V "cc") (add (V "B3") (add (mul (V "vb") (V "nn")) (V "va")))).evalB B σ
          = some true := condEq_true _ _ σ small_cc hsm1 (by simp [den, hcc, hB3, hb, hnn, ha]; omega)
      obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (V "dg") (V "dg") σ
        (by simp [small, hdg]; omega) (by simp [small, den, Env.setVar, hdg]; omega)
      refine ⟨σ', (Run.ite_false hF (Run.ite_true hT r)).mono
        (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
      · rw [e1]; unfold vertexDayN; rw [if_neg h0, if_pos (Or.inl h1)]; simp [den, hdg]
      · rw [e2]; unfold vertexDayN; rw [if_neg h0, if_pos (Or.inl h1)]
        simp [den, Env.setVar, hdg]
    · have hF1 : (Cond.eq (V "cc") (add (V "B3") (add (mul (V "vb") (V "nn")) (V "va")))).evalB B σ
          = some false := condEq_false _ _ σ small_cc hsm1 (by simp [den, hcc, hB3, hb, hnn, ha]; omega)
      have hsm2 : small B σ (add (lit 3) (V "vb")) := by
        simp [small, den, hb]
        omega
      by_cases h2 : c = 3 + b
      · have hT : (Cond.eq (V "cc") (add (lit 3) (V "vb"))).evalB B σ = some true :=
          condEq_true _ _ σ small_cc hsm2 (by simp [den, hcc, hb]; omega)
        obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (V "dg") (V "dg") σ
          (by simp [small, hdg]; omega) (by simp [small, den, Env.setVar, hdg]; omega)
        refine ⟨σ', (Run.ite_false hF (Run.ite_false hF1 (Run.ite_true hT r))).mono
          (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
        · rw [e1]; unfold vertexDayN; rw [if_neg h0, if_pos (Or.inr (by rw [hdiv]; exact h2))]
          simp [den, hdg]
        · rw [e2]; unfold vertexDayN; rw [if_neg h0, if_pos (Or.inr (by rw [hdiv]; exact h2))]
          simp [den, Env.setVar, hdg]
      · have hF2 : (Cond.eq (V "cc") (add (lit 3) (V "vb"))).evalB B σ = some false :=
          condEq_false _ _ σ small_cc hsm2 (by simp [den, hcc, hb]; omega)
        obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 1) (add (V "dg") (V "cc")) σ
          (by simp [small]; omega)
          (by simp [small, den, Env.setVar, hdg, hcc]; omega)
        refine ⟨σ', (Run.ite_false hF (Run.ite_false hF1 (Run.ite_false hF2 r))).mono
          (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
        · rw [e1]; unfold vertexDayN
          rw [if_neg h0, if_neg (by rw [hdiv]; omega)]; simp [den]
        · rw [e2]; unfold vertexDayN
          rw [if_neg h0, if_neg (by rw [hdiv]; omega)]; simp [den, Env.setVar, hdg, hcc]

/-- The jobs of a validation day: the vertex clients of the colour and the edge clients of its
vertices. -/
def validNext : Com :=
  .ite (.lt (V "cc") (V "B4")) (pdCom (lit 1) (add (V "dn") (V "cc")))
    (.ite (.eq (div (div (sub (V "cc") (V "B4")) (V "dg")) (V "nn")) (V "vb"))
      (pdCom (lit 1)
        (add (add (mul (V "dg") (sub (div (sub (V "cc") (V "B4")) (V "dg"))
            (mul (div (div (sub (V "cc") (V "B4")) (V "dg")) (V "nn")) (V "nn"))))
          (sub (sub (V "cc") (V "B4")) (mul (div (sub (V "cc") (V "B4")) (V "dg")) (V "dg"))))
          (lit 1)))
      (pdCom (lit 1) (add (V "dn") (V "cc"))))

def validCom : Com :=
  .ite (.eq (V "cc") (lit 0)) (pdCom (V "S2") (add (V "dn") (V "S2")))
    (.ite (.lt (V "cc") (V "B3")) validNext
      (.ite (.lt (V "cc") (V "B4"))
        (.ite (.eq (div (sub (V "cc") (V "B3")) (V "nn")) (V "vb"))
          (pdCom (V "dg")
            (mul (V "dg") (add (sub (sub (V "cc") (V "B3"))
              (mul (div (sub (V "cc") (V "B3")) (V "nn")) (V "nn"))) (lit 1))))
          validNext)
        validNext))

lemma mod_sub (x n : ℕ) : x - x / n * n = x % n := MisFind.mod_eq_sub x n

set_option maxHeartbeats 6400000 in
/-- **The jobs of a validation day after the vertex clients.** -/
theorem validNext_run (ns : List ℕ) (i c b : ℕ) (σ : Env) (hj : JC ns i c σ)
    (hb : σ.vars "vb" = b) (hbl : b < lN ns) (hn0 : 0 < nN ns) (hcl : c < clN ns)
    (hM : Mag ns < B) :
    ∃ σ', Run B validNext σ σ' 60 ∧ σ'.vars "pv" = 1 ∧
      σ'.vars "dv" = (if 3 + lN ns + VM ns ≤ c ∧
          ((c - (3 + lN ns + VM ns)) / degN ns) / nN ns = b then
        degN ns * (((c - (3 + lN ns + VM ns)) / degN ns) % nN ns) +
          (c - (3 + lN ns + VM ns)) % degN ns + 1
      else degN ns * nN ns + c) ∧ JStep AJ σ σ' := by
  have hsp := VM_le_span ns
  have hlc := lN_le_span ns
  have hcls := cl_le ns
  have hspg := span_ge ns
  unfold Mag at hM
  obtain ⟨hdi, hcc, hnn, hlc', hV, hdg, hS2, hB3, hB4, hdn, hn1, hLB⟩ := hj
  have hdg1 : 1 ≤ degN ns := by unfold degN; omega
  have hnn_le : nN ns ≤ degN ns * nN ns := Nat.le_mul_of_pos_left _ hdg1
  have small_cc : small B σ (V "cc") := by simp [small, hcc]; omega
  have hsm3 : small B σ (add (V "dn") (V "cc")) := by simp [small, den, hdn, hcc]; omega
  have hsm1 : small B σ (lit 1) := by simp [small]; omega
  have hc4 : small B σ (V "B4") := by simp [small, hB4]; omega
  by_cases h4 : c < 3 + lN ns + VM ns
  · have hT : (Cond.lt (V "cc") (V "B4")).evalB B σ = some true :=
      condLt_true _ _ σ small_cc hc4 (by simp [den, hcc, hB4]; omega)
    obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 1) (add (V "dn") (V "cc")) σ hsm1
      (by simp [small, den, Env.setVar, hdn, hcc]; omega)
    refine ⟨σ', (Run.ite_true hT r).mono (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
    · rw [e1]; rfl
    · rw [e2, if_neg (by omega)]; simp [den, Env.setVar, hdn, hcc]
  · have hF : (Cond.lt (V "cc") (V "B4")).evalB B σ = some false :=
      condLt_false _ _ σ small_cc hc4 (by simp [den, hcc, hB4]; omega)
    obtain ⟨m2, hm2⟩ : ∃ m2, m2 = c - (3 + lN ns + VM ns) := ⟨_, rfl⟩
    obtain ⟨q2, hq2⟩ : ∃ q2, q2 = m2 / degN ns := ⟨_, rfl⟩
    obtain ⟨q3, hq3⟩ : ∃ q3, q3 = q2 / nN ns := ⟨_, rfl⟩
    have hq2m : q2 ≤ m2 := by rw [hq2]; exact Nat.div_le_self _ _
    have hq3q : q3 ≤ q2 := by rw [hq3]; exact Nat.div_le_self _ _
    have hq3n : q3 * nN ns ≤ q2 := by rw [hq3]; exact Nat.div_mul_le_self _ _
    have hq2d : q2 * degN ns ≤ m2 := by rw [hq2]; exact Nat.div_mul_le_self _ _
    have hmodn : q2 - q3 * nN ns < nN ns := by
      rw [hq3, mod_sub]; exact Nat.mod_lt _ hn0
    have hmodd : m2 - q2 * degN ns < degN ns := by
      rw [hq2, mod_sub]; exact Nat.mod_lt _ (by omega)
    have hprod : degN ns * (q2 - q3 * nN ns) ≤ degN ns * nN ns := Nat.mul_le_mul_left _ hmodn.le
    have hm2c : m2 ≤ c := by omega
    have hsm3' : small B σ (div (div (sub (V "cc") (V "B4")) (V "dg")) (V "nn")) := by
      simp [small, den, hcc, hB4, hdg, hnn]
      rw [← hm2, ← hq2, ← hq3]
      omega
    have hsmb : small B σ (V "vb") := by simp [small, hb]; omega
    have hden3 : den σ (div (div (sub (V "cc") (V "B4")) (V "dg")) (V "nn")) = q3 := by
      simp [den, hcc, hB4, hdg, hnn]; rw [← hm2, ← hq2, ← hq3]
    by_cases h3 : q3 = b
    · have hT3 : (Cond.eq (div (div (sub (V "cc") (V "B4")) (V "dg")) (V "nn")) (V "vb")).evalB B σ
          = some true := condEq_true _ _ σ hsm3' hsmb (by rw [hden3]; simp [den, hb, h3])
      obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 1) (add (add (mul (V "dg") (sub (div (sub
        (V "cc") (V "B4")) (V "dg")) (mul (div (div (sub (V "cc") (V "B4")) (V "dg")) (V "nn"))
        (V "nn")))) (sub (sub (V "cc") (V "B4")) (mul (div (sub (V "cc") (V "B4")) (V "dg"))
        (V "dg")))) (lit 1)) σ hsm1
        (by
          simp [small, den, Env.setVar, hcc, hB4, hdg, hnn]
          rw [← hm2, ← hq2, ← hq3]
          omega)
      refine ⟨σ', (Run.ite_false hF (Run.ite_true hT3 r)).mono
        (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
      · rw [e1]; rfl
      · rw [e2]
        simp [den, Env.setVar, hcc, hB4, hdg, hnn]
        rw [← hm2, ← hq2, ← hq3, if_pos ⟨by omega, h3⟩]
        rw [hq3, hq2, mod_sub, mod_sub]
    · have hF3 : (Cond.eq (div (div (sub (V "cc") (V "B4")) (V "dg")) (V "nn")) (V "vb")).evalB B σ
          = some false := condEq_false _ _ σ hsm3' hsmb (by rw [hden3]; simp [den, hb, h3])
      obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 1) (add (V "dn") (V "cc")) σ hsm1
        (by simp [small, den, Env.setVar, hdn, hcc]; omega)
      refine ⟨σ', (Run.ite_false hF (Run.ite_false hF3 r)).mono
        (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
      · rw [e1]; rfl
      · rw [e2, if_neg (by
          rintro ⟨-, h⟩
          apply h3
          rw [hq3, hq2, hm2]; exact h)]
        simp [den, Env.setVar, hdn, hcc]

set_option maxHeartbeats 6400000 in
/-- **A job of a validation day.** -/
theorem validCom_run (ns : List ℕ) (i c b : ℕ) (σ : Env) (hj : JC ns i c σ)
    (hb : σ.vars "vb" = b) (hbl : b < lN ns) (hn0 : 0 < nN ns) (hcl : c < clN ns)
    (hM : Mag ns < B) :
    ∃ σ', Run B validCom σ σ' 80 ∧
      σ'.vars "pv" = (validationDayN ns b c).1 ∧
      σ'.vars "dv" = (validationDayN ns b c).2 ∧ JStep AJ σ σ' := by
  have hsp := VM_le_span ns
  have hlc := lN_le_span ns
  have hcls := cl_le ns
  have hspg := span_ge ns
  unfold Mag at hM
  have hj0 := hj
  obtain ⟨hdi, hcc, hnn, hlc', hV, hdg, hS2, hB3, hB4, hdn, hn1, hLB⟩ := hj
  have hdg1 : 1 ≤ degN ns := by unfold degN; omega
  have hnn_le : nN ns ≤ degN ns * nN ns := Nat.le_mul_of_pos_left _ hdg1
  have small_cc : small B σ (V "cc") := by simp [small, hcc]; omega
  have small0 : small B σ (lit 0) := by simp [small]; omega
  have hc3 : small B σ (V "B3") := by simp [small, hB3]; omega
  have hc4 : small B σ (V "B4") := by simp [small, hB4]; omega
  unfold validationDayN
  by_cases h0 : c = 0
  · have hT : (Cond.eq (V "cc") (lit 0)).evalB B σ = some true :=
      condEq_true _ _ σ small_cc small0 (by simp [den, hcc, h0])
    obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (V "S2") (add (V "dn") (V "S2")) σ
      (by simp [small, hS2]; omega)
      (by simp [small, den, Env.setVar, hS2, hdn]; omega)
    refine ⟨σ', (Run.ite_true hT r).mono (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
    · rw [e1, if_pos h0]; simp [den, hS2]
    · rw [e2, if_pos h0]; simp [den, Env.setVar, hS2, hdn]
  · have hF : (Cond.eq (V "cc") (lit 0)).evalB B σ = some false :=
      condEq_false _ _ σ small_cc small0 (by simp [den, hcc]; omega)
    rw [if_neg h0]
    obtain ⟨σn, r0, e10, e20, st0⟩ := validNext_run (B := B) ns i c b σ hj0 hb hbl hn0 hcl hM
    by_cases h3 : c < 3 + lN ns
    · have hT : (Cond.lt (V "cc") (V "B3")).evalB B σ = some true :=
        condLt_true _ _ σ small_cc hc3 (by simp [den, hcc, hB3]; omega)
      refine ⟨_, (Run.ite_false hF (Run.ite_true hT r0)).mono
        (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st0⟩
      · rw [e10, if_neg (by omega), if_neg (by omega)]
      · rw [e20, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · have hF3 : (Cond.lt (V "cc") (V "B3")).evalB B σ = some false :=
        condLt_false _ _ σ small_cc hc3 (by simp [den, hcc, hB3]; omega)
      by_cases h4 : c < 3 + lN ns + VM ns
      · have hT4 : (Cond.lt (V "cc") (V "B4")).evalB B σ = some true :=
          condLt_true _ _ σ small_cc hc4 (by simp [den, hcc, hB4]; omega)
        obtain ⟨m1, hm1⟩ : ∃ m1, m1 = c - (3 + lN ns) := ⟨_, rfl⟩
        obtain ⟨q1, hq1⟩ : ∃ q1, q1 = m1 / nN ns := ⟨_, rfl⟩
        have hq1m : q1 ≤ m1 := by rw [hq1]; exact Nat.div_le_self _ _
        have hq1n : q1 * nN ns ≤ m1 := by rw [hq1]; exact Nat.div_mul_le_self _ _
        have hmodn : m1 - q1 * nN ns < nN ns := by
          rw [hq1, mod_sub]; exact Nat.mod_lt _ hn0
        have hprod : degN ns * (m1 - q1 * nN ns + 1) ≤ degN ns * nN ns :=
          Nat.mul_le_mul_left _ (by omega)
        have hsm1 : small B σ (div (sub (V "cc") (V "B3")) (V "nn")) := by
          simp [small, den, hcc, hB3, hnn]; rw [← hm1, ← hq1]; omega
        have hsmb : small B σ (V "vb") := by simp [small, hb]; omega
        have hden1 : den σ (div (sub (V "cc") (V "B3")) (V "nn")) = q1 := by
          simp [den, hcc, hB3, hnn]; rw [← hm1, ← hq1]
        by_cases h5 : q1 = b
        · have hT5 : (Cond.eq (div (sub (V "cc") (V "B3")) (V "nn")) (V "vb")).evalB B σ
              = some true := condEq_true _ _ σ hsm1 hsmb (by rw [hden1]; simp [den, hb, h5])
          obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (V "dg") (mul (V "dg") (add (sub (sub (V "cc")
            (V "B3")) (mul (div (sub (V "cc") (V "B3")) (V "nn")) (V "nn"))) (lit 1))) σ
            (by simp [small, hdg]; omega)
            (by
              simp [small, den, Env.setVar, hcc, hB3, hdg, hnn]
              rw [← hm1, ← hq1]
              omega)
          refine ⟨σ', (Run.ite_false hF (Run.ite_false hF3 (Run.ite_true hT4
            (Run.ite_true hT5 r)))).mono (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
          · rw [e1, if_pos ⟨by omega, h4, by rw [← hm1, ← hq1]; exact h5⟩]; simp [den, hdg]
          · rw [e2, if_pos ⟨by omega, h4, by rw [← hm1, ← hq1]; exact h5⟩]
            simp [den, Env.setVar, hcc, hB3, hdg, hnn]
            rw [← hm1, ← hq1, hq1, mod_sub]
            exact Or.inl rfl
        · have hF5 : (Cond.eq (div (sub (V "cc") (V "B3")) (V "nn")) (V "vb")).evalB B σ
              = some false := condEq_false _ _ σ hsm1 hsmb (by rw [hden1]; simp [den, hb, h5])
          refine ⟨_, (Run.ite_false hF (Run.ite_false hF3 (Run.ite_true hT4
            (Run.ite_false hF5 r0)))).mono (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st0⟩
          · rw [e10, if_neg (by
              rintro ⟨-, -, h⟩; apply h5; rw [hq1, hm1]; exact h), if_neg (by omega)]
          · rw [e20, if_neg (by omega), if_neg (by
              rintro ⟨-, -, h⟩; apply h5; rw [hq1, hm1]; exact h), if_neg (by omega)]
      · have hF4 : (Cond.lt (V "cc") (V "B4")).evalB B σ = some false :=
          condLt_false _ _ σ small_cc hc4 (by simp [den, hcc, hB4]; omega)
        have hnot : ¬ (3 + lN ns ≤ c ∧ c < 3 + lN ns + VM ns ∧ (c - (3 + lN ns)) / nN ns = b) :=
          fun h => h4 h.2.1
        refine ⟨_, (Run.ite_false hF (Run.ite_false hF3 (Run.ite_false hF4 r0))).mono
          (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st0⟩
        · rw [e10, if_neg hnot]; split_ifs <;> rfl
        · rw [e20, if_neg hnot]; split_ifs <;> rfl

/-! ### The edge days -/

/-- The neighbours of a vertex before another, as a count over the array. -/
lemma idx_eq (ns : List ℕ) (w w' : ℕ) :
    (List.range w').countP (MisCount.onePred ns (2 + w * VM ns)) = idxN ns w w' := by
  unfold idxN
  refine List.countP_congr fun x _ => ?_
  unfold MisCount.onePred mat
  rw [Nat.add_assoc]

/-- **The endpoints of an edge lie among the vertices.** -/
lemma edge_lt (ns : List ℕ) (e : ℕ) (he : e < edgeN ns) :
    ((edgeCellsN ns).getD e (0, 0)).1 < VM ns ∧ ((edgeCellsN ns).getD e (0, 0)).2 < VM ns := by
  have hl : e < (edgeCellsN ns).length := by
    have : (edgeCellsN ns).length = edgeN ns := by
      unfold edgeCellsN edgeN
      rw [List.length_map, List.countP_eq_length_filter]
    omega
  have hmem := List.getElem_mem hl
  rw [← List.getD_eq_getElem _ (0, 0) hl] at hmem
  generalize (edgeCellsN ns).getD e (0, 0) = q at hmem ⊢
  have hmem2 : q ∈ ((List.range (VM ns * VM ns)).filter (qualE ns)).map
      (fun t => (t / VM ns, t % VM ns)) := hmem
  obtain ⟨t, ht, hteq⟩ := List.mem_map.mp hmem2
  obtain ⟨ht1, -⟩ := List.mem_filter.mp ht
  obtain ⟨-, h1, h2⟩ := cell_split ns t (List.mem_range.mp ht1)
  rw [← hteq]
  exact ⟨h1, h2⟩

/-- The clients of an edge day, once the endpoints of the edge and the positions of each among the
neighbours of the other are known. -/
def edgeDisp : Com :=
  .ite (.eq (V "cc") (lit 0)) (pdCom (V "S2") (add (lit 3) (V "S2")))
    (.ite (.eq (V "cc") (lit 2)) (pdCom (lit 2) (lit 2))
      (.ite (.eq (V "cc") (lit 1)) (pdCom (lit 2) (lit 3))
        (.ite (.eq (V "cc") (add (add (V "B4") (mul (V "fw") (V "dg"))) (V "k1")))
          (pdCom (lit 1) (lit 3))
          (.ite (.eq (V "cc") (add (add (V "B4") (mul (V "fw2") (V "dg"))) (V "k2")))
            (pdCom (lit 1) (lit 1))
            (pdCom (lit 1) (add (lit 3) (V "cc")))))))

/-- The edge day of the edge from `fw` to `fw2`. -/
def edgeCom : Com :=
  .seq (.assign "e" (sub (V "di") (V "LB")))
  (.seq MisFind.findCom
  (.seq (.assign "bs" (add (lit 2) (mul (V "fw") (V "V"))))
  (.seq (.assign "bd" (V "fw2"))
  (.seq MisCount.cntCom
  (.seq (.assign "k1" (V "cnt"))
  (.seq (.assign "bs" (add (lit 2) (mul (V "fw2") (V "V"))))
  (.seq (.assign "bd" (V "fw"))
  (.seq MisCount.cntCom
  (.seq (.assign "k2" (V "cnt")) edgeDisp)))))))))

lemma idxN_le (ns : List ℕ) (w w' : ℕ) : idxN ns w w' ≤ w' := by
  unfold idxN
  have := List.countP_le_length (p := fun x => decide (mat ns w x = 1)) (l := List.range w')
  simpa using this

set_option maxHeartbeats 6400000 in
/-- **The clients of an edge day.** -/
theorem edgeDisp_run (ns : List ℕ) (i c w w' : ℕ) (σ : Env) (hj : JC ns i c σ)
    (hfw : σ.vars "fw" = w) (hfw2 : σ.vars "fw2" = w') (hk1 : σ.vars "k1" = idxN ns w w')
    (hk2 : σ.vars "k2" = idxN ns w' w) (hw : w < VM ns) (hw' : w' < VM ns)
    (hcl : c < clN ns) (hM : Mag ns < B) :
    ∃ σ', Run B edgeDisp σ σ' 60 ∧ σ'.vars "pv" = (edgeDayN ns w w' c).1 ∧
      σ'.vars "dv" = (edgeDayN ns w w' c).2 ∧ JStep AJ σ σ' := by
  have hsp := VM_le_span ns
  have hlc := lN_le_span ns
  have hcls := cl_le ns
  have hspg := span_ge ns
  have hVdg := Vdg_le ns
  have hspe := span_eq ns
  unfold Mag at hM
  obtain ⟨hdi, hcc, hnn, hlc', hV, hdg, hS2, hB3, hB4, hdn, hn1, hLB⟩ := hj
  have hdg1 : 1 ≤ degN ns := by unfold degN; omega
  have hi1 := idxN_le ns w w'
  have hi2 := idxN_le ns w' w
  have hwd : w * degN ns ≤ VM ns * degN ns := Nat.mul_le_mul_right _ hw.le
  have hw'd : w' * degN ns ≤ VM ns * degN ns := Nat.mul_le_mul_right _ hw'.le
  have small_cc : small B σ (V "cc") := by simp [small, hcc]; omega
  have sm0 : small B σ (lit 0) := by simp [small]; omega
  have sm1 : small B σ (lit 1) := by simp [small]; omega
  have sm2 : small B σ (lit 2) := by simp [small]; omega
  have sm3 : small B σ (lit 3) := by simp [small]; omega
  have hinc1 : small B σ (add (add (V "B4") (mul (V "fw") (V "dg"))) (V "k1")) := by
    simp [small, den, hB4, hfw, hdg, hk1]; omega
  have hinc2 : small B σ (add (add (V "B4") (mul (V "fw2") (V "dg"))) (V "k2")) := by
    simp [small, den, hB4, hfw2, hdg, hk2]; omega
  unfold edgeDayN incIdN
  by_cases h0 : c = 0
  · have hT : (Cond.eq (V "cc") (lit 0)).evalB B σ = some true :=
      condEq_true _ _ σ small_cc sm0 (by simp [den, hcc, h0])
    obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (V "S2") (add (lit 3) (V "S2")) σ
      (by simp [small, hS2]; omega) (by simp [small, den, Env.setVar, hS2]; omega)
    refine ⟨σ', (Run.ite_true hT r).mono (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
    · rw [e1, if_pos h0]; simp [den, hS2]
    · rw [e2, if_pos h0]; simp [den, Env.setVar, hS2]
  · have hF0 : (Cond.eq (V "cc") (lit 0)).evalB B σ = some false :=
      condEq_false _ _ σ small_cc sm0 (by simp [den, hcc]; omega)
    by_cases h2 : c = 2
    · have hT : (Cond.eq (V "cc") (lit 2)).evalB B σ = some true :=
        condEq_true _ _ σ small_cc sm2 (by simp [den, hcc, h2])
      obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 2) (lit 2) σ sm2
        (by simp [small]; omega)
      refine ⟨σ', (Run.ite_false hF0 (Run.ite_true hT r)).mono
        (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
      · rw [e1, if_neg h0, if_pos h2]; simp [den]
      · rw [e2, if_neg h0, if_pos h2]; simp [den, Env.setVar]
    · have hF2 : (Cond.eq (V "cc") (lit 2)).evalB B σ = some false :=
        condEq_false _ _ σ small_cc sm2 (by simp [den, hcc]; omega)
      by_cases h1 : c = 1
      · have hT : (Cond.eq (V "cc") (lit 1)).evalB B σ = some true :=
          condEq_true _ _ σ small_cc sm1 (by simp [den, hcc, h1])
        obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 2) (lit 3) σ sm2
          (by simp [small]; omega)
        refine ⟨σ', (Run.ite_false hF0 (Run.ite_false hF2 (Run.ite_true hT r))).mono
          (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
        · rw [e1, if_neg h0, if_neg h2, if_pos h1]; simp [den]
        · rw [e2, if_neg h0, if_neg h2, if_pos h1]; simp [den, Env.setVar]
      · have hF1 : (Cond.eq (V "cc") (lit 1)).evalB B σ = some false :=
          condEq_false _ _ σ small_cc sm1 (by simp [den, hcc]; omega)
        by_cases h3 : c = 3 + lN ns + VM ns + w * degN ns + idxN ns w w'
        · have hT : (Cond.eq (V "cc") (add (add (V "B4") (mul (V "fw") (V "dg"))) (V "k1"))).evalB B σ
              = some true := condEq_true _ _ σ small_cc hinc1 (by
                simp [den, hcc, hB4, hfw, hdg, hk1]; omega)
          obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 1) (lit 3) σ sm1
            (by simp [small]; omega)
          refine ⟨σ', (Run.ite_false hF0 (Run.ite_false hF2 (Run.ite_false hF1
            (Run.ite_true hT r)))).mono (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
          · rw [e1, if_neg h0, if_neg h2, if_neg h1, if_pos h3]; simp [den]
          · rw [e2, if_neg h0, if_neg h2, if_neg h1, if_pos h3]; simp [den, Env.setVar]
        · have hF3 : (Cond.eq (V "cc") (add (add (V "B4") (mul (V "fw") (V "dg"))) (V "k1"))).evalB
              B σ = some false := condEq_false _ _ σ small_cc hinc1 (by
                simp [den, hcc, hB4, hfw, hdg, hk1]; omega)
          by_cases h4 : c = 3 + lN ns + VM ns + w' * degN ns + idxN ns w' w
          · have hT : (Cond.eq (V "cc") (add (add (V "B4") (mul (V "fw2") (V "dg"))) (V "k2"))).evalB
                B σ = some true := condEq_true _ _ σ small_cc hinc2 (by
                  simp [den, hcc, hB4, hfw2, hdg, hk2]; omega)
            obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 1) (lit 1) σ sm1
              (by simp [small]; omega)
            refine ⟨σ', (Run.ite_false hF0 (Run.ite_false hF2 (Run.ite_false hF1
              (Run.ite_false hF3 (Run.ite_true hT r))))).mono
              (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
            · rw [e1, if_neg h0, if_neg h2, if_neg h1, if_neg h3, if_pos h4]; simp [den]
            · rw [e2, if_neg h0, if_neg h2, if_neg h1, if_neg h3, if_pos h4]
              simp [den, Env.setVar]
          · have hF4 : (Cond.eq (V "cc") (add (add (V "B4") (mul (V "fw2") (V "dg"))) (V "k2"))).evalB
                B σ = some false := condEq_false _ _ σ small_cc hinc2 (by
                  simp [den, hcc, hB4, hfw2, hdg, hk2]; omega)
            obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 1) (add (lit 3) (V "cc")) σ sm1
              (by simp [small, den, Env.setVar, hcc]; omega)
            refine ⟨σ', (Run.ite_false hF0 (Run.ite_false hF2 (Run.ite_false hF1
              (Run.ite_false hF3 (Run.ite_false hF4 r))))).mono
              (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
            · rw [e1, if_neg h0, if_neg h2, if_neg h1, if_neg h3, if_neg h4]; simp [den]
            · rw [e2, if_neg h0, if_neg h2, if_neg h1, if_neg h3, if_neg h4]
              simp [den, Env.setVar, hcc]

/-- The scalars of the edge-day job that no step of it changes. -/
def XE : List String := AJ ++ ["e", "bs", "bd", "k1", "k2"] ++ MisFind.AF ++ MisCount.AN

/-- What an edge-day job reads. -/
def JCE (ns : List ℕ) (i c : ℕ) (σ : Env) : Prop :=
  JC ns i c σ ∧ σ.arrs "TK" = ns ∧ σ.vars "VV" = VM ns * VM ns

lemma JCE.step {ns : List ℕ} {i c : ℕ} {σ σ' : Env} (h : JCE ns i c σ) (hk : JStep XE σ σ') :
    JCE ns i c σ' := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hk.2.2 "di" (by decide)]; exact h.1.vdi
  · rw [hk.2.2 "cc" (by decide)]; exact h.1.vcc
  · rw [hk.2.2 "nn" (by decide)]; exact h.1.vnn
  · rw [hk.2.2 "lc" (by decide)]; exact h.1.vlc
  · rw [hk.2.2 "V" (by decide)]; exact h.1.vV
  · rw [hk.2.2 "dg" (by decide)]; exact h.1.vdg
  · rw [hk.2.2 "S2" (by decide)]; exact h.1.vS2
  · rw [hk.2.2 "B3" (by decide)]; exact h.1.vB3
  · rw [hk.2.2 "B4" (by decide)]; exact h.1.vB4
  · rw [hk.2.2 "dn" (by decide)]; exact h.1.vdn
  · rw [hk.2.2 "nn1" (by decide)]; exact h.1.vn1
  · rw [hk.2.2 "LB" (by decide)]; exact h.1.vLB
  · rw [hk.1]; exact h.2.1
  · rw [hk.2.2 "VV" (by decide)]; exact h.2.2

/-- The cost of an edge day's job. -/
def Kedge (V VV : ℕ) : ℕ := 200 + (84 * VV + 20) + 2 * (44 * V + 20)

set_option maxHeartbeats 12800000 in
/-- **A job of an edge day.** -/
theorem edgeCom_run (ns : List ℕ) (i c : ℕ) (σ : Env) (hj : JC ns i c σ)
    (hA : σ.arrs "TK" = ns) (hVV : σ.vars "VV" = VM ns * VM ns)
    (hE : ∀ k < VM ns * VM ns, ns.getD (2 + k) 0 + 8 < B) (hlen : 2 + VM ns * VM ns ≤ ns.length)
    (hbig : 2 * (VM ns * VM ns) + 2 * VM ns + 2 * lN ns + 60 < B) (hM : Mag ns < B)
    (hi1 : lN ns * (nN ns + 1) ≤ i) (hi2 : i - lN ns * (nN ns + 1) < edgeN ns)
    (hcl : c < clN ns) :
    ∃ σ', Run B edgeCom σ σ' (Kedge (VM ns) (VM ns * VM ns)) ∧
      σ'.vars "pv" = (edgeDayN ns ((edgeCellsN ns).getD (i - lN ns * (nN ns + 1)) (0, 0)).1
        ((edgeCellsN ns).getD (i - lN ns * (nN ns + 1)) (0, 0)).2 c).1 ∧
      σ'.vars "dv" = (edgeDayN ns ((edgeCellsN ns).getD (i - lN ns * (nN ns + 1)) (0, 0)).1
        ((edgeCellsN ns).getD (i - lN ns * (nN ns + 1)) (0, 0)).2 c).2 ∧
      JStep XE σ σ' := by
  have hsp := VM_le_span ns
  have hlc := lN_le_span ns
  have hcls := cl_le ns
  have hspg := span_ge ns
  unfold Mag at hM
  have hjce : JCE ns i c σ := ⟨hj, hA, hVV⟩
  obtain ⟨hdi, hcc, hnn, hlc', hV, hdg, hS2, hB3, hB4, hdn, hn1, hLB⟩ := hj
  have hEle : edgeN ns ≤ VM ns * VM ns := by
    unfold edgeN
    have := List.countP_le_length (p := qualE ns) (l := List.range (VM ns * VM ns))
    simpa using this
  have hLBv : lN ns * (nN ns + 1) = VM ns + lN ns := by
    rw [Nat.mul_add, Nat.mul_one, VM_eq]
  have hdg1 : 1 ≤ degN ns := by unfold degN; omega
  have hi3 : i < VM ns * VM ns + VM ns + lN ns := by omega
  obtain ⟨hw1, hw2⟩ := edge_lt ns (i - lN ns * (nN ns + 1)) hi2
  have hpair := MisFind.edgeCells_getD ns (i - lN ns * (nN ns + 1))
  -- e := di - LB
  have small_di : small B σ (V "di") := by simp [small, hdi]; omega
  have small_LB : small B σ (V "LB") := by simp [small, hLB]; omega
  have s1 := asgE (B := B) "e" (sub (V "di") (V "LB")) σ (by
    simp [small, den, hdi, hLB]; omega)
  set σ1 := σ.setVar "e" (den σ (sub (V "di") (V "LB"))) with hσ1
  have he1 : σ1.vars "e" = i - lN ns * (nN ns + 1) := by simp [hσ1, den, Env.setVar, hdi, hLB]
  have k1 : JStep XE σ σ1 := JStep.setVar σ "e" _ (by simp [XE, AJ])
  have hc1 := hjce.step k1
  have hVdg := Vdg_le ns
  -- the scan for the edge
  obtain ⟨σ2, r2, hfw, hfw2, ha2, ho2, hf2⟩ := MisFind.findCom_run (B := B) ns (VM ns)
    (VM ns * VM ns) (i - lN ns * (nN ns + 1)) σ1 hE hlen (by omega) hc1.2.1 hc1.1.vV hc1.2.2 he1
  have k2 : JStep XE σ1 σ2 := ⟨ha2, ho2, fun y hy => hf2 y (fun h => hy (by simp [XE, h]))⟩
  have hc2 := hc1.step k2
  obtain ⟨w, hw⟩ : ∃ w, w = ((edgeCellsN ns).getD (i - lN ns * (nN ns + 1)) (0, 0)).1 := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w', w' = ((edgeCellsN ns).getD (i - lN ns * (nN ns + 1)) (0, 0)).2 :=
    ⟨_, rfl⟩
  rw [← hw] at hw1
  rw [← hw'] at hw2
  have hfw' : σ2.vars "fw" = w := by rw [hfw, hw, hpair]
  have hfw2' : σ2.vars "fw2" = w' := by rw [hfw2, hw', hpair]
  have hwV : w * VM ns ≤ VM ns * VM ns := Nat.mul_le_mul_right _ hw1.le
  have hw'V : w' * VM ns ≤ VM ns * VM ns := Nat.mul_le_mul_right _ hw2.le
  have hwd : w * degN ns ≤ VM ns * degN ns := Nat.mul_le_mul_right _ hw1.le
  have hw'd : w' * degN ns ≤ VM ns * degN ns := Nat.mul_le_mul_right _ hw2.le
  -- the first count: the neighbours of w before w'
  have s3 := asgE (B := B) "bs" (add (lit 2) (mul (V "fw") (V "V"))) σ2 (by
    simp [small, den, hfw', hc2.1.vV]; omega)
  set σ3 := σ2.setVar "bs" (den σ2 (add (lit 2) (mul (V "fw") (V "V")))) with hσ3
  have hbs3 : σ3.vars "bs" = 2 + w * VM ns := by simp [hσ3, den, Env.setVar, hfw', hc2.1.vV]
  have k3 : JStep XE σ2 σ3 := JStep.setVar σ2 "bs" _ (by simp [XE])
  have hc3 := hc2.step k3
  have hfw23 : σ3.vars "fw2" = w' := by simp [hσ3, Env.setVar, hfw2']
  have s4 := asgE (B := B) "bd" (V "fw2") σ3 (by simp [small, hfw23]; omega)
  set σ4 := σ3.setVar "bd" (den σ3 (V "fw2")) with hσ4
  have hbd4 : σ4.vars "bd" = w' := by simp [hσ4, den, Env.setVar, hfw23]
  have hbs4 : σ4.vars "bs" = 2 + w * VM ns := by simp [hσ4, Env.setVar, hbs3]
  have k4 : JStep XE σ3 σ4 := JStep.setVar σ3 "bd" _ (by simp [XE])
  have hc4 := hc3.step k4
  obtain ⟨σ5, r5, c5, a5, o5, f5⟩ := MisCount.cntCom_run (B := B) ns (2 + w * VM ns) w' σ4
    (fun k hk => by
      have := hE (w * VM ns + k) (MisCheck.cell_lt' _ _ _ hw1 (by omega))
      rwa [← Nat.add_assoc] at this)
    (by have := MisCheck.cell_lt' (VM ns) w w' hw1 hw2; omega) (by omega) hc4.2.1 hbs4 hbd4
  have k5 : JStep XE σ4 σ5 := ⟨a5, o5, fun y hy => f5 y (fun h => hy (by
    simp only [MisCount.AN, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp [XE, MisCount.AN]))⟩
  have hc5 := hc4.step k5
  have hk1 : σ5.vars "cnt" = idxN ns w w' := by rw [c5, idx_eq]
  have hi1 := idxN_le ns w w'
  have hi2 := idxN_le ns w' w
  have hfw5 : σ5.vars "fw" = w := by
    rw [f5 "fw" (by simp [MisCount.AN])]; simp [hσ4, hσ3, Env.setVar, hfw']
  have hfw25 : σ5.vars "fw2" = w' := by
    rw [f5 "fw2" (by simp [MisCount.AN])]; simp [hσ4, hσ3, Env.setVar, hfw2']
  -- k1 := cnt
  have s6 := asgE (B := B) "k1" (V "cnt") σ5 (by simp [small, hk1]; omega)
  set σ6 := σ5.setVar "k1" (den σ5 (V "cnt")) with hσ6
  have hk16 : σ6.vars "k1" = idxN ns w w' := by simp [hσ6, den, Env.setVar, hk1]
  have hfw6 : σ6.vars "fw" = w := by simp [hσ6, Env.setVar, hfw5]
  have hfw26 : σ6.vars "fw2" = w' := by simp [hσ6, Env.setVar, hfw25]
  have k6 : JStep XE σ5 σ6 := JStep.setVar σ5 "k1" _ (by simp [XE])
  have hc6 := hc5.step k6
  -- the second count: the neighbours of w' before w
  have s7 := asgE (B := B) "bs" (add (lit 2) (mul (V "fw2") (V "V"))) σ6 (by
    simp [small, den, hfw26, hc6.1.vV]; omega)
  set σ7 := σ6.setVar "bs" (den σ6 (add (lit 2) (mul (V "fw2") (V "V")))) with hσ7
  have hbs7 : σ7.vars "bs" = 2 + w' * VM ns := by simp [hσ7, den, Env.setVar, hfw26, hc6.1.vV]
  have hfw7 : σ7.vars "fw" = w := by simp [hσ7, Env.setVar, hfw6]
  have hfw27 : σ7.vars "fw2" = w' := by simp [hσ7, Env.setVar, hfw26]
  have hk17 : σ7.vars "k1" = idxN ns w w' := by simp [hσ7, Env.setVar, hk16]
  have k7 : JStep XE σ6 σ7 := JStep.setVar σ6 "bs" _ (by simp [XE])
  have hc7 := hc6.step k7
  have s8 := asgE (B := B) "bd" (V "fw") σ7 (by simp [small, hfw7]; omega)
  set σ8 := σ7.setVar "bd" (den σ7 (V "fw")) with hσ8
  have hbd8 : σ8.vars "bd" = w := by simp [hσ8, den, Env.setVar, hfw7]
  have hbs8 : σ8.vars "bs" = 2 + w' * VM ns := by simp [hσ8, Env.setVar, hbs7]
  have k8 : JStep XE σ7 σ8 := JStep.setVar σ7 "bd" _ (by simp [XE])
  have hc8 := hc7.step k8
  obtain ⟨σ9, r9, c9, a9, o9, f9⟩ := MisCount.cntCom_run (B := B) ns (2 + w' * VM ns) w σ8
    (fun k hk => by
      have := hE (w' * VM ns + k) (MisCheck.cell_lt' _ _ _ hw2 (by omega))
      rwa [← Nat.add_assoc] at this)
    (by have := MisCheck.cell_lt' (VM ns) w' w hw2 hw1; omega) (by omega) hc8.2.1 hbs8 hbd8
  have k9 : JStep XE σ8 σ9 := ⟨a9, o9, fun y hy => f9 y (fun h => hy (by
    simp only [MisCount.AN, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp [XE, MisCount.AN]))⟩
  have hc9 := hc8.step k9
  have hk2 : σ9.vars "cnt" = idxN ns w' w := by rw [c9, idx_eq]
  have hfw9 : σ9.vars "fw" = w := by
    rw [f9 "fw" (by simp [MisCount.AN])]; simp [hσ8, Env.setVar, hfw7]
  have hfw29 : σ9.vars "fw2" = w' := by
    rw [f9 "fw2" (by simp [MisCount.AN])]; simp [hσ8, Env.setVar, hfw27]
  have hk19 : σ9.vars "k1" = idxN ns w w' := by
    rw [f9 "k1" (by simp [MisCount.AN])]; simp [hσ8, Env.setVar, hk17]
  have s10 := asgE (B := B) "k2" (V "cnt") σ9 (by simp [small, hk2]; omega)
  set σ10 := σ9.setVar "k2" (den σ9 (V "cnt")) with hσ10
  have hk210 : σ10.vars "k2" = idxN ns w' w := by simp [hσ10, den, Env.setVar, hk2]
  have hfw10 : σ10.vars "fw" = w := by simp [hσ10, Env.setVar, hfw9]
  have hfw210 : σ10.vars "fw2" = w' := by simp [hσ10, Env.setVar, hfw29]
  have hk110 : σ10.vars "k1" = idxN ns w w' := by simp [hσ10, Env.setVar, hk19]
  have k10 : JStep XE σ9 σ10 := JStep.setVar σ9 "k2" _ (by simp [XE])
  have hc10 := hc9.step k10
  obtain ⟨σ', rD, e1, e2, stD⟩ := edgeDisp_run (B := B) ns i c w w' σ10 hc10.1 hfw10 hfw210 hk110
    hk210 hw1 hw2 hcl hM
  have kD : JStep XE σ10 σ' := stD.mono (fun y hy => by simp only [XE, List.mem_append]; left; left; left; exact hy)
  refine ⟨σ', (s1.seq (r2.seq (s3.seq (s4.seq (r5.seq (s6.seq (s7.seq (s8.seq (r9.seq
    (s10.seq rD)))))))))).mono (by
      unfold Kedge; simp [Expr.size] <;> omega), ?_, ?_,
    (((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8).trans k9).trans
      k10).trans kD⟩
  · rw [← hw, ← hw']; exact e1
  · rw [← hw, ← hw']; exact e2

/-- The processing time and the due date of the job of client `cc` on day `di`. -/
def jobCom : Com :=
  .ite (.lt (V "di") (V "LB"))
    (.seq (.assign "vb" (div (V "di") (V "nn1")))
      (.seq (.assign "va" (sub (V "di") (mul (V "vb") (V "nn1"))))
        (.ite (.lt (V "va") (V "nn")) vertexCom validCom)))
    edgeCom

/-- The cost of a job. -/
def Kjob (V VV : ℕ) : ℕ := 300 + (84 * VV + 20) + 2 * (44 * V + 20)

set_option maxHeartbeats 12800000 in
/-- **The job of a client on a day.** -/
theorem jobCom_run (ns : List ℕ) (i c : ℕ) (σ : Env) (hc : JCE ns i c σ)
    (hE : ∀ k < VM ns * VM ns, ns.getD (2 + k) 0 + 8 < B) (hlen : 2 + VM ns * VM ns ≤ ns.length)
    (hbig : 2 * (VM ns * VM ns) + 2 * VM ns + 2 * lN ns + 60 < B) (hM : Mag ns < B)
    (hn0 : 0 < nN ns) (hi : i < daysN ns) (hcl : c < clN ns) :
    ∃ σ', Run B jobCom σ σ' (Kjob (VM ns) (VM ns * VM ns)) ∧
      σ'.vars "pv" = (jobN ns i c).1 ∧ σ'.vars "dv" = (jobN ns i c).2 ∧ JStep XE σ σ' := by
  have hc0 := hc
  obtain ⟨hj, hA, hVV⟩ := hc
  have hj0 := hj
  have hsp := VM_le_span ns
  have hlc := lN_le_span ns
  have hspg := span_ge ns
  have hLBv : lN ns * (nN ns + 1) = VM ns + lN ns := by rw [Nat.mul_add, Nat.mul_one, VM_eq]
  obtain ⟨hdi, hcc, hnn, hlc', hV, hdg, hS2, hB3, hB4, hdn, hn1, hLB⟩ := hj
  have hEle : edgeN ns ≤ VM ns * VM ns := by
    unfold edgeN
    have := List.countP_le_length (p := qualE ns) (l := List.range (VM ns * VM ns))
    simpa using this
  unfold daysN at hi
  unfold Mag at hM
  have hdg1 : 1 ≤ degN ns := by unfold degN; omega
  have hnn_le : nN ns ≤ degN ns * nN ns := Nat.le_mul_of_pos_left _ hdg1
  have hdiB : small B σ (V "di") := by simp [small, hdi]; omega
  have hLBB : small B σ (V "LB") := by simp [small, hLB]; omega
  unfold jobN
  by_cases h1 : i < lN ns * (nN ns + 1)
  · have hT : (Cond.lt (V "di") (V "LB")).evalB B σ = some true :=
      condLt_true _ _ σ hdiB hLBB (by simp [den, hdi, hLB]; omega)
    rw [if_pos h1]
    have hn1B : small B σ (V "nn1") := by simp [small, hn1]; omega
    have hn1pos : 0 < nN ns + 1 := by omega
    have hdivle : i / (nN ns + 1) ≤ i := Nat.div_le_self _ _
    have hbmul : i / (nN ns + 1) * (nN ns + 1) ≤ i := Nat.div_mul_le_self _ _
    have s1 := asgE (B := B) "vb" (div (V "di") (V "nn1")) σ (by
      simp [small, den, hdi, hn1]; omega)
    set σ1 := σ.setVar "vb" (den σ (div (V "di") (V "nn1"))) with hσ1
    have hb1 : σ1.vars "vb" = i / (nN ns + 1) := by simp [hσ1, den, Env.setVar, hdi, hn1]
    have hbl : i / (nN ns + 1) < lN ns := (Nat.div_lt_iff_lt_mul hn1pos).2 h1
    have k1 : JStep XE σ σ1 := JStep.setVar σ "vb" _ (by simp [XE, AJ])
    have hc1 := hc0.step k1
    have s2 := asgE (B := B) "va" (sub (V "di") (mul (V "vb") (V "nn1"))) σ1 (by
      simp [small, den, Env.setVar, hc1.1.vdi, hc1.1.vn1, hb1]
      omega)
    set σ2 := σ1.setVar "va" (den σ1 (sub (V "di") (mul (V "vb") (V "nn1")))) with hσ2
    have ha2 : σ2.vars "va" = i - i / (nN ns + 1) * (nN ns + 1) := by
      simp [hσ2, den, Env.setVar, hc1.1.vdi, hc1.1.vn1, hb1]
    have hb2 : σ2.vars "vb" = i / (nN ns + 1) := by simp [hσ2, Env.setVar, hb1]
    have k2 : JStep XE σ1 σ2 := JStep.setVar σ1 "va" _ (by simp [XE, AJ])
    have hc2 := hc1.step k2
    have hmod : i - i / (nN ns + 1) * (nN ns + 1) = i % (nN ns + 1) := MisFind.mod_eq_sub i _
    have hmlt : i % (nN ns + 1) < nN ns + 1 := Nat.mod_lt _ hn1pos
    have hva : small B σ2 (V "va") := by simp [small, ha2]; omega
    have hnnB : small B σ2 (V "nn") := by simp [small, hc2.1.vnn]; omega
    by_cases h2 : i % (nN ns + 1) < nN ns
    · have hT2 : (Cond.lt (V "va") (V "nn")).evalB B σ2 = some true :=
        condLt_true _ _ σ2 hva hnnB (by simp [den, ha2, hc2.1.vnn]; omega)
      have hw0 : i / (nN ns + 1) * nN ns + i % (nN ns + 1) < VM ns := by
        have := Nat.mul_le_mul_right (nN ns) (show i / (nN ns + 1) + 1 ≤ lN ns by omega)
        rw [Nat.add_mul, Nat.one_mul, ← VM_eq] at this
        omega
      obtain ⟨σ', r, e1, e2, st⟩ := vertexCom_run (B := B) ns i c (i / (nN ns + 1))
        (i % (nN ns + 1)) σ2 hc2.1 hb2 (by rw [ha2, hmod]) h2 hw0 hcl hM
      refine ⟨σ', (Run.ite_true hT ((s1.seq (s2.seq (Run.ite_true hT2 r))))).mono
        (by unfold Kjob; simp [Cond.size, Expr.size] <;> omega), ?_, ?_,
        ((k1.trans k2).trans (st.mono (fun y hy => by simp only [XE, List.mem_append]; left; left; left; exact hy)))⟩
      · rw [if_pos h2]; exact e1
      · rw [if_pos h2]; exact e2
    · have hF2 : (Cond.lt (V "va") (V "nn")).evalB B σ2 = some false :=
        condLt_false _ _ σ2 hva hnnB (by simp [den, ha2, hc2.1.vnn]; omega)
      obtain ⟨σ', r, e1, e2, st⟩ := validCom_run (B := B) ns i c (i / (nN ns + 1)) σ2 hc2.1 hb2 hbl
        hn0 hcl hM
      refine ⟨σ', (Run.ite_true hT ((s1.seq (s2.seq (Run.ite_false hF2 r))))).mono
        (by unfold Kjob; simp [Cond.size, Expr.size] <;> omega), ?_, ?_,
        ((k1.trans k2).trans (st.mono (fun y hy => by simp only [XE, List.mem_append]; left; left; left; exact hy)))⟩
      · rw [if_neg h2]; exact e1
      · rw [if_neg h2]; exact e2
  · have hF : (Cond.lt (V "di") (V "LB")).evalB B σ = some false :=
      condLt_false _ _ σ hdiB hLBB (by simp [den, hdi, hLB]; omega)
    rw [if_neg h1]
    obtain ⟨σ', r, e1, e2, st⟩ := edgeCom_run (B := B) ns i c σ hj0 hA hVV hE hlen hbig hM
      (by omega) (by omega) hcl
    exact ⟨σ', (Run.ite_false hF r).mono (by
      unfold Kjob Kedge; simp [Cond.size, Expr.size] <;> omega), e1, e2, st⟩

end Lax117284Proofs.Machine.MisJob
