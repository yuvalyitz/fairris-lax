import Lax117284Proofs.Machine.IlpSpec
import Lax117284Proofs.Machine.IlpProg
import Lax808846Proofs.Transfer
import Lax808846Proofs.Tactic

/-!
The context of the machine: what never changes while certificates are decoded, and how a phase is
shown to preserve it.

`Ctx n cnt bb σ` says that the constants of the header (`N M n T Z V K R D rb tn nn bb`) hold their
values, that `z` is the word of the integer program and that every working array has its length.
Every phase leaves the lengths of all arrays alone (`Run.len_arrs`), so the context is preserved as
soon as the phase does not assign to the constants nor store into `z` (`Ctx.stable`).
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients

/-! ### Frames -/

theorem bigStep_len_arrs {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStep c σ σ' k) (a : String) :
    (σ'.arrs a).length = (σ.arrs a).length := by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => exact length_arrs_setArr _ _ _ _ _
  | seq _ _ ih ih' => rw [ih', ih]
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => rw [ih', ih]
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem run_len_arrs {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) (a : String) :
    (σ'.arrs a).length = (σ.arrs a).length := by
  obtain ⟨_, _, hbs⟩ := h.bigStep; exact bigStep_len_arrs hbs a

/-- What a run of `c` leaves alone. -/
def Keeps (c : Com) (σ σ' : Env) : Prop :=
  (∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y) ∧ (∀ a, a ∉ c.warrs → σ'.arrs a = σ.arrs a) ∧
    (∀ a, (σ'.arrs a).length = (σ.arrs a).length)

theorem run_keeps {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) : Keeps c σ σ' :=
  ⟨fun y hy => h.frame_var y hy, fun a ha => h.frame_arr a ha, fun a => run_len_arrs h a⟩

/-- Every specification also says what the command leaves alone (`Spec.frame` and the lengths). -/
theorem spec_keeps {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com} {K : ℕ}
    (h : Spec B P c Q K) : Spec B P c (fun σ σ' => Q σ σ' ∧ Keeps c σ σ') K := by
  intro σ hσ
  obtain ⟨σ', hr, hq⟩ := h σ hσ
  exact ⟨σ', hr, hq, run_keeps hr⟩

/-- A property of the environment that is preserved by every run of `c` that leaves alone the
names it depends on. -/
def Stable (c : Com) (C : Env → Prop) : Prop := ∀ σ σ', C σ → Keeps c σ σ' → C σ'

theorem Stable.and {c : Com} {C D : Env → Prop} (h1 : Stable c C) (h2 : Stable c D) :
    Stable c (fun σ => C σ ∧ D σ) :=
  fun σ σ' h hk => ⟨h1 σ σ' h.1 hk, h2 σ σ' h.2 hk⟩

theorem stable_true (c : Com) : Stable c (fun _ => True) := fun _ _ _ _ => trivial

theorem stable_var {c : Com} (y : String) (P : ℕ → Prop) (h : y ∉ c.wvars) :
    Stable c (fun σ => P (σ.vars y)) :=
  fun σ σ' hσ hk => by show P (σ'.vars y); rw [hk.1 y h]; exact hσ

theorem stable_arr {c : Com} (a : String) (P : List ℕ → Prop) (h : a ∉ c.warrs) :
    Stable c (fun σ => P (σ.arrs a)) :=
  fun σ σ' hσ hk => by show P (σ'.arrs a); rw [hk.2.1 a h]; exact hσ

theorem stable_len {c : Com} (a : String) (P : ℕ → Prop) :
    Stable c (fun σ => P (σ.arrs a).length) :=
  fun σ σ' hσ hk => by show P (σ'.arrs a).length; rw [hk.2.2 a]; exact hσ

/-! ### The context -/

/-- The constants of the header, the word, and the lengths of the working arrays. -/
structure Ctx (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (σ : Env) : Prop where
  hN : σ.vars "N" = nN n
  hM : σ.vars "M" = nM n
  hn : σ.vars "n" = n
  hT : σ.vars "T" = nT n
  hZ : σ.vars "Z" = nZ n
  hV : σ.vars "V" = nV n
  hK : σ.vars "K" = Kn n
  hR : σ.vars "R" = Rd n
  hD : σ.vars "D" = Dn n
  hrb : σ.vars "rb" = 2 + nM n * nN n
  htn : σ.vars "tn" = 2 + nT n * nN n
  hnn : σ.vars "nn" = n * n
  hbb : σ.vars "bb" = bb
  hz : σ.arrs "z" = ilpWord n cnt bb
  ldg : (σ.arrs "dg").length = Dn n
  lhl : (σ.arrs "hl").length = nT n
  lkd : (σ.arrs "kd").length = nN n
  lrk : (σ.arrs "rkA").length = nN n
  lsg : (σ.arrs "sg").length = nT n
  lS : (σ.arrs "S").length = n
  lwv : (σ.arrs "wv").length = nN n
  les : (σ.arrs "es").length = nT n
  lxv : (σ.arrs "xv").length = nN n

/-- The names the context depends on. -/
def ctxVars : List String :=
  ["N", "M", "n", "T", "Z", "V", "K", "R", "D", "rb", "tn", "nn", "bb"]

theorem Ctx.stable {c : Com} {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} (hv : ∀ y ∈ ctxVars, y ∉ c.wvars)
    (hz : "z" ∉ c.warrs) : Stable c (Ctx n cnt bb) := by
  intro σ σ' h hk
  have hV : ∀ y, y ∈ ctxVars → σ'.vars y = σ.vars y := fun y hy => hk.1 y (hv y hy)
  exact
    { hN := by rw [hV "N" (by simp [ctxVars])]; exact h.hN
      hM := by rw [hV "M" (by simp [ctxVars])]; exact h.hM
      hn := by rw [hV "n" (by simp [ctxVars])]; exact h.hn
      hT := by rw [hV "T" (by simp [ctxVars])]; exact h.hT
      hZ := by rw [hV "Z" (by simp [ctxVars])]; exact h.hZ
      hV := by rw [hV "V" (by simp [ctxVars])]; exact h.hV
      hK := by rw [hV "K" (by simp [ctxVars])]; exact h.hK
      hR := by rw [hV "R" (by simp [ctxVars])]; exact h.hR
      hD := by rw [hV "D" (by simp [ctxVars])]; exact h.hD
      hrb := by rw [hV "rb" (by simp [ctxVars])]; exact h.hrb
      htn := by rw [hV "tn" (by simp [ctxVars])]; exact h.htn
      hnn := by rw [hV "nn" (by simp [ctxVars])]; exact h.hnn
      hbb := by rw [hV "bb" (by simp [ctxVars])]; exact h.hbb
      hz := by rw [hk.2.1 "z" hz]; exact h.hz
      ldg := by rw [hk.2.2 "dg"]; exact h.ldg
      lhl := by rw [hk.2.2 "hl"]; exact h.lhl
      lkd := by rw [hk.2.2 "kd"]; exact h.lkd
      lrk := by rw [hk.2.2 "rkA"]; exact h.lrk
      lsg := by rw [hk.2.2 "sg"]; exact h.lsg
      lS := by rw [hk.2.2 "S"]; exact h.lS
      lwv := by rw [hk.2.2 "wv"]; exact h.lwv
      les := by rw [hk.2.2 "es"]; exact h.les
      lxv := by rw [hk.2.2 "xv"]; exact h.lxv }

/-- Setting a scalar that is not a constant keeps the context. -/
theorem Ctx.setVar {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {σ : Env} (h : Ctx n cnt bb σ) {y : String}
    (hy : y ∉ ctxVars) (v : ℕ) : Ctx n cnt bb (σ.setVar y v) := by
  have hne : ∀ x ∈ ctxVars, x ≠ y := fun x hx hxy => hy (hxy ▸ hx)
  have e : ∀ x ∈ ctxVars, (σ.setVar y v).vars x = σ.vars x := fun x hx => by
    simp [Env.setVar, hne x hx]
  exact
    { hN := by rw [e "N" (by simp [ctxVars])]; exact h.hN
      hM := by rw [e "M" (by simp [ctxVars])]; exact h.hM
      hn := by rw [e "n" (by simp [ctxVars])]; exact h.hn
      hT := by rw [e "T" (by simp [ctxVars])]; exact h.hT
      hZ := by rw [e "Z" (by simp [ctxVars])]; exact h.hZ
      hV := by rw [e "V" (by simp [ctxVars])]; exact h.hV
      hK := by rw [e "K" (by simp [ctxVars])]; exact h.hK
      hR := by rw [e "R" (by simp [ctxVars])]; exact h.hR
      hD := by rw [e "D" (by simp [ctxVars])]; exact h.hD
      hrb := by rw [e "rb" (by simp [ctxVars])]; exact h.hrb
      htn := by rw [e "tn" (by simp [ctxVars])]; exact h.htn
      hnn := by rw [e "nn" (by simp [ctxVars])]; exact h.hnn
      hbb := by rw [e "bb" (by simp [ctxVars])]; exact h.hbb
      hz := h.hz, ldg := h.ldg, lhl := h.lhl, lkd := h.lkd, lrk := h.lrk, lsg := h.lsg,
      lS := h.lS, lwv := h.lwv, les := h.les, lxv := h.lxv }

end Lax117284Proofs.Machine.Ilp
