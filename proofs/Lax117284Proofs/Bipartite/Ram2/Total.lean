import Lax117284Proofs.Bipartite.Ram2.SymmFill
import Lax117284Proofs.Bipartite.Ram2.Checks

/-!
The total program: read the word into `t`; answer `0` if it is shorter than four entries; read
the header; run the syntactic checks and the degree pass (which checks `crosses`), each guarded
by the flag `ok`; if the flag stands, build the symmetrized word in `a` and run Kuhn's algorithm
on it, answering whether every left vertex is matched; otherwise answer `0`.

This file: the program, the `ok`-guard combinator, and what every phase leaves alone
(`Untouched`: the search's own arrays and scalars, the output tape).
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteDecision
open scoped Classical

variable {B : ℕ}

/-- Write whether the count is `n`. -/
def finalC : Com :=
  .ite (.eq (.var "count") (.var "n")) (.write (.lit 1)) (.write (.lit 0))

/-- **The heavy path**: symmetrize, search from every left vertex, count, compare. -/
def heavyTot : Com :=
  .seq prefixCom
    (.seq posCom
      (.seq fillPass
        (.seq (.assign "m" (.sub (.var "V") (.var "n")))
          (.seq (.assign "l0" (.lit 0)) (.seq outerLoop (.seq countCom finalC))))))

/-- A phase run only while the flag stands. -/
def guarded (c : Com) : Com := .ite (.eq (.var "ok") (.lit 1)) c .skip

/-- **The total program**, after the length has been read into `len`. -/
def totCom : Com :=
  .seq readT
    (.ite (.lt (.var "len") (.lit 4)) (.write (.lit 0))
      (.seq hdrT
        (.seq (.assign "ok" (.lit 1))
          (.seq chk1
            (.seq (guarded chk2)
              (.seq (guarded chk3)
                (.seq (guarded degPass)
                  (.ite (.eq (.var "ok") (.lit 1)) heavyTot (.write (.lit 0))))))))))

/-- The array lengths declared to the run. -/
def extT (x : List ℕ) : String → ℕ := fun a =>
  if a = "t" ∨ a = "a" then x.length
  else if a = "deg" ∨ a = "pos" then nw x
  else if a = "vis" ∨ a = "mu" then Vw x - nw x
  else Vw x - nw x + 1

/-! ### What the phases leave alone -/

/-- The search's scalars and arrays are as at the start, and nothing has been written. -/
structure Untouched (x : List ℕ) (σ : Env) : Prop where
  top : σ.vars "top" = 0
  vis : σ.arrs "vis" = List.replicate (Vw x - nw x) 0
  mu : σ.arrs "mu" = List.replicate (Vw x - nw x) 0
  stkL : σ.arrs "stkL" = List.replicate (Vw x - nw x + 1) 0
  stkR : σ.arrs "stkR" = List.replicate (Vw x - nw x + 1) 0
  stkX : σ.arrs "stkX" = List.replicate (Vw x - nw x + 1) 0
  out : σ.out = []

/-- A run of a command that writes neither `top` nor the search's arrays nor the output keeps
`Untouched`. -/
theorem Untouched.of_run {x : List ℕ} {σ σ' : Env} {c : Com} {K : ℕ} (h : Untouched x σ)
    (hr : Run B c σ σ' K) (htop : "top" ∉ c.wvars)
    (harr : ∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ c.warrs) (hw : c.NoWrite) :
    Untouched x σ' := by
  have hv := hr.frame_var "top" htop
  have ha : ∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], σ'.arrs a = σ.arrs a :=
    fun a ha => hr.frame_arr a (harr a ha)
  refine ⟨by rw [hv]; exact h.top, ?_, ?_, ?_, ?_, ?_, by rw [hr.out_eq hw]; exact h.out⟩
  · rw [ha "vis" (by simp)]; exact h.vis
  · rw [ha "mu" (by simp)]; exact h.mu
  · rw [ha "stkL" (by simp)]; exact h.stkL
  · rw [ha "stkR" (by simp)]; exact h.stkR
  · rw [ha "stkX" (by simp)]; exact h.stkX

theorem Untouched.setVar {x : List ℕ} {σ : Env} (h : Untouched x σ) (y : String) (hy : y ≠ "top")
    (v : ℕ) : Untouched x (σ.setVar y v) :=
  ⟨by simp [Ne.symm hy]; exact h.top, h.vis, h.mu, h.stkL, h.stkR, h.stkX, h.out⟩

/-- The frame conditions of the phases before the search, read off their syntax. -/
theorem frame_readT : "top" ∉ readT.wvars ∧
    (∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ readT.warrs) ∧ readT.NoWrite := by
  simp [readT, readTBody, Com.wvars, Com.warrs, Com.NoWrite]

theorem frame_chk1 : "top" ∉ chk1.wvars ∧
    (∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ chk1.warrs) ∧ chk1.NoWrite := by
  simp [chk1, Com.wvars, Com.warrs, Com.NoWrite]

theorem frame_chk2 : "top" ∉ chk2.wvars ∧
    (∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ chk2.warrs) ∧ chk2.NoWrite := by
  simp [chk2, chk2Body, Com.wvars, Com.warrs, Com.NoWrite]

theorem frame_chk3 : "top" ∉ chk3.wvars ∧
    (∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ chk3.warrs) ∧ chk3.NoWrite := by
  simp [chk3, chk3Body, Com.wvars, Com.warrs, Com.NoWrite]

theorem frame_degPass : "top" ∉ degPass.wvars ∧
    (∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ degPass.warrs) ∧ degPass.NoWrite := by
  simp [degPass, rowIter, degBody, degThen, degElse, Com.wvars, Com.warrs, Com.NoWrite]

theorem frame_prefix : "top" ∉ prefixCom.wvars ∧
    (∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ prefixCom.warrs) ∧ prefixCom.NoWrite := by
  simp [prefixCom, prefixBody, prefixThen, prefixElse, Com.wvars, Com.warrs, Com.NoWrite]

theorem frame_pos : "top" ∉ posCom.wvars ∧
    (∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ posCom.warrs) ∧ posCom.NoWrite := by
  simp [posCom, posBody, Com.wvars, Com.warrs, Com.NoWrite]

theorem frame_fillPass : "top" ∉ fillPass.wvars ∧
    (∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ fillPass.warrs) ∧ fillPass.NoWrite := by
  simp [fillPass, rowIter, fillBody, fillThen, fillElse, Com.wvars, Com.warrs, Com.NoWrite]

/-- The arrays `deg`, `pos`, `a` are untouched by the checks. -/
theorem warrs_checks : ∀ a ∈ ["deg", "pos", "a"],
    a ∉ readT.warrs ∧ a ∉ hdrT.warrs ∧ a ∉ chk1.warrs ∧ a ∉ chk2.warrs ∧ a ∉ chk3.warrs := by
  simp [readT, readTBody, hdrT, chk1, chk2, chk2Body, chk3, chk3Body, Com.warrs]

theorem warrs_degPass : ∀ a ∈ ["pos", "a"], a ∉ degPass.warrs := by
  simp [degPass, rowIter, degBody, degThen, degElse, Com.warrs]

theorem warrs_prefix : "pos" ∉ prefixCom.warrs := by
  simp [prefixCom, prefixBody, prefixThen, prefixElse, Com.warrs]

/-! ### The guard -/

/-- **A guarded phase.** If the flag stands, the phase runs and refines the flag by `Q'`; if not,
nothing happens and the flag stays down. -/
theorem guarded_run {Q Q' : Prop} {c : Com} {σ : Env} {Kc : ℕ} (Post : Env → Prop) (h1B : 1 < B)
    (hok : σ.vars "ok" ≤ 1) (hiff : σ.vars "ok" = 1 ↔ Q) (hpost : Post σ)
    (hc : σ.vars "ok" = 1 → ∃ σ' K, Run B c σ σ' K ∧ K ≤ Kc ∧ σ'.vars "ok" ≤ 1 ∧
      (σ'.vars "ok" = 1 ↔ Q') ∧ Post σ') :
    ∃ σ' K, Run B (guarded c) σ σ' K ∧ K ≤ 5 + (if σ.vars "ok" = 1 then Kc else 0) ∧
      σ'.vars "ok" ≤ 1 ∧ (σ'.vars "ok" = 1 ↔ Q ∧ Q') ∧ Post σ' := by
  have hokB : σ.vars "ok" < B := by omega
  by_cases h : σ.vars "ok" = 1
  · obtain ⟨σ', K, hr, hK, hok', hiff', hp'⟩ := hc h
    have hcond := RunStep.cond_eq_true B σ (.var "ok") (.lit 1) _ _ (RunStep.eval_var B σ "ok" hokB)
      (RunStep.eval_lit B 1 σ h1B) h
    refine ⟨σ', _, RunStep.ite_true B _ c .skip σ σ' K hcond hr, by rw [if_pos h]; simp; omega,
      hok', ?_, hp'⟩
    rw [hiff']
    exact ⟨fun hq' => ⟨hiff.1 h, hq'⟩, fun hq => hq.2⟩
  · have hcond := RunStep.cond_eq_false B σ (.var "ok") (.lit 1) _ _ (RunStep.eval_var B σ "ok" hokB)
      (RunStep.eval_lit B 1 σ h1B) h
    refine ⟨σ, _, RunStep.ite_false B _ c .skip σ σ 1 hcond (RunStep.skip B σ),
      by rw [if_neg h]; simp, hok, ?_, hpost⟩
    exact ⟨fun h' => absurd h' h, fun hq => absurd (hiff.2 hq.1) h⟩

/-- The cost of the total program: linear in the word, plus `400 · (|x| + 1) · n` for the
searches of a well-formed word. -/
noncomputable def totCost (x : List ℕ) : ℕ :=
  600 * (x.length + 1) + (if WellFormed x then 400 * ((x.length + 1) * nw x) else 0)

end Lax117284Proofs.Bipartite.Ram2
