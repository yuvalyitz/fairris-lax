import Lax117284Proofs.Machine.TwMain2

/-!
The main program, phase by phase: the word of the graph and the run of the decomposition step.
-/

namespace Lax117284Proofs.Machine.TwMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol
open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding
open Lax117284Proofs.Machine.TwRam (opcode fa fb fc Small)

variable {B : ℕ}

/-- The scalars the guarded branch writes before the choice of the answer. -/
def VG : List String := ["mask", "bb"] ++ TwGraph.SGW ++ TwSetup.SI

/-- The arrays it writes. -/
def AG : List String := ["Y", "OP", "XA", "XB", "XC", "M", "O"]

/-- What the graph and the run of the decomposition step cost. -/
def Kgi (m n t : ℕ) (plen : ℕ) : ℕ :=
  30 + ((214 * m + 90 + 20 + 4) * (n * n) + 6 + 60) + (13 * plen + 1 + 30 + 250 * (t + 1))

theorem phaseGI {x : List ℕ} {I : Instance} {k : ℕ} (hdec : EncodesUniform x I k)
    (prog : Program) (ext : String → ℕ) (Wp Pn OL w t : ℕ) (z : List ℕ) (σ2 : Env)
    (hW : W ext ["X"] (VR ++ TwPrep.SPrep) σ2)
    (hXa : σ2.arrs "X" = x) (hn : σ2.vars "n" = I.clients) (hm : σ2.vars "m" = I.days)
    (hmn : σ2.vars "mn" = I.days * I.clients) (hw2 : σ2.vars "w" = w)
    (hwp : σ2.vars "wp" = Wp) (hP : σ2.vars "P" = Pn)
    (hextY : ext "Y" = I.clients * I.clients + 2) (hextOP : ext "OP" = prog.length)
    (hextXA : ext "XA" = prog.length) (hextXB : ext "XB" = prog.length)
    (hextXC : ext "XC" = prog.length) (hextM : ext "M" = Pn) (hextO : ext "O" = OL)
    (hPn : Pn = 2 ^ Wp) (hsm : Small Wp prog)
    (hRuns : RunsTo Wp prog (TwGraph.gwList x I.clients I.days ++ [w]) z t) (hOLt : t < OL)
    (hlit : ∀ ins ∈ prog, opcode ins + 3 < B ∧ fa ins + 3 < B ∧ fb ins + 3 < B ∧ fc ins + 3 < B)
    -- the bounds
    (h2m : 2 ^ I.days + 8 < B) (hnB : I.clients + 8 < B) (hmB : I.days + 8 < B)
    (hnn : I.clients * I.clients + 8 < B) (hLX : x.length + 8 < B) (hXB : ∀ v ∈ x, v < B)
    (hwB : w + 8 < B)
    (hyP : ∀ v ∈ TwGraph.gwList x I.clients I.days ++ [w], v < Pn)
    (hyPn : I.clients * I.clients + 2 < Pn)
    (bPP : Pn * Pn < B) (b2 : Pn + Pn < B)
    (bnd : prog.length + OL + (I.clients * I.clients + 2) + Pn + 24 < B) (hOL : 0 < OL) :
    ∃ σ5, Run B (.seq TwPrep.maskCom (.seq TwGraph.gwCom (TwSetup.interpCom prog))) σ2 σ5
        (Kgi I.days I.clients t prog.length) ∧
      z = (σ5.arrs "O").take (σ5.vars "ol") ∧ (σ5.arrs "O").length = OL ∧
      σ5.arrs "Y" = TwGraph.gwList x I.clients I.days ++ [w] ∧
      σ5.arrs "X" = x ∧ W ext ("X" :: AG) (VR ++ TwPrep.SPrep ++ VG) σ5 ∧
      (∀ v, v ∉ VG → σ5.vars v = σ2.vars v) ∧ σ5.vars "mask" = 2 ^ I.days - 1 ∧
      σ5.vars "bb" = 2 ^ I.days ∧ σ5.out = σ2.out := by
  have hmB' : I.days + 3 < B := by omega
  obtain ⟨σ3, r3, e3⟩ := TwPrep.maskCom_run (B := B) σ2 I.days hm (by omega)
  have hv3 : ∀ v, v ≠ "mask" → v ≠ "bb" → σ3.vars v = σ2.vars v := by
    intro v h1 h2; rw [e3]; simp [Env.setVar, h1, h2]
  have ha3 : σ3.arrs = σ2.arrs := by rw [e3]; simp [Env.setVar]
  have ho3 : σ3.out = σ2.out := by rw [e3]; simp [Env.setVar]
  have hmask3 : σ3.vars "mask" = 2 ^ I.days - 1 := by rw [e3]; simp [Env.setVar]
  have hXlen : 2 + 2 * (I.days * I.clients) + 1 ≤ x.length := by
    have := ClientsWord.len_eq hdec; omega
  have hY3 : σ3.arrs "Y" = List.replicate (I.clients * I.clients + 2) 0 := by
    rw [ha3, hW.arrs "Y" (by simp), hextY]
  obtain ⟨σ4, r4, hY4, hoth4, hv4, ho4⟩ := TwGraph.gwCom_run (B := B) x I.clients I.days σ3
    (by rw [ha3]; exact hXa) (by rw [hv3 "n" (by decide) (by decide)]; exact hn)
    (by rw [hv3 "m" (by decide) (by decide)]; exact hm)
    (by rw [hv3 "mn" (by decide) (by decide)]; exact hmn) hmask3 hY3 hXlen hXB (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (by rw [hv3 "w" (by decide) (by decide), hw2]; omega)
  have hw4 : σ4.vars "w" = w := by
    rw [hv4 "w" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD]), hv3 "w" (by decide) (by decide), hw2]
  have hv34 : ∀ v, v ∉ TwGraph.SGW → v ≠ "mask" → v ≠ "bb" → σ4.vars v = σ2.vars v := by
    intro v h1 h2 h3; rw [hv4 v h1, hv3 v h2 h3]
  have hZ4 : ∀ a, a ≠ "Y" → σ4.arrs a = σ2.arrs a := by
    intro a ha; rw [hoth4 a ha, ha3]
  have hyl : (TwGraph.gwList x I.clients I.days ++ [w]).length = I.clients * I.clients + 2 := by
    simp [TwGraph.gwList_length]; omega
  have hn4 : σ4.vars "n" = I.clients := by
    rw [hv34 "n" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD]) (by decide) (by decide), hn]
  have hY4' : σ4.arrs "Y" = TwGraph.gwList x I.clients I.days ++ [w] := by rw [hY4, hv3 "w" (by decide) (by decide), hw2]
  obtain ⟨σ5, r5, hz, hOlen, hv5, ha5, ho5⟩ := TwSetup.interpCom_run (B := B) prog
    (TwGraph.gwList x I.clients I.days ++ [w]) z I.clients Pn Wp OL t σ4 hY4' hn4 hyl
    (by rw [hZ4 "OP" (by decide), hW.arrs "OP" (by simp), hextOP])
    (by rw [hZ4 "XA" (by decide), hW.arrs "XA" (by simp), hextXA])
    (by rw [hZ4 "XB" (by decide), hW.arrs "XB" (by simp), hextXB])
    (by rw [hZ4 "XC" (by decide), hW.arrs "XC" (by simp), hextXC])
    (by rw [hZ4 "M" (by decide), hW.arrs "M" (by simp), hextM])
    (by rw [hZ4 "O" (by decide), hW.arrs "O" (by simp), hextO])
    (by rw [hv34 "pc" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD]) (by decide) (by decide)]
        exact hW.vars "pc" (by simp [VR, TwPrep.SPrep]))
    (by rw [hv34 "cur" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD]) (by decide) (by decide)]
        exact hW.vars "cur" (by simp [VR, TwPrep.SPrep]))
    (by rw [hv34 "ol" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD]) (by decide) (by decide)]
        exact hW.vars "ol" (by simp [VR, TwPrep.SPrep]))
    (by rw [hv34 "P" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD]) (by decide) (by decide), hP])
    (by rw [hv34 "wp" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD]) (by decide) (by decide), hwp])
    hPn hsm hyP (by rw [hyl]; exact hyPn) bPP b2 (by rw [hyl]; exact bnd) hOL hOLt hlit hRuns
  have hZ5 : ∀ a, a ∉ AG → σ5.arrs a = σ2.arrs a := by
    intro a ha
    rw [ha5 a (fun h => ha (by simp only [AG, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)),
      hZ4 a (fun h => ha (by simp [AG, h]))]
  refine ⟨σ5, (r3.seq (r4.seq r5)).mono (by unfold Kgi; omega), hz, hOlen, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [ha5 "Y" (by decide), hY4']
  · rw [ha5 "X" (by decide), hZ4 "X" (by decide), hXa]
  · intro a ha
    have h1 : a ∉ AG := fun h => ha (by simp [h])
    have h2 : a ∉ ["X"] := fun h => ha (by simp at h ⊢; tauto)
    rw [hZ5 a h1, hW.arrs a h2]
  · intro v hv
    have h1 : v ∉ TwSetup.SI := fun h => hv (by simp [VG, h])
    have h2 : v ∉ TwGraph.SGW := fun h => hv (by simp [VG, h])
    have h3 : v ≠ "mask" := fun h => hv (by simp [VG, h])
    have h4 : v ≠ "bb" := fun h => hv (by simp [VG, h])
    have h5 : v ∉ VR ++ TwPrep.SPrep := fun h => hv (by simp at h ⊢; tauto)
    rw [hv5 v h1, hv34 v h2 h3 h4, hW.vars v h5]
  · intro v hv
    have h1 : v ∉ TwSetup.SI := fun h => hv (by simp [VG, h])
    have h2 : v ∉ TwGraph.SGW := fun h => hv (by simp [VG, h])
    have h3 : v ≠ "mask" := fun h => hv (by simp [VG, h])
    have h4 : v ≠ "bb" := fun h => hv (by simp [VG, h])
    rw [hv5 v h1, hv34 v h2 h3 h4]
  · rw [hv5 "mask" (by simp [TwSetup.SI]), hv4 "mask" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD]), hmask3]
  · rw [hv5 "bb" (by simp [TwSetup.SI]), hv4 "bb" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD])]
    rw [e3]; simp [Env.setVar]
  · rw [ho5, ho4, ho3]

end Lax117284Proofs.Machine.TwMain
