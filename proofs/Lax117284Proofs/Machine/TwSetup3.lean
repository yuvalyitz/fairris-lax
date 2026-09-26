import Lax117284Proofs.Machine.TwSetup2

/-!
Loading the code, and the frame of the interpreter's loop.
-/

namespace Lax117284Proofs.Machine.TwSetup

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol
open Lax117284Proofs.Machine.TwRam (opcode fa fb fc)

variable {B : ℕ}

theorem loopCom_frame_vars : Lax117284Proofs.Machine.TwRam.loopCom.wvars ⊆
    ["pc", "cur", "ol", "run", "op", "ia", "ib", "ic", "t1", "t2", "ta"] := by
  decide +kernel

theorem loopCom_frame_arrs : Lax117284Proofs.Machine.TwRam.loopCom.warrs ⊆ ["M", "O"] := by
  decide +kernel

theorem loopCom_frame_write : Lax117284Proofs.Machine.TwRam.loopCom.NoWrite := by
  decide +kernel

theorem loadFrom_run : ∀ (rest : List Instr) (i : ℕ) (σ : Env),
    (∀ a ∈ ["OP", "XA", "XB", "XC"], i + rest.length ≤ (σ.arrs a).length) →
    i + rest.length + 3 < B →
    (∀ ins ∈ rest, opcode ins + 3 < B ∧ fa ins + 3 < B ∧ fb ins + 3 < B ∧ fc ins + 3 < B) →
    ∃ σ', Run B (loadFrom i rest) σ σ' (13 * rest.length + 1) ∧
      σ'.arrs "OP" = setFrom (σ.arrs "OP") i (rest.map opcode) ∧
      σ'.arrs "XA" = setFrom (σ.arrs "XA") i (rest.map fa) ∧
      σ'.arrs "XB" = setFrom (σ.arrs "XB") i (rest.map fb) ∧
      σ'.arrs "XC" = setFrom (σ.arrs "XC") i (rest.map fc) ∧
      (∀ a, a ∉ ["OP", "XA", "XB", "XC"] → σ'.arrs a = σ.arrs a) ∧ σ'.vars = σ.vars ∧
      σ'.out = σ.out
  | [], i, σ, _, _, _ => by
    refine ⟨σ, ?_, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩
    exact Run.skip.mono (by simp)
  | ins :: rest, i, σ, hlen, hB, hv => by
    have hl1 : ∀ a ∈ ["OP", "XA", "XB", "XC"], i + 1 + rest.length ≤ (σ.arrs a).length := by
      intro a ha; have := hlen a ha; simp only [List.length_cons] at this; omega
    have h0 := hv ins List.mem_cons_self
    obtain ⟨σ1, r1, e1⟩ := storeIns_run (B := B) i ins σ
      (by have := hlen "OP" (by simp); simp at this; omega)
      (by have := hlen "XA" (by simp); simp at this; omega)
      (by have := hlen "XB" (by simp); simp at this; omega)
      (by have := hlen "XC" (by simp); simp at this; omega)
      (by simp at hB; omega) h0.1 h0.2.1 h0.2.2.1 h0.2.2.2
    obtain ⟨σ2, r2, hOP, hXA, hXB, hXC, hoth, hvar, hout⟩ := loadFrom_run rest (i + 1) σ1
      (by
        intro a ha
        have := hl1 a ha
        rw [e1]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> simpa using this)
      (by simp at hB; omega) (fun ins' h' => hv ins' (List.mem_cons_of_mem _ h'))
    refine ⟨σ2, (r1.seq r2).mono (by simp only [List.length_cons]; omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hOP, e1]; simp [setFrom]
    · rw [hXA, e1]; simp [setFrom]
    · rw [hXB, e1]; simp [setFrom]
    · rw [hXC, e1]; simp [setFrom]
    · intro a ha
      rw [hoth a ha, e1]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
      simp [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2]
    · rw [hvar, e1]; simp
    · rw [hout, e1]; simp

end Lax117284Proofs.Machine.TwSetup
