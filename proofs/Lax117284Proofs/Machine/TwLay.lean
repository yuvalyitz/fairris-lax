import Lax117284Proofs.Machine.TwNum13
import Lax117284Proofs.Machine.ClMainOk

/-!
The layout of the main program: the scalars and arrays it mentions and the depth of its
expressions, and the proof that a layout that has them compiles it.
-/

namespace Lax117284Proofs.Machine.TwLay

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846.Ram
open Lax117284Proofs.Machine.ClMain (cS cA cD eS eA eD com_ok)
open Lax117284Proofs.Machine.TwMain

/-- The arrays of the machine. -/
def arrsT : List String :=
  ["OP", "XA", "XB", "XC", "Y", "M", "O", "BG", "SZ", "TB", "X", "bfsc"]

/-- A command fits: its arrays are the machine's and it needs at most five temporaries. -/
def Fine (c : Com) : Prop := (∀ a ∈ cA c, a ∈ arrsT) ∧ cD c ≤ 5

theorem Fine.seq {c d : Com} (h1 : Fine c) (h2 : Fine d) : Fine (.seq c d) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · simp only [cA, List.mem_append] at ha
    rcases ha with ha | ha
    · exact h1.1 a ha
    · exact h2.1 a ha
  · simp only [cD]; have := h1.2; have := h2.2; omega

theorem Fine.ite {b : Cond} {c d : Com} (hb : eD (condExpr b) ≤ 5)
    (hbA : ∀ a ∈ eA (condExpr b), a ∈ arrsT) (h1 : Fine c) (h2 : Fine d) :
    Fine (.ite b c d) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · simp only [cA, List.mem_append] at ha
    rcases ha with ha | ha | ha
    · exact hbA a ha
    · exact h1.1 a ha
    · exact h2.1 a ha
  · simp only [cD]; have := h1.2; have := h2.2; omega

theorem fine_read : Fine ClMain.readCom := by unfold Fine; decide +kernel
theorem fine_prep (cc plit : ℕ) : Fine (TwPrep.prepCom cc plit) := by
  have : Fine (TwPrep.prepCom 0 0) := by unfold Fine; decide +kernel
  exact this
theorem fine_mask : Fine TwPrep.maskCom := by unfold Fine; decide +kernel
theorem fine_gw : Fine TwGraph.gwCom := by unfold Fine; decide +kernel
theorem fine_loop : Fine TwRam.loopCom := by unfold Fine; decide +kernel
theorem fine_init (plen : ℕ) : Fine (TwSetup.initCom plen) := by
  have : Fine (TwSetup.initCom 0) := by unfold Fine; decide +kernel
  exact this
theorem fine_dpSetup : Fine TwNode.dpSetup := by unfold Fine; decide +kernel
theorem fine_dpCom : Fine TwNode.dpCom := by unfold Fine; decide +kernel
theorem fine_brute0 : Fine brute0 := by unfold Fine brute0 brute zeroCom; decide +kernel

theorem fine_loadFrom (P : List Instr) (j : ℕ) : Fine (TwSetup.loadFrom j P) := by
  induction P generalizing j with
  | nil => refine ⟨fun a ha => ?_, ?_⟩ <;> simp [TwSetup.loadFrom, cA, cD] at *
  | cons i rest ih =>
    have hs : Fine (TwSetup.storeIns j i) := by
      have : Fine (TwSetup.storeIns 0 (.halt)) := by unfold Fine; decide +kernel
      exact this
    exact hs.seq (ih (j + 1))

theorem fine_brute : Fine brute := by unfold Fine brute; decide +kernel

theorem fine_interp (prog : Program) : Fine (TwSetup.interpCom prog) :=
  (fine_loadFrom prog 0).seq ((fine_init prog.length).seq fine_loop)

theorem eD_ok : eD (condExpr (.eq (Expr.get "O" (Expr.lit 0)) (Expr.lit 1))) ≤ 5 := by
  decide +kernel
theorem eA_ok : ∀ a ∈ eA (condExpr (.eq (Expr.get "O" (Expr.lit 0)) (Expr.lit 1))), a ∈ arrsT := by
  decide +kernel
theorem eD_ok' : eD (condExpr (.lt (Expr.lit 0) (Expr.var "ok"))) ≤ 5 := by decide +kernel
theorem eA_ok' : ∀ a ∈ eA (condExpr (.lt (Expr.lit 0) (Expr.var "ok"))), a ∈ arrsT := by decide +kernel

theorem fine_guarded (prog : Program) : Fine (guarded prog) :=
  (fine_mask.seq (fine_gw.seq (fine_interp prog))).seq
    (Fine.ite eD_ok eA_ok (fine_dpSetup.seq fine_dpCom) fine_brute)

theorem fine_main (prog : Program) (cc plit : ℕ) : Fine (mainCom prog cc plit) :=
  fine_read.seq ((fine_prep cc plit).seq (Fine.ite eD_ok' eA_ok' (fine_guarded prog) fine_brute0))

/-- **The layout of the main program.** -/
def layoutT (prog : Program) (cc plit : ℕ) : Layout := ⟨cS (mainCom prog cc plit), arrsT, 5⟩

theorem layout_ok (prog : Program) (cc plit : ℕ) : Com.Ok (layoutT prog cc plit) (mainCom prog cc plit) :=
  com_ok (layoutT prog cc plit) (mainCom prog cc plit) (fun y h => h) (fine_main prog cc plit).1
    (fine_main prog cc plit).2

end Lax117284Proofs.Machine.TwLay
