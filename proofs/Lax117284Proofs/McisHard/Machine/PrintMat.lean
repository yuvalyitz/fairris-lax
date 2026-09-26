import Lax117284Proofs.McisHard.Machine.PredFinal
import Lax117284Proofs.Machine.ILoop

/-!
# Writing the adjacency matrix of `H` (WP7, part 1)

Two nested counters `w`, `w2` below the scalar `pV` (`= kOf * nOf`); every iteration runs `bitCom`, which
reads `w`, `w2`, and writes the bit it leaves in `bt` to the output.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Print

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.ILoop
open Lax117284Proofs.McisHard Lax117284Proofs.McisHard.Bit

open Classical in
/-- The bit of the matrix, as a number. -/
noncomputable def bitOf (ns : List ℕ) (w w2 : ℕ) : ℕ := if decide (adjF ns w w2) then 1 else 0

/-- One bit: compute it, write it. -/
def rowBody : Com := .seq bitCom (.write (.var "bt"))

/-- One row: the bits at `(w, w2)` for `w2 < pV`. -/
def rowCom : Com := fLoop "w2" "pV" rowBody

/-- The matrix: all the rows. -/
def matCom : Com := fLoop "w" "pV" rowCom

variable {B : ℕ}

theorem bitCom_warrs : bitCom.warrs = [] := by decide

theorem AB_w : "w" ∉ AB := by decide
theorem AB_w2 : "w2" ∉ AB := by decide
theorem AB_pV : "pV" ∉ AB := by decide
theorem AB_N : "N" ∉ AB := by decide
theorem AB_A2 : "A2" ∉ AB := by decide

theorem rowCom_run (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) (hB : 60 * (SlotsN ns + 4) < B)
    (hE : ∀ k < 3 + 2 * SlotsN ns, ns.getD k 0 + 8 < B) (Vv : ℕ) (hV : Vv + 8 < B) (σ : Env)
    (hctx : Ctx[ns, σ]) (hpv : σ.vars "pV" = Vv) (w0 : ℕ) (hw : σ.vars "w" = w0) (hw0 : w0 < B) :
    ∃ σ', Run B rowCom σ σ' ((Kbit (SlotsN ns) + 2 + 10 + 4) * Vv + 6) ∧
      σ'.out = σ.out ++ (List.range Vv).map (fun w2 => bitOf ns w0 w2) ∧ Ctx[ns, σ'] ∧
      σ'.vars "pV" = Vv ∧ σ'.vars "w" = w0 := by
  obtain ⟨σ', r, hQ⟩ := iLoop_spec (B := B) "w2" "pV" rowBody
    (fun j σ1 => Ctx[ns, σ1] ∧ σ1.vars "pV" = Vv ∧ σ1.vars "w" = w0 ∧
      σ1.out = σ.out ++ (List.range j).map (fun w2 => bitOf ns w0 w2))
    (Kbit (SlotsN ns) + 2) Vv σ hpv
    (fun j σ1 h => h.2.1) (by decide) (by omega)
    ⟨⟨by simpa [Env.setVar] using hctx.1, by simpa [Env.setVar] using hctx.2.1,
        by simpa [Env.setVar] using hctx.2.2⟩,
      by simp [Env.setVar, hpv], by simp [Env.setVar, hw], by simp [Env.setVar]⟩
    (fun j σ1 v h => ⟨⟨by simpa [Env.setVar] using h.1.1, by simpa [Env.setVar] using h.1.2.1,
        by simpa [Env.setVar] using h.1.2.2⟩, by simpa [Env.setVar] using h.2.1,
      by simpa [Env.setVar] using h.2.2.1, by simpa [Env.setVar] using h.2.2.2⟩)
    (by
      intro j σ1 hq hj hjV
      obtain ⟨hc1, hp1, hw1, ho1⟩ := hq
      obtain ⟨σ2, r2, hbt, ha2, ho2, hi2, hf2⟩ := bitCom_run B ns hs hc hB hE σ1 hc1.1 hc1.2.1
        hc1.2.2 w0 j hw1 (by simpa using hj) (by omega) (by omega)
      have hbtB : σ2.vars "bt" < B := by rw [hbt]; split <;> omega
      have r3 : Run B (.write (.var "bt")) σ2 { σ2 with out := σ2.out ++ [σ2.vars "bt"] } 2 :=
        (Run.write (evalB_var hbtB)).mono (by simp [Expr.size])
      refine ⟨_, (r2.seq r3).mono (by omega), ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
      · simpa [ha2] using hc1.1
      · simpa [hf2 "N" AB_N] using hc1.2.1
      · simpa [hf2 "A2" AB_A2] using hc1.2.2
      · simpa [hf2 "pV" AB_pV] using hp1
      · simpa [hf2 "w" AB_w] using hw1
      · simp only [ho2, ho1, List.range_succ, List.map_append, List.append_assoc, hbt]
        simp [bitOf]
      · simpa [hf2 "w2" AB_w2] using hj)
  obtain ⟨hc2, hp2, hw2, ho2⟩ := hQ
  refine ⟨σ', r, ?_, hc2, hp2, hw2⟩
  simpa using ho2

theorem matCom_run (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) (hB : 60 * (SlotsN ns + 4) < B)
    (hE : ∀ k < 3 + 2 * SlotsN ns, ns.getD k 0 + 8 < B) (Vv : ℕ) (hV : Vv + 8 < B) (σ : Env)
    (hctx : Ctx[ns, σ]) (hpv : σ.vars "pV" = Vv) :
    ∃ σ', Run B matCom σ σ' (((Kbit (SlotsN ns) + 2 + 10 + 4) * Vv + 6 + 10 + 4) * Vv + 6) ∧
      σ'.out = σ.out ++ (List.range Vv).flatMap (fun w => (List.range Vv).map
        (fun w2 => bitOf ns w w2)) ∧ Ctx[ns, σ'] ∧ σ'.vars "pV" = Vv := by
  obtain ⟨σ', r, hQ⟩ := iLoop_spec (B := B) "w" "pV" rowCom
    (fun j σ1 => Ctx[ns, σ1] ∧ σ1.vars "pV" = Vv ∧
      σ1.out = σ.out ++ (List.range j).flatMap (fun w => (List.range Vv).map
        (fun w2 => bitOf ns w w2)))
    ((Kbit (SlotsN ns) + 2 + 10 + 4) * Vv + 6) Vv σ hpv
    (fun j σ1 h => h.2.1) (by decide) (by omega)
    ⟨⟨by simpa [Env.setVar] using hctx.1, by simpa [Env.setVar] using hctx.2.1,
        by simpa [Env.setVar] using hctx.2.2⟩,
      by simp [Env.setVar, hpv], by simp [Env.setVar]⟩
    (fun j σ1 v h => ⟨⟨by simpa [Env.setVar] using h.1.1, by simpa [Env.setVar] using h.1.2.1,
        by simpa [Env.setVar] using h.1.2.2⟩, by simpa [Env.setVar] using h.2.1,
      by simpa [Env.setVar] using h.2.2⟩)
    (by
      intro j σ1 hq hj hjV
      obtain ⟨hc1, hp1, ho1⟩ := hq
      obtain ⟨σ2, r2, ho2, hc2, hp2, hw2⟩ := rowCom_run ns hs hc hB hE Vv hV σ1 hc1 hp1 j hj
        (by omega)
      refine ⟨σ2, r2, ⟨hc2, hp2, ?_⟩, hw2.trans hj.symm ▸ hj⟩
      rw [ho2, ho1, List.range_succ, List.flatMap_append]
      simp)
  obtain ⟨hc2, hp2, ho2⟩ := hQ
  exact ⟨σ', r, ho2, hc2, hp2⟩

end Lax117284Proofs.McisHard.Print
