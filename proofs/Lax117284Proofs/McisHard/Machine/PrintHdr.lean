import Lax117284Proofs.McisHard.Machine.PrintMat

/-!
# The Header of the Image of `H` (WP7, Part 2)

`hdrCom` computes `pK = kOf ns`, `pM = nOf ns`, `pV = pK * pM`; `preCom` writes the two numbers.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Print

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.ILoop
open Lax117284Proofs.Machine.Out (emitVar emitVar_spec)
open Lax117284Proofs.Machine.Bits (bitsNat)
open Lax117284Proofs.McisHard Lax117284Proofs.McisHard.Bit

variable {B : ℕ}

/-- `pK = kOf`, `pM = nOf`, `pV = pK * pM`. -/
def hdrCom : Com :=
  .seq (.ite (.eq (V "N") (.lit 0))
    (.seq (.assign "pK" (.lit 2)) (.assign "pM" (.lit 4)))
    (.seq (.assign "pM" (mul (V "N") (.lit 36)))
      (.assign "pK" (add (add (.get "TK" (.lit 1)) (.get "TK" (.lit 2))) (mul (V "N") (.lit 10))))))
    (.assign "pV" (mul (V "pK") (V "pM")))

theorem kOf_ge (ns : List ℕ) : 2 ≤ kOf ns := by
  unfold kOf; split_ifs with h <;> omega

theorem nOf_ge (ns : List ℕ) : 4 ≤ nOf ns := by
  unfold nOf; split_ifs with h
  · omega
  · unfold SlotsN at h ⊢; omega

theorem kOf_le_V (ns : List ℕ) : kOf ns ≤ kOf ns * nOf ns := by
  have := nOf_ge ns
  nlinarith

theorem nOf_le_V (ns : List ℕ) : nOf ns ≤ kOf ns * nOf ns := by
  have := kOf_ge ns
  nlinarith

set_option maxHeartbeats 1600000 in
theorem hdrCom_spec (ns : List ℕ) (hP : Pars B ns) (hV : kOf ns * nOf ns + 8 < B) :
    Spec B (fun σ => Ctx[ns, σ]) hdrCom
      (fun σ σ' => σ'.vars "pK" = kOf ns ∧ σ'.vars "pM" = nOf ns ∧
        σ'.vars "pV" = kOf ns * nOf ns ∧ Ctx[ns, σ'] ∧ σ'.out = σ.out) 40 := by
  have hk := kOf_le_V ns
  have hn := nOf_le_V ns
  have hE1 := hP.hE1
  have hlen := hP.hlen
  by_cases h0 : SlotsN ns = 0
  · have hkk : kOf ns = 2 := by unfold kOf; rw [if_pos h0]
    have hnn : nOf ns = 4 := by unfold nOf; rw [if_pos h0]
    run_vcg
    vcg_norm
    vcg_fin
  · have hkk : kOf ns = ns.getD 1 0 + ns.getD 2 0 + 10 * SlotsN ns := by
      unfold kOf; rw [if_neg h0]
    have hnn : nOf ns = SlotsN ns * 36 := by unfold nOf; rw [if_neg h0]
    run_vcg
    vcg_norm
    vcg_fin
    all_goals first | omega | (ring_nf at hV ⊢; omega)


/-- The whole image: the two numbers of the header, then the matrix. -/
def printCom : Com :=
  .seq hdrCom (.seq (emitVar "pK") (.seq (emitVar "pM") matCom))

/-- The cost of writing the image, with `V` the number of vertices of `H`. -/
def KprintM (Sz N V : ℕ) : ℕ :=
  40 + (48 * Sz + 50) + (48 * Sz + 50) + (((Kbit N + 2 + 10 + 4) * V + 6 + 10 + 4) * V + 6)

end Lax117284Proofs.McisHard.Print
