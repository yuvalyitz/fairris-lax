import Lax117284Proofs.McisHard.Machine.PrintHdr
import Lax117284Proofs.McisHard.MathFinal

/-!
# Writing the image of `H` (WP7, part 3): `printCom_run`
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Print

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284Proofs.Machine.Out (emitVar emitVar_spec)
open Lax117284Proofs.Machine.Bits (bitsNat natBits natBits_encodeNat)
open Lax117284Proofs.McisHard Lax117284Proofs.McisHard.Bit
open Lax117284.Problems (encodeNat)

variable {B : ℕ}

open Classical in
/-- **The image on bits.** -/
theorem natBits_image (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) :
    natBits (Lax117284.MulticolouredIndepSet.encodeInstance (Hfin ns)) =
      bitsNat (kOf ns) ++ bitsNat (nOf ns) ++ (List.range (kOf ns * nOf ns)).flatMap
        (fun w => (List.range (kOf ns * nOf ns)).map (fun w2 => bitOf ns w w2)) := by
  rw [Proved.encodeInstance_Hfin ns hs hc]
  simp only [natBits, List.map_append, List.map_flatMap, List.map_map]
  have h1 := natBits_encodeNat (kOf ns)
  have h2 := natBits_encodeNat (nOf ns)
  simp only [natBits] at h1 h2
  rw [h1, h2]
  rfl

theorem printCom_run (Sz : ℕ) (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns)
    (hB : 60 * (SlotsN ns + 4) < B) (hE : ∀ k < 3 + 2 * SlotsN ns, ns.getD k 0 + 8 < B)
    (hV : kOf ns * nOf ns + 8 < B) (hsz : ∀ v, v + 4 < B → v.size ≤ Sz) (σ : Env)
    (hctx : Ctx[ns, σ]) :
    ∃ σ', Run B printCom σ σ' (KprintM Sz (SlotsN ns) (kOf ns * nOf ns)) ∧
      σ'.out = σ.out ++ natBits (Lax117284.MulticolouredIndepSet.encodeInstance (Hfin ns)) := by
  have hP := pars_of B ns hs hB hE
  obtain ⟨σ1, r1, hK, hM, hVv, hc1, ho1⟩ := hdrCom_spec ns hP hV σ hctx
  have hkB := kOf_le_V ns
  have hnB := nOf_le_V ns
  obtain ⟨σ2, r2, o2, f2, a2⟩ := emitVar_spec (B := B) "pK" Sz σ1
    ⟨by rw [hK]; omega, by rw [hK]; exact hsz _ (by omega)⟩
  have c2 : Ctx[ns, σ2] := ⟨by rw [a2]; exact hc1.1, by rw [f2 "N" (by decide)]; exact hc1.2.1,
    by rw [f2 "A2" (by decide)]; exact hc1.2.2⟩
  have m2 : σ2.vars "pM" = nOf ns := by rw [f2 "pM" (by decide)]; exact hM
  have v2 : σ2.vars "pV" = kOf ns * nOf ns := by rw [f2 "pV" (by decide)]; exact hVv
  obtain ⟨σ3, r3, o3, f3, a3⟩ := emitVar_spec (B := B) "pM" Sz σ2
    ⟨by rw [m2]; omega, by rw [m2]; exact hsz _ (by omega)⟩
  have c3 : Ctx[ns, σ3] := ⟨by rw [a3]; exact c2.1, by rw [f3 "N" (by decide)]; exact c2.2.1,
    by rw [f3 "A2" (by decide)]; exact c2.2.2⟩
  have v3 : σ3.vars "pV" = kOf ns * nOf ns := by rw [f3 "pV" (by decide)]; exact v2
  obtain ⟨σ4, r4, o4, -, -⟩ := matCom_run ns hs hc hB hE (kOf ns * nOf ns) hV σ3 c3 v3
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by unfold KprintM; omega), ?_⟩
  rw [o4, o3, o2, m2, hK, ho1, natBits_image ns hs hc]
  simp

end Lax117284Proofs.McisHard.Print
