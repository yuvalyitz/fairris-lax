import Lax117284Proofs.Machine.TwMain3

/-!
The main program, phase by phase: the dynamic program on what the decomposition step returned.
-/

namespace Lax117284Proofs.Machine.TwMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol
open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding
open Lax117284Proofs.Machine.TwNode (Params NC)

variable {B : ℕ}

lemma getD_of_take {a z : List ℕ} {n i : ℕ} (h : z = a.take n) (hi : i < z.length) :
    a.getD i 0 = z.getD i 0 := by
  subst h
  have h1 : i < a.length := by
    have := hi; simp only [List.length_take] at this; omega
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ hi, List.getElem_take]

open Classical in
/-- **The dynamic program answers**, on the environment the decomposition step leaves. -/
theorem phaseDP (P : Params) (ext : String → ℕ) (z : List ℕ) (σ5 : Env)
    (hzD : z = 1 :: P.D) (hz : z = (σ5.arrs "O").take (σ5.vars "ol"))
    (hzB : ∀ v ∈ z, v < B)
    (hW : W ext ("X" :: AG) (VR ++ TwPrep.SPrep ++ VG) σ5)
    (hXa : σ5.arrs "X" = P.y ++ [P.kk]) (hn : σ5.vars "n" = P.n) (hm : σ5.vars "m" = P.m)
    (hk : σ5.vars "k" = P.kk) (hw : σ5.vars "w" = P.w) (hmn : σ5.vars "mn" = P.m * P.n)
    (hmask : σ5.vars "mask" = 2 ^ P.m - 1) (hbb : σ5.vars "bb" = 2 ^ P.m)
    (hXB : ∀ v ∈ σ5.arrs "X", v < B)
    (hextSZ : P.N ≤ ext "SZ") (hextBG : P.N * P.wid ≤ ext "BG")
    (hextTB : P.N * P.tabs ≤ ext "TB") (hlenO : 3 * P.N + 5 ≤ (σ5.arrs "O").length)
    (b1 : P.N * P.tabs + P.tabs + 32 < B) (b2 : P.N * P.wid + P.wid + 32 < B)
    (b3 : 3 * P.N + 32 < B) (b4 : P.tabs * P.bs + 32 < B)
    (b5 : P.wid * (P.wid * P.m + 1) + P.wid * P.m + P.m + 32 < B)
    (b6 : (σ5.arrs "X").length + 32 < B) (b7 : (σ5.arrs "O").length + 32 < B)
    (b8 : P.n + P.m + P.kk + 32 < B) (b9 : P.m * (P.wid + 1) + P.wid + 32 < B)
    (b10 : 2 ^ P.m + 32 < B) :
    ∃ σ7, Run B dpBranch σ5 σ7 (60 + TwNode.dpCost P) ∧
      σ7.out = σ5.out ++ [if P.I.HasKFairSchedule P.kk then 1 else 0] := by
  have hDl : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have hwid : P.wid = P.w + 1 := rfl
  have hO : ∀ j < P.D.length, (σ5.arrs "O").getD (j + 1) 0 = P.D.getD j 0 := by
    intro j hj
    have hzl : j + 1 < z.length := by rw [hzD]; simp; omega
    rw [getD_of_take hz hzl, hzD]; simp
  have hOB : ∀ j < P.D.length, (σ5.arrs "O").getD (j + 1) 0 < B := by
    intro j hj
    rw [hO j hj]
    have hmem : P.D.getD j 0 ∈ z := by
      rw [hzD]
      have : P.D.getD j 0 ∈ P.D := by
        rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
      exact List.mem_cons_of_mem _ this
    exact hzB _ hmem
  have hSZ : (σ5.arrs "SZ").length = ext "SZ" := by rw [hW.arrs "SZ" (by simp [AG])]; simp
  have hBG : (σ5.arrs "BG").length = ext "BG" := by rw [hW.arrs "BG" (by simp [AG])]; simp
  have hTB : (σ5.arrs "TB").length = ext "TB" := by rw [hW.arrs "TB" (by simp [AG])]; simp
  have hN : (σ5.arrs "O").getD 1 0 = P.N := by
    have := hO 0 (by omega)
    rw [show (0 : ℕ) + 1 = 1 from rfl] at this
    rw [this]; rfl
  have htab : 2 ^ (P.m * (P.w + 1)) = P.tabs := TwNode.tabs_eq P
  obtain ⟨σ6, r6, e6⟩ := TwNode.dpSetup_run (B := B) σ5 P.kk P.w P.m hk hw hm (by omega) (by omega)
    (by have : P.m * (P.w + 1) ≤ P.m * (P.wid + 1) := Nat.mul_le_mul_left _ (by unfold Params.wid; omega)
        omega)
    (by rw [htab]; omega) (by omega) (by rw [hN]; omega)
  rw [htab] at e6
  have hNC : NC P B σ6 := by
    rw [e6]
    exact TwNode.nc_of_setup P σ5 hn hm hmask hbb hmn hXa hXB hO hOB hlenO (by omega) (by omega)
      (by omega) b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  obtain ⟨σ7, r7, ho7⟩ := TwNode.dpCom_run hNC
  refine ⟨σ7, (r6.seq r7).mono (by omega), ?_⟩
  rw [ho7, e6]; simp [TwNode.setupState, Env.setVar]

end Lax117284Proofs.Machine.TwMain
