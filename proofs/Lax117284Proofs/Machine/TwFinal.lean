import Lax117284Proofs.Machine.TwLay
import Lax117284.Theorem4

/-!
The second bullet of Theorem 4, from the cited theorem on nice tree decompositions: the main
program decides the problem within `c * g (parameter) * (|x| + 1) ^ c` instructions.
-/

namespace Lax117284Proofs.Machine.TwFinal

open Lax808846.Ram Lax808846.RamComputes Lax808846Proofs.Transfer Lax808846Proofs.Compile
open Lax117284.Scheduling Lax117284.InstanceEncoding Lax117284.ConflictGraph
open Lax117284.ParameterizedComplexity
open Lax117284Proofs.Machine.TwNum
open Lax117284Proofs.Machine.ClMain (Mx le_Mx Mx_mem_or_zero)

theorem mono_ineq {c c' : ℕ} (hc : c ≤ c') (b w : ℕ) (hb : 1 ≤ b) :
    c * 2 ^ (c * w ^ 3) * b ^ c ≤ c' * 2 ^ (c' * w ^ 3) * b ^ c' :=
  Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_right _ hc))) (Nat.pow_le_pow_right hb hc)

/-- The cited theorem holds at every larger constant. -/
theorem AxStmt.mono {prog : Program} {c c' : ℕ} (h : AxStmt prog c) (hc : c ≤ c') :
    AxStmt prog c' := by
  intro W w g I hg hyp
  obtain ⟨out, t, ht, hr, hcase⟩ := h W w g I hg (fun v hv =>
    le_trans (mono_ineq hc _ w (by omega)) (hyp v hv))
  exact ⟨out, t, ht.trans (mono_ineq hc _ w (by omega)), hr, hcase⟩

theorem fits_Mx {c w : ℕ} {x : List ℕ} (hx : Dm x) (hf : Fits c w x) :
    c * (x.length + Mx x + 1) ^ c ≤ 2 ^ w := by
  have hl := hx.three
  rcases Mx_mem_or_zero x with hm | hm
  · exact hf _ hm
  · have h0 := hf (x.getD 0 0) (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
    rw [hm]
    have : c * (x.length + 0 + 1) ^ c ≤ c * (x.length + x.getD 0 0 + 1) ^ c :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega

theorem fits_num {a b CB EB S c w : ℕ} (ha : 1 ≤ a) (hb : b ≤ CB * a ^ EB) (hEB : EB ≤ c)
    (hc : 7 + S + 12 * CB ≤ c) (h2 : c * a ^ c ≤ 2 ^ w) :
    b ≤ 2 ^ w ∧ 5 + 2 + S + 12 * b ≤ 2 ^ w := by
  have h1 : a ^ EB ≤ a ^ c := Nat.pow_le_pow_right ha hEB
  have h3 : b ≤ CB * a ^ c := hb.trans (Nat.mul_le_mul_left _ h1)
  have h4 : 1 ≤ a ^ c := Nat.one_le_pow _ _ ha
  refine ⟨?_, ?_⟩
  · have : CB * a ^ c ≤ c * a ^ c := Nat.mul_le_mul_right _ (by omega)
    omega
  · have h5 : (7 + S + 12 * CB) * a ^ c ≤ c * a ^ c := Nat.mul_le_mul_right _ hc
    have h6 : 7 + S ≤ (7 + S) * a ^ c := Nat.le_mul_of_pos_right _ h4
    nlinarith

open Classical in
/-- **The problem is fixed-parameter tractable in the number of days plus the treewidth**, given
the cited theorem. -/
theorem fpt_real (hex : ∃ (prog : Program) (c : ℕ), AxStmt prog c) :
    FPT Lax117284.Theorem4.byDaysAndTreewidth := by
  obtain ⟨prog, c0, hax0⟩ := hex
  have hca : 1 ≤ c0 + 1 := by omega
  have hcc : c0 + 1 + 1 ≤ c0 + 1 + 1 := le_rfl
  have hax : AxStmt prog (c0 + 1) := AxStmt.mono hax0 (by omega)
  obtain ⟨Cp, Ep, hT⟩ := time_le (prog := prog) (ca := c0 + 1) (cc := c0 + 1 + 1) hca hcc
  obtain ⟨CB, EB, hB⟩ := plon_Bx (prog := prog) (ca := c0 + 1) (cc := c0 + 1 + 1)
    (plit := PLit prog + (c0 + 1) + 1) hca hcc
  set lay := TwLay.layoutT prog (c0 + 1 + 1) (PLit prog + (c0 + 1) + 1) with hlay
  set S := lay.scalars.length with hS
  set c := Ep + EB + (7 + S + 12 * CB) + 1 with hcdef
  refine ⟨compileProgram lay (TwMain.mainCom prog (c0 + 1 + 1) (PLit prog + (c0 + 1) + 1)), c,
    Gp (c0 + 1 + 1) Cp, fun w => ?_⟩
  have hs : Solves lay (TwMain.mainCom prog (c0 + 1 + 1) (PLit prog + (c0 + 1) + 1))
      {x | x ∈ Lax117284.Theorem4.byDaysAndTreewidth.Domain ∧ Fits c w x} fAnsT
      (Bx prog (c0 + 1) (c0 + 1 + 1) (PLit prog + (c0 + 1) + 1))
      (Kx prog (c0 + 1) (c0 + 1 + 1)) := by
    refine ⟨TwLay.layout_ok _ _ _, fun x hx v hv => ?_, fun x hx => ?_⟩
    · exact (B_unc (prog := prog) (ca := c0 + 1) (cc := c0 + 1 + 1)
        (plit := PLit prog + (c0 + 1) + 1) hx.1).2.2.1 v hv
    · exact ⟨extx prog (c0 + 1) (c0 + 1 + 1) (PLit prog + (c0 + 1) + 1) x,
        core hax hca hcc (by omega) (by omega) hx.1⟩
  refine computesInTime_of_solves hs ?_ ?_
  · rintro x ⟨hx, hf⟩
    have hfM := fits_Mx hx hf
    have hb := hB x hx
    have ha : 1 ≤ Aw x := Aw_pos x
    have := fits_num (S := S) (w := w) ha hb (by omega) (by omega) hfM
    refine fitsWords_of_max_le (Bx_pos x) (max_le this.1 ?_)
    have e : lay.span (Bx prog (c0 + 1) (c0 + 1 + 1) (PLit prog + (c0 + 1) + 1) x) =
        5 + 2 + S + 12 * Bx prog (c0 + 1) (c0 + 1 + 1) (PLit prog + (c0 + 1) + 1) x := rfl
    rw [e]; exact this.2
  · rintro x ⟨hx, hf⟩
    have h1 := hT x hx
    have h2 : (x.length + 1) ^ Ep ≤ (x.length + 1) ^ c :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : 10 * Kx prog (c0 + 1) (c0 + 1 + 1) x + 1 ≤
        Gp (c0 + 1 + 1) Cp ((Ix x).days + treewidth (Ix x)) * (x.length + 1) ^ c :=
      h1.trans (Nat.mul_le_mul_left _ h2)
    show 10 * Kx prog (c0 + 1) (c0 + 1 + 1) x + 1 ≤ c * Gp (c0 + 1 + 1) Cp
      ((decode x.dropLast).days + treewidth (decode x.dropLast)) * (x.length + 1) ^ c
    have : Gp (c0 + 1 + 1) Cp ((Ix x).days + treewidth (Ix x)) ≤
        c * Gp (c0 + 1 + 1) Cp ((Ix x).days + treewidth (Ix x)) :=
      Nat.le_mul_of_pos_left _ (by omega)
    calc 10 * Kx prog (c0 + 1) (c0 + 1 + 1) x + 1
        ≤ Gp (c0 + 1 + 1) Cp ((Ix x).days + treewidth (Ix x)) * (x.length + 1) ^ c := h3
      _ ≤ c * Gp (c0 + 1 + 1) Cp ((Ix x).days + treewidth (Ix x)) * (x.length + 1) ^ c :=
          Nat.mul_le_mul_right _ this

end Lax117284Proofs.Machine.TwFinal
