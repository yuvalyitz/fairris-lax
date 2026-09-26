import Lax117284Proofs.Machine.MisAccept

/-!
The accepting phase of the reduction of Lemma 14, run: on an array the check accepts it writes the
image, and on any other it writes the rejected word.
-/

namespace Lax117284Proofs.Machine.MisRun

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.MisBlk Lax117284Proofs.Machine.MisSem
open Lax117284Proofs.Machine.MisPrint Lax117284Proofs.Machine.MisChk Lax117284Proofs.Machine.MisAccept
open Lax117284Proofs.Machine.SatOps (asg_tkl)
open Lax117284Proofs.Machine.FreeAccept (rejectPrint rejectPrint_run)
open Lax117284Proofs.Machine.MisJob (Mag)
open Lax117284Proofs.Machine.MisFormat (VM)

variable {B : ℕ}

set_option maxHeartbeats 12800000 in
/-- **The numbers of the image.** -/
theorem postM_run (arr : List ℕ) (σ : Env) (hA : σ.arrs "TK" = arr)
    (hnn : σ.vars "nn" = nN arr) (hlc : σ.vars "lc" = lN arr) (hV : σ.vars "V" = VM arr)
    (hVV : σ.vars "VV" = VM arr * VM arr) (hEE : σ.vars "EE" = edgeN arr)
    (hrr : σ.vars "rr" = rowSum arr 0) (hM : Mag arr + 4 < B) (hn0 : 0 < nN arr)
    (hBP : daysN arr * clN arr + clN arr + daysN arr + 100 < B) :
    ∃ σ', Run B postM σ σ' 400 ∧ PC arr σ' ∧ σ'.out = σ.out := by
  have hdg1 : 1 ≤ degN arr := by unfold degN; omega
  have hCpos : 0 < clN arr := by unfold clN; omega
  have hcle : clN arr = spanN arr + 1 := by unfold clN spanN; omega
  have hDle : daysN arr ≤ daysN arr * clN arr := Nat.le_mul_of_pos_right _ hCpos
  have hEd : edgeN arr ≤ daysN arr := by unfold daysN; omega
  have hnn_le : nN arr ≤ degN arr * nN arr := Nat.le_mul_of_pos_left _ hdg1
  have hdn_le : degN arr ≤ degN arr * nN arr := Nat.le_mul_of_pos_right _ hn0
  have hrrle : rowSum arr 0 ≤ degN arr := by unfold degN; omega
  have hM' := hM
  unfold Mag spanN at hM'
  have hrrB : σ.vars "rr" < B := by rw [hrr]; omega
  have h1B : small B σ (.lit 1) := by simp [small]; omega
  have hrB : small B σ (V "rr") := by simp [small]; exact hrrB
  have s1 : Run B dgM σ (σ.setVar "dg" (degN arr)) 12 := by
    by_cases hr : rowSum arr 0 < 1
    · have hT := condLt_true (V "rr") (.lit 1) σ hrB h1B (by simp [den, hrr]; omega)
      have hd : degN arr = 1 := by unfold degN; omega
      have a := asgE (B := B) "dg" (.lit 1) σ h1B
      have e : den σ (.lit 1) = degN arr := by simp [den, hd]
      rw [e] at a
      exact (Run.ite_true hT a).mono (by simp [Cond.size, Expr.size])
    · have hF := condLt_false (V "rr") (.lit 1) σ hrB h1B (by simp [den, hrr]; omega)
      have hd : degN arr = rowSum arr 0 := by unfold degN; omega
      have a := asgE (B := B) "dg" (V "rr") σ hrB
      have e : den σ (V "rr") = degN arr := by simp [den, hrr, hd]
      rw [e] at a
      exact (Run.ite_false hF a).mono (by simp [Cond.size, Expr.size])
  set σ1 := σ.setVar "dg" (degN arr) with hσ1
  have b6 : (lN arr * (nN arr + 1) + edgeN arr) *
      (3 + lN arr + VM arr + VM arr * degN arr) < B := by
    have := hBP; unfold daysN clN at this; omega
  have b5 : lN arr * (nN arr + 1) + edgeN arr < B := by
    have := hBP; unfold daysN at this; omega
  obtain ⟨σ2, r2, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, A2, O2, F2⟩ :=
    postTail_run (B := B) σ1 (lN arr) (nN arr) (VM arr) (edgeN arr) (degN arr)
      (by simp [hσ1, Env.setVar, hnn]) (by simp [hσ1, Env.setVar, hlc])
      (by simp [hσ1, Env.setVar, hV]) (by simp [hσ1, Env.setVar, hEE]) (by simp [hσ1, Env.setVar])
      (by omega) (by omega) (by omega) (by omega) (by omega) b5 b6
  have fr : ∀ y, y ∉ APT → y ≠ "dg" → σ2.vars y = σ.vars y := fun y hy hyd => by
    rw [F2 y hy]
    simp [hσ1, Env.setVar, hyd]
  have dg2 : σ2.vars "dg" = degN arr := by
    rw [F2 "dg" (by decide)]; simp [hσ1, Env.setVar]
  refine ⟨σ2, (s1.seq r2).mono (by omega), ⟨?_, ?_, ?_, ?_, dg2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, ?_⟩
  · rw [A2]; simp [hσ1, Env.setVar, hA]
  · rw [fr "nn" (by decide) (by decide)]; exact hnn
  · rw [fr "lc" (by decide) (by decide)]; exact hlc
  · rw [fr "V" (by decide) (by decide)]; exact hV
  · rw [w1]; rfl
  · rw [w3]
  · rw [w4]
  · rw [w5]
  · rw [w6]
  · rw [w7]
  · rw [fr "VV" (by decide) (by decide)]; exact hVV
  · rw [w2]; rfl
  · rw [w8]; rfl
  · rw [w9]
  · rw [w10]; rfl
  · rw [O2]; simp [hσ1, Env.setVar]

/-- The cost of the accepting phase. -/
def Kreal (Sz Vn VV DC CC : ℕ) : ℕ :=
  500 + Kchk Vn VV + Kprint Sz Vn VV DC CC + 3 * (48 * Sz + 50)

open Classical in
set_option maxHeartbeats 12800000 in
/-- **The accepting phase.** -/
theorem acceptM_run (Sz : ℕ) (arr : List ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hA : σ.arrs "TK" = arr)
    (hlen : 2 + VM arr * VM arr ≤ arr.length)
    (hE : ∀ k < VM arr * VM arr, arr.getD (2 + k) 0 + 8 < B)
    (h0 : lN arr + 8 < B) (h1 : nN arr + 8 < B)
    (hB : VM arr * VM arr + 2 * VM arr + nN arr + 40 < B)
    (hbig : 2 * (VM arr * VM arr) + 2 * VM arr + 2 * lN arr + 60 < B)
    (hcM : CondM arr → Mag arr + 4 < B)
    (hcBP : CondM arr → daysN arr * clN arr + clN arr + daysN arr + 100 < B) :
    ∃ σ', Run B acceptM σ σ'
        (Kreal Sz (VM arr) (VM arr * VM arr) (if CondM arr then daysN arr * clN arr else 0)
          (if CondM arr then clN arr else 0)) ∧
      σ'.out = σ.out ++ (if CondM arr then numBits (outM arr) else numBits [1, 0, 1]) := by
  have hVMe : VM arr = lN arr * nN arr := rfl
  have hVle : VM arr ≤ VM arr * VM arr ∨ VM arr = 0 := by
    rcases Nat.eq_zero_or_pos (VM arr) with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.le_mul_of_pos_left _ h)
  have hl2 : 2 ≤ arr.length := by omega
  -- the counts
  have s1 := asg_tkl (B := B) "nn" 1 σ arr hA (by omega) (by omega) (by unfold nN at h1; omega)
  set σ1 := σ.setVar "nn" (arr.getD 1 0) with hσ1
  have A1 : σ1.arrs "TK" = arr := by simp [hσ1, Env.setVar, hA]
  have s2 := asg_tkl (B := B) "lc" 0 σ1 arr A1 (by omega) (by omega) (by unfold lN at h0; omega)
  set σ2 := σ1.setVar "lc" (arr.getD 0 0) with hσ2
  have nn2 : σ2.vars "nn" = nN arr := by simp [hσ2, hσ1, Env.setVar]; rfl
  have lc2 : σ2.vars "lc" = lN arr := by simp [hσ2, Env.setVar]; rfl
  have s3 := asgE (B := B) "V" (.bin .mul (V "lc") (V "nn")) σ2 (by
    simp only [small_bin, small_var, den_bin, den_var, Bop.apply_mul, nn2, lc2]; omega)
  set σ3 := σ2.setVar "V" (den σ2 (.bin .mul (V "lc") (V "nn"))) with hσ3
  have V3 : σ3.vars "V" = VM arr := by
    simp only [hσ3, den_bin, den_var, Bop.apply_mul, nn2, lc2, Env.setVar, if_true]; rfl
  have nn3 : σ3.vars "nn" = nN arr := by simp [hσ3, Env.setVar, nn2]
  have lc3 : σ3.vars "lc" = lN arr := by simp [hσ3, Env.setVar, lc2]
  have s4 := asgE (B := B) "VV" (.bin .mul (V "V") (V "V")) σ3 (by
    simp only [small_bin, small_var, den_bin, den_var, Bop.apply_mul, V3]; omega)
  set σ4 := σ3.setVar "VV" (den σ3 (.bin .mul (V "V") (V "V"))) with hσ4
  have VV4 : σ4.vars "VV" = VM arr * VM arr := by
    simp [hσ4, den, Env.setVar, V3]
  have V4 : σ4.vars "V" = VM arr := by simp [hσ4, Env.setVar, V3]
  have nn4 : σ4.vars "nn" = nN arr := by simp [hσ4, Env.setVar, nn3]
  have lc4 : σ4.vars "lc" = lN arr := by simp [hσ4, Env.setVar, lc3]
  have A4 : σ4.arrs "TK" = arr := by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, hA]
  have O4 : σ4.out = σ.out := by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar]
  -- the check
  obtain ⟨σ5, r5, ok5, EE5, rr5, k5⟩ := checkCom_run (B := B) arr σ4 hE hlen hB
    ⟨A4, V4, VV4, nn4⟩
  have hokB : σ5.vars "ok" < B := by rw [ok5]; split <;> omega
  have hokT : small B σ5 (V "ok") := by simp [small]; exact hokB
  have h1T : small B σ5 (.lit 1) := by simp [small]; omega
  have prep : Run B prepM σ σ4 16 := by
    refine (s1.seq (s2.seq (s3.seq s4))).mono ?_
    simp [Expr.size]
  by_cases hc : CondM arr
  · have hcT : (Cond.eq (V "ok") (.lit 1)).evalB B σ5 = some true :=
      condEq_true _ _ σ5 hokT h1T (by simp [den, ok5, hc])
    have hMc := hcM hc
    have hBPc := hcBP hc
    have hn0 : 0 < nN arr := by have := hc.1; omega
    have hCpos : 0 < clN arr := by unfold clN; omega
    have hDle : daysN arr ≤ daysN arr * clN arr := Nat.le_mul_of_pos_right _ hCpos
    have hEd : edgeN arr ≤ daysN arr := by unfold daysN; omega
    obtain ⟨σ6, r6, pc6, o6⟩ := postM_run (B := B) arr σ5 (by rw [k5.1]; exact A4)
      (by rw [k5.2.2 "nn" (by decide)]; exact nn4) (by rw [k5.2.2 "lc" (by decide)]; exact lc4)
      (by rw [k5.2.2 "V" (by decide)]; exact V4) (by rw [k5.2.2 "VV" (by decide)]; exact VV4)
      EE5 rr5 hMc hn0 hBPc
    obtain ⟨σ7, r7, o7⟩ := printM_run (B := B) Sz arr σ6 pc6 hs hE hlen hbig hMc hn0 hBPc
      (by omega)
    refine ⟨σ7, (prep.seq (r5.seq (Run.ite_true hcT (r6.seq r7)))).mono ?_, ?_⟩
    · unfold Kreal
      simp only [if_pos hc, Cond.size, Expr.size]
      omega
    · rw [o7, o6, k5.2.1, O4, if_pos hc]
  · have hcF : (Cond.eq (V "ok") (.lit 1)).evalB B σ5 = some false :=
      condEq_false _ _ σ5 hokT h1T (by simp [den, ok5, hc])
    obtain ⟨σ6, r6, o6, -, -⟩ := rejectPrint_run (B := B) Sz σ5 hs (by omega)
    refine ⟨σ6, (prep.seq (r5.seq (Run.ite_false hcF r6))).mono ?_, ?_⟩
    · unfold Kreal
      simp only [if_neg hc, Cond.size, Expr.size]
      unfold Kprint
      omega
    · rw [o6, k5.2.1, O4, if_neg hc]

end Lax117284Proofs.Machine.MisRun
