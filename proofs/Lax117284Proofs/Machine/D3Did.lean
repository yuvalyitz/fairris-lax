import Lax117284Proofs.Machine.X3Loop
import Lax117284Proofs.Machine.D3Sem

/-!
The check that the due dates of the numbers are day-independent: every cell's due date equals the
due date of the same client on the first day. Unlike the day-independence check of Theorem 3(ii),
the processing time is left unchecked.
-/

namespace Lax117284Proofs.Machine.D3Did

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.FoldLoop
open Lax117284Proofs.Machine.MisBlk (asgE condEq_true condEq_false)
open Lax117284Proofs.Machine.X3Loop (rd)
open Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.D3Sem (DID)

variable {B : ℕ}

/-- The cell `t` has the due date of its client on the first day. -/
def DIDp (arr : List ℕ) (n t : ℕ) : Prop :=
  arr.getD (2 + 2 * t + 1) 0 = arr.getD (2 + 2 * (t % n) + 1) 0

instance (arr : List ℕ) (n t : ℕ) : Decidable (DIDp arr n t) := by unfold DIDp; infer_instance

/-- The body of the check: the cell `i`. -/
def didBody : Com :=
  .seq (.assign "ci" (.bin .div (V "i") (V "n")))
  (.seq (.assign "cr" (mul (V "ci") (V "n")))
  (.seq (.assign "tt" (sub (V "i") (V "cr")))
  (.seq (.assign "da" (rd "i" 1))
  (.seq (.assign "db" (rd "tt" 1))
    (.ite (.eq (V "da") (V "db")) .skip (.assign "ok" (.lit 0)))))))

/-- The scalars the check assigns. -/
def SDID : List String := ["ci", "cr", "tt", "da", "db", "ok"]

lemma mod_eq_sub'' (i n : ℕ) : i - i / n * n = i % n := by
  have := Nat.div_add_mod i n
  rw [Nat.mul_comm] at this
  omega

set_option maxHeartbeats 6400000 in
/-- **One cell of the check.** -/
theorem didBody_run (arr : List ℕ) (n N i : ℕ) (σ : Env)
    (hA : σ.arrs "TK" = arr) (hi : σ.vars "i" = i) (hiN : i < N) (hn : σ.vars "n" = n)
    (hn0 : 0 < n) (hnN : n ≤ N) (hlen : 3 + 2 * N ≤ arr.length)
    (hE : ∀ k < 3 + 2 * N, arr.getD k 0 + 8 < B) (hNB : 2 * N + 8 < B) (hok : σ.vars "ok" ≤ 1) :
    ∃ σ', Run B didBody σ σ' 80 ∧
      σ'.vars "ok" = (if σ.vars "ok" = 1 ∧ DIDp arr n i then 1 else 0) ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ SDID → σ'.vars y = σ.vars y := by
  have hmod : i % n < n := Nat.mod_lt _ hn0
  have hdiv : i / n * n ≤ i := Nat.div_mul_le_self _ _
  have hdle : i / n ≤ i := Nat.div_le_self _ _
  have hmsub := mod_eq_sub'' i n
  have s1 := asgE (B := B) "ci" (.bin .div (V "i") (V "n")) σ (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_div, hi, hn]; omega)
  set σ1 := σ.setVar "ci" (MisBlk.den σ (.bin .div (V "i") (V "n"))) with hσ1
  have hci1 : σ1.vars "ci" = i / n := by simp [hσ1, MisBlk.den, Env.setVar, hi, hn]
  have hi1 : σ1.vars "i" = i := by simp [hσ1, Env.setVar, hi]
  have hn1 : σ1.vars "n" = n := by simp [hσ1, Env.setVar, hn]
  have s2 := asgE (B := B) "cr" (mul (V "ci") (V "n")) σ1 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_mul, hci1, hn1]
    omega)
  set σ2 := σ1.setVar "cr" (MisBlk.den σ1 (mul (V "ci") (V "n"))) with hσ2
  have hcr2 : σ2.vars "cr" = i / n * n := by simp [hσ2, MisBlk.den, Env.setVar, hci1, hn1]
  have hi2 : σ2.vars "i" = i := by simp [hσ2, Env.setVar, hi1]
  have s3 := asgE (B := B) "tt" (sub (V "i") (V "cr")) σ2 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_sub, hcr2, hi2]
    omega)
  set σ3 := σ2.setVar "tt" (MisBlk.den σ2 (sub (V "i") (V "cr"))) with hσ3
  have htt3 : σ3.vars "tt" = i % n := by
    simp [hσ3, MisBlk.den, Env.setVar, hcr2, hi2, Bop.apply_sub, hmsub]
  have hi3 : σ3.vars "i" = i := by simp [hσ3, Env.setVar, hi2]
  have hA3 : σ3.arrs "TK" = arr := by simp [hσ3, hσ2, hσ1, Env.setVar, hA]
  have e1 := hE (2 + 2 * i + 1) (by omega)
  have e3 := hE (2 + 2 * (i % n) + 1) (by omega)
  have s4 := asg_tk (B := B) "i" "da" 1 σ3 arr i hA3 hi3 (by omega) (by omega) (by omega)
  set σ4 := σ3.setVar "da" (arr.getD (2 + 2 * i + 1) 0) with hσ4
  have hA4 : σ4.arrs "TK" = arr := by simp [hσ4, Env.setVar, hA3]
  have htt4 : σ4.vars "tt" = i % n := by simp [hσ4, Env.setVar, htt3]
  have s5 := asg_tk (B := B) "tt" "db" 1 σ4 arr (i % n) hA4 htt4 (by omega) (by omega) (by omega)
  set σ5 := σ4.setVar "db" (arr.getD (2 + 2 * (i % n) + 1) 0) with hσ5
  have hda5 : σ5.vars "da" = arr.getD (2 + 2 * i + 1) 0 := by simp [hσ5, hσ4, Env.setVar]
  have hdb5 : σ5.vars "db" = arr.getD (2 + 2 * (i % n) + 1) 0 := by simp [hσ5, Env.setVar]
  have hok5 : σ5.vars "ok" = σ.vars "ok" := by
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have hA5 : σ5.arrs = σ.arrs := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have hO5 : σ5.out = σ.out := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have hfr5 : ∀ y, y ∉ SDID → σ5.vars y = σ.vars y := by
    intro y hy
    have g : ∀ z, z ∈ SDID → y ≠ z := fun z hz h => hy (h ▸ hz)
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar, g "ci" (by simp [SDID]), g "cr" (by simp [SDID]),
      g "tt" (by simp [SDID]), g "da" (by simp [SDID]), g "db" (by simp [SDID])]
  have sd : MisBlk.small B σ5 (V "da") := by show σ5.vars "da" < B; rw [hda5]; omega
  have se : MisBlk.small B σ5 (V "db") := by show σ5.vars "db" < B; rw [hdb5]; omega
  have s0 := MisBlk.asgE (B := B) "ok" (.lit 0) σ5 (by simp [MisBlk.small]; omega)
  have hz : (σ5.setVar "ok" (MisBlk.den σ5 (.lit 0))).vars "ok" = 0 := by
    simp [Env.setVar, MisBlk.den]
  have hfz : ∀ y, y ∉ SDID →
      (σ5.setVar "ok" (MisBlk.den σ5 (.lit 0))).vars y = σ.vars y := by
    intro y hy
    have : y ≠ "ok" := fun h => hy (by simp [SDID, h])
    simp only [Env.setVar, if_neg this]
    exact hfr5 y hy
  have hAz : (σ5.setVar "ok" (MisBlk.den σ5 (.lit 0))).arrs = σ.arrs := by simp [Env.setVar, hA5]
  have hOz : (σ5.setVar "ok" (MisBlk.den σ5 (.lit 0))).out = σ.out := by simp [Env.setVar, hO5]
  by_cases hpd : arr.getD (2 + 2 * i + 1) 0 = arr.getD (2 + 2 * (i % n) + 1) 0
  · have hT2 : (Cond.eq (V "da") (V "db")).evalB B σ5 = some true :=
      MisBlk.condEq_true _ _ σ5 sd se (by
        show σ5.vars "da" = σ5.vars "db"; rw [hda5, hdb5]; exact hpd)
    refine ⟨σ5, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (Run.ite_true hT2 Run.skip)))))).mono (by
      simp [Cond.size, Expr.size]), ?_, hA5, hO5, fun y hy => ?_⟩
    · rw [hok5]
      by_cases h1 : σ.vars "ok" = 1
      · rw [if_pos ⟨h1, hpd⟩]; omega
      · rw [if_neg (fun h => h1 h.1)]; omega
    · exact hfr5 y hy
  · have hF2 : (Cond.eq (V "da") (V "db")).evalB B σ5 = some false :=
      MisBlk.condEq_false _ _ σ5 sd se (by
        show σ5.vars "da" ≠ σ5.vars "db"; rw [hda5, hdb5]; exact hpd)
    refine ⟨_, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (Run.ite_false hF2 s0)))))).mono (by
      simp [Cond.size, Expr.size]), ?_, hAz, hOz, hfz⟩
    rw [hz, if_neg (fun h => hpd h.2)]

/-- The check of the whole table. -/
def didCom : Com := fLoop "i" "N" didBody

set_option maxHeartbeats 3200000 in
/-- **The day-independence check.** -/
theorem didCom_run (arr : List ℕ) (n m N : ℕ) (σ : Env)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hN : σ.vars "N" = N) (hNmn : N = m * n)
    (hlen : 3 + 2 * N ≤ arr.length) (hE : ∀ k < 3 + 2 * N, arr.getD k 0 + 8 < B)
    (hNB : 2 * N + 8 < B) (hok : σ.vars "ok" ≤ 1) :
    ∃ σ', Run B didCom σ σ' ((80 + 10 + 4) * N + 6) ∧
      σ'.vars "ok" = flagTo (DIDp arr n) (σ.vars "ok") N ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ "i" :: SDID → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hacc, hag, hout⟩ := fLoop_spec (B := B) "i" "N" "ok" didBody ("i" :: SDID)
    (fun j a => if a = 1 ∧ DIDp arr n j then 1 else 0) (fun j a => a ≤ 1) 80 N σ
    (by simp) (by simp [SDID]) (by decide) hN (by omega) hok
    (fun j a ha => by split <;> omega) (by
      intro σ1 hAg hlt hq
      have hA1 : σ1.arrs "TK" = arr := by rw [hAg.1]; exact hA
      have hn1 : σ1.vars "n" = n := by rw [hAg.2 "n" (by simp [SDID])]; exact hn
      have hn0 : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp at hNmn; omega
        · exact h
      have hnN : n ≤ N := by rw [hNmn]; exact Nat.le_mul_of_pos_left _ (by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h; simp at hNmn; omega
        · exact h)
      obtain ⟨σ2, r2, c2, a2, o2, f2⟩ := didBody_run (B := B) arr n N (σ1.vars "i") σ1 hA1 rfl hlt
        hn1 hn0 hnN hlen hE hNB hq
      refine ⟨σ2, r2, c2, ⟨by rw [a2, hAg.1], fun y hy => ?_⟩, f2 "i" (by simp [SDID]), o2⟩
      have hy' : y ∉ SDID := fun h => hy (List.mem_cons_of_mem _ h)
      rw [f2 y hy', hAg.2 y hy])
  refine ⟨σ', r, ?_, hag.1, hout, fun y hy => hag.2 y hy⟩
  rw [hacc]
  exact Lax117284Proofs.Machine.X3Loop.foldl_flag (DIDp arr n) (σ.vars "ok") hok N

end Lax117284Proofs.Machine.D3Did
