import Lax117284Proofs.Machine.D3Cell

/-!
One day of a client: the processing time of the client on the day is read off the table, the
table is swept, and the weight of the day's digit moves to the next.
-/

namespace Lax117284Proofs.Machine.D3Day

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.FoldLoop
open Lax117284Proofs.Machine.MisBlk (asgE condLt_true condLt_false)
open Lax117284Proofs.Machine.X3Loop (rd)
open Lax117284Proofs.Machine.D3Ops Lax117284Proofs.Machine.D3Sweep

variable {B : ℕ}

/-- The environment with the day's scalars changed. -/
lemma rescalEnv {arr : List ℕ} {n P k b1 pw pw2 c qic qic2 ec PK : ℕ} {σ σ' : Env}
    (h : SwEnv B arr n P k b1 pw c qic ec PK σ)
    (hv : ∀ y ∈ ["PK", "PP", "kp", "b1", "cl", "ec"], σ'.vars y = σ.vars y)
    (hpw : σ'.vars "pw" = pw2) (hq : σ'.vars "qic" = qic2) (hpB : pw2 + 8 < B) (hqB : qic2 + 8 < B)
    (ha : σ'.arrs = σ.arrs) : SwEnv B arr n P k b1 pw2 c qic2 ec PK σ' := by
  refine ⟨by rw [ha]; exact h.hA, ?_, ?_, ?_, ?_, hpw, ?_, hq, ?_, h.hlen, h.hE, h.hnB,
    by rw [ha]; exact h.hRlen, by rw [ha]; exact h.hRK, by rw [ha]; exact h.hRv,
    by rw [ha]; exact h.hRB, h.hPKB, h.hPB, h.hkB, h.hb1B, hpB, h.hcB, hqB, h.heB⟩
  · rw [hv "PK" (by simp)]; exact h.vPK
  · rw [hv "PP" (by simp)]; exact h.vPP
  · rw [hv "kp" (by simp)]; exact h.vkp
  · rw [hv "b1" (by simp)]; exact h.vb1
  · rw [hv "cl" (by simp)]; exact h.vcl
  · rw [hv "ec" (by simp)]; exact h.vec

/-- The body of the loop over the days. -/
def dayBody : Com :=
  .seq (.assign "ix2" (add (mul (V "dy") (V "n")) (V "jc")))
  (.seq (.assign "qic" (rd "ix2" 0))
  (.seq sweepLoop (.assign "pw" (mul (V "pw") (V "b1")))))

/-- The scalars the day assigns, besides those of the sweep. -/
def SDAY : List String := ["ix2", "qic", "pw"]

set_option maxHeartbeats 12800000 in
/-- **One day of a client.** -/
theorem dayBody_run {arr : List ℕ} {n m P k b1 pw c qic ec PK : ℕ} (σ : Env)
    (h : SwEnv B arr n P k b1 pw c qic ec PK σ) (hP0 : 0 < P) (i jc : ℕ)
    (hdy : σ.vars "dy" = i) (hn : σ.vars "n" = n) (hjc : σ.vars "jc" = jc) (hi : i < m)
    (hjcn : jc < n) (hlen : 3 + 2 * (m * n) ≤ arr.length)
    (hE : ∀ j < 3 + 2 * (m * n), arr.getD j 0 + 8 < B) (hmnB : 2 * (m * n) + 8 < B)
    (hpw2 : pw * b1 + 8 < B)
    (hcells : ∀ x < PK, (σ.arrs "R").getD x 0 = 1 → CellOk arr (σ.arrs "R") n P k b1 pw c
      (arr.getD (2 + 2 * (i * n + jc)) 0) ec PK B x)
    (h01 : ∀ x < PK, (σ.arrs "R").getD x 0 ≤ 1) :
    ∃ σ', Run B dayBody σ σ' ((400 + 10 + 4) * PK + 6 + 60) ∧
      SwEnv B arr n P k b1 (pw * b1) c (arr.getD (2 + 2 * (i * n + jc)) 0) ec PK σ' ∧
      σ'.arrs "R" = D3List.swRun PK (tgtM P k b1 pw c (arr.getD (2 + 2 * (i * n + jc)) 0) ec
        (eOrd arr (σ.arrs "R") PK)) (σ.arrs "R") ∧
      σ'.arrs "TK" = σ.arrs "TK" ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ SDAY ++ ("jj" :: SSW) → σ'.vars y = σ.vars y := by
  have hidx : i * n + jc < m * n := by
    have := Nat.mul_le_mul_right n (show i + 1 ≤ m by omega)
    nlinarith
  have e1 := hE (2 + 2 * (i * n + jc)) (by omega)
  have e0 : arr.getD (2 + 2 * (i * n + jc) + 0) 0 = arr.getD (2 + 2 * (i * n + jc)) 0 := rfl
  have hiB : i * n + jc + 8 < B := by omega
  have s1 := asgE (B := B) "ix2" (add (mul (V "dy") (V "n")) (V "jc")) σ (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_add, Bop.apply_mul,
      hdy, hn, hjc]
    have h1 : i * n ≤ m * n := Nat.mul_le_mul_right n (by omega)
    have h2 : i ≤ i * n := Nat.le_mul_of_pos_right i (by omega)
    have h3 : n ≤ m * n := Nat.le_mul_of_pos_left n (by omega)
    have hd : MisBlk.den σ (mul (V "dy") (V "n")) = i * n := by
      simp [mul, hdy, hn]
    rw [hd]
    exact ⟨⟨by omega, by omega, by omega⟩, by omega, by omega⟩)
  set σ1 := σ.setVar "ix2" (MisBlk.den σ (add (mul (V "dy") (V "n")) (V "jc"))) with hσ1
  have hix1 : σ1.vars "ix2" = i * n + jc := by
    simp [hσ1, MisBlk.den, Env.setVar, hdy, hn, hjc]
  have hA1 : σ1.arrs = σ.arrs := by simp [hσ1, Env.setVar]
  have s2 := asg_tk (B := B) "ix2" "qic" 0 σ1 arr (i * n + jc) (by rw [hA1]; exact h.hA) hix1
    (by omega) (by omega) (by omega)
  set σ2 := σ1.setVar "qic" (arr.getD (2 + 2 * (i * n + jc) + 0) 0) with hσ2
  have hqic2 : σ2.vars "qic" = arr.getD (2 + 2 * (i * n + jc)) 0 := by
    simp [hσ2, Env.setVar]
  have hA2 : σ2.arrs = σ.arrs := by simp [hσ2, Env.setVar, hA1]
  have hv2 : ∀ y, y ≠ "ix2" → y ≠ "qic" → σ2.vars y = σ.vars y := by
    intro y a b; simp [hσ2, hσ1, Env.setVar, a, b]
  have hh2 : SwEnv B arr n P k b1 pw c (arr.getD (2 + 2 * (i * n + jc)) 0) ec PK σ2 :=
    rescalEnv h (fun y hy => hv2 y (by intro e; subst e; simp at hy) (by intro e; subst e; simp at hy))
      (by rw [hv2 "pw" (by decide) (by decide)]; exact h.vpw) hqic2 h.hpwB
      (by have := hE (2 + 2 * (i * n + jc)) (by omega); omega) hA2
  obtain ⟨σ3, r3, hh3, hR3, hA3, hO3, hF3⟩ := sweepLoop_run (B := B) σ2 hh2 hP0
    (by rw [hA2]; exact hcells) (by rw [hA2]; exact h01)
  have hpw3 : σ3.vars "pw" = pw := by
    rw [hF3 "pw" (by simp [SSW, S1, S2])]; exact hh2.vpw
  have hb13 : σ3.vars "b1" = b1 := hh3.vb1
  have s4 := asgE (B := B) "pw" (mul (V "pw") (V "b1")) σ3 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_mul, hpw3, hb13]
    have := h.hpwB; have := h.hb1B
    exact ⟨by omega, by omega, by omega⟩)
  set σ4 := σ3.setVar "pw" (MisBlk.den σ3 (mul (V "pw") (V "b1"))) with hσ4
  have hpw4 : σ4.vars "pw" = pw * b1 := by simp [hσ4, MisBlk.den, Env.setVar, hpw3, hb13]
  have hA4 : σ4.arrs = σ3.arrs := by simp [hσ4, Env.setVar]
  have hv4 : ∀ y, y ≠ "pw" → σ4.vars y = σ3.vars y := by intro y a; simp [hσ4, Env.setVar, a]
  refine ⟨σ4, (s1.seq (s2.seq (r3.seq s4))).mono (by simp [Expr.size]; omega), ?_, ?_, ?_, ?_,
    fun y hy => ?_⟩
  · have hq3 : σ3.vars "qic" = arr.getD (2 + 2 * (i * n + jc)) 0 := hh3.vqic
    refine rescalEnv hh3 (fun y hy' => ?_) hpw4 (by rw [hv4 "qic" (by decide)]; exact hq3) hpw2
      (by have := hE (2 + 2 * (i * n + jc)) (by omega); omega) hA4
    rw [hv4 y (by intro e; subst e; simp at hy')]
  · rw [hA4, hR3, hA2]
  · rw [hA4, hA3, hA2]
  · simp [hσ4, hO3, hσ2, hσ1, Env.setVar]
  · have g : y ∉ SDAY := fun e => hy (List.mem_append_left _ e)
    have g2 : y ∉ "jj" :: SSW := fun e => hy (List.mem_append_right _ e)
    have g3 : y ≠ "pw" := fun e => g (by simp [SDAY, e])
    have g4 : y ≠ "ix2" := fun e => g (by simp [SDAY, e])
    have g5 : y ≠ "qic" := fun e => g (by simp [SDAY, e])
    rw [hv4 y g3, hF3 y g2, hv2 y g4 g5]

end Lax117284Proofs.Machine.D3Day
