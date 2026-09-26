import Lax117284Proofs.Machine.ClMainCrit

/-!
The word length of the oracle: the least power of two that is at least `c1 * (2 * zl + m + 1) ^ E`,
found by doubling; `wpv` is its exponent and `Mp` the power itself.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.Machine.ClBuild

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The doubling of the power, one step. -/
def wpStep : Com := seqs [asg "Mp" (mul (lit 2) (V "Mp")), asg "wpv" (add (V "wpv") (lit 1))]

def wpLoop : Com := .while (.lt (V "Mp") (V "tg")) wpStep

/-- `E` multiplications of `tg` by `bs`. -/
def mulSteps : ℕ → Com
  | 0 => .skip
  | n + 1 => .seq (asg "tg" (mul (V "tg") (V "bs"))) (mulSteps n)

/-- The exponent `wpv` and the power `Mp` for the target `tg = c1 * (2 * zl + m + 1) ^ E`. -/
def wpCom (c1 E : ℕ) : Com := seqs [
  asg "bs" (add (add (mul (lit 2) (V "zl")) (V "m")) (lit 1)),
  asg "tg" (lit c1), mulSteps E, asg "wpv" (lit 0), asg "Mp" (lit 1), wpLoop]

variable {B tg zl m : ℕ} {σ : Env}

/-- The invariant of the doubling. -/
def WI (tg : ℕ) (σ : Env) : Prop :=
  σ.vars "tg" = tg ∧ σ.vars "Mp" = 2 ^ σ.vars "wpv" ∧ (σ.vars "wpv" = 0 → σ.vars "Mp" = 1) ∧
    (0 < σ.vars "wpv" → σ.vars "Mp" < 2 * tg)

theorem WI.mp_lt (h : WI tg σ) (h1 : 1 ≤ tg) (hB : 2 * tg < B) : σ.vars "Mp" < B := by
  by_cases hw : σ.vars "wpv" = 0
  · rw [h.2.2.1 hw]; omega
  · have := h.2.2.2 (Nat.pos_of_ne_zero hw); omega

theorem wpStep_spec (h1 : 1 ≤ tg) (hB : 2 * tg < B) :
    Spec B (fun σ => WI tg σ ∧ (Cond.lt (V "Mp") (V "tg")).evalB B σ = some true) wpStep
      (fun σ σ' => WI tg σ' ∧ tg - σ'.vars "Mp" < tg - σ.vars "Mp") 40 := by
  have key : ∀ σ : Env, WI tg σ ∧ (Cond.lt (V "Mp") (V "tg")).evalB B σ = some true →
      WI tg σ ∧ σ.vars "Mp" < tg := fun σ ⟨h, hv⟩ =>
    ⟨h, by have := lt_of_condLt_true hv; rw [h.1] at this; exact this⟩
  refine Spec.pre (P := fun σ => WI tg σ ∧ σ.vars "Mp" < tg) ?_ key
  run_vcg
  all_goals obtain ⟨ht, hM, h0, hp⟩ := ‹WI tg σ›
  all_goals have hw : σ.vars "wpv" < 2 ^ σ.vars "wpv" := Nat.lt_two_pow_self
  all_goals have hpos : 1 ≤ 2 ^ σ.vars "wpv" := Nat.one_le_two_pow
  · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [Env.setVar, ht, hM, pow_succ]
    all_goals omega
  all_goals simp [Env.setVar]
  all_goals omega

theorem wpLoop_spec (h1 : 1 ≤ tg) (hB : 2 * tg < B) :
    Spec B (WI tg) wpLoop
      (fun _ σ' => σ'.vars "Mp" = 2 ^ σ'.vars "wpv" ∧ tg ≤ σ'.vars "Mp" ∧ σ'.vars "Mp" ≤ 2 * tg ∧
        σ'.vars "wpv" = Nat.clog 2 tg)
      ((1 + 3 + 40) * tg + 1 + 3) := by
  have hs : (Cond.lt (V "Mp") (V "tg")).size = 3 := by simp
  refine (Spec.while_count (B := B) (b := Cond.lt (V "Mp") (V "tg")) (c := wpStep) (WI tg)
    (fun σ => tg - σ.vars "Mp") 40 ?_ (wpStep_spec h1 hB) (fun σ h => h) ?_).post ?_
  · intro σ h
    exact evalB_condLt_vars (h.mp_lt h1 hB) (by rw [h.1]; omega)
  · intro σ h
    have : tg - σ.vars "Mp" ≤ tg := Nat.sub_le _ _
    show (1 + 3 + 40) * (tg - σ.vars "Mp") + 1 + 3 ≤ (1 + 3 + 40) * tg + 1 + 3
    have := Nat.mul_le_mul_left (1 + 3 + 40) this
    omega
  · intro σ σ' h ⟨hI, hf⟩
    have hle := le_of_condLt_false hf
    obtain ⟨ht, hM, h0, hp⟩ := hI
    rw [ht] at hle
    refine ⟨hM, hle, ?_, ?_⟩
    · by_cases hw : σ'.vars "wpv" = 0
      · rw [h0 hw]; omega
      · have := hp (Nat.pos_of_ne_zero hw); omega
    · apply le_antisymm
      · by_cases hw : σ'.vars "wpv" = 0
        · omega
        · have hp' := hp (Nat.pos_of_ne_zero hw)
          have h2 : 2 ^ σ'.vars "wpv" = 2 * 2 ^ (σ'.vars "wpv" - 1) := by
            rw [← pow_succ']; congr 1; omega
          have := (Nat.lt_clog_iff_pow_lt (b := 2) (by norm_num) (x := tg) (y := σ'.vars "wpv" - 1)).mpr
            (by omega)
          omega
      · exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr (by rw [← hM]; exact hle)

/-- The scalars the exponent is computed from. -/
def WP (zl m : ℕ) (σ : Env) : Prop := σ.vars "zl" = zl ∧ σ.vars "m" = m

theorem mulSteps_spec (b : ℕ) (hb : 1 ≤ b) (hbB : b < B) : ∀ (n t : ℕ), t * b ^ n < B →
    Spec B (fun σ => σ.vars "bs" = b ∧ σ.vars "tg" = t) (mulSteps n)
      (fun _ σ' => σ'.vars "bs" = b ∧ σ'.vars "tg" = t * b ^ n) (10 * n + 1)
  | 0, t, _ => by
    refine Spec.mono (Spec.post Spec.skip ?_) (by omega)
    rintro σ σ' ⟨h1, h2⟩ rfl
    exact ⟨h1, by simpa using h2⟩
  | n + 1, t, h => by
    have hbn : b ≤ b ^ (n + 1) := Nat.le_self_pow (by omega) b
    have htb : t * b ≤ t * b ^ (n + 1) := Nat.mul_le_mul_left _ hbn
    have hp1 : 1 ≤ b ^ (n + 1) := Nat.one_le_pow _ _ (by omega)
    have ht : t ≤ t * b ^ (n + 1) := Nat.le_mul_of_pos_right _ hp1
    have h' : t * b * b ^ n < B := by rw [mul_assoc, ← pow_succ']; exact h
    have ih := mulSteps_spec b hb hbB n (t * b) h'
    have e : t * b ^ (n + 1) = t * b * b ^ n := by ring
    have hs : Spec B (fun σ => σ.vars "bs" = b ∧ σ.vars "tg" = t) (asg "tg" (mul (V "tg") (V "bs")))
        (fun _ σ' => σ'.vars "bs" = b ∧ σ'.vars "tg" = t * b) 4 := by
      run_vcg
      all_goals (rename_i h1 h2)
      all_goals first | (simp [Env.setVar, h1, h2]; done) | (simp only [h1, h2]; omega) | omega
    unfold mulSteps
    refine Spec.mono (Spec.post (Spec.seq hs ih (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)) ?_) (by omega)
    rintro σ σ' - h
    rw [e]; exact h

theorem wpCom_spec (c1 E : ℕ) (hc : 1 ≤ c1) (hbB : 2 * zl + m + 1 < B)
    (hB : 2 * (c1 * (2 * zl + m + 1) ^ E) < B) :
    Spec B (WP zl m) (wpCom c1 E)
      (fun _ σ' => σ'.vars "Mp" = 2 ^ σ'.vars "wpv" ∧ c1 * (2 * zl + m + 1) ^ E ≤ σ'.vars "Mp" ∧
        σ'.vars "Mp" ≤ 2 * (c1 * (2 * zl + m + 1) ^ E) ∧
        σ'.vars "wpv" = Nat.clog 2 (c1 * (2 * zl + m + 1) ^ E))
      (44 * (c1 * (2 * zl + m + 1) ^ E) + 10 * E + 80) := by
  have hb1 : 1 ≤ 2 * zl + m + 1 := by omega
  have hp1 : 1 ≤ (2 * zl + m + 1) ^ E := Nat.one_le_pow _ _ hb1
  have h1 : 1 ≤ c1 * (2 * zl + m + 1) ^ E := Nat.mul_pos hc hp1
  have hl := wpLoop_spec (B := B) h1 hB
  have hc1B : c1 < B := by
    have := Nat.le_mul_of_pos_right c1 hp1
    omega
  have hm := mulSteps_spec (B := B) (2 * zl + m + 1) hb1 hbB E c1 (by omega)
  run_vcg [hm, hl]
  all_goals try assumption
  all_goals try obtain ⟨hz, hm'⟩ := ‹WP zl m σ›
  all_goals try (rw [hz]; omega)
  all_goals try (rw [hm']; omega)
  all_goals try omega
  all_goals try (simp [Env.setVar, hz, hm']; done)
  simp [WI, Env.setVar]
  simp_all

end Lax117284Proofs.Machine.ClMain
