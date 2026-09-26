import Lax117284Proofs.Machine.MisBlk

/-!
The power `(n + 1) ^ m` of a fixed number `m` of days: `m` is fixed once and for all, so the power
is computed by `m` multiplications laid out once, at the time the command is built.
-/

namespace Lax117284Proofs.Machine.D3Pow

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.MisBlk

variable {B : ℕ}

/-- A variable, as an expression. -/
abbrev V (s : String) : Expr := .var s

/-- Multiplication of two expressions. -/
abbrev mul (e f : Expr) : Expr := .bin .mul e f

/-- The command that computes `PP := b1 ^ m`, from `PP := 1` by `m` multiplications. -/
def powCom : ℕ → Com
  | 0 => .assign "PP" (.lit 1)
  | m + 1 => .seq (powCom m) (.assign "PP" (mul (V "PP") (V "b1")))

/-- The size of `powCom m`, for the cost bound. -/
def KpowCom : ℕ → ℕ
  | 0 => 1 + (Expr.lit 1 : Expr).size
  | m + 1 => KpowCom m + (1 + (mul (V "PP") (V "b1")).size)

set_option maxHeartbeats 3200000 in
/-- **The power of a fixed number of days.** -/
theorem powCom_run (m : ℕ) (σ : Env) (b1 : ℕ) (hb1 : σ.vars "b1" = b1)
    (hbd : ∀ i ≤ m, b1 ^ i + 8 < B) :
    ∃ σ', Run B (powCom m) σ σ' (KpowCom m) ∧ σ'.vars "PP" = b1 ^ m ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ≠ "PP" → σ'.vars y = σ.vars y := by
  induction m with
  | zero =>
    refine ⟨σ.setVar "PP" (MisBlk.den σ (.lit 1)), ?_, ?_, ?_, ?_, ?_⟩
    · exact asgE (B := B) "PP" (.lit 1) σ (by simp [MisBlk.small]; have := hbd 0 le_rfl; omega)
    · simp [Env.setVar, MisBlk.den]
    · simp [Env.setVar]
    · simp [Env.setVar]
    · intro y hy; simp [Env.setVar, hy]
  | succ m ih =>
    obtain ⟨σ1, r1, hPP1, hA1, hO1, hF1⟩ := ih (fun i hi => hbd i (by omega))
    have hb11 : σ1.vars "b1" = b1 := hF1 "b1" (by decide) ▸ hb1
    have s2 := asgE (B := B) "PP" (mul (V "PP") (V "b1")) σ1 (by
      simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_mul, hPP1, hb11]
      have h1 := hbd (m + 1) le_rfl
      have h2 := hbd m (by omega)
      have h3 := hbd 1 (by omega)
      have hpow : b1 ^ (m + 1) = b1 ^ m * b1 := pow_succ b1 m
      simp only [pow_one] at h3
      exact ⟨by omega, by omega, by omega⟩)
    refine ⟨σ1.setVar "PP" (MisBlk.den σ1 (mul (V "PP") (V "b1"))), (r1.seq s2), ?_, ?_, ?_, ?_⟩
    · simp [Env.setVar, MisBlk.den, Bop.apply_mul, hPP1, hb11, pow_succ]
    · simp [Env.setVar, hA1]
    · simp [Env.setVar, hO1]
    · intro y hy; simp only [Env.setVar, if_neg hy]; exact hF1 y hy

/-- Subtraction of two expressions. -/
abbrev sub (e f : Expr) : Expr := .bin .sub e f

/-- The body of the check that the runtime copy `mc` reaches `0` after `d` decrements: one
decrement, or a failure the moment `mc` is already `0`. -/
def checkMLoop : ℕ → Com
  | 0 => .ite (.eq (V "mc") (.lit 0)) .skip (.assign "ok" (.lit 0))
  | d + 1 => .ite (.lt (.lit 0) (V "mc"))
      (.seq (.assign "mc" (sub (V "mc") (.lit 1))) (checkMLoop d))
      (.assign "ok" (.lit 0))

/-- The cost of `checkMLoop d`. -/
def KcheckMLoop : ℕ → ℕ
  | 0 => 20
  | d + 1 => 20 + (1 + (sub (V "mc") (.lit 1)).size) + KcheckMLoop d

set_option maxHeartbeats 3200000 in
/-- **The check that `mc` equals `d`, by `d` decrements.** -/
theorem checkMLoop_run (d : ℕ) (σ : Env) (mc0 ok0 : ℕ) (hmc : σ.vars "mc" = mc0) (hmcB : mc0 < B)
    (hok : σ.vars "ok" = ok0) (hok01 : ok0 ≤ 1) :
    ∃ σ', Run B (checkMLoop d) σ σ' (KcheckMLoop d) ∧
      σ'.vars "ok" = (if mc0 = d then ok0 else 0) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ≠ "ok" → y ≠ "mc" → σ'.vars y = σ.vars y := by
  induction d generalizing σ mc0 with
  | zero =>
    have hsc : MisBlk.small B σ (V "mc") := by show σ.vars "mc" < B; rw [hmc]; exact hmcB
    have hs0 : MisBlk.small B σ (Expr.lit 0) := by simp [MisBlk.small]; omega
    by_cases hc : mc0 = 0
    · have hT : (Cond.eq (V "mc") (.lit 0)).evalB B σ = some true :=
        condEq_true _ _ σ hsc hs0 (by simp [MisBlk.den, hmc, hc])
      refine ⟨_, (Run.ite_true hT Run.skip).mono (by simp [Cond.size, Expr.size, KcheckMLoop]),
        ?_, rfl, rfl, fun y a b => rfl⟩
      rw [if_pos hc]; exact hok
    · have hF : (Cond.eq (V "mc") (.lit 0)).evalB B σ = some false :=
        condEq_false _ _ σ hsc hs0 (by simp [MisBlk.den, hmc]; exact hc)
      have s := asgE (B := B) "ok" (.lit 0) σ (by simp [MisBlk.small]; omega)
      refine ⟨_, (Run.ite_false hF s).mono (by simp [Cond.size, Expr.size, KcheckMLoop]), ?_, ?_,
        ?_, fun y a b => ?_⟩
      · simp [Env.setVar, MisBlk.den, if_neg hc]
      · simp [Env.setVar]
      · simp [Env.setVar]
      · simp only [Env.setVar, if_neg a]
  | succ d ih =>
    have hs0 : MisBlk.small B σ (Expr.lit 0) := by simp [MisBlk.small]; omega
    have hsc : MisBlk.small B σ (V "mc") := by show σ.vars "mc" < B; rw [hmc]; exact hmcB
    by_cases hc : 0 < mc0
    · have hT : (Cond.lt (.lit 0) (V "mc")).evalB B σ = some true :=
        condLt_true _ _ σ hs0 hsc (by simpa [MisBlk.den, hmc] using hc)
      have s1 := asgE (B := B) "mc" (sub (V "mc") (.lit 1)) σ (by
        show MisBlk.small B σ (V "mc") ∧ MisBlk.small B σ (Expr.lit 1) ∧
          Bop.apply .sub (MisBlk.den σ (V "mc")) (MisBlk.den σ (Expr.lit 1)) < B
        simp only [MisBlk.den_var, MisBlk.den_lit, Bop.apply_sub, hmc]
        exact ⟨hsc, by simp [MisBlk.small]; omega, by omega⟩)
      set σ1 := σ.setVar "mc" (MisBlk.den σ (sub (V "mc") (.lit 1))) with hσ1
      have hmc1 : σ1.vars "mc" = mc0 - 1 := by
        simp [hσ1, MisBlk.den, Env.setVar, hmc, Bop.apply_sub]
      have hok1 : σ1.vars "ok" = ok0 := by simp [hσ1, Env.setVar, hok]
      obtain ⟨σ2, r2, ho2, hA2, hO2, hF2⟩ := ih σ1 (mc0 - 1) hmc1 (by omega) hok1
      refine ⟨σ2, (Run.ite_true hT (s1.seq r2)).mono (by
        simp [Cond.size, Expr.size, KcheckMLoop]; omega), ?_, ?_, ?_, fun y a b => ?_⟩
      · rw [ho2]
        by_cases hpos : mc0 = d + 1
        · rw [if_pos hpos, if_pos (by omega : mc0 - 1 = d)]
        · rw [if_neg hpos, if_neg (by omega : mc0 - 1 ≠ d)]
      · simp [hA2, hσ1, Env.setVar]
      · simp [hO2, hσ1, Env.setVar]
      · rw [hF2 y a b]; simp [hσ1, Env.setVar, b]
    · have hF : (Cond.lt (.lit 0) (V "mc")).evalB B σ = some false :=
        condLt_false _ _ σ hs0 hsc (by simpa [MisBlk.den, hmc] using hc)
      have s := asgE (B := B) "ok" (.lit 0) σ (by simp [MisBlk.small]; omega)
      refine ⟨_, (Run.ite_false hF s).mono (by simp [Cond.size, Expr.size, KcheckMLoop]; omega),
        ?_, ?_, ?_, fun y a b => ?_⟩
      · simp only [Env.setVar, MisBlk.den, if_true]
        rw [if_neg (by omega)]
      · simp [Env.setVar]
      · simp [Env.setVar]
      · simp only [Env.setVar, if_neg a]

/-- **The check that the runtime `m` equals the fixed `m`.** -/
def checkM (m : ℕ) : Com := .seq (.assign "mc" (V "m")) (checkMLoop m)

/-- The cost of `checkM m`. -/
def KcheckM (m : ℕ) : ℕ := (1 + (V "m" : Expr).size) + KcheckMLoop m

set_option maxHeartbeats 3200000 in
/-- **The gate.** -/
theorem checkM_run (m : ℕ) (σ : Env) (m0 ok0 : ℕ) (hm : σ.vars "m" = m0) (hm0B : m0 < B)
    (hok : σ.vars "ok" = ok0) (hok01 : ok0 ≤ 1) :
    ∃ σ', Run B (checkM m) σ σ' (KcheckM m) ∧
      σ'.vars "ok" = (if m0 = m then ok0 else 0) ∧ σ'.vars "m" = m0 ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ≠ "ok" → y ≠ "mc" → y ≠ "m" → σ'.vars y = σ.vars y := by
  have s1 := asgE (B := B) "mc" (V "m") σ (by simp only [MisBlk.small_var]; omega)
  set σ1 := σ.setVar "mc" (MisBlk.den σ (V "m")) with hσ1
  have hmc1 : σ1.vars "mc" = m0 := by simp [hσ1, MisBlk.den, Env.setVar, hm]
  have hok1 : σ1.vars "ok" = ok0 := by simp [hσ1, Env.setVar, hok]
  have hm1 : σ1.vars "m" = m0 := by simp [hσ1, Env.setVar, hm]
  obtain ⟨σ2, r2, ho2, hA2, hO2, hF2⟩ := checkMLoop_run (B := B) m σ1 m0 ok0 hmc1 hm0B hok1
    hok01
  refine ⟨σ2, (s1.seq r2).mono (by simp [KcheckM]), ho2, ?_, hA2, hO2, fun y a b _ => ?_⟩
  · rw [hF2 "m" (by decide) (by decide)]; exact hm1
  · rw [hF2 y a b]; simp [hσ1, Env.setVar, b]

end Lax117284Proofs.Machine.D3Pow
