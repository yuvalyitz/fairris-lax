import Lax117284Proofs.Machine.TwPrep

/-!
The loops that compute `⌊log₂ L⌋` and the number of admitted widths.
-/

namespace Lax117284Proofs.Machine.TwPrep

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {B : ℕ}

/-- One more if `2 ^ (lg + 1) ≤ L`. -/
def lgBody : Com :=
  .ite (.lt (Expr.lit 1) (.bin .shiftr (V "L") (V "lg"))) (.assign "lg" (add (V "lg") (Expr.lit 1)))
    .skip

/-- The loop: `lg` becomes `⌊log₂ L⌋`. -/
def lgLoop : Com := fLoop "j" "L" lgBody

theorem lgBody_run (σ : Env) (hL : σ.vars "L" < B) (hlg : σ.vars "lg" + 2 < B) :
    ∃ σ', Run B lgBody σ σ' 20 ∧ σ'.vars "lg" = lgStep (σ.vars "L") (σ.vars "lg") ∧
      Agr ["lg"] σ σ' ∧ σ'.vars "j" = σ.vars "j" ∧ σ'.out = σ.out := by
  have hd : σ.vars "L" / 2 ^ σ.vars "lg" < B := lt_of_le_of_lt (Nat.div_le_self _ _) hL
  unfold lgBody
  run_vcg
  · refine ⟨?_, agr_set (by simp) _, by simp [Env.setVar], rfl⟩
    unfold lgStep; rw [if_pos (by omega)]; nrm
  · refine ⟨?_, Agr.refl _ _, rfl, rfl⟩
    unfold lgStep; rw [if_neg (by omega)]; rfl

theorem lgLoop_run (σ0 : Env) (L : ℕ) (hL0 : 0 < L) (hLv : σ0.vars "L" = L) (hLB : L + 3 < B)
    (hlg0 : σ0.vars "lg" = 0) :
    ∃ σ', Run B lgLoop σ0 σ' ((20 + 10 + 4) * L + 6) ∧ σ'.vars "lg" = Nat.log 2 L ∧
      Agr ["j", "lg"] σ0 σ' ∧ σ'.out = σ0.out := by
  have hf := fLoop_spec (B := B) "j" "L" "lg" lgBody ["j", "lg"] (fun _ a => lgStep L a)
    (fun _ a => a ≤ Nat.log 2 L) 20 L σ0 (by simp) (by simp) (by decide) hLv (by omega)
    (by rw [hlg0]; omega)
    (fun j a h => by
      unfold lgStep
      by_cases hc : 1 < L / 2 ^ a
      · rw [if_pos hc]; have := (one_lt_div_iff (by omega)).1 hc; omega
      · rw [if_neg hc]; omega)
    (by
      intro σ hA hlt hQ
      have hfr : ∀ y, y ∉ ["j", "lg"] → σ.vars y = σ0.vars y := hA.2
      have e1 : σ.vars "L" = L := by rw [hfr "L" (by simp)]; exact hLv
      have hlogL : Nat.log 2 L ≤ L := Nat.log_le_self 2 L
      obtain ⟨σ', r, hv, hA', hj, ho⟩ := lgBody_run (B := B) σ (by rw [e1]; omega)
        (by have := hQ; omega)
      refine ⟨σ', r, ?_, agr_comp (S := ["j", "lg"]) hA hA' (by intro x hx; exact hx)
        (by intro x hx; simp at hx; simp [hx]), hj, ho⟩
      rw [hv, e1])
  obtain ⟨σ', r, hv, hA, ho⟩ := hf
  refine ⟨σ', r, ?_, hA, ho⟩
  rw [hv, hlg0, lg_iter (by omega) L]
  exact min_eq_right (Nat.log_le_self 2 L)

/-- The number `geE cc m j`, as an expression. -/
def geExpr (cc : ℕ) : Expr :=
  add (add (mul (Expr.lit cc) (mul (mul (add (V "j") (Expr.lit 1)) (add (V "j") (Expr.lit 1)))
    (add (V "j") (Expr.lit 1)))) (mul (V "m") (add (V "j") (Expr.lit 1)))) (Expr.lit 2)

/-- One more if the width `j` is admitted. -/
def wcBody (cc : ℕ) : Com :=
  .ite (.lt (geExpr cc) (V "lg1")) (.assign "wc" (add (V "wc") (Expr.lit 1))) .skip

/-- The loop: `wc` becomes the number of admitted widths. -/
def wcLoop (cc : ℕ) : Com := fLoop "j" "lg1" (wcBody cc)

theorem wcBody_run (cc : ℕ) (σ : Env) (hcc : 1 ≤ cc) (hccB : cc < B)
    (hgB : geE cc (σ.vars "m") (σ.vars "j") + 3 < B) (hlg1 : σ.vars "lg1" < B)
    (hwc : σ.vars "wc" + 2 < B) :
    ∃ σ', Run B (wcBody cc) σ σ' 40 ∧
      σ'.vars "wc" = σ.vars "wc" +
        (if geE cc (σ.vars "m") (σ.vars "j") < σ.vars "lg1" then 1 else 0) ∧
      Agr ["wc"] σ σ' ∧ σ'.vars "j" = σ.vars "j" ∧ σ'.out = σ.out := by
  have ha : σ.vars "j" + 1 ≤ (σ.vars "j" + 1) * (σ.vars "j" + 1) := Nat.le_mul_self _
  have ha2 : (σ.vars "j" + 1) * (σ.vars "j" + 1) ≤
      (σ.vars "j" + 1) * (σ.vars "j" + 1) * (σ.vars "j" + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have ht : (σ.vars "j" + 1) * (σ.vars "j" + 1) * (σ.vars "j" + 1) ≤
      cc * ((σ.vars "j" + 1) * (σ.vars "j" + 1) * (σ.vars "j" + 1)) :=
    Nat.le_mul_of_pos_left _ hcc
  have hmm : σ.vars "m" ≤ σ.vars "m" * (σ.vars "j" + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hg : geE cc (σ.vars "m") (σ.vars "j") = cc * ((σ.vars "j" + 1) * (σ.vars "j" + 1) *
      (σ.vars "j" + 1)) + σ.vars "m" * (σ.vars "j" + 1) + 2 := rfl
  unfold wcBody geExpr
  run_vcg
  all_goals first
    | (refine ⟨?_, agr_set (by simp) _, by simp [Env.setVar], rfl⟩
       nrm
       rw [if_pos (by omega)])
    | (refine ⟨?_, Agr.refl _ _, rfl, rfl⟩
       rw [if_neg (by omega), Nat.add_zero])
    | omega

end Lax117284Proofs.Machine.TwPrep
