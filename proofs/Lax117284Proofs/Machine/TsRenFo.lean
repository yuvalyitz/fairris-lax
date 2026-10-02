import Lax117284Proofs.Machine.SatOps
import Lax117284Proofs.Machine.TsRenSem

/-!
The first occurrence of the variable of a position: a loop over the earlier positions that
remembers the first one carrying the same variable.
-/

namespace Lax117284Proofs.Machine.TsRenFo

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.SatOps
open Lax117284Proofs.TwoSatRename Lax117284Proofs.Machine.TsRenSem

variable {B : ℕ}

abbrev bumpS (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

/-- The body of the loop: compare the earlier position `j` with the given one, and remember
`j` if it is the first to agree. -/
def foBody : Com :=
  .seq (.assign "vj" (.get "TK" (add (.lit 2) (mul (.lit 2) (V "j")))))
  (.seq (.ite (.eq (V "vj") (V "vp")) (.ite (.eq (V "r") (V "p")) (.assign "r" (V "j")) .skip) .skip)
    (bumpS "j"))

def foLoop : Com := .seq (.assign "j" (.lit 0)) (.while (.lt (V "j") (V "p")) foBody)

/-- The scalars the loop assigns. -/
def AF : List String := ["j", "vj", "r"]

structure FInv (arr : List ℕ) (p : ℕ) (σ0 σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  hp : σ.vars "p" = p
  hvp : σ.vars "vp" = arr.getD (2 + 2 * p) 0
  hj : σ.vars "j" ≤ p
  hr : σ.vars "r" = if fo (idxA arr) p < σ.vars "j" then fo (idxA arr) p else p
  fr : ∀ y, y ∉ AF → σ.vars y = σ0.vars y

lemma finv_step (arr : List ℕ) (p : ℕ) (σ0 σ σ' : Env) (hI : FInv arr p σ0 σ)
    (hlt : σ.vars "j" < p) (hv : ∀ y, y ∉ AF → σ'.vars y = σ.vars y)
    (ha : σ'.arrs = σ.arrs) (ho : σ'.out = σ.out) (_hj : σ'.vars "j" = σ.vars "j")
    (hr : σ'.vars "r" = if fo (idxA arr) p < σ.vars "j" + 1 then fo (idxA arr) p else p) :
    FInv arr p σ0 (σ'.setVar "j" (σ.vars "j" + 1)) ∧
      (σ'.setVar "j" (σ.vars "j" + 1)).vars "j" = σ.vars "j" + 1 := by
  have hsa := hI.arrs
  have hso := hI.out
  have hA0 := hI.hA
  have hpv := hI.hp
  have hvpv := hI.hvp
  have hjle := hI.hj
  have hfr := hI.fr
  clear hI
  refine ⟨⟨?_, ?_, hA0, ?_, ?_, ?_, ?_, fun y hy => ?_⟩, by simp [Env.setVar]⟩
  · simp only [Env.setVar]; rw [ha, hsa]
  · simp only [Env.setVar]; rw [ho, hso]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "p" (by simp [AF]), hpv]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "vp" (by simp [AF]), hvpv]
  · simp [Env.setVar]; omega
  · simp only [Env.setVar]; rw [if_neg (by decide), if_true, hr]
  · have hyj : y ≠ "j" := fun h => hy (by simp [AF, h])
    simp only [Env.setVar, if_neg hyj]
    rw [hv y hy, hfr y hy]

set_option maxHeartbeats 1600000 in
theorem foBody_spec (arr : List ℕ) (p : ℕ) (σ0 : Env)
    (hE : ∀ k ≤ p, arr.getD (2 + 2 * k) 0 + 8 < B)
    (hlen : 3 + 2 * p ≤ arr.length) (hpB : 2 * p + 16 < B) :
    Spec B (fun σ => FInv arr p σ0 σ ∧ σ.vars "j" < p) foBody
      (fun σ σ' => FInv arr p σ0 σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 40 := by
  rintro σ ⟨hI, hlt⟩
  have hI' := hI
  obtain ⟨hsa, hso, hA0, hpv, hvpv, hjle, hrv, hfr⟩ := hI
  have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
  set j := σ.vars "j" with hjdef
  have hjv : σ.vars "j" = j := rfl
  have hfle := fo_le (idxA arr) p
  have hrB : σ.vars "r" < B := by rw [hrv]; split <;> omega
  have e1 := hE j (by omega)
  have e2 := hE p le_rfl
  have s1 := asg_idx (B := B) "vj" 2 2 "j" σ arr j hA rfl (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  set σ1 := σ.setVar "vj" (arr.getD (2 + 2 * j) 0) with hσ1
  have hvj : σ1.vars "vj" = arr.getD (2 + 2 * j) 0 := by simp [hσ1, Env.setVar]
  have hvp1 : σ1.vars "vp" = arr.getD (2 + 2 * p) 0 := by simp [hσ1, Env.setVar, hvpv]
  have hr1 : σ1.vars "r" = σ.vars "r" := by simp [hσ1, Env.setVar]
  have hp1 : σ1.vars "p" = p := by simp [hσ1, Env.setVar, hpv]
  have hj1 : σ1.vars "j" = j := by simp [hσ1, Env.setVar, hjv]
  have ha1 : σ1.arrs = σ.arrs := by simp [hσ1, Env.setVar]
  have ho1 : σ1.out = σ.out := by simp [hσ1, Env.setVar]
  have hfr1 : ∀ y, y ∉ AF → σ1.vars y = σ.vars y := by
    intro y hy
    have g1 : y ≠ "vj" := fun h => hy (by simp [AF, h])
    simp [hσ1, Env.setVar, g1]
  have c1 := cond_eqv (B := B) "vj" "vp" σ1 _ _ hvj hvp1 (by omega) (by omega)
  have c2 := cond_eqv (B := B) "r" "p" σ1 _ _ hr1 hp1 hrB (by omega)
  have rI : ∀ σ' : Env, σ'.vars "j" = j →
      Run B (.assign "j" (.bin .add (V "j") (.lit 1))) σ' (σ'.setVar "j" (j + 1)) 5 :=
    fun σ' hi' => by
      have r : Run B (.assign "j" (.bin .add (V "j") (.lit 1))) σ'
          (σ'.setVar "j" (σ'.vars "j" + 1)) (1 + (Expr.bin .add (V "j") (.lit 1)).size) :=
        Run.assign (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
      rw [hi'] at r
      exact r.mono (by simp [Expr.size])
  have hidx : idxA arr j = arr.getD (2 + 2 * j) 0 := rfl
  have hidxp : idxA arr p = arr.getD (2 + 2 * p) 0 := rfl
  by_cases hm : arr.getD (2 + 2 * j) 0 = arr.getD (2 + 2 * p) 0
  · have hT1 : (Cond.eq (V "vj") (V "vp")).evalB B σ1 = some true := by
      rw [c1, hm]; simp
    have hfo : fo (idxA arr) p ≤ j := fo_le_of_eq (idxA arr) p (by rw [hidx, hidxp, hm])
    by_cases hrp : σ.vars "r" = p
    · have hT2 : (Cond.eq (V "r") (V "p")).evalB B σ1 = some true := by
        rw [c2, hrp]; simp
      have hfoj : fo (idxA arr) p = j := by
        rw [hrv] at hrp
        by_contra hne
        have : fo (idxA arr) p < j := by omega
        rw [if_pos this] at hrp
        omega
      have s3 : Run B (.assign "r" (V "j")) σ1 (σ1.setVar "r" j) 2 := by
        have := Run.assign (B := B) (σ := σ1) (x := "r") (e := V "j") (v := j)
          (by have := evalB_var (B := B) (x := "j") (σ := σ1) (by omega); rwa [hj1] at this)
        exact this.mono (by simp [Expr.size])
      obtain ⟨hJ, hJi⟩ := finv_step arr p σ0 σ (σ1.setVar "r" j) hI' hlt
        (fun y hy => by
          have : y ≠ "r" := fun h => hy (by simp [AF, h])
          simp only [Env.setVar, if_neg this]; exact hfr1 y hy)
        (by simp [Env.setVar, ha1]) (by simp [Env.setVar, ho1]) (by simp [Env.setVar, hj1, hjdef])
        (by
          simp only [Env.setVar, if_true]
          rw [if_pos (by omega), hfoj])
      exact ⟨_, (s1.seq ((Run.ite_true hT1 (Run.ite_true hT2 s3)).seq
        (rI _ (by simp [Env.setVar, hj1])))).mono (by simp [Cond.size, Expr.size]), hJ, hJi⟩
    · have hF2 : (Cond.eq (V "r") (V "p")).evalB B σ1 = some false := by
        rw [c2]; simp only [beq_eq_false_iff_ne.mpr hrp]
      have hfoj : fo (idxA arr) p < j := by
        rw [hrv] at hrp
        by_contra hne
        rw [if_neg hne] at hrp
        exact hrp rfl
      obtain ⟨hJ, hJi⟩ := finv_step arr p σ0 σ σ1 hI' hlt hfr1 ha1 ho1 hj1
        (by rw [hr1, hrv, if_pos hfoj, if_pos (by omega)])
      exact ⟨_, (s1.seq ((Run.ite_true hT1 (Run.ite_false hF2 Run.skip)).seq
        (rI _ hj1))).mono (by simp [Cond.size, Expr.size]), hJ, hJi⟩
  · have hF1 : (Cond.eq (V "vj") (V "vp")).evalB B σ1 = some false := by
      rw [c1]; simp only [beq_eq_false_iff_ne.mpr hm]
    have hne : fo (idxA arr) p ≠ j := fun h => by
      have := idx_fo (idxA arr) p
      rw [h, hidx, hidxp] at this
      exact hm this
    obtain ⟨hJ, hJi⟩ := finv_step arr p σ0 σ σ1 hI' hlt hfr1 ha1 ho1 hj1
      (by
        rw [hr1, hrv]
        by_cases hlt' : fo (idxA arr) p < j
        · rw [if_pos hlt', if_pos (by omega)]
        · rw [if_neg hlt', if_neg (by omega)])
    exact ⟨_, (s1.seq ((Run.ite_false hF1 Run.skip).seq (rI _ hj1))).mono
      (by simp [Cond.size, Expr.size]), hJ, hJi⟩

/-- **The loop finds the first occurrence.** -/
theorem foLoop_spec (arr : List ℕ) (p : ℕ) (σ : Env)
    (hE : ∀ k ≤ p, arr.getD (2 + 2 * k) 0 + 8 < B)
    (hlen : 3 + 2 * p ≤ arr.length) (hpB : 2 * p + 16 < B)
    (hA : σ.arrs "TK" = arr) (hpv : σ.vars "p" = p)
    (hvp : σ.vars "vp" = arr.getD (2 + 2 * p) 0) (hr : σ.vars "r" = p) :
    ∃ σ', Run B foLoop σ σ' ((40 + 4) * p + 6) ∧
      σ'.vars "r" = fo (idxA arr) p ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ AF → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := foBody) "j" "p"
    (FInv arr p σ) p 40 (by omega) (fun _ h => h.hj) (fun _ h => h.hp)
    (foBody_spec arr p σ hE hlen hpB)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, by simp [Env.setVar, hpv],
      by simp [Env.setVar, hvp], by simp [Env.setVar], by
        simp [Env.setVar, hr], fun y hy => by
      have hyj : y ≠ "j" := fun h => hy (by simp [AF, h])
      simp [Env.setVar, hyj]⟩
  refine ⟨σ', r, ?_, hI.arrs.trans (by simp), hI.out.trans (by simp), ?_⟩
  · rw [hI.hr, hi]
    have := fo_le (idxA arr) p
    by_cases h : fo (idxA arr) p < p
    · rw [if_pos h]
    · rw [if_neg h]; omega
  · intro y hy
    rw [hI.fr y hy]

end Lax117284Proofs.Machine.TsRenFo
