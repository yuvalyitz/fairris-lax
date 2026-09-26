import Lax117284Proofs.Machine.TsRenLit
import Lax117284Proofs.Machine.SatCheck

/-!
The whole of the renaming reduction after the tokenizer has accepted: read the counts off the
array, check that every position names a variable of the formula, and write either the image
or the rejected word.
-/

namespace Lax117284Proofs.Machine.TsRenAccept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.SatOps
open Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.SatCheck (flag_fail flag_pass)
open Lax117284Proofs.Machine.TsRenFormat Lax117284Proofs.Machine.TsRenSem
open Lax117284Proofs.Machine.TsRenLit
open Lax117284Proofs.Machine.TsRenFo (bumpS)

variable {B : ℕ}

/-! ### The counts -/

/-- Read the counts off the array: the number of variables, the number of clauses, the number
of positions; and raise the flag. -/
def prepR : Com :=
  .seq (.assign "n" (.get "TK" (.lit 0)))
  (.seq (.assign "C" (.get "TK" (.lit 1)))
  (.seq (.assign "N" (.bin .mul (V "C") (.lit 2)))
    (.assign "ok" (.lit 1))))

/-- The scalars the preparation assigns. -/
def AP : List String := ["n", "C", "N", "ok"]

theorem prepR_run (arr : List ℕ) (σ : Env) (hA : σ.arrs "TK" = arr) (h2 : 2 ≤ arr.length)
    (hE : ∀ k < 2, arr.getD k 0 + 8 < B) (hN : 2 * arr.getD 1 0 + 8 < B) :
    ∃ σ', Run B prepR σ σ' 14 ∧ σ'.vars "n" = arr.getD 0 0 ∧ σ'.vars "C" = arr.getD 1 0 ∧
      σ'.vars "N" = PosN arr ∧ σ'.vars "ok" = 1 ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ AP → σ'.vars y = σ.vars y := by
  have e0 := hE 0 (by omega)
  have e1 := hE 1 (by omega)
  have s0 := asg_tkl (B := B) "n" 0 σ arr hA (by omega) (by omega) (by omega)
  set σ0 := σ.setVar "n" (arr.getD 0 0) with h0
  have A0 : σ0.arrs "TK" = arr := by simp [h0, Env.setVar, hA]
  have s1 := asg_tkl (B := B) "C" 1 σ0 arr A0 (by omega) (by omega) (by omega)
  set σ1 := σ0.setVar "C" (arr.getD 1 0) with h1
  have vC : σ1.vars "C" = arr.getD 1 0 := by simp [h1, Env.setVar]
  have s2 := asg_binr (B := B) .mul "C" 2 "N" σ1 (arr.getD 1 0) vC
    (by simp only [Bop.apply_mul]; omega) (by omega) (by omega)
  simp only [Bop.apply_mul] at s2
  set σ2 := σ1.setVar "N" (arr.getD 1 0 * 2) with h2'
  have s3 := asg_lit (B := B) "ok" 1 σ2 (by omega)
  refine ⟨_, (s0.seq (s1.seq (s2.seq s3))).mono (by omega), ?_, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_⟩
  · simp [h2', h1, h0, Env.setVar]
  · simp [h2', h1, Env.setVar]
  · simp [h2', Env.setVar, PosN]; omega
  · simp [Env.setVar]
  · simp [h2', h1, h0, Env.setVar]
  · simp [h2', h1, h0, Env.setVar]
  · have g1 : y ≠ "n" := fun h => hy (by simp [AP, h])
    have g2 : y ≠ "C" := fun h => hy (by simp [AP, h])
    have g3 : y ≠ "N" := fun h => hy (by simp [AP, h])
    have g4 : y ≠ "ok" := fun h => hy (by simp [AP, h])
    simp [h2', h1, h0, Env.setVar, g1, g2, g3, g4]

/-! ### The check -/

/-- The check of the position `i`: its variable is below the number of variables. -/
def chkBody : Com :=
  .seq (.assign "vp" (.get "TK" (add (.lit 2) (mul (.lit 2) (V "i")))))
  (.seq (.ite (.lt (V "vp") (V "n")) .skip (.assign "ok" (.lit 0)))
    (bumpS "i"))

def chkLoop : Com := .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "N")) chkBody)

/-- The scalars the pass assigns. -/
def AC : List String := ["vp", "ok", "i"]

structure CInv (arr : List ℕ) (S n ok0 : ℕ) (σ0 σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vN : σ.vars "N" = S
  vn : σ.vars "n" = n
  hi : σ.vars "i" ≤ S
  hok : σ.vars "ok" = flagTo (PassR arr) ok0 (σ.vars "i")
  fr : ∀ y, y ∉ AC → σ.vars y = σ0.vars y

lemma cinv_step (arr : List ℕ) (S n ok0 : ℕ) (σ0 σ σ' : Env) (hI : CInv arr S n ok0 σ0 σ)
    (hlt : σ.vars "i" < S) (hv : ∀ y, y ∉ AC → σ'.vars y = σ.vars y)
    (ha : σ'.arrs = σ.arrs) (ho : σ'.out = σ.out) (_hi : σ'.vars "i" = σ.vars "i")
    (hok : σ'.vars "ok" = flagTo (PassR arr) ok0 (σ.vars "i" + 1)) :
    CInv arr S n ok0 σ0 (σ'.setVar "i" (σ.vars "i" + 1)) ∧
      (σ'.setVar "i" (σ.vars "i" + 1)).vars "i" = σ.vars "i" + 1 := by
  have hsa := hI.arrs
  have hso := hI.out
  have hA0 := hI.hA
  have hNv := hI.vN
  have hnv := hI.vn
  have hfr := hI.fr
  clear hI
  refine ⟨⟨?_, ?_, hA0, ?_, ?_, ?_, ?_, fun y hy => ?_⟩, by simp [Env.setVar]⟩
  · simp only [Env.setVar]; rw [ha, hsa]
  · simp only [Env.setVar]; rw [ho, hso]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "N" (by simp [AC]), hNv]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "n" (by simp [AC]), hnv]
  · simp [Env.setVar]; omega
  · simp [Env.setVar, hok]
  · have hyi : y ≠ "i" := fun h => hy (by simp [AC, h])
    simp only [Env.setVar, if_neg hyi]
    rw [hv y hy, hfr y hy]

theorem chkBody_spec (arr : List ℕ) (S n ok0 : ℕ) (σ0 : Env) (hn : n = arr.getD 0 0)
    (hEv : ∀ k < S, arr.getD (2 + 2 * k) 0 + 8 < B) (hlen : 2 + 2 * S ≤ arr.length)
    (hSB : 2 * S + 16 < B) (hnB : n + 8 < B) (hok0 : ok0 ≤ 1) :
    Spec B (fun σ => CInv arr S n ok0 σ0 σ ∧ σ.vars "i" < S) chkBody
      (fun σ σ' => CInv arr S n ok0 σ0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 30 := by
  rintro σ ⟨hI, hlt⟩
  have hI' := hI
  obtain ⟨hsa, hso, hA0, hNv, hnv, hile, hokv, hfr⟩ := hI
  have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
  obtain ⟨k, hk⟩ : ∃ k, σ.vars "i" = k := ⟨_, rfl⟩
  rw [hk] at hlt hokv
  have e1 := hEv k hlt
  have s1 := asg_idx (B := B) "vp" 2 2 "i" σ arr k hA hk (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  set σ1 := σ.setVar "vp" (arr.getD (2 + 2 * k) 0) with hσ1
  have hvp1 : σ1.vars "vp" = arr.getD (2 + 2 * k) 0 := by simp [hσ1, Env.setVar]
  have hn1 : σ1.vars "n" = n := by simp [hσ1, Env.setVar, hnv]
  have hk1 : σ1.vars "i" = k := by simp [hσ1, Env.setVar, hk]
  have ha1 : σ1.arrs = σ.arrs := by simp [hσ1, Env.setVar]
  have ho1 : σ1.out = σ.out := by simp [hσ1, Env.setVar]
  have hfr1 : ∀ y, y ∉ AC → σ1.vars y = σ.vars y := by
    intro y hy
    have g1 : y ≠ "vp" := fun h => hy (by simp [AC, h])
    simp [hσ1, Env.setVar, g1]
  have c1 := cond_ltv (B := B) "vp" "n" σ1 _ _ hvp1 hn1 (by omega) (by omega)
  have rI : ∀ σ' : Env, σ'.vars "i" = k → Run B (bumpS "i") σ' (σ'.setVar "i" (k + 1)) 5 :=
    fun σ' hi' => by
      have r : Run B (.assign "i" (.bin .add (V "i") (.lit 1))) σ'
          (σ'.setVar "i" (σ'.vars "i" + 1)) (1 + (Expr.bin .add (V "i") (.lit 1)).size) :=
        Run.assign (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
      rw [hi'] at r
      exact r.mono (by simp [Expr.size])
  by_cases hp : arr.getD (2 + 2 * k) 0 < n
  · have hT : (Cond.lt (V "vp") (V "n")).evalB B σ1 = some true := by
      rw [c1]; exact congrArg some (decide_eq_true hp)
    have hpass : PassR arr k := by unfold PassR; rw [← hn]; exact hp
    obtain ⟨hJ, hJi⟩ := cinv_step arr S n ok0 σ0 σ σ1 hI' (by rw [hk]; exact hlt) hfr1 ha1 ho1
      (by rw [hk1, hk]) (by
        rw [hσ1]; simp only [Env.setVar, if_neg (by decide : "ok" ≠ "vp")]
        rw [hokv, hk, flag_pass (PassR arr) ok0 k hpass hok0])
    exact ⟨_, (s1.seq ((Run.ite_true hT Run.skip).seq (rI _ hk1))).mono
      (by simp [Cond.size, Expr.size]), by rw [hk] at hJ; exact hJ, by rw [hk] at hJi ⊢; exact hJi⟩
  · have hF : (Cond.lt (V "vp") (V "n")).evalB B σ1 = some false := by
      rw [c1]; exact congrArg some (decide_eq_false hp)
    have hfail : ¬ PassR arr k := fun h => hp (by unfold PassR at h; rwa [← hn] at h)
    have hrok : Run B (.assign "ok" (.lit 0)) σ1 (σ1.setVar "ok" 0) 2 :=
      (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
    have hi2 : (σ1.setVar "ok" 0).vars "i" = k := by simp [Env.setVar, hk1]
    obtain ⟨hJ, hJi⟩ := cinv_step arr S n ok0 σ0 σ (σ1.setVar "ok" 0) hI' (by rw [hk]; exact hlt)
      (fun y hy => by
        have hyo : y ≠ "ok" := fun h => hy (by simp [AC, h])
        simp only [Env.setVar, if_neg hyo]; exact hfr1 y hy)
      (by simp [Env.setVar, ha1]) (by simp [Env.setVar, ho1]) (by rw [hi2, hk])
      (by simp [Env.setVar, hk]; exact (flag_fail (PassR arr) ok0 _ hfail).symm)
    exact ⟨_, (s1.seq ((Run.ite_false hF hrok).seq (rI _ hi2))).mono
      (by simp [Cond.size, Expr.size]), by rw [hk] at hJ; exact hJ, by rw [hk] at hJi ⊢; exact hJi⟩

/-- **The pass.** -/
theorem chkLoop_run (arr : List ℕ) (S n ok0 : ℕ) (σ : Env) (hn : n = arr.getD 0 0)
    (hEv : ∀ k < S, arr.getD (2 + 2 * k) 0 + 8 < B) (hlen : 2 + 2 * S ≤ arr.length)
    (hSB : 2 * S + 16 < B) (hnB : n + 8 < B) (hok0 : ok0 ≤ 1)
    (hA : σ.arrs "TK" = arr) (hNv : σ.vars "N" = S) (hnv : σ.vars "n" = n)
    (hok : σ.vars "ok" = ok0) :
    ∃ σ', Run B chkLoop σ σ' ((30 + 4) * S + 6) ∧
      σ'.vars "ok" = flagTo (PassR arr) ok0 S ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ AC → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := chkBody) "i" "N"
    (CInv arr S n ok0 σ) S 30 (by omega) (fun _ h => h.hi) (fun _ h => h.vN)
    (chkBody_spec arr S n ok0 σ hn hEv hlen hSB hnB hok0)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, by simp [Env.setVar, hNv],
      by simp [Env.setVar, hnv], by simp [Env.setVar], by
        simp only [Env.setVar]
        simp [flagTo_zero (PassR arr) ok0 hok0, hok], fun y hy => by
      have hyi : y ≠ "i" := fun h => hy (by simp [AC, h])
      simp [Env.setVar, hyi]⟩
  refine ⟨σ', r, ?_, hI.arrs.trans (by simp), hI.out.trans (by simp), ?_⟩
  · rw [hI.hok, hi]
  · intro y hy
    rw [hI.fr y hy]

/-! ### The whole of the accepting phase -/

/-- Write the rejected word: one empty clause. -/
def rejR : Com := .seq (.write (.lit 1)) (.seq (.write (.lit 0)) (.write (.lit 0)))

theorem rejR_run (σ : Env) (hB : 2 < B) :
    ∃ σ', Run B rejR σ σ' 6 ∧ σ'.out = σ.out ++ [1, 0, 0] := by
  have w1 := write_bit (B := B) 1 (by omega) σ
  have w2 := write_bit (B := B) 0 (by omega) { σ with out := σ.out ++ [1] }
  have w3 := write_bit (B := B) 0 (by omega) { σ with out := σ.out ++ [1] ++ [0] }
  exact ⟨_, w1.seq (w2.seq w3), by simp⟩

/-- The whole of the reduction, after the tokenizer has accepted. -/
def acceptR : Com :=
  .seq prepR (.seq chkLoop (.ite (.eq (V "ok") (.lit 1)) printR rejR))

/-- The cost of the accepting phase, on an input of `l` tokens. -/
def KaccR (l : ℕ) : ℕ := 14 + ((30 + 4) * l + 6) + 4 + Kprint l l + 6

lemma Kprint_mono (S S' C C' : ℕ) (h1 : S ≤ S') (h2 : C ≤ C') :
    Kprint S C ≤ Kprint S' C' := by
  unfold Kprint Kcl Klit
  have : (2 + 4 + (2 + 12 + 2 + ((40 + 4) * S + 6) + (2 + ((6 + 4) * S + 6)) + 2 + 12 + 2) + 12 +
      (2 + 12 + 2 + ((40 + 4) * S + 6) + (2 + ((6 + 4) * S + 6)) + 2 + 12 + 2) + 2 + 10 + 4) * C ≤
      (2 + 4 + (2 + 12 + 2 + ((40 + 4) * S' + 6) + (2 + ((6 + 4) * S' + 6)) + 2 + 12 + 2) + 12 +
      (2 + 12 + 2 + ((40 + 4) * S' + 6) + (2 + ((6 + 4) * S' + 6)) + 2 + 12 + 2) + 2 + 10 + 4) * C' :=
    Nat.mul_le_mul (by omega) h2
  omega

lemma KaccR_mono (a b : ℕ) (h : a ≤ b) : KaccR a ≤ KaccR b := by
  unfold KaccR
  have := Kprint_mono a b a b h h
  omega

open scoped Classical in
/-- **The accepting phase.** -/
theorem acceptR_run (l : ℕ) (arr : List ℕ) (σ : Env) (hA : σ.arrs "TK" = arr)
    (hlen : 2 + 2 * PosN arr ≤ arr.length)
    (hE : ∀ k < 2 + 2 * PosN arr, arr.getD k 0 + 8 < B) (hl : PosN arr ≤ l)
    (hB : 2 * PosN arr + 20 < B) :
    ∃ σ', Run B acceptR σ σ' (KaccR l) ∧
      σ'.out = σ.out ++ (if CondR arr then outBits arr (arr.getD 1 0) else [1, 0, 0]) := by
  obtain ⟨S, hSdef⟩ : ∃ S, PosN arr = S := ⟨_, rfl⟩
  have hS2 : S = 2 * arr.getD 1 0 := by rw [← hSdef]; rfl
  rw [hSdef] at hlen hE hl hB
  have hn0 := hE 0 (by omega)
  have hn1 := hE 1 (by omega)
  obtain ⟨σ1, r1, e1n, e1C, e1N, e1ok, e1a, e1o, e1f⟩ :=
    prepR_run (B := B) arr σ hA (by omega) (fun k hk => hE k (by omega)) (by omega)
  rw [hSdef] at e1N
  have A1 : σ1.arrs "TK" = arr := by rw [e1a]; exact hA
  obtain ⟨σ2, r2, e2ok, e2a, e2o, e2f⟩ := chkLoop_run (B := B) arr S (arr.getD 0 0) 1 σ1 rfl
    (fun k hk => hE _ (by omega)) hlen (by omega) hn0 le_rfl A1 e1N e1n e1ok
  have A2 : σ2.arrs "TK" = arr := by rw [e2a]; exact A1
  have hC2 : σ2.vars "C" = arr.getD 1 0 := by rw [e2f "C" (by decide)]; exact e1C
  have hcond : σ2.vars "ok" = 1 ↔ CondR arr := by
    rw [e2ok, flagTo_eq_one]
    unfold CondR
    rw [hSdef]
    exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  have hokB : σ2.vars "ok" < B := by
    rw [e2ok]; have := flagTo_le (PassR arr) 1 S; omega
  have hb : Bnd B arr (2 * arr.getD 1 0) :=
    ⟨fun k hk => hE _ (by omega), fun k hk => hE _ (by omega), by omega, by omega⟩
  by_cases hok : σ2.vars "ok" = 1
  · have hc := hcond.1 hok
    have hcondT : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some true := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    obtain ⟨σ3, r3, o3⟩ := printR_run (B := B) arr (arr.getD 1 0) σ2 hb A2 hC2 (by omega)
    have hK := Kprint_mono (2 * arr.getD 1 0) l (arr.getD 1 0) l (by omega) (by omega)
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_true hcondT r3))).mono ?_, ?_⟩
    · unfold KaccR
      have h1 : (30 + 4) * S ≤ (30 + 4) * l := Nat.mul_le_mul_left _ hl
      simp only [Cond.size, Expr.size]
      omega
    · rw [o3, e2o, e1o, if_pos hc]
  · have hno : ¬ CondR arr := fun h => hok (hcond.2 h)
    have hcondF : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some false := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    obtain ⟨σ3, r3, o3⟩ := rejR_run (B := B) σ2 (by omega)
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_false hcondF r3))).mono ?_, ?_⟩
    · unfold KaccR
      have h1 : (30 + 4) * S ≤ (30 + 4) * l := Nat.mul_le_mul_left _ hl
      simp only [Cond.size, Expr.size]
      omega
    · rw [o3, e2o, e1o, if_neg hno]

end Lax117284Proofs.Machine.TsRenAccept
