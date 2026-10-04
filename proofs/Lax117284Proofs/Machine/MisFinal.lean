import Lax117284Proofs.Machine.SatOps
import Lax117284Proofs.Machine.SatRank
import Lax117284Proofs.Machine.MisSem
import Lax117284Proofs.Machine.Flag
import Lax117284Proofs.Machine.MisBlk
import Lax117284Proofs.Machine.Emit
import Lax117284Proofs.Machine.FreeAccept
import Lax117284Proofs.Machine.MisNk
import Lax117284Proofs.Machine.WrapTFinal

/-! ### `Lax117284Proofs.Machine.MisCount` -/

section
/-!
Counting the ones in a run of the array: a loop over `bd` consecutive entries starting at `bs`. The
number of neighbours of a vertex, and the position of a neighbour among them, are such counts.
-/

namespace Lax117284Proofs.Machine.MisCount

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.SatOps
open Lax117284Proofs.Machine.SatRank (bumpS countP_range_succ)

variable {B : ℕ}

/-- The entry at `bs + j` is one. -/
def onePred (arr : List ℕ) (bs j : ℕ) : Bool := decide (arr.getD (bs + j) 0 = 1)

/-- The body of the loop. -/
def cntBody : Com :=
  .seq (.assign "xj" (.get "TK" (.bin .add (V "bs") (V "j"))))
  (.seq (.ite (.eq (V "xj") (.lit 1)) (bumpS "cnt") .skip) (bumpS "j"))

def cntLoop : Com := .seq (.assign "j" (.lit 0)) (.while (.lt (V "j") (V "bd")) cntBody)

/-- Count the ones among the `bd` entries from `bs`. -/
def cntCom : Com := .seq (.assign "cnt" (.lit 0)) cntLoop

/-- The scalars the loop assigns. -/
def AN : List String := ["j", "xj", "cnt"]

structure NInv (arr : List ℕ) (bs bd : ℕ) (σ0 σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vbs : σ.vars "bs" = bs
  vbd : σ.vars "bd" = bd
  hj : σ.vars "j" ≤ bd
  hc : σ.vars "cnt" = (List.range (σ.vars "j")).countP (onePred arr bs)
  fr : ∀ y, y ∉ AN → σ.vars y = σ0.vars y

lemma ninv_step (arr : List ℕ) (bs bd : ℕ) (σ0 σ σ' : Env) (hI : NInv arr bs bd σ0 σ)
    (hlt : σ.vars "j" < bd) (hv : ∀ y, y ∉ AN → σ'.vars y = σ.vars y)
    (ha : σ'.arrs = σ.arrs) (ho : σ'.out = σ.out) (hj : σ'.vars "j" = σ.vars "j")
    (hcnt : σ'.vars "cnt" = (List.range (σ.vars "j" + 1)).countP (onePred arr bs)) :
    NInv arr bs bd σ0 (σ'.setVar "j" (σ.vars "j" + 1)) ∧
      (σ'.setVar "j" (σ.vars "j" + 1)).vars "j" = σ.vars "j" + 1 := by
  have hsa := hI.arrs
  have hso := hI.out
  have hA0 := hI.hA
  have hbs := hI.vbs
  have hbd := hI.vbd
  have hjle := hI.hj
  have hc := hI.hc
  have hfr := hI.fr
  clear hI
  refine ⟨⟨?_, ?_, hA0, ?_, ?_, ?_, ?_, fun y hy => ?_⟩, by simp [Env.setVar]⟩
  · simp only [Env.setVar]; rw [ha, hsa]
  · simp only [Env.setVar]; rw [ho, hso]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "bs" (by simp [AN]), hbs]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "bd" (by simp [AN]), hbd]
  · simp [Env.setVar]; omega
  · simp only [Env.setVar]; rw [if_neg (by decide), if_true, hcnt]
  · have hyj : y ≠ "j" := fun h => hy (by simp [AN, h])
    simp only [Env.setVar, if_neg hyj]
    rw [hv y hy, hfr y hy]

set_option maxHeartbeats 1600000 in
theorem cntBody_spec (arr : List ℕ) (bs bd : ℕ) (σ0 : Env)
    (hE : ∀ k < bd, arr.getD (bs + k) 0 + 8 < B) (hlen : bs + bd ≤ arr.length)
    (hB : bs + bd + 16 < B) :
    Spec B (fun σ => NInv arr bs bd σ0 σ ∧ σ.vars "j" < bd) cntBody
      (fun σ σ' => NInv arr bs bd σ0 σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 40 := by
  rintro σ ⟨hI, hlt⟩
  have hI' := hI
  obtain ⟨hsa, hso, hA0, hbs, hbd, hjle, hc, hfr⟩ := hI
  have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
  obtain ⟨j, hjv⟩ : ∃ j, σ.vars "j" = j := ⟨_, rfl⟩
  rw [hjv] at hlt hc
  have hcnt_le : (List.range j).countP (onePred arr bs) ≤ j := by
    have := List.countP_le_length (p := onePred arr bs) (l := List.range j)
    simpa using this
  have hcB : σ.vars "cnt" < B := by rw [hc]; omega
  have e1 := hE j hlt
  have hidx : (V "bs" : Expr).evalB B σ = some bs := by
    have := evalB_var (B := B) (x := "bs") (σ := σ) (by omega)
    rwa [hbs] at this
  have hidj : (V "j" : Expr).evalB B σ = some j := by
    have := evalB_var (B := B) (x := "j") (σ := σ) (by omega)
    rwa [hjv] at this
  have hsum : (Expr.bin .add (V "bs") (V "j")).evalB B σ = some (bs + j) :=
    evalB_bin hidx hidj (by simp; omega)
  have hget := RunStep.eval_get B σ "TK" (Expr.bin .add (V "bs") (V "j")) (bs + j) hsum
    (by rw [hA]; omega) (by rw [hA]; omega)
  rw [hA] at hget
  have s1 : Run B (.assign "xj" (.get "TK" (.bin .add (V "bs") (V "j")))) σ
      (σ.setVar "xj" (arr.getD (bs + j) 0)) (1 + (Expr.get "TK" (Expr.bin .add (V "bs") (V "j"))).size) :=
    Run.assign hget
  set σ1 := σ.setVar "xj" (arr.getD (bs + j) 0) with hσ1
  have hxj : σ1.vars "xj" = arr.getD (bs + j) 0 := by simp [hσ1, Env.setVar]
  have hj1 : σ1.vars "j" = j := by simp [hσ1, Env.setVar, hjv]
  have hcn1 : σ1.vars "cnt" = σ.vars "cnt" := by simp [hσ1, Env.setVar]
  have ha1 : σ1.arrs = σ.arrs := by simp [hσ1, Env.setVar]
  have ho1 : σ1.out = σ.out := by simp [hσ1, Env.setVar]
  have hfr1 : ∀ y, y ∉ AN → σ1.vars y = σ.vars y := by
    intro y hy
    have g1 : y ≠ "xj" := fun h => hy (by simp [AN, h])
    simp [hσ1, Env.setVar, g1]
  have c1 := cond_eql (B := B) "xj" 1 σ1 _ hxj (by omega) (by omega)
  have rI : ∀ σ' : Env, σ'.vars "j" = j →
      Run B (bumpS "j") σ' (σ'.setVar "j" (j + 1)) 5 :=
    fun σ' hi' => by
      have r : Run B (.assign "j" (.bin .add (V "j") (.lit 1))) σ'
          (σ'.setVar "j" (σ'.vars "j" + 1)) (1 + (Expr.bin .add (V "j") (.lit 1)).size) :=
        Run.assign (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
      rw [hi'] at r
      exact r.mono (by simp [Expr.size])
  have hpj : ∀ b : Bool, onePred arr bs j = b → True := fun _ _ => trivial
  by_cases hone : arr.getD (bs + j) 0 = 1
  · have hT : (Cond.eq (V "xj") (.lit 1)).evalB B σ1 = some true := by
      rw [c1, hone]; simp
    have hp1 : onePred arr bs j = true := decide_eq_true hone
    have s3 := asg_addl (B := B) "cnt" "cnt" 1 σ1 (σ.vars "cnt") (by rw [hcn1]) (by omega)
      (by omega) (by omega)
    have s3' : Run B (bumpS "cnt") σ1 (σ1.setVar "cnt" (σ.vars "cnt" + 1)) 5 := s3
    obtain ⟨hJ, hJi⟩ := ninv_step arr bs bd σ0 σ (σ1.setVar "cnt" (σ.vars "cnt" + 1)) hI' (by rw [hjv]; exact hlt)
      (fun y hy => by
        have : y ≠ "cnt" := fun h => hy (by simp [AN, h])
        simp only [Env.setVar, if_neg this]; exact hfr1 y hy)
      (by simp [Env.setVar, ha1]) (by simp [Env.setVar, ho1]) (by simp [Env.setVar, hj1, hjv])
      (by
        simp only [Env.setVar, if_true]
        rw [hjv, countP_range_succ, hp1, ← hc]
        simp)
    exact ⟨_, (s1.seq ((Run.ite_true hT s3').seq (rI _ (by simp [Env.setVar, hj1])))).mono
      (by simp [Cond.size, Expr.size]), by rw [hjv] at hJ; exact hJ, by
        rw [hjv] at hJi ⊢; exact hJi⟩
  · have hF : (Cond.eq (V "xj") (.lit 1)).evalB B σ1 = some false := by
      rw [c1]; simp only [beq_eq_false_iff_ne.mpr hone]
    have hp0 : onePred arr bs j = false := decide_eq_false hone
    obtain ⟨hJ, hJi⟩ := ninv_step arr bs bd σ0 σ σ1 hI' (by rw [hjv]; exact hlt) hfr1 ha1 ho1
      (by rw [hj1, hjv])
      (by rw [hcn1, hjv, countP_range_succ, hp0, ← hc]; simp)
    exact ⟨_, (s1.seq ((Run.ite_false hF Run.skip).seq (rI _ hj1))).mono
      (by simp [Cond.size, Expr.size]), by rw [hjv] at hJ; exact hJ, by
        rw [hjv] at hJi ⊢; exact hJi⟩

/-- **The loop counts.** -/
theorem cntLoop_spec (arr : List ℕ) (bs bd : ℕ) (σ : Env)
    (hE : ∀ k < bd, arr.getD (bs + k) 0 + 8 < B) (hlen : bs + bd ≤ arr.length)
    (hB : bs + bd + 16 < B) (hA : σ.arrs "TK" = arr) (hbs : σ.vars "bs" = bs)
    (hbd : σ.vars "bd" = bd) (hcn : σ.vars "cnt" = 0) :
    ∃ σ', Run B cntLoop σ σ' ((40 + 4) * bd + 6) ∧
      σ'.vars "cnt" = (List.range bd).countP (onePred arr bs) ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ AN → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := cntBody) "j" "bd"
    (NInv arr bs bd σ) bd 40 (by omega) (fun _ h => h.hj) (fun _ h => h.vbd)
    (cntBody_spec arr bs bd σ hE hlen hB)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, by simp [Env.setVar, hbs],
      by simp [Env.setVar, hbd], by simp [Env.setVar], by
        simp [Env.setVar, hcn], fun y hy => by
      have hyj : y ≠ "j" := fun h => hy (by simp [AN, h])
      simp [Env.setVar, hyj]⟩
  refine ⟨σ', r, ?_, hI.arrs.trans (by simp [Env.setVar]), hI.out.trans (by simp [Env.setVar]), ?_⟩
  · rw [hI.hc, hi]
  · intro y hy
    rw [hI.fr y hy]

/-- **The count of the ones in a run.** -/
theorem cntCom_run (arr : List ℕ) (bs bd : ℕ) (σ : Env)
    (hE : ∀ k < bd, arr.getD (bs + k) 0 + 8 < B) (hlen : bs + bd ≤ arr.length)
    (hB : bs + bd + 16 < B) (hA : σ.arrs "TK" = arr) (hbs : σ.vars "bs" = bs)
    (hbd : σ.vars "bd" = bd) :
    ∃ σ', Run B cntCom σ σ' ((40 + 4) * bd + 20) ∧
      σ'.vars "cnt" = (List.range bd).countP (onePred arr bs) ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ AN → σ'.vars y = σ.vars y := by
  have s0 := asg_lit (B := B) "cnt" 0 σ (by omega)
  obtain ⟨σ', r, c, a, o, f⟩ := cntLoop_spec (B := B) arr bs bd (σ.setVar "cnt" 0) hE hlen hB
    (by simp [Env.setVar, hA]) (by simp [Env.setVar, hbs]) (by simp [Env.setVar, hbd])
    (by simp [Env.setVar])
  refine ⟨σ', (s0.seq r).mono (by omega), c, a.trans (by simp [Env.setVar]),
    o.trans (by simp [Env.setVar]), fun y hy => ?_⟩
  rw [f y hy]
  have : y ≠ "cnt" := fun h => hy (by simp [AN, h])
  simp [Env.setVar, this]

end Lax117284Proofs.Machine.MisCount

end

/-! ### `Lax117284Proofs.Machine.MisFind` -/

section
/-!
The endpoints of the `e`-th edge: a scan over the cells of the matrix that counts the entries that
are edges from a smaller number to a larger, and remembers the endpoints of the one that is `e`-th.
-/

namespace Lax117284Proofs.Machine.MisFind

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.SatOps
open Lax117284Proofs.Machine.SatRank (bumpS countP_range_succ)
open Lax117284Proofs.Machine.MisSem
open Lax117284Proofs.Machine.MisFormat (VM)

variable {B : ℕ}

/-- The cell `t` is the entry of an edge from a smaller number to a larger, `V` being the number of
vertices. -/
def qualV (arr : List ℕ) (V t : ℕ) : Bool :=
  decide (arr.getD (2 + t) 0 = 1 ∧ t / V < t % V)

/-- The body of the scan. -/
def findBody : Com :=
  .seq (.assign "xf" (.get "TK" (add (.lit 2) (mul (.lit 1) (V "j")))))
  (.seq (.assign "fq" (.bin .div (V "j") (V "V")))
  (.seq (.assign "fm" (.bin .mul (V "fq") (V "V")))
  (.seq (.assign "fr" (.bin .sub (V "j") (V "fm")))
  (.seq (.ite (.eq (V "xf") (.lit 1))
      (.ite (.lt (V "fq") (V "fr"))
        (.seq (.ite (.eq (V "cnt") (V "e"))
            (.seq (.assign "fw" (V "fq")) (.assign "fw2" (V "fr"))) .skip)
          (bumpS "cnt"))
        .skip)
      .skip)
    (bumpS "j")))))

def findLoop : Com := .seq (.assign "j" (.lit 0)) (.while (.lt (V "j") (V "VV")) findBody)

/-- Look for the `e`-th edge. -/
def findCom : Com :=
  .seq (.assign "fw" (.lit 0)) (.seq (.assign "fw2" (.lit 0)) (.seq (.assign "cnt" (.lit 0)) findLoop))

/-- The scalars the scan assigns. -/
def AF : List String := ["j", "xf", "fq", "fm", "fr", "fw", "fw2", "cnt"]

/-- The cell of the `e`-th edge among the first `j` cells, or `0`. -/
def edgeCellAt (arr : List ℕ) (V e j : ℕ) : ℕ :=
  ((List.range j).filter (qualV arr V)).getD e 0

structure FInv (arr : List ℕ) (V VV e : ℕ) (σ0 σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vV : σ.vars "V" = V
  vVV : σ.vars "VV" = VV
  ve : σ.vars "e" = e
  hj : σ.vars "j" ≤ VV
  hc : σ.vars "cnt" = (List.range (σ.vars "j")).countP (qualV arr V)
  hw : σ.vars "fw" = edgeCellAt arr V e (σ.vars "j") / V
  hw2 : σ.vars "fw2" = edgeCellAt arr V e (σ.vars "j") % V
  fr : ∀ y, y ∉ AF → σ.vars y = σ0.vars y

lemma getD_snoc (l : List ℕ) (j e : ℕ) :
    (l ++ [j]).getD e 0 = if l.length = e then j else l.getD e 0 := by
  by_cases h1 : e < l.length
  · rw [List.getD_append _ _ _ _ h1, if_neg (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default _ _ (by omega : l.length ≤ e)]
    by_cases h2 : l.length = e
    · rw [if_pos h2]
      have : e - l.length = 0 := by omega
      rw [this]; rfl
    · rw [if_neg h2]
      have : e - l.length = (e - l.length - 1) + 1 := by omega
      rw [this]; simp

lemma edgeCellAt_succ (arr : List ℕ) (V e j : ℕ) :
    edgeCellAt arr V e (j + 1) = if qualV arr V j = true then
      (if ((List.range j).countP (qualV arr V)) = e then j else edgeCellAt arr V e j)
      else edgeCellAt arr V e j := by
  unfold edgeCellAt
  rw [List.range_succ, List.filter_append]
  by_cases h : qualV arr V j = true
  · rw [List.filter_cons_of_pos (by simpa using h), List.filter_nil, if_pos h, getD_snoc,
      List.countP_eq_length_filter]
  · rw [List.filter_cons_of_neg (by simpa using h), List.filter_nil, if_neg h]
    simp

lemma finv_step (arr : List ℕ) (V VV e : ℕ) (σ0 σ σ' : Env) (hI : FInv arr V VV e σ0 σ)
    (hlt : σ.vars "j" < VV) (hv : ∀ y, y ∉ AF → σ'.vars y = σ.vars y)
    (ha : σ'.arrs = σ.arrs) (ho : σ'.out = σ.out) (hj : σ'.vars "j" = σ.vars "j")
    (hcnt : σ'.vars "cnt" = (List.range (σ.vars "j" + 1)).countP (qualV arr V))
    (hw : σ'.vars "fw" = edgeCellAt arr V e (σ.vars "j" + 1) / V)
    (hw2 : σ'.vars "fw2" = edgeCellAt arr V e (σ.vars "j" + 1) % V) :
    FInv arr V VV e σ0 (σ'.setVar "j" (σ.vars "j" + 1)) ∧
      (σ'.setVar "j" (σ.vars "j" + 1)).vars "j" = σ.vars "j" + 1 := by
  have hsa := hI.arrs
  have hso := hI.out
  have hA0 := hI.hA
  have hVv := hI.vV
  have hVVv := hI.vVV
  have hev := hI.ve
  have hjle := hI.hj
  have hc := hI.hc
  have hw0 := hI.hw
  have hw20 := hI.hw2
  have hfr := hI.fr
  clear hI
  refine ⟨⟨?_, ?_, hA0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_⟩, by simp [Env.setVar]⟩
  · simp only [Env.setVar]; rw [ha, hsa]
  · simp only [Env.setVar]; rw [ho, hso]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "V" (by simp [AF]), hVv]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "VV" (by simp [AF]), hVVv]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "e" (by simp [AF]), hev]
  · simp [Env.setVar]; omega
  · simp only [Env.setVar]; rw [if_neg (by decide), if_true, hcnt]
  · simp only [Env.setVar]; rw [if_neg (by decide), if_true, hw]
  · simp only [Env.setVar]; rw [if_neg (by decide), if_true, hw2]
  · have hyj : y ≠ "j" := fun h => hy (by simp [AF, h])
    simp only [Env.setVar, if_neg hyj]
    rw [hv y hy, hfr y hy]

lemma mod_eq_sub (j V : ℕ) : j - j / V * V = j % V := by
  have := Nat.div_add_mod j V
  rw [Nat.mul_comm] at this
  omega

/-- An assignment of a scalar to a scalar. -/
theorem asg_var (z x : String) (σ : Env) (a : ℕ) (hx : σ.vars x = a) (ha : a < B) :
    Run B (.assign z (V x)) σ (σ.setVar z a) 3 := by
  have := evalB_var (B := B) (x := x) (σ := σ) (by omega)
  rw [hx] at this
  exact (Run.assign this).mono (by simp [Expr.size])

set_option maxHeartbeats 6400000 in
theorem findBody_spec (arr : List ℕ) (Vn VV e : ℕ) (σ0 : Env)
    (hE : ∀ k < VV, arr.getD (2 + k) 0 + 8 < B) (hlen : 2 + VV ≤ arr.length)
    (hB : VV + Vn + e + 16 < B) :
    Spec B (fun σ => FInv arr Vn VV e σ0 σ ∧ σ.vars "j" < VV) findBody
      (fun σ σ' => FInv arr Vn VV e σ0 σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 80 := by
  rintro σ ⟨hI, hlt⟩
  have hI' := hI
  obtain ⟨hsa, hso, hA0, hVv, hVVv, hev, hjle, hc, hw0, hw20, hfr⟩ := hI
  have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
  obtain ⟨j, hjv⟩ : ∃ j, σ.vars "j" = j := ⟨_, rfl⟩
  rw [hjv] at hlt hc hw0 hw20
  have hcnt_le : (List.range j).countP (qualV arr Vn) ≤ j := by
    have := List.countP_le_length (p := qualV arr Vn) (l := List.range j)
    simpa using this
  have hcB : σ.vars "cnt" < B := by rw [hc]; omega
  have e1 := hE j hlt
  have hdiv : j / Vn ≤ j := Nat.div_le_self _ _
  have hmul : j / Vn * Vn ≤ j := by
    rcases Nat.eq_zero_or_pos Vn with h | h
    · subst h; simp
    · exact Nat.div_mul_le_self _ _
  have s1 := asg_idx (B := B) "xf" 2 1 "j" σ arr j hA hjv (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by rw [Nat.one_mul]; omega)
  simp only [Nat.one_mul] at s1
  set σ1 := σ.setVar "xf" (arr.getD (2 + j) 0) with hσ1
  have hj1 : σ1.vars "j" = j := by simp [hσ1, Env.setVar, hjv]
  have hV1 : σ1.vars "V" = Vn := by simp [hσ1, Env.setVar, hVv]
  have s2 := asg_bin (B := B) .div "j" "V" "fq" σ1 j Vn hj1 hV1
    (by simp only [Bop.apply_div]; omega) (by omega) (by omega)
  simp only [Bop.apply_div] at s2
  set σ2 := σ1.setVar "fq" (j / Vn) with hσ2
  have hq2 : σ2.vars "fq" = j / Vn := by simp [hσ2, Env.setVar]
  have hV2 : σ2.vars "V" = Vn := by simp [hσ2, hσ1, Env.setVar, hVv]
  have s3 := asg_bin (B := B) .mul "fq" "V" "fm" σ2 (j / Vn) Vn hq2 hV2
    (by simp only [Bop.apply_mul]; omega) (by omega) (by omega)
  simp only [Bop.apply_mul] at s3
  set σ3 := σ2.setVar "fm" (j / Vn * Vn) with hσ3
  have hj3 : σ3.vars "j" = j := by simp [hσ3, hσ2, hσ1, Env.setVar, hjv]
  have hm3 : σ3.vars "fm" = j / Vn * Vn := by simp [hσ3, Env.setVar]
  have s4 := asg_bin (B := B) .sub "j" "fm" "fr" σ3 j (j / Vn * Vn) hj3 hm3
    (by simp only [Bop.apply_sub]; omega) (by omega) (by omega)
  simp only [Bop.apply_sub] at s4
  set σ4 := σ3.setVar "fr" (j - j / Vn * Vn) with hσ4
  have hx4 : σ4.vars "xf" = arr.getD (2 + j) 0 := by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have hq4 : σ4.vars "fq" = j / Vn := by simp [hσ4, hσ3, hσ2, Env.setVar]
  have hr4 : σ4.vars "fr" = j - j / Vn * Vn := by simp [hσ4, Env.setVar]
  have hcn4 : σ4.vars "cnt" = σ.vars "cnt" := by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have hj4 : σ4.vars "j" = j := by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, hjv]
  have he4 : σ4.vars "e" = e := by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, hev]
  have hw4 : σ4.vars "fw" = σ.vars "fw" := by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have hw24 : σ4.vars "fw2" = σ.vars "fw2" := by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have ha4 : σ4.arrs = σ.arrs := by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have ho4 : σ4.out = σ.out := by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have hfr4 : ∀ y, y ∉ AF → σ4.vars y = σ.vars y := by
    intro y hy
    have g1 : y ≠ "xf" := fun h => hy (by simp [AF, h])
    have g2 : y ≠ "fq" := fun h => hy (by simp [AF, h])
    have g3 : y ≠ "fm" := fun h => hy (by simp [AF, h])
    have g4 : y ≠ "fr" := fun h => hy (by simp [AF, h])
    simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, g1, g2, g3, g4]
  have hmr : j - j / Vn * Vn = j % Vn := mod_eq_sub j Vn
  have c1 := cond_eql (B := B) "xf" 1 σ4 _ hx4 (by omega) (by omega)
  have c2 := cond_ltv (B := B) "fq" "fr" σ4 _ _ hq4 hr4 (by omega) (by omega)
  have rI : ∀ σ' : Env, σ'.vars "j" = j →
      Run B (bumpS "j") σ' (σ'.setVar "j" (j + 1)) 5 :=
    fun σ' hi' => by
      have r : Run B (.assign "j" (.bin .add (V "j") (.lit 1))) σ'
          (σ'.setVar "j" (σ'.vars "j" + 1)) (1 + (Expr.bin .add (V "j") (.lit 1)).size) :=
        Run.assign (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
      rw [hi'] at r
      exact r.mono (by simp [Expr.size])
  have hsucc := edgeCellAt_succ arr Vn e j
  have hcs := countP_range_succ (qualV arr Vn) j
  -- the frame of a state that only changes the listed scalars
  have hqual : qualV arr Vn j = decide (arr.getD (2 + j) 0 = 1 ∧ j / Vn < j % Vn) := rfl
  have hnq : ∀ (σ' : Env), σ'.vars "cnt" = σ.vars "cnt" → σ'.vars "fw" = σ.vars "fw" →
      σ'.vars "fw2" = σ.vars "fw2" → σ'.arrs = σ.arrs → σ'.out = σ.out →
      (∀ y, y ∉ AF → σ'.vars y = σ.vars y) → σ'.vars "j" = j → qualV arr Vn j = false →
      FInv arr Vn VV e σ0 (σ'.setVar "j" (j + 1)) ∧
        (σ'.setVar "j" (j + 1)).vars "j" = j + 1 := by
    intro σ' hc' hw' hw2' ha' ho' hf' hj' hq
    have := finv_step arr Vn VV e σ0 σ σ' hI' (by rw [hjv]; exact hlt) hf' ha' ho'
      (by rw [hj', hjv]) (by rw [hc', hjv, hcs, hq, ← hc]; simp)
      (by rw [hw', hjv, hsucc, if_neg (by simp [hq]), hw0])
      (by rw [hw2', hjv, hsucc, if_neg (by simp [hq]), hw20])
    rw [hjv] at this
    exact this
  by_cases hx1 : arr.getD (2 + j) 0 = 1
  · have hT1 : (Cond.eq (V "xf") (.lit 1)).evalB B σ4 = some true := by rw [c1, hx1]; simp
    by_cases hlt2 : j / Vn < j % Vn
    · have hT2 : (Cond.lt (V "fq") (V "fr")).evalB B σ4 = some true := by
        rw [c2]; exact congrArg some (decide_eq_true (by rw [hmr]; exact hlt2))
      have hq : qualV arr Vn j = true := by rw [hqual]; exact decide_eq_true ⟨hx1, hlt2⟩
      have c3 := cond_eqv (B := B) "cnt" "e" σ4 _ _ hcn4 he4 (by omega) (by omega)
      by_cases hce : σ.vars "cnt" = e
      · have hT3 : (Cond.eq (V "cnt") (V "e")).evalB B σ4 = some true := by
          rw [c3, hce]; simp
        have hcnt_e : (List.range j).countP (qualV arr Vn) = e := by rw [← hc]; exact hce
        have s5 := asg_var (B := B) "fw" "fq" σ4 (j / Vn) hq4 (by omega)
        set σ5 := σ4.setVar "fw" (j / Vn) with hσ5
        have hr5 : σ5.vars "fr" = j - j / Vn * Vn := by simp [hσ5, Env.setVar, hr4]
        have s6 := asg_var (B := B) "fw2" "fr" σ5 (j - j / Vn * Vn) hr5 (by omega)
        set σ6 := σ5.setVar "fw2" (j - j / Vn * Vn) with hσ6
        have hcn6 : σ6.vars "cnt" = σ.vars "cnt" := by simp [hσ6, hσ5, Env.setVar, hcn4]
        have s7 := asg_addl (B := B) "cnt" "cnt" 1 σ6 (σ.vars "cnt") hcn6 (by omega) (by omega)
          (by omega)
        have s7' : Run B (bumpS "cnt") σ6 (σ6.setVar "cnt" (σ.vars "cnt" + 1)) 5 := s7
        have hfin : ∀ y, y ∉ AF → ((σ6.setVar "cnt" (σ.vars "cnt" + 1))).vars y = σ.vars y := by
          intro y hy
          have g1 : y ≠ "fw" := fun h => hy (by simp [AF, h])
          have g2 : y ≠ "fw2" := fun h => hy (by simp [AF, h])
          have g3 : y ≠ "cnt" := fun h => hy (by simp [AF, h])
          simp only [Env.setVar, hσ6, hσ5, if_neg g1, if_neg g2, if_neg g3]
          exact hfr4 y hy
        have hj6 : (σ6.setVar "cnt" (σ.vars "cnt" + 1)).vars "j" = j := by
          simp [Env.setVar, hσ6, hσ5, hj4]
        obtain ⟨hJ, hJi⟩ := finv_step arr Vn VV e σ0 σ (σ6.setVar "cnt" (σ.vars "cnt" + 1)) hI'
          (by rw [hjv]; exact hlt) hfin (by simp [Env.setVar, hσ6, hσ5, ha4])
          (by simp [Env.setVar, hσ6, hσ5, ho4]) (by rw [hj6, hjv])
          (by
            simp only [Env.setVar, if_true]
            rw [hjv, hcs, hq, ← hc]; simp)
          (by
            simp only [Env.setVar, hσ6, hσ5, if_neg (show ("fw" ≠ "cnt") by decide),
              if_neg (show ("fw" ≠ "fw2") by decide), if_true]
            rw [hjv, hsucc, if_pos hq, if_pos hcnt_e])
          (by
            simp only [Env.setVar, hσ6, hσ5, if_neg (show ("fw2" ≠ "cnt") by decide), if_true]
            rw [hjv, hsucc, if_pos hq, if_pos hcnt_e, hmr])
        exact ⟨_, (s1.seq (s2.seq (s3.seq (s4.seq ((Run.ite_true hT1 (Run.ite_true hT2
          ((Run.ite_true hT3 (s5.seq s6)).seq s7'))).seq (rI _ hj6)))))).mono
          (by simp [Cond.size, Expr.size]), by rw [hjv] at hJ; exact hJ, by
            rw [hjv] at hJi ⊢; exact hJi⟩
      · have hF3 : (Cond.eq (V "cnt") (V "e")).evalB B σ4 = some false := by
          rw [c3]; simp only [beq_eq_false_iff_ne.mpr hce]
        have hcnt_e : ¬ (List.range j).countP (qualV arr Vn) = e := by rw [← hc]; exact hce
        have s7 := asg_addl (B := B) "cnt" "cnt" 1 σ4 (σ.vars "cnt") hcn4 (by omega) (by omega)
          (by omega)
        have s7' : Run B (bumpS "cnt") σ4 (σ4.setVar "cnt" (σ.vars "cnt" + 1)) 5 := s7
        have hfin : ∀ y, y ∉ AF → ((σ4.setVar "cnt" (σ.vars "cnt" + 1))).vars y = σ.vars y := by
          intro y hy
          have g3 : y ≠ "cnt" := fun h => hy (by simp [AF, h])
          simp only [Env.setVar, if_neg g3]
          exact hfr4 y hy
        have hj6 : (σ4.setVar "cnt" (σ.vars "cnt" + 1)).vars "j" = j := by
          simp [Env.setVar, hj4]
        obtain ⟨hJ, hJi⟩ := finv_step arr Vn VV e σ0 σ (σ4.setVar "cnt" (σ.vars "cnt" + 1)) hI'
          (by rw [hjv]; exact hlt) hfin (by simp [Env.setVar, ha4])
          (by simp [Env.setVar, ho4]) (by rw [hj6, hjv])
          (by
            simp only [Env.setVar, if_true]
            rw [hjv, hcs, hq, ← hc]; simp)
          (by
            simp only [Env.setVar, if_neg (show ("fw" ≠ "cnt") by decide)]
            rw [hw4, hjv, hsucc, if_pos hq, if_neg hcnt_e, hw0])
          (by
            simp only [Env.setVar, if_neg (show ("fw2" ≠ "cnt") by decide)]
            rw [hw24, hjv, hsucc, if_pos hq, if_neg hcnt_e, hw20])
        exact ⟨_, (s1.seq (s2.seq (s3.seq (s4.seq ((Run.ite_true hT1 (Run.ite_true hT2
          ((Run.ite_false hF3 Run.skip).seq s7'))).seq (rI _ hj6)))))).mono
          (by simp [Cond.size, Expr.size]), by rw [hjv] at hJ; exact hJ, by
            rw [hjv] at hJi ⊢; exact hJi⟩
    · have hF2 : (Cond.lt (V "fq") (V "fr")).evalB B σ4 = some false := by
        rw [c2]; exact congrArg some (decide_eq_false (by rw [hmr]; exact hlt2))
      have hq : qualV arr Vn j = false := by
        rw [hqual]; exact decide_eq_false (fun h => hlt2 h.2)
      obtain ⟨hJ, hJi⟩ := hnq σ4 hcn4 hw4 hw24 ha4 ho4 hfr4 hj4 hq
      exact ⟨_, (s1.seq (s2.seq (s3.seq (s4.seq ((Run.ite_true hT1 (Run.ite_false hF2 Run.skip)).seq
        (rI _ hj4)))))).mono (by simp [Cond.size, Expr.size]), hJ, by rw [hjv]; exact hJi⟩
  · have hF1 : (Cond.eq (V "xf") (.lit 1)).evalB B σ4 = some false := by
      rw [c1]; simp only [beq_eq_false_iff_ne.mpr hx1]
    have hq : qualV arr Vn j = false := by
      rw [hqual]; exact decide_eq_false (fun h => hx1 h.1)
    obtain ⟨hJ, hJi⟩ := hnq σ4 hcn4 hw4 hw24 ha4 ho4 hfr4 hj4 hq
    exact ⟨_, (s1.seq (s2.seq (s3.seq (s4.seq ((Run.ite_false hF1 Run.skip).seq
      (rI _ hj4)))))).mono (by simp [Cond.size, Expr.size]), hJ, by rw [hjv]; exact hJi⟩

/-- **The scan.** -/
theorem findCom_run (arr : List ℕ) (Vn VV e : ℕ) (σ : Env)
    (hE : ∀ k < VV, arr.getD (2 + k) 0 + 8 < B) (hlen : 2 + VV ≤ arr.length)
    (hB : VV + Vn + e + 16 < B) (hA : σ.arrs "TK" = arr) (hV : σ.vars "V" = Vn)
    (hVV : σ.vars "VV" = VV) (he : σ.vars "e" = e) :
    ∃ σ', Run B findCom σ σ' ((80 + 4) * VV + 20) ∧
      σ'.vars "fw" = edgeCellAt arr Vn e VV / Vn ∧ σ'.vars "fw2" = edgeCellAt arr Vn e VV % Vn ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ ∀ y, y ∉ AF → σ'.vars y = σ.vars y := by
  have s0 := asg_lit (B := B) "fw" 0 σ (by omega)
  set σ1 := σ.setVar "fw" 0 with hσ1
  have s1 := asg_lit (B := B) "fw2" 0 σ1 (by omega)
  set σ2 := σ1.setVar "fw2" 0 with hσ2
  have s2 := asg_lit (B := B) "cnt" 0 σ2 (by omega)
  set σ3 := σ2.setVar "cnt" 0 with hσ3
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := findBody) "j" "VV"
    (FInv arr Vn VV e σ3) VV 80 (by omega) (fun _ h => h.hj) (fun _ h => h.vVV)
    (findBody_spec arr Vn VV e σ3 hE hlen hB)) σ3
    ⟨by simp [Env.setVar], by simp [Env.setVar], by simp [hσ3, hσ2, hσ1, Env.setVar, hA],
      by simp [hσ3, hσ2, hσ1, Env.setVar, hV], by simp [hσ3, hσ2, hσ1, Env.setVar, hVV],
      by simp [hσ3, hσ2, hσ1, Env.setVar, he], by simp [Env.setVar], by
        simp [hσ3, hσ2, hσ1, Env.setVar, List.range_zero], by
        simp [hσ3, hσ2, hσ1, Env.setVar, edgeCellAt], by
        simp [hσ3, hσ2, hσ1, Env.setVar, edgeCellAt],
      fun y hy => by
        have hyj : y ≠ "j" := fun h => hy (by simp [AF, h])
        simp [Env.setVar, hyj]⟩
  refine ⟨σ', (s0.seq (s1.seq (s2.seq r))).mono (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hI.hw, hi]
  · rw [hI.hw2, hi]
  · rw [hI.arrs]; simp [hσ3, hσ2, hσ1, Env.setVar]
  · rw [hI.out]; simp [hσ3, hσ2, hσ1, Env.setVar]
  · intro y hy
    rw [hI.fr y hy]
    have g1 : y ≠ "fw" := fun h => hy (by simp [AF, h])
    have g2 : y ≠ "fw2" := fun h => hy (by simp [AF, h])
    have g3 : y ≠ "cnt" := fun h => hy (by simp [AF, h])
    simp [hσ3, hσ2, hσ1, Env.setVar, g1, g2, g3]

/-- **The pair the scan finds is the `e`-th of the pairs of endpoints.** -/
theorem edgeCells_getD (ns : List ℕ) (e : ℕ) :
    (edgeCellsN ns).getD e (0, 0) =
      (edgeCellAt ns (VM ns) e (VM ns * VM ns) / VM ns,
        edgeCellAt ns (VM ns) e (VM ns * VM ns) % VM ns) := by
  unfold edgeCellsN edgeCellAt
  have : ((0 : ℕ) / VM ns, (0 : ℕ) % VM ns) = ((0 : ℕ), (0 : ℕ)) := by simp
  rw [← this, List.getD_map]
  rfl

end Lax117284Proofs.Machine.MisFind

end

/-! ### `Lax117284Proofs.Machine.MisCheck` -/

section
/-!
The pass over the cells of the adjacency matrix that checks that every cell is symmetric, that no
vertex is adjacent to itself, and that no two vertices of the same class are adjacent, and counts the
edges.
-/

namespace Lax117284Proofs.Machine.MisCheck

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.SatOps Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.SatRank (bumpS countP_range_succ)
open Lax117284Proofs.Machine.MisSem Lax117284Proofs.Machine.MisFind
open Lax117284Proofs.Machine.MisFormat (VM)

variable {B : ℕ}

/-! ### Guards -/

/-- Clear the flag unless the condition holds. -/
def guard (b : Cond) : Com := .ite b .skip (.assign "ok" (.lit 0))

/-- Clear the flag if the first condition holds and the second does not. -/
def impGuard (b b' : Cond) : Com := .ite b (guard b') .skip

/-- Only the flag changed. -/
def OkStep (σ σ' : Env) (v : ℕ) : Prop :=
  σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ (∀ y, y ≠ "ok" → σ'.vars y = σ.vars y) ∧ σ'.vars "ok" = v

lemma okStep_setVar (σ : Env) (v : ℕ) : OkStep σ (σ.setVar "ok" v) v :=
  ⟨rfl, rfl, fun y hy => by simp [Env.setVar, hy], by simp [Env.setVar]⟩

lemma okStep_refl (σ : Env) : OkStep σ σ (σ.vars "ok") := ⟨rfl, rfl, fun _ _ => rfl, rfl⟩

theorem guard_run (b : Cond) (σ : Env) (P : Prop) [Decidable P] (hb : b.evalB B σ = some (decide P))
    (hokB : 0 < B) :
    ∃ σ', Run B (guard b) σ σ' (1 + b.size + 2) ∧
      OkStep σ σ' (if P then σ.vars "ok" else 0) := by
  by_cases hP : P
  · have hT : b.evalB B σ = some true := by rw [hb]; exact congrArg some (decide_eq_true hP)
    exact ⟨σ, (Run.ite_true hT Run.skip).mono (by omega), by rw [if_pos hP]; exact okStep_refl σ⟩
  · have hF : b.evalB B σ = some false := by rw [hb]; exact congrArg some (decide_eq_false hP)
    have l := asg_lit (B := B) "ok" 0 σ hokB
    exact ⟨_, (Run.ite_false hF l).mono (by omega), by rw [if_neg hP]; exact okStep_setVar σ 0⟩

theorem impGuard_run (b b' : Cond) (σ : Env) (P Q : Prop) [Decidable P] [Decidable Q]
    (hb : b.evalB B σ = some (decide P)) (hb' : b'.evalB B σ = some (decide Q)) (hokB : 0 < B) :
    ∃ σ', Run B (impGuard b b') σ σ' (1 + b.size + (1 + b'.size + 2)) ∧
      OkStep σ σ' (if P → Q then σ.vars "ok" else 0) := by
  by_cases hP : P
  · have hT : b.evalB B σ = some true := by rw [hb]; exact congrArg some (decide_eq_true hP)
    obtain ⟨σ', r, o⟩ := guard_run b' σ Q hb' hokB
    refine ⟨σ', (Run.ite_true hT r).mono (by omega), ?_⟩
    have : (if Q then σ.vars "ok" else 0) = (if P → Q then σ.vars "ok" else 0) := by
      by_cases hQ : Q <;> simp [hQ, hP]
    rw [← this]; exact o
  · have hF : b.evalB B σ = some false := by rw [hb]; exact congrArg some (decide_eq_false hP)
    refine ⟨σ, (Run.ite_false hF Run.skip).mono (by omega), ?_⟩
    have : σ.vars "ok" = (if P → Q then σ.vars "ok" else 0) := by
      rw [if_pos (fun h => absurd h hP)]
    rw [← this]; exact okStep_refl σ

/-! ### The pass -/

/-- The cell `t` is symmetric, is empty on the diagonal and empty between two vertices of the same
class; `V` is the number of vertices and `n` the number of vertices per class. -/
def PassV (arr : List ℕ) (V n t : ℕ) : Prop :=
  arr.getD (2 + t) 0 = arr.getD (2 + (t % V * V + t / V)) 0 ∧
  (t / V = t % V → arr.getD (2 + t) 0 = 0) ∧
  (t / V / n = t % V / n → arr.getD (2 + t) 0 = 0)

instance (arr : List ℕ) (V n : ℕ) : DecidablePred (PassV arr V n) := fun t => by
  unfold PassV; infer_instance

/-- The body of the pass. -/
def chkA : Com :=
  .seq (.assign "xa" (.get "TK" (add (.lit 2) (mul (.lit 1) (V "i")))))
  (.seq (.assign "qa" (.bin .div (V "i") (V "V")))
  (.seq (.assign "ma" (.bin .mul (V "qa") (V "V")))
  (.seq (.assign "ra" (.bin .sub (V "i") (V "ma")))
  (.seq (.assign "ta" (.bin .mul (V "ra") (V "V")))
  (.seq (.assign "tb" (.bin .add (V "ta") (V "qa")))
  (.seq (.assign "ya" (.get "TK" (add (.lit 2) (mul (.lit 1) (V "tb")))))
  (.seq (.assign "ca" (.bin .div (V "qa") (V "nn")))
  (.seq (.assign "cb" (.bin .div (V "ra") (V "nn")))
  (.seq (guard (.eq (V "xa") (V "ya")))
  (.seq (impGuard (.eq (V "qa") (V "ra")) (.eq (V "xa") (.lit 0)))
  (.seq (impGuard (.eq (V "ca") (V "cb")) (.eq (V "xa") (.lit 0)))
  (.seq (.ite (.eq (V "xa") (.lit 1))
      (.ite (.lt (V "qa") (V "ra")) (bumpS "cnt") .skip) .skip)
    (bumpS "i")))))))))))))

def chkALoop : Com := .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "VV")) chkA)

/-- The scalars the pass assigns. -/
def AA : List String := ["i", "xa", "qa", "ma", "ra", "ta", "tb", "ya", "ca", "cb", "ok", "cnt"]

structure AInv (arr : List ℕ) (Vn n VV ok0 : ℕ) (σ0 σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vV : σ.vars "V" = Vn
  vn : σ.vars "nn" = n
  vVV : σ.vars "VV" = VV
  hi : σ.vars "i" ≤ VV
  hok : σ.vars "ok" = flagTo (PassV arr Vn n) ok0 (σ.vars "i")
  hc : σ.vars "cnt" = (List.range (σ.vars "i")).countP (qualV arr Vn)
  fr : ∀ y, y ∉ AA → σ.vars y = σ0.vars y

lemma ainv_step (arr : List ℕ) (Vn n VV ok0 : ℕ) (σ0 σ σ' : Env) (hI : AInv arr Vn n VV ok0 σ0 σ)
    (hlt : σ.vars "i" < VV) (hv : ∀ y, y ∉ AA → σ'.vars y = σ.vars y)
    (ha : σ'.arrs = σ.arrs) (ho : σ'.out = σ.out) (hi : σ'.vars "i" = σ.vars "i")
    (hok : σ'.vars "ok" = flagTo (PassV arr Vn n) ok0 (σ.vars "i" + 1))
    (hcnt : σ'.vars "cnt" = (List.range (σ.vars "i" + 1)).countP (qualV arr Vn)) :
    AInv arr Vn n VV ok0 σ0 (σ'.setVar "i" (σ.vars "i" + 1)) ∧
      (σ'.setVar "i" (σ.vars "i" + 1)).vars "i" = σ.vars "i" + 1 := by
  have hsa := hI.arrs
  have hso := hI.out
  have hA0 := hI.hA
  have hVv := hI.vV
  have hnv := hI.vn
  have hVVv := hI.vVV
  have hile := hI.hi
  have hokv := hI.hok
  have hc := hI.hc
  have hfr := hI.fr
  clear hI
  refine ⟨⟨?_, ?_, hA0, ?_, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_⟩, by simp [Env.setVar]⟩
  · simp only [Env.setVar]; rw [ha, hsa]
  · simp only [Env.setVar]; rw [ho, hso]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "V" (by simp [AA]), hVv]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "nn" (by simp [AA]), hnv]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "VV" (by simp [AA]), hVVv]
  · simp [Env.setVar]; omega
  · simp [Env.setVar, hok]
  · simp [Env.setVar, hcnt]
  · have hyi : y ≠ "i" := fun h => hy (by simp [AA, h])
    simp only [Env.setVar, if_neg hyi]
    rw [hv y hy, hfr y hy]

/-- The value of an equality of two scalars, as a decision. -/
lemma condEqD (x y : String) (σ : Env) (a b : ℕ) (hx : σ.vars x = a) (hy : σ.vars y = b)
    (ha : a < B) (hb : b < B) :
    (Cond.eq (V x) (V y)).evalB B σ = some (decide (a = b)) := by
  rw [cond_eqv (B := B) x y σ a b hx hy ha hb]
  exact congrArg some (beq_eq_decide _ _)

lemma condEqLD (x : String) (c : ℕ) (σ : Env) (a : ℕ) (hx : σ.vars x = a) (ha : a < B)
    (hc : c < B) : (Cond.eq (V x) (.lit c)).evalB B σ = some (decide (a = c)) := by
  rw [cond_eql (B := B) x c σ a hx ha hc]
  exact congrArg some (beq_eq_decide _ _)

lemma cell_lt' (Vn a b : ℕ) (ha : a < Vn) (hb : b < Vn) : a * Vn + b < Vn * Vn := by
  have : a * Vn + b < (a + 1) * Vn := by rw [Nat.add_mul, Nat.one_mul]; omega
  have h2 : (a + 1) * Vn ≤ Vn * Vn := Nat.mul_le_mul_right _ (by omega)
  omega

set_option maxHeartbeats 12800000 in
theorem chkA_spec (arr : List ℕ) (Vn n VV ok0 : ℕ) (σ0 : Env) (hVVeq : VV = Vn * Vn)
    (hE : ∀ k < VV, arr.getD (2 + k) 0 + 8 < B) (hlen : 2 + VV ≤ arr.length)
    (hB : VV + Vn + n + 16 < B) (hok0 : ok0 ≤ 1) :
    Spec B (fun σ => AInv arr Vn n VV ok0 σ0 σ ∧ σ.vars "i" < VV) chkA
      (fun σ σ' => AInv arr Vn n VV ok0 σ0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 300 := by
  rintro σ ⟨hI, hlt⟩
  have hI' := hI
  obtain ⟨hsa, hso, hA0, hVv, hnv, hVVv, hile, hokv, hc, hfr⟩ := hI
  have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
  obtain ⟨i, hiv⟩ : ∃ i, σ.vars "i" = i := ⟨_, rfl⟩
  rw [hiv] at hlt hokv hc
  have hVpos : 0 < Vn := by
    by_contra h0
    have : Vn = 0 := by omega
    rw [this] at hVVeq; omega
  have hqa : i / Vn < Vn := (Nat.div_lt_iff_lt_mul hVpos).2 (by rw [← hVVeq]; exact hlt)
  have hra : i % Vn < Vn := Nat.mod_lt _ hVpos
  have hmr : i - i / Vn * Vn = i % Vn := mod_eq_sub i Vn
  have hmul : i / Vn * Vn ≤ i := Nat.div_mul_le_self _ _
  have htb := cell_lt' Vn (i % Vn) (i / Vn) hra hqa
  have hokle : flagTo (PassV arr Vn n) ok0 i ≤ 1 := flagTo_le _ _ _
  have hcnt_le : (List.range i).countP (qualV arr Vn) ≤ i := by
    have := List.countP_le_length (p := qualV arr Vn) (l := List.range i)
    simpa using this
  have hcB : σ.vars "cnt" < B := by rw [hc]; omega
  have hokB : σ.vars "ok" < B := by rw [hokv]; omega
  have e1 := hE i hlt
  have htb' : (i - i / Vn * Vn) * Vn + i / Vn < VV := by rw [hmr, hVVeq]; exact htb
  have e2 := hE ((i - i / Vn * Vn) * Vn + i / Vn) htb'
  have hd1 : i / Vn / n ≤ i / Vn := Nat.div_le_self _ _
  have hd2 : (i - i / Vn * Vn) / n ≤ i - i / Vn * Vn := Nat.div_le_self _ _
  -- xa
  have s1 := asg_idx (B := B) "xa" 2 1 "i" σ arr i hA hiv (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by rw [Nat.one_mul]; omega)
  simp only [Nat.one_mul] at s1
  set σ1 := σ.setVar "xa" (arr.getD (2 + i) 0) with hσ1
  have hi1 : σ1.vars "i" = i := by simp [hσ1, Env.setVar, hiv]
  have hV1 : σ1.vars "V" = Vn := by simp [hσ1, Env.setVar, hVv]
  have s2 := asg_bin (B := B) .div "i" "V" "qa" σ1 i Vn hi1 hV1
    (by simp only [Bop.apply_div]; omega) (by omega) (by omega)
  simp only [Bop.apply_div] at s2
  set σ2 := σ1.setVar "qa" (i / Vn) with hσ2
  have hq2 : σ2.vars "qa" = i / Vn := by simp [hσ2, Env.setVar]
  have hV2 : σ2.vars "V" = Vn := by simp [hσ2, hσ1, Env.setVar, hVv]
  have s3 := asg_bin (B := B) .mul "qa" "V" "ma" σ2 (i / Vn) Vn hq2 hV2
    (by simp only [Bop.apply_mul]; omega) (by omega) (by omega)
  simp only [Bop.apply_mul] at s3
  set σ3 := σ2.setVar "ma" (i / Vn * Vn) with hσ3
  have hi3 : σ3.vars "i" = i := by simp [hσ3, hσ2, hσ1, Env.setVar, hiv]
  have hm3 : σ3.vars "ma" = i / Vn * Vn := by simp [hσ3, Env.setVar]
  have s4 := asg_bin (B := B) .sub "i" "ma" "ra" σ3 i (i / Vn * Vn) hi3 hm3
    (by simp only [Bop.apply_sub]; omega) (by omega) (by omega)
  simp only [Bop.apply_sub] at s4
  set σ4 := σ3.setVar "ra" (i - i / Vn * Vn) with hσ4
  have hr4 : σ4.vars "ra" = i - i / Vn * Vn := by simp [hσ4, Env.setVar]
  have hV4 : σ4.vars "V" = Vn := by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, hVv]
  have s5 := asg_bin (B := B) .mul "ra" "V" "ta" σ4 (i - i / Vn * Vn) Vn hr4 hV4
    (by simp only [Bop.apply_mul]; omega) (by omega) (by omega)
  simp only [Bop.apply_mul] at s5
  set σ5 := σ4.setVar "ta" ((i - i / Vn * Vn) * Vn) with hσ5
  have ht5 : σ5.vars "ta" = (i - i / Vn * Vn) * Vn := by simp [hσ5, Env.setVar]
  have hq5 : σ5.vars "qa" = i / Vn := by simp [hσ5, hσ4, hσ3, hσ2, Env.setVar]
  have s6 := asg_bin (B := B) .add "ta" "qa" "tb" σ5 ((i - i / Vn * Vn) * Vn) (i / Vn) ht5 hq5
    (by simp only [Bop.apply_add]; omega) (by omega) (by omega)
  simp only [Bop.apply_add] at s6
  set σ6 := σ5.setVar "tb" ((i - i / Vn * Vn) * Vn + i / Vn) with hσ6
  have hb6 : σ6.vars "tb" = (i - i / Vn * Vn) * Vn + i / Vn := by simp [hσ6, Env.setVar]
  have hA6 : σ6.arrs "TK" = arr := by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar, hA]
  have s7 := asg_idx (B := B) "ya" 2 1 "tb" σ6 arr ((i - i / Vn * Vn) * Vn + i / Vn) hA6 hb6
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [Nat.one_mul]; omega)
  simp only [Nat.one_mul] at s7
  set σ7 := σ6.setVar "ya" (arr.getD (2 + ((i - i / Vn * Vn) * Vn + i / Vn)) 0) with hσ7
  have hq7 : σ7.vars "qa" = i / Vn := by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, Env.setVar]
  have hn7 : σ7.vars "nn" = n := by
    simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar, hnv]
  have s8 := asg_bin (B := B) .div "qa" "nn" "ca" σ7 (i / Vn) n hq7 hn7
    (by simp only [Bop.apply_div]; omega) (by omega) (by omega)
  simp only [Bop.apply_div] at s8
  set σ8 := σ7.setVar "ca" (i / Vn / n) with hσ8
  have hr8 : σ8.vars "ra" = i - i / Vn * Vn := by
    simp [hσ8, hσ7, hσ6, hσ5, Env.setVar, hσ4]
  have hn8 : σ8.vars "nn" = n := by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar, hnv]
  have s9 := asg_bin (B := B) .div "ra" "nn" "cb" σ8 (i - i / Vn * Vn) n hr8 hn8
    (by simp only [Bop.apply_div]; omega) (by omega) (by omega)
  simp only [Bop.apply_div] at s9
  set σ9 := σ8.setVar "cb" ((i - i / Vn * Vn) / n) with hσ9
  -- the facts about σ9
  have hxa9 : σ9.vars "xa" = arr.getD (2 + i) 0 := by
    simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have hya9 : σ9.vars "ya" = arr.getD (2 + (i % Vn * Vn + i / Vn)) 0 := by
    rw [← hmr]; simp [hσ9, hσ8, hσ7, Env.setVar]
  have hqa9 : σ9.vars "qa" = i / Vn := by
    simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, Env.setVar]
  have hra9 : σ9.vars "ra" = i % Vn := by
    rw [← hmr]; simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, Env.setVar]
  have hca9 : σ9.vars "ca" = i / Vn / n := by simp [hσ9, hσ8, Env.setVar]
  have hcb9 : σ9.vars "cb" = i % Vn / n := by rw [← hmr]; simp [hσ9, Env.setVar]
  have hok9 : σ9.vars "ok" = σ.vars "ok" := by
    simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have hcn9 : σ9.vars "cnt" = σ.vars "cnt" := by
    simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have hi9 : σ9.vars "i" = i := by
    simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar, hiv]
  have ha9 : σ9.arrs = σ.arrs := by
    simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have ho9 : σ9.out = σ.out := by
    simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have hfr9 : ∀ y, y ∉ AA → σ9.vars y = σ.vars y := by
    intro y hy
    have g1 : y ≠ "xa" := fun h => hy (by simp [AA, h])
    have g2 : y ≠ "qa" := fun h => hy (by simp [AA, h])
    have g3 : y ≠ "ma" := fun h => hy (by simp [AA, h])
    have g4 : y ≠ "ra" := fun h => hy (by simp [AA, h])
    have g5 : y ≠ "ta" := fun h => hy (by simp [AA, h])
    have g6 : y ≠ "tb" := fun h => hy (by simp [AA, h])
    have g7 : y ≠ "ya" := fun h => hy (by simp [AA, h])
    have g8 : y ≠ "ca" := fun h => hy (by simp [AA, h])
    have g9 : y ≠ "cb" := fun h => hy (by simp [AA, h])
    simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar, g1, g2, g3, g4, g5, g6, g7, g8, g9]
  have hokB9 : 0 < B := by omega
  have hd3 : i % Vn / n ≤ i % Vn := Nat.div_le_self _ _
  have e2m : arr.getD (2 + (i % Vn * Vn + i / Vn)) 0 + 8 < B := by
    have := e2; rwa [hmr] at this
  -- guard 1
  obtain ⟨σg1, rg1, og1⟩ := guard_run (B := B) (.eq (V "xa") (V "ya")) σ9
    (arr.getD (2 + i) 0 = arr.getD (2 + (i % Vn * Vn + i / Vn)) 0)
    (condEqD "xa" "ya" σ9 _ _ hxa9 hya9 (by omega) (by omega)) hokB9
  have fr1 : ∀ y, y ≠ "ok" → σg1.vars y = σ9.vars y := og1.2.2.1
  -- guard 2
  obtain ⟨σg2, rg2, og2⟩ := impGuard_run (B := B) (.eq (V "qa") (V "ra")) (.eq (V "xa") (.lit 0)) σg1
    (i / Vn = i % Vn) (arr.getD (2 + i) 0 = 0)
    (condEqD "qa" "ra" σg1 _ _ (by rw [fr1 _ (by decide)]; exact hqa9)
      (by rw [fr1 _ (by decide)]; exact hra9) (by omega) (by omega))
    (condEqLD "xa" 0 σg1 _ (by rw [fr1 _ (by decide)]; exact hxa9) (by omega) (by omega)) hokB9
  have fr2 : ∀ y, y ≠ "ok" → σg2.vars y = σg1.vars y := og2.2.2.1
  -- guard 3
  obtain ⟨σg3, rg3, og3⟩ := impGuard_run (B := B) (.eq (V "ca") (V "cb")) (.eq (V "xa") (.lit 0)) σg2
    (i / Vn / n = i % Vn / n) (arr.getD (2 + i) 0 = 0)
    (condEqD "ca" "cb" σg2 _ _ (by rw [fr2 _ (by decide), fr1 _ (by decide)]; exact hca9)
      (by rw [fr2 _ (by decide), fr1 _ (by decide)]; exact hcb9) (by omega) (by omega))
    (condEqLD "xa" 0 σg2 _ (by rw [fr2 _ (by decide), fr1 _ (by decide)]; exact hxa9) (by omega)
      (by omega)) hokB9
  have fr3 : ∀ y, y ≠ "ok" → σg3.vars y = σg2.vars y := og3.2.2.1
  have fall : ∀ y, y ≠ "ok" → σg3.vars y = σ9.vars y := fun y hy =>
    (fr3 y hy).trans ((fr2 y hy).trans (fr1 y hy))
  have ha3 : σg3.arrs = σ.arrs := og3.1.trans (og2.1.trans (og1.1.trans ha9))
  have ho3 : σg3.out = σ.out := og3.2.1.trans (og2.2.1.trans (og1.2.1.trans ho9))
  have hok3 : σg3.vars "ok" = (if (i / Vn / n = i % Vn / n → arr.getD (2 + i) 0 = 0) then
      (if (i / Vn = i % Vn → arr.getD (2 + i) 0 = 0) then
        (if arr.getD (2 + i) 0 = arr.getD (2 + (i % Vn * Vn + i / Vn)) 0 then σ.vars "ok" else 0)
      else 0) else 0) := by
    rw [og3.2.2.2, og2.2.2.2, og1.2.2.2, hok9]
  have hi3' : σg3.vars "i" = i := by rw [fall _ (by decide), hi9]
  have hokfin : σg3.vars "ok" = flagTo (PassV arr Vn n) ok0 (i + 1) := by
    rw [hok3, flagTo_succ, ← hokv]
    unfold PassV
    have hf : σ.vars "ok" = 0 ∨ σ.vars "ok" = 1 := by omega
    rcases hf with h | h <;> rw [h] <;>
      (split_ifs <;> first | rfl | omega | (exfalso; tauto))
  -- the count
  have hxa3 : σg3.vars "xa" = arr.getD (2 + i) 0 := by rw [fall _ (by decide)]; exact hxa9
  have hqa3 : σg3.vars "qa" = i / Vn := by rw [fall _ (by decide)]; exact hqa9
  have hra3 : σg3.vars "ra" = i % Vn := by rw [fall _ (by decide)]; exact hra9
  have hcn3 : σg3.vars "cnt" = σ.vars "cnt" := by rw [fall _ (by decide)]; exact hcn9
  have hokB3 : σg3.vars "ok" < B := by rw [hokfin]; have := flagTo_le (PassV arr Vn n) ok0 (i + 1); omega
  have c1 := cond_eql (B := B) "xa" 1 σg3 _ hxa3 (by omega) (by omega)
  have c2 := cond_ltv (B := B) "qa" "ra" σg3 _ _ hqa3 hra3 (by omega) (by omega)
  have rI : ∀ σ' : Env, σ'.vars "i" = i →
      Run B (bumpS "i") σ' (σ'.setVar "i" (i + 1)) 5 :=
    fun σ' hi' => by
      have r : Run B (.assign "i" (.bin .add (V "i") (.lit 1))) σ'
          (σ'.setVar "i" (σ'.vars "i" + 1)) (1 + (Expr.bin .add (V "i") (.lit 1)).size) :=
        Run.assign (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
      rw [hi'] at r
      exact r.mono (by simp [Expr.size])
  have hcs := countP_range_succ (qualV arr Vn) i
  have hqual : qualV arr Vn i = decide (arr.getD (2 + i) 0 = 1 ∧ i / Vn < i % Vn) := rfl
  have hfrall : ∀ y, y ∉ AA → σg3.vars y = σ.vars y := fun y hy =>
    (fall y (fun h => hy (by simp [AA, h]))).trans (hfr9 y hy)
  have hnq : ∀ (σ' : Env), σ'.vars "cnt" = σ.vars "cnt" → σ'.vars "ok" = σg3.vars "ok" →
      σ'.arrs = σ.arrs → σ'.out = σ.out → (∀ y, y ∉ AA → σ'.vars y = σ.vars y) →
      σ'.vars "i" = i → qualV arr Vn i = false →
      AInv arr Vn n VV ok0 σ0 (σ'.setVar "i" (i + 1)) ∧
        (σ'.setVar "i" (i + 1)).vars "i" = i + 1 := by
    intro σ' hc' hk' ha' ho' hf' hi'' hq
    have := ainv_step arr Vn n VV ok0 σ0 σ σ' hI' (by rw [hiv]; exact hlt) hf' ha' ho'
      (by rw [hi'', hiv]) (by rw [hk', hokfin, hiv])
      (by rw [hc', hiv, hcs, hq, ← hc]; simp)
    rw [hiv] at this
    exact this
  by_cases hx1 : arr.getD (2 + i) 0 = 1
  · have hT1 : (Cond.eq (V "xa") (.lit 1)).evalB B σg3 = some true := by rw [c1, hx1]; simp
    by_cases hlt2 : i / Vn < i % Vn
    · have hT2 : (Cond.lt (V "qa") (V "ra")).evalB B σg3 = some true := by
        rw [c2]; exact congrArg some (decide_eq_true hlt2)
      have hq : qualV arr Vn i = true := by rw [hqual]; exact decide_eq_true ⟨hx1, hlt2⟩
      have s7' := asg_addl (B := B) "cnt" "cnt" 1 σg3 (σ.vars "cnt") hcn3 (by omega) (by omega)
        (by omega)
      have s7'' : Run B (bumpS "cnt") σg3 (σg3.setVar "cnt" (σ.vars "cnt" + 1)) 5 := s7'
      have hfin : ∀ y, y ∉ AA → (σg3.setVar "cnt" (σ.vars "cnt" + 1)).vars y = σ.vars y := by
        intro y hy
        have g3 : y ≠ "cnt" := fun h => hy (by simp [AA, h])
        simp only [Env.setVar, if_neg g3]
        exact hfrall y hy
      have hi6 : (σg3.setVar "cnt" (σ.vars "cnt" + 1)).vars "i" = i := by
        simp [Env.setVar, hi3']
      obtain ⟨hJ, hJi⟩ := ainv_step arr Vn n VV ok0 σ0 σ (σg3.setVar "cnt" (σ.vars "cnt" + 1)) hI'
        (by rw [hiv]; exact hlt) hfin (by simp [Env.setVar, ha3]) (by simp [Env.setVar, ho3])
        (by rw [hi6, hiv])
        (by simp [Env.setVar, hokfin, hiv])
        (by
          simp only [Env.setVar, if_true]
          rw [hiv, hcs, hq, ← hc]; simp)
      exact ⟨_, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (rg1.seq
        (rg2.seq (rg3.seq ((Run.ite_true hT1 (Run.ite_true hT2 s7'')).seq (rI _ hi6)))))))))))))).mono
        (by simp [Cond.size, Expr.size] <;> omega), by rw [hiv] at hJ; exact hJ, by
          rw [hiv] at hJi ⊢; exact hJi⟩
    · have hF2 : (Cond.lt (V "qa") (V "ra")).evalB B σg3 = some false := by
        rw [c2]; exact congrArg some (decide_eq_false hlt2)
      have hq : qualV arr Vn i = false := by
        rw [hqual]; exact decide_eq_false (fun h => hlt2 h.2)
      obtain ⟨hJ, hJi⟩ := hnq σg3 hcn3 rfl ha3 ho3 hfrall hi3' hq
      exact ⟨_, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (rg1.seq
        (rg2.seq (rg3.seq ((Run.ite_true hT1 (Run.ite_false hF2 Run.skip)).seq
          (rI _ hi3')))))))))))))).mono (by simp [Cond.size, Expr.size] <;> omega), hJ,
        by rw [hiv]; exact hJi⟩
  · have hF1 : (Cond.eq (V "xa") (.lit 1)).evalB B σg3 = some false := by
      rw [c1]; simp only [beq_eq_false_iff_ne.mpr hx1]
    have hq : qualV arr Vn i = false := by
      rw [hqual]; exact decide_eq_false (fun h => hx1 h.1)
    obtain ⟨hJ, hJi⟩ := hnq σg3 hcn3 rfl ha3 ho3 hfrall hi3' hq
    exact ⟨_, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (rg1.seq
      (rg2.seq (rg3.seq ((Run.ite_false hF1 Run.skip).seq (rI _ hi3')))))))))))))).mono
      (by simp [Cond.size, Expr.size] <;> omega), hJ, by rw [hiv]; exact hJi⟩

/-- **The pass over the cells.** -/
theorem chkALoop_run (arr : List ℕ) (Vn n VV ok0 : ℕ) (σ : Env) (hVVeq : VV = Vn * Vn)
    (hE : ∀ k < VV, arr.getD (2 + k) 0 + 8 < B) (hlen : 2 + VV ≤ arr.length)
    (hB : VV + Vn + n + 16 < B) (hok0 : ok0 ≤ 1) (hA : σ.arrs "TK" = arr)
    (hV : σ.vars "V" = Vn) (hn : σ.vars "nn" = n) (hVV : σ.vars "VV" = VV)
    (hok : σ.vars "ok" = ok0) (hcn : σ.vars "cnt" = 0) :
    ∃ σ', Run B chkALoop σ σ' ((300 + 4) * VV + 6) ∧
      σ'.vars "ok" = flagTo (PassV arr Vn n) ok0 VV ∧
      σ'.vars "cnt" = (List.range VV).countP (qualV arr Vn) ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ AA → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := chkA) "i" "VV"
    (AInv arr Vn n VV ok0 σ) VV 300 (by omega) (fun _ h => h.hi) (fun _ h => h.vVV)
    (chkA_spec arr Vn n VV ok0 σ hVVeq hE hlen hB hok0)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, by simp [Env.setVar, hV],
      by simp [Env.setVar, hn], by simp [Env.setVar, hVV], by simp [Env.setVar], by
        simp only [Env.setVar]
        simp [flagTo_zero (PassV arr Vn n) ok0 hok0, hok], by
        simp [Env.setVar, hcn], fun y hy => by
      have hyi : y ≠ "i" := fun h => hy (by simp [AA, h])
      simp [Env.setVar, hyi]⟩
  refine ⟨σ', r, ?_, ?_, hI.arrs.trans (by simp [Env.setVar]), hI.out.trans (by simp [Env.setVar]), ?_⟩
  · rw [hI.hok, hi]
  · rw [hI.hc, hi]
  · intro y hy
    rw [hI.fr y hy]

/-! ### The pass over the rows -/

/-- The row `w` has `r` ones. -/
def RowP (arr : List ℕ) (Vn r w : ℕ) : Prop :=
  (List.range Vn).countP (MisCount.onePred arr (2 + w * Vn)) = r

instance (arr : List ℕ) (Vn r : ℕ) : DecidablePred (RowP arr Vn r) := fun w => by
  unfold RowP; infer_instance

lemma rowP_iff (ns : List ℕ) (w : ℕ) : RowP ns (VM ns) (rowSum ns 0) w ↔ rowSum ns w = rowSum ns 0 := by
  have : (List.range (VM ns)).countP (MisCount.onePred ns (2 + w * VM ns)) = rowSum ns w := by
    unfold rowSum
    refine List.countP_congr fun x _ => ?_
    unfold MisCount.onePred mat
    rw [Nat.add_assoc]
  unfold RowP
  rw [this]

/-- The body of the pass over the rows. -/
def chkB : Com :=
  .seq (.assign "rb" (.bin .mul (V "i") (V "V")))
  (.seq (.assign "bs" (add (.lit 2) (mul (.lit 1) (V "rb"))))
  (.seq (.assign "bd" (V "V"))
  (.seq MisCount.cntCom
  (.seq (guard (.eq (V "cnt") (V "rr")))
    (bumpS "i")))))

def chkBLoop : Com := .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "V")) chkB)

/-- The scalars the pass assigns. -/
def AB : List String := ["i", "rb", "bs", "bd", "j", "xj", "cnt", "ok"]

structure BInv (arr : List ℕ) (Vn r ok0 : ℕ) (σ0 σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vV : σ.vars "V" = Vn
  vr : σ.vars "rr" = r
  hi : σ.vars "i" ≤ Vn
  hok : σ.vars "ok" = flagTo (RowP arr Vn r) ok0 (σ.vars "i")
  fr : ∀ y, y ∉ AB → σ.vars y = σ0.vars y

lemma binv_step (arr : List ℕ) (Vn r ok0 : ℕ) (σ0 σ σ' : Env) (hI : BInv arr Vn r ok0 σ0 σ)
    (hlt : σ.vars "i" < Vn) (hv : ∀ y, y ∉ AB → σ'.vars y = σ.vars y)
    (ha : σ'.arrs = σ.arrs) (ho : σ'.out = σ.out) (hi : σ'.vars "i" = σ.vars "i")
    (hok : σ'.vars "ok" = flagTo (RowP arr Vn r) ok0 (σ.vars "i" + 1)) :
    BInv arr Vn r ok0 σ0 (σ'.setVar "i" (σ.vars "i" + 1)) ∧
      (σ'.setVar "i" (σ.vars "i" + 1)).vars "i" = σ.vars "i" + 1 := by
  have hsa := hI.arrs
  have hso := hI.out
  have hA0 := hI.hA
  have hVv := hI.vV
  have hrv := hI.vr
  have hile := hI.hi
  have hokv := hI.hok
  have hfr := hI.fr
  clear hI
  refine ⟨⟨?_, ?_, hA0, ?_, ?_, ?_, ?_, fun y hy => ?_⟩, by simp [Env.setVar]⟩
  · simp only [Env.setVar]; rw [ha, hsa]
  · simp only [Env.setVar]; rw [ho, hso]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "V" (by simp [AB]), hVv]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "rr" (by simp [AB]), hrv]
  · simp [Env.setVar]; omega
  · simp [Env.setVar, hok]
  · have hyi : y ≠ "i" := fun h => hy (by simp [AB, h])
    simp only [Env.setVar, if_neg hyi]
    rw [hv y hy, hfr y hy]

set_option maxHeartbeats 6400000 in
theorem chkB_spec (arr : List ℕ) (Vn VV r ok0 : ℕ) (σ0 : Env) (hVVeq : VV = Vn * Vn)
    (hE : ∀ k < VV, arr.getD (2 + k) 0 + 8 < B) (hlen : 2 + VV ≤ arr.length)
    (hB : VV + Vn + r + 24 < B) (hok0 : ok0 ≤ 1) :
    Spec B (fun σ => BInv arr Vn r ok0 σ0 σ ∧ σ.vars "i" < Vn) chkB
      (fun σ σ' => BInv arr Vn r ok0 σ0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1)
      ((40 + 4) * Vn + 100) := by
  rintro σ ⟨hI, hlt⟩
  have hI' := hI
  obtain ⟨hsa, hso, hA0, hVv, hrv, hile, hokv, hfr⟩ := hI
  have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
  obtain ⟨i, hiv⟩ : ∃ i, σ.vars "i" = i := ⟨_, rfl⟩
  rw [hiv] at hlt hokv
  have hiV : i * Vn + Vn ≤ Vn * Vn := by
    have := Nat.mul_le_mul_right Vn (show i + 1 ≤ Vn by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have hokle : flagTo (RowP arr Vn r) ok0 i ≤ 1 := flagTo_le _ _ _
  have hokB : σ.vars "ok" < B := by rw [hokv]; omega
  have s1 := asg_bin (B := B) .mul "i" "V" "rb" σ i Vn hiv hVv
    (by simp only [Bop.apply_mul]; omega) (by omega) (by omega)
  simp only [Bop.apply_mul] at s1
  set σ1 := σ.setVar "rb" (i * Vn) with hσ1
  have hrb1 : σ1.vars "rb" = i * Vn := by simp [hσ1, Env.setVar]
  have s2 := asg_linl (B := B) "bs" 2 1 "rb" σ1 (i * Vn) hrb1 (by omega) (by omega) (by omega)
    (by omega) (by omega)
  simp only [Nat.one_mul] at s2
  set σ2 := σ1.setVar "bs" (2 + i * Vn) with hσ2
  have hV2 : σ2.vars "V" = Vn := by simp [hσ2, hσ1, Env.setVar, hVv]
  have s3 := asg_var (B := B) "bd" "V" σ2 Vn hV2 (by omega)
  set σ3 := σ2.setVar "bd" Vn with hσ3
  have hA3 : σ3.arrs "TK" = arr := by simp [hσ3, hσ2, hσ1, Env.setVar, hA]
  have hbs3 : σ3.vars "bs" = 2 + i * Vn := by simp [hσ3, hσ2, Env.setVar]
  have hbd3 : σ3.vars "bd" = Vn := by simp [hσ3, Env.setVar]
  obtain ⟨σ4, r4, c4, a4, o4, f4⟩ := MisCount.cntCom_run (B := B) arr (2 + i * Vn) Vn σ3
    (fun k hk => by
      have := hE (i * Vn + k) (by omega)
      rwa [← Nat.add_assoc] at this)
    (by omega) (by omega) hA3 hbs3 hbd3
  have hrr4 : σ4.vars "rr" = r := by
    rw [f4 "rr" (by simp [MisCount.AN])]; simp [hσ3, hσ2, hσ1, Env.setVar, hrv]
  have hcnB : σ4.vars "cnt" < B := by
    rw [c4]
    have := List.countP_le_length (p := MisCount.onePred arr (2 + i * Vn)) (l := List.range Vn)
    simp at this; omega
  have hokB4 : 0 < B := by omega
  obtain ⟨σ5, r5, o5⟩ := guard_run (B := B) (.eq (V "cnt") (V "rr")) σ4
    (RowP arr Vn r i) (by
      have := condEqD (B := B) "cnt" "rr" σ4 _ _ rfl hrr4 hcnB (by omega)
      unfold RowP
      rw [c4] at this
      exact this) hokB4
  have fr5 : ∀ y, y ≠ "ok" → σ5.vars y = σ4.vars y := o5.2.2.1
  have hok4 : σ4.vars "ok" = σ.vars "ok" := by
    rw [f4 "ok" (by simp [MisCount.AN])]; simp [hσ3, hσ2, hσ1, Env.setVar]
  have hi4 : σ4.vars "i" = i := by
    rw [f4 "i" (by simp [MisCount.AN])]; simp [hσ3, hσ2, hσ1, Env.setVar, hiv]
  have hi5 : σ5.vars "i" = i := by rw [fr5 _ (by decide), hi4]
  have ha5 : σ5.arrs = σ.arrs := o5.1.trans (a4.trans (by simp [hσ3, hσ2, hσ1, Env.setVar]))
  have ho5 : σ5.out = σ.out := o5.2.1.trans (o4.trans (by simp [hσ3, hσ2, hσ1, Env.setVar]))
  have hfrall : ∀ y, y ∉ AB → σ5.vars y = σ.vars y := by
    intro y hy
    have hyo : y ≠ "ok" := fun h => hy (by simp [AB, h])
    have g1 : y ∉ MisCount.AN := fun h => hy (by
      simp only [MisCount.AN, AB, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
    have g2 : y ≠ "rb" := fun h => hy (by simp [AB, h])
    have g3 : y ≠ "bs" := fun h => hy (by simp [AB, h])
    have g4 : y ≠ "bd" := fun h => hy (by simp [AB, h])
    rw [fr5 y hyo, f4 y g1]
    simp [hσ3, hσ2, hσ1, Env.setVar, g2, g3, g4]
  have hokfin : σ5.vars "ok" = flagTo (RowP arr Vn r) ok0 (i + 1) := by
    rw [o5.2.2.2, hok4, flagTo_succ, ← hokv]
    have hf : σ.vars "ok" = 0 ∨ σ.vars "ok" = 1 := by omega
    rcases hf with h | h <;> rw [h] <;> (split_ifs <;> first | rfl | omega | (exfalso; tauto))
  have rI : Run B (bumpS "i") σ5 (σ5.setVar "i" (i + 1)) 5 := by
    have r : Run B (.assign "i" (.bin .add (V "i") (.lit 1))) σ5
        (σ5.setVar "i" (σ5.vars "i" + 1)) (1 + (Expr.bin .add (V "i") (.lit 1)).size) :=
      Run.assign (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
    rw [hi5] at r
    exact r.mono (by simp [Expr.size])
  obtain ⟨hJ, hJi⟩ := binv_step arr Vn r ok0 σ0 σ σ5 hI' (by rw [hiv]; exact hlt) hfrall ha5 ho5
    (by rw [hi5, hiv]) (by rw [hokfin, hiv])
  exact ⟨_, (s1.seq (s2.seq (s3.seq (r4.seq (r5.seq rI))))).mono
    (by simp [Cond.size, Expr.size] <;> omega), by rw [hiv] at hJ; exact hJ, by
      rw [hiv] at hJi ⊢; exact hJi⟩

/-- **The pass over the rows.** -/
theorem chkBLoop_run (arr : List ℕ) (Vn VV r ok0 : ℕ) (σ : Env) (hVVeq : VV = Vn * Vn)
    (hE : ∀ k < VV, arr.getD (2 + k) 0 + 8 < B) (hlen : 2 + VV ≤ arr.length)
    (hB : VV + Vn + r + 24 < B) (hok0 : ok0 ≤ 1) (hA : σ.arrs "TK" = arr)
    (hV : σ.vars "V" = Vn) (hr : σ.vars "rr" = r) (hok : σ.vars "ok" = ok0) :
    ∃ σ', Run B chkBLoop σ σ' (((40 + 4) * Vn + 100 + 4) * Vn + 6) ∧
      σ'.vars "ok" = flagTo (RowP arr Vn r) ok0 Vn ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ AB → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r', hI, hi⟩ := (Spec.forRangeZero (B := B) (c := chkB) "i" "V"
    (BInv arr Vn r ok0 σ) Vn ((40 + 4) * Vn + 100) (by omega) (fun _ h => h.hi) (fun _ h => h.vV)
    (chkB_spec arr Vn VV r ok0 σ hVVeq hE hlen hB hok0)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, by simp [Env.setVar, hV],
      by simp [Env.setVar, hr], by simp [Env.setVar], by
        simp only [Env.setVar]
        simp [flagTo_zero (RowP arr Vn r) ok0 hok0, hok], fun y hy => by
      have hyi : y ≠ "i" := fun h => hy (by simp [AB, h])
      simp [Env.setVar, hyi]⟩
  refine ⟨σ', r', ?_, hI.arrs.trans (by simp [Env.setVar]), hI.out.trans (by simp [Env.setVar]), ?_⟩
  · rw [hI.hok, hi]
  · intro y hy
    rw [hI.fr y hy]

end Lax117284Proofs.Machine.MisCheck

end

/-! ### `Lax117284Proofs.Machine.MisChk` -/

section
/-!
The whole check of the normal form: the size of the classes, the pass over the cells, the parity of
the number of edges, the degree of the vertex `0`, and the pass over the rows.
-/

namespace Lax117284Proofs.Machine.MisChk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.SatOps Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.SatRank (bumpS countP_range_succ)
open Lax117284Proofs.Machine.MisSem Lax117284Proofs.Machine.MisFind Lax117284Proofs.Machine.MisCheck
open Lax117284Proofs.Machine.MisFormat (VM)

variable {B : ℕ}

/-- The first half: the size of the classes, the pass over the cells, and the number of edges. -/
def checkPA : Com :=
  .seq (.assign "ok" (.lit 1))
  (.seq (guard (.lt (.lit 3) (V "nn")))
  (.seq (.assign "cnt" (.lit 0))
  (.seq chkALoop (.assign "EE" (V "cnt")))))

/-- The second half: the parity of the number of edges and the degree of the vertex `0`. -/
def checkPB : Com :=
  .seq (.assign "eh" (.bin .div (V "EE") (.lit 2)))
  (.seq (.assign "em" (.bin .mul (V "eh") (.lit 2)))
  (.seq (guard (.eq (V "EE") (V "em")))
  (.seq (.assign "bs" (.lit 2))
  (.seq (.assign "bd" (V "V"))
  (.seq MisCount.cntCom
  (.seq (.assign "rr" (V "cnt"))
    (impGuard (.lt (.lit 0) (V "V")) (.lt (.lit 0) (V "rr")))))))))

/-- The check. -/
def checkCom : Com := .seq checkPA (.seq checkPB chkBLoop)

/-- The scalars the check assigns. -/
def AK : List String := AA ++ AB ++ ["EE", "eh", "em", "rr"]

/-- Nothing changed but the scalars the check assigns. -/
def KStep (σ σ' : Env) : Prop :=
  σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ ∀ y, y ∉ AK → σ'.vars y = σ.vars y

lemma KStep.trans {σ σ' σ'' : Env} (h : KStep σ σ') (h' : KStep σ' σ'') : KStep σ σ'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, fun y hy => (h'.2.2 y hy).trans (h.2.2 y hy)⟩

lemma KStep.setVar (σ : Env) (z : String) (v : ℕ) (hz : z ∈ AK) : KStep σ (σ.setVar z v) :=
  ⟨rfl, rfl, fun y hy => by
    have : y ≠ z := fun h => hy (h ▸ hz)
    simp [Env.setVar, this]⟩

lemma KStep.ok {σ σ' : Env} {v : ℕ} (h : OkStep σ σ' v) : KStep σ σ' :=
  ⟨h.1, h.2.1, fun y hy => h.2.2.1 y (fun e => hy (by simp [AK, AA, e]))⟩

lemma KStep.of_frame {σ σ' : Env} (X : List String) (hX : ∀ y, y ∈ X → y ∈ AK)
    (ha : σ'.arrs = σ.arrs) (ho : σ'.out = σ.out) (hf : ∀ y, y ∉ X → σ'.vars y = σ.vars y) :
    KStep σ σ' :=
  ⟨ha, ho, fun y hy => hf y (fun h => hy (hX y h))⟩

lemma count2_eq (ns : List ℕ) :
    (List.range (VM ns)).countP (MisCount.onePred ns 2) = rowSum ns 0 := by
  unfold rowSum
  refine List.countP_congr fun x _ => ?_
  unfold MisCount.onePred mat
  simp

/-- The regularity conditions of the machine are those of the source. -/
lemma reg_iff (ns : List ℕ) :
    ((0 < VM ns → 0 < rowSum ns 0) ∧ ∀ w < VM ns, RowP ns (VM ns) (rowSum ns 0) w) ↔ RegM ns := by
  unfold RegM
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h : VM ns = 0
    · exact Or.inl h
    · exact Or.inr ⟨h1 (by omega), fun w hw => (rowP_iff ns w).1 (h2 w hw)⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact ⟨fun h' => by omega, fun w hw => by omega⟩
    · exact ⟨fun _ => h1, fun w hw => (rowP_iff ns w).2 (h2 w hw)⟩

/-- The context every step of the check keeps. -/
def Ctx (arr : List ℕ) (Vn VV n : ℕ) (σ : Env) : Prop :=
  σ.arrs "TK" = arr ∧ σ.vars "V" = Vn ∧ σ.vars "VV" = VV ∧ σ.vars "nn" = n

lemma Ctx.step {arr : List ℕ} {Vn VV n : ℕ} {σ σ' : Env} (h : Ctx arr Vn VV n σ) (hk : KStep σ σ') :
    Ctx arr Vn VV n σ' :=
  ⟨by rw [hk.1]; exact h.1, by rw [hk.2.2 "V" (by decide)]; exact h.2.1,
    by rw [hk.2.2 "VV" (by decide)]; exact h.2.2.1, by rw [hk.2.2 "nn" (by decide)]; exact h.2.2.2⟩

set_option maxHeartbeats 12800000 in
/-- **The first half of the check.** -/
theorem checkPA_run (arr : List ℕ) (Vn VV n : ℕ) (σ : Env) (hVVd : VV = Vn * Vn)
    (hE : ∀ k < VV, arr.getD (2 + k) 0 + 8 < B) (hlen : 2 + VV ≤ arr.length)
    (hB : VV + Vn + n + 40 < B) (hc : Ctx arr Vn VV n σ) :
    ∃ σ', Run B checkPA σ σ' (100 + (304 * VV + 6)) ∧
      σ'.vars "ok" = flagTo (PassV arr Vn n) (if 3 < n then 1 else 0) VV ∧
      σ'.vars "EE" = (List.range VV).countP (qualV arr Vn) ∧ Ctx arr Vn VV n σ' ∧ KStep σ σ' := by
  have hokB : 0 < B := by omega
  have hc0 := hc
  obtain ⟨hA, hV, hVV, hn⟩ := hc
  have s1 := asg_lit (B := B) "ok" 1 σ (by omega)
  set σ1 := σ.setVar "ok" 1 with hσ1
  have k1 : KStep σ σ1 := KStep.setVar σ "ok" 1 (by simp [AK, AA])
  obtain ⟨hA1, hV1, hVV1, hn1⟩ := hc0.step k1
  obtain ⟨σ2, r2, o2⟩ := guard_run (B := B) (.lt (.lit 3) (V "nn")) σ1 (3 < n)
    (cond_lll (B := B) 3 "nn" σ1 n hn1 (by omega) (by omega)) hokB
  have k2 : KStep σ1 σ2 := KStep.ok o2
  have hok2 : σ2.vars "ok" = if 3 < n then 1 else 0 := by
    rw [o2.2.2.2]; simp [hσ1, Env.setVar]
  have s3 := asg_lit (B := B) "cnt" 0 σ2 (by omega)
  set σ3 := σ2.setVar "cnt" 0 with hσ3
  have k3 : KStep σ2 σ3 := KStep.setVar σ2 "cnt" 0 (by simp [AK, AA])
  have hc3 : Ctx arr Vn VV n σ3 := ((hc0.step k1).step k2).step k3
  have hok3 : σ3.vars "ok" = if 3 < n then 1 else 0 := by simp [hσ3, Env.setVar, hok2]
  obtain ⟨σ4, r4, o4, c4, a4, ou4, f4⟩ := chkALoop_run (B := B) arr Vn n VV
    (if 3 < n then 1 else 0) σ3 hVVd hE hlen (by omega) (by split <;> omega) hc3.1 hc3.2.1 hc3.2.2.2
    hc3.2.2.1 hok3 (by simp [hσ3, Env.setVar])
  have k4 : KStep σ3 σ4 := KStep.of_frame AA (fun y hy => by simp [AK, hy]) a4 ou4 f4
  have hc4 : Ctx arr Vn VV n σ4 := hc3.step k4
  have hcnB : σ4.vars "cnt" < B := by
    rw [c4]
    have := List.countP_le_length (p := qualV arr Vn) (l := List.range VV)
    simp at this; omega
  have s5 := asg_var (B := B) "EE" "cnt" σ4 _ rfl hcnB
  set σ5 := σ4.setVar "EE" (σ4.vars "cnt") with hσ5
  have k5 : KStep σ4 σ5 := KStep.setVar σ4 "EE" _ (by simp [AK])
  refine ⟨σ5, (s1.seq (r2.seq (s3.seq (r4.seq s5)))).mono (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, hc4.step k5,
    ((((k1.trans k2).trans k3).trans k4).trans k5)⟩
  · simp [hσ5, Env.setVar, o4]
  · simp [hσ5, Env.setVar, c4]

set_option maxHeartbeats 12800000 in
/-- **The second half of the check.** -/
theorem checkPB_run (arr : List ℕ) (Vn VV n E ok0 : ℕ) (σ : Env) (hVVd : VV = Vn * Vn)
    (hE : ∀ k < VV, arr.getD (2 + k) 0 + 8 < B) (hlen : 2 + VV ≤ arr.length)
    (hB : VV + Vn + n + 40 < B) (hc : Ctx arr Vn VV n σ) (hEle : E ≤ VV) (hEv : σ.vars "EE" = E)
    (hok0 : ok0 ≤ 1) (hok : σ.vars "ok" = ok0) :
    ∃ σ', Run B checkPB σ σ' ((40 + 4) * Vn + 100) ∧
      σ'.vars "ok" = (if (0 < Vn → 0 < (List.range Vn).countP (MisCount.onePred arr 2)) then
        (if E = E / 2 * 2 then ok0 else 0) else 0) ∧
      σ'.vars "rr" = (List.range Vn).countP (MisCount.onePred arr 2) ∧
      σ'.vars "EE" = E ∧ Ctx arr Vn VV n σ' ∧ KStep σ σ' := by
  have hokB : 0 < B := by omega
  have hc0 := hc
  obtain ⟨hA, hV, hVV, hn⟩ := hc
  have hVle : Vn ≤ VV := by
    rcases Nat.eq_zero_or_pos Vn with h | h
    · omega
    · rw [hVVd]; exact Nat.le_mul_of_pos_left _ h
  have s6 := asg_binr (B := B) .div "EE" 2 "eh" σ E hEv (by simp only [Bop.apply_div]; omega)
    (by omega) (by omega)
  simp only [Bop.apply_div] at s6
  set σ6 := σ.setVar "eh" (E / 2) with hσ6
  have k6 : KStep σ σ6 := KStep.setVar σ "eh" _ (by simp [AK])
  have hh6 : σ6.vars "eh" = E / 2 := by simp [hσ6, Env.setVar]
  have s7 := asg_binr (B := B) .mul "eh" 2 "em" σ6 (E / 2) hh6
    (by simp only [Bop.apply_mul]; omega) (by omega) (by omega)
  simp only [Bop.apply_mul] at s7
  set σ7 := σ6.setVar "em" (E / 2 * 2) with hσ7
  have k7 : KStep σ6 σ7 := KStep.setVar σ6 "em" _ (by simp [AK])
  have hE7 : σ7.vars "EE" = E := by simp [hσ7, hσ6, Env.setVar, hEv]
  have hm7 : σ7.vars "em" = E / 2 * 2 := by simp [hσ7, Env.setVar]
  obtain ⟨σ8, r8, o8⟩ := guard_run (B := B) (.eq (V "EE") (V "em")) σ7 (E = E / 2 * 2)
    (condEqD (B := B) "EE" "em" σ7 E (E / 2 * 2) hE7 hm7 (by omega) (by omega)) hokB
  have k8 : KStep σ7 σ8 := KStep.ok o8
  have hok7 : σ7.vars "ok" = ok0 := by simp [hσ7, hσ6, Env.setVar, hok]
  have hok8 : σ8.vars "ok" = if E = E / 2 * 2 then ok0 else 0 := by rw [o8.2.2.2, hok7]
  have hc8 := ((hc0.step k6).step k7).step k8
  have s9 := asg_lit (B := B) "bs" 2 σ8 (by omega)
  set σ9 := σ8.setVar "bs" 2 with hσ9
  have k9 : KStep σ8 σ9 := KStep.setVar σ8 "bs" _ (by simp [AK, AB])
  have hc9 := hc8.step k9
  have s10 := asg_var (B := B) "bd" "V" σ9 Vn hc9.2.1 (by omega)
  set σ10 := σ9.setVar "bd" Vn with hσ10
  have k10 : KStep σ9 σ10 := KStep.setVar σ9 "bd" _ (by simp [AK, AB])
  have hc10 := hc9.step k10
  obtain ⟨σ11, r11, c11, a11, o11, f11⟩ := MisCount.cntCom_run (B := B) arr 2 Vn σ10
    (fun k hk => hE k (by omega)) (by omega) (by omega) hc10.1 (by simp [hσ10, hσ9, Env.setVar])
    (by simp [hσ10, Env.setVar])
  have k11 : KStep σ10 σ11 := KStep.of_frame MisCount.AN (fun y hy => by
    simp only [MisCount.AN, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> simp [AK, AA, AB]) a11 o11 f11
  have hc11 := hc10.step k11
  have hcn11 : σ11.vars "cnt" < B := by
    rw [c11]
    have := List.countP_le_length (p := MisCount.onePred arr 2) (l := List.range Vn)
    simp at this; omega
  have s12 := asg_var (B := B) "rr" "cnt" σ11 _ rfl hcn11
  set σ12 := σ11.setVar "rr" (σ11.vars "cnt") with hσ12
  have k12 : KStep σ11 σ12 := KStep.setVar σ11 "rr" _ (by simp [AK])
  have hc12 := hc11.step k12
  have hrr12 : σ12.vars "rr" = (List.range Vn).countP (MisCount.onePred arr 2) := by
    simp [hσ12, Env.setVar, c11]
  have hV12 : σ12.vars "V" = Vn := hc12.2.1
  have hrB : σ12.vars "rr" < B := by
    rw [hrr12]
    have := List.countP_le_length (p := MisCount.onePred arr 2) (l := List.range Vn)
    simp at this; omega
  obtain ⟨σ13, r13, o13⟩ := impGuard_run (B := B) (.lt (.lit 0) (V "V")) (.lt (.lit 0) (V "rr")) σ12
    (0 < Vn) (0 < (List.range Vn).countP (MisCount.onePred arr 2))
    (by
      have := cond_lll (B := B) 0 "V" σ12 Vn hV12 (by omega) (by omega)
      exact this)
    (cond_lll (B := B) 0 "rr" σ12 _ hrr12 (by omega) (by omega)) hokB
  have k13 : KStep σ12 σ13 := KStep.ok o13
  have hok12 : σ12.vars "ok" = σ8.vars "ok" := by
    simp only [hσ12, Env.setVar, if_neg (show ("ok" ≠ "rr") by decide)]
    rw [f11 "ok" (by simp [MisCount.AN])]
    simp [hσ10, hσ9, Env.setVar]
  have hEE13 : σ13.vars "EE" = E := by
    rw [o13.2.2.1 "EE" (by decide)]
    simp only [hσ12, Env.setVar, if_neg (show ("EE" ≠ "rr") by decide)]
    rw [f11 "EE" (by simp [MisCount.AN])]
    simp only [hσ10, hσ9, Env.setVar, if_neg (show ("EE" ≠ "bd") by decide),
      if_neg (show ("EE" ≠ "bs") by decide)]
    rw [o8.2.2.1 "EE" (by decide), hE7]
  refine ⟨σ13, (s6.seq (s7.seq (r8.seq (s9.seq (s10.seq (r11.seq (s12.seq r13))))))).mono
    (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, hEE13, hc12.step k13,
    (((((((k6.trans k7).trans k8).trans k9).trans k10).trans k11).trans k12).trans k13)⟩
  · rw [o13.2.2.2, hok12, hok8]
  · rw [o13.2.2.1 "rr" (by decide), hrr12]

open Classical in
/-- **The machine's flag is the normal form of the source.** -/
theorem flag_iff (arr : List ℕ) :
    flagTo (RowP arr (VM arr) (rowSum arr 0))
      (if (0 < VM arr → 0 < rowSum arr 0) then
        (if edgeN arr = edgeN arr / 2 * 2 then
          flagTo (PassV arr (VM arr) (nN arr)) (if 3 < nN arr then 1 else 0) (VM arr * VM arr)
         else 0) else 0) (VM arr) = if CondM arr then 1 else 0 := by
  have hle := flagTo_le (RowP arr (VM arr) (rowSum arr 0))
    (if (0 < VM arr → 0 < rowSum arr 0) then
        (if edgeN arr = edgeN arr / 2 * 2 then
          flagTo (PassV arr (VM arr) (nN arr)) (if 3 < nN arr then 1 else 0) (VM arr * VM arr)
         else 0) else 0) (VM arr)
  have key : flagTo (RowP arr (VM arr) (rowSum arr 0))
      (if (0 < VM arr → 0 < rowSum arr 0) then
        (if edgeN arr = edgeN arr / 2 * 2 then
          flagTo (PassV arr (VM arr) (nN arr)) (if 3 < nN arr then 1 else 0) (VM arr * VM arr)
         else 0) else 0) (VM arr) = 1 ↔ CondM arr := by
    rw [flagTo_eq_one]
    have hreg := reg_iff arr
    unfold CondM
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : (0 < VM arr → 0 < rowSum arr 0) ∧ edgeN arr = edgeN arr / 2 * 2 ∧
          flagTo (PassV arr (VM arr) (nN arr)) (if 3 < nN arr then 1 else 0) (VM arr * VM arr) = 1 := by
        by_cases a : (0 < VM arr → 0 < rowSum arr 0)
        · rw [if_pos a] at h1
          by_cases b : edgeN arr = edgeN arr / 2 * 2
          · rw [if_pos b] at h1; exact ⟨a, b, h1⟩
          · rw [if_neg b] at h1; omega
        · rw [if_neg a] at h1; omega
      obtain ⟨a, b, c⟩ := h1'
      rw [flagTo_eq_one] at c
      obtain ⟨c1, c2⟩ := c
      have : 3 < nN arr := by
        by_contra h; rw [if_neg h] at c1; omega
      exact ⟨by omega, c2, hreg.1 ⟨a, h2⟩, by omega⟩
    · rintro ⟨h1, h2, h3, h4⟩
      obtain ⟨a, b⟩ := hreg.2 h3
      refine ⟨?_, b⟩
      rw [if_pos a, if_pos (by omega), flagTo_eq_one]
      exact ⟨by rw [if_pos (by omega)], h2⟩
  by_cases hc : CondM arr
  · rw [if_pos hc]; exact key.2 hc
  · rw [if_neg hc]
    have : ¬ (flagTo (RowP arr (VM arr) (rowSum arr 0))
      (if (0 < VM arr → 0 < rowSum arr 0) then
        (if edgeN arr = edgeN arr / 2 * 2 then
          flagTo (PassV arr (VM arr) (nN arr)) (if 3 < nN arr then 1 else 0) (VM arr * VM arr)
         else 0) else 0) (VM arr) = 1) := fun h => hc (key.1 h)
    omega

/-- The cost of the check. -/
def Kchk (Vn VV : ℕ) : ℕ :=
  (100 + (304 * VV + 6)) + ((40 + 4) * Vn + 100) + (((40 + 4) * Vn + 100 + 4) * Vn + 6) + 10

open Classical in
set_option maxHeartbeats 6400000 in
/-- **The check.** -/
theorem checkCom_run (arr : List ℕ) (σ : Env)
    (hE : ∀ k < VM arr * VM arr, arr.getD (2 + k) 0 + 8 < B)
    (hlen : 2 + VM arr * VM arr ≤ arr.length)
    (hB : VM arr * VM arr + 2 * VM arr + nN arr + 40 < B)
    (hc : Ctx arr (VM arr) (VM arr * VM arr) (nN arr) σ) :
    ∃ σ', Run B checkCom σ σ' (Kchk (VM arr) (VM arr * VM arr)) ∧
      σ'.vars "ok" = (if CondM arr then 1 else 0) ∧ σ'.vars "EE" = edgeN arr ∧
      σ'.vars "rr" = rowSum arr 0 ∧ KStep σ σ' := by
  obtain ⟨σ1, r1, o1, e1, hc1, k1⟩ := checkPA_run (B := B) arr (VM arr) (VM arr * VM arr) (nN arr) σ
    rfl hE hlen (by omega) hc
  have hEle : (List.range (VM arr * VM arr)).countP (qualV arr (VM arr)) ≤ VM arr * VM arr := by
    have := List.countP_le_length (p := qualV arr (VM arr)) (l := List.range (VM arr * VM arr))
    simpa using this
  have hok1 : flagTo (PassV arr (VM arr) (nN arr)) (if 3 < nN arr then 1 else 0)
      (VM arr * VM arr) ≤ 1 := flagTo_le _ _ _
  obtain ⟨σ2, r2, o2, rr2, hEE2, hc2, k2⟩ := checkPB_run (B := B) arr (VM arr) (VM arr * VM arr) (nN arr)
    ((List.range (VM arr * VM arr)).countP (qualV arr (VM arr))) _ σ1 rfl hE hlen (by omega) hc1 hEle
    e1 hok1 o1
  have hrle : (List.range (VM arr)).countP (MisCount.onePred arr 2) ≤ VM arr := by
    have := List.countP_le_length (p := MisCount.onePred arr 2) (l := List.range (VM arr))
    simpa using this
  have hok2 : (if (0 < VM arr → 0 < (List.range (VM arr)).countP (MisCount.onePred arr 2)) then
        (if (List.range (VM arr * VM arr)).countP (qualV arr (VM arr)) =
          (List.range (VM arr * VM arr)).countP (qualV arr (VM arr)) / 2 * 2 then
          flagTo (PassV arr (VM arr) (nN arr)) (if 3 < nN arr then 1 else 0) (VM arr * VM arr)
        else 0) else 0) ≤ 1 := by
    by_cases a : (0 < VM arr → 0 < (List.range (VM arr)).countP (MisCount.onePred arr 2))
    · rw [if_pos a]
      by_cases b : (List.range (VM arr * VM arr)).countP (qualV arr (VM arr)) =
          (List.range (VM arr * VM arr)).countP (qualV arr (VM arr)) / 2 * 2
      · rw [if_pos b]; exact hok1
      · rw [if_neg b]; omega
    · rw [if_neg a]; omega
  obtain ⟨σ3, r3, o3, a3, ou3, f3⟩ := chkBLoop_run (B := B) arr (VM arr) (VM arr * VM arr)
    ((List.range (VM arr)).countP (MisCount.onePred arr 2)) _ σ2 rfl hE hlen (by omega) hok2
    hc2.1 hc2.2.1 rr2 o2
  have k3 : KStep σ2 σ3 := KStep.of_frame AB (fun y hy => by simp [AK, hy]) a3 ou3 f3
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by unfold Kchk; omega), ?_, ?_, ?_, k1.trans (k2.trans k3)⟩
  · rw [o3, ← flag_iff arr, count2_eq]
    rfl
  · rw [f3 "EE" (by decide), hEE2]; rfl
  · rw [f3 "rr" (by decide), rr2, count2_eq]

end Lax117284Proofs.Machine.MisChk

end

/-! ### `Lax117284Proofs.Machine.MisJob` -/

section
/-!
The processing time and the due date of a job of the constructed instance, as a command: the case
analysis of the construction on the day and the client.
-/

namespace Lax117284Proofs.Machine.MisJob

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.MisBlk Lax117284Proofs.Machine.MisSem
open Lax117284Proofs.Machine.MisFormat (VM)

variable {B : ℕ}

abbrev V (s : String) : Expr := .var s
abbrev lit (n : ℕ) : Expr := .lit n
abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev div (e f : Expr) : Expr := .bin .div e f

/-- The processing time and the due date, computed independently. -/
def pdCom (e1 e2 : Expr) : Com := .seq (.assign "pv" e1) (.assign "dv" e2)

/-- The scalars a job assigns, apart from those of the scans it runs. -/
def AJ : List String := ["pv", "dv", "vb", "va", "ee"]

/-- Nothing changed but the scalars a job assigns. -/
def JStep (X : List String) (σ σ' : Env) : Prop :=
  σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ ∀ y, y ∉ X → σ'.vars y = σ.vars y

lemma JStep.trans {X} {σ σ' σ'' : Env} (h : JStep X σ σ') (h' : JStep X σ' σ'') : JStep X σ σ'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, fun y hy => (h'.2.2 y hy).trans (h.2.2 y hy)⟩

lemma JStep.setVar {X} (σ : Env) (z : String) (v : ℕ) (hz : z ∈ X) : JStep X σ (σ.setVar z v) :=
  ⟨rfl, rfl, fun y hy => by
    have : y ≠ z := fun h => hy (h ▸ hz)
    simp [Env.setVar, this]⟩

lemma JStep.mono {X Y} (hXY : ∀ y, y ∈ X → y ∈ Y) {σ σ' : Env} (h : JStep X σ σ') : JStep Y σ σ' :=
  ⟨h.1, h.2.1, fun y hy => h.2.2 y (fun hx => hy (hXY y hx))⟩

/-- **The two assignments of a job.** -/
theorem pd_run (e1 e2 : Expr) (σ : Env) (h1 : small B σ e1)
    (h2 : small B (σ.setVar "pv" (den σ e1)) e2) :
    ∃ σ', Run B (pdCom e1 e2) σ σ' (2 + e1.size + e2.size) ∧ σ'.vars "pv" = den σ e1 ∧
      σ'.vars "dv" = den (σ.setVar "pv" (den σ e1)) e2 ∧ JStep AJ σ σ' := by
  have r1 := asgE (B := B) "pv" e1 σ h1
  have r2 := asgE (B := B) "dv" e2 (σ.setVar "pv" (den σ e1)) h2
  refine ⟨_, (r1.seq r2).mono (by omega), ?_, ?_, ?_⟩
  · simp [Env.setVar]
  · simp [Env.setVar]
  · exact (JStep.setVar σ "pv" _ (by simp [AJ])).trans (JStep.setVar _ "dv" _ (by simp [AJ]))

/-- What the job commands read. -/
structure JC (ns : List ℕ) (i c : ℕ) (σ : Env) : Prop where
  vdi : σ.vars "di" = i
  vcc : σ.vars "cc" = c
  vnn : σ.vars "nn" = nN ns
  vlc : σ.vars "lc" = lN ns
  vV : σ.vars "V" = VM ns
  vdg : σ.vars "dg" = degN ns
  vS2 : σ.vars "S2" = spanN ns
  vB3 : σ.vars "B3" = 3 + lN ns
  vB4 : σ.vars "B4" = 3 + lN ns + VM ns
  vdn : σ.vars "dn" = degN ns * nN ns
  vn1 : σ.vars "nn1" = nN ns + 1
  vLB : σ.vars "LB" = lN ns * (nN ns + 1)

/-- The number of the vertex and the selection clients depends on the vertex day. -/
def vertexCom : Com :=
  .ite (.eq (V "cc") (lit 0)) (pdCom (V "S2") (add (V "dg") (V "S2")))
    (.ite (.eq (V "cc") (add (V "B3") (add (mul (V "vb") (V "nn")) (V "va"))))
      (pdCom (V "dg") (V "dg"))
      (.ite (.eq (V "cc") (add (lit 3) (V "vb")))
        (pdCom (V "dg") (V "dg"))
        (pdCom (lit 1) (add (V "dg") (V "cc")))))

/-- The words of the magnitude of every value a job computes. -/
def Mag (ns : List ℕ) : ℕ := 2 * spanN ns + degN ns * nN ns + degN ns + 100

lemma VM_le_span (ns : List ℕ) : VM ns ≤ spanN ns := by
  unfold spanN; omega

lemma lN_le_span (ns : List ℕ) : lN ns ≤ spanN ns := by
  unfold spanN; omega

lemma span_ge (ns : List ℕ) : 2 + lN ns + VM ns ≤ spanN ns := by
  unfold spanN; omega

lemma span_eq (ns : List ℕ) : spanN ns = 2 + lN ns + VM ns + VM ns * degN ns := rfl

lemma Vdg_le (ns : List ℕ) : VM ns * degN ns ≤ spanN ns := by
  unfold spanN; omega

lemma cl_le (ns : List ℕ) : clN ns = spanN ns + 1 := by unfold clN spanN; omega

set_option maxHeartbeats 3200000 in
/-- **A job of a vertex day.** -/
theorem vertexCom_run (ns : List ℕ) (i c b a : ℕ) (σ : Env) (hj : JC ns i c σ)
    (hb : σ.vars "vb" = b) (ha : σ.vars "va" = a) (han : a < nN ns) (hw0 : b * nN ns + a < VM ns)
    (hcl : c < clN ns) (hM : Mag ns < B) :
    ∃ σ', Run B vertexCom σ σ' 40 ∧
      σ'.vars "pv" = (vertexDayN ns (b * nN ns + a) c).1 ∧
      σ'.vars "dv" = (vertexDayN ns (b * nN ns + a) c).2 ∧ JStep AJ σ σ' := by
  have hsp := VM_le_span ns
  have hlc := lN_le_span ns
  have hcls := cl_le ns
  have hspg := span_ge ns
  unfold Mag at hM
  have hdiv : (b * nN ns + a) / nN ns = b := by
    have hn : 0 < nN ns := by omega
    rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt han, Nat.add_zero]
  obtain ⟨hdi, hcc, hnn, hlc', hV, hdg, hS2, hB3, hB4, hdn, hn1, hLB⟩ := hj
  have hdg1 : 1 ≤ degN ns := by unfold degN; omega
  have hbn : b * nN ns ≤ b * nN ns + a := by omega
  have hbb : b ≤ b * nN ns := Nat.le_mul_of_pos_right _ (by omega)
  have hnn_le : nN ns ≤ degN ns * nN ns := Nat.le_mul_of_pos_left _ hdg1
  have small_cc : small B σ (V "cc") := by simp [small, hcc]; omega
  have small0 : small B σ (lit 0) := by simp [small]; omega
  by_cases h0 : c = 0
  · have hT : (Cond.eq (V "cc") (lit 0)).evalB B σ = some true :=
      condEq_true _ _ σ small_cc small0 (by simp [den, hcc, h0])
    obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (V "S2") (add (V "dg") (V "S2")) σ
      (by simp [small, hS2]; omega) (by simp [small, den, Env.setVar, hS2, hdg]; omega)
    refine ⟨σ', (Run.ite_true hT r).mono (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
    · rw [e1]; unfold vertexDayN; rw [if_pos h0]; simp [den, hS2]
    · rw [e2]; unfold vertexDayN; rw [if_pos h0]; simp [den, Env.setVar, hS2, hdg]
  · have hF : (Cond.eq (V "cc") (lit 0)).evalB B σ = some false :=
      condEq_false _ _ σ small_cc small0 (by simp [den, hcc]; omega)
    have hsm1 : small B σ (add (V "B3") (add (mul (V "vb") (V "nn")) (V "va"))) := by
      simp [small, den, hB3, hb, hnn, ha]
      omega
    by_cases h1 : c = 3 + lN ns + (b * nN ns + a)
    · have hT : (Cond.eq (V "cc") (add (V "B3") (add (mul (V "vb") (V "nn")) (V "va")))).evalB B σ
          = some true := condEq_true _ _ σ small_cc hsm1 (by simp [den, hcc, hB3, hb, hnn, ha]; omega)
      obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (V "dg") (V "dg") σ
        (by simp [small, hdg]; omega) (by simp [small, den, Env.setVar, hdg]; omega)
      refine ⟨σ', (Run.ite_false hF (Run.ite_true hT r)).mono
        (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
      · rw [e1]; unfold vertexDayN; rw [if_neg h0, if_pos (Or.inl h1)]; simp [den, hdg]
      · rw [e2]; unfold vertexDayN; rw [if_neg h0, if_pos (Or.inl h1)]
        simp [den, Env.setVar, hdg]
    · have hF1 : (Cond.eq (V "cc") (add (V "B3") (add (mul (V "vb") (V "nn")) (V "va")))).evalB B σ
          = some false := condEq_false _ _ σ small_cc hsm1 (by simp [den, hcc, hB3, hb, hnn, ha]; omega)
      have hsm2 : small B σ (add (lit 3) (V "vb")) := by
        simp [small, den, hb]
        omega
      by_cases h2 : c = 3 + b
      · have hT : (Cond.eq (V "cc") (add (lit 3) (V "vb"))).evalB B σ = some true :=
          condEq_true _ _ σ small_cc hsm2 (by simp [den, hcc, hb]; omega)
        obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (V "dg") (V "dg") σ
          (by simp [small, hdg]; omega) (by simp [small, den, Env.setVar, hdg]; omega)
        refine ⟨σ', (Run.ite_false hF (Run.ite_false hF1 (Run.ite_true hT r))).mono
          (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
        · rw [e1]; unfold vertexDayN; rw [if_neg h0, if_pos (Or.inr (by rw [hdiv]; exact h2))]
          simp [den, hdg]
        · rw [e2]; unfold vertexDayN; rw [if_neg h0, if_pos (Or.inr (by rw [hdiv]; exact h2))]
          simp [den, Env.setVar, hdg]
      · have hF2 : (Cond.eq (V "cc") (add (lit 3) (V "vb"))).evalB B σ = some false :=
          condEq_false _ _ σ small_cc hsm2 (by simp [den, hcc, hb]; omega)
        obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 1) (add (V "dg") (V "cc")) σ
          (by simp [small]; omega)
          (by simp [small, den, Env.setVar, hdg, hcc]; omega)
        refine ⟨σ', (Run.ite_false hF (Run.ite_false hF1 (Run.ite_false hF2 r))).mono
          (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
        · rw [e1]; unfold vertexDayN
          rw [if_neg h0, if_neg (by rw [hdiv]; omega)]; simp [den]
        · rw [e2]; unfold vertexDayN
          rw [if_neg h0, if_neg (by rw [hdiv]; omega)]; simp [den, Env.setVar, hdg, hcc]

/-- The jobs of a validation day: the vertex clients of the colour and the edge clients of its
vertices. -/
def validNext : Com :=
  .ite (.lt (V "cc") (V "B4")) (pdCom (lit 1) (add (V "dn") (V "cc")))
    (.ite (.eq (div (div (sub (V "cc") (V "B4")) (V "dg")) (V "nn")) (V "vb"))
      (pdCom (lit 1)
        (add (add (mul (V "dg") (sub (div (sub (V "cc") (V "B4")) (V "dg"))
            (mul (div (div (sub (V "cc") (V "B4")) (V "dg")) (V "nn")) (V "nn"))))
          (sub (sub (V "cc") (V "B4")) (mul (div (sub (V "cc") (V "B4")) (V "dg")) (V "dg"))))
          (lit 1)))
      (pdCom (lit 1) (add (V "dn") (V "cc"))))

def validCom : Com :=
  .ite (.eq (V "cc") (lit 0)) (pdCom (V "S2") (add (V "dn") (V "S2")))
    (.ite (.lt (V "cc") (V "B3")) validNext
      (.ite (.lt (V "cc") (V "B4"))
        (.ite (.eq (div (sub (V "cc") (V "B3")) (V "nn")) (V "vb"))
          (pdCom (V "dg")
            (mul (V "dg") (add (sub (sub (V "cc") (V "B3"))
              (mul (div (sub (V "cc") (V "B3")) (V "nn")) (V "nn"))) (lit 1))))
          validNext)
        validNext))

lemma mod_sub (x n : ℕ) : x - x / n * n = x % n := MisFind.mod_eq_sub x n

set_option maxHeartbeats 6400000 in
/-- **The jobs of a validation day after the vertex clients.** -/
theorem validNext_run (ns : List ℕ) (i c b : ℕ) (σ : Env) (hj : JC ns i c σ)
    (hb : σ.vars "vb" = b) (hbl : b < lN ns) (hn0 : 0 < nN ns) (hcl : c < clN ns)
    (hM : Mag ns < B) :
    ∃ σ', Run B validNext σ σ' 60 ∧ σ'.vars "pv" = 1 ∧
      σ'.vars "dv" = (if 3 + lN ns + VM ns ≤ c ∧
          ((c - (3 + lN ns + VM ns)) / degN ns) / nN ns = b then
        degN ns * (((c - (3 + lN ns + VM ns)) / degN ns) % nN ns) +
          (c - (3 + lN ns + VM ns)) % degN ns + 1
      else degN ns * nN ns + c) ∧ JStep AJ σ σ' := by
  have hsp := VM_le_span ns
  have hlc := lN_le_span ns
  have hcls := cl_le ns
  have hspg := span_ge ns
  unfold Mag at hM
  obtain ⟨hdi, hcc, hnn, hlc', hV, hdg, hS2, hB3, hB4, hdn, hn1, hLB⟩ := hj
  have hdg1 : 1 ≤ degN ns := by unfold degN; omega
  have hnn_le : nN ns ≤ degN ns * nN ns := Nat.le_mul_of_pos_left _ hdg1
  have small_cc : small B σ (V "cc") := by simp [small, hcc]; omega
  have hsm3 : small B σ (add (V "dn") (V "cc")) := by simp [small, den, hdn, hcc]; omega
  have hsm1 : small B σ (lit 1) := by simp [small]; omega
  have hc4 : small B σ (V "B4") := by simp [small, hB4]; omega
  by_cases h4 : c < 3 + lN ns + VM ns
  · have hT : (Cond.lt (V "cc") (V "B4")).evalB B σ = some true :=
      condLt_true _ _ σ small_cc hc4 (by simp [den, hcc, hB4]; omega)
    obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 1) (add (V "dn") (V "cc")) σ hsm1
      (by simp [small, den, Env.setVar, hdn, hcc]; omega)
    refine ⟨σ', (Run.ite_true hT r).mono (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
    · rw [e1]; rfl
    · rw [e2, if_neg (by omega)]; simp [den, Env.setVar, hdn, hcc]
  · have hF : (Cond.lt (V "cc") (V "B4")).evalB B σ = some false :=
      condLt_false _ _ σ small_cc hc4 (by simp [den, hcc, hB4]; omega)
    obtain ⟨m2, hm2⟩ : ∃ m2, m2 = c - (3 + lN ns + VM ns) := ⟨_, rfl⟩
    obtain ⟨q2, hq2⟩ : ∃ q2, q2 = m2 / degN ns := ⟨_, rfl⟩
    obtain ⟨q3, hq3⟩ : ∃ q3, q3 = q2 / nN ns := ⟨_, rfl⟩
    have hq2m : q2 ≤ m2 := by rw [hq2]; exact Nat.div_le_self _ _
    have hq3q : q3 ≤ q2 := by rw [hq3]; exact Nat.div_le_self _ _
    have hq3n : q3 * nN ns ≤ q2 := by rw [hq3]; exact Nat.div_mul_le_self _ _
    have hq2d : q2 * degN ns ≤ m2 := by rw [hq2]; exact Nat.div_mul_le_self _ _
    have hmodn : q2 - q3 * nN ns < nN ns := by
      rw [hq3, mod_sub]; exact Nat.mod_lt _ hn0
    have hmodd : m2 - q2 * degN ns < degN ns := by
      rw [hq2, mod_sub]; exact Nat.mod_lt _ (by omega)
    have hprod : degN ns * (q2 - q3 * nN ns) ≤ degN ns * nN ns := Nat.mul_le_mul_left _ hmodn.le
    have hm2c : m2 ≤ c := by omega
    have hsm3' : small B σ (div (div (sub (V "cc") (V "B4")) (V "dg")) (V "nn")) := by
      simp [small, den, hcc, hB4, hdg, hnn]
      rw [← hm2, ← hq2, ← hq3]
      omega
    have hsmb : small B σ (V "vb") := by simp [small, hb]; omega
    have hden3 : den σ (div (div (sub (V "cc") (V "B4")) (V "dg")) (V "nn")) = q3 := by
      simp [den, hcc, hB4, hdg, hnn]; rw [← hm2, ← hq2, ← hq3]
    by_cases h3 : q3 = b
    · have hT3 : (Cond.eq (div (div (sub (V "cc") (V "B4")) (V "dg")) (V "nn")) (V "vb")).evalB B σ
          = some true := condEq_true _ _ σ hsm3' hsmb (by rw [hden3]; simp [den, hb, h3])
      obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 1) (add (add (mul (V "dg") (sub (div (sub
        (V "cc") (V "B4")) (V "dg")) (mul (div (div (sub (V "cc") (V "B4")) (V "dg")) (V "nn"))
        (V "nn")))) (sub (sub (V "cc") (V "B4")) (mul (div (sub (V "cc") (V "B4")) (V "dg"))
        (V "dg")))) (lit 1)) σ hsm1
        (by
          simp [small, den, Env.setVar, hcc, hB4, hdg, hnn]
          rw [← hm2, ← hq2, ← hq3]
          omega)
      refine ⟨σ', (Run.ite_false hF (Run.ite_true hT3 r)).mono
        (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
      · rw [e1]; rfl
      · rw [e2]
        simp [den, Env.setVar, hcc, hB4, hdg, hnn]
        rw [← hm2, ← hq2, ← hq3, if_pos ⟨by omega, h3⟩]
        rw [hq3, hq2, mod_sub, mod_sub]
    · have hF3 : (Cond.eq (div (div (sub (V "cc") (V "B4")) (V "dg")) (V "nn")) (V "vb")).evalB B σ
          = some false := condEq_false _ _ σ hsm3' hsmb (by rw [hden3]; simp [den, hb, h3])
      obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 1) (add (V "dn") (V "cc")) σ hsm1
        (by simp [small, den, Env.setVar, hdn, hcc]; omega)
      refine ⟨σ', (Run.ite_false hF (Run.ite_false hF3 r)).mono
        (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
      · rw [e1]; rfl
      · rw [e2, if_neg (by
          rintro ⟨-, h⟩
          apply h3
          rw [hq3, hq2, hm2]; exact h)]
        simp [den, Env.setVar, hdn, hcc]

set_option maxHeartbeats 6400000 in
/-- **A job of a validation day.** -/
theorem validCom_run (ns : List ℕ) (i c b : ℕ) (σ : Env) (hj : JC ns i c σ)
    (hb : σ.vars "vb" = b) (hbl : b < lN ns) (hn0 : 0 < nN ns) (hcl : c < clN ns)
    (hM : Mag ns < B) :
    ∃ σ', Run B validCom σ σ' 80 ∧
      σ'.vars "pv" = (validationDayN ns b c).1 ∧
      σ'.vars "dv" = (validationDayN ns b c).2 ∧ JStep AJ σ σ' := by
  have hsp := VM_le_span ns
  have hlc := lN_le_span ns
  have hcls := cl_le ns
  have hspg := span_ge ns
  unfold Mag at hM
  have hj0 := hj
  obtain ⟨hdi, hcc, hnn, hlc', hV, hdg, hS2, hB3, hB4, hdn, hn1, hLB⟩ := hj
  have hdg1 : 1 ≤ degN ns := by unfold degN; omega
  have hnn_le : nN ns ≤ degN ns * nN ns := Nat.le_mul_of_pos_left _ hdg1
  have small_cc : small B σ (V "cc") := by simp [small, hcc]; omega
  have small0 : small B σ (lit 0) := by simp [small]; omega
  have hc3 : small B σ (V "B3") := by simp [small, hB3]; omega
  have hc4 : small B σ (V "B4") := by simp [small, hB4]; omega
  unfold validationDayN
  by_cases h0 : c = 0
  · have hT : (Cond.eq (V "cc") (lit 0)).evalB B σ = some true :=
      condEq_true _ _ σ small_cc small0 (by simp [den, hcc, h0])
    obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (V "S2") (add (V "dn") (V "S2")) σ
      (by simp [small, hS2]; omega)
      (by simp [small, den, Env.setVar, hS2, hdn]; omega)
    refine ⟨σ', (Run.ite_true hT r).mono (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
    · rw [e1, if_pos h0]; simp [den, hS2]
    · rw [e2, if_pos h0]; simp [den, Env.setVar, hS2, hdn]
  · have hF : (Cond.eq (V "cc") (lit 0)).evalB B σ = some false :=
      condEq_false _ _ σ small_cc small0 (by simp [den, hcc]; omega)
    rw [if_neg h0]
    obtain ⟨σn, r0, e10, e20, st0⟩ := validNext_run (B := B) ns i c b σ hj0 hb hbl hn0 hcl hM
    by_cases h3 : c < 3 + lN ns
    · have hT : (Cond.lt (V "cc") (V "B3")).evalB B σ = some true :=
        condLt_true _ _ σ small_cc hc3 (by simp [den, hcc, hB3]; omega)
      refine ⟨_, (Run.ite_false hF (Run.ite_true hT r0)).mono
        (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st0⟩
      · rw [e10, if_neg (by omega), if_neg (by omega)]
      · rw [e20, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · have hF3 : (Cond.lt (V "cc") (V "B3")).evalB B σ = some false :=
        condLt_false _ _ σ small_cc hc3 (by simp [den, hcc, hB3]; omega)
      by_cases h4 : c < 3 + lN ns + VM ns
      · have hT4 : (Cond.lt (V "cc") (V "B4")).evalB B σ = some true :=
          condLt_true _ _ σ small_cc hc4 (by simp [den, hcc, hB4]; omega)
        obtain ⟨m1, hm1⟩ : ∃ m1, m1 = c - (3 + lN ns) := ⟨_, rfl⟩
        obtain ⟨q1, hq1⟩ : ∃ q1, q1 = m1 / nN ns := ⟨_, rfl⟩
        have hq1m : q1 ≤ m1 := by rw [hq1]; exact Nat.div_le_self _ _
        have hq1n : q1 * nN ns ≤ m1 := by rw [hq1]; exact Nat.div_mul_le_self _ _
        have hmodn : m1 - q1 * nN ns < nN ns := by
          rw [hq1, mod_sub]; exact Nat.mod_lt _ hn0
        have hprod : degN ns * (m1 - q1 * nN ns + 1) ≤ degN ns * nN ns :=
          Nat.mul_le_mul_left _ (by omega)
        have hsm1 : small B σ (div (sub (V "cc") (V "B3")) (V "nn")) := by
          simp [small, den, hcc, hB3, hnn]; rw [← hm1, ← hq1]; omega
        have hsmb : small B σ (V "vb") := by simp [small, hb]; omega
        have hden1 : den σ (div (sub (V "cc") (V "B3")) (V "nn")) = q1 := by
          simp [den, hcc, hB3, hnn]; rw [← hm1, ← hq1]
        by_cases h5 : q1 = b
        · have hT5 : (Cond.eq (div (sub (V "cc") (V "B3")) (V "nn")) (V "vb")).evalB B σ
              = some true := condEq_true _ _ σ hsm1 hsmb (by rw [hden1]; simp [den, hb, h5])
          obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (V "dg") (mul (V "dg") (add (sub (sub (V "cc")
            (V "B3")) (mul (div (sub (V "cc") (V "B3")) (V "nn")) (V "nn"))) (lit 1))) σ
            (by simp [small, hdg]; omega)
            (by
              simp [small, den, Env.setVar, hcc, hB3, hdg, hnn]
              rw [← hm1, ← hq1]
              omega)
          refine ⟨σ', (Run.ite_false hF (Run.ite_false hF3 (Run.ite_true hT4
            (Run.ite_true hT5 r)))).mono (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
          · rw [e1, if_pos ⟨by omega, h4, by rw [← hm1, ← hq1]; exact h5⟩]; simp [den, hdg]
          · rw [e2, if_pos ⟨by omega, h4, by rw [← hm1, ← hq1]; exact h5⟩]
            simp [den, Env.setVar, hcc, hB3, hdg, hnn]
            rw [← hm1, ← hq1, hq1, mod_sub]
            exact Or.inl rfl
        · have hF5 : (Cond.eq (div (sub (V "cc") (V "B3")) (V "nn")) (V "vb")).evalB B σ
              = some false := condEq_false _ _ σ hsm1 hsmb (by rw [hden1]; simp [den, hb, h5])
          refine ⟨_, (Run.ite_false hF (Run.ite_false hF3 (Run.ite_true hT4
            (Run.ite_false hF5 r0)))).mono (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st0⟩
          · rw [e10, if_neg (by
              rintro ⟨-, -, h⟩; apply h5; rw [hq1, hm1]; exact h), if_neg (by omega)]
          · rw [e20, if_neg (by omega), if_neg (by
              rintro ⟨-, -, h⟩; apply h5; rw [hq1, hm1]; exact h), if_neg (by omega)]
      · have hF4 : (Cond.lt (V "cc") (V "B4")).evalB B σ = some false :=
          condLt_false _ _ σ small_cc hc4 (by simp [den, hcc, hB4]; omega)
        have hnot : ¬ (3 + lN ns ≤ c ∧ c < 3 + lN ns + VM ns ∧ (c - (3 + lN ns)) / nN ns = b) :=
          fun h => h4 h.2.1
        refine ⟨_, (Run.ite_false hF (Run.ite_false hF3 (Run.ite_false hF4 r0))).mono
          (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st0⟩
        · rw [e10, if_neg hnot]; split_ifs <;> rfl
        · rw [e20, if_neg hnot]; split_ifs <;> rfl

/-! ### The edge days -/

/-- The neighbours of a vertex before another, as a count over the array. -/
lemma idx_eq (ns : List ℕ) (w w' : ℕ) :
    (List.range w').countP (MisCount.onePred ns (2 + w * VM ns)) = idxN ns w w' := by
  unfold idxN
  refine List.countP_congr fun x _ => ?_
  unfold MisCount.onePred mat
  rw [Nat.add_assoc]

/-- **The endpoints of an edge lie among the vertices.** -/
lemma edge_lt (ns : List ℕ) (e : ℕ) (he : e < edgeN ns) :
    ((edgeCellsN ns).getD e (0, 0)).1 < VM ns ∧ ((edgeCellsN ns).getD e (0, 0)).2 < VM ns := by
  have hl : e < (edgeCellsN ns).length := by
    have : (edgeCellsN ns).length = edgeN ns := by
      unfold edgeCellsN edgeN
      rw [List.length_map, List.countP_eq_length_filter]
    omega
  have hmem := List.getElem_mem hl
  rw [← List.getD_eq_getElem _ (0, 0) hl] at hmem
  generalize (edgeCellsN ns).getD e (0, 0) = q at hmem ⊢
  have hmem2 : q ∈ ((List.range (VM ns * VM ns)).filter (qualE ns)).map
      (fun t => (t / VM ns, t % VM ns)) := hmem
  obtain ⟨t, ht, hteq⟩ := List.mem_map.mp hmem2
  obtain ⟨ht1, -⟩ := List.mem_filter.mp ht
  obtain ⟨-, h1, h2⟩ := cell_split ns t (List.mem_range.mp ht1)
  rw [← hteq]
  exact ⟨h1, h2⟩

/-- The clients of an edge day, once the endpoints of the edge and the positions of each among the
neighbours of the other are known. -/
def edgeDisp : Com :=
  .ite (.eq (V "cc") (lit 0)) (pdCom (V "S2") (add (lit 3) (V "S2")))
    (.ite (.eq (V "cc") (lit 2)) (pdCom (lit 2) (lit 2))
      (.ite (.eq (V "cc") (lit 1)) (pdCom (lit 2) (lit 3))
        (.ite (.eq (V "cc") (add (add (V "B4") (mul (V "fw") (V "dg"))) (V "k1")))
          (pdCom (lit 1) (lit 3))
          (.ite (.eq (V "cc") (add (add (V "B4") (mul (V "fw2") (V "dg"))) (V "k2")))
            (pdCom (lit 1) (lit 1))
            (pdCom (lit 1) (add (lit 3) (V "cc")))))))

/-- The edge day of the edge from `fw` to `fw2`. -/
def edgeCom : Com :=
  .seq (.assign "e" (sub (V "di") (V "LB")))
  (.seq MisFind.findCom
  (.seq (.assign "bs" (add (lit 2) (mul (V "fw") (V "V"))))
  (.seq (.assign "bd" (V "fw2"))
  (.seq MisCount.cntCom
  (.seq (.assign "k1" (V "cnt"))
  (.seq (.assign "bs" (add (lit 2) (mul (V "fw2") (V "V"))))
  (.seq (.assign "bd" (V "fw"))
  (.seq MisCount.cntCom
  (.seq (.assign "k2" (V "cnt")) edgeDisp)))))))))

lemma idxN_le (ns : List ℕ) (w w' : ℕ) : idxN ns w w' ≤ w' := by
  unfold idxN
  have := List.countP_le_length (p := fun x => decide (mat ns w x = 1)) (l := List.range w')
  simpa using this

set_option maxHeartbeats 6400000 in
/-- **The clients of an edge day.** -/
theorem edgeDisp_run (ns : List ℕ) (i c w w' : ℕ) (σ : Env) (hj : JC ns i c σ)
    (hfw : σ.vars "fw" = w) (hfw2 : σ.vars "fw2" = w') (hk1 : σ.vars "k1" = idxN ns w w')
    (hk2 : σ.vars "k2" = idxN ns w' w) (hw : w < VM ns) (hw' : w' < VM ns)
    (hcl : c < clN ns) (hM : Mag ns < B) :
    ∃ σ', Run B edgeDisp σ σ' 60 ∧ σ'.vars "pv" = (edgeDayN ns w w' c).1 ∧
      σ'.vars "dv" = (edgeDayN ns w w' c).2 ∧ JStep AJ σ σ' := by
  have hsp := VM_le_span ns
  have hlc := lN_le_span ns
  have hcls := cl_le ns
  have hspg := span_ge ns
  have hVdg := Vdg_le ns
  have hspe := span_eq ns
  unfold Mag at hM
  obtain ⟨hdi, hcc, hnn, hlc', hV, hdg, hS2, hB3, hB4, hdn, hn1, hLB⟩ := hj
  have hdg1 : 1 ≤ degN ns := by unfold degN; omega
  have hi1 := idxN_le ns w w'
  have hi2 := idxN_le ns w' w
  have hwd : w * degN ns ≤ VM ns * degN ns := Nat.mul_le_mul_right _ hw.le
  have hw'd : w' * degN ns ≤ VM ns * degN ns := Nat.mul_le_mul_right _ hw'.le
  have small_cc : small B σ (V "cc") := by simp [small, hcc]; omega
  have sm0 : small B σ (lit 0) := by simp [small]; omega
  have sm1 : small B σ (lit 1) := by simp [small]; omega
  have sm2 : small B σ (lit 2) := by simp [small]; omega
  have sm3 : small B σ (lit 3) := by simp [small]; omega
  have hinc1 : small B σ (add (add (V "B4") (mul (V "fw") (V "dg"))) (V "k1")) := by
    simp [small, den, hB4, hfw, hdg, hk1]; omega
  have hinc2 : small B σ (add (add (V "B4") (mul (V "fw2") (V "dg"))) (V "k2")) := by
    simp [small, den, hB4, hfw2, hdg, hk2]; omega
  unfold edgeDayN incIdN
  by_cases h0 : c = 0
  · have hT : (Cond.eq (V "cc") (lit 0)).evalB B σ = some true :=
      condEq_true _ _ σ small_cc sm0 (by simp [den, hcc, h0])
    obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (V "S2") (add (lit 3) (V "S2")) σ
      (by simp [small, hS2]; omega) (by simp [small, den, Env.setVar, hS2]; omega)
    refine ⟨σ', (Run.ite_true hT r).mono (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
    · rw [e1, if_pos h0]; simp [den, hS2]
    · rw [e2, if_pos h0]; simp [den, Env.setVar, hS2]
  · have hF0 : (Cond.eq (V "cc") (lit 0)).evalB B σ = some false :=
      condEq_false _ _ σ small_cc sm0 (by simp [den, hcc]; omega)
    by_cases h2 : c = 2
    · have hT : (Cond.eq (V "cc") (lit 2)).evalB B σ = some true :=
        condEq_true _ _ σ small_cc sm2 (by simp [den, hcc, h2])
      obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 2) (lit 2) σ sm2
        (by simp [small]; omega)
      refine ⟨σ', (Run.ite_false hF0 (Run.ite_true hT r)).mono
        (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
      · rw [e1, if_neg h0, if_pos h2]; simp [den]
      · rw [e2, if_neg h0, if_pos h2]; simp [den, Env.setVar]
    · have hF2 : (Cond.eq (V "cc") (lit 2)).evalB B σ = some false :=
        condEq_false _ _ σ small_cc sm2 (by simp [den, hcc]; omega)
      by_cases h1 : c = 1
      · have hT : (Cond.eq (V "cc") (lit 1)).evalB B σ = some true :=
          condEq_true _ _ σ small_cc sm1 (by simp [den, hcc, h1])
        obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 2) (lit 3) σ sm2
          (by simp [small]; omega)
        refine ⟨σ', (Run.ite_false hF0 (Run.ite_false hF2 (Run.ite_true hT r))).mono
          (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
        · rw [e1, if_neg h0, if_neg h2, if_pos h1]; simp [den]
        · rw [e2, if_neg h0, if_neg h2, if_pos h1]; simp [den, Env.setVar]
      · have hF1 : (Cond.eq (V "cc") (lit 1)).evalB B σ = some false :=
          condEq_false _ _ σ small_cc sm1 (by simp [den, hcc]; omega)
        by_cases h3 : c = 3 + lN ns + VM ns + w * degN ns + idxN ns w w'
        · have hT : (Cond.eq (V "cc") (add (add (V "B4") (mul (V "fw") (V "dg"))) (V "k1"))).evalB B σ
              = some true := condEq_true _ _ σ small_cc hinc1 (by
                simp [den, hcc, hB4, hfw, hdg, hk1]; omega)
          obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 1) (lit 3) σ sm1
            (by simp [small]; omega)
          refine ⟨σ', (Run.ite_false hF0 (Run.ite_false hF2 (Run.ite_false hF1
            (Run.ite_true hT r)))).mono (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
          · rw [e1, if_neg h0, if_neg h2, if_neg h1, if_pos h3]; simp [den]
          · rw [e2, if_neg h0, if_neg h2, if_neg h1, if_pos h3]; simp [den, Env.setVar]
        · have hF3 : (Cond.eq (V "cc") (add (add (V "B4") (mul (V "fw") (V "dg"))) (V "k1"))).evalB
              B σ = some false := condEq_false _ _ σ small_cc hinc1 (by
                simp [den, hcc, hB4, hfw, hdg, hk1]; omega)
          by_cases h4 : c = 3 + lN ns + VM ns + w' * degN ns + idxN ns w' w
          · have hT : (Cond.eq (V "cc") (add (add (V "B4") (mul (V "fw2") (V "dg"))) (V "k2"))).evalB
                B σ = some true := condEq_true _ _ σ small_cc hinc2 (by
                  simp [den, hcc, hB4, hfw2, hdg, hk2]; omega)
            obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 1) (lit 1) σ sm1
              (by simp [small]; omega)
            refine ⟨σ', (Run.ite_false hF0 (Run.ite_false hF2 (Run.ite_false hF1
              (Run.ite_false hF3 (Run.ite_true hT r))))).mono
              (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
            · rw [e1, if_neg h0, if_neg h2, if_neg h1, if_neg h3, if_pos h4]; simp [den]
            · rw [e2, if_neg h0, if_neg h2, if_neg h1, if_neg h3, if_pos h4]
              simp [den, Env.setVar]
          · have hF4 : (Cond.eq (V "cc") (add (add (V "B4") (mul (V "fw2") (V "dg"))) (V "k2"))).evalB
                B σ = some false := condEq_false _ _ σ small_cc hinc2 (by
                  simp [den, hcc, hB4, hfw2, hdg, hk2]; omega)
            obtain ⟨σ', r, e1, e2, st⟩ := pd_run (B := B) (lit 1) (add (lit 3) (V "cc")) σ sm1
              (by simp [small, den, Env.setVar, hcc]; omega)
            refine ⟨σ', (Run.ite_false hF0 (Run.ite_false hF2 (Run.ite_false hF1
              (Run.ite_false hF3 (Run.ite_false hF4 r))))).mono
              (by simp [Cond.size, Expr.size] <;> omega), ?_, ?_, st⟩
            · rw [e1, if_neg h0, if_neg h2, if_neg h1, if_neg h3, if_neg h4]; simp [den]
            · rw [e2, if_neg h0, if_neg h2, if_neg h1, if_neg h3, if_neg h4]
              simp [den, Env.setVar, hcc]

/-- The scalars of the edge-day job that no step of it changes. -/
def XE : List String := AJ ++ ["e", "bs", "bd", "k1", "k2"] ++ MisFind.AF ++ MisCount.AN

/-- What an edge-day job reads. -/
def JCE (ns : List ℕ) (i c : ℕ) (σ : Env) : Prop :=
  JC ns i c σ ∧ σ.arrs "TK" = ns ∧ σ.vars "VV" = VM ns * VM ns

lemma JCE.step {ns : List ℕ} {i c : ℕ} {σ σ' : Env} (h : JCE ns i c σ) (hk : JStep XE σ σ') :
    JCE ns i c σ' := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hk.2.2 "di" (by decide)]; exact h.1.vdi
  · rw [hk.2.2 "cc" (by decide)]; exact h.1.vcc
  · rw [hk.2.2 "nn" (by decide)]; exact h.1.vnn
  · rw [hk.2.2 "lc" (by decide)]; exact h.1.vlc
  · rw [hk.2.2 "V" (by decide)]; exact h.1.vV
  · rw [hk.2.2 "dg" (by decide)]; exact h.1.vdg
  · rw [hk.2.2 "S2" (by decide)]; exact h.1.vS2
  · rw [hk.2.2 "B3" (by decide)]; exact h.1.vB3
  · rw [hk.2.2 "B4" (by decide)]; exact h.1.vB4
  · rw [hk.2.2 "dn" (by decide)]; exact h.1.vdn
  · rw [hk.2.2 "nn1" (by decide)]; exact h.1.vn1
  · rw [hk.2.2 "LB" (by decide)]; exact h.1.vLB
  · rw [hk.1]; exact h.2.1
  · rw [hk.2.2 "VV" (by decide)]; exact h.2.2

/-- The cost of an edge day's job. -/
def Kedge (V VV : ℕ) : ℕ := 200 + (84 * VV + 20) + 2 * (44 * V + 20)

set_option maxHeartbeats 12800000 in
/-- **A job of an edge day.** -/
theorem edgeCom_run (ns : List ℕ) (i c : ℕ) (σ : Env) (hj : JC ns i c σ)
    (hA : σ.arrs "TK" = ns) (hVV : σ.vars "VV" = VM ns * VM ns)
    (hE : ∀ k < VM ns * VM ns, ns.getD (2 + k) 0 + 8 < B) (hlen : 2 + VM ns * VM ns ≤ ns.length)
    (hbig : 2 * (VM ns * VM ns) + 2 * VM ns + 2 * lN ns + 60 < B) (hM : Mag ns < B)
    (hi1 : lN ns * (nN ns + 1) ≤ i) (hi2 : i - lN ns * (nN ns + 1) < edgeN ns)
    (hcl : c < clN ns) :
    ∃ σ', Run B edgeCom σ σ' (Kedge (VM ns) (VM ns * VM ns)) ∧
      σ'.vars "pv" = (edgeDayN ns ((edgeCellsN ns).getD (i - lN ns * (nN ns + 1)) (0, 0)).1
        ((edgeCellsN ns).getD (i - lN ns * (nN ns + 1)) (0, 0)).2 c).1 ∧
      σ'.vars "dv" = (edgeDayN ns ((edgeCellsN ns).getD (i - lN ns * (nN ns + 1)) (0, 0)).1
        ((edgeCellsN ns).getD (i - lN ns * (nN ns + 1)) (0, 0)).2 c).2 ∧
      JStep XE σ σ' := by
  have hsp := VM_le_span ns
  have hlc := lN_le_span ns
  have hcls := cl_le ns
  have hspg := span_ge ns
  unfold Mag at hM
  have hjce : JCE ns i c σ := ⟨hj, hA, hVV⟩
  obtain ⟨hdi, hcc, hnn, hlc', hV, hdg, hS2, hB3, hB4, hdn, hn1, hLB⟩ := hj
  have hEle : edgeN ns ≤ VM ns * VM ns := by
    unfold edgeN
    have := List.countP_le_length (p := qualE ns) (l := List.range (VM ns * VM ns))
    simpa using this
  have hLBv : lN ns * (nN ns + 1) = VM ns + lN ns := by
    rw [Nat.mul_add, Nat.mul_one, VM_eq]
  have hdg1 : 1 ≤ degN ns := by unfold degN; omega
  have hi3 : i < VM ns * VM ns + VM ns + lN ns := by omega
  obtain ⟨hw1, hw2⟩ := edge_lt ns (i - lN ns * (nN ns + 1)) hi2
  have hpair := MisFind.edgeCells_getD ns (i - lN ns * (nN ns + 1))
  -- e := di - LB
  have small_di : small B σ (V "di") := by simp [small, hdi]; omega
  have small_LB : small B σ (V "LB") := by simp [small, hLB]; omega
  have s1 := asgE (B := B) "e" (sub (V "di") (V "LB")) σ (by
    simp [small, den, hdi, hLB]; omega)
  set σ1 := σ.setVar "e" (den σ (sub (V "di") (V "LB"))) with hσ1
  have he1 : σ1.vars "e" = i - lN ns * (nN ns + 1) := by simp [hσ1, den, Env.setVar, hdi, hLB]
  have k1 : JStep XE σ σ1 := JStep.setVar σ "e" _ (by simp [XE, AJ])
  have hc1 := hjce.step k1
  have hVdg := Vdg_le ns
  -- the scan for the edge
  obtain ⟨σ2, r2, hfw, hfw2, ha2, ho2, hf2⟩ := MisFind.findCom_run (B := B) ns (VM ns)
    (VM ns * VM ns) (i - lN ns * (nN ns + 1)) σ1 hE hlen (by omega) hc1.2.1 hc1.1.vV hc1.2.2 he1
  have k2 : JStep XE σ1 σ2 := ⟨ha2, ho2, fun y hy => hf2 y (fun h => hy (by simp [XE, h]))⟩
  have hc2 := hc1.step k2
  obtain ⟨w, hw⟩ : ∃ w, w = ((edgeCellsN ns).getD (i - lN ns * (nN ns + 1)) (0, 0)).1 := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w', w' = ((edgeCellsN ns).getD (i - lN ns * (nN ns + 1)) (0, 0)).2 :=
    ⟨_, rfl⟩
  rw [← hw] at hw1
  rw [← hw'] at hw2
  have hfw' : σ2.vars "fw" = w := by rw [hfw, hw, hpair]
  have hfw2' : σ2.vars "fw2" = w' := by rw [hfw2, hw', hpair]
  have hwV : w * VM ns ≤ VM ns * VM ns := Nat.mul_le_mul_right _ hw1.le
  have hw'V : w' * VM ns ≤ VM ns * VM ns := Nat.mul_le_mul_right _ hw2.le
  have hwd : w * degN ns ≤ VM ns * degN ns := Nat.mul_le_mul_right _ hw1.le
  have hw'd : w' * degN ns ≤ VM ns * degN ns := Nat.mul_le_mul_right _ hw2.le
  -- the first count: the neighbours of w before w'
  have s3 := asgE (B := B) "bs" (add (lit 2) (mul (V "fw") (V "V"))) σ2 (by
    simp [small, den, hfw', hc2.1.vV]; omega)
  set σ3 := σ2.setVar "bs" (den σ2 (add (lit 2) (mul (V "fw") (V "V")))) with hσ3
  have hbs3 : σ3.vars "bs" = 2 + w * VM ns := by simp [hσ3, den, Env.setVar, hfw', hc2.1.vV]
  have k3 : JStep XE σ2 σ3 := JStep.setVar σ2 "bs" _ (by simp [XE])
  have hc3 := hc2.step k3
  have hfw23 : σ3.vars "fw2" = w' := by simp [hσ3, Env.setVar, hfw2']
  have s4 := asgE (B := B) "bd" (V "fw2") σ3 (by simp [small, hfw23]; omega)
  set σ4 := σ3.setVar "bd" (den σ3 (V "fw2")) with hσ4
  have hbd4 : σ4.vars "bd" = w' := by simp [hσ4, den, Env.setVar, hfw23]
  have hbs4 : σ4.vars "bs" = 2 + w * VM ns := by simp [hσ4, Env.setVar, hbs3]
  have k4 : JStep XE σ3 σ4 := JStep.setVar σ3 "bd" _ (by simp [XE])
  have hc4 := hc3.step k4
  obtain ⟨σ5, r5, c5, a5, o5, f5⟩ := MisCount.cntCom_run (B := B) ns (2 + w * VM ns) w' σ4
    (fun k hk => by
      have := hE (w * VM ns + k) (MisCheck.cell_lt' _ _ _ hw1 (by omega))
      rwa [← Nat.add_assoc] at this)
    (by have := MisCheck.cell_lt' (VM ns) w w' hw1 hw2; omega) (by omega) hc4.2.1 hbs4 hbd4
  have k5 : JStep XE σ4 σ5 := ⟨a5, o5, fun y hy => f5 y (fun h => hy (by
    simp only [MisCount.AN, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp [XE, MisCount.AN]))⟩
  have hc5 := hc4.step k5
  have hk1 : σ5.vars "cnt" = idxN ns w w' := by rw [c5, idx_eq]
  have hi1 := idxN_le ns w w'
  have hi2 := idxN_le ns w' w
  have hfw5 : σ5.vars "fw" = w := by
    rw [f5 "fw" (by simp [MisCount.AN])]; simp [hσ4, hσ3, Env.setVar, hfw']
  have hfw25 : σ5.vars "fw2" = w' := by
    rw [f5 "fw2" (by simp [MisCount.AN])]; simp [hσ4, hσ3, Env.setVar, hfw2']
  -- k1 := cnt
  have s6 := asgE (B := B) "k1" (V "cnt") σ5 (by simp [small, hk1]; omega)
  set σ6 := σ5.setVar "k1" (den σ5 (V "cnt")) with hσ6
  have hk16 : σ6.vars "k1" = idxN ns w w' := by simp [hσ6, den, Env.setVar, hk1]
  have hfw6 : σ6.vars "fw" = w := by simp [hσ6, Env.setVar, hfw5]
  have hfw26 : σ6.vars "fw2" = w' := by simp [hσ6, Env.setVar, hfw25]
  have k6 : JStep XE σ5 σ6 := JStep.setVar σ5 "k1" _ (by simp [XE])
  have hc6 := hc5.step k6
  -- the second count: the neighbours of w' before w
  have s7 := asgE (B := B) "bs" (add (lit 2) (mul (V "fw2") (V "V"))) σ6 (by
    simp [small, den, hfw26, hc6.1.vV]; omega)
  set σ7 := σ6.setVar "bs" (den σ6 (add (lit 2) (mul (V "fw2") (V "V")))) with hσ7
  have hbs7 : σ7.vars "bs" = 2 + w' * VM ns := by simp [hσ7, den, Env.setVar, hfw26, hc6.1.vV]
  have hfw7 : σ7.vars "fw" = w := by simp [hσ7, Env.setVar, hfw6]
  have hfw27 : σ7.vars "fw2" = w' := by simp [hσ7, Env.setVar, hfw26]
  have hk17 : σ7.vars "k1" = idxN ns w w' := by simp [hσ7, Env.setVar, hk16]
  have k7 : JStep XE σ6 σ7 := JStep.setVar σ6 "bs" _ (by simp [XE])
  have hc7 := hc6.step k7
  have s8 := asgE (B := B) "bd" (V "fw") σ7 (by simp [small, hfw7]; omega)
  set σ8 := σ7.setVar "bd" (den σ7 (V "fw")) with hσ8
  have hbd8 : σ8.vars "bd" = w := by simp [hσ8, den, Env.setVar, hfw7]
  have hbs8 : σ8.vars "bs" = 2 + w' * VM ns := by simp [hσ8, Env.setVar, hbs7]
  have k8 : JStep XE σ7 σ8 := JStep.setVar σ7 "bd" _ (by simp [XE])
  have hc8 := hc7.step k8
  obtain ⟨σ9, r9, c9, a9, o9, f9⟩ := MisCount.cntCom_run (B := B) ns (2 + w' * VM ns) w σ8
    (fun k hk => by
      have := hE (w' * VM ns + k) (MisCheck.cell_lt' _ _ _ hw2 (by omega))
      rwa [← Nat.add_assoc] at this)
    (by have := MisCheck.cell_lt' (VM ns) w' w hw2 hw1; omega) (by omega) hc8.2.1 hbs8 hbd8
  have k9 : JStep XE σ8 σ9 := ⟨a9, o9, fun y hy => f9 y (fun h => hy (by
    simp only [MisCount.AN, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp [XE, MisCount.AN]))⟩
  have hc9 := hc8.step k9
  have hk2 : σ9.vars "cnt" = idxN ns w' w := by rw [c9, idx_eq]
  have hfw9 : σ9.vars "fw" = w := by
    rw [f9 "fw" (by simp [MisCount.AN])]; simp [hσ8, Env.setVar, hfw7]
  have hfw29 : σ9.vars "fw2" = w' := by
    rw [f9 "fw2" (by simp [MisCount.AN])]; simp [hσ8, Env.setVar, hfw27]
  have hk19 : σ9.vars "k1" = idxN ns w w' := by
    rw [f9 "k1" (by simp [MisCount.AN])]; simp [hσ8, Env.setVar, hk17]
  have s10 := asgE (B := B) "k2" (V "cnt") σ9 (by simp [small, hk2]; omega)
  set σ10 := σ9.setVar "k2" (den σ9 (V "cnt")) with hσ10
  have hk210 : σ10.vars "k2" = idxN ns w' w := by simp [hσ10, den, Env.setVar, hk2]
  have hfw10 : σ10.vars "fw" = w := by simp [hσ10, Env.setVar, hfw9]
  have hfw210 : σ10.vars "fw2" = w' := by simp [hσ10, Env.setVar, hfw29]
  have hk110 : σ10.vars "k1" = idxN ns w w' := by simp [hσ10, Env.setVar, hk19]
  have k10 : JStep XE σ9 σ10 := JStep.setVar σ9 "k2" _ (by simp [XE])
  have hc10 := hc9.step k10
  obtain ⟨σ', rD, e1, e2, stD⟩ := edgeDisp_run (B := B) ns i c w w' σ10 hc10.1 hfw10 hfw210 hk110
    hk210 hw1 hw2 hcl hM
  have kD : JStep XE σ10 σ' := stD.mono (fun y hy => by simp only [XE, List.mem_append]; left; left; left; exact hy)
  refine ⟨σ', (s1.seq (r2.seq (s3.seq (s4.seq (r5.seq (s6.seq (s7.seq (s8.seq (r9.seq
    (s10.seq rD)))))))))).mono (by
      unfold Kedge; simp [Expr.size] <;> omega), ?_, ?_,
    (((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8).trans k9).trans
      k10).trans kD⟩
  · rw [← hw, ← hw']; exact e1
  · rw [← hw, ← hw']; exact e2

/-- The processing time and the due date of the job of client `cc` on day `di`. -/
def jobCom : Com :=
  .ite (.lt (V "di") (V "LB"))
    (.seq (.assign "vb" (div (V "di") (V "nn1")))
      (.seq (.assign "va" (sub (V "di") (mul (V "vb") (V "nn1"))))
        (.ite (.lt (V "va") (V "nn")) vertexCom validCom)))
    edgeCom

/-- The cost of a job. -/
def Kjob (V VV : ℕ) : ℕ := 300 + (84 * VV + 20) + 2 * (44 * V + 20)

set_option maxHeartbeats 12800000 in
/-- **The job of a client on a day.** -/
theorem jobCom_run (ns : List ℕ) (i c : ℕ) (σ : Env) (hc : JCE ns i c σ)
    (hE : ∀ k < VM ns * VM ns, ns.getD (2 + k) 0 + 8 < B) (hlen : 2 + VM ns * VM ns ≤ ns.length)
    (hbig : 2 * (VM ns * VM ns) + 2 * VM ns + 2 * lN ns + 60 < B) (hM : Mag ns < B)
    (hn0 : 0 < nN ns) (hi : i < daysN ns) (hcl : c < clN ns) :
    ∃ σ', Run B jobCom σ σ' (Kjob (VM ns) (VM ns * VM ns)) ∧
      σ'.vars "pv" = (jobN ns i c).1 ∧ σ'.vars "dv" = (jobN ns i c).2 ∧ JStep XE σ σ' := by
  have hc0 := hc
  obtain ⟨hj, hA, hVV⟩ := hc
  have hj0 := hj
  have hsp := VM_le_span ns
  have hlc := lN_le_span ns
  have hspg := span_ge ns
  have hLBv : lN ns * (nN ns + 1) = VM ns + lN ns := by rw [Nat.mul_add, Nat.mul_one, VM_eq]
  obtain ⟨hdi, hcc, hnn, hlc', hV, hdg, hS2, hB3, hB4, hdn, hn1, hLB⟩ := hj
  have hEle : edgeN ns ≤ VM ns * VM ns := by
    unfold edgeN
    have := List.countP_le_length (p := qualE ns) (l := List.range (VM ns * VM ns))
    simpa using this
  unfold daysN at hi
  unfold Mag at hM
  have hdg1 : 1 ≤ degN ns := by unfold degN; omega
  have hnn_le : nN ns ≤ degN ns * nN ns := Nat.le_mul_of_pos_left _ hdg1
  have hdiB : small B σ (V "di") := by simp [small, hdi]; omega
  have hLBB : small B σ (V "LB") := by simp [small, hLB]; omega
  unfold jobN
  by_cases h1 : i < lN ns * (nN ns + 1)
  · have hT : (Cond.lt (V "di") (V "LB")).evalB B σ = some true :=
      condLt_true _ _ σ hdiB hLBB (by simp [den, hdi, hLB]; omega)
    rw [if_pos h1]
    have hn1B : small B σ (V "nn1") := by simp [small, hn1]; omega
    have hn1pos : 0 < nN ns + 1 := by omega
    have hdivle : i / (nN ns + 1) ≤ i := Nat.div_le_self _ _
    have hbmul : i / (nN ns + 1) * (nN ns + 1) ≤ i := Nat.div_mul_le_self _ _
    have s1 := asgE (B := B) "vb" (div (V "di") (V "nn1")) σ (by
      simp [small, den, hdi, hn1]; omega)
    set σ1 := σ.setVar "vb" (den σ (div (V "di") (V "nn1"))) with hσ1
    have hb1 : σ1.vars "vb" = i / (nN ns + 1) := by simp [hσ1, den, Env.setVar, hdi, hn1]
    have hbl : i / (nN ns + 1) < lN ns := (Nat.div_lt_iff_lt_mul hn1pos).2 h1
    have k1 : JStep XE σ σ1 := JStep.setVar σ "vb" _ (by simp [XE, AJ])
    have hc1 := hc0.step k1
    have s2 := asgE (B := B) "va" (sub (V "di") (mul (V "vb") (V "nn1"))) σ1 (by
      simp [small, den, Env.setVar, hc1.1.vdi, hc1.1.vn1, hb1]
      omega)
    set σ2 := σ1.setVar "va" (den σ1 (sub (V "di") (mul (V "vb") (V "nn1")))) with hσ2
    have ha2 : σ2.vars "va" = i - i / (nN ns + 1) * (nN ns + 1) := by
      simp [hσ2, den, Env.setVar, hc1.1.vdi, hc1.1.vn1, hb1]
    have hb2 : σ2.vars "vb" = i / (nN ns + 1) := by simp [hσ2, Env.setVar, hb1]
    have k2 : JStep XE σ1 σ2 := JStep.setVar σ1 "va" _ (by simp [XE, AJ])
    have hc2 := hc1.step k2
    have hmod : i - i / (nN ns + 1) * (nN ns + 1) = i % (nN ns + 1) := MisFind.mod_eq_sub i _
    have hmlt : i % (nN ns + 1) < nN ns + 1 := Nat.mod_lt _ hn1pos
    have hva : small B σ2 (V "va") := by simp [small, ha2]; omega
    have hnnB : small B σ2 (V "nn") := by simp [small, hc2.1.vnn]; omega
    by_cases h2 : i % (nN ns + 1) < nN ns
    · have hT2 : (Cond.lt (V "va") (V "nn")).evalB B σ2 = some true :=
        condLt_true _ _ σ2 hva hnnB (by simp [den, ha2, hc2.1.vnn]; omega)
      have hw0 : i / (nN ns + 1) * nN ns + i % (nN ns + 1) < VM ns := by
        have := Nat.mul_le_mul_right (nN ns) (show i / (nN ns + 1) + 1 ≤ lN ns by omega)
        rw [Nat.add_mul, Nat.one_mul, ← VM_eq] at this
        omega
      obtain ⟨σ', r, e1, e2, st⟩ := vertexCom_run (B := B) ns i c (i / (nN ns + 1))
        (i % (nN ns + 1)) σ2 hc2.1 hb2 (by rw [ha2, hmod]) h2 hw0 hcl hM
      refine ⟨σ', (Run.ite_true hT ((s1.seq (s2.seq (Run.ite_true hT2 r))))).mono
        (by unfold Kjob; simp [Cond.size, Expr.size] <;> omega), ?_, ?_,
        ((k1.trans k2).trans (st.mono (fun y hy => by simp only [XE, List.mem_append]; left; left; left; exact hy)))⟩
      · rw [if_pos h2]; exact e1
      · rw [if_pos h2]; exact e2
    · have hF2 : (Cond.lt (V "va") (V "nn")).evalB B σ2 = some false :=
        condLt_false _ _ σ2 hva hnnB (by simp [den, ha2, hc2.1.vnn]; omega)
      obtain ⟨σ', r, e1, e2, st⟩ := validCom_run (B := B) ns i c (i / (nN ns + 1)) σ2 hc2.1 hb2 hbl
        hn0 hcl hM
      refine ⟨σ', (Run.ite_true hT ((s1.seq (s2.seq (Run.ite_false hF2 r))))).mono
        (by unfold Kjob; simp [Cond.size, Expr.size] <;> omega), ?_, ?_,
        ((k1.trans k2).trans (st.mono (fun y hy => by simp only [XE, List.mem_append]; left; left; left; exact hy)))⟩
      · rw [if_neg h2]; exact e1
      · rw [if_neg h2]; exact e2
  · have hF : (Cond.lt (V "di") (V "LB")).evalB B σ = some false :=
      condLt_false _ _ σ hdiB hLBB (by simp [den, hdi, hLB]; omega)
    rw [if_neg h1]
    obtain ⟨σ', r, e1, e2, st⟩ := edgeCom_run (B := B) ns i c σ hj0 hA hVV hE hlen hbig hM
      (by omega) (by omega) hcl
    exact ⟨σ', (Run.ite_false hF r).mono (by
      unfold Kjob Kedge; simp [Cond.size, Expr.size] <;> omega), e1, e2, st⟩

end Lax117284Proofs.Machine.MisJob

end

/-! ### `Lax117284Proofs.Machine.MisPrint` -/

section
/-!
Writing the image of Lemma 14: the number of clients and of days, the processing time and the due
date of every job cell by cell, and the fairness parameter of every client.
-/

namespace Lax117284Proofs.Machine.MisPrint

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.MisBlk Lax117284Proofs.Machine.MisSem
open Lax117284Proofs.Machine.MisJob (jobCom XE Kjob JCE JC JStep AJ jobCom_run Mag)
open Lax117284Proofs.Machine.MisFormat (VM)

variable {B : ℕ}

/-- Everything a cell reads. -/
structure PC (ns : List ℕ) (σ : Env) : Prop where
  hA : σ.arrs "TK" = ns
  vnn : σ.vars "nn" = nN ns
  vlc : σ.vars "lc" = lN ns
  vV : σ.vars "V" = VM ns
  vdg : σ.vars "dg" = degN ns
  vS2 : σ.vars "S2" = spanN ns
  vB3 : σ.vars "B3" = 3 + lN ns
  vB4 : σ.vars "B4" = 3 + lN ns + VM ns
  vdn : σ.vars "dn" = degN ns * nN ns
  vn1 : σ.vars "nn1" = nN ns + 1
  vLB : σ.vars "LB" = lN ns * (nN ns + 1)
  vVV : σ.vars "VV" = VM ns * VM ns
  vCC : σ.vars "CC" = clN ns
  vDD : σ.vars "DD" = daysN ns
  vE2 : σ.vars "E2" = edgeN ns / 2
  vDC : σ.vars "DC" = daysN ns * clN ns

/-- The cell `i` of the image: the day and the client, and the job. -/
def cellBody : Com :=
  .seq (.assign "di" (.bin .div (V "i") (V "CC")))
  (.seq (.assign "dm" (.bin .mul (V "di") (V "CC")))
  (.seq (.assign "cc" (.bin .sub (V "i") (V "dm")))
  (.seq jobCom (.seq (emitVar "pv") (emitVar "dv")))))

/-- The scalars a cell assigns. -/
def SCELL : List String := "i" :: (XE ++ ["di", "dm", "cc"] ++ SCR)

/-- The cost of a cell. -/
def Kcell (Sz V VV : ℕ) : ℕ := 100 + Kjob V VV + 2 * (48 * Sz + 50)

/-- **Every number of the image is small.** -/
lemma job_bound (ns : List ℕ) (i c : ℕ) (hn0 : 0 < nN ns) (hcl : c < clN ns) :
    (jobN ns i c).1 < Mag ns ∧ (jobN ns i c).2 < Mag ns := by
  have hspe := MisJob.span_eq ns
  have hcls := MisJob.cl_le ns
  have hdg1 : 1 ≤ degN ns := by unfold degN; omega
  have hnn_le : nN ns ≤ degN ns * nN ns := Nat.le_mul_of_pos_left _ hdg1
  have hVdg := MisJob.Vdg_le ns
  have h1 : ∀ x, degN ns * (x % nN ns + 1) ≤ degN ns * nN ns :=
    fun x => Nat.mul_le_mul_left _ (Nat.mod_lt _ hn0)
  have h2 : ∀ q m, degN ns * (q % nN ns) + m % degN ns + 1 ≤ degN ns * nN ns + degN ns := by
    intro q m
    have a := Nat.mul_le_mul_left (degN ns) (Nat.mod_lt q hn0).le
    have b := Nat.mod_lt m (show 0 < degN ns by omega)
    omega
  unfold Mag
  unfold jobN vertexDayN validationDayN edgeDayN
  split_ifs <;> simp only [] <;> first | omega | (constructor <;> first | omega | skip)
  all_goals first
    | (have := h1 (c - (3 + lN ns)); omega)
    | (have := h2 ((c - (3 + lN ns + VM ns)) / degN ns) (c - (3 + lN ns + VM ns)); omega)

lemma PC.of_agr {ns : List ℕ} {σ0 σ : Env} (h : PC ns σ0) (hAg : Agr SCELL σ0 σ) : PC ns σ := by
  have fr : ∀ y, y ∉ SCELL → σ.vars y = σ0.vars y := hAg.2
  refine ⟨by rw [hAg.1]; exact h.hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fr "nn" (by decide)]; exact h.vnn
  · rw [fr "lc" (by decide)]; exact h.vlc
  · rw [fr "V" (by decide)]; exact h.vV
  · rw [fr "dg" (by decide)]; exact h.vdg
  · rw [fr "S2" (by decide)]; exact h.vS2
  · rw [fr "B3" (by decide)]; exact h.vB3
  · rw [fr "B4" (by decide)]; exact h.vB4
  · rw [fr "dn" (by decide)]; exact h.vdn
  · rw [fr "nn1" (by decide)]; exact h.vn1
  · rw [fr "LB" (by decide)]; exact h.vLB
  · rw [fr "VV" (by decide)]; exact h.vVV
  · rw [fr "CC" (by decide)]; exact h.vCC
  · rw [fr "DD" (by decide)]; exact h.vDD
  · rw [fr "E2" (by decide)]; exact h.vE2
  · rw [fr "DC" (by decide)]; exact h.vDC

set_option maxHeartbeats 12800000 in
/-- **A cell of the image.** -/
theorem cellBody_run (Sz : ℕ) (ns : List ℕ) (σ0 σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hAg : Agr SCELL σ0 σ) (hpc : PC ns σ0)
    (hE : ∀ k < VM ns * VM ns, ns.getD (2 + k) 0 + 8 < B) (hlen : 2 + VM ns * VM ns ≤ ns.length)
    (hbig : 2 * (VM ns * VM ns) + 2 * VM ns + 2 * lN ns + 60 < B) (hM : Mag ns + 4 < B)
    (hn0 : 0 < nN ns) (hBP : daysN ns * clN ns + clN ns + daysN ns + 100 < B)
    (hlt : σ.vars "i" < daysN ns * clN ns) :
    ∃ σ', Run B cellBody σ σ' (Kcell Sz (VM ns) (VM ns * VM ns)) ∧
      σ'.out = σ.out ++ (bitsNat (MisSem.jobN ns (σ.vars "i" / clN ns) (σ.vars "i" % clN ns)).1 ++
        bitsNat (MisSem.jobN ns (σ.vars "i" / clN ns) (σ.vars "i" % clN ns)).2) ∧
      Agr SCELL σ0 σ' ∧ σ'.vars "i" = σ.vars "i" := by
  have hp := hpc.of_agr hAg
  obtain ⟨t, ht⟩ : ∃ t, σ.vars "i" = t := ⟨_, rfl⟩
  rw [ht] at hlt ⊢
  have hCpos : 0 < clN ns := by unfold clN; omega
  have hd_lt : t / clN ns < daysN ns := (Nat.div_lt_iff_lt_mul hCpos).2 hlt
  have hdle : t / clN ns ≤ t := Nat.div_le_self _ _
  have hmle : t / clN ns * clN ns ≤ t := Nat.div_mul_le_self _ _
  have hmod : t - t / clN ns * clN ns = t % clN ns := MisFind.mod_eq_sub t _
  have hmlt : t % clN ns < clN ns := Nat.mod_lt _ hCpos
  have s1 := asgE (B := B) "di" (.bin .div (V "i") (V "CC")) σ (by
    simp [small, den, ht, hp.vCC]; omega)
  set σ1 := σ.setVar "di" (den σ (.bin .div (V "i") (V "CC"))) with hσ1
  have hdi1 : σ1.vars "di" = t / clN ns := by simp [hσ1, den, Env.setVar, ht, hp.vCC]
  have s2 := asgE (B := B) "dm" (.bin .mul (V "di") (V "CC")) σ1 (by
    simp [small, den, hσ1, Env.setVar, ht, hp.vCC]; omega)
  set σ2 := σ1.setVar "dm" (den σ1 (.bin .mul (V "di") (V "CC"))) with hσ2
  have hdm2 : σ2.vars "dm" = t / clN ns * clN ns := by
    simp [hσ2, den, Env.setVar, hdi1, hσ1, hp.vCC, ht]
  have hi2 : σ2.vars "i" = t := by simp [hσ2, hσ1, Env.setVar, ht]
  have s3 := asgE (B := B) "cc" (.bin .sub (V "i") (V "dm")) σ2 (by
    simp [small, den, hi2, hdm2]; omega)
  set σ3 := σ2.setVar "cc" (den σ2 (.bin .sub (V "i") (V "dm"))) with hσ3
  have hcc3 : σ3.vars "cc" = t % clN ns := by simp [hσ3, den, Env.setVar, hi2, hdm2, hmod]
  have hdi3 : σ3.vars "di" = t / clN ns := by simp [hσ3, hσ2, Env.setVar, hdi1]
  have fr3 : ∀ y, y ∉ ["di", "dm", "cc"] → σ3.vars y = σ.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hσ3, hσ2, hσ1, Env.setVar, hy.1, hy.2.1, hy.2.2]
  have ar3 : σ3.arrs = σ.arrs := by simp [hσ3, hσ2, hσ1, Env.setVar]
  have ou3 : σ3.out = σ.out := by simp [hσ3, hσ2, hσ1, Env.setVar]
  have hjce : JCE ns (t / clN ns) (t % clN ns) σ3 :=
    ⟨⟨hdi3, hcc3, by rw [fr3 "nn" (by decide)]; exact hp.vnn,
      by rw [fr3 "lc" (by decide)]; exact hp.vlc,
      by rw [fr3 "V" (by decide)]; exact hp.vV,
      by rw [fr3 "dg" (by decide)]; exact hp.vdg,
      by rw [fr3 "S2" (by decide)]; exact hp.vS2,
      by rw [fr3 "B3" (by decide)]; exact hp.vB3,
      by rw [fr3 "B4" (by decide)]; exact hp.vB4,
      by rw [fr3 "dn" (by decide)]; exact hp.vdn,
      by rw [fr3 "nn1" (by decide)]; exact hp.vn1,
      by rw [fr3 "LB" (by decide)]; exact hp.vLB⟩,
      by rw [ar3]; exact hp.hA, by rw [fr3 "VV" (by decide)]; exact hp.vVV⟩
  obtain ⟨σ4, r4, hpv, hdv, hst⟩ := jobCom_run (B := B) ns (t / clN ns) (t % clN ns) σ3 hjce hE hlen
    hbig (by omega) hn0 hd_lt hmlt
  obtain ⟨hb1, hb2⟩ := job_bound ns (t / clN ns) (t % clN ns) hn0 hmlt
  obtain ⟨σ5, r5, o5, v5, a5⟩ := emitVar_spec (B := B) "pv" Sz σ4
    ⟨by rw [hpv]; omega, by rw [hpv]; exact hs _ (by omega)⟩
  have s5 : Same σ4 σ5 := same_of_frame v5 a5
  have hdv5 : σ5.vars "dv" = (jobN ns (t / clN ns) (t % clN ns)).2 := by
    rw [s5.1 "dv" (by decide)]; exact hdv
  obtain ⟨σ6, r6, o6, v6, a6⟩ := emitVar_spec (B := B) "dv" Sz σ5
    ⟨by rw [hdv5]; omega, by rw [hdv5]; exact hs _ (by omega)⟩
  have s6 : Same σ5 σ6 := same_of_frame v6 a6
  refine ⟨σ6, ?_, ?_, ?_, ?_⟩
  · refine (s1.seq (s2.seq (s3.seq (r4.seq (r5.seq r6))))).mono ?_
    unfold Kcell
    simp [Expr.size]
    omega
  · rw [o6, o5, hst.2.1, ou3, hdv5, hpv, List.append_assoc]
  · have hfr : ∀ y, y ∉ SCELL → σ6.vars y = σ0.vars y := by
      intro y hy
      have hy' : y ≠ "i" ∧ y ∉ XE ∧ y ≠ "di" ∧ y ≠ "dm" ∧ y ≠ "cc" ∧ y ∉ SCR := by
        simp only [SCELL, List.mem_cons, List.mem_append, not_or] at hy
        tauto
      rw [s6.1 y hy'.2.2.2.2.2, s5.1 y hy'.2.2.2.2.2, hst.2.2 y hy'.2.1,
        fr3 y (by simp [hy'.2.2.1, hy'.2.2.2.1, hy'.2.2.2.2.1])]
      exact hAg.2 y hy
    refine ⟨?_, hfr⟩
    rw [s6.2, s5.2, hst.1, ar3]; exact hAg.1
  · rw [s6.1 "i" (by decide), s5.1 "i" (by decide), hst.2.2 "i" (by decide),
      fr3 "i" (by decide), ht]

/-- The fairness parameter of a client. -/
def kvBody : Com :=
  .ite (.eq (V "i") (.lit 0)) (emitVar "DD")
    (.ite (.eq (V "i") (.lit 1)) (emitVar "E2")
      (.ite (.eq (V "i") (.lit 2)) (emitVar "E2") (emitLit 1)))

/-- The cost of a fairness parameter. -/
def Kkv (Sz : ℕ) : ℕ := 100 + (48 * Sz + 50)

/-- **The fairness parameter of a client.** -/
theorem kvBody_run (Sz : ℕ) (ns : List ℕ) (σ0 σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hAg : Agr ("i" :: SCR) σ0 σ) (hpc : PC ns σ0)
    (hDD : daysN ns + 4 < B) (hE2 : edgeN ns / 2 + 4 < B) (hlt : σ.vars "i" < clN ns)
    (hBi : clN ns + 4 < B) :
    ∃ σ', Run B kvBody σ σ' (Kkv Sz) ∧
      σ'.out = σ.out ++ bitsNat (kvN ns (σ.vars "i")) ∧
      Agr ("i" :: SCR) σ0 σ' ∧ σ'.vars "i" = σ.vars "i" := by
  obtain ⟨t, ht⟩ : ∃ t, σ.vars "i" = t := ⟨_, rfl⟩
  rw [ht] at hlt ⊢
  have hDDv : σ.vars "DD" = daysN ns := by rw [hAg.2 "DD" (by decide)]; exact hpc.vDD
  have hE2v : σ.vars "E2" = edgeN ns / 2 := by rw [hAg.2 "E2" (by decide)]; exact hpc.vE2
  have hiB : small B σ (V "i") := by simp [small, ht]; omega
  have h0B : small B σ (.lit 0) := by simp [small]; omega
  have h1B : small B σ (.lit 1) := by simp [small]; omega
  have h2B : small B σ (.lit 2) := by simp [small]; omega
  have fin : ∀ (σ' : Env), (∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ.vars y) → σ'.arrs = σ.arrs →
      Agr ("i" :: SCR) σ0 σ' ∧ σ'.vars "i" = t := by
    intro σ' hv ha
    refine ⟨⟨by rw [ha]; exact hAg.1, fun y hy => ?_⟩, ?_⟩
    · have hy' : y ∉ ["v", "s", "u", "i2"] ∧ y ∉ "i" :: SCR := by
        simp only [SCR, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢
        tauto
      rw [hv y hy'.1]; exact hAg.2 y hy'.2
    · rw [hv "i" (by decide), ht]
  have hK : Kkv Sz = 100 + (48 * Sz + 50) := rfl
  by_cases h0 : t = 0
  · obtain ⟨σ', r, o, v, a⟩ := emitVar_spec (B := B) "DD" Sz σ
      ⟨by rw [hDDv]; omega, by rw [hDDv]; exact hs _ (by omega)⟩
    have hT : (Cond.eq (V "i") (.lit 0)).evalB B σ = some true :=
      condEq_true _ _ σ hiB h0B (by simp [den, ht, h0])
    refine ⟨σ', (Run.ite_true hT r).mono (by simp [Cond.size, Expr.size, hK] <;> omega), ?_,
      fin σ' v a⟩
    rw [o, hDDv]; simp [kvN, h0]
  · have hF : (Cond.eq (V "i") (.lit 0)).evalB B σ = some false :=
      condEq_false _ _ σ hiB h0B (by simp [den, ht, h0])
    by_cases h1 : t = 1
    · obtain ⟨σ', r, o, v, a⟩ := emitVar_spec (B := B) "E2" Sz σ
        ⟨by rw [hE2v]; omega, by rw [hE2v]; exact hs _ (by omega)⟩
      have hT : (Cond.eq (V "i") (.lit 1)).evalB B σ = some true :=
        condEq_true _ _ σ hiB h1B (by simp [den, ht, h1])
      refine ⟨σ', (Run.ite_false hF (Run.ite_true hT r)).mono
        (by simp [Cond.size, Expr.size, hK] <;> omega), ?_, fin σ' v a⟩
      rw [o, hE2v]; simp [kvN, h1]
    · have hF1 : (Cond.eq (V "i") (.lit 1)).evalB B σ = some false :=
        condEq_false _ _ σ hiB h1B (by simp [den, ht, h1])
      by_cases h2 : t = 2
      · obtain ⟨σ', r, o, v, a⟩ := emitVar_spec (B := B) "E2" Sz σ
          ⟨by rw [hE2v]; omega, by rw [hE2v]; exact hs _ (by omega)⟩
        have hT : (Cond.eq (V "i") (.lit 2)).evalB B σ = some true :=
          condEq_true _ _ σ hiB h2B (by simp [den, ht, h2])
        refine ⟨σ', (Run.ite_false hF (Run.ite_false hF1 (Run.ite_true hT r))).mono
          (by simp [Cond.size, Expr.size, hK] <;> omega), ?_, fin σ' v a⟩
        rw [o, hE2v]; simp [kvN, h2]
      · have hF2 : (Cond.eq (V "i") (.lit 2)).evalB B σ = some false :=
          condEq_false _ _ σ hiB h2B (by simp [den, ht, h2])
        obtain ⟨σ', r, o, v, a⟩ := (emitLit_spec (B := B) 1 Sz (by omega) (hs _ (by omega))) σ trivial
        refine ⟨σ', (Run.ite_false hF (Run.ite_false hF1 (Run.ite_false hF2 r))).mono
          (by simp [Cond.size, Expr.size, hK] <;> omega), ?_, fin σ' v a⟩
        rw [o]; simp [kvN, h0, h1, h2]

lemma PC.of_same {ns : List ℕ} {σ σ' : Env} (h : PC ns σ) (hs : Same σ σ') : PC ns σ' :=
  have hAg : Agr SCELL σ σ' := ⟨hs.2, fun y hy => hs.1 y (fun hm => hy (by
    simp only [SCELL, List.mem_cons, List.mem_append]; tauto))⟩
  h.of_agr hAg

lemma numBits_flatMap' {α : Type} (L : List α) (f : α → List ℕ) :
    numBits (L.flatMap f) = L.flatMap (fun a => numBits (f a)) := by
  simp only [numBits, List.flatMap_assoc]

lemma numBits_map' {α : Type} (L : List α) (f : α → ℕ) :
    numBits (L.map f) = L.flatMap (fun a => bitsNat (f a)) := by
  simp [numBits, List.flatMap_map]

/-- The cost of writing the image. -/
def Kprint (Sz V VV DC CC : ℕ) : ℕ :=
  2 * (48 * Sz + 50) + (Kcell Sz V VV + 10 + 4) * DC + 6 + (Kkv Sz + 10 + 4) * CC + 6

/-- Write the whole image. -/
def printM : Com :=
  .seq (emitVar "CC") (.seq (emitVar "DD") (.seq (outLoop "DC" cellBody) (outLoop "CC" kvBody)))

/-- **Writing the image.** -/
theorem printM_run (Sz : ℕ) (ns : List ℕ) (σ : Env) (hpc : PC ns σ)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hE : ∀ k < VM ns * VM ns, ns.getD (2 + k) 0 + 8 < B) (hlen : 2 + VM ns * VM ns ≤ ns.length)
    (hbig : 2 * (VM ns * VM ns) + 2 * VM ns + 2 * lN ns + 60 < B) (hM : Mag ns + 4 < B)
    (hn0 : 0 < nN ns) (hBP : daysN ns * clN ns + clN ns + daysN ns + 100 < B)
    (hE2 : edgeN ns / 2 + 4 < B) :
    ∃ σ', Run B printM σ σ'
      (Kprint Sz (VM ns) (VM ns * VM ns) (daysN ns * clN ns) (clN ns)) ∧
      σ'.out = σ.out ++ numBits (outM ns) := by
  have hCpos : 0 < clN ns := by unfold clN; omega
  have hDle : daysN ns ≤ daysN ns * clN ns := Nat.le_mul_of_pos_right _ hCpos
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "CC" Sz σ
    ⟨by rw [hpc.vCC]; omega, by rw [hpc.vCC]; exact hs _ (by omega)⟩
  have s1 : Same σ σ1 := same_of_frame v1 a1
  have p1 := hpc.of_same s1
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitVar_spec (B := B) "DD" Sz σ1
    ⟨by rw [p1.vDD]; omega, by rw [p1.vDD]; exact hs _ (by omega)⟩
  have s2 : Same σ1 σ2 := same_of_frame v2 a2
  have p2 := p1.of_same s2
  obtain ⟨σ3, r3, o3, hAg3⟩ := eLoop (B := B) "DC" cellBody SCELL
    (fun t => bitsNat (MisSem.jobN ns (t / clN ns) (t % clN ns)).1 ++
      bitsNat (MisSem.jobN ns (t / clN ns) (t % clN ns)).2) (Kcell Sz (VM ns) (VM ns * VM ns))
    (daysN ns * clN ns) σ2 (by simp [SCELL]) (by decide) p2.vDC (by omega) (by
      intro σ' hAg hlt
      obtain ⟨σ'', r, o, a, hi⟩ := cellBody_run (B := B) Sz ns σ2 σ' hs hAg p2 hE hlen hbig hM hn0 hBP hlt
      exact ⟨σ'', r, o, a, hi⟩)
  have p3 := p2.of_agr hAg3
  obtain ⟨σ4, r4, o4, hAg4⟩ := eLoop (B := B) "CC" kvBody ("i" :: SCR)
    (fun t => bitsNat (kvN ns t)) (Kkv Sz) (clN ns) σ3 (by simp) (by decide) p3.vCC (by omega) (by
      intro σ' hAg hlt
      exact kvBody_run (B := B) Sz ns σ3 σ' hs hAg p3 (by omega) hE2 hlt (by omega))
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by unfold Kprint; omega), ?_⟩
  rw [o4, o3, o2, o1]
  unfold outM
  simp only [numBits_append, numBits_cons, numBits_nil, List.append_nil, List.append_assoc,
    numBits_flatMap', numBits_map']
  rw [hpc.vCC, p1.vDD]

end Lax117284Proofs.Machine.MisPrint

end

/-! ### `Lax117284Proofs.Machine.MisAccept` -/

section
/-!
The whole of the reduction of Lemma 14 after the tokenizer has accepted: read the counts off the
array, check the matrix, derive the numbers of the image, and write the image or the rejected word.
-/

namespace Lax117284Proofs.Machine.MisAccept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.MisBlk Lax117284Proofs.Machine.MisSem
open Lax117284Proofs.Machine.MisPrint Lax117284Proofs.Machine.MisChk
open Lax117284Proofs.Machine.SatOps (asg_tkl)
open Lax117284Proofs.Machine.FreeAccept (rejectPrint rejectPrint_run)
open Lax117284Proofs.Machine.MisJob (Mag)
open Lax117284Proofs.Machine.MisFormat (VM)

variable {B : ℕ}

/-- Read the counts off the array. -/
def prepM : Com :=
  .seq (.assign "nn" (.get "TK" (.lit 1)))
  (.seq (.assign "lc" (.get "TK" (.lit 0)))
  (.seq (.assign "V" (.bin .mul (V "lc") (V "nn")))
        (.assign "VV" (.bin .mul (V "V") (V "V")))))

/-- The fairness degree of the vertex `0`. -/
def dgM : Com := .ite (.lt (V "rr") (.lit 1)) (.assign "dg" (.lit 1)) (.assign "dg" (V "rr"))

/-- The rest of the numbers of the image, from the degree. -/
def postTail : Com :=
  .seq (.assign "S2" (.bin .add (.bin .add (.bin .add (.lit 2) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg"))))
  (.seq (.assign "CC" (.bin .add (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg"))))
  (.seq (.assign "B3" (.bin .add (.lit 3) (V "lc")))
  (.seq (.assign "B4" (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")))
  (.seq (.assign "dn" (.bin .mul (V "dg") (V "nn")))
  (.seq (.assign "nn1" (.bin .add (V "nn") (.lit 1)))
  (.seq (.assign "LB" (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))))
  (.seq (.assign "DD" (.bin .add (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))) (V "EE")))
  (.seq (.assign "E2" (.bin .div (V "EE") (.lit 2)))
        (.assign "DC" (.bin .mul (.bin .add (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))) (V "EE")) (.bin .add (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg")))))))))))))

/-- Derive the numbers of the image from the check. -/
def postM : Com := .seq dgM postTail

/-- The scalars the derivation assigns, apart from the degree. -/
def APT : List String := ["S2", "CC", "B3", "B4", "dn", "nn1", "LB", "DD", "E2", "DC"]

/-- The whole of the reduction, after the tokenizer has accepted. -/
def acceptM : Com :=
  .seq prepM (.seq checkCom (.ite (.eq (V "ok") (.lit 1)) (.seq postM printM) rejectPrint))

/-- The five inputs of the derivation: the assignments leave them alone. -/
def Key (n l Vn E d : ℕ) (τ : Env) : Prop :=
  τ.vars "nn" = n ∧ τ.vars "lc" = l ∧ τ.vars "V" = Vn ∧ τ.vars "EE" = E ∧ τ.vars "dg" = d

theorem Key.set {n l Vn E d : ℕ} {τ : Env} (h : Key n l Vn E d τ) {z : String} (hz : z ∈ APT)
    (v : ℕ) : Key n l Vn E d (τ.setVar z v) := by
  simp only [APT, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simpa [Key, Env.setVar] using h

/-- One assignment of the derivation: the run, and the inputs still in place. -/
theorem postStep {n l Vn E d : ℕ} (τ : Env) (K : Key n l Vn E d τ) (z : String) (hz : z ∈ APT)
    (e : Expr) (v : ℕ) (hs : small B τ e) (hd : den τ e = v) :
    Run B (.assign z e) τ (τ.setVar z v) (1 + e.size) ∧ Key n l Vn E d (τ.setVar z v) := by
  refine ⟨?_, K.set hz v⟩
  rw [← hd]
  exact asgE z e τ hs

/-- The rest of the numbers, on plain numbers. -/
theorem postTail_run (σ : Env) (l n Vn E d : ℕ) (hnn : σ.vars "nn" = n) (hlc : σ.vars "lc" = l)
    (hV : σ.vars "V" = Vn) (hEE : σ.vars "EE" = E) (hdg : σ.vars "dg" = d)
    (b0 : d < B) (b1 : Vn * d < B) (b2 : 3 + l + Vn + Vn * d < B) (b3 : d * n < B) (b4 : n + 1 < B)
    (b5 : l * (n + 1) + E < B) (b6 : (l * (n + 1) + E) * (3 + l + Vn + Vn * d) < B) :
    ∃ σ', Run B postTail σ σ' 300 ∧ σ'.vars "S2" = 2 + l + Vn + Vn * d ∧
      σ'.vars "CC" = 3 + l + Vn + Vn * d ∧ σ'.vars "B3" = 3 + l ∧ σ'.vars "B4" = 3 + l + Vn ∧
      σ'.vars "dn" = d * n ∧ σ'.vars "nn1" = n + 1 ∧ σ'.vars "LB" = l * (n + 1) ∧
      σ'.vars "DD" = l * (n + 1) + E ∧ σ'.vars "E2" = E / 2 ∧
      σ'.vars "DC" = (l * (n + 1) + E) * (3 + l + Vn + Vn * d) ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ ∀ y, y ∉ APT → σ'.vars y = σ.vars y := by
  have K0 : Key n l Vn E d σ := ⟨hnn, hlc, hV, hEE, hdg⟩
  obtain ⟨r1, K1⟩ := postStep (B := B) (σ) K0 "S2" (by decide) (.bin .add (.bin .add (.bin .add (.lit 2) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg"))) (2 + l + Vn + Vn * d)
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K0.1, K0.2.1, K0.2.2.1, K0.2.2.2.1, K0.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K0.1, K0.2.1, K0.2.2.1, K0.2.2.2.1, K0.2.2.2.2])
  generalize hσ1 : (σ).setVar "S2" (2 + l + Vn + Vn * d) = σ1 at r1 K1
  obtain ⟨r2, K2⟩ := postStep (B := B) (σ1) K1 "CC" (by decide) (.bin .add (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg"))) (3 + l + Vn + Vn * d)
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K1.1, K1.2.1, K1.2.2.1, K1.2.2.2.1, K1.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K1.1, K1.2.1, K1.2.2.1, K1.2.2.2.1, K1.2.2.2.2])
  generalize hσ2 : (σ1).setVar "CC" (3 + l + Vn + Vn * d) = σ2 at r2 K2
  obtain ⟨r3, K3⟩ := postStep (B := B) (σ2) K2 "B3" (by decide) (.bin .add (.lit 3) (V "lc")) (3 + l)
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K2.1, K2.2.1, K2.2.2.1, K2.2.2.2.1, K2.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K2.1, K2.2.1, K2.2.2.1, K2.2.2.2.1, K2.2.2.2.2])
  generalize hσ3 : (σ2).setVar "B3" (3 + l) = σ3 at r3 K3
  obtain ⟨r4, K4⟩ := postStep (B := B) (σ3) K3 "B4" (by decide) (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")) (3 + l + Vn)
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K3.1, K3.2.1, K3.2.2.1, K3.2.2.2.1, K3.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K3.1, K3.2.1, K3.2.2.1, K3.2.2.2.1, K3.2.2.2.2])
  generalize hσ4 : (σ3).setVar "B4" (3 + l + Vn) = σ4 at r4 K4
  obtain ⟨r5, K5⟩ := postStep (B := B) (σ4) K4 "dn" (by decide) (.bin .mul (V "dg") (V "nn")) (d * n)
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K4.1, K4.2.1, K4.2.2.1, K4.2.2.2.1, K4.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K4.1, K4.2.1, K4.2.2.1, K4.2.2.2.1, K4.2.2.2.2])
  generalize hσ5 : (σ4).setVar "dn" (d * n) = σ5 at r5 K5
  obtain ⟨r6, K6⟩ := postStep (B := B) (σ5) K5 "nn1" (by decide) (.bin .add (V "nn") (.lit 1)) (n + 1)
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K5.1, K5.2.1, K5.2.2.1, K5.2.2.2.1, K5.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K5.1, K5.2.1, K5.2.2.1, K5.2.2.2.1, K5.2.2.2.2])
  generalize hσ6 : (σ5).setVar "nn1" (n + 1) = σ6 at r6 K6
  obtain ⟨r7, K7⟩ := postStep (B := B) (σ6) K6 "LB" (by decide) (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))) (l * (n + 1))
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K6.1, K6.2.1, K6.2.2.1, K6.2.2.2.1, K6.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K6.1, K6.2.1, K6.2.2.1, K6.2.2.2.1, K6.2.2.2.2])
  generalize hσ7 : (σ6).setVar "LB" (l * (n + 1)) = σ7 at r7 K7
  obtain ⟨r8, K8⟩ := postStep (B := B) (σ7) K7 "DD" (by decide) (.bin .add (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))) (V "EE")) (l * (n + 1) + E)
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K7.1, K7.2.1, K7.2.2.1, K7.2.2.2.1, K7.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K7.1, K7.2.1, K7.2.2.1, K7.2.2.2.1, K7.2.2.2.2])
  generalize hσ8 : (σ7).setVar "DD" (l * (n + 1) + E) = σ8 at r8 K8
  obtain ⟨r9, K9⟩ := postStep (B := B) (σ8) K8 "E2" (by decide) (.bin .div (V "EE") (.lit 2)) (E / 2)
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K8.1, K8.2.1, K8.2.2.1, K8.2.2.2.1, K8.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K8.1, K8.2.1, K8.2.2.1, K8.2.2.2.1, K8.2.2.2.2])
  generalize hσ9 : (σ8).setVar "E2" (E / 2) = σ9 at r9 K9
  obtain ⟨r10, K10⟩ := postStep (B := B) (σ9) K9 "DC" (by decide) (.bin .mul (.bin .add (.bin .mul (V "lc") (.bin .add (V "nn") (.lit 1))) (V "EE")) (.bin .add (.bin .add (.bin .add (.lit 3) (V "lc")) (V "V")) (.bin .mul (V "V") (V "dg")))) ((l * (n + 1) + E) * (3 + l + Vn + Vn * d))
    (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K9.1, K9.2.1, K9.2.2.1, K9.2.2.2.1, K9.2.2.2.2]; omega) (by simp only [small_bin, small_var, small_lit, den_bin, den_var, den_lit, Bop.apply_add, Bop.apply_mul, Bop.apply_div, K9.1, K9.2.1, K9.2.2.1, K9.2.2.2.1, K9.2.2.2.2])
  generalize hσ10 : (σ9).setVar "DC" ((l * (n + 1) + E) * (3 + l + Vn + Vn * d)) = σ10 at r10 K10
  refine ⟨σ10, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq r10))))))))).mono
    (by simp [Expr.size]), ?_⟩
  subst hσ10 hσ9 hσ8 hσ7 hσ6 hσ5 hσ4 hσ3 hσ2 hσ1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try simp [Env.setVar]
  intro y hy
  simp only [APT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hy
  simp [Env.setVar, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

end Lax117284Proofs.Machine.MisAccept

end

/-! ### `Lax117284Proofs.Machine.MisRun` -/

section
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

end

/-! ### `Lax117284Proofs.Machine.MisCong` -/

section
/-!
Everything the reduction of Lemma 14 reads of its array is in the first `2 + V²` entries, and so an
array that agrees with the token values there has the same image.
-/

namespace Lax117284Proofs.Machine.MisCong

open Lax117284Proofs.Machine.MisSem
open Lax117284Proofs.Machine.MisFormat (VM)

/-- The arrays agree on the entries the reduction reads. -/
def AgrM (arr ns : List ℕ) : Prop := ∀ k < 2 + VM ns * VM ns, arr.getD k 0 = ns.getD k 0

variable {arr ns : List ℕ}

lemma lN_cong (h : AgrM arr ns) : lN arr = lN ns := h 0 (by omega)

lemma nN_cong (h : AgrM arr ns) : nN arr = nN ns := h 1 (by omega)

lemma VM_cong (h : AgrM arr ns) : VM arr = VM ns := by
  have h0 := lN_cong h
  have h1 := nN_cong h
  unfold lN at h0
  unfold nN at h1
  unfold VM
  rw [h0, h1]

lemma qualE_cong (h : AgrM arr ns) {t : ℕ} (ht : t < VM ns * VM ns) :
    qualE arr t = qualE ns t := by
  unfold qualE
  rw [VM_cong h, h (2 + t) (by omega)]

lemma edgeN_cong (h : AgrM arr ns) : edgeN arr = edgeN ns := by
  unfold edgeN
  rw [VM_cong h]
  exact List.countP_congr (fun t ht => by
    rw [qualE_cong h (List.mem_range.mp ht)])

lemma edgeCells_cong (h : AgrM arr ns) : edgeCellsN arr = edgeCellsN ns := by
  unfold edgeCellsN
  rw [VM_cong h]
  congr 1
  exact List.filter_congr (fun t ht => qualE_cong h (List.mem_range.mp ht))

lemma mat_cong (h : AgrM arr ns) {w w' : ℕ} (hw : w < VM ns) (hw' : w' < VM ns) :
    mat arr w w' = mat ns w w' := by
  unfold mat
  rw [VM_cong h]
  exact h _ (by have := cell_lt ns hw hw'; omega)

lemma rowSum_cong (h : AgrM arr ns) {w : ℕ} (hw : w < VM ns) : rowSum arr w = rowSum ns w := by
  unfold rowSum
  rw [VM_cong h]
  exact List.countP_congr (fun w' hw' => by
    rw [mat_cong h hw (List.mem_range.mp hw')])

lemma rowSum_zero_cong (h : AgrM arr ns) : rowSum arr 0 = rowSum ns 0 := by
  by_cases hv : 0 < VM ns
  · exact rowSum_cong h hv
  · have : VM ns = 0 := by omega
    unfold rowSum
    rw [VM_cong h, this]
    rfl

lemma degN_cong (h : AgrM arr ns) : degN arr = degN ns := by
  unfold degN; rw [rowSum_zero_cong h]

lemma spanN_cong (h : AgrM arr ns) : spanN arr = spanN ns := by
  unfold spanN; rw [lN_cong h, VM_cong h, degN_cong h]

lemma clN_cong (h : AgrM arr ns) : clN arr = clN ns := by
  unfold clN; rw [lN_cong h, VM_cong h, degN_cong h]

lemma daysN_cong (h : AgrM arr ns) : daysN arr = daysN ns := by
  unfold daysN; rw [lN_cong h, nN_cong h, edgeN_cong h]

lemma idxN_cong (h : AgrM arr ns) {w w' : ℕ} (hw : w' = 0 ∨ (w < VM ns ∧ w' ≤ VM ns)) :
    idxN arr w w' = idxN ns w w' := by
  unfold idxN
  rcases hw with hw | ⟨hw, hw'⟩
  · subst hw; rfl
  · exact List.countP_congr (fun x hx => by
      have hx' := List.mem_range.mp hx
      rw [mat_cong h hw (by omega)])

lemma PassM_cong (h : AgrM arr ns) {t : ℕ} (ht : t < VM ns * VM ns) :
    PassM arr t ↔ PassM ns t := by
  have hV : 0 < VM ns := by
    rcases Nat.eq_zero_or_pos (VM ns) with h0 | h0
    · rw [h0] at ht; omega
    · exact h0
  have hq : t / VM ns < VM ns := (Nat.div_lt_iff_lt_mul hV).2 ht
  have hr : t % VM ns < VM ns := Nat.mod_lt _ hV
  have hc := cell_lt ns hr hq
  unfold PassM
  rw [VM_cong h, nN_cong h, h (2 + t) (by omega), h (2 + (t % VM ns * VM ns + t / VM ns)) (by omega)]

lemma RegM_cong (h : AgrM arr ns) : RegM arr ↔ RegM ns := by
  unfold RegM
  rw [VM_cong h, rowSum_zero_cong h]
  constructor
  · rintro (h0 | ⟨h1, h2⟩)
    · exact Or.inl h0
    · exact Or.inr ⟨h1, fun w hw => by rw [← rowSum_cong h hw, h2 w hw]⟩
  · rintro (h0 | ⟨h1, h2⟩)
    · exact Or.inl h0
    · exact Or.inr ⟨h1, fun w hw => by rw [rowSum_cong h hw, h2 w hw]⟩

/-- **The check reads only the entries it should.** -/
lemma CondM_cong (h : AgrM arr ns) : CondM arr ↔ CondM ns := by
  unfold CondM
  rw [nN_cong h, VM_cong h, edgeN_cong h, RegM_cong h]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, fun t ht => (PassM_cong h ht).1 (h2 t ht), h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, fun t ht => (PassM_cong h ht).2 (h2 t ht), h3, h4⟩

lemma edgeCells_getD_lt (ns : List ℕ) (j : ℕ) :
    ((edgeCellsN ns).getD j (0, 0)).1 = 0 ∧ ((edgeCellsN ns).getD j (0, 0)).2 = 0 ∨
    ((edgeCellsN ns).getD j (0, 0)).1 < VM ns ∧ ((edgeCellsN ns).getD j (0, 0)).2 < VM ns := by
  by_cases hj : j < (edgeCellsN ns).length
  · right
    have hm := List.getElem_mem hj
    rw [← List.getD_eq_getElem _ (0, 0) hj] at hm
    generalize (edgeCellsN ns).getD j (0, 0) = q at hm ⊢
    unfold edgeCellsN at hm
    obtain ⟨t, ht, e⟩ := List.mem_map.mp hm
    have ht' := List.mem_range.mp (List.mem_filter.mp ht).1
    have hV : 0 < VM ns := by
      rcases Nat.eq_zero_or_pos (VM ns) with h0 | h0
      · rw [h0] at ht'; omega
      · exact h0
    rw [← e]
    exact ⟨(Nat.div_lt_iff_lt_mul hV).2 ht', Nat.mod_lt _ hV⟩
  · left
    rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨rfl, rfl⟩

lemma edgeDayN_cong (h : AgrM arr ns) {w w' : ℕ}
    (hw : (w = 0 ∧ w' = 0) ∨ (w < VM ns ∧ w' < VM ns)) (c : ℕ) :
    edgeDayN arr w w' c = edgeDayN ns w w' c := by
  have e1 : idxN arr w w' = idxN ns w w' := idxN_cong h (by omega)
  have e2 : idxN arr w' w = idxN ns w' w := idxN_cong h (by omega)
  unfold edgeDayN incIdN
  rw [e1, e2, lN_cong h, VM_cong h, degN_cong h, spanN_cong h]

lemma jobN_cong (h : AgrM arr ns) (i c : ℕ) : jobN arr i c = jobN ns i c := by
  unfold jobN
  simp only [lN_cong h, nN_cong h, edgeCells_cong h]
  split_ifs with h1 h2
  · unfold vertexDayN
    simp only [lN_cong h, nN_cong h, degN_cong h, spanN_cong h]
  · unfold validationDayN
    simp only [lN_cong h, nN_cong h, degN_cong h, spanN_cong h, VM_cong h]
  · exact edgeDayN_cong h (by
      rcases edgeCells_getD_lt ns (i - lN ns * (nN ns + 1)) with ⟨a, b⟩ | ⟨a, b⟩
      · exact Or.inl ⟨a, b⟩
      · exact Or.inr ⟨a, b⟩) c

lemma kvN_cong (h : AgrM arr ns) (c : ℕ) : kvN arr c = kvN ns c := by
  unfold kvN; rw [daysN_cong h, edgeN_cong h]

/-- **The image only depends on the entries the reduction reads.** -/
lemma outM_cong (h : AgrM arr ns) : outM arr = outM ns := by
  have hk : kvN arr = kvN ns := funext (kvN_cong h)
  unfold outM
  rw [clN_cong h, daysN_cong h, hk]
  simp only [jobN_cong h]

end Lax117284Proofs.Machine.MisCong

end

/-! ### `Lax117284Proofs.Machine.MisBound` -/

section
/-!
The word of the machine is large enough for everything the accepting phase of Lemma 14 computes,
and the phase costs at most a cubic in the number of tokens.
-/

namespace Lax117284Proofs.Machine.MisBound

open Lax117284Proofs.Machine.MisSem Lax117284Proofs.Machine.MisPrint Lax117284Proofs.Machine.MisChk
open Lax117284Proofs.Machine.MisRun
open Lax117284Proofs.Machine.MisJob (Mag)
open Lax117284Proofs.Machine.MisFormat (VM)

/-- **The cost of the accepting phase is a polynomial.** -/
theorem Kreal_le (Sz l Vn VVn DC CC : ℕ) (hV : Vn ≤ l) (hVV : VVn = Vn * Vn) (hVl : VVn ≤ l)
    (hDC : DC ≤ 12 * ((l + 1) * (l + 1))) (hCC : CC ≤ 4 * (l + 1)) :
    Kreal Sz Vn VVn DC CC ≤ 30000 * (Sz + 1) * (l + 1) ^ 3 := by
  unfold Kreal Kprint Kcell Kkv MisJob.Kjob Kchk
  have hA : 100 + (300 + (84 * VVn + 20) + 2 * (44 * Vn + 20)) + 2 * (48 * Sz + 50) + 10 + 4 ≤
      574 * ((l + 1) * (Sz + 1)) := by nlinarith [Nat.zero_le (l * Sz)]
  have hB := Nat.mul_le_mul hA hDC
  have hC : (100 + (48 * Sz + 50) + 10 + 4) * CC ≤ (164 + 48 * Sz) * (4 * (l + 1)) :=
    Nat.mul_le_mul (by omega) hCC
  have hD : ((40 + 4) * Vn + 100 + 4) * Vn = 44 * VVn + 104 * Vn := by rw [hVV]; ring
  obtain ⟨x, hx⟩ : ∃ x, x = l + 1 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = Sz + 1 := ⟨_, rfl⟩
  have hx1 : 1 ≤ x := by omega
  have hy1 : 1 ≤ y := by omega
  have hxx : x ≤ x * x := Nat.le_mul_of_pos_left _ (by omega)
  have hxxx : x * x ≤ x * x * x := Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = x * x * x * y := ⟨_, rfl⟩
  have hZx : x ≤ Z := by
    rw [hZ]; calc x ≤ x * x := hxx
      _ ≤ x * x * x := hxxx
      _ ≤ x * x * x * y := Nat.le_mul_of_pos_right _ (by omega)
  have hZy : y ≤ Z := by
    rw [hZ]; calc y ≤ 1 * y := by omega
      _ ≤ x * x * x * y := Nat.mul_le_mul_right _ (by have := Nat.mul_le_mul hxx hx1; nlinarith)
  have hZxy : x * y ≤ Z := by
    rw [hZ]; exact Nat.mul_le_mul_right _ (le_trans hxx hxxx)
  have hZ2 : 12 * (x * x) * (574 * (x * y)) ≤ 6888 * Z := by
    rw [hZ]; nlinarith [Nat.zero_le (x * x * x * y)]
  have hxy : (l + 1) * (Sz + 1) = x * y := by rw [hx, hy]
  have hxx' : (l + 1) * (l + 1) = x * x := by rw [hx]
  rw [hxy, hxx'] at hB
  have hcube : 30000 * (Sz + 1) * (l + 1) ^ 3 = 30000 * Z := by rw [hZ, ← hx, ← hy]; ring
  rw [hcube]
  have hC' : (164 + 48 * Sz) * (4 * (l + 1)) ≤ 656 * Z := by
    have : (164 + 48 * Sz) * (4 * (l + 1)) ≤ 656 * (x * y) := by
      rw [hx, hy]; nlinarith [Nat.zero_le (l * Sz)]
    omega
  have hB' : (100 + (300 + (84 * VVn + 20) + 2 * (44 * Vn + 20)) + 2 * (48 * Sz + 50) + 10 + 4) * DC ≤
      6888 * Z := by
    calc _ ≤ 574 * (x * y) * (12 * (x * x)) := hB
      _ = 12 * (x * x) * (574 * (x * y)) := by ring
      _ ≤ 6888 * Z := hZ2
  omega

lemma Mag_cong {arr ns : List ℕ} (h : MisCong.AgrM arr ns) : Mag arr = Mag ns := by
  unfold Mag
  rw [MisCong.spanN_cong h, MisCong.degN_cong h, MisCong.nN_cong h]

section Shape

variable {ns : List ℕ}

lemma VM_le_len (hsh : MisFormat.ShapeM ns) : VM ns ≤ ns.length := by
  obtain ⟨-, hl, -⟩ := hsh
  rcases Nat.eq_zero_or_pos (VM ns) with h | h
  · omega
  · have := Nat.le_mul_of_pos_left (VM ns) h; omega

lemma VV_le_len (hsh : MisFormat.ShapeM ns) : VM ns * VM ns ≤ ns.length := by
  obtain ⟨-, hl, -⟩ := hsh; omega

lemma edgeN_le (ns : List ℕ) : edgeN ns ≤ VM ns * VM ns := by
  unfold edgeN
  have := List.countP_le_length (p := qualE ns) (l := List.range (VM ns * VM ns))
  simpa using this

lemma rowSum_le (ns : List ℕ) : rowSum ns 0 ≤ VM ns := by
  unfold rowSum
  have := List.countP_le_length (p := fun w' => decide (mat ns 0 w' = 1)) (l := List.range (VM ns))
  simpa using this

lemma degN_le (ns : List ℕ) : degN ns ≤ VM ns + 1 := by
  have := rowSum_le ns
  unfold degN; omega

lemma lN_le_VM (h : 4 ≤ nN ns) : lN ns ≤ VM ns := by
  rw [MisSem.VM_eq]; exact Nat.le_mul_of_pos_right _ (by omega)

lemma daysN_le (hsh : MisFormat.ShapeM ns) (h : 4 ≤ nN ns) : daysN ns ≤ 3 * ns.length := by
  have h1 := VM_le_len hsh
  have h2 := VV_le_len hsh
  have h3 := edgeN_le ns
  have h4 := lN_le_VM h
  have h5 : lN ns * (nN ns + 1) = VM ns + lN ns := by rw [Nat.mul_add, Nat.mul_one, MisSem.VM_eq]
  unfold daysN; omega

lemma clN_le (hsh : MisFormat.ShapeM ns) (h : 4 ≤ nN ns) : clN ns ≤ 4 * ns.length + 3 := by
  have h1 := VM_le_len hsh
  have h2 := VV_le_len hsh
  have h4 := lN_le_VM h
  have h5 : VM ns * degN ns ≤ VM ns * (VM ns + 1) := Nat.mul_le_mul_left _ (degN_le ns)
  have h6 : VM ns * (VM ns + 1) = VM ns * VM ns + VM ns := by rw [Nat.mul_add, Nat.mul_one]
  unfold clN; omega

end Shape

/-- **The numbers of the accepting phase fit in the word.** -/
theorem accept_bounds (ns : List ℕ) (B L : ℕ) (hsh : MisFormat.ShapeM ns)
    (hlL : ns.length ≤ L) (hv : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1))
    (hB : 2 ^ (2 * L + 4) + 8 * L + 64 ≤ B) :
    (∀ k < VM ns * VM ns, ns.getD (2 + k) 0 + 8 < B) ∧ lN ns + 8 < B ∧ nN ns + 8 < B ∧
    VM ns * VM ns + 2 * VM ns + nN ns + 40 < B ∧
    2 * (VM ns * VM ns) + 2 * VM ns + 2 * lN ns + 60 < B ∧
    (CondM ns → Mag ns + 4 < B) ∧
    (CondM ns → daysN ns * clN ns + clN ns + daysN ns + 100 < B) := by
  have hsh0 := hsh
  obtain ⟨h2, hl, -⟩ := hsh
  have h1 := VM_le_len hsh0
  have h3 := VV_le_len hsh0
  obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ L := ⟨_, rfl⟩
  have hPL : L + 1 ≤ P := by rw [hP]; exact Nat.lt_two_pow_self
  have hP4 : 4 ≤ P := by
    rw [hP]; calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * P := by rw [hP]; ring
  have hpow2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (P * P) := by rw [hP]; ring
  rw [hpow2] at hB
  rw [hpow1] at hv
  have hPP : 4 * P ≤ P * P := Nat.mul_le_mul_right P hP4
  have hLL : L * L + 2 * L + 1 ≤ P * P := by nlinarith [Nat.mul_le_mul hPL hPL]
  have hl0 : lN ns < 2 * P := hv 0 (by omega)
  have hn0 : nN ns < 2 * P := hv 1 (by omega)
  refine ⟨fun k hk => ?_, by omega, by omega, by omega, by omega, fun hc => ?_, fun hc => ?_⟩
  · have := hv (2 + k) (by omega); omega
  · have h4 : 4 ≤ nN ns := hc.1
    have hdg := degN_le ns
    have hsp : spanN ns ≤ 2 + 4 * L := by
      have h5 : VM ns * degN ns ≤ VM ns * (VM ns + 1) := Nat.mul_le_mul_left _ hdg
      have h6 : VM ns * (VM ns + 1) = VM ns * VM ns + VM ns := by rw [Nat.mul_add, Nat.mul_one]
      have := lN_le_VM h4
      unfold spanN; omega
    have hdn : degN ns * nN ns ≤ 2 * (P * P) := by
      calc degN ns * nN ns ≤ P * (2 * P) := Nat.mul_le_mul (by omega) (by omega)
        _ = 2 * (P * P) := by ring
    unfold Mag; omega
  · have h4 : 4 ≤ nN ns := hc.1
    have hd := daysN_le hsh0 h4
    have hcl := clN_le hsh0 h4
    have hDC : daysN ns * clN ns ≤ (3 * L) * (4 * L + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hDC' : (3 * L) * (4 * L + 3) = 12 * (L * L) + 9 * L := by ring
    omega

end Lax117284Proofs.Machine.MisBound

end

/-! ### `Lax117284Proofs.Machine.MisFinal` -/

section
/-!
The reduction of Lemma 14 from the multicoloured independent set problem to the problem with the
fairness parameter of every client given is polynomial-time computable.
-/

namespace Lax117284Proofs.Machine.MisFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists
open Lax117284Proofs.Machine.MisFormat Lax117284Proofs.Machine.MisSem Lax117284Proofs.Machine.MisCong
open Lax117284Proofs.Machine.MisRun Lax117284Proofs.Machine.MisBound Lax117284Proofs.Machine.MisAccept
open Lax117284Proofs.Machine.WrapT Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.TokModel
open Lax117284Proofs.Machine.TokProg (Tok.val)

open scoped Classical

lemma getD_eq_of_take' {arr ns : List ℕ} (h : arr.take ns.length = ns) :
    ∀ k < ns.length, arr.getD k 0 = ns.getD k 0 := fun k hk => by
  conv_rhs => rw [← h]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]

/-- The cost of the accepting phase. -/
def KaccM (Sz l : ℕ) : ℕ := 30000 * (Sz + 1) * (l + 1) ^ 3

lemma KaccM_mono (Sz a b : ℕ) (h : a ≤ b) : KaccM Sz a ≤ KaccM Sz b := by
  unfold KaccM
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)

/-- **The reduction as a reduction on tokens.** -/
noncomputable def W : WrapT where
  E := EM
  nk := MisNk.nkM
  Knk := 80
  hnk := fun B Bt cap hB => MisNk.nkM_spec (B := B) Bt cap hB
  red := Lax117284.Lemma14.reduce
  cond := fun ts => CondM (ts.map Tok.val)
  outW := fun ts => numCode (outM (ts.map Tok.val))
  sem_acc := fun ts hc hcond => t14_eq ts hc hcond
  rejW := rejectedPerClient
  sem_rej := fun w h => t14_rej w h
  rej := FreeAccept.rejectPrint
  Krej := fun Sz => 3 * (48 * Sz + 50)
  rejRun := fun B Sz σ hs hB => by
    obtain ⟨σ', r, o, -, -⟩ := FreeAccept.rejectPrint_run (B := B) Sz σ hs hB
    exact ⟨σ', r, by rw [o, rejectedPerClient_eq, FreeMain.natBits_rejected]⟩
  acc := acceptM
  Kacc := KaccM
  Kmono := KaccM_mono
  accRun := fun B Sz L ts arr σ hconf harr hA hlenL hvals hB hs => by
    obtain ⟨hshape, hts⟩ := shape_of_conforms hconf
    obtain ⟨ns, hns⟩ : ∃ ns, ts.map Tok.val = ns := ⟨_, rfl⟩
    rw [hns] at hshape
    have hlenns : ns.length = ts.length := by rw [← hns]; simp
    have harr' : arr.take ns.length = ns := by rw [hlenns, ← hns]; exact harr
    have hg := getD_eq_of_take' harr'
    obtain ⟨h2, hl, hsg⟩ := hshape
    have hshape' : ShapeM ns := ⟨h2, hl, hsg⟩
    have hAg : AgrM arr ns := fun k hk => hg k (by omega)
    have hlenA : ns.length ≤ arr.length := by
      have := congrArg List.length harr'
      rw [List.length_take] at this
      omega
    have hval : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1) := by
      intro k hk
      rw [List.getD_eq_getElem _ _ hk]
      have hk' : k < (ts.map Tok.val).length := by rw [hns]; exact hk
      obtain ⟨t, ht, e⟩ := List.mem_map.mp (List.getElem_mem hk')
      have : (ts.map Tok.val)[k] = ns[k] := by simp [hns]
      rw [← this, ← e]
      exact hvals t ht
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := accept_bounds ns B L hshape' (by omega) hval hB
    have hVM := VM_cong hAg
    have hlN := lN_cong hAg
    have hnN := nN_cong hAg
    have hcond := CondM_cong hAg
    have hE : ∀ k < VM arr * VM arr, arr.getD (2 + k) 0 + 8 < B := by
      intro k hk
      rw [hVM] at hk
      rw [hAg (2 + k) (by omega)]
      exact b1 k hk
    obtain ⟨σ', r, o⟩ := acceptM_run (B := B) Sz arr σ hs hA (by rw [hVM]; omega) hE
      (by rw [hlN]; exact b2) (by rw [hnN]; exact b3)
      (by rw [hVM, hnN]; exact b4) (by rw [hVM, hlN]; exact b5)
      (fun hc => by
        have := b6 (hcond.1 hc)
        rw [Mag_cong hAg]; exact this)
      (fun hc => by
        have := b7 (hcond.1 hc)
        rw [daysN_cong hAg, clN_cong hAg]; exact this)
    refine ⟨σ', r.mono ?_, ?_⟩
    · show Kreal Sz (VM arr) (VM arr * VM arr) (if CondM arr then daysN arr * clN arr else 0)
          (if CondM arr then clN arr else 0) ≤ KaccM Sz ts.length
      unfold KaccM
      rw [← hlenns, hVM]
      have h1 := VM_le_len hshape'
      have h3 := VV_le_len hshape'
      by_cases hc : CondM arr
      · simp only [if_pos hc]
        rw [daysN_cong hAg, clN_cong hAg]
        have h4 : 4 ≤ nN ns := ((hcond.1 hc).1)
        have hd := daysN_le hshape' h4
        have hcl := clN_le hshape' h4
        exact Kreal_le Sz ns.length (VM ns) (VM ns * VM ns) _ _ h1 rfl h3
          (le_trans (Nat.mul_le_mul hd hcl) (by nlinarith)) (by omega)
      · simp only [if_neg hc]
        exact Kreal_le Sz ns.length (VM ns) (VM ns * VM ns) 0 0 h1 rfl h3 (by omega) (by omega)
    · rw [o]
      congr 1
      show _ = if CondM (ts.map Tok.val) then natBits (numCode (outM (ts.map Tok.val)))
        else natBits rejectedPerClient
      rw [hns]
      by_cases hc : CondM ns
      · rw [if_pos (hcond.2 hc), if_pos hc, outM_cong hAg, natBits_numCode]
      · rw [if_neg (fun h => hc (hcond.1 h)), if_neg hc, rejectedPerClient_eq,
          FreeMain.natBits_rejected]

/-- The scalars of the program. -/
def layoutM : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "v", "s", "u", "i2", "ix", "aa", "M", "B3", "B4", "CC", "DC", "DD", "E2", "EE", "LB", "S2", "V", "VV", "bd", "bs", "ca", "cb", "cc", "cnt", "dg", "di", "dm", "dn", "dv", "e", "eh", "em", "ee", "fm", "fq", "fr", "fw", "fw2", "k1", "k2", "lc", "ma", "nn", "nn1", "ok", "pv", "qa", "ra", "rb", "rr", "ta", "tb", "va", "vb", "xa", "xf", "xj", "ya"],
    ["a", "TK"], 12⟩

theorem com_ok : Com.Ok layoutM W.mainW := by
  simp [WrapT.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, MisNk.nkM,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptM, prepM, postM, dgM, postTail, MisPrint.printM, MisPrint.cellBody, MisPrint.kvBody,
    MisChk.checkCom, MisChk.checkPA, MisChk.checkPB, MisCheck.guard, MisCheck.impGuard,
    MisCheck.chkA, MisCheck.chkALoop, MisCheck.chkB, MisCheck.chkBLoop,
    MisCount.cntCom, MisCount.cntLoop, MisCount.cntBody,
    MisFind.findCom, MisFind.findLoop, MisFind.findBody,
    MisJob.jobCom, MisJob.pdCom, MisJob.vertexCom, MisJob.validCom, MisJob.validNext,
    MisJob.edgeDisp, MisJob.edgeCom,
    FreeAccept.rejectPrint, Out.outLoop, Out.emitTK, Out.emitAt, Out.emitVal, Out.emitVar,
    Out.emitLit, EmitNat.emitNat, EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop,
    EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody, layoutM, Com.Ok, Cond.Ok, condExpr,
    Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 30000 * (Sz + 1) * (l + 1) ^ 3 := by
  intro Sz l
  show KaccM Sz l ≤ _
  exact le_refl _

/--
---
conclusion: Lax117284.Lemma14.reduce_polyTime
---
The reduction is a word RAM program on the zeros and ones of its input: a one-pass tokenizer reads
the number of colours, the number of vertices per colour, and the bits of the adjacency matrix; a
first pass over the matrix checks that it is symmetric, has no loop and no edge inside a colour
class; a second checks that the graph is regular of a positive degree and has an even number of
edges, by counting the neighbours of every vertex; and the numbers of the image are then written
cell by cell, the processing time and the due date of each job being a closed form computed from
its day and its client: a case analysis on the kind of day — a vertex day, a validation day or the
day of an edge, whose endpoints are found by scanning the matrix for the corresponding edge — and
on the kind of client. The number of colours and the number of vertices are numbers of the input
and are bounded by its length, since the image is only written for a graph. A word that is not the
code of such a graph is answered with the rejected word. The numbers may be exponential in the
length of the input, which the word length of a polynomial-time word RAM accommodates, and
polynomial time on the word RAM transfers to a Turing machine.
-/
theorem reduce_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id id Lax117284.Lemma14.reduce) :=
  WrapTFinal.polyTimeE W layoutM com_ok rfl (by simp [layoutM]) 30000 3 (by omega) Kpoly
    (fun Sz => by
      show 3 * (48 * Sz + 50) ≤ 30000 * (Sz + 1)
      omega)

end Lax117284Proofs.Machine.MisFinal

end
