import Lax117284Proofs.Machine.MisCount

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
