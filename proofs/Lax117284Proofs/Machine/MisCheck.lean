import Lax117284Proofs.Machine.MisFind
import Lax117284Proofs.Machine.Flag

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
