import Lax117284Proofs.Machine.MisCheck

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
