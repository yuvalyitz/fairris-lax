import Lax117284Proofs.Machine.TwRamDefs

/-!
The blocks of the interpreter that compute what an instruction stores and where: each leaves the
destination in `ta` and the value, already reduced modulo `2 ^ Wp`, in `t1`.
-/

namespace Lax117284Proofs.Machine.TwRam

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

variable {B : ℕ}

/-- The environment `σ'` is `σ` with the scratch scalars `ta`, `t1`, `t2` changed, `ta` and `t1`
to the destination `d` and the value `v`. -/
structure Wr (σ σ' : Env) (d v : ℕ) : Prop where
  ta : σ'.vars "ta" = d
  t1 : σ'.vars "t1" = v
  arrs : σ'.arrs = σ.arrs
  fr : ∀ x, x ≠ "ta" → x ≠ "t1" → x ≠ "t2" → σ'.vars x = σ.vars x

/-- Normalize the reads of an updated environment. -/
macro "nrm" : tactic => `(tactic| simp only [vars_setVar, arrs_setVar, inp_setVar, out_setVar,
  vars_setArr, ↓reduceIte, String.reduceEq, eq_self])

lemma land_le (a b : ℕ) : Nat.land a b ≤ a := Nat.and_le_left

lemma mod_eq' (x P : ℕ) : x - x / P * P = x % P := by
  rw [Nat.mod_eq_sub_mul_div, Nat.mul_comm]

/-- The side goals of a walk over a block that reduces modulo `P`. -/
macro "side" : tactic => `(tactic| first
  | omega
  | (nrm <;> omega)
  | (nrm; exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) (by omega))
  | (nrm; exact lt_of_le_of_lt (Nat.sub_le _ _) (by omega))
  | (nrm; exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
  | (nrm; exact lt_of_le_of_lt (land_le _ _) (by omega)))

/-- The unchanged parts of a `Wr`. -/
macro "wr_fr" : tactic => `(tactic| (intro x h1 h2 h3; simp only [vars_setVar, h1, h2, h3,
  ↓reduceIte, if_false]))

def cSet : Com := .seq (.assign "ta" (V "ia")) (.assign "t1" (V "ib"))
def modP : Com := .assign "t1" (sub (V "t1") (mul (dvd (V "t1") (V "P")) (V "P")))
def cAdd : Com := .seq (.assign "ta" (V "ia"))
  (.seq (.assign "t1" (add (G "M" (V "ib")) (G "M" (V "ic")))) modP)

theorem cSet_run {Pn : ℕ} {σ : Env} (hP : Pn < B) (ha : σ.vars "ia" < Pn) (hb : σ.vars "ib" < Pn) :
    ∃ σ', Run B cSet σ σ' 10 ∧ Wr σ σ' (σ.vars "ia") (σ.vars "ib") := by
  unfold cSet
  run_vcg
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm
  · nrm
  · wr_fr

/-- The reads of `M` at two operands, in terms of the machine state. -/
structure Ops (Pn : ℕ) (y : List ℕ) (s : State) (σ : Env) : Prop where
  ia : σ.vars "ia" < Pn
  ib : σ.vars "ib" < Pn
  ic : σ.vars "ic" < Pn
  e1 : (σ.arrs "M").getD (σ.vars "ib") 0 = s.mem (σ.vars "ib")
  e2 : (σ.arrs "M").getD (σ.vars "ic") 0 = s.mem (σ.vars "ic")
  f1 : s.mem (σ.vars "ib") < Pn
  f2 : s.mem (σ.vars "ic") < Pn
  e3 : (σ.arrs "M").getD (σ.vars "ia") 0 = s.mem (σ.vars "ia")
  f3 : s.mem (σ.vars "ia") < Pn
  e4 : (σ.arrs "M").getD (s.mem (σ.vars "ib")) 0 = s.mem (s.mem (σ.vars "ib"))
  f4 : s.mem (s.mem (σ.vars "ib")) < Pn
  Pv : σ.vars "P" = Pn
  Mlen : (σ.arrs "M").length = Pn

lemma Ops.mk' {Wp Pn : ℕ} {y : List ℕ} {P : Program} {OL : ℕ} {s : State} {σ : Env}
    (hR : Rel Pn y s σ) (hC : Cst Wp Pn P y OL σ) (ha : σ.vars "ia" < Pn)
    (hb : σ.vars "ib" < Pn) (hc : σ.vars "ic" < Pn) : Ops Pn y s σ :=
  ⟨ha, hb, hc, hR.M _ hb, hR.M _ hc, hR.mem _, hR.mem _, hR.M _ ha, hR.mem _,
    hR.M _ (hR.mem _), hR.mem _, hC.Pv, hC.Mlen⟩

theorem cAdd_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ)
    (hP : Pn + Pn < B) :
    ∃ σ', Run B cAdd σ σ' 40 ∧
      Wr σ σ' (σ.vars "ia") ((s.mem (σ.vars "ib") + s.mem (σ.vars "ic")) % Pn) := by
  have ha := hO.ia
  have hb := hO.ib
  have hc := hO.ic
  have e1 := hO.e1
  have e2 := hO.e2
  have f1 := hO.f1
  have f2 := hO.f2
  have e3 := hO.e3
  have f3 := hO.f3
  have e4 := hO.e4
  have f4 := hO.f4
  have hPv := hO.Pv
  have hL := hO.Mlen
  clear hO
  unfold cAdd modP
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm
    rw [e1, e2, hPv]
    exact mod_eq' _ _
  · nrm
  · wr_fr

def cLoad : Com := .seq (.assign "ta" (V "ia")) (.assign "t1" (G "M" (G "M" (V "ib"))))
def cStore : Com := .seq (.assign "ta" (G "M" (V "ia"))) (.assign "t1" (G "M" (V "ib")))
def cSub : Com := .seq (.assign "ta" (V "ia")) (.assign "t1" (sub (G "M" (V "ib")) (G "M" (V "ic"))))
def cMul : Com := .seq (.assign "ta" (V "ia"))
  (.seq (.assign "t1" (mul (G "M" (V "ib")) (G "M" (V "ic")))) modP)
def cDiv : Com := .seq (.assign "ta" (V "ia")) (.assign "t1" (dvd (G "M" (V "ib")) (G "M" (V "ic"))))
def cAnd : Com := .seq (.assign "ta" (V "ia")) (.assign "t1" (.bin .and (G "M" (V "ib")) (G "M" (V "ic"))))
/-- The shift, without a case split: `t2` is `1` if the shift amount is below the word length and
`0` otherwise, and the amount is multiplied by it. -/
def cShl : Com := .seq (.assign "ta" (V "ia"))
  (.seq (.assign "t2" (sub (V "wp") (G "M" (V "ic"))))
    (.seq (.assign "t2" (dvd (V "t2") (V "t2")))
      (.seq (.assign "t1" (.bin .shiftl (G "M" (V "ib")) (mul (G "M" (V "ic")) (V "t2"))))
        (.seq modP (.assign "t1" (mul (V "t1") (V "t2")))))))
def cNot : Com := .seq (.assign "ta" (V "ia")) (.assign "t1" (sub (sub (V "P") (L 1)) (G "M" (V "ib"))))
def cIlen : Com := .seq (.assign "ta" (V "ia")) (.assign "t1" (V "ylen"))
def cIload : Com :=
  .seq (.ite (.lt (G "M" (V "ib")) (V "ylen")) (.assign "t1" (G "Y" (G "M" (V "ib"))))
    (.assign "t1" (L 0))) (.assign "ta" (V "ia"))

/-- All the fields of a `Wr` except the value. -/
macro "wr_rest" : tactic => `(tactic| (refine ⟨?_, ?_, ?_, ?_⟩ <;> first
  | (nrm; done) | wr_fr | skip))

theorem cLoad_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ) (hB : Pn < B) :
    ∃ σ', Run B cLoad σ σ' 30 ∧ Wr σ σ' (σ.vars "ia") (s.mem (s.mem (σ.vars "ib"))) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  unfold cLoad
  run_vcg
  all_goals try side
  all_goals try (nrm; rw [e1, e4]; omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; rw [e1]; exact e4
  · nrm
  · wr_fr

theorem cStore_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ) (hB : Pn < B) :
    ∃ σ', Run B cStore σ σ' 30 ∧ Wr σ σ' (s.mem (σ.vars "ia")) (s.mem (σ.vars "ib")) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  unfold cStore
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm; exact e3
  · nrm; exact e1
  · nrm
  · wr_fr

theorem cSub_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ) (hB : Pn < B) :
    ∃ σ', Run B cSub σ σ' 40 ∧
      Wr σ σ' (σ.vars "ia") (s.mem (σ.vars "ib") - s.mem (σ.vars "ic")) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  unfold cSub
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; rw [e1, e2]
  · nrm
  · wr_fr

theorem cMul_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ)
    (hB : Pn * Pn < B) :
    ∃ σ', Run B cMul σ σ' 60 ∧
      Wr σ σ' (σ.vars "ia") ((s.mem (σ.vars "ib") * s.mem (σ.vars "ic")) % Pn) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  have hp : s.mem (σ.vars "ib") * s.mem (σ.vars "ic") < B :=
    lt_of_lt_of_le (Nat.mul_lt_mul'' f1 f2) hB.le
  have hp' : (σ.arrs "M").getD (σ.vars "ib") 0 * (σ.arrs "M").getD (σ.vars "ic") 0 < B := by
    rw [e1, e2]; exact hp
  have hPB : Pn < B := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by omega)) hB
  unfold cMul modP
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; rw [e1, e2, hPv]; exact mod_eq' _ _
  · nrm
  · wr_fr


theorem cDiv_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ) (hB : Pn < B) :
    ∃ σ', Run B cDiv σ σ' 40 ∧
      Wr σ σ' (σ.vars "ia") (s.mem (σ.vars "ib") / s.mem (σ.vars "ic")) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  unfold cDiv
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; rw [e1, e2]
  · nrm
  · wr_fr

theorem cAnd_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ) (hB : Pn < B) :
    ∃ σ', Run B cAnd σ σ' 40 ∧
      Wr σ σ' (σ.vars "ia") (Nat.land (s.mem (σ.vars "ib")) (s.mem (σ.vars "ic"))) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  unfold cAnd
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; rw [e1, e2]
  · nrm
  · wr_fr

theorem cNot_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ) (hB : Pn < B) :
    ∃ σ', Run B cNot σ σ' 40 ∧
      Wr σ σ' (σ.vars "ia") (Pn - 1 - s.mem (σ.vars "ib")) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  unfold cNot
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; rw [e1, hPv]
  · nrm
  · wr_fr

theorem cIlen_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hylen : σ.vars "ylen" = y.length)
    (hB : y.length < B) (hP : Pn < B) (ha : σ.vars "ia" < Pn) :
    ∃ σ', Run B cIlen σ σ' 20 ∧ Wr σ σ' (σ.vars "ia") y.length := by
  unfold cIlen
  run_vcg
  all_goals try side
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; exact hylen
  · nrm
  · wr_fr



lemma div_self_le (a : ℕ) : a / a ≤ 1 := by
  rcases Nat.eq_zero_or_pos a with h | h
  · simp [h]
  · rw [Nat.div_self h]

lemma flag_eq (c W : ℕ) : (W - c) / (W - c) = if c < W then 1 else 0 := by
  by_cases h : c < W
  · rw [if_pos h]; exact Nat.div_self (by omega)
  · rw [if_neg h]; have : W - c = 0 := by omega
    rw [this]

lemma shl_bound {Pn Wp B b c : ℕ} (hPn : Pn = 2 ^ Wp) (hB : Pn * Pn < B) (hb : b < Pn) :
    b * 2 ^ (c * ((Wp - c) / (Wp - c))) < B := by
  rw [flag_eq]
  by_cases h : c < Wp
  · rw [if_pos h, Nat.mul_one]
    have h1 : 2 ^ c < Pn := by rw [hPn]; exact Nat.pow_lt_pow_right (by omega) h
    exact lt_of_lt_of_le (Nat.mul_lt_mul'' hb h1) hB.le
  · rw [if_neg h]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
    have hp : 0 < Pn := hPn ▸ Nat.two_pow_pos _
    exact lt_of_lt_of_le hb ((Nat.le_mul_of_pos_left _ hp).trans hB.le)

theorem cShl_run {Pn Wp : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ)
    (hB : Pn * Pn < B) (hPn : Pn = 2 ^ Wp) (hwp : σ.vars "wp" = Wp) :
    ∃ σ', Run B cShl σ σ' 80 ∧
      Wr σ σ' (σ.vars "ia")
        (if s.mem (σ.vars "ic") < Wp then (s.mem (σ.vars "ib") * 2 ^ s.mem (σ.vars "ic")) % Pn
          else 0) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  have hPB : Pn < B := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by omega)) hB
  have hW : Wp < B := lt_of_lt_of_le (hPn ▸ Nat.lt_two_pow_self) hPB.le
  have hsh := shl_bound (b := s.mem (σ.vars "ib")) (c := s.mem (σ.vars "ic")) hPn hB f1
  have hshg : (σ.arrs "M").getD (σ.vars "ib") 0 *
      2 ^ ((σ.arrs "M").getD (σ.vars "ic") 0 *
        ((σ.vars "wp" - (σ.arrs "M").getD (σ.vars "ic") 0) /
          (σ.vars "wp" - (σ.arrs "M").getD (σ.vars "ic") 0))) < B := by
    rw [e1, e2, hwp]; exact hsh
  unfold cShl modP
  run_vcg
  all_goals try side
  all_goals try (nrm; rw [hwp]; exact hW)
  all_goals try (nrm; rw [e2, hwp, flag_eq]; split_ifs <;> omega)
  all_goals try (nrm; rw [e1, e2, hwp]; exact hsh)
  all_goals try (nrm; exact lt_of_le_of_lt (Nat.div_le_self _ _) hshg)
  all_goals try (nrm; exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) hshg)
  all_goals try (nrm; exact lt_of_le_of_lt (Nat.sub_le _ _) hshg)
  all_goals try (nrm; exact lt_of_le_of_lt ((Nat.mul_le_mul_left _ (div_self_le _)).trans_eq
    (Nat.mul_one _)) (lt_of_le_of_lt (Nat.sub_le _ _) hshg))
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm
  · nrm
    rw [e1, e2, hwp, hPv, mod_eq', flag_eq]
    by_cases h : s.mem (σ.vars "ic") < Wp
    · simp [h]
    · simp [h]
  · nrm
  · wr_fr


theorem cIload_run {Pn : ℕ} {y : List ℕ} {s : State} {σ : Env} (hO : Ops Pn y s σ)
    (hB : Pn < B) (hY : σ.arrs "Y" = y) (hylen : σ.vars "ylen" = y.length)
    (hyB : ∀ v ∈ y, v < B) (hyl : y.length < B) :
    ∃ σ', Run B cIload σ σ' 40 ∧
      Wr σ σ' (σ.vars "ia") (if s.mem (σ.vars "ib") < y.length then y.getD (s.mem (σ.vars "ib")) 0
        else 0) := by
  obtain ⟨ha, hb, hc, e1, e2, f1, f2, e3, f3, e4, f4, hPv, hL⟩ := hO
  have hyg : ∀ k, (σ.arrs "Y").getD k 0 < B := by
    intro k; rw [hY]
    by_cases hk : k < y.length
    · have := hyB (y.getD k 0) (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk)
      simpa using this
    · rw [getD_of_le (by omega)]; omega
  have hYl : (σ.arrs "Y").length = y.length := by rw [hY]
  unfold cIload
  run_vcg
  all_goals try side
  all_goals try exact hyg _
  all_goals refine ⟨?_, ?_, ?_, ?_⟩
  all_goals try nrm
  all_goals try wr_fr
  · rw [e1, hY, if_pos (by omega)]
  · rw [if_neg (by omega)]

end Lax117284Proofs.Machine.TwRam
