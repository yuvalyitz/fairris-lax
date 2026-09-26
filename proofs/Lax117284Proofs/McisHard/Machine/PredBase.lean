import Lax117284Proofs.McisHard.Machine.PredInfra

/-!
# Clause-level commands for the adjacency bit (WP6)

`compCom` (the literals of two positions are complementary), `cidCom` (the clause number of a position),
`clauseCom` (the size of the clause of a position and the position `mateN`).
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Bit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284Proofs.Machine.SatRank Lax117284Proofs.Machine.SatOps Lax117284Proofs.Machine.T9Ops

variable {B : ℕ}

/-! ### The comparison of the literals of two positions -/

def compCom : Com :=
  .seq (.assign "bv1" (.get "TK" (add (.lit 3) (mul (.lit 2) (V "ba")))))
  (.seq (.assign "bs1" (.get "TK" (add (.lit 4) (mul (.lit 2) (V "ba")))))
  (.seq (.assign "bv2" (.get "TK" (add (.lit 3) (mul (.lit 2) (V "bb")))))
  (.seq (.assign "bs2" (.get "TK" (add (.lit 4) (mul (.lit 2) (V "bb")))))
  (.ite (.eq (V "bv1") (V "bv2"))
    (.ite (.eq (V "bs1") (V "bs2")) (.assign "bc" (.lit 0)) (.assign "bc" (.lit 1)))
    (.assign "bc" (.lit 0))))))

@[simp] def AComp : List String := ["bv1", "bs1", "bv2", "bs2", "bc"]

set_option maxHeartbeats 1600000 in
theorem compCom_spec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns ∧ σ.vars "bb" < SlotsN ns) compCom
      (fun σ σ' => σ'.vars "bc" = ind (compN ns (σ.vars "ba") (σ.vars "bb"))) 60 := by
  have hE1 := hP.hE1
  have hE2 := hP.hE2
  have hlen := hP.hlen
  have hB := hP.hB
  run_vcg
  vcg_norm
  vcg_fin
  all_goals first
    | (refine (ind_true ?_).symm; simp_all [compN, litV, litS, List.getD_eq_getElem?_getD]; done)
    | (refine (ind_false ?_).symm; simp_all [compN, litV, litS, List.getD_eq_getElem?_getD]; done)

theorem compCom_fspec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns ∧ σ.vars "bb" < SlotsN ns) compCom
      (fun σ σ' => (σ'.vars "bc" = ind (compN ns (σ.vars "ba") (σ.vars "bb")) ∧ σ'.vars "bc" ≤ 1) ∧
        Fr AComp σ σ' ∧ Ctx[ns, σ']) 60 :=
  (frSpecC (compCom_spec ns hP) AComp (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).post fun _ σ' _ ⟨hq, hf⟩ => ⟨⟨hq, hq ▸ ind_le _⟩, hf⟩

/-! ### The clause number of a position -/

/-- Read the position in `x`, write its clause number to `z`. -/
def cidCom (x z : String) : Com :=
  .ite (.lt (V x) (V "A2")) (.assign z (div (V x) (.lit 2)))
    (.assign z (add (div (V "A2") (.lit 2)) (div (sub (V x) (V "A2")) (.lit 3))))

theorem cidCom_spec (ns : List ℕ) (hP : Pars B ns) (x z : String) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars x < SlotsN ns) (cidCom x z)
      (fun σ σ' => σ'.vars z = clId ns (σ.vars x)) 20 := by
  have hB := hP.hB
  run_vcg
  vcg_norm
  vcg_fin
  all_goals (simp only [clId, List.getD_eq_getElem?_getD]; split_ifs <;> omega)

theorem cidCom_fspec (ns : List ℕ) (hP : Pars B ns) (x z : String) (hzN : z ≠ "N")
    (hzA : z ≠ "A2") :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars x < SlotsN ns) (cidCom x z)
      (fun σ σ' => σ'.vars z = clId ns (σ.vars x) ∧ Fr [z] σ σ' ∧ Ctx[ns, σ']) 20 :=
  frSpecC (cidCom_spec ns hP x z) [z] (by simp [cidCom, Com.wvars]) (by simp [cidCom, Com.warrs])
    (by simp [cidCom, Com.reads]) (by simp [cidCom, Com.NoWrite]) (by simp [Ne.symm hzN])
    (by simp [Ne.symm hzA])

/-! ### The size of the clause of a position and its mate -/

/-- Read the position in `ba` and the port in `bj`: `bs` is the size of the clause of the position, `bm` is
`mateN ns ba bj`. -/
def clauseCom : Com :=
  .ite (.lt (V "ba") (V "A2"))
    (.seq (.assign "bs" (.lit 2))
      (.seq (.assign "bq1" (div (V "ba") (.lit 2)))
      (.seq (.assign "bx" (sub (V "ba") (mul (V "bq1") (.lit 2))))
      (.seq (.assign "by" (add (add (V "bx") (V "bj")) (.lit 1)))
      (.seq (.assign "bz" (div (V "by") (.lit 2)))
      (.seq (.assign "bz" (sub (V "by") (mul (V "bz") (.lit 2))))
        (.assign "bm" (add (sub (V "ba") (V "bx")) (V "bz")))))))))
    (.seq (.assign "bs" (.lit 3))
      (.seq (.assign "bd0" (sub (V "ba") (V "A2")))
      (.seq (.assign "bq1" (div (V "bd0") (.lit 3)))
      (.seq (.assign "bx" (sub (V "bd0") (mul (V "bq1") (.lit 3))))
      (.seq (.assign "by" (add (add (V "bx") (V "bj")) (.lit 1)))
      (.seq (.assign "bz" (div (V "by") (.lit 3)))
      (.seq (.assign "bz" (sub (V "by") (mul (V "bz") (.lit 3))))
        (.assign "bm" (add (sub (V "ba") (V "bx")) (V "bz"))))))))))

@[simp] def AClause : List String := ["bs", "bq1", "bx", "by", "bz", "bd0", "bm"]

theorem clauseCom_spec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns ∧ σ.vars "bj" < 8) clauseCom
      (fun σ σ' => σ'.vars "bs" = clSz ns (σ.vars "ba") ∧
        σ'.vars "bm" = mateN ns (σ.vars "ba") (σ.vars "bj")) 80 := by
  have hB := hP.hB
  run_vcg
  vcg_norm
  vcg_fin
  all_goals (simp only [clSz, mateN, clIx, List.getD_eq_getElem?_getD]; split_ifs <;> omega)

/-- The mate of a position is a position. -/
theorem mateN_lt (ns : List ℕ) {o : ℕ} (ho : o < SlotsN ns) (j : ℕ) : mateN ns o j < SlotsN ns := by
  unfold mateN clIx clSz SlotsN at *
  split_ifs <;> omega

theorem clSz_le (ns : List ℕ) (o : ℕ) : clSz ns o ≤ 3 := by unfold clSz; split <;> omega

theorem clauseCom_fspec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns ∧ σ.vars "bj" < 8) clauseCom
      (fun σ σ' => (σ'.vars "bs" = clSz ns (σ.vars "ba") ∧
        σ'.vars "bm" = mateN ns (σ.vars "ba") (σ.vars "bj") ∧ σ'.vars "bs" ≤ 3 ∧
        σ'.vars "bm" < SlotsN ns) ∧ Fr AClause σ σ' ∧ Ctx[ns, σ']) 80 :=
  (frSpecC (clauseCom_spec ns hP) AClause (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).post fun σ σ' hP' ⟨hq, hf⟩ =>
      ⟨⟨hq.1, hq.2, hq.1 ▸ clSz_le _ _, hq.2 ▸ mateN_lt ns hP'.2.1 _⟩, hf⟩

end Lax117284Proofs.McisHard.Bit
