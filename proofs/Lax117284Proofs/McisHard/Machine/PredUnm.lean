import Lax117284Proofs.McisHard.Machine.PredBase

/-!
# The predicate `unmatchedN` on the machine (WP6)

`coCntCom`: the number of positions carrying the complementary literal of a position (a wrapper of
`SatRank.rankLoop_spec` with the sign `1 - sign`), and `unmatchedCom`.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Bit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284Proofs.Machine.SatRank Lax117284Proofs.Machine.SatOps Lax117284Proofs.Machine.T9Ops

variable {B : ℕ}

/-! ### The counting loop as a `Spec` -/

theorem rankLoopS (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => σ.arrs "TK" = ns ∧ σ.vars "o" ≤ SlotsN ns ∧ σ.vars "vo" + 8 < B ∧
        σ.vars "so" + 8 < B ∧ σ.vars "cnt" = 0) rankLoop
      (fun σ σ' => σ'.vars "cnt" = (List.range (σ.vars "o")).countP (rpred ns (σ.vars "vo") (σ.vars "so")) ∧
        Fr AR σ σ') (64 * SlotsN ns + 6) := by
  rintro σ ⟨hA, ho, hv, hs, hc⟩
  have hB := hP.hB
  have hlen := hP.hlen
  obtain ⟨σ', r, c, a, o, f⟩ := rankLoop_spec (B := B) ns (σ.vars "vo") (σ.vars "so") (σ.vars "o") σ
    (fun k hk => by have := hP.hE (3 + 2 * k); omega) (fun k hk => by have := hP.hE (4 + 2 * k); omega)
    (by omega) (by omega) (by omega) (by omega) hA rfl rfl rfl hc
  refine ⟨σ', r.mono ?_, c, a, o, r.frame_inp (by decide), f⟩
  have := Nat.mul_le_mul_left 64 ho
  omega

/-! ### The number of complementary positions -/

theorem coCountN_eq (ns : List ℕ) (hP : Pars B ns) {o : ℕ} (ho : o < SlotsN ns) :
    coCountN ns o = (List.range (SlotsN ns)).countP
      (rpred ns (ns.getD (3 + 2 * o) 0) (1 - ns.getD (4 + 2 * o) 0)) := by
  unfold coCountN
  rw [List.countP_eq_length_filter]
  refine congrArg List.length (List.filter_congr fun x hx => ?_)
  have hx' := List.mem_range.mp hx
  have h1 := hP.hsg x hx'
  have h2 := hP.hsg o ho
  simp only [rpred, litV, litS]
  apply decide_eq_decide.mpr
  omega

/-- Read the position in `ba`; `cnt` is the number of positions with the complementary literal. -/
def coCntCom : Com :=
  .seq (.assign "o" (V "N"))
  (.seq (.assign "vo" (.get "TK" (add (.lit 3) (mul (.lit 2) (V "ba")))))
  (.seq (.assign "so" (sub (.lit 1) (.get "TK" (add (.lit 4) (mul (.lit 2) (V "ba"))))))
  (.seq (.assign "cnt" (.lit 0)) rankLoop)))

@[simp] def ACo : List String := ["o", "vo", "so", "cnt", "j", "vj", "sj"]

set_option maxHeartbeats 1600000 in
theorem coCntCom_spec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns) coCntCom
      (fun σ σ' => σ'.vars "cnt" = coCountN ns (σ.vars "ba") ∧ Fr ACo σ σ')
      (64 * SlotsN ns + 60) := by
  have hE1 := hP.hE1
  have hE8 := hP.hE8
  have hlen := hP.hlen
  have hB := hP.hB
  run_vcg [rankLoopS ns hP]
  vcg_norm
  vcg_fin
  have hba : σ.vars "ba" < SlotsN ns := by simp only [SlotsN, List.getD_eq_getElem?_getD]; omega
  rw [coCountN_eq ns hP hba]
  simp [List.getD_eq_getElem?_getD, SlotsN]

theorem coCountN_le (ns : List ℕ) (o : ℕ) : coCountN ns o ≤ SlotsN ns := by
  unfold coCountN
  exact (List.length_filter_le _ _).trans (by simp)

theorem coCntCom_fspec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns) coCntCom
      (fun σ σ' => (σ'.vars "cnt" = coCountN ns (σ.vars "ba") ∧ σ'.vars "cnt" ≤ SlotsN ns) ∧
        Fr ACo σ σ' ∧ Ctx[ns, σ']) (64 * SlotsN ns + 60) :=
  (coCntCom_spec ns hP).post fun σ σ' hpre ⟨hq, hf⟩ =>
    ⟨⟨hq, hq ▸ coCountN_le ns _⟩, hf, ctx_of_eq hpre.1 hf.1 (hf.2.2.2 "N" (by decide))
      (hf.2.2.2 "A2" (by decide))⟩

/-! ### `unmatchedN` -/

/-- Read the position in `ba` and the port in `bj`; `bu` is `unmatchedN ns ba bj`. -/
def unmatchedCom : Com :=
  .ite (.eq (V "bj") (.lit 4)) (.assign "bu" (.lit 1))
    (.ite (.lt (V "bj") (.lit 2))
      (.seq clauseCom
        (.ite (.lt (V "bs") (add (V "bj") (.lit 2))) (.assign "bu" (.lit 1))
          (.seq (.assign "bb" (V "bm")) (.seq compCom (.assign "bu" (V "bc"))))))
      (.ite (.lt (V "bj") (.lit 4))
        (.seq coCntCom
          (.ite (.lt (V "cnt") (sub (V "bj") (.lit 1))) (.assign "bu" (.lit 1)) (.assign "bu" (.lit 0))))
        (.assign "bu" (.lit 0))))

@[simp] def AUnm : List String := AClause ++ AComp ++ ACo ++ ["bu", "bb"]

theorem unmatchedCom_spec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns ∧ σ.vars "bj" < 8) unmatchedCom
      (fun σ σ' => σ'.vars "bu" = ind (unmatchedN ns (σ.vars "ba") (σ.vars "bj")))
      (64 * SlotsN ns + 200) := by
  have hE1 := hP.hE1
  have hB := hP.hB
  run_vcg [clauseCom_fspec ns hP, compCom_fspec ns hP, coCntCom_fspec ns hP]
  vcg_norm
  vcg_fin
  all_goals first
    | (refine (ind_true ?_).symm; unfold unmatchedN
       first
         | exact Or.inl (by omega)
         | exact Or.inr (Or.inl ⟨by omega, Or.inl (by omega)⟩)
         | exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))
    | (refine (ind_false ?_).symm; unfold unmatchedN
       rintro (h | ⟨h, -⟩ | ⟨h1, h2, h3⟩) <;> omega)
    | (apply ind_congr
       unfold unmatchedN
       constructor
       · intro h; exact Or.inr (Or.inl ⟨by omega, Or.inr h⟩)
       · rintro (h | ⟨-, h | h⟩ | ⟨h, -⟩) <;> first | omega | exact h)

theorem unmatchedCom_fspec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns ∧ σ.vars "bj" < 8) unmatchedCom
      (fun σ σ' => (σ'.vars "bu" = ind (unmatchedN ns (σ.vars "ba") (σ.vars "bj")) ∧
        σ'.vars "bu" ≤ 1) ∧ Fr AUnm σ σ' ∧ Ctx[ns, σ']) (64 * SlotsN ns + 200) :=
  (frSpecC (unmatchedCom_spec ns hP) AUnm (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).post fun _ σ' _ ⟨hq, hf⟩ => ⟨⟨hq, hq ▸ ind_le _⟩, hf⟩

end Lax117284Proofs.McisHard.Bit
