import Lax117284Proofs.McisHard.Machine.PredUnm
import Lax117284Proofs.McisHard.Machine.PredMath

/-!
# The Predicates `gadAdj`, `PE` and the Port Relation `RN` on the Machine (WP6)
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Bit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284Proofs.Machine.SatRank Lax117284Proofs.Machine.SatOps Lax117284Proofs.Machine.T9Ops

variable {B : ℕ}

/-! ### The gadget adjacency table -/

/-- The pairs of the gadget that are *not* adjacent, as the codes `7 t + t'`. -/
def gadChain : List ℕ := [0, 1, 2, 7, 8, 14, 16, 24, 25, 31, 32, 40, 41, 47, 48]

def gadTest : List ℕ → Com
  | [] => .assign "bd" (.lit 1)
  | k :: ks => .ite (.eq (V "bcd") (.lit k)) (.assign "bd" (.lit 0)) (gadTest ks)

/-- Read the gadget vertices `bg`, `bg2`; `bd` is `gadAdj bg bg2`. -/
def gadCom : Com :=
  .ite (.lt (V "bg") (.lit 7))
    (.ite (.lt (V "bg2") (.lit 7))
      (.seq (.assign "bcd" (add (mul (V "bg") (.lit 7)) (V "bg2"))) (gadTest gadChain))
      (.assign "bd" (.lit 0)))
    (.assign "bd" (.lit 0))

@[simp] def AGad : List String := ["bd", "bcd"]

set_option maxHeartbeats 3200000 in
theorem gadCom_spec (hB : 60 < B) :
    Spec B (fun σ => σ.vars "bg" < 8 ∧ σ.vars "bg2" < 8) gadCom
      (fun σ σ' => σ'.vars "bd" = ind (gadAdj (σ.vars "bg") (σ.vars "bg2"))) 200 := by
  run_vcg
  vcg_norm
  all_goals first
    | omega
    | (refine (ind_true ?_).symm; unfold gadAdj; omega)
    | (refine (ind_false ?_).symm; unfold gadAdj; omega)

theorem gadCom_fspec (hB : 60 < B) :
    Spec B (fun σ => σ.vars "bg" < 8 ∧ σ.vars "bg2" < 8) gadCom
      (fun σ σ' => (σ'.vars "bd" = ind (gadAdj (σ.vars "bg") (σ.vars "bg2")) ∧ σ'.vars "bd" ≤ 1) ∧
        Fr AGad σ σ') 200 :=
  (frSpec (gadCom_spec hB) AGad (by decide) (by decide) (by decide) (by decide)).post
    fun _ σ' _ ⟨hq, hf⟩ => ⟨⟨hq, hq ▸ ind_le _⟩, hf⟩

/-! ### The rank of a position as a `Spec` -/

theorem rankN_le (ns : List ℕ) (o : ℕ) : rankN ns o ≤ o := by
  unfold rankN
  exact List.countP_le_length.trans (by simp)

theorem rankComS (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => σ.arrs "TK" = ns ∧ σ.vars "o" < SlotsN ns) rankCom
      (fun σ σ' => (σ'.vars "cnt" = rankN ns (σ.vars "o") ∧ σ'.vars "cnt" ≤ σ.vars "o") ∧
        Fr ARC σ σ') (64 * SlotsN ns + 46) := by
  rintro σ ⟨hA, ho⟩
  have hB := hP.hB
  have hlen := hP.hlen
  obtain ⟨σ', r, c, -, -, a, o, f⟩ := rankCom_run (B := B) ns (σ.vars "o") σ
    (fun k hk => by have := hP.hE (3 + 2 * k); omega) (fun k hk => by have := hP.hE (4 + 2 * k); omega)
    (by omega) (by omega) hA rfl
  refine ⟨σ', r.mono ?_, ⟨c, c ▸ rankN_le ns _⟩, a, o, r.frame_inp (by decide), f⟩
  unfold Krank
  omega

/-! ### `PE` -/

theorem clId_le (ns : List ℕ) (o : ℕ) : clId ns o ≤ o := by unfold clId; split <;> omega

/-- Read the positions in `ba`, `bb`; `bpe` is `PEP ns ba bb`. -/
def peCom : Com :=
  .ite (.eq (V "ba") (V "bb")) (.assign "bpe" (.lit 0))
    (.seq (cidCom "ba" "bk1") (.seq (cidCom "bb" "bk2")
      (.ite (.eq (V "bk1") (V "bk2")) (.assign "bpe" (.lit 1))
        (.seq compCom (.assign "bpe" (V "bc"))))))

@[simp] def APe : List String := ["bpe", "bk1", "bk2"] ++ AComp

set_option maxHeartbeats 3200000 in
theorem peCom_spec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns ∧ σ.vars "bb" < SlotsN ns) peCom
      (fun σ σ' => σ'.vars "bpe" = ind (PEP ns (σ.vars "ba") (σ.vars "bb"))) 200 := by
  have hE1 := hP.hE1
  have hE8 := hP.hE8
  have hlen := hP.hlen
  have hB := hP.hB
  run_vcg [cidCom_fspec ns hP "ba" "bk1" (by decide) (by decide),
    cidCom_fspec ns hP "bb" "bk2" (by decide) (by decide), compCom_fspec ns hP]
  vcg_norm
  vcg_fin
  all_goals first
    | (have := clId_le ns (σ.vars "ba"); have := clId_le ns (σ.vars "bb"); omega)
    | (refine (ind_false ?_).symm; exact fun h => h.1 rfl)
    | (refine (ind_true ?_).symm; exact ⟨by omega, Or.inl (by assumption)⟩)
    | (apply ind_congr
       constructor
       · intro h; exact ⟨by omega, Or.inr h⟩
       · rintro ⟨-, h | h⟩
         · exact absurd h ‹_›
         · exact h)

theorem peCom_fspec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns ∧ σ.vars "bb" < SlotsN ns) peCom
      (fun σ σ' => (σ'.vars "bpe" = ind (PEP ns (σ.vars "ba") (σ.vars "bb")) ∧ σ'.vars "bpe" ≤ 1) ∧
        Fr APe σ σ' ∧ Ctx[ns, σ']) 200 :=
  (frSpecC (peCom_spec ns hP) APe (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).post fun _ σ' _ ⟨hq, hf⟩ => ⟨⟨hq, hq ▸ ind_le _⟩, hf⟩

/-! ### The port relation `RN` -/

lemma ind_pos_iff {P : Prop} : 0 < ind P ↔ P := by
  unfold ind; split <;> simp_all

/-- Read the positions in `ba`, `bb` and the ports in `bj`, `bjp`; `bl` is `RN ns ba bj bb bjp`. -/
def linkCom : Com :=
  .ite (.lt (V "bj") (.lit 2))
    (.ite (.lt (V "bjp") (.lit 2))
      (.seq clauseCom
        (.ite (.eq (add (add (V "bj") (V "bjp")) (.lit 2)) (V "bs"))
          (.ite (.eq (V "bb") (V "bm"))
            (.seq compCom (.assign "bl" (sub (.lit 1) (V "bc"))))
            (.assign "bl" (.lit 0)))
          (.assign "bl" (.lit 0))))
      (.assign "bl" (.lit 0)))
    (.ite (.lt (V "bj") (.lit 4))
      (.ite (.lt (V "bjp") (.lit 4))
        (.ite (.lt (.lit 1) (V "bjp"))
          (.seq compCom
            (.ite (.lt (.lit 0) (V "bc"))
              (.seq (.assign "o" (V "bb"))
                (.seq rankCom
                  (.seq (.assign "br1" (V "cnt"))
                    (.seq (.assign "o" (V "ba"))
                      (.seq rankCom
                        (.ite (.eq (add (V "br1") (.lit 2)) (V "bj"))
                          (.ite (.eq (add (V "cnt") (.lit 2)) (V "bjp"))
                            (.assign "bl" (.lit 1)) (.assign "bl" (.lit 0)))
                          (.assign "bl" (.lit 0))))))))
              (.assign "bl" (.lit 0))))
          (.assign "bl" (.lit 0)))
        (.assign "bl" (.lit 0)))
      (.assign "bl" (.lit 0)))

@[simp] def ALink : List String := ["bl", "br1", "o"] ++ AClause ++ AComp ++ ARC

set_option maxHeartbeats 3200000 in
theorem linkCom_spec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns ∧ σ.vars "bb" < SlotsN ns ∧
        σ.vars "bj" < 8 ∧ σ.vars "bjp" < 8) linkCom
      (fun σ σ' => σ'.vars "bl" =
        ind (RN ns (σ.vars "ba") (σ.vars "bj") (σ.vars "bb") (σ.vars "bjp")))
      (128 * SlotsN ns + 300) := by
  have hE1 := hP.hE1
  have hE8 := hP.hE8
  have hlen := hP.hlen
  have hB := hP.hB
  run_vcg [clauseCom_fspec ns hP, compCom_fspec ns hP, rankComS ns hP]
  vcg_norm
  vcg_fin
  all_goals try simp_all [ind_pos_iff, ind_eq_zero]
  all_goals first
    | (have := rankN_le ns (σ.vars "bb"); have := rankN_le ns (σ.vars "ba"); omega)
    | (refine (ind_false ?_).symm
       rintro ⟨-, -, ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩
       · first | omega | exact absurd h5 ‹_›
       · first | omega | exact absurd h5 ‹_›)
    | (refine (ind_true ?_).symm
       exact ⟨by simp only [SlotsN, List.getD_eq_getElem?_getD]; omega,
         by simp only [SlotsN, List.getD_eq_getElem?_getD]; omega,
         Or.inr ⟨by omega, by omega, by omega, by omega, ‹_›, by omega, by omega⟩⟩)
    | (by_cases hc : compN ns (σ.vars "ba") (mateN ns (σ.vars "ba") (σ.vars "bj"))
       · rw [ind_true hc, ind_false (by rintro ⟨-, -, ⟨-, -, -, -, h⟩ | ⟨h, -⟩⟩; exact h hc; omega)]
       · rw [ind_false hc, ind_true ⟨by simp only [SlotsN, List.getD_eq_getElem?_getD]; omega,
           by simp only [SlotsN, List.getD_eq_getElem?_getD]; omega,
           Or.inl ⟨by omega, by omega, by omega, rfl, hc⟩⟩])

theorem linkCom_fspec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns ∧ σ.vars "bb" < SlotsN ns ∧
        σ.vars "bj" < 8 ∧ σ.vars "bjp" < 8) linkCom
      (fun σ σ' => (σ'.vars "bl" =
        ind (RN ns (σ.vars "ba") (σ.vars "bj") (σ.vars "bb") (σ.vars "bjp")) ∧ σ'.vars "bl" ≤ 1) ∧
        Fr ALink σ σ' ∧ Ctx[ns, σ']) (128 * SlotsN ns + 300) :=
  (frSpecC (linkCom_spec ns hP) ALink (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).post fun _ σ' _ ⟨hq, hf⟩ => ⟨⟨hq, hq ▸ ind_le _⟩, hf⟩

end Lax117284Proofs.McisHard.Bit
