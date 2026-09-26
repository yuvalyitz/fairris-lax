import Lax117284Proofs.McisHard.Machine.PredLink

/-!
# The adjacency bit of `H`: the case tree and the whole command (WP6)

`treeCom`: the bit of `G'` at two vertex numbers `bTu`, `bTv` (`treeP`); `bitCom`: decode the two numbers of `H` and
either compare (`N = 0`) or walk the tree.  Every block has at most one command whose specification carries a
frame, so the proofs are short.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Bit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284Proofs.Machine.SatRank Lax117284Proofs.Machine.SatOps Lax117284Proofs.Machine.T9Ops

variable {B : ℕ}

/-! ### Arithmetic on indicators -/

/-- `x - x / n * n` is `x % n`. -/
theorem sub_div_mul (x n : ℕ) : x - x / n * n = x % n := by
  rw [Nat.mod_def, Nat.mul_comm]

theorem flag_eq (a b : ℕ) : 1 - ((a - b) + (b - a)) = ind (a = b) := by
  unfold ind; split <;> omega

theorem flag_zero (a : ℕ) : 1 - a = ind (a = 0) := by
  unfold ind; split <;> omega

theorem ind_and (P Q : Prop) : ind P - (ind P - ind Q) = ind (P ∧ Q) := by
  unfold ind; split_ifs <;> simp_all

theorem ind_max (P Q : Prop) : ind P + (ind Q - ind P) = ind (P ∨ Q) := by
  unfold ind; split_ifs <;> simp_all <;> omega

/-! ### A position and a slot of it -/

/-- A position and a slot of the same position. -/
def posP (ns : List ℕ) (o p r : ℕ) : Prop :=
  o = p ∧ (r - 1) % 7 = 0 ∧ unmatchedN ns o ((r - 1) / 7)

/-- The case tree of two slot vertices, as a proposition. -/
def slotP (ns : List ℕ) (o p r r2 : ℕ) : Prop :=
  (o = p ∧ (r - 1) / 7 = (r2 - 1) / 7 ∧ gadAdj ((r - 1) % 7) ((r2 - 1) % 7)) ∨
    ((r - 1) % 7 = 0 ∧ (r2 - 1) % 7 = 0 ∧ RN ns o ((r - 1) / 7) p ((r2 - 1) / 7))

/-- `unmatched(bTo, x)`, into `bt`. -/
def unmLeaf (x : String) : Com :=
  .seq (.assign "ba" (V "bTo")) (.seq (.assign "bj" (V x))
    (.seq unmatchedCom (.assign "bt" (V "bu"))))

/-- Decode the slot of a vertex `r ≠ 0` (in `x`): the port in `bTq`, the vertex of the gadget in `bTt`. -/
def slotDecode (x : String) : Com :=
  .seq (.assign "bTx" (sub (V x) (.lit 1)))
    (.seq (.assign "bTq" (div (V "bTx") (.lit 7)))
      (.assign "bTt" (sub (V "bTx") (mul (V "bTq") (.lit 7)))))

/-- The case of a position vertex and a slot vertex of the same position. -/
def posSlot (x : String) : Com :=
  .ite (.eq (V "bTo") (V "bTo2"))
    (.seq (slotDecode x)
      (.ite (.eq (V "bTt") (.lit 0)) (unmLeaf "bTq") (.assign "bt" (.lit 0))))
    (.assign "bt" (.lit 0))

@[simp] def APos : List String := ["bTx", "bTq", "bTt", "bt", "ba", "bj"] ++ AUnm

set_option maxHeartbeats 3200000 in
theorem posSlot2_spec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "bTo" < SlotsN ns ∧ σ.vars "bTo2" < SlotsN ns ∧
        0 < σ.vars "bTr2" ∧ σ.vars "bTr2" < 36)
      (posSlot "bTr2")
      (fun σ σ' => σ'.vars "bt" = ind (posP ns (σ.vars "bTo") (σ.vars "bTo2") (σ.vars "bTr2")))
      (64 * SlotsN ns + 400) := by
  have hB := hP.hB
  run_vcg [unmatchedCom_fspec ns hP]
  vcg_norm
  · obtain ⟨⟨hq, -⟩, -⟩ := ‹_ ∧ _ ∧ _›
    rw [hq]; apply ind_congr; unfold posP
    constructor
    · intro h; exact ⟨by assumption, by omega, h⟩
    · rintro ⟨-, -, h⟩; exact h
  · refine (ind_false ?_).symm; rintro ⟨-, h, -⟩; omega
  · refine (ind_false ?_).symm; rintro ⟨h, -⟩; exact ‹¬_› h
  all_goals first
    | omega
    | exact ⟨⟨‹_›, ‹_›, ‹_›⟩, by omega, by omega⟩

set_option maxHeartbeats 3200000 in
theorem posSlot1_spec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "bTo" < SlotsN ns ∧ σ.vars "bTo2" < SlotsN ns ∧
        0 < σ.vars "bTr" ∧ σ.vars "bTr" < 36)
      (posSlot "bTr")
      (fun σ σ' => σ'.vars "bt" = ind (posP ns (σ.vars "bTo") (σ.vars "bTo2") (σ.vars "bTr")))
      (64 * SlotsN ns + 400) := by
  have hB := hP.hB
  run_vcg [unmatchedCom_fspec ns hP]
  vcg_norm
  · obtain ⟨⟨hq, -⟩, -⟩ := ‹_ ∧ _ ∧ _›
    rw [hq]; apply ind_congr; unfold posP
    constructor
    · intro h; exact ⟨by assumption, by omega, h⟩
    · rintro ⟨-, -, h⟩; exact h
  · refine (ind_false ?_).symm; rintro ⟨-, h, -⟩; omega
  · refine (ind_false ?_).symm; rintro ⟨h, -⟩; exact ‹¬_› h
  all_goals first
    | omega
    | exact ⟨⟨‹_›, ‹_›, ‹_›⟩, by omega, by omega⟩

theorem posSlot2_fspec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "bTo" < SlotsN ns ∧ σ.vars "bTo2" < SlotsN ns ∧
        0 < σ.vars "bTr2" ∧ σ.vars "bTr2" < 36)
      (posSlot "bTr2")
      (fun σ σ' => (σ'.vars "bt" = ind (posP ns (σ.vars "bTo") (σ.vars "bTo2") (σ.vars "bTr2")) ∧
        σ'.vars "bt" ≤ 1) ∧ Fr APos σ σ' ∧ Ctx[ns, σ']) (64 * SlotsN ns + 400) :=
  (frSpecC (posSlot2_spec ns hP) APos (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).post fun _ σ' _ ⟨hq, hf⟩ => ⟨⟨hq, hq ▸ ind_le _⟩, hf⟩

theorem posSlot1_fspec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "bTo" < SlotsN ns ∧ σ.vars "bTo2" < SlotsN ns ∧
        0 < σ.vars "bTr" ∧ σ.vars "bTr" < 36)
      (posSlot "bTr")
      (fun σ σ' => (σ'.vars "bt" = ind (posP ns (σ.vars "bTo") (σ.vars "bTo2") (σ.vars "bTr")) ∧
        σ'.vars "bt" ≤ 1) ∧ Fr APos σ σ' ∧ Ctx[ns, σ']) (64 * SlotsN ns + 400) :=
  (frSpecC (posSlot1_spec ns hP) APos (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).post fun _ σ' _ ⟨hq, hf⟩ => ⟨⟨hq, hq ▸ ind_le _⟩, hf⟩

/-! ### The gadget half of two slot vertices -/

def gadBlock : Com :=
  .seq (.assign "bg" (V "bTta")) (.seq (.assign "bg2" (V "bTt"))
  (.seq (.assign "bE1" (sub (.lit 1) (add (sub (V "bTo") (V "bTo2")) (sub (V "bTo2") (V "bTo")))))
  (.seq (.assign "bE2" (sub (.lit 1) (add (sub (V "bTqa") (V "bTq")) (sub (V "bTq") (V "bTqa")))))
  (.seq (.assign "bE" (sub (V "bE1") (sub (V "bE1") (V "bE2"))))
  (.seq gadCom (.assign "bTg" (sub (V "bd") (sub (V "bd") (V "bE")))))))))

@[simp] def AGadB : List String := ["bg", "bg2", "bE1", "bE2", "bE", "bTg"] ++ AGad

set_option maxHeartbeats 3200000 in
theorem gadBlock_spec (hB : 60 < B) :
    Spec B (fun σ => σ.vars "bTta" < 8 ∧ σ.vars "bTt" < 8 ∧ σ.vars "bTo" < B ∧ σ.vars "bTo2" < B ∧
        σ.vars "bTqa" < B ∧ σ.vars "bTq" < B) gadBlock
      (fun σ σ' => σ'.vars "bTg" = ind ((σ.vars "bTo" = σ.vars "bTo2" ∧ σ.vars "bTqa" = σ.vars "bTq") ∧
        gadAdj (σ.vars "bTta") (σ.vars "bTt"))) 300 := by
  run_vcg [gadCom_fspec hB]
  vcg_norm
  · obtain ⟨⟨hq, -⟩, -, -, -, hfr⟩ := ‹_ ∧ _ ∧ _ ∧ _ ∧ _›
    have h1 := hfr "bE" (by simp)
    simp only [String.reduceEq, ↓reduceIte, flag_eq, ind_and] at h1
    rw [hq, h1, ind_and]
    exact ind_congr (by tauto)
  all_goals first
    | omega
    | exact ⟨by omega, by omega⟩
    | (simp_all only [Fr, AGad, List.mem_cons, List.not_mem_nil, or_false, not_or, String.reduceEq,
        ↓reduceIte, ite_true, ite_false, not_false_eq_true, and_true, true_and, ne_eq] <;> omega)

theorem gadBlock_fspec (hB : 60 < B) :
    Spec B (fun σ => σ.vars "bTta" < 8 ∧ σ.vars "bTt" < 8 ∧ σ.vars "bTo" < B ∧ σ.vars "bTo2" < B ∧
        σ.vars "bTqa" < B ∧ σ.vars "bTq" < B) gadBlock
      (fun σ σ' => (σ'.vars "bTg" = ind ((σ.vars "bTo" = σ.vars "bTo2" ∧ σ.vars "bTqa" = σ.vars "bTq") ∧
        gadAdj (σ.vars "bTta") (σ.vars "bTt")) ∧ σ'.vars "bTg" ≤ 1) ∧ Fr AGadB σ σ') 300 :=
  (frSpec (gadBlock_spec hB) AGadB (by decide) (by decide) (by decide) (by decide)).post
    fun _ σ' _ ⟨hq, hf⟩ => ⟨⟨hq, hq ▸ ind_le _⟩, hf⟩

/-! ### The link half of two slot vertices -/

def linkBlock : Com :=
  .seq (.assign "ba" (V "bTo")) (.seq (.assign "bj" (V "bTqa"))
  (.seq (.assign "bb" (V "bTo2")) (.seq (.assign "bjp" (V "bTq"))
  (.seq (.assign "bF1" (sub (.lit 1) (V "bTta"))) (.seq (.assign "bF2" (sub (.lit 1) (V "bTt")))
  (.seq (.assign "bF" (sub (V "bF1") (sub (V "bF1") (V "bF2"))))
  (.seq linkCom (.assign "bTl" (sub (V "bl") (sub (V "bl") (V "bF")))))))))))

@[simp] def ALinkB : List String := ["ba", "bj", "bb", "bjp", "bF1", "bF2", "bF", "bTl"] ++ ALink

@[simp] def ASlot : List String :=
  ["bTx", "bTqa", "bTta", "bTq", "bTt", "bt"] ++ AGadB ++ ALinkB

-- Unfold the frames of the blocks and `simp_all` (no arithmetic hypotheses are around).
macro "fr_simp" : tactic => `(tactic| simp_all only [Fr, AGad, AGadB, ALinkB, APos, AClause, AComp, ACo, AUnm,
  APe, ALink, Lax117284Proofs.Machine.SatRank.ARC, Lax117284Proofs.Machine.SatRank.AR, List.mem_cons,
  List.mem_append, List.not_mem_nil, List.mem_singleton, or_false, not_or, String.reduceEq, ↓reduceIte,
  ite_true, ite_false, not_false_eq_true, and_true, true_and, ne_eq])

set_option maxHeartbeats 3200000 in
theorem linkBlock_spec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "bTo" < SlotsN ns ∧ σ.vars "bTo2" < SlotsN ns ∧
        σ.vars "bTqa" < 8 ∧ σ.vars "bTq" < 8 ∧ σ.vars "bTta" < 8 ∧ σ.vars "bTt" < 8) linkBlock
      (fun σ σ' => σ'.vars "bTl" = ind ((σ.vars "bTta" = 0 ∧ σ.vars "bTt" = 0) ∧
        RN ns (σ.vars "bTo") (σ.vars "bTqa") (σ.vars "bTo2") (σ.vars "bTq")))
      (128 * SlotsN ns + 400) := by
  have hB := hP.hB
  run_vcg [linkCom_fspec ns hP]
  vcg_norm
  · obtain ⟨⟨hq, -⟩, ⟨-, -, -, hfr⟩, -⟩ := ‹_ ∧ _ ∧ _›
    have h1 := hfr "bF" (by simp)
    simp only [String.reduceEq, ↓reduceIte, flag_zero, ind_and] at h1
    rw [h1, hq, ind_and]
    exact ind_congr (by tauto)
  all_goals first
    | omega
    | exact ⟨⟨‹_›, ‹_›, ‹_›⟩, ‹_›, ‹_›, ‹_›, ‹_›⟩
    | (fr_simp <;> omega)

theorem linkBlock_fspec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "bTo" < SlotsN ns ∧ σ.vars "bTo2" < SlotsN ns ∧
        σ.vars "bTqa" < 8 ∧ σ.vars "bTq" < 8 ∧ σ.vars "bTta" < 8 ∧ σ.vars "bTt" < 8) linkBlock
      (fun σ σ' => (σ'.vars "bTl" = ind ((σ.vars "bTta" = 0 ∧ σ.vars "bTt" = 0) ∧
        RN ns (σ.vars "bTo") (σ.vars "bTqa") (σ.vars "bTo2") (σ.vars "bTq")) ∧ σ'.vars "bTl" ≤ 1) ∧
        Fr ALinkB σ σ' ∧ Ctx[ns, σ']) (128 * SlotsN ns + 400) :=
  (frSpecC (linkBlock_spec ns hP) ALinkB (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).post fun _ σ' _ ⟨hq, hf⟩ => ⟨⟨hq, hq ▸ ind_le _⟩, hf⟩

/-! ### Two slot vertices -/

def slotDec : Com :=
  .seq (.assign "bTx" (sub (V "bTr") (.lit 1)))
  (.seq (.assign "bTqa" (div (V "bTx") (.lit 7)))
  (.seq (.assign "bTta" (sub (V "bTx") (mul (V "bTqa") (.lit 7))))
  (.seq (.assign "bTx" (sub (V "bTr2") (.lit 1)))
  (.seq (.assign "bTq" (div (V "bTx") (.lit 7)))
    (.assign "bTt" (sub (V "bTx") (mul (V "bTq") (.lit 7))))))))

def slotSlot : Com :=
  .seq slotDec (.seq gadBlock (.seq linkBlock
    (.assign "bt" (add (V "bTg") (sub (V "bTl") (V "bTg"))))))

set_option maxHeartbeats 3200000 in
theorem slotSlot_spec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "bTo" < SlotsN ns ∧ σ.vars "bTo2" < SlotsN ns ∧
        0 < σ.vars "bTr" ∧ σ.vars "bTr" < 36 ∧ 0 < σ.vars "bTr2" ∧ σ.vars "bTr2" < 36) slotSlot
      (fun σ σ' => σ'.vars "bt" =
        ind (slotP ns (σ.vars "bTo") (σ.vars "bTo2") (σ.vars "bTr") (σ.vars "bTr2")))
      (128 * SlotsN ns + 1000) := by
  have hB := hP.hB
  run_vcg [gadBlock_fspec (B := B) (by omega), linkBlock_fspec ns hP]
  vcg_norm
  · obtain ⟨⟨hq2, -⟩, ⟨-, -, -, hfr2⟩, -⟩ := ‹_ ∧ Fr ALinkB _ _ ∧ _›
    obtain ⟨⟨hq1, -⟩, ⟨-, -, -, hfr1⟩⟩ := ‹_ ∧ Fr AGadB _ _›
    have e1 := hfr1 "bTta" (by simp)
    have e2 := hfr1 "bTt" (by simp)
    have e3 := hfr1 "bTo" (by simp)
    have e4 := hfr1 "bTqa" (by simp)
    have e5 := hfr1 "bTo2" (by simp)
    have e6 := hfr1 "bTq" (by simp)
    simp only [String.reduceEq, ↓reduceIte, sub_div_mul] at e1 e2 e3 e4 e5 e6 hq1
    rw [hfr2 "bTg" (by simp), hq1, hq2, e1, e2, e3, e4, e5, e6, ind_max]
    apply ind_congr
    unfold slotP
    tauto
  all_goals first
    | omega
    | (fr_simp <;> omega)

theorem slotSlot_fspec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "bTo" < SlotsN ns ∧ σ.vars "bTo2" < SlotsN ns ∧
        0 < σ.vars "bTr" ∧ σ.vars "bTr" < 36 ∧ 0 < σ.vars "bTr2" ∧ σ.vars "bTr2" < 36) slotSlot
      (fun σ σ' => (σ'.vars "bt" =
        ind (slotP ns (σ.vars "bTo") (σ.vars "bTo2") (σ.vars "bTr") (σ.vars "bTr2")) ∧
          σ'.vars "bt" ≤ 1) ∧ Fr ASlot σ σ' ∧ Ctx[ns, σ']) (128 * SlotsN ns + 1000) :=
  (frSpecC (slotSlot_spec ns hP) ASlot (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).post fun _ σ' _ ⟨hq, hf⟩ => ⟨⟨hq, hq ▸ ind_le _⟩, hf⟩

/-! ### The tree -/

/-- The bit of `G'` at the vertex numbers `bTu`, `bTv` (both below `36 N`). -/
def treeCom : Com :=
  .seq (.assign "bTo" (div (V "bTu") (.lit 36)))
  (.seq (.assign "bTr" (sub (V "bTu") (mul (V "bTo") (.lit 36))))
  (.seq (.assign "bTo2" (div (V "bTv") (.lit 36)))
  (.seq (.assign "bTr2" (sub (V "bTv") (mul (V "bTo2") (.lit 36))))
    (.ite (.eq (V "bTr") (.lit 0))
      (.ite (.eq (V "bTr2") (.lit 0))
        (.seq (.assign "ba" (V "bTo")) (.seq (.assign "bb" (V "bTo2"))
          (.seq peCom (.assign "bt" (V "bpe")))))
        (posSlot "bTr2"))
      (.ite (.eq (V "bTr2") (.lit 0)) (posSlot "bTr") slotSlot)))))

@[simp] def ATree : List String :=
  ["bTo", "bTr", "bTo2", "bTr2", "bt", "ba", "bb"] ++ APe ++ APos ++ ASlot

set_option maxHeartbeats 6400000 in
theorem treeCom_spec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "bTu" < 36 * SlotsN ns ∧ σ.vars "bTv" < 36 * SlotsN ns)
      treeCom (fun σ σ' => σ'.vars "bt" = ind (treeP ns (σ.vars "bTu") (σ.vars "bTv")))
      (128 * SlotsN ns + 1200) := by
  have hB := hP.hB
  run_vcg [peCom_fspec ns hP, posSlot2_fspec ns hP, posSlot1_fspec ns hP, slotSlot_fspec ns hP]
  vcg_norm
  · obtain ⟨⟨hq, -⟩, -⟩ := ‹_ ∧ _ ∧ _›
    simp only [sub_div_mul] at *
    rw [hq]; apply ind_congr; unfold treeP
    rw [if_pos (by omega), if_pos (by omega)]
  · obtain ⟨⟨hq, -⟩, -⟩ := ‹_ ∧ _ ∧ _›
    simp only [sub_div_mul] at *
    rw [hq]; apply ind_congr; unfold treeP posP
    rw [if_pos (by omega), if_neg (by omega)]
  · obtain ⟨⟨hq, -⟩, -⟩ := ‹_ ∧ _ ∧ _›
    simp only [sub_div_mul] at *
    rw [hq]; apply ind_congr; unfold treeP posP
    rw [if_neg (by omega), if_pos (by omega)]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h1 ▸ h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h1 ▸ h3⟩
  · obtain ⟨⟨hq, -⟩, -⟩ := ‹_ ∧ _ ∧ _›
    simp only [sub_div_mul] at *
    rw [hq]; apply ind_congr; unfold treeP slotP
    rw [if_neg (by omega), if_neg (by omega)]
  all_goals first
    | omega
    | (refine ⟨⟨‹_›, ‹_›, ‹_›⟩, ?_⟩; omega)

set_option maxRecDepth 100000 in
theorem treeCom_fspec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "bTu" < 36 * SlotsN ns ∧ σ.vars "bTv" < 36 * SlotsN ns)
      treeCom (fun σ σ' => (σ'.vars "bt" = ind (treeP ns (σ.vars "bTu") (σ.vars "bTv")) ∧
        σ'.vars "bt" ≤ 1) ∧ Fr ATree σ σ' ∧ Ctx[ns, σ']) (128 * SlotsN ns + 1200) :=
  (frSpecC (treeCom_spec ns hP) ATree (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).post fun _ σ' _ ⟨hq, hf⟩ => ⟨⟨hq, hq ▸ ind_le _⟩, hf⟩

/-! ### The whole command -/

/-- The bit of `H` at the vertex numbers in `w`, `w2`. -/
def bitCom : Com :=
  .ite (.eq (V "N") (.lit 0))
    (.seq (.assign "bTi" (div (V "w") (.lit 4)))
      (.seq (.assign "bTu" (sub (V "w") (mul (V "bTi") (.lit 4))))
      (.seq (.assign "bTj" (div (V "w2") (.lit 4)))
      (.seq (.assign "bTv" (sub (V "w2") (mul (V "bTj") (.lit 4))))
        (.ite (.eq (V "bTi") (V "bTj")) (.assign "bt" (.lit 0))
          (.ite (.eq (V "bTu") (V "bTv")) (.assign "bt" (.lit 1)) (.assign "bt" (.lit 0))))))))
    (.seq (.assign "bTn" (mul (V "N") (.lit 36)))
      (.seq (.assign "bTi" (div (V "w") (V "bTn")))
      (.seq (.assign "bTu" (sub (V "w") (mul (V "bTi") (V "bTn"))))
      (.seq (.assign "bTj" (div (V "w2") (V "bTn")))
      (.seq (.assign "bTv" (sub (V "w2") (mul (V "bTj") (V "bTn"))))
        (.ite (.eq (V "bTi") (V "bTj")) (.assign "bt" (.lit 0))
          (.ite (.eq (V "bTu") (V "bTv")) (.assign "bt" (.lit 1)) treeCom)))))))

theorem nOf_pos (ns : List ℕ) (h : SlotsN ns ≠ 0) : nOf ns = SlotsN ns * 36 := by
  unfold nOf; rw [if_neg h]

theorem nOf_zero (ns : List ℕ) (h : SlotsN ns = 0) : nOf ns = 4 := by
  unfold nOf; rw [if_pos h]

set_option maxHeartbeats 6400000 in
theorem bitCom_spec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "w" < B ∧ σ.vars "w2" < B) bitCom
      (fun σ σ' => σ'.vars "bt" = ind (adjM ns (σ.vars "w") (σ.vars "w2")))
      (128 * SlotsN ns + 1500) := by
  have hB := hP.hB
  run_vcg [treeCom_fspec ns hP]
  vcg_norm
  · have hN : σ.vars "N" = SlotsN ns := ‹_›
    have h0 : SlotsN ns = 0 := by omega
    have hn := nOf_zero ns h0
    try simp only [sub_div_mul] at *
    refine (ind_false ?_).symm; unfold adjM; rw [hn]
    rintro ⟨h, -⟩; exact h (by omega)
  · have hN : σ.vars "N" = SlotsN ns := ‹_›
    have h0 : SlotsN ns = 0 := by omega
    have hn := nOf_zero ns h0
    try simp only [sub_div_mul] at *
    refine (ind_true ?_).symm; unfold adjM; rw [hn]
    exact ⟨by omega, Or.inl (by omega)⟩
  · have hN : σ.vars "N" = SlotsN ns := ‹_›
    have h0 : SlotsN ns = 0 := by omega
    have hn := nOf_zero ns h0
    try simp only [sub_div_mul] at *
    refine (ind_false ?_).symm; unfold adjM; rw [hn]
    rintro ⟨-, h | ⟨h, -⟩⟩
    · omega
    · exact h h0
  · have hN : σ.vars "N" = SlotsN ns := ‹_›
    have hne : SlotsN ns ≠ 0 := by omega
    have hn := nOf_pos ns hne
    try simp only [hN, sub_div_mul] at *
    refine (ind_false ?_).symm; unfold adjM; rw [hn]
    rintro ⟨h, -⟩; exact h ‹_›
  · have hN : σ.vars "N" = SlotsN ns := ‹_›
    have hne : SlotsN ns ≠ 0 := by omega
    have hn := nOf_pos ns hne
    try simp only [hN, sub_div_mul] at *
    refine (ind_true ?_).symm; unfold adjM; rw [hn]
    exact ⟨‹_›, Or.inl ‹_›⟩
  · have hN : σ.vars "N" = SlotsN ns := ‹_›
    have hne : SlotsN ns ≠ 0 := by omega
    have hn := nOf_pos ns hne
    obtain ⟨⟨hq, -⟩, -⟩ := ‹_ ∧ _ ∧ _›
    try simp only [hN, sub_div_mul] at *
    rw [hq]; apply ind_congr; unfold adjM; rw [hn]
    constructor
    · intro h; exact ⟨‹_›, Or.inr ⟨hne, h⟩⟩
    · rintro ⟨-, h | ⟨-, h⟩⟩
      · exact absurd h ‹_›
      · exact h
  all_goals first
    | omega
    | (have h1 := Nat.div_le_self (σ.vars "w") (σ.vars "N" * 36)
       have h2 := Nat.div_mul_le_self (σ.vars "w") (σ.vars "N" * 36)
       have h3 := Nat.div_le_self (σ.vars "w2") (σ.vars "N" * 36)
       have h4 := Nat.div_mul_le_self (σ.vars "w2") (σ.vars "N" * 36)
       omega)
    | (refine ⟨⟨‹_›, ‹_›, ‹_›⟩, ?_, ?_⟩
       · rw [sub_div_mul]
         have := Nat.mod_lt (σ.vars "w") (show σ.vars "N" * 36 > 0 by omega)
         omega
       · rw [sub_div_mul]
         have := Nat.mod_lt (σ.vars "w2") (show σ.vars "N" * 36 > 0 by omega)
         omega)

end Lax117284Proofs.McisHard.Bit
