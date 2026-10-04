import Lax117284Proofs.Machine.TwFill
import Lax117284Proofs.Machine.TwCf
import Lax117284.Bodlaender
import Lax117284.InstanceEncoding
import Lax117284Proofs.Machine.TwNode
import Lax117284Proofs.Machine.ClMainRead
import Lax117284Proofs.Machine.ClBruteFinal
import Lax117284Proofs.Machine.TwPrep3
import Lax117284Proofs.Machine.TwSetup4
import Lax117284Proofs.Machine.TwZero
import Lax117284Proofs.Machine.TwSetup1
import Mathlib.Tactic
import Lax117284Proofs.Machine.TwPrep
import Lax117284Proofs.Machine.ClMainBound
import Lax117284Proofs.ClientsWord

/-! ### `Lax117284Proofs.Machine.TwGraph` -/

section
/-!
The adjacency matrix of the overall conflict graph, built by the fill loop: the cell `fc` is the
pair of clients `fc / n` and `fc % n`, and it is `1` when they are distinct and conflict on some day.
The count of the conflicting days is the loop over the days that the violation counter already has,
run with the digit that holds every day.
-/

namespace Lax117284Proofs.Machine.TwGraph

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {B : ℕ}

macro "nrmB" : tactic => `(tactic| simp only [vars_setVar, arrs_setVar, inp_setVar, out_setVar, vars_setArr, arrs_setArr, ↓reduceIte, String.reduceEq, eq_self])

/-- The scalars a cell writes. -/
def SG : List String := ["val", "du", "dv", "dt", "dq"] ++ SD

/-- The two clients of a cell, and the digit that holds every day. -/
def adjPre : Com := seqs
  [ .assign "du" (.bin .div (V "fc") (V "n")),
    .assign "dv" (sub (V "fc") (mul (V "du") (V "n"))),
    .assign "dt" (V "mask"),
    .assign "dq" (V "mask"),
    .assign "vi" (L 0) ]

/-- The bit: distinct clients that conflict on some day. -/
def adjFin : Com :=
  .ite (.eq (V "du") (V "dv")) (.assign "val" (L 0))
    (.ite (.lt (L 0) (V "vi")) (.assign "val" (L 1)) (.assign "val" (L 0)))

/-- The cell of the matrix. -/
def adjCell : Com := .seq adjPre (.seq dLoop adjFin)

/-- The bit of the matrix: the two clients are distinct and conflict on a day. -/
def adjBit (X : List ℕ) (n m fc : ℕ) : ℕ :=
  if fc / n ≠ fc % n ∧ ∃ d < m, cfN X n m d (fc / n) (fc % n) then 1 else 0

lemma testBit_mask (m d : ℕ) (hd : d < m) : (2 ^ m - 1).testBit d = true := by
  rw [Nat.testBit_two_pow_sub_one]; simpa using hd

lemma cfDayN_mask_pos (X : List ℕ) (n m u v : ℕ) :
    0 < cfDayN X n m u v (2 ^ m - 1) (2 ^ m - 1) ↔ ∃ d < m, cfN X n m d u v := by
  unfold cfDayN
  rw [Finset.sum_pos_iff]
  constructor
  · rintro ⟨d, hd, hpos⟩
    have hd' := Finset.mem_range.1 hd
    refine ⟨d, hd', ?_⟩
    by_contra hn
    simp [hn] at hpos
  · rintro ⟨d, hd, hc⟩
    refine ⟨d, Finset.mem_range.2 hd, ?_⟩
    simp [testBit_mask m d hd, hc]

lemma mod_eq_sub (a n : ℕ) : a % n = a - a / n * n := by
  rw [Nat.mod_def, Nat.mul_comm]

theorem adjPre_run (σ : Env) (n : ℕ) (hn : σ.vars "n" = n) (hnB : n < B) (hmask : σ.vars "mask" < B)
    (hfc : σ.vars "fc" < B) (h0 : 0 < B) :
    ∃ σ1, Run B adjPre σ σ1 60 ∧ σ1 = ((((σ.setVar "du" (σ.vars "fc" / n)).setVar "dv"
      (σ.vars "fc" - σ.vars "fc" / n * n)).setVar "dt" (σ.vars "mask")).setVar "dq"
      (σ.vars "mask")).setVar "vi" 0 := by
  have hd : σ.vars "fc" / n < B := lt_of_le_of_lt (Nat.div_le_self _ _) hfc
  have hm : σ.vars "fc" / n * n < B := lt_of_le_of_lt (Nat.div_mul_le_self _ _) hfc
  unfold adjPre seqs
  run_vcg
  all_goals (try nrm)
  all_goals try (first | omega | (simp only [hn]; omega) | exact hd | (simp only [hn]; exact hm))
  all_goals (try simp only [hn])

/-- **The cell of the matrix.** -/
theorem adjCell_run (X : List ℕ) (n m : ℕ) (σ : Env) (hX : σ.arrs "X" = X)
    (hn : σ.vars "n" = n) (hm : σ.vars "m" = m) (hmn : σ.vars "mn" = m * n)
    (hmask : σ.vars "mask" = 2 ^ m - 1) (hfc : σ.vars "fc" < n * n)
    (hlen : 2 + 2 * (m * n) + 1 ≤ X.length) (hXB : ∀ v ∈ X, v < B) (hB : X.length + 8 < B)
    (hmB : m + 3 < B) (hnB : n < B) (hmk : 2 ^ m < B) (hnn : n * n < B) :
    ∃ σ', Run B adjCell σ σ' (214 * m + 90) ∧
      σ'.vars "val" = adjBit X n m (σ.vars "fc") ∧ σ'.arrs = σ.arrs ∧
      (∀ y, y ∉ SG → σ'.vars y = σ.vars y) ∧ σ'.out = σ.out := by
  have hnpos : 0 < n := by
    by_contra h; have : n = 0 := by omega
    subst this; omega
  have hfcB : σ.vars "fc" < B := by omega
  have hmaskB : σ.vars "mask" < B := by rw [hmask]; omega
  obtain ⟨σ1, r1, e1⟩ := adjPre_run (B := B) σ n hn hnB hmaskB hfcB (by omega)
  have hdu1 : σ1.vars "du" = σ.vars "fc" / n := by rw [e1]; simp [Env.setVar]
  have hdv1 : σ1.vars "dv" = σ.vars "fc" % n := by
    rw [e1]; simp [Env.setVar, mod_eq_sub]
  have hdt1 : σ1.vars "dt" = σ.vars "mask" := by rw [e1]; simp [Env.setVar]
  have hdq1 : σ1.vars "dq" = σ.vars "mask" := by rw [e1]; simp [Env.setVar]
  have hvi1 : σ1.vars "vi" = 0 := by rw [e1]; simp [Env.setVar]
  have hfr1 : ∀ y, y ∉ ["du", "dv", "dt", "dq", "vi"] → σ1.vars y = σ.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [e1]; simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2]
  have har1 : σ1.arrs = σ.arrs := by rw [e1]; simp [Env.setVar]
  have ho1 : σ1.out = σ.out := by rw [e1]; simp [Env.setVar]
  have hdult : σ1.vars "du" < n := by
    rw [hdu1]; exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hfc)
  have hdvlt : σ1.vars "dv" < n := by rw [hdv1]; exact Nat.mod_lt _ hnpos
  obtain ⟨σ2, r2, hv2, hA2, ho2⟩ := dLoop_run (B := B) X n m σ1 (by rw [har1]; exact hX)
    (by rw [hfr1 "n" (by simp)]; exact hn) (by rw [hfr1 "m" (by simp)]; exact hm)
    (by rw [hfr1 "mn" (by simp)]; exact hmn) hdult hdvlt hlen hXB hB
    (by rw [hdt1, hmask]; omega) (by rw [hdq1, hmask]; omega) (by omega) hnB
    (by rw [hvi1]; omega)
  have hdu2 : σ2.vars "du" = σ.vars "fc" / n := by rw [hA2.2 "du" (by simp [SD]), hdu1]
  have hdv2 : σ2.vars "dv" = σ.vars "fc" % n := by rw [hA2.2 "dv" (by simp [SD]), hdv1]
  have hcnt : σ2.vars "vi" = cfDayN X n m (σ.vars "fc" / n) (σ.vars "fc" % n) (2 ^ m - 1) (2 ^ m - 1) := by
    rw [hv2, hvi1, hdu1, hdv1, hdt1, hdq1, hmask]; simp
  have hvi2B : σ2.vars "vi" ≤ m := by rw [hcnt]; exact cfDayN_le _ _ _ _ _ _ _
  have hiff := cfDayN_mask_pos X n m (σ.vars "fc" / n) (σ.vars "fc" % n)
  have hAdj : (if σ.vars "fc" / n ≠ σ.vars "fc" % n then
      (if 0 < σ2.vars "vi" then 1 else 0) else 0) = adjBit X n m (σ.vars "fc") := by
    unfold adjBit
    rw [hcnt]
    by_cases h1 : σ.vars "fc" / n ≠ σ.vars "fc" % n <;>
      by_cases h2 : ∃ d < m, cfN X n m d (σ.vars "fc" / n) (σ.vars "fc" % n) <;>
      simp [h1, h2, hiff]
  obtain ⟨σ3, r3, e3, ha3, ho3, hf3⟩ : ∃ σ3, Run B adjFin σ2 σ3 20 ∧
      σ3.vars "val" = (if σ.vars "fc" / n ≠ σ.vars "fc" % n then
        (if 0 < σ2.vars "vi" then 1 else 0) else 0) ∧ σ3.arrs = σ2.arrs ∧ σ3.out = σ2.out ∧
      (∀ y, y ≠ "val" → σ3.vars y = σ2.vars y) := by
    unfold adjFin
    run_vcg
    all_goals first
      | (refine ⟨?_, rfl, rfl, fun y hy => by simp [Env.setVar, hy]⟩
         nrmB
         first
           | rw [if_neg (by omega)]
           | rw [if_pos (by omega), if_pos (by omega)]
           | rw [if_pos (by omega), if_neg (by omega)])
      | omega
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), by rw [e3, hAdj], by rw [ha3, hA2.1, har1], ?_, by rw [ho3, ho2, ho1]⟩
  intro y hy
  have hy' : y ∉ ["du", "dv", "dt", "dq", "vi"] ∧ y ∉ SD ∧ y ≠ "val" := by
    refine ⟨?_, fun h => hy (by simp [SG, h]), fun h => hy (by simp [SG, h])⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> exact hy (by simp [SG, SD, h])
  rw [hf3 y hy'.2.2, hA2.2 y hy'.2.1, hfr1 y hy'.1]

end Lax117284Proofs.Machine.TwGraph

end

/-! ### `Lax117284Proofs.Machine.TwGraph2` -/

section
/-!
The word of the graph: the fill of the matrix, the whole array, and the fact that it presents the
overall conflict graph.
-/

namespace Lax117284Proofs.Machine.TwGraph

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit
open Lax117284.Scheduling Lax117284.InstanceEncoding

variable {B : ℕ}

theorem graphFill_run (X : List ℕ) (n m : ℕ) (σ : Env) (hX : σ.arrs "X" = X)
    (hn : σ.vars "n" = n) (hm : σ.vars "m" = m) (hmn : σ.vars "mn" = m * n)
    (hmask : σ.vars "mask" = 2 ^ m - 1) (hbs : σ.vars "bs" = 1) (hfn : σ.vars "fn" = n * n)
    (hY : 1 + n * n ≤ (σ.arrs "Y").length)
    (hlen : 2 + 2 * (m * n) + 1 ≤ X.length) (hXB : ∀ v ∈ X, v < B) (hB : X.length + 8 < B)
    (hmB : m + 3 < B) (hnB : n < B) (hmk : 2 ^ m < B) (hnn : n * n + 8 < B) :
    ∃ σ', Run B (fillLoop "Y" adjCell) σ σ' ((214 * m + 90 + 20 + 4) * (n * n) + 6) ∧
      (σ'.arrs "Y").length = (σ.arrs "Y").length ∧
      (∀ k, (σ'.arrs "Y").getD k 0 =
        if 1 ≤ k ∧ k < 1 + n * n then adjBit X n m (k - 1) else (σ.arrs "Y").getD k 0) ∧
      AgrA ("fc" :: SG) "Y" σ σ' ∧ σ'.out = σ.out := by
  have hres := fillLoop_run (B := B) "Y" adjCell (adjBit X n m) ("fc" :: SG) (214 * m + 90) (n * n)
    σ hfn (by omega) (by rw [hbs]; omega)
    (fun k => by
      have : adjBit X n m k ≤ 1 := by unfold adjBit; split_ifs <;> omega
      omega) (by simp [SG, SD]) (by rw [hbs]; omega) (by
      intro τ hF hA hlt
      have hfr : ∀ y, y ∉ "fc" :: SG → τ.vars y = σ.vars y := hA.1
      have e1 : τ.vars "n" = n := by rw [hfr "n" (by simp [SG, SD])]; exact hn
      have e2 : τ.vars "m" = m := by rw [hfr "m" (by simp [SG, SD])]; exact hm
      have e3 : τ.vars "mn" = m * n := by rw [hfr "mn" (by simp [SG, SD])]; exact hmn
      have e4 : τ.vars "mask" = 2 ^ m - 1 := by rw [hfr "mask" (by simp [SG, SD])]; exact hmask
      have e5 : τ.arrs "X" = X := by rw [hA.2 "X" (by decide)]; exact hX
      obtain ⟨τ', r, hv, ha, hf, ho⟩ := adjCell_run (B := B) X n m τ e5 e1 e2 e3 e4 hlt hlen hXB hB
        hmB hnB hmk (by omega)
      exact ⟨τ', r, hv, by rw [ha], fun y hy => hf y (fun h => hy (List.mem_cons_of_mem _ h)),
        hf "fc" (by simp [SG, SD]), ho⟩)
  obtain ⟨σ', r, hl, hg, hA, ho⟩ := hres
  refine ⟨σ', r, hl, fun k => ?_, hA, ho⟩
  rw [hg k, hbs]

/-- The word of the graph: the number of clients, then the matrix. -/
def gwList (X : List ℕ) (n m : ℕ) : List ℕ := n :: (List.range (n * n)).map (adjBit X n m)

lemma gwList_length (X : List ℕ) (n m : ℕ) : (gwList X n m).length = 1 + n * n := by
  simp [gwList]; try omega

lemma gwList_getD_zero (X : List ℕ) (n m : ℕ) : (gwList X n m).getD 0 0 = n := by
  simp [gwList]

lemma gwList_getD_succ (X : List ℕ) (n m : ℕ) {k : ℕ} (hk : k < n * n) :
    (gwList X n m).getD (1 + k) 0 = adjBit X n m k := by
  simp [gwList, List.getD_eq_getElem?_getD, hk, Nat.add_comm 1 k]

/-- **The matrix is the adjacency of the overall conflict graph.** -/
theorem encodesGraph_gwList {I : Instance} {y X : List ℕ} (hy : EncodesInstance y I)
    (hXy : ∀ j < y.length, X.getD j 0 = y.getD j 0) :
    Lax117284.Bodlaender.EncodesGraph (gwList X I.clients I.days) I := by
  classical
  refine ⟨by rw [gwList_length], by rw [gwList_getD_zero], fun u v => ?_⟩
  have hnpos : 0 < I.clients := by have := u.isLt; omega
  have hk : u.val * I.clients + v.val < I.clients * I.clients := by
    calc u.val * I.clients + v.val < u.val * I.clients + I.clients := by have := v.isLt; omega
      _ = (u.val + 1) * I.clients := by ring
      _ ≤ I.clients * I.clients := Nat.mul_le_mul_right _ u.isLt
  have e : 1 + u.val * I.clients + v.val = 1 + (u.val * I.clients + v.val) := by ring
  rw [e, gwList_getD_succ _ _ _ hk]
  unfold adjBit
  have hdiv : (u.val * I.clients + v.val) / I.clients = u.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hnpos, Nat.div_eq_of_lt v.isLt, Nat.zero_add]
  have hmod : (u.val * I.clients + v.val) % I.clients = v.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt v.isLt]
  rw [hdiv, hmod]
  refine if_congr ?_ rfl rfl
  unfold Lax117284.ConflictGraph.overallGraph
  simp only
  constructor
  · rintro ⟨hne, d, hd, hc⟩
    refine ⟨fun h => hne (by simp [h]), ⟨d, hd⟩, ?_⟩
    exact (Instance.conflictAt_iff I ⟨d, hd⟩ u v).1
      ((Lax117284Proofs.Machine.TwCf.cfN_iff hy hXy hd u.isLt v.isLt).1 hc)
  · rintro ⟨hne, d, hc⟩
    refine ⟨fun h => hne (Fin.ext h), d.val, d.isLt, ?_⟩
    exact (Lax117284Proofs.Machine.TwCf.cfN_iff hy hXy d.isLt u.isLt v.isLt).2
      ((Instance.conflictAt_iff I d u v).2 hc)

end Lax117284Proofs.Machine.TwGraph

end

/-! ### `Lax117284Proofs.Machine.TwGraph3` -/

section
/-!
The array `Y`: the word of the graph followed by the width.
-/

namespace Lax117284Proofs.Machine.TwGraph

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {B : ℕ}

lemma list_ext_getD {a b : List ℕ} (hl : a.length = b.length)
    (h : ∀ k, a.getD k 0 = b.getD k 0) : a = b := by
  apply List.ext_getElem hl
  intro k h1 h2
  have := h k
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

lemma getD_append_singleton (l : List ℕ) (w k : ℕ) :
    (l ++ [w]).getD k 0 = if k < l.length then l.getD k 0 else if k = l.length then w else 0 := by
  by_cases h : k < l.length
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [if_neg h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : l.length ≤ k)]
    by_cases h2 : k = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : k - l.length ≥ 1 := by omega
      rw [List.getElem?_eq_none (by simp; omega)]; simp

/-- The count, and the range of the fill. -/
def gwPre : Com := seqs
  [ .store "Y" (Expr.lit 0) (V "n"),
    .assign "bs" (Expr.lit 1),
    .assign "fn" (mul (V "n") (V "n")) ]

/-- The width. -/
def gwPost : Com := .store "Y" (add (mul (V "n") (V "n")) (Expr.lit 1)) (V "w")

/-- **The word handed to the decomposition step**: the count, the matrix, the width. -/
def gwCom : Com := .seq gwPre (.seq (fillLoop "Y" adjCell) gwPost)

/-- The scalars the word writes. -/
def SGW : List String := "fc" :: SG ++ ["bs", "fn"]

theorem gwPre_run (σ : Env) (n : ℕ) (hn : σ.vars "n" = n) (hnB : n < B) (hnn : n * n + 3 < B)
    (hY : 0 < (σ.arrs "Y").length) :
    ∃ σ1, Run B gwPre σ σ1 20 ∧
      σ1 = (((σ.setArr "Y" 0 n).setVar "bs" 1).setVar "fn" (n * n)) := by
  unfold gwPre seqs
  run_vcg
  all_goals (try nrmB)
  all_goals try (first | omega | (simp only [hn]; omega))
  all_goals (try simp only [hn])

theorem gwPost_run (σ : Env) (n : ℕ) (hn : σ.vars "n" = n) (hnB : n < B) (hnn : n * n + 3 < B)
    (hw : σ.vars "w" < B) (hlen : n * n + 1 < (σ.arrs "Y").length) :
    ∃ σ1, Run B gwPost σ σ1 20 ∧ σ1 = σ.setArr "Y" (n * n + 1) (σ.vars "w") := by
  unfold gwPost
  run_vcg
  all_goals (try nrmB)
  all_goals try (first | omega | (simp only [hn]; omega))
  all_goals (try simp only [hn])

theorem gwCom_run (X : List ℕ) (n m : ℕ) (σ : Env) (hX : σ.arrs "X" = X)
    (hn : σ.vars "n" = n) (hm : σ.vars "m" = m) (hmn : σ.vars "mn" = m * n)
    (hmask : σ.vars "mask" = 2 ^ m - 1) (hY : σ.arrs "Y" = List.replicate (n * n + 2) 0)
    (hlen : 2 + 2 * (m * n) + 1 ≤ X.length) (hXB : ∀ v ∈ X, v < B) (hB : X.length + 8 < B)
    (hmB : m + 3 < B) (hnB : n < B) (hmk : 2 ^ m < B) (hnn : n * n + 8 < B)
    (hw : σ.vars "w" < B) :
    ∃ σ', Run B gwCom σ σ' ((214 * m + 90 + 20 + 4) * (n * n) + 6 + 60) ∧
      σ'.arrs "Y" = gwList X n m ++ [σ.vars "w"] ∧
      (∀ a, a ≠ "Y" → σ'.arrs a = σ.arrs a) ∧ (∀ v, v ∉ SGW → σ'.vars v = σ.vars v) ∧
      σ'.out = σ.out := by
  obtain ⟨σ1, r1, e1⟩ := gwPre_run (B := B) σ n hn hnB (by omega) (by rw [hY]; simp)
  have hY1 : σ1.arrs "Y" = (List.replicate (n * n + 2) 0).set 0 n := by rw [e1]; simp [hY]
  have hY1l : (σ1.arrs "Y").length = n * n + 2 := by rw [hY1]; simp
  have hoth1 : ∀ a, a ≠ "Y" → σ1.arrs a = σ.arrs a := by intro a ha; rw [e1]; simp [ha]
  have hv1 : ∀ v, v ≠ "bs" → v ≠ "fn" → σ1.vars v = σ.vars v := by
    intro v h1 h2; rw [e1]; simp [Env.setVar, h1, h2]
  obtain ⟨σ4, r4, hl4, hg4, hA4, ho4⟩ := graphFill_run (B := B) X n m σ1
    (by rw [hoth1 "X" (by decide), hX])
    (by rw [hv1 "n" (by decide) (by decide), hn]) (by rw [hv1 "m" (by decide) (by decide), hm])
    (by rw [hv1 "mn" (by decide) (by decide), hmn])
    (by rw [hv1 "mask" (by decide) (by decide), hmask]) (by rw [e1]; simp) (by rw [e1]; simp)
    (by rw [hY1l]; omega) hlen hXB hB hmB hnB hmk hnn
  have hv4 : ∀ v, v ∉ SGW → σ4.vars v = σ.vars v := by
    intro v hv
    have h4 : σ4.vars v = σ1.vars v := hA4.1 v (fun h => hv (by
      simp only [SGW, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
      simp only [List.mem_cons] at h ⊢; tauto))
    rw [h4, hv1 v (fun h => hv (by simp [SGW, h])) (fun h => hv (by simp [SGW, h]))]
  have hw4 : σ4.vars "w" = σ.vars "w" := hv4 "w" (by simp [SGW, SG, SD])
  have hn4 : σ4.vars "n" = n := by rw [hv4 "n" (by simp [SGW, SG, SD]), hn]
  have hYl4 : (σ4.arrs "Y").length = n * n + 2 := by rw [hl4, hY1l]
  obtain ⟨σ5, r5, e5⟩ := gwPost_run (B := B) σ4 n hn4 hnB (by omega) (by rw [hw4]; exact hw)
    (by rw [hYl4]; omega)
  have hY5 : σ5.arrs "Y" = (σ4.arrs "Y").set (n * n + 1) (σ.vars "w") := by
    rw [e5, hw4]; simp
  refine ⟨σ5, ?_, ?_, ?_, ?_, ?_⟩
  · exact (r1.seq (r4.seq r5)).mono (by omega)
  · rw [hY5]
    refine list_ext_getD (by rw [List.length_set, hYl4]; simp [gwList_length]; omega) (fun k => ?_)
    rw [getD_set', getD_append_singleton, gwList_length, hYl4]
    by_cases hk : k = n * n + 1
    · subst hk
      rw [if_pos ⟨rfl, by omega⟩, if_neg (by omega), if_pos (by omega)]
    · by_cases hk0 : k = 0
      · subst hk0
        rw [if_neg (by omega), hg4 0, if_neg (by omega), if_pos (by omega)]
        rw [hY1, getD_set', if_pos ⟨rfl, by simp⟩, gwList_getD_zero]
      · by_cases hkr : k < 1 + n * n
        · rw [if_neg (by omega), if_pos hkr, hg4 k, if_pos ⟨by omega, hkr⟩]
          have : k = 1 + (k - 1) := by omega
          conv_rhs => rw [this]
          rw [gwList_getD_succ X n m (by omega)]
        · rw [if_neg (by omega), if_neg hkr, if_neg (by omega), hg4 k, if_neg (by omega)]
          rw [hY1, getD_set']
          rw [if_neg (by omega)]
          exact List.getD_eq_default _ _ (by simp; omega)
  · intro a ha
    rw [e5]; simp [ha, hA4.2 a ha, hoth1 a ha]
  · intro v hv
    rw [e5, hw4]; simp [hv4 v hv]
  · rw [e5]; simp [ho4, e1]

end Lax117284Proofs.Machine.TwGraph

end

/-! ### `Lax117284Proofs.Machine.TwKeep` -/

section
/-!
What a node program keeps: everything but its scratch scalars and the rows it fills.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

/-- The scalars the node programs write. -/
def SN : List String :=
  ["c", "vx", "ot", "s", "cw", "p", "pt", "s1", "iw", "bs", "fn", "fc", "val", "Pp", "shp1",
    "cbase", "off", "vs", "e", "lo", "hi", "rm", "so", "ac", "ix", "kd", "ov", "ob", "tbs"] ++ SV

/-- **Nothing but the scratch scalars changed, the input arrays are as they were, and the arrays
that are filled kept their length.** -/
structure Keep (σ0 σ : Env) : Prop where
  vars : ∀ y, y ∉ SN → σ.vars y = σ0.vars y
  X : σ.arrs "X" = σ0.arrs "X"
  O : σ.arrs "O" = σ0.arrs "O"
  szl : (σ.arrs "SZ").length = (σ0.arrs "SZ").length
  bgl : (σ.arrs "BG").length = (σ0.arrs "BG").length
  tbl : (σ.arrs "TB").length = (σ0.arrs "TB").length
  out : σ.out = σ0.out

lemma Keep.refl (σ : Env) : Keep σ σ := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma Keep.trans {σ0 σ1 σ2 : Env} (h1 : Keep σ0 σ1) (h2 : Keep σ1 σ2) : Keep σ0 σ2 :=
  ⟨fun y hy => (h2.vars y hy).trans (h1.vars y hy), h2.X.trans h1.X, h2.O.trans h1.O,
    h2.szl.trans h1.szl, h2.bgl.trans h1.bgl, h2.tbl.trans h1.tbl, h2.out.trans h1.out⟩

lemma Keep.of_agr {S : List String} {σ0 σ : Env} (h : Agr S σ0 σ) (hS : ∀ y ∈ S, y ∈ SN)
    (ho : σ.out = σ0.out) : Keep σ0 σ := by
  refine ⟨fun y hy => h.2 y (fun hyS => hy (hS y hyS)), ?_, ?_, ?_, ?_, ?_, ho⟩ <;>
    simp [h.1]

lemma Keep.of_agrA {S : List String} {arr : String} {σ0 σ : Env} (h : AgrA S arr σ0 σ)
    (hl : (σ.arrs arr).length = (σ0.arrs arr).length) (hS : ∀ y ∈ S, y ∈ SN)
    (harr : arr = "SZ" ∨ arr = "BG" ∨ arr = "TB") (ho : σ.out = σ0.out) : Keep σ0 σ := by
  have hx : ∀ a, a ≠ arr → σ.arrs a = σ0.arrs a := h.2
  rcases harr with rfl | rfl | rfl
  · exact ⟨fun y hy => h.1 y (fun hyS => hy (hS y hyS)), hx _ (by decide), hx _ (by decide), hl,
      by rw [hx _ (by decide)], by rw [hx _ (by decide)], ho⟩
  · exact ⟨fun y hy => h.1 y (fun hyS => hy (hS y hyS)), hx _ (by decide), hx _ (by decide),
      by rw [hx _ (by decide)], hl, by rw [hx _ (by decide)], ho⟩
  · exact ⟨fun y hy => h.1 y (fun hyS => hy (hS y hyS)), hx _ (by decide), hx _ (by decide),
      by rw [hx _ (by decide)], by rw [hx _ (by decide)], hl, ho⟩

lemma Keep.setVar {σ0 σ : Env} (h : Keep σ0 σ) {x : String} (hx : x ∈ SN) (v : ℕ) :
    Keep σ0 (σ.setVar x v) := by
  refine ⟨fun y hy => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : y ≠ x := fun e => hy (e ▸ hx)
    simp only [vars_setVar, this, if_false]; exact h.vars y hy
  · simpa using h.X
  · simpa using h.O
  · simpa using h.szl
  · simpa using h.bgl
  · simpa using h.tbl
  · simpa using h.out

lemma Keep.setArr {σ0 σ : Env} (h : Keep σ0 σ) {a : String} (ha : a = "SZ" ∨ a = "BG" ∨ a = "TB")
    (i v : ℕ) : Keep σ0 (σ.setArr a i v) := by
  rcases ha with rfl | rfl | rfl
  · exact ⟨fun y hy => by simpa using h.vars y hy, by simpa using h.X, by simpa using h.O,
      by simpa using h.szl, by simpa using h.bgl, by simpa using h.tbl, by simpa using h.out⟩
  · exact ⟨fun y hy => by simpa using h.vars y hy, by simpa using h.X, by simpa using h.O,
      by simpa using h.szl, by simpa using h.bgl, by simpa using h.tbl, by simpa using h.out⟩
  · exact ⟨fun y hy => by simpa using h.vars y hy, by simpa using h.X, by simpa using h.O,
      by simpa using h.szl, by simpa using h.bgl, by simpa using h.tbl, by simpa using h.out⟩

variable {P : Params} {B : ℕ}

lemma Keep.nc {σ0 σ : Env} (h : NC P B σ0) (k : Keep σ0 σ) : NC P B σ :=
  h.transfer (fun y hy => k.vars y (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [SN, SV, Stt, St2, SD])) k.X k.O k.szl k.bgl k.tbl

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwIntro` -/

section
/-!
The program of an introduce node.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- Every sorted bag has at most `wid` entries. -/
lemma bagL_len_le (P : Params) {j : ℕ} (hj : j < P.N) : (bagL P.D j).length ≤ P.wid :=
  bagL_length_le P.hD hj

/-- The entries of a sorted bag are clients (or the default zero). -/
lemma bagL_get_le (P : Params) {j : ℕ} (hj : j < P.N) (t : ℕ) : (bagL P.D j)[t]! ≤ P.n := by
  by_cases ht : t < (bagL P.D j).length
  · obtain ⟨-, hm⟩ := bagL_spec P.hD j hj
    have := ((hm _).1 (List.getElem_mem ht)).1
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ht]
    exact this.le
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp

lemma bagL_get_lt (P : Params) {j t : ℕ} (hj : j < P.N) (ht : t < (bagL P.D j).length) :
    (bagL P.D j)[t]! < P.n := by
  obtain ⟨-, hm⟩ := bagL_spec P.hD j hj
  have := ((hm _).1 (List.getElem_mem ht)).1
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  exact this

lemma vertex_eq (P : Params) (hC : NC P B σ) {i : ℕ} (hi : i < P.N) :
    (σ.arrs "O").getD (3 + 3 * i) 0 = vertex P.D i := by
  have hl : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have := hC.O_ (2 + 3 * i) (by omega)
  rw [show 2 + 3 * i + 1 = 3 + 3 * i by omega] at this
  rw [this]; rfl

lemma other_eq (P : Params) (hC : NC P B σ) {i : ℕ} (hi : i < P.N) :
    (σ.arrs "O").getD (4 + 3 * i) 0 = other P.D i := by
  have hl : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have := hC.O_ (3 + 3 * i) (by omega)
  rw [show 3 + 3 * i + 1 = 4 + 3 * i by omega] at this
  rw [this]; rfl

lemma kind_eq (P : Params) (hC : NC P B σ) {i : ℕ} (hi : i < P.N) :
    (σ.arrs "O").getD (2 + 3 * i) 0 = kind P.D i := by
  have hl : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have := hC.O_ (1 + 3 * i) (by omega)
  rw [show 1 + 3 * i + 1 = 2 + 3 * i by omega] at this
  rw [this]; rfl

/-! ### The head: the record, the position, the sizes -/

/-- The sizes an introduce node needs. -/
def introTail1 : Com := seqs
  [ .assign "s1" (add (V "s") (L 1)),
    .assign "iw" (mul (V "i") (V "w1")),
    .assign "bs" (V "iw"),
    .assign "fn" (V "s1") ]

/-- The head of the program of an introduce node. -/
def introHead : Com := .seq recCom (.seq posLoop introTail1)

lemma SR_sub : ∀ y ∈ SR, y ∈ SN := by intro y hy; simp only [SR, List.mem_cons, List.not_mem_nil, or_false] at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [SN]

theorem introHead_run {i0 : ℕ} (hC : NC P B σ)
    (hN : NI P.I P.kk P.D P.wid P.tabs (i0 + 1) σ) (hi : σ.vars "i" = i0 + 1) (hiN : i0 + 1 < P.N) :
    ∃ σ1, Run B introHead σ σ1 (34 * P.wid + 130) ∧ Keep σ σ1 ∧ σ1.arrs = σ.arrs ∧
      σ1.vars "c" = i0 ∧ σ1.vars "s" = (bagL P.D i0).length ∧
      σ1.vars "vx" = vertex P.D (i0 + 1) ∧ σ1.vars "ot" = other P.D (i0 + 1) ∧
      σ1.vars "p" = pos (bagL P.D i0) (vertex P.D (i0 + 1)) ∧ σ1.vars "cw" = i0 * P.wid ∧
      σ1.vars "s1" = (bagL P.D i0).length + 1 ∧ σ1.vars "iw" = (i0 + 1) * P.wid ∧
      σ1.vars "bs" = (i0 + 1) * P.wid ∧ σ1.vars "fn" = (bagL P.D i0).length + 1 := by
  have hBpos : 0 < B := by have := hC.b3; omega
  have hlD : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have hb2 := hC.b2
  have hb3 := hC.b3
  have hw1 := hC.w1_
  have hNw : ∀ j, j ≤ P.N → j * P.wid ≤ P.N * P.wid := fun j hj => Nat.mul_le_mul_right _ hj
  have hi2 : (i0 + 2) * P.wid ≤ P.N * P.wid := hNw _ (by omega)
  have hi2' : (i0 + 2) * P.wid = i0 * P.wid + P.wid + P.wid := by ring
  have hi1' : (i0 + 1) * P.wid = i0 * P.wid + P.wid := by ring
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  have hSc : (σ.arrs "SZ").getD i0 0 < B := by
    rw [hN.sz i0 (by omega)]; omega
  obtain ⟨σ1, r1, hc1, hvx1, hot1, hs1, hcw1, hp1, A1, o1⟩ := recCom_run (B := B) (σ := σ)
    (i := i0 + 1) (N := P.N) hi hiN hC.lenSZ (by have := hC.lenO; omega)
    (hC.O_lt (by omega) (by omega)) (hC.O_lt (by omega) (by omega))
    (by simpa using hSc) (by have := hC.b3; omega)
    (by rw [hw1, Nat.add_sub_cancel]; have := hNw i0 (by omega); omega)
    (by rw [hw1]; have := hNw 1 (by omega); omega)
  have hvx' : σ1.vars "vx" = vertex P.D (i0 + 1) := by rw [hvx1, vertex_eq P hC hiN]
  have hot' : σ1.vars "ot" = other P.D (i0 + 1) := by rw [hot1, other_eq P hC hiN]
  have hs' : σ1.vars "s" = (bagL P.D i0).length := by
    rw [hs1, Nat.add_sub_cancel, hN.sz i0 (by omega)]
  have hcw' : σ1.vars "cw" = i0 * P.wid := by rw [hcw1, Nat.add_sub_cancel, hw1]
  have hvxB : σ1.vars "vx" < B := by rw [hvx1]; exact hC.O_lt (by omega) (by omega)
  obtain ⟨σ2, r2, hp2, A2, o2⟩ := posLoop_run (B := B) (σ0 := σ1) (f := fun t => (bagL P.D i0)[t]!)
    (s0 := (bagL P.D i0).length) (cw0 := i0 * P.wid) hs' hcw' hp1
    (fun t ht => by rw [A1.1]; exact hN.bg i0 (by omega) t ht)
    (by rw [A1.1]; have := hC.lenBG; omega)
    (fun t => by have := bagL_get_le P (j := i0) (by omega) t; have := hC.b8; omega) hvxB
    (by have := bagL_len_le P (j := i0) (by omega); omega)
  have hs2 : σ2.vars "s" = (bagL P.D i0).length := by rw [A2.2 "s" (by simp), hs']
  have hi2v : σ2.vars "i" = i0 + 1 := by rw [A2.2 "i" (by simp), A1.2 "i" (by simp [SR]), hi]
  have hw2 : σ2.vars "w1" = P.wid := by rw [A2.2 "w1" (by simp), A1.2 "w1" (by simp [SR]), hw1]
  have hp' : σ2.vars "p" = pos (bagL P.D i0) (vertex P.D (i0 + 1)) := by
    rw [hp2, pos_eq_sum, hvx']
  obtain ⟨σ3, r3, e3⟩ : ∃ σ3, Run B introTail1 σ2 σ3 40 ∧ σ3 =
      (((σ2.setVar "s1" ((bagL P.D i0).length + 1)).setVar "iw" ((i0 + 1) * P.wid)).setVar "bs"
        ((i0 + 1) * P.wid)).setVar "fn" ((bagL P.D i0).length + 1) := by
    unfold introTail1 seqs
    run_vcg
    all_goals try (nrmA; simp only [hs2, hi2v, hw2]; omega)
    all_goals try (nrmA; omega)
    all_goals (try nrmA)
    all_goals (try simp only [hs2, hi2v, hw2])
  have hv3 : ∀ y, y ∉ ["s1", "iw", "bs", "fn"] → σ3.vars y = σ2.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [e3]; simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]
  have k1 := Keep.of_agr A1 SR_sub o1
  have k2 := Keep.of_agr A2 (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [SN]) o2
  have k3 : Keep σ2 σ3 := by
    rw [e3]
    exact ((((Keep.refl σ2).setVar (by simp [SN]) _).setVar (by simp [SN]) _).setVar
      (by simp [SN]) _).setVar (by simp [SN]) _
  have har : σ3.arrs = σ.arrs := by rw [e3]; simp [A2.1, A1.1]
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), k1.trans (k2.trans k3), har, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv3 "c" (by simp), A2.2 "c" (by simp), hc1]; simp
  · rw [hv3 "s" (by simp), hs2]
  · rw [hv3 "vx" (by simp), A2.2 "vx" (by simp), hvx']
  · rw [hv3 "ot" (by simp), A2.2 "ot" (by simp), hot']
  · rw [hv3 "p" (by simp), hp']
  · rw [hv3 "cw" (by simp), A2.2 "cw" (by simp), hcw']
  · rw [e3]; simp [Env.setVar, hs2]
  · rw [e3]; simp [Env.setVar]
  · rw [e3]; simp [Env.setVar]
  · rw [e3]; simp [Env.setVar, hs2]

/-! ### The row of the bag -/

/-- The value of the cell of the new bag: the child's entry before the position, the vertex at it,
the child's entry one earlier after it. -/
def bgPreIntro : Com :=
  .ite (.lt (V "fc") (V "p")) (.assign "val" (G "BG" (add (V "cw") (V "fc"))))
    (.ite (.eq (V "fc") (V "p")) (.assign "val" (V "vx"))
      (.assign "val" (G "BG" (sub (add (V "cw") (V "fc")) (L 1)))))

theorem bgPreIntro_run (σ : Env) (l : List ℕ) (p vx cw : ℕ) (hp : σ.vars "p" = p)
    (hvx : σ.vars "vx" = vx) (hcw : σ.vars "cw" = cw)
    (hrd : ∀ t < l.length, (σ.arrs "BG").getD (cw + t) 0 = l[t]!) (hpl : p ≤ l.length)
    (hf : σ.vars "fc" ≤ l.length) (hlen : cw + l.length + 1 ≤ (σ.arrs "BG").length)
    (hbd : ∀ t : ℕ, l[t]! < B) (hvxB : vx < B) (hb : cw + l.length + 8 < B) :
    ∃ σ', Run B bgPreIntro σ σ' 20 ∧
      σ'.vars "val" = (l.insertIdx p vx)[σ.vars "fc"]! ∧ σ'.arrs = σ.arrs ∧
      (∀ y, y ≠ "val" → σ'.vars y = σ.vars y) ∧ σ'.out = σ.out := by
  have hrd' : ∀ t < l.length, (σ.arrs "BG").getD (σ.vars "cw" + t) 0 = l[t]! := by
    rw [hcw]; exact hrd
  have hins := getElem!_insertIdx l p vx hpl (σ.vars "fc")
  unfold bgPreIntro
  run_vcg
  · refine ⟨?_, rfl, fun y hy => by simp [Env.setVar, hy], rfl⟩
    nrmA
    rw [hins, if_pos (by omega), hrd' _ (by omega)]
  · refine ⟨?_, rfl, fun y hy => by simp [Env.setVar, hy], rfl⟩
    nrmA
    rw [hins, if_neg (by omega), if_pos (by omega), hvx]
  · refine ⟨?_, rfl, fun y hy => by simp [Env.setVar, hy], rfl⟩
    nrmA
    rw [hins, if_neg (by omega), if_neg (by omega),
      show σ.vars "cw" + σ.vars "fc" - 1 = σ.vars "cw" + (σ.vars "fc" - 1) by omega,
      hrd' _ (by omega)]
  · rw [hrd' _ (by omega)]; exact hbd _
  · rw [show σ.vars "cw" + σ.vars "fc" - 1 = σ.vars "cw" + (σ.vars "fc" - 1) by omega,
      hrd' _ (by omega)]
    exact hbd _

/-- The length of the bag of an introduce node. -/
lemma bagL_intro_len (P : Params) {i : ℕ} (hk : kind P.D (i + 1) = 1) :
    (bagL P.D (i + 1)).length = (bagL P.D i).length + 1 := by
  rw [bagL_intro hk, List.length_insertIdx_of_le_length pos_le_length]

/-- **The state after the head of an introduce node**, without the description of the arrays. -/
structure HQ (P : Params) (B : ℕ) (i0 : ℕ) (σ : Env) : Prop where
  C : NC P B σ
  iN : i0 + 1 < P.N
  i_ : σ.vars "i" = i0 + 1
  c_ : σ.vars "c" = i0
  s_ : σ.vars "s" = (bagL P.D i0).length
  vx_ : σ.vars "vx" = vertex P.D (i0 + 1)
  p_ : σ.vars "p" = pos (bagL P.D i0) (vertex P.D (i0 + 1))
  cw_ : σ.vars "cw" = i0 * P.wid
  s1_ : σ.vars "s1" = (bagL P.D i0).length + 1
  iw_ : σ.vars "iw" = (i0 + 1) * P.wid
  bs_ : σ.vars "bs" = (i0 + 1) * P.wid
  fn_ : σ.vars "fn" = (bagL P.D i0).length + 1
  k_ : kind P.D (i0 + 1) = 1

/-- The state after the head of an introduce node. -/
structure HP (P : Params) (B : ℕ) (i0 : ℕ) (σ : Env) : Prop extends HQ P B i0 σ where
  N : NI P.I P.kk P.D P.wid P.tabs (i0 + 1) σ

lemma HQ.transfer {i0 : ℕ} {σ σ' : Env} (h : HQ P B i0 σ) (k : Keep σ σ')
    (hv : ∀ y ∈ ["i", "c", "s", "vx", "p", "cw", "s1", "iw", "bs", "fn"],
      σ'.vars y = σ.vars y) : HQ P B i0 σ' :=
  ⟨k.nc h.C, h.iN, by rw [hv "i" (by simp)]; exact h.i_, by rw [hv "c" (by simp)]; exact h.c_,
    by rw [hv "s" (by simp)]; exact h.s_, by rw [hv "vx" (by simp)]; exact h.vx_,
    by rw [hv "p" (by simp)]; exact h.p_, by rw [hv "cw" (by simp)]; exact h.cw_,
    by rw [hv "s1" (by simp)]; exact h.s1_, by rw [hv "iw" (by simp)]; exact h.iw_,
    by rw [hv "bs" (by simp)]; exact h.bs_, by rw [hv "fn" (by simp)]; exact h.fn_, h.k_⟩

lemma NI.of_arrs {I kk D w1 Tm i} {σ σ' : Env} (h : NI I kk D w1 Tm i σ)
    (he : σ'.arrs = σ.arrs) : NI I kk D w1 Tm i σ' :=
  ⟨fun j hj => by rw [he]; exact h.sz j hj, fun j hj t ht => by rw [he]; exact h.bg j hj t ht,
    fun j hj e he' => by rw [he]; exact h.tb j hj e he'⟩

theorem introBG_run {i0 : ℕ} (h : HP P B i0 σ) :
    ∃ σ4, Run B (fillLoop "BG" bgPreIntro) σ σ4 ((20 + 20 + 4) * ((bagL P.D i0).length + 1) + 6) ∧
      AgrA ["fc", "val"] "BG" σ σ4 ∧ σ4.out = σ.out ∧
      (σ4.arrs "BG").length = (σ.arrs "BG").length ∧
      RowDesc "BG" ((i0 + 1) * P.wid) (bagL P.D (i0 + 1)).length
        (fun t => (bagL P.D (i0 + 1))[t]!) σ σ4 := by
  have hC := h.C
  have hiN := h.iN
  have hlD : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have hl1 := bagL_intro_len P h.k_
  have hle1 := bagL_len_le P (j := i0 + 1) h.iN
  have hle0 := bagL_len_le P (j := i0) (by have := h.iN; omega)
  have hb2 := hC.b2
  have hb3 := hC.b3
  have hb8 := hC.b8
  have hBpos : 0 < B := by omega
  have hNw : (i0 + 2) * P.wid ≤ P.N * P.wid := Nat.mul_le_mul_right _ h.iN
  have hi2' : (i0 + 2) * P.wid = i0 * P.wid + P.wid + P.wid := by ring
  have hi1' : (i0 + 1) * P.wid = i0 * P.wid + P.wid := by ring
  have hlenBG := hC.lenBG
  have hvxB : σ.vars "vx" < B := by
    rw [h.vx_, ← vertex_eq P hC h.iN]; exact hC.O_lt (by omega) (by omega)
  have hpl : pos (bagL P.D i0) (vertex P.D (i0 + 1)) ≤ (bagL P.D i0).length := pos_le_length
  have hres := fillLoop_run (B := B) "BG" bgPreIntro (fun t => (bagL P.D (i0 + 1))[t]!)
    ["fc", "val"] 20 ((bagL P.D i0).length + 1) σ h.fn_ (by omega)
    (by rw [h.bs_]; omega) (fun t => by
      have := bagL_get_le P (j := i0 + 1) h.iN t; omega) (by simp) (by rw [h.bs_]; omega) (by
    intro σ' hF hA hlt
    have e1 : σ'.vars "p" = σ.vars "p" := hA.1 "p" (by simp)
    have e2 : σ'.vars "vx" = σ.vars "vx" := hA.1 "vx" (by simp)
    have e3 : σ'.vars "cw" = σ.vars "cw" := hA.1 "cw" (by simp)
    have hbsl : σ.vars "bs" = (i0 + 1) * P.wid := h.bs_
    obtain ⟨σ'', r, hv, ha, hfr, ho⟩ := bgPreIntro_run (B := B) σ' (bagL P.D i0)
      (pos (bagL P.D i0) (vertex P.D (i0 + 1))) (vertex P.D (i0 + 1)) (i0 * P.wid)
      (by rw [e1, h.p_]) (by rw [e2, h.vx_]) (by rw [e3, h.cw_])
      (fun t ht => by
        rw [hF.2, if_neg (by rw [hbsl]; omega)]
        exact h.N.bg i0 (by omega) t ht) hpl (by omega)
      (by rw [hF.1]; omega)
      (fun t => by have := bagL_get_le P (j := i0) (by omega) t; omega)
      (by rw [← h.vx_]; exact hvxB) (by omega)
    refine ⟨σ'', r, ?_, by rw [ha], fun y hy => hfr y (by intro e; exact hy (by simp [e])),
      hfr "fc" (by decide), ho⟩
    rw [hv, ← bagL_intro h.k_])
  obtain ⟨σ4, r, hl, hg, hA, ho⟩ := hres
  refine ⟨σ4, r, hA, ho, hl, fun k => ?_⟩
  rw [hg k, h.bs_, hl1]

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwIntro2` -/

section
/-!
The program of an introduce node, continued: the size, the parameters of the table, and the table.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

lemma bpow (P : Params) (s : ℕ) : (2 ^ P.I.days) ^ s = 2 ^ (P.m * s) := by
  rw [← pow_mul]; rfl

lemma pow_le_tabs (P : Params) {s : ℕ} (hs : s ≤ P.wid) : 2 ^ (P.m * s) ≤ P.tabs := by
  unfold Params.tabs Params.bs
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hs)

section Tbv

variable {I : Lax117284.Scheduling.Instance} {kk : ℕ} {D : List ℕ} {j e : ℕ}

lemma tbv_one (h : TB I kk D j e) : tbv I kk D j e = 1 := by unfold tbv; simp [h]

lemma tbv_zero (h : ¬ TB I kk D j e) : tbv I kk D j e = 0 := by unfold tbv; simp [h]

lemma tbv_le_one : tbv I kk D j e ≤ 1 := by
  by_cases h : TB I kk D j e
  · rw [tbv_one h]
  · rw [tbv_zero h]; omega

/-- **The table entry of an introduce node**, as a number. -/
lemma tbv_intro {i : ℕ} (hk : kind D (i + 1) = 1) :
    tbv I kk D (i + 1) e = if violE I kk (bagL D (i + 1)) e = 0 then
      tbv I kk D i (rmN (2 ^ I.days) (pos (bagL D i) (vertex D (i + 1))) e) else 0 := by
  by_cases h : violE I kk (bagL D (i + 1)) e = 0
  · rw [if_pos h]
    have h1 := (violE_eq_zero I kk _ e).1 h
    by_cases h2 : TB I kk D i (rmN (2 ^ I.days) (pos (bagL D i) (vertex D (i + 1))) e)
    · rw [tbv_one ((TB_intro hk).2 ⟨h1.1, h1.2, h2⟩), tbv_one h2]
    · rw [tbv_zero (fun h' => h2 ((TB_intro hk).1 h').2.2), tbv_zero h2]
  · rw [if_neg h]
    exact tbv_zero (fun h' => h ((violE_eq_zero I kk _ e).2
      ⟨((TB_intro hk).1 h').1, ((TB_intro hk).1 h').2.1⟩))

end Tbv

/-! ### The size and the parameters of the table -/

/-- Store the size, and set the parameters of the fill of the table. -/
def introMid : Com := seqs
  [ .store "SZ" (V "i") (V "s1"),
    .assign "Pp" (.bin .shiftl (L 1) (mul (V "m") (V "p"))),
    .assign "shp1" (mul (V "m") (add (V "p") (L 1))),
    .assign "cbase" (mul (V "c") (V "Tm")),
    .assign "off" (V "iw"),
    .assign "vs" (V "s1"),
    .assign "bs" (mul (V "i") (V "Tm")),
    .assign "fn" (.bin .shiftl (L 1) (mul (V "m") (V "s1"))) ]

/-- The state after `introMid`. -/
def midState (P : Params) (i0 : ℕ) (σ : Env) : Env :=
  (((((((σ.setArr "SZ" (i0 + 1) ((bagL P.D i0).length + 1)).setVar "Pp"
    (2 ^ (P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1))))).setVar "shp1"
    (P.m * (pos (bagL P.D i0) (vertex P.D (i0 + 1)) + 1))).setVar "cbase" (i0 * P.tabs)).setVar
    "off" ((i0 + 1) * P.wid)).setVar "vs" ((bagL P.D i0).length + 1)).setVar "bs"
    ((i0 + 1) * P.tabs)).setVar "fn" (2 ^ (P.m * ((bagL P.D i0).length + 1)))

theorem introMid_run {i0 : ℕ} (h : HQ P B i0 σ) :
    ∃ σ', Run B introMid σ σ' 100 ∧ σ' = midState P i0 σ := by
  have hC := h.C
  have hiN := h.iN
  have hl1 := bagL_intro_len P h.k_
  have hle1 := bagL_len_le P (j := i0 + 1) h.iN
  have hb1 := hC.b1
  have hb9 := hC.b9
  have hb3 := hC.b3
  have hb2 := hC.b2
  have hiw : (i0 + 1) * P.wid ≤ P.N * P.wid := Nat.mul_le_mul_right _ (by omega)
  have hpl : pos (bagL P.D i0) (vertex P.D (i0 + 1)) ≤ (bagL P.D i0).length := pos_le_length
  have hlenSZ := hC.lenSZ
  have hNt : (i0 + 2) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ h.iN
  have hi2 : (i0 + 2) * P.tabs = i0 * P.tabs + P.tabs + P.tabs := by ring
  have hi1 : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
  have hp1 : 2 ^ (P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1))) ≤ P.tabs :=
    pow_le_tabs P (by omega)
  have hp2 : 2 ^ (P.m * ((bagL P.D i0).length + 1)) ≤ P.tabs := pow_le_tabs P (by omega)
  have hmp : P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1)) ≤ P.m * P.wid :=
    Nat.mul_le_mul_left _ (by omega)
  have hmp1 : P.m * (pos (bagL P.D i0) (vertex P.D (i0 + 1)) + 1) ≤ P.m * P.wid :=
    Nat.mul_le_mul_left _ (by omega)
  have hms1 : P.m * ((bagL P.D i0).length + 1) ≤ P.m * P.wid := Nat.mul_le_mul_left _ (by omega)
  have hmw : P.m * (P.wid + 1) = P.m * P.wid + P.m := by ring
  have hct : i0 * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ (by omega)
  unfold introMid seqs
  run_vcg
  all_goals (try nrmA)
  all_goals try (first | omega | (simp only [h.i_, h.s1_, hC.m_, h.p_, hC.Tm_, h.c_, h.iw_, one_mul]; omega))
  all_goals (try simp only [midState, h.i_, h.s1_, hC.m_, h.p_, hC.Tm_, h.c_, h.iw_, one_mul])

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwIntro3` -/

section
/-!
The cell of the table of an introduce node.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- The cost of the count of the violations, for a bag of `l` clients and `m` days. -/
def vcost (m l : ℕ) : ℕ :=
  (30 + ((30 + (200 + 10 + 4) * m + 6 + 10 + 4) * l + 6) + ((10 + 10 + 4) * m + 6 + 2) + 20 + 10 +
    4) * l + 6 + 2

lemma vcost_mono (m : ℕ) {l l' : ℕ} (h : l ≤ l') : vcost m l ≤ vcost m l' := by
  unfold vcost; gcongr

lemma violN_le (X : List ℕ) (n m kk : ℕ) (bl : List ℕ) (e : ℕ) :
    violN X n m kk bl e ≤ bl.length * (bl.length * m + 1) := by
  unfold violN
  refine le_trans (Finset.sum_le_sum (g := fun _ => 1 + bl.length * m) fun t ht => ?_) ?_
  · have ht' := Finset.mem_range.1 ht
    have h1 : ∑ t2 ∈ Finset.range t, cfDayN X n m bl[t]! bl[t2]! (dg (2 ^ m) e t)
        (dg (2 ^ m) e t2) ≤ t * m := by
      calc _ ≤ ∑ t2 ∈ Finset.range t, m :=
            Finset.sum_le_sum fun t2 _ => cfDayN_le _ _ _ _ _ _ _
        _ = t * m := by simp
    have h2 : t * m ≤ bl.length * m := Nat.mul_le_mul_right m ht'.le
    split_ifs <;> omega
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [add_comm 1]

/-- The lookup in the table of the child, when there is no violation. -/
def introTail : Com :=
  .ite (.lt (L 0) (V "vi")) (.assign "val" (L 0))
    (seqs [ .assign "lo" (.bin .and (V "e") (sub (V "Pp") (L 1))),
            .assign "hi" (.bin .shiftr (V "e") (V "shp1")),
            .assign "rm" (add (V "lo") (mul (V "hi") (V "Pp"))),
            .assign "val" (G "TB" (add (V "cbase") (V "rm"))) ])

theorem introTail_run (σ : Env) (m p e cb : ℕ) (hPp : σ.vars "Pp" = 2 ^ (m * p))
    (hsh : σ.vars "shp1" = m * (p + 1)) (he : σ.vars "e" = e) (hcb : σ.vars "cbase" = cb)
    (hidx : cb + rmN (2 ^ m) p e < (σ.arrs "TB").length)
    (hTB : (σ.arrs "TB").getD (cb + rmN (2 ^ m) p e) 0 < B)
    (hrm : rmN (2 ^ m) p e < B) (hcbB : cb + rmN (2 ^ m) p e < B)
    (hpp : 2 ^ (m * p) < B) (hsB : m * (p + 1) < B) (heB : e < B) (hB : 2 < B)
    (hvi : σ.vars "vi" < B) :
    ∃ σ', Run B introTail σ σ' 40 ∧
      σ'.vars "val" = (if σ.vars "vi" = 0 then (σ.arrs "TB").getD (cb + rmN (2 ^ m) p e) 0
        else 0) ∧
      σ'.arrs = σ.arrs ∧ (∀ y, y ∉ ["lo", "hi", "rm", "val"] → σ'.vars y = σ.vars y) ∧
      σ'.out = σ.out := by
  have hrs := rmN_shift m p e
  have hlo : Nat.land e (2 ^ (m * p) - 1) < B := by omega
  have hhp : e / 2 ^ (m * (p + 1)) * 2 ^ (m * p) < B := by omega
  have hhi : e / 2 ^ (m * (p + 1)) < B := lt_of_le_of_lt (Nat.div_le_self _ _) heB
  unfold introTail seqs
  run_vcg
  all_goals (try nrmA)
  all_goals try (first | omega | exact hTB | (simp only [hPp, hsh, he, hcb, ← hrs]; first | omega | exact hTB | exact hidx))
  · refine ⟨?_, trivial, ?_, trivial⟩
    · rw [if_neg (by omega)]
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [hy.2.2.2]
  · refine ⟨?_, trivial, ?_, trivial⟩
    · simp only [hPp, hsh, he, hcb, ← hrs]
      rw [if_pos (by omega)]
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwIntro4` -/

section
/-!
The cell of the table of an introduce node: the count of the violations, then the lookup.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

lemma bpow' (P : Params) (s : ℕ) : (2 ^ P.m) ^ s = 2 ^ (P.m * s) := by rw [← pow_mul]

/-- The cell of the table of an introduce node. -/
def introCell : Com := .seq (.assign "e" (V "fc")) (.seq violCom introTail)

/-- The scalars a cell writes. -/
def SI : List String := ["e", "lo", "hi", "rm", "val"] ++ SV

lemma SI_sub : ∀ y ∈ "fc" :: SI, y ∈ SN := by
  intro y hy
  simp only [SI, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | h
  · simp [SN]
  · simp [SN]
  · simp [SN]
  · simp [SN]
  · simp [SN]
  · simp [SN]
  · simp only [SN, List.mem_append]; right; simpa using h

/-- **The context of a cell of the table of an introduce node.** -/
structure TC (P : Params) (B : ℕ) (i0 : ℕ) (σ : Env) : Prop where
  C : NC P B σ
  iN : i0 + 1 < P.N
  k_ : kind P.D (i0 + 1) = 1
  bg : ∀ t < (bagL P.D (i0 + 1)).length,
    (σ.arrs "BG").getD ((i0 + 1) * P.wid + t) 0 = (bagL P.D (i0 + 1))[t]!
  tb : ∀ e < (2 ^ P.m) ^ (bagL P.D i0).length,
    (σ.arrs "TB").getD (i0 * P.tabs + e) 0 = tbv P.I P.kk P.D i0 e
  off_ : σ.vars "off" = (i0 + 1) * P.wid
  vs_ : σ.vars "vs" = (bagL P.D (i0 + 1)).length
  Pp_ : σ.vars "Pp" = 2 ^ (P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1)))
  shp1_ : σ.vars "shp1" = P.m * (pos (bagL P.D i0) (vertex P.D (i0 + 1)) + 1)
  cbase_ : σ.vars "cbase" = i0 * P.tabs

theorem introCell_run {i0 : ℕ} (hT : TC P B i0 σ)
    (hfc : σ.vars "fc" < 2 ^ (P.m * (bagL P.D (i0 + 1)).length)) :
    ∃ σ', Run B introCell σ σ' (vcost P.m (bagL P.D (i0 + 1)).length + 60) ∧
      σ'.vars "val" = tbv P.I P.kk P.D (i0 + 1) (σ.vars "fc") ∧ σ'.arrs = σ.arrs ∧
      (∀ y, y ∉ SI → σ'.vars y = σ.vars y) ∧ σ'.out = σ.out := by
  have hC := hT.C
  have hiN := hT.iN
  have hl1 := bagL_intro_len P hT.k_
  have hle1 := bagL_len_le P (j := i0 + 1) hiN
  have hb1 := hC.b1
  have hb2 := hC.b2
  have hb5 := hC.b5
  have hb6 := hC.b6
  have hb8 := hC.b8
  have hb10 := hC.b10
  have hlenBG := hC.lenBG
  have hlenTB := hC.lenTB
  have hyl : P.y.length = 2 + 2 * (P.m * P.n) := by
    rw [P.hy.length_eq]; unfold Params.m Params.n; ring
  have hlX := hC.lenX
  have hNw : (i0 + 2) * P.wid ≤ P.N * P.wid := Nat.mul_le_mul_right _ hiN
  have hi2' : (i0 + 2) * P.wid = i0 * P.wid + P.wid + P.wid := by ring
  have hi1' : (i0 + 1) * P.wid = i0 * P.wid + P.wid := by ring
  have hNt : (i0 + 1) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ (by omega)
  have hi1t : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
  have hpt : 2 ^ (P.m * (bagL P.D (i0 + 1)).length) ≤ P.tabs := pow_le_tabs P hle1
  have hfcB : σ.vars "fc" < B := by omega
  have hbl1 : ∀ t < (bagL P.D (i0 + 1)).length, (bagL P.D (i0 + 1))[t]! < P.n :=
    fun t ht => bagL_get_lt P hiN ht
  have r1 : Run B (.assign "e" (V "fc")) σ (σ.setVar "e" (σ.vars "fc")) 2 :=
    (Run.assign (evalB_var hfcB)).mono (by simp [Expr.size])
  have h1 : (bagL P.D (i0 + 1)).length * ((bagL P.D (i0 + 1)).length * P.m + 1) ≤
      P.wid * (P.wid * P.m + 1) :=
    Nat.mul_le_mul hle1 (by have := Nat.mul_le_mul_right P.m hle1; omega)
  have h2 : (bagL P.D (i0 + 1)).length * P.m ≤ P.wid * P.m := Nat.mul_le_mul_right _ hle1
  have hV : VC (σ.arrs "X") P.n P.m P.kk (bagL P.D (i0 + 1)) B (σ.setVar "e" (σ.vars "fc")) := by
    refine ⟨by simp, by simp [hC.n_], by simp [hC.m_], by simp [hC.kk_], by simp [hC.mn_],
      by simp [hC.mask_], by omega, by simpa using hC.XB,
      by omega, by omega, by omega, by omega, ?_, ?_, hbl1, ?_, ?_,
      by omega, by omega, by omega⟩
    · intro t ht
      simpa [hT.off_] using hT.bg t ht
    · simp only [vars_setVar, arrs_setVar, String.reduceEq, if_false]
      rw [hT.off_]; omega
    · simp only [vars_setVar, String.reduceEq, if_false]
      rw [hT.off_]; omega
    · simp [hT.vs_]
  obtain ⟨σ2, r2, hv2, A2, o2⟩ := violCom_run hV (by simp; exact hfcB)
  have hfr : ∀ y, y ∉ SV → y ≠ "e" → σ2.vars y = σ.vars y := by
    intro y hy hne
    rw [A2.2 y hy]
    simp [Env.setVar, hne]
  have he2 : σ2.vars "e" = σ.vars "fc" := by
    rw [A2.2 "e" (by simp [SV, Stt, St2, SD])]; simp [Env.setVar]
  have har : σ2.arrs = σ.arrs := by rw [A2.1]; simp
  have hvi : σ2.vars "vi" = violE P.I P.kk (bagL P.D (i0 + 1)) (σ.vars "fc") := by
    rw [hv2]
    simp only [vars_setVar, if_true]
    exact violN_eq_violE P.hy hC.Xy P.kk _ (fun t ht => hbl1 t ht) _
  have hpl : pos (bagL P.D i0) (vertex P.D (i0 + 1)) ≤ (bagL P.D i0).length := pos_le_length
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  have hfc' : σ.vars "fc" < (2 ^ P.m) ^ ((bagL P.D i0).length + 1) := by
    rw [bpow', ← hl1]; exact hfc
  have hrmlt : rmN (2 ^ P.m) (pos (bagL P.D i0) (vertex P.D (i0 + 1))) (σ.vars "fc") <
      (2 ^ P.m) ^ (bagL P.D i0).length := rmN_lt (by positivity) hfc' hpl
  have hpt0 : (2 ^ P.m) ^ (bagL P.D i0).length ≤ P.tabs := by
    rw [bpow']; exact pow_le_tabs P hlen0
  have hct : i0 * P.tabs + P.tabs ≤ P.N * P.tabs := by
    have : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
    have := Nat.mul_le_mul_right P.tabs (show i0 + 1 ≤ P.N by omega)
    omega
  have hTBv := hT.tb _ hrmlt
  have hTBB : (σ2.arrs "TB").getD (i0 * P.tabs + rmN (2 ^ P.m)
      (pos (bagL P.D i0) (vertex P.D (i0 + 1))) (σ.vars "fc")) 0 < B := by
    rw [har, hTBv]; have := tbv_le_one (I := P.I) (kk := P.kk) (D := P.D)
      (j := i0) (e := rmN (2 ^ P.m) (pos (bagL P.D i0) (vertex P.D (i0 + 1))) (σ.vars "fc"))
    omega
  obtain ⟨σ3, r3, hv3, ha3, hf3, o3⟩ := introTail_run (B := B) σ2 P.m
    (pos (bagL P.D i0) (vertex P.D (i0 + 1))) (σ.vars "fc") (i0 * P.tabs)
    ((hfr "Pp" (by simp [SV, Stt, St2, SD]) (by decide)).trans hT.Pp_)
    ((hfr "shp1" (by simp [SV, Stt, St2, SD]) (by decide)).trans hT.shp1_)
    he2 ((hfr "cbase" (by simp [SV, Stt, St2, SD]) (by decide)).trans hT.cbase_)
    (by rw [har]; omega) hTBB (by omega) (by omega)
    (by have := pow_le_tabs P (s := pos (bagL P.D i0) (vertex P.D (i0 + 1))) (by omega); omega)
    (by
      have h1 := Nat.mul_le_mul_left P.m
        (show pos (bagL P.D i0) (vertex P.D (i0 + 1)) + 1 ≤ P.wid by omega)
      have h2 := Nat.mul_le_mul_left P.m (show P.wid ≤ P.wid + 1 by omega)
      have hb9 := hC.b9
      omega) hfcB (by omega)
    (by rw [hv2]; exact lt_of_le_of_lt (violN_le _ _ _ _ _ _) (by omega))
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by unfold vcost; omega), ?_, ha3.trans har, ?_,
    by rw [o3, o2]; simp⟩
  · rw [hv3, hvi, har, hTBv, tbv_intro hT.k_]
    rfl
  · intro y hy
    have hyS : y ∉ SV := fun h => hy (by simp [SI, h])
    have hye : y ≠ "e" := fun h => hy (by simp [SI, h])
    rw [hf3 y (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> exact hy (by simp [SI, h])), hfr y hyS hye]

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwIntro5` -/

section
/-!
The fill of the table of an introduce node.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- The context survives a fill that keeps the other arrays and the constants. -/
lemma NC.of_agrA {S : List String} {arr : String} {σ0 σ : Env} (h : NC P B σ0)
    (hA : AgrA S arr σ0 σ) (hl : (σ.arrs arr).length = (σ0.arrs arr).length)
    (hS : ∀ y ∈ S, y ∈ SN) (harr : arr = "SZ" ∨ arr = "BG" ∨ arr = "TB") : NC P B σ := by
  have hx : ∀ a, a ≠ arr → σ.arrs a = σ0.arrs a := hA.2
  refine h.transfer (fun y hy => hA.1 y (fun hyS => ?_)) (hx _ ?_) (hx _ ?_) ?_ ?_ ?_
  · have := hS y hyS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [SN, SV, Stt, St2, SD] at this
  · rcases harr with rfl | rfl | rfl <;> decide
  · rcases harr with rfl | rfl | rfl <;> decide
  · rcases harr with rfl | rfl | rfl
    · exact hl
    · rw [hx _ (by decide)]
    · rw [hx _ (by decide)]
  · rcases harr with rfl | rfl | rfl
    · rw [hx _ (by decide)]
    · exact hl
    · rw [hx _ (by decide)]
  · rcases harr with rfl | rfl | rfl
    · rw [hx _ (by decide)]
    · rw [hx _ (by decide)]
    · exact hl

theorem introTB_run {i0 : ℕ} (hT : TC P B i0 σ) (hbs : σ.vars "bs" = (i0 + 1) * P.tabs)
    (hfn : σ.vars "fn" = 2 ^ (P.m * (bagL P.D (i0 + 1)).length)) :
    ∃ σ', Run B (fillLoop "TB" introCell) σ σ'
        ((vcost P.m (bagL P.D (i0 + 1)).length + 60 + 20 + 4) *
          2 ^ (P.m * (bagL P.D (i0 + 1)).length) + 6) ∧
      AgrA ("fc" :: SI) "TB" σ σ' ∧ σ'.out = σ.out ∧
      (σ'.arrs "TB").length = (σ.arrs "TB").length ∧
      RowDesc "TB" ((i0 + 1) * P.tabs) ((2 ^ P.I.days) ^ (bagL P.D (i0 + 1)).length)
        (fun e => tbv P.I P.kk P.D (i0 + 1) e) σ σ' := by
  have hC := hT.C
  have hiN := hT.iN
  have hl1 := bagL_intro_len P hT.k_
  have hle1 := bagL_len_le P (j := i0 + 1) hiN
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  have hb1 := hC.b1
  have hlenTB := hC.lenTB
  have hpt : 2 ^ (P.m * (bagL P.D (i0 + 1)).length) ≤ P.tabs := pow_le_tabs P hle1
  have hpt0 : (2 ^ P.m) ^ (bagL P.D i0).length ≤ P.tabs := by
    rw [bpow']; exact pow_le_tabs P hlen0
  have hNt : (i0 + 2) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ hiN
  have hi2t : (i0 + 2) * P.tabs = (i0 + 1) * P.tabs + P.tabs := by ring
  have hi1t : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
  have hres := fillLoop_run (B := B) "TB" introCell (fun e => tbv P.I P.kk P.D (i0 + 1) e)
    ("fc" :: SI) (vcost P.m (bagL P.D (i0 + 1)).length + 60) (2 ^ (P.m * (bagL P.D (i0 + 1)).length))
    σ hfn (by omega) (by rw [hbs]; omega)
    (fun k => lt_of_le_of_lt tbv_le_one (by omega)) (by simp [SI, SV, Stt, St2, SD])
    (by rw [hbs]; omega) (by
      intro σ' hF hA hlt
      have hC' : NC P B σ' := hC.of_agrA hA hF.1 SI_sub (Or.inr (Or.inr rfl))
      have hS : ∀ y, y ∈ ["off", "vs", "Pp", "shp1", "cbase"] → σ'.vars y = σ.vars y :=
        fun y hy => hA.1 y (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp [SI, SV, Stt, St2, SD])
      have hT' : TC P B i0 σ' :=
        ⟨hC', hiN, hT.k_, fun t ht => by rw [hA.2 "BG" (by decide)]; exact hT.bg t ht,
          fun e he => by
            rw [hF.2, if_neg (by rw [hbs]; omega)]; exact hT.tb e he,
          by rw [hS "off" (by simp)]; exact hT.off_, by rw [hS "vs" (by simp)]; exact hT.vs_,
          by rw [hS "Pp" (by simp)]; exact hT.Pp_, by rw [hS "shp1" (by simp)]; exact hT.shp1_,
          by rw [hS "cbase" (by simp)]; exact hT.cbase_⟩
      obtain ⟨σ'', r, hv, ha, hfr, ho⟩ := introCell_run hT' hlt
      exact ⟨σ'', r, hv, ha, fun y hy => hfr y (fun h => hy (List.mem_cons_of_mem _ h)),
        hfr "fc" (by simp [SI, SV, Stt, St2, SD]), ho⟩)
  obtain ⟨σ', r, hl, hg, hA, ho⟩ := hres
  refine ⟨σ', r, hA, ho, hl, fun k => ?_⟩
  rw [hg k, hbs, bpow]

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwIntro6` -/

section
/-!
The whole program of an introduce node, and its correctness.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- **The program of an introduce node.** -/
def introCom : Com :=
  .seq introHead (.seq (fillLoop "BG" bgPreIntro) (.seq introMid (fillLoop "TB" introCell)))

/-- What an introduce node costs. -/
def introCost (P : Params) : ℕ :=
  (34 * P.wid + 130) + ((20 + 20 + 4) * P.wid + 6) + 100 +
    ((vcost P.m P.wid + 60 + 20 + 4) * P.tabs + 6)

lemma midState_arrs (P : Params) (i0 : ℕ) (σ : Env) {a : String} (ha : a ≠ "SZ") :
    (midState P i0 σ).arrs a = σ.arrs a := by
  simp [midState, ha]

theorem introCom_run {i0 : ℕ} (hC : NC P B σ) (hN : NI P.I P.kk P.D P.wid P.tabs (i0 + 1) σ)
    (hi : σ.vars "i" = i0 + 1) (hiN : i0 + 1 < P.N) (hk : kind P.D (i0 + 1) = 1) :
    ∃ σ', Run B introCom σ σ' (introCost P) ∧ Keep σ σ' ∧
      NI P.I P.kk P.D P.wid P.tabs (i0 + 1 + 1) σ' ∧ σ'.out = σ.out := by
  have hl1 := bagL_intro_len P hk
  have hle1 := bagL_len_le P (j := i0 + 1) hiN
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  obtain ⟨σ3, r3, k3, har3, hc3, hs3, hvx3, hot3, hp3, hcw3, hs13, hiw3, hbs3, hfn3⟩ :=
    introHead_run hC hN hi hiN
  have hQ3 : HQ P B i0 σ3 :=
    ⟨k3.nc hC, hiN, (k3.vars "i" (by simp [SN, SV, Stt, St2, SD])).trans hi, hc3, hs3, hvx3, hp3,
      hcw3, hs13, hiw3, hbs3, hfn3, hk⟩
  have hP3 : HP P B i0 σ3 := ⟨hQ3, hN.of_arrs har3⟩
  obtain ⟨σ4, r4, hA4, o4, hl4, hrow4⟩ := introBG_run hP3
  have k4 : Keep σ3 σ4 := Keep.of_agrA hA4 hl4
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> simp [SN]) (Or.inr (Or.inl rfl)) o4
  have hQ4 : HQ P B i0 σ4 := hQ3.transfer k4 (fun y hy => hA4.1 y (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  obtain ⟨σ5, r5, e5⟩ := introMid_run hQ4
  have k5 : Keep σ4 σ5 := by
    rw [e5]; unfold midState
    exact (((((((Keep.refl σ4).setArr (Or.inl rfl) _ _).setVar (by simp [SN]) _).setVar
      (by simp [SN]) _).setVar (by simp [SN]) _).setVar (by simp [SN]) _).setVar
      (by simp [SN]) _).setVar (by simp [SN]) _ |>.setVar (by simp [SN]) _
  have hBG5 : σ5.arrs "BG" = σ4.arrs "BG" := by rw [e5]; exact midState_arrs P i0 σ4 (by decide)
  have hTB5 : σ5.arrs "TB" = σ.arrs "TB" := by
    rw [e5, midState_arrs P i0 σ4 (by decide), hA4.2 "TB" (by decide), har3]
  have hSZ5 : σ5.arrs "SZ" = (σ.arrs "SZ").set (i0 + 1) ((bagL P.D i0).length + 1) := by
    rw [e5]; simp [midState, hA4.2 "SZ" (by decide), har3]
  have hT5 : TC P B i0 σ5 := by
    refine ⟨k5.nc hQ4.C, hiN, hk, fun t ht => ?_, fun e he => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hBG5, hrow4, if_pos (by omega)]
      simp
    · rw [hTB5]; exact hN.tb i0 (by omega) e he
    · rw [e5]; simp [midState]
    · rw [e5]; simp [midState, hl1]
    · rw [e5]; simp [midState]
    · rw [e5]; simp [midState]
    · rw [e5]; simp [midState]
  have hbs5 : σ5.vars "bs" = (i0 + 1) * P.tabs := by rw [e5]; simp [midState]
  have hfn5 : σ5.vars "fn" = 2 ^ (P.m * (bagL P.D (i0 + 1)).length) := by
    rw [e5, hl1]; simp [midState]
  obtain ⟨σ6, r6, hA6, o6, hl6, hrow6⟩ := introTB_run hT5 hbs5 hfn5
  have k6 : Keep σ5 σ6 := Keep.of_agrA hA6 hl6 SI_sub (Or.inr (Or.inr rfl)) o6
  have hpt : 2 ^ (P.m * (bagL P.D (i0 + 1)).length) ≤ P.tabs := pow_le_tabs P hle1
  have hK : (vcost P.m (bagL P.D (i0 + 1)).length + 60 + 20 + 4) *
      2 ^ (P.m * (bagL P.D (i0 + 1)).length) ≤ (vcost P.m P.wid + 60 + 20 + 4) * P.tabs :=
    Nat.mul_le_mul (by have := vcost_mono P.m hle1; omega) hpt
  refine ⟨σ6, (r3.seq (r4.seq (r5.seq r6))).mono (by unfold introCost; omega),
    k3.trans (k4.trans (k5.trans k6)), ?_, by rw [o6, e5]; simp [midState, o4, k3.out]⟩
  refine NI_next (i := i0 + 1) (σ0 := σ) hN (fun j hj => bagL_len_le P (by omega))
    (fun s hs => by rw [bpow]; exact pow_le_tabs P hs) ?_ ?_ ?_
  · intro k
    rw [hA6.2 "SZ" (by decide), hSZ5, getD_set']
    by_cases hk1 : k = i0 + 1
    · subst hk1
      rw [if_pos ⟨rfl, by have := hC.lenSZ; omega⟩, if_pos (by omega), hl1]
    · rw [if_neg (by omega), if_neg (by omega)]
  · intro k
    rw [hA6.2 "BG" (by decide), hBG5, hrow4, har3]
  · intro k
    rw [hrow6, hTB5]

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwForget1` -/

section
/-!
The program of a forget node: the head and the row of the bag.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- The vertex forgotten is in the child's bag, at the position `pos`. -/
lemma bagL_forget_facts (P : Params) {i : ℕ} (hi : i + 1 < P.N) (hk : kind P.D (i + 1) = 2) :
    pos (bagL P.D i) (vertex P.D (i + 1)) < (bagL P.D i).length := by
  obtain ⟨hp, hm⟩ := bagL_spec P.hD i (by have : P.N = nodeCount P.D := rfl; omega)
  have hshape := P.hD.shape (i + 1) hi
  rcases hshape with h0 | ⟨_, h1, _⟩ | ⟨_, _, hv', hin⟩ | ⟨_, h3, _⟩
  · omega
  · omega
  · have hvl : vertex P.D (i + 1) ∈ bagL P.D i := (hm _).2 ⟨hv', by simpa using hin hv'⟩
    obtain ⟨h, -, -⟩ := getElem_pos hp hvl
    exact h
  · omega

/-- The length of the bag of a forget node. -/
lemma bagL_forget_len (P : Params) {i : ℕ} (hi : i + 1 < P.N) (hk : kind P.D (i + 1) = 2) :
    (bagL P.D (i + 1)).length = (bagL P.D i).length - 1 := by
  have := bagL_forget_facts P hi hk
  rw [bagL_forget hk, List.length_eraseIdx_of_lt this]

/-- The sizes a forget node needs. -/
def forgetTail1 : Com := seqs
  [ .assign "s1" (sub (V "s") (L 1)),
    .assign "iw" (mul (V "i") (V "w1")),
    .assign "bs" (V "iw"),
    .assign "fn" (V "s1") ]

/-- The head of the program of a forget node. -/
def forgetHead : Com := .seq recCom (.seq posLoop forgetTail1)

theorem forgetHead_run {i0 : ℕ} (hC : NC P B σ)
    (hN : NI P.I P.kk P.D P.wid P.tabs (i0 + 1) σ) (hi : σ.vars "i" = i0 + 1) (hiN : i0 + 1 < P.N) :
    ∃ σ1, Run B forgetHead σ σ1 (34 * P.wid + 130) ∧ Keep σ σ1 ∧ σ1.arrs = σ.arrs ∧
      σ1.vars "c" = i0 ∧ σ1.vars "s" = (bagL P.D i0).length ∧
      σ1.vars "vx" = vertex P.D (i0 + 1) ∧ σ1.vars "ot" = other P.D (i0 + 1) ∧
      σ1.vars "p" = pos (bagL P.D i0) (vertex P.D (i0 + 1)) ∧ σ1.vars "cw" = i0 * P.wid ∧
      σ1.vars "s1" = (bagL P.D i0).length - 1 ∧ σ1.vars "iw" = (i0 + 1) * P.wid ∧
      σ1.vars "bs" = (i0 + 1) * P.wid ∧ σ1.vars "fn" = (bagL P.D i0).length - 1 := by
  have hBpos : 0 < B := by have := hC.b3; omega
  have hlD : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have hb2 := hC.b2
  have hb3 := hC.b3
  have hw1 := hC.w1_
  have hNw : ∀ j, j ≤ P.N → j * P.wid ≤ P.N * P.wid := fun j hj => Nat.mul_le_mul_right _ hj
  have hi2 : (i0 + 2) * P.wid ≤ P.N * P.wid := hNw _ (by omega)
  have hi2' : (i0 + 2) * P.wid = i0 * P.wid + P.wid + P.wid := by ring
  have hi1' : (i0 + 1) * P.wid = i0 * P.wid + P.wid := by ring
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  have hSc : (σ.arrs "SZ").getD i0 0 < B := by
    rw [hN.sz i0 (by omega)]; omega
  obtain ⟨σ1, r1, hc1, hvx1, hot1, hs1, hcw1, hp1, A1, o1⟩ := recCom_run (B := B) (σ := σ)
    (i := i0 + 1) (N := P.N) hi hiN hC.lenSZ (by have := hC.lenO; omega)
    (hC.O_lt (by omega) (by omega)) (hC.O_lt (by omega) (by omega))
    (by simpa using hSc) (by have := hC.b3; omega)
    (by rw [hw1, Nat.add_sub_cancel]; have := hNw i0 (by omega); omega)
    (by rw [hw1]; have := hNw 1 (by omega); omega)
  have hvx' : σ1.vars "vx" = vertex P.D (i0 + 1) := by rw [hvx1, vertex_eq P hC hiN]
  have hot' : σ1.vars "ot" = other P.D (i0 + 1) := by rw [hot1, other_eq P hC hiN]
  have hs' : σ1.vars "s" = (bagL P.D i0).length := by
    rw [hs1, Nat.add_sub_cancel, hN.sz i0 (by omega)]
  have hcw' : σ1.vars "cw" = i0 * P.wid := by rw [hcw1, Nat.add_sub_cancel, hw1]
  have hvxB : σ1.vars "vx" < B := by rw [hvx1]; exact hC.O_lt (by omega) (by omega)
  obtain ⟨σ2, r2, hp2, A2, o2⟩ := posLoop_run (B := B) (σ0 := σ1) (f := fun t => (bagL P.D i0)[t]!)
    (s0 := (bagL P.D i0).length) (cw0 := i0 * P.wid) hs' hcw' hp1
    (fun t ht => by rw [A1.1]; exact hN.bg i0 (by omega) t ht)
    (by rw [A1.1]; have := hC.lenBG; omega)
    (fun t => by have := bagL_get_le P (j := i0) (by omega) t; have := hC.b8; omega) hvxB
    (by have := bagL_len_le P (j := i0) (by omega); omega)
  have hs2 : σ2.vars "s" = (bagL P.D i0).length := by rw [A2.2 "s" (by simp), hs']
  have hi2v : σ2.vars "i" = i0 + 1 := by rw [A2.2 "i" (by simp), A1.2 "i" (by simp [SR]), hi]
  have hw2 : σ2.vars "w1" = P.wid := by rw [A2.2 "w1" (by simp), A1.2 "w1" (by simp [SR]), hw1]
  have hp' : σ2.vars "p" = pos (bagL P.D i0) (vertex P.D (i0 + 1)) := by
    rw [hp2, pos_eq_sum, hvx']
  obtain ⟨σ3, r3, e3⟩ : ∃ σ3, Run B forgetTail1 σ2 σ3 40 ∧ σ3 =
      (((σ2.setVar "s1" ((bagL P.D i0).length - 1)).setVar "iw" ((i0 + 1) * P.wid)).setVar "bs"
        ((i0 + 1) * P.wid)).setVar "fn" ((bagL P.D i0).length - 1) := by
    unfold forgetTail1 seqs
    run_vcg
    all_goals try (nrmA; simp only [hs2, hi2v, hw2]; omega)
    all_goals try (nrmA; omega)
    all_goals (try nrmA)
    all_goals (try simp only [hs2, hi2v, hw2])
  have hv3 : ∀ y, y ∉ ["s1", "iw", "bs", "fn"] → σ3.vars y = σ2.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [e3]; simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]
  have k1 := Keep.of_agr A1 SR_sub o1
  have k2 := Keep.of_agr A2 (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [SN]) o2
  have k3 : Keep σ2 σ3 := by
    rw [e3]
    exact ((((Keep.refl σ2).setVar (by simp [SN]) _).setVar (by simp [SN]) _).setVar
      (by simp [SN]) _).setVar (by simp [SN]) _
  have har : σ3.arrs = σ.arrs := by rw [e3]; simp [A2.1, A1.1]
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), k1.trans (k2.trans k3), har, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv3 "c" (by simp), A2.2 "c" (by simp), hc1]; simp
  · rw [hv3 "s" (by simp), hs2]
  · rw [hv3 "vx" (by simp), A2.2 "vx" (by simp), hvx']
  · rw [hv3 "ot" (by simp), A2.2 "ot" (by simp), hot']
  · rw [hv3 "p" (by simp), hp']
  · rw [hv3 "cw" (by simp), A2.2 "cw" (by simp), hcw']
  · rw [e3]; simp [Env.setVar, hs2]
  · rw [e3]; simp [Env.setVar]
  · rw [e3]; simp [Env.setVar]
  · rw [e3]; simp [Env.setVar, hs2]


/-! ### The row of the bag -/

/-- The value of the cell of the new bag: the child's entry at or after the position. -/
def bgPreForget : Com :=
  .ite (.lt (V "fc") (V "p")) (.assign "val" (G "BG" (add (V "cw") (V "fc"))))
    (.assign "val" (G "BG" (add (add (V "cw") (V "fc")) (L 1))))

theorem bgPreForget_run (σ : Env) (l : List ℕ) (p cw : ℕ) (hp : σ.vars "p" = p)
    (hcw : σ.vars "cw" = cw) (hpB : p < B)
    (hrd : ∀ t < l.length, (σ.arrs "BG").getD (cw + t) 0 = l[t]!)
    (hf : σ.vars "fc" + 1 < l.length) (hlen : cw + l.length ≤ (σ.arrs "BG").length)
    (hbd : ∀ t : ℕ, l[t]! < B) (hb : cw + l.length + 8 < B) :
    ∃ σ', Run B bgPreForget σ σ' 20 ∧
      σ'.vars "val" = (l.eraseIdx p)[σ.vars "fc"]! ∧ σ'.arrs = σ.arrs ∧
      (∀ y, y ≠ "val" → σ'.vars y = σ.vars y) ∧ σ'.out = σ.out := by
  have hrd' : ∀ t < l.length, (σ.arrs "BG").getD (σ.vars "cw" + t) 0 = l[t]! := by
    rw [hcw]; exact hrd
  have hers := getElem!_eraseIdx l p (σ.vars "fc")
  unfold bgPreForget
  run_vcg
  all_goals first
    | (refine ⟨?_, rfl, fun y hy => by simp [Env.setVar, hy], rfl⟩
       nrmA
       first
         | rw [hers, if_pos (by omega), hrd' _ (by omega)]
         | rw [hers, if_neg (by omega),
             show σ.vars "cw" + σ.vars "fc" + 1 = σ.vars "cw" + (σ.vars "fc" + 1) by omega,
             hrd' _ (by omega)])
    | omega
    | (rw [hrd' _ (by omega)]; exact hbd _)
    | (rw [show σ.vars "cw" + σ.vars "fc" + 1 = σ.vars "cw" + (σ.vars "fc" + 1) by omega,
         hrd' _ (by omega)]
       exact hbd _)

/-- **The state after the head of a forget node**, without the description of the arrays. -/
structure HQf (P : Params) (B : ℕ) (i0 : ℕ) (σ : Env) : Prop where
  C : NC P B σ
  iN : i0 + 1 < P.N
  i_ : σ.vars "i" = i0 + 1
  c_ : σ.vars "c" = i0
  s_ : σ.vars "s" = (bagL P.D i0).length
  vx_ : σ.vars "vx" = vertex P.D (i0 + 1)
  p_ : σ.vars "p" = pos (bagL P.D i0) (vertex P.D (i0 + 1))
  cw_ : σ.vars "cw" = i0 * P.wid
  s1_ : σ.vars "s1" = (bagL P.D i0).length - 1
  iw_ : σ.vars "iw" = (i0 + 1) * P.wid
  bs_ : σ.vars "bs" = (i0 + 1) * P.wid
  fn_ : σ.vars "fn" = (bagL P.D i0).length - 1
  k_ : kind P.D (i0 + 1) = 2

/-- The state after the head of a forget node. -/
structure HPf (P : Params) (B : ℕ) (i0 : ℕ) (σ : Env) : Prop extends HQf P B i0 σ where
  N : NI P.I P.kk P.D P.wid P.tabs (i0 + 1) σ

lemma HQf.transfer {i0 : ℕ} {σ σ' : Env} (h : HQf P B i0 σ) (k : Keep σ σ')
    (hv : ∀ y ∈ ["i", "c", "s", "vx", "p", "cw", "s1", "iw", "bs", "fn"],
      σ'.vars y = σ.vars y) : HQf P B i0 σ' :=
  ⟨k.nc h.C, h.iN, by rw [hv "i" (by simp)]; exact h.i_, by rw [hv "c" (by simp)]; exact h.c_,
    by rw [hv "s" (by simp)]; exact h.s_, by rw [hv "vx" (by simp)]; exact h.vx_,
    by rw [hv "p" (by simp)]; exact h.p_, by rw [hv "cw" (by simp)]; exact h.cw_,
    by rw [hv "s1" (by simp)]; exact h.s1_, by rw [hv "iw" (by simp)]; exact h.iw_,
    by rw [hv "bs" (by simp)]; exact h.bs_, by rw [hv "fn" (by simp)]; exact h.fn_, h.k_⟩

theorem forgetBG_run {i0 : ℕ} (h : HPf P B i0 σ) :
    ∃ σ4, Run B (fillLoop "BG" bgPreForget) σ σ4
        ((20 + 20 + 4) * ((bagL P.D i0).length - 1) + 6) ∧
      AgrA ["fc", "val"] "BG" σ σ4 ∧ σ4.out = σ.out ∧
      (σ4.arrs "BG").length = (σ.arrs "BG").length ∧
      RowDesc "BG" ((i0 + 1) * P.wid) (bagL P.D (i0 + 1)).length
        (fun t => (bagL P.D (i0 + 1))[t]!) σ σ4 := by
  have hC := h.C
  have hiN := h.iN
  have hl1 := bagL_forget_len P h.iN h.k_
  have hle1 := bagL_len_le P (j := i0 + 1) h.iN
  have hle0 := bagL_len_le P (j := i0) (by omega)
  have hb2 := hC.b2
  have hb3 := hC.b3
  have hb8 := hC.b8
  have hBpos : 0 < B := by omega
  have hNw : (i0 + 2) * P.wid ≤ P.N * P.wid := Nat.mul_le_mul_right _ h.iN
  have hi2' : (i0 + 2) * P.wid = i0 * P.wid + P.wid + P.wid := by ring
  have hi1' : (i0 + 1) * P.wid = i0 * P.wid + P.wid := by ring
  have hlenBG := hC.lenBG
  have hres := fillLoop_run (B := B) "BG" bgPreForget (fun t => (bagL P.D (i0 + 1))[t]!)
    ["fc", "val"] 20 ((bagL P.D i0).length - 1) σ h.fn_ (by omega)
    (by rw [h.bs_]; omega) (fun t => by
      have := bagL_get_le P (j := i0 + 1) h.iN t; omega) (by simp) (by rw [h.bs_]; omega) (by
    intro σ' hF hA hlt
    have e1 : σ'.vars "p" = σ.vars "p" := hA.1 "p" (by simp)
    have e3 : σ'.vars "cw" = σ.vars "cw" := hA.1 "cw" (by simp)
    have hbsl : σ.vars "bs" = (i0 + 1) * P.wid := h.bs_
    obtain ⟨σ'', r, hv, ha, hfr, ho⟩ := bgPreForget_run (B := B) σ' (bagL P.D i0)
      (pos (bagL P.D i0) (vertex P.D (i0 + 1))) (i0 * P.wid)
      (by rw [e1, h.p_]) (by rw [e3, h.cw_])
      (by have : pos (bagL P.D i0) (vertex P.D (i0 + 1)) ≤ (bagL P.D i0).length := pos_le_length
          omega)
      (fun t ht => by
        rw [hF.2, if_neg (by rw [hbsl]; omega)]
        exact h.N.bg i0 (by omega) t ht) (by omega)
      (by rw [hF.1]; omega)
      (fun t => by have := bagL_get_le P (j := i0) (by omega) t; omega) (by omega)
    refine ⟨σ'', r, ?_, by rw [ha], fun y hy => hfr y (by intro e; exact hy (by simp [e])),
      hfr "fc" (by decide), ho⟩
    rw [hv, ← bagL_forget h.k_])
  obtain ⟨σ4, r, hl, hg, hA, ho⟩ := hres
  refine ⟨σ4, r, hA, ho, hl, fun k => ?_⟩
  rw [hg k, h.bs_, hl1]

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwForget2` -/

section
/-!
The program of a forget node: the size and the parameters of the table, and the table's loop
over the forgotten digit.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- Store the size, and set the parameters of the fill of the table. -/
def forgetMid : Com := seqs
  [ .store "SZ" (V "i") (V "s1"),
    .assign "Pp" (.bin .shiftl (L 1) (mul (V "m") (V "p"))),
    .assign "shp1" (mul (V "m") (V "p")),
    .assign "cbase" (mul (V "c") (V "Tm")),
    .assign "bs" (mul (V "i") (V "Tm")),
    .assign "fn" (.bin .shiftl (L 1) (mul (V "m") (V "s1"))) ]

/-- The state after `forgetMid`. -/
def midStateF (P : Params) (i0 : ℕ) (σ : Env) : Env :=
  ((((σ.setArr "SZ" (i0 + 1) ((bagL P.D i0).length - 1)).setVar "Pp"
    (2 ^ (P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1))))).setVar "shp1"
    (P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1)))).setVar "cbase" (i0 * P.tabs)).setVar
    "bs" ((i0 + 1) * P.tabs) |>.setVar "fn" (2 ^ (P.m * ((bagL P.D i0).length - 1)))

theorem forgetMid_run {i0 : ℕ} (h : HQf P B i0 σ) :
    ∃ σ', Run B forgetMid σ σ' 100 ∧ σ' = midStateF P i0 σ := by
  have hC := h.C
  have hiN := h.iN
  have hl1 := bagL_forget_len P h.iN h.k_
  have hpl := bagL_forget_facts P h.iN h.k_
  have hle0 := bagL_len_le P (j := i0) (by omega)
  have hb1 := hC.b1
  have hb9 := hC.b9
  have hb3 := hC.b3
  have hb2 := hC.b2
  have hlenSZ := hC.lenSZ
  have hNt : (i0 + 2) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ h.iN
  have hi2 : (i0 + 2) * P.tabs = i0 * P.tabs + P.tabs + P.tabs := by ring
  have hi1 : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
  have hp1 : 2 ^ (P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1))) ≤ P.tabs :=
    pow_le_tabs P (by omega)
  have hp2 : 2 ^ (P.m * ((bagL P.D i0).length - 1)) ≤ P.tabs := pow_le_tabs P (by omega)
  have hmp : P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1)) ≤ P.m * P.wid :=
    Nat.mul_le_mul_left _ (by omega)
  have hms1 : P.m * ((bagL P.D i0).length - 1) ≤ P.m * P.wid := Nat.mul_le_mul_left _ (by omega)
  have hmw : P.m * (P.wid + 1) = P.m * P.wid + P.m := by ring
  have hct : i0 * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ (by omega)
  unfold forgetMid seqs
  run_vcg
  all_goals (try nrmA)
  all_goals try (first | omega | (simp only [h.i_, h.s1_, hC.m_, h.p_, hC.Tm_, h.c_, one_mul]; omega))
  all_goals (try simp only [midStateF, h.i_, h.s1_, hC.m_, h.p_, hC.Tm_, h.c_, one_mul])

/-! ### The loop over the forgotten digit -/

lemma lor_le_one {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : Nat.lor a b ≤ 1 := by
  interval_cases a <;> interval_cases b <;> decide

/-- **The fold of `or` over the digits is the existence of a one.** -/
lemma or_fold (N : ℕ) (T : ℕ → ℕ) (hT : ∀ j < N, T j ≤ 1) : ∀ M ≤ N,
    (List.range M).foldl (fun a j => if j < N then Nat.lor a (T j) else a) 0 =
      if ∃ j < M, T j = 1 then 1 else 0
  | 0, _ => by simp
  | M + 1, hM => by
    rw [List.range_succ, List.foldl_append, or_fold N T hT M (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, if_pos (show M < N by omega)]
    have h1 := hT M (by omega)
    by_cases hex : ∃ j < M, T j = 1
    · have hex' : ∃ j < M + 1, T j = 1 := by
        obtain ⟨j, hj, e⟩ := hex; exact ⟨j, by omega, e⟩
      rw [if_pos hex, if_pos hex']
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h | h <;> simp [h]
    · rw [if_neg hex]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h | h
      · have : ¬ ∃ j < M + 1, T j = 1 := by
          rintro ⟨j, hj, e⟩
          by_cases hjm : j < M
          · exact hex ⟨j, hjm, e⟩
          · have : j = M := by omega
            subst this; omega
        rw [if_neg this]; simp [h]
      · rw [if_pos ⟨M, by omega, h⟩]; simp [h]

/-- One step of the loop over the forgotten digit. -/
def forgetBody : Com :=
  .seq (.assign "ix" (add (add (V "lo") (mul (V "so") (V "Pp"))) (V "hi")))
    (.assign "ac" (.bin .or (V "ac") (G "TB" (add (V "cbase") (V "ix")))))

theorem forgetBody_run (σ : Env)
    (hidx : σ.vars "cbase" + (σ.vars "lo" + σ.vars "so" * σ.vars "Pp" + σ.vars "hi") <
      (σ.arrs "TB").length)
    (hixB : σ.vars "cbase" + (σ.vars "lo" + σ.vars "so" * σ.vars "Pp" + σ.vars "hi") < B)
    (hac : σ.vars "ac" ≤ 1)
    (hT : (σ.arrs "TB").getD (σ.vars "cbase" +
      (σ.vars "lo" + σ.vars "so" * σ.vars "Pp" + σ.vars "hi")) 0 ≤ 1) (hB : 2 < B)
    (hso : σ.vars "so" < B) (hPp : σ.vars "Pp" < B) :
    ∃ σ', Run B forgetBody σ σ' 30 ∧
      σ'.vars "ac" = Nat.lor (σ.vars "ac") ((σ.arrs "TB").getD (σ.vars "cbase" +
        (σ.vars "lo" + σ.vars "so" * σ.vars "Pp" + σ.vars "hi")) 0) ∧
      Agr ["ix", "ac"] σ σ' ∧ σ'.vars "so" = σ.vars "so" ∧ σ'.out = σ.out := by
  have hlor := lor_le_one hac hT
  unfold forgetBody
  run_vcg
  all_goals try (nrmA; first | omega | exact lt_of_le_of_lt hlor (by omega))
  refine ⟨?_, ⟨rfl, fun y hy => ?_⟩, ?_, rfl⟩
  · nrmA
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [Env.setVar, hy.1, hy.2]
  · nrmA

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwForget3` -/

section
/-!
The cell of the table of a forget node.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- **The table entry of a forget node**, as a number. -/
lemma tbv_forget {I : Lax117284.Scheduling.Instance} {kk : ℕ} {D : List ℕ} {i e : ℕ}
    (hk : kind D (i + 1) = 2) :
    tbv I kk D (i + 1) e = if ∃ S < 2 ^ I.days,
      tbv I kk D i (insN (2 ^ I.days) (pos (bagL D i) (vertex D (i + 1))) S e) = 1 then 1 else 0 := by
  by_cases h : ∃ S < 2 ^ I.days, tbv I kk D i (insN (2 ^ I.days) (pos (bagL D i) (vertex D (i + 1))) S e) = 1
  · rw [if_pos h]
    obtain ⟨S, hS, hT⟩ := h
    refine tbv_one ((TB_forget hk).2 ⟨S, hS, ?_⟩)
    by_contra hn
    rw [tbv_zero hn] at hT; omega
  · rw [if_neg h]
    refine tbv_zero fun hTB => h ?_
    obtain ⟨S, hS, hT⟩ := (TB_forget hk).1 hTB
    exact ⟨S, hS, tbv_one hT⟩

/-- The loop over the forgotten digit: the `or` of the table entries of the child. -/
def forgetOr : Com := fLoop "so" "bb" forgetBody

/-- The scalars the loop writes. -/
def SO : List String := ["so", "ix", "ac"]

theorem forgetOr_run (σ0 : Env) (N cb : ℕ) (hbb : σ0.vars "bb" = N) (hNB : N + 1 < B)
    (hcb : σ0.vars "cbase" = cb) (hac : σ0.vars "ac" ≤ 1)
    (hidx : ∀ j < N, cb + (σ0.vars "lo" + j * σ0.vars "Pp" + σ0.vars "hi") <
      (σ0.arrs "TB").length)
    (hixB : ∀ j < N, cb + (σ0.vars "lo" + j * σ0.vars "Pp" + σ0.vars "hi") < B)
    (hT : ∀ j < N, (σ0.arrs "TB").getD (cb + (σ0.vars "lo" + j * σ0.vars "Pp" + σ0.vars "hi")) 0 ≤ 1)
    (hB : 2 < B) (hPp : σ0.vars "Pp" < B) :
    ∃ σ', Run B forgetOr σ0 σ' ((30 + 10 + 4) * N + 6) ∧
      σ'.vars "ac" = (List.range N).foldl (fun a j => if j < N then Nat.lor a
        ((σ0.arrs "TB").getD (cb + (σ0.vars "lo" + j * σ0.vars "Pp" + σ0.vars "hi")) 0) else a)
        (σ0.vars "ac") ∧ Agr SO σ0 σ' ∧ σ'.out = σ0.out := by
  have hf := fLoop_spec (B := B) "so" "bb" "ac" forgetBody SO
    (fun j a => if j < N then Nat.lor a
      ((σ0.arrs "TB").getD (cb + (σ0.vars "lo" + j * σ0.vars "Pp" + σ0.vars "hi")) 0) else a)
    (fun _ a => a ≤ 1) 30 N σ0 (by simp [SO]) (by simp [SO]) (by decide) hbb hNB hac
    (fun j a h => by
      by_cases hj : j < N
      · simp only [hj, if_true]
        exact lor_le_one h (hT j hj) 
      · simp only [hj, if_false]; exact h) (by
      intro σ hA hlt hQ
      have hfr : ∀ y, y ∉ SO → σ.vars y = σ0.vars y := hA.2
      have e1 : σ.vars "lo" = σ0.vars "lo" := hfr "lo" (by simp [SO])
      have e2 : σ.vars "hi" = σ0.vars "hi" := hfr "hi" (by simp [SO])
      have e3 : σ.vars "Pp" = σ0.vars "Pp" := hfr "Pp" (by simp [SO])
      have e4 : σ.vars "cbase" = cb := by rw [hfr "cbase" (by simp [SO]), hcb]
      have e5 : σ.arrs "TB" = σ0.arrs "TB" := by rw [hA.1]
      have hlt' : σ.vars "so" < N := hlt
      obtain ⟨σ', r, hv, hA', hso, ho⟩ := forgetBody_run (B := B) σ
        (by rw [e1, e2, e3, e4, e5]; exact hidx _ hlt') (by rw [e1, e2, e3, e4]; exact hixB _ hlt')
        hQ (by rw [e1, e2, e3, e4, e5]; exact hT _ hlt') hB (by omega) (by rw [e3]; exact hPp)
      refine ⟨σ', r, ?_, agr_comp (S := SO) hA hA' (by intro x hx; exact hx)
        (by intro x hx; simp at hx; simp [SO]; tauto), hso, ho⟩
      rw [hv, e1, e2, e3, e4, e5, if_pos hlt'])
  obtain ⟨σ', r, hv, hA, ho⟩ := hf
  exact ⟨σ', r, hv, hA, ho⟩

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwForget4` -/

section
/-!
The cell of the table of a forget node, continued: the preparation and the whole cell.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- The preparation of a cell of a forget node: the low part, the high part, the accumulator. -/
def forgetPre : Com := seqs
  [ .assign "e" (V "fc"),
    .assign "lo" (.bin .and (V "e") (sub (V "Pp") (L 1))),
    .assign "hi" (mul (.bin .shiftr (V "e") (V "shp1")) (mul (V "Pp") (V "bb"))),
    .assign "ac" (L 0) ]

theorem forgetPre_run (σ : Env) (m p fc : ℕ) (hPp : σ.vars "Pp" = 2 ^ (m * p))
    (hsh : σ.vars "shp1" = m * p) (hfc : σ.vars "fc" = fc) (hbb : σ.vars "bb" = 2 ^ m)
    (hfcB : fc < B) (hPpB : 2 ^ (m * p) < B) (hshB : m * p < B)
    (hPq : 2 ^ (m * p) * 2 ^ m < B) (hhiB : fc / 2 ^ (m * p) * (2 ^ (m * p) * 2 ^ m) < B)
    (hmB : 2 ^ m < B) (h0 : 2 < B) :
    ∃ σ1, Run B forgetPre σ σ1 60 ∧ σ1 =
      (((σ.setVar "e" fc).setVar "lo" (Nat.land fc (2 ^ (m * p) - 1))).setVar "hi"
        (fc / 2 ^ (m * p) * (2 ^ (m * p) * 2 ^ m))).setVar "ac" 0 := by
  have hlo : Nat.land fc (2 ^ (m * p) - 1) < B := lt_of_le_of_lt Nat.and_le_left hfcB
  have hhi : fc / 2 ^ (m * p) < B := lt_of_le_of_lt (Nat.div_le_self _ _) hfcB
  unfold forgetPre seqs
  run_vcg
  all_goals (try nrmA)
  all_goals try (first | omega | (simp only [hPp, hsh, hfc, hbb]; first | omega | exact hlo | exact hhi | exact lt_of_le_of_lt (by omega) hPpB))
  all_goals (try simp only [hPp, hsh, hfc, hbb])

/-- The cell of the table of a forget node. -/
def forgetCell : Com := .seq forgetPre (.seq forgetOr (.assign "val" (V "ac")))

/-- The scalars a forget cell writes. -/
def SF : List String := ["e", "lo", "hi", "ac", "so", "ix", "val"]

lemma SF_sub : ∀ y ∈ "fc" :: SF, y ∈ SN := by
  intro y hy
  simp only [SF, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [SN]

/-- **The context of a cell of the table of a forget node.** -/
structure TCf (P : Params) (B : ℕ) (i0 : ℕ) (σ : Env) : Prop where
  C : NC P B σ
  iN : i0 + 1 < P.N
  k_ : kind P.D (i0 + 1) = 2
  tb : ∀ e < (2 ^ P.m) ^ (bagL P.D i0).length,
    (σ.arrs "TB").getD (i0 * P.tabs + e) 0 = tbv P.I P.kk P.D i0 e
  Pp_ : σ.vars "Pp" = 2 ^ (P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1)))
  shp1_ : σ.vars "shp1" = P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1))
  cbase_ : σ.vars "cbase" = i0 * P.tabs

/-- The number the table of the child is asked at, in the shape the machine computes it. -/
lemma insAt_eq (m p j e : ℕ) :
    Nat.land e (2 ^ (m * p) - 1) + j * 2 ^ (m * p) + e / 2 ^ (m * p) * (2 ^ (m * p) * 2 ^ m) =
      insN (2 ^ m) p j e := by
  have h : 2 ^ (m * p) * 2 ^ m = 2 ^ (m * (p + 1)) := by rw [← pow_add, Nat.mul_succ]
  rw [insN_shift, h]

theorem forgetCell_run {i0 : ℕ} (hT : TCf P B i0 σ)
    (hfc : σ.vars "fc" < 2 ^ (P.m * ((bagL P.D i0).length - 1))) :
    ∃ σ', Run B forgetCell σ σ' (44 * 2 ^ P.m + 130) ∧
      σ'.vars "val" = tbv P.I P.kk P.D (i0 + 1) (σ.vars "fc") ∧ σ'.arrs = σ.arrs ∧
      (∀ y, y ∉ SF → σ'.vars y = σ.vars y) ∧ σ'.out = σ.out := by
  have hC := hT.C
  have hiN := hT.iN
  have hpl := bagL_forget_facts P hiN hT.k_
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  have hb1 := hC.b1
  have hb9 := hC.b9
  have hb10 := hC.b10
  have hlenTB := hC.lenTB
  set p := pos (bagL P.D i0) (vertex P.D (i0 + 1)) with hpdef
  set len0 := (bagL P.D i0).length with hlen0def
  have hfc' : σ.vars "fc" < (2 ^ P.m) ^ (len0 - 1) := by rw [bpow']; exact hfc
  have hptab : 2 ^ (P.m * len0) ≤ P.tabs := pow_le_tabs P hlen0
  have hpow1 : (2 ^ P.m) ^ len0 ≤ P.tabs := by rw [bpow']; exact hptab
  have hpow2 : (2 ^ P.m) ^ (len0 - 1) ≤ P.tabs := by
    rw [bpow']; exact pow_le_tabs P (by omega)
  have hct : i0 * P.tabs + P.tabs ≤ P.N * P.tabs := by
    have : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
    have := Nat.mul_le_mul_right P.tabs (show i0 + 1 ≤ P.N by omega)
    omega
  -- the numbers the child's table is asked at
  have hins : ∀ j < 2 ^ P.m, insN (2 ^ P.m) p j (σ.vars "fc") < (2 ^ P.m) ^ len0 := by
    intro j hj
    have := insN_lt (b := 2 ^ P.m) (by positivity) (s := len0 - 1) (p := p) (S := j)
      (e := σ.vars "fc") hfc' hj (by omega)
    rwa [Nat.sub_add_cancel (by omega)] at this
  have hPq : 2 ^ (P.m * p) * 2 ^ P.m ≤ P.tabs := by
    rw [← pow_add, ← Nat.mul_succ]; exact pow_le_tabs P (by omega)
  have hPp' : 2 ^ (P.m * p) ≤ P.tabs := pow_le_tabs P (by omega)
  have hmp : P.m * p ≤ P.m * P.wid := Nat.mul_le_mul_left _ (by omega)
  have hmw : P.m * (P.wid + 1) = P.m * P.wid + P.m := by ring
  have hfcB : σ.vars "fc" < B := by omega
  have hins0 := hins 0 (by positivity)
  have hins0' := insAt_eq P.m p 0 (σ.vars "fc")
  have hBpos : 0 < B := by omega
  obtain ⟨σ1, r1, e1⟩ := forgetPre_run (B := B) σ P.m p (σ.vars "fc") hT.Pp_ hT.shp1_ rfl hC.bb_
    hfcB (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hlo1 : σ1.vars "lo" = Nat.land (σ.vars "fc") (2 ^ (P.m * p) - 1) := by
    rw [e1]; simp [Env.setVar]
  have hhi1 : σ1.vars "hi" = σ.vars "fc" / 2 ^ (P.m * p) * (2 ^ (P.m * p) * 2 ^ P.m) := by
    rw [e1]; simp [Env.setVar]
  have hPp1 : σ1.vars "Pp" = 2 ^ (P.m * p) := by rw [e1]; simp [Env.setVar]; exact hT.Pp_
  have hbb1 : σ1.vars "bb" = 2 ^ P.m := by rw [e1]; simp [Env.setVar, hC.bb_]
  have hcb1 : σ1.vars "cbase" = i0 * P.tabs := by rw [e1]; simp [Env.setVar, hT.cbase_]
  have hac1 : σ1.vars "ac" = 0 := by rw [e1]; simp [Env.setVar]
  have har1 : σ1.arrs = σ.arrs := by rw [e1]; simp [Env.setVar]
  have hix : ∀ j, σ1.vars "lo" + j * σ1.vars "Pp" + σ1.vars "hi" =
      insN (2 ^ P.m) p j (σ.vars "fc") := fun j => by
    rw [hlo1, hPp1, hhi1]; exact insAt_eq _ _ _ _
  have hrowT : ∀ j < 2 ^ P.m, (σ.arrs "TB").getD (i0 * P.tabs +
      insN (2 ^ P.m) p j (σ.vars "fc")) 0 = tbv P.I P.kk P.D i0 (insN (2 ^ P.m) p j (σ.vars "fc")) :=
    fun j hj => hT.tb _ (hins j hj)
  obtain ⟨σ2, r2, hv2, A2, o2⟩ := forgetOr_run (B := B) σ1 (2 ^ P.m) (i0 * P.tabs) hbb1
    (by omega) hcb1 (by omega)
    (fun j hj => by rw [hix, har1]; have := hins j hj; omega)
    (fun j hj => by rw [hix]; have := hins j hj; omega)
    (fun j hj => by rw [hix, har1, hrowT j hj]; exact tbv_le_one) (by omega)
    (by rw [hPp1]; omega)
  have hfold := or_fold (2 ^ P.m) (fun j => (σ1.arrs "TB").getD (i0 * P.tabs +
    (σ1.vars "lo" + j * σ1.vars "Pp" + σ1.vars "hi")) 0)
    (fun j hj => by
      show (σ1.arrs "TB").getD _ 0 ≤ 1
      rw [hix, har1, hrowT j hj]; exact tbv_le_one) (2 ^ P.m) le_rfl
  have hac2 : σ2.vars "ac" ≤ 1 := by
    rw [hv2, hac1, hfold]; split_ifs <;> omega
  have r3 : Run B (.assign "val" (V "ac")) σ2 (σ2.setVar "val" (σ2.vars "ac")) 2 :=
    (Run.assign (evalB_var (by omega))).mono (by simp [Expr.size])
  refine ⟨σ2.setVar "val" (σ2.vars "ac"), (r1.seq (r2.seq r3)).mono (by omega), ?_, ?_, ?_, ?_⟩
  · simp only [vars_setVar, if_true]
    rw [hv2, hac1, hfold, tbv_forget hT.k_]
    exact if_congr (exists_congr fun j => and_congr_right fun hj => by
      show (σ1.arrs "TB").getD _ 0 = 1 ↔ _
      rw [hix, har1, hrowT j hj]; exact Iff.rfl) rfl rfl
  · simp only [arrs_setVar]; rw [A2.1, har1]
  · intro y hy
    simp only [SF, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    have hyv : y ≠ "val" := hy.2.2.2.2.2.2
    simp only [vars_setVar, hyv, if_false]
    rw [A2.2 y (by simp [SO]; tauto), e1]
    simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1]
  · simp only [out_setVar]; rw [o2, e1]; simp [Env.setVar]

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwForget5` -/

section
/-!
The fill of the table of a forget node, and the whole program of a forget node.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

theorem forgetTB_run {i0 : ℕ} (hT : TCf P B i0 σ) (hbs : σ.vars "bs" = (i0 + 1) * P.tabs)
    (hfn : σ.vars "fn" = 2 ^ (P.m * ((bagL P.D i0).length - 1))) :
    ∃ σ', Run B (fillLoop "TB" forgetCell) σ σ'
        ((44 * 2 ^ P.m + 130 + 20 + 4) * 2 ^ (P.m * ((bagL P.D i0).length - 1)) + 6) ∧
      AgrA ("fc" :: SF) "TB" σ σ' ∧ σ'.out = σ.out ∧
      (σ'.arrs "TB").length = (σ.arrs "TB").length ∧
      RowDesc "TB" ((i0 + 1) * P.tabs) ((2 ^ P.I.days) ^ (bagL P.D (i0 + 1)).length)
        (fun e => tbv P.I P.kk P.D (i0 + 1) e) σ σ' := by
  have hC := hT.C
  have hiN := hT.iN
  have hl1 := bagL_forget_len P hiN hT.k_
  have hle1 := bagL_len_le P (j := i0 + 1) hiN
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  have hb1 := hC.b1
  have hlenTB := hC.lenTB
  have hpt : 2 ^ (P.m * ((bagL P.D i0).length - 1)) ≤ P.tabs := pow_le_tabs P (by omega)
  have hpt0 : (2 ^ P.m) ^ (bagL P.D i0).length ≤ P.tabs := by
    rw [bpow']; exact pow_le_tabs P hlen0
  have hNt : (i0 + 2) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ hiN
  have hi2t : (i0 + 2) * P.tabs = (i0 + 1) * P.tabs + P.tabs := by ring
  have hi1t : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
  have hres := fillLoop_run (B := B) "TB" forgetCell (fun e => tbv P.I P.kk P.D (i0 + 1) e)
    ("fc" :: SF) (44 * 2 ^ P.m + 130) (2 ^ (P.m * ((bagL P.D i0).length - 1)))
    σ hfn (by omega) (by rw [hbs]; omega)
    (fun k => lt_of_le_of_lt tbv_le_one (by omega)) (by simp [SF])
    (by rw [hbs]; omega) (by
      intro σ' hF hA hlt
      have hC' : NC P B σ' := hC.of_agrA hA hF.1 SF_sub (Or.inr (Or.inr rfl))
      have hS : ∀ y, y ∈ ["Pp", "shp1", "cbase"] → σ'.vars y = σ.vars y :=
        fun y hy => hA.1 y (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl <;> simp [SF])
      have hT' : TCf P B i0 σ' :=
        ⟨hC', hiN, hT.k_, fun e he => by
            rw [hF.2, if_neg (by rw [hbs]; omega)]; exact hT.tb e he,
          by rw [hS "Pp" (by simp)]; exact hT.Pp_, by rw [hS "shp1" (by simp)]; exact hT.shp1_,
          by rw [hS "cbase" (by simp)]; exact hT.cbase_⟩
      obtain ⟨σ'', r, hv, ha, hfr, ho⟩ := forgetCell_run hT' hlt
      exact ⟨σ'', r, hv, ha, fun y hy => hfr y (fun h => hy (List.mem_cons_of_mem _ h)),
        hfr "fc" (by simp [SF]), ho⟩)
  obtain ⟨σ', r, hl, hg, hA, ho⟩ := hres
  refine ⟨σ', r, hA, ho, hl, fun k => ?_⟩
  rw [hg k, hbs, hl1, bpow]

/-- **The program of a forget node.** -/
def forgetCom : Com :=
  .seq forgetHead (.seq (fillLoop "BG" bgPreForget) (.seq forgetMid (fillLoop "TB" forgetCell)))

/-- What a forget node costs. -/
def forgetCost (P : Params) : ℕ :=
  (34 * P.wid + 130) + ((20 + 20 + 4) * P.wid + 6) + 100 +
    ((44 * 2 ^ P.m + 130 + 20 + 4) * P.tabs + 6)

theorem forgetCom_run {i0 : ℕ} (hC : NC P B σ) (hN : NI P.I P.kk P.D P.wid P.tabs (i0 + 1) σ)
    (hi : σ.vars "i" = i0 + 1) (hiN : i0 + 1 < P.N) (hk : kind P.D (i0 + 1) = 2) :
    ∃ σ', Run B forgetCom σ σ' (forgetCost P) ∧ Keep σ σ' ∧
      NI P.I P.kk P.D P.wid P.tabs (i0 + 1 + 1) σ' ∧ σ'.out = σ.out := by
  have hl1 := bagL_forget_len P hiN hk
  have hpl := bagL_forget_facts P hiN hk
  have hle1 := bagL_len_le P (j := i0 + 1) hiN
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  obtain ⟨σ3, r3, k3, har3, hc3, hs3, hvx3, hot3, hp3, hcw3, hs13, hiw3, hbs3, hfn3⟩ :=
    forgetHead_run hC hN hi hiN
  have hQ3 : HQf P B i0 σ3 :=
    ⟨k3.nc hC, hiN, (k3.vars "i" (by simp [SN, SV, Stt, St2, SD])).trans hi, hc3, hs3, hvx3, hp3,
      hcw3, hs13, hiw3, hbs3, hfn3, hk⟩
  have hP3 : HPf P B i0 σ3 := ⟨hQ3, hN.of_arrs har3⟩
  obtain ⟨σ4, r4, hA4, o4, hl4, hrow4⟩ := forgetBG_run hP3
  have k4 : Keep σ3 σ4 := Keep.of_agrA hA4 hl4
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> simp [SN]) (Or.inr (Or.inl rfl)) o4
  have hQ4 : HQf P B i0 σ4 := hQ3.transfer k4 (fun y hy => hA4.1 y (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  obtain ⟨σ5, r5, e5⟩ := forgetMid_run hQ4
  have k5 : Keep σ4 σ5 := by
    rw [e5]; unfold midStateF
    exact ((((((Keep.refl σ4).setArr (Or.inl rfl) _ _).setVar (by simp [SN]) _).setVar
      (by simp [SN]) _).setVar (by simp [SN]) _).setVar (by simp [SN]) _).setVar
      (by simp [SN]) _
  have hTB5 : σ5.arrs "TB" = σ.arrs "TB" := by
    rw [e5]; simp [midStateF, hA4.2 "TB" (by decide), har3]
  have hSZ5 : σ5.arrs "SZ" = (σ.arrs "SZ").set (i0 + 1) ((bagL P.D i0).length - 1) := by
    rw [e5]; simp [midStateF, hA4.2 "SZ" (by decide), har3]
  have hBG5 : σ5.arrs "BG" = σ4.arrs "BG" := by
    rw [e5]; simp [midStateF]
  have hT5 : TCf P B i0 σ5 := by
    refine ⟨k5.nc hQ4.C, hiN, hk, fun e he => ?_, ?_, ?_, ?_⟩
    · rw [hTB5]; exact hN.tb i0 (by omega) e he
    · rw [e5]; simp [midStateF]
    · rw [e5]; simp [midStateF]
    · rw [e5]; simp [midStateF]
  have hbs5 : σ5.vars "bs" = (i0 + 1) * P.tabs := by rw [e5]; simp [midStateF]
  have hfn5 : σ5.vars "fn" = 2 ^ (P.m * ((bagL P.D i0).length - 1)) := by
    rw [e5]; simp [midStateF]
  obtain ⟨σ6, r6, hA6, o6, hl6, hrow6⟩ := forgetTB_run hT5 hbs5 hfn5
  have k6 : Keep σ5 σ6 := Keep.of_agrA hA6 hl6 SF_sub (Or.inr (Or.inr rfl)) o6
  have hpt : 2 ^ (P.m * ((bagL P.D i0).length - 1)) ≤ P.tabs := pow_le_tabs P (by omega)
  have hK : (44 * 2 ^ P.m + 130 + 20 + 4) * 2 ^ (P.m * ((bagL P.D i0).length - 1)) ≤
      (44 * 2 ^ P.m + 130 + 20 + 4) * P.tabs := Nat.mul_le_mul le_rfl hpt
  refine ⟨σ6, (r3.seq (r4.seq (r5.seq r6))).mono (by unfold forgetCost; omega),
    k3.trans (k4.trans (k5.trans k6)), ?_, by rw [o6, e5]; simp [midStateF, o4, k3.out]⟩
  refine NI_next (i := i0 + 1) (σ0 := σ) hN (fun j hj => bagL_len_le P (by omega))
    (fun s hs => by rw [bpow]; exact pow_le_tabs P hs) ?_ ?_ ?_
  · intro k
    rw [hA6.2 "SZ" (by decide), hSZ5, getD_set']
    by_cases hk1 : k = i0 + 1
    · subst hk1
      rw [if_pos ⟨rfl, by have := hC.lenSZ; omega⟩, if_pos (by omega), hl1]
    · rw [if_neg (by omega), if_neg (by omega)]
  · intro k
    rw [hA6.2 "BG" (by decide), hBG5, hrow4, har3]
  · intro k
    rw [hrow6, hTB5]

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwJoin1` -/

section
/-!
The program of a join node: the head and the row of the bag.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- **The second child of a join node is earlier and has the same bag.** -/
lemma join_facts (P : Params) {i : ℕ} (hi : i + 1 < P.N) (hk : kind P.D (i + 1) = 3) :
    other P.D (i + 1) < i ∧ bagL P.D (other P.D (i + 1)) = bagL P.D i := by
  have hN : P.N = nodeCount P.D := rfl
  have hshape := P.hD.shape (i + 1) hi
  rcases hshape with h0 | ⟨_, h1, _⟩ | ⟨_, h2, _⟩ | ⟨_, _, ho, hb⟩
  · omega
  · omega
  · omega
  · have hb' : bagAt P.I.clients P.D (other P.D (i + 1)) = bagAt P.I.clients P.D i := by
      simpa using hb
    obtain ⟨hp0, hm0⟩ := bagL_spec P.hD i (by omega)
    obtain ⟨hpo, hmo⟩ := bagL_spec P.hD (other P.D (i + 1)) (by omega)
    refine ⟨by omega, eq_of_mem_iff hpo hp0 fun x => ?_⟩
    rw [hmo, hm0, hb']

/-- **The table entry of a join node**, as a number. -/
lemma tbv_join {I : Lax117284.Scheduling.Instance} {kk : ℕ} {D : List ℕ} {i e : ℕ}
    (hk : kind D (i + 1) = 3) (ho : other D (i + 1) < i + 1) :
    tbv I kk D (i + 1) e = tbv I kk D i e * tbv I kk D (other D (i + 1)) e := by
  by_cases h1 : TB I kk D i e <;> by_cases h2 : TB I kk D (other D (i + 1)) e
  · rw [tbv_one ((TB_join hk ho).2 ⟨h1, h2⟩), tbv_one h1, tbv_one h2]
  · rw [tbv_zero (fun h => h2 ((TB_join hk ho).1 h).2), tbv_zero h2]; simp
  · rw [tbv_zero (fun h => h1 ((TB_join hk ho).1 h).1), tbv_zero h1]; simp
  · rw [tbv_zero (fun h => h1 ((TB_join hk ho).1 h).1), tbv_zero h1]; simp

/-- The sizes a join node needs. -/
def joinTail1 : Com := seqs
  [ .assign "s1" (V "s"),
    .assign "iw" (mul (V "i") (V "w1")),
    .assign "bs" (V "iw"),
    .assign "fn" (V "s") ]

/-- The head of the program of a join node. -/
def joinHead : Com := .seq recCom joinTail1

theorem joinHead_run {i0 : ℕ} (hC : NC P B σ)
    (hN : NI P.I P.kk P.D P.wid P.tabs (i0 + 1) σ) (hi : σ.vars "i" = i0 + 1) (hiN : i0 + 1 < P.N) :
    ∃ σ1, Run B joinHead σ σ1 100 ∧ Keep σ σ1 ∧ σ1.arrs = σ.arrs ∧
      σ1.vars "c" = i0 ∧ σ1.vars "s" = (bagL P.D i0).length ∧
      σ1.vars "ot" = other P.D (i0 + 1) ∧ σ1.vars "cw" = i0 * P.wid ∧
      σ1.vars "s1" = (bagL P.D i0).length ∧ σ1.vars "iw" = (i0 + 1) * P.wid ∧
      σ1.vars "bs" = (i0 + 1) * P.wid ∧ σ1.vars "fn" = (bagL P.D i0).length := by
  have hb2 := hC.b2
  have hb3 := hC.b3
  have hlD : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have hw1 := hC.w1_
  have hNw : ∀ j, j ≤ P.N → j * P.wid ≤ P.N * P.wid := fun j hj => Nat.mul_le_mul_right _ hj
  have hi2 : (i0 + 2) * P.wid ≤ P.N * P.wid := hNw _ (by omega)
  have hi2' : (i0 + 2) * P.wid = i0 * P.wid + P.wid + P.wid := by ring
  have hi1' : (i0 + 1) * P.wid = i0 * P.wid + P.wid := by ring
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  have hSc : (σ.arrs "SZ").getD i0 0 < B := by
    rw [hN.sz i0 (by omega)]; omega
  obtain ⟨σ1, r1, hc1, hvx1, hot1, hs1, hcw1, hp1, A1, o1⟩ := recCom_run (B := B) (σ := σ)
    (i := i0 + 1) (N := P.N) hi hiN hC.lenSZ (by have := hC.lenO; omega)
    (hC.O_lt (by omega) (by omega)) (hC.O_lt (by omega) (by omega))
    (by simpa using hSc) (by have := hC.b3; omega)
    (by rw [hw1, Nat.add_sub_cancel]; have := hNw i0 (by omega); omega)
    (by rw [hw1]; have := hNw 1 (by omega); omega)
  have hot' : σ1.vars "ot" = other P.D (i0 + 1) := by rw [hot1, other_eq P hC hiN]
  have hs' : σ1.vars "s" = (bagL P.D i0).length := by
    rw [hs1, Nat.add_sub_cancel, hN.sz i0 (by omega)]
  have hcw' : σ1.vars "cw" = i0 * P.wid := by rw [hcw1, Nat.add_sub_cancel, hw1]
  have hi1v : σ1.vars "i" = i0 + 1 := by rw [A1.2 "i" (by simp [SR]), hi]
  have hw1v : σ1.vars "w1" = P.wid := by rw [A1.2 "w1" (by simp [SR]), hw1]
  obtain ⟨σ3, r3, e3⟩ : ∃ σ3, Run B joinTail1 σ1 σ3 40 ∧ σ3 =
      (((σ1.setVar "s1" (bagL P.D i0).length).setVar "iw" ((i0 + 1) * P.wid)).setVar "bs"
        ((i0 + 1) * P.wid)).setVar "fn" (bagL P.D i0).length := by
    unfold joinTail1 seqs
    run_vcg
    all_goals (try nrmA)
    all_goals try (first | omega | (simp only [hs', hi1v, hw1v]; omega))
    all_goals (try simp only [hs', hi1v, hw1v])
  have hv3 : ∀ y, y ∉ ["s1", "iw", "bs", "fn"] → σ3.vars y = σ1.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [e3]; simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]
  have k1 := Keep.of_agr A1 SR_sub o1
  have k3 : Keep σ1 σ3 := by
    rw [e3]
    exact ((((Keep.refl σ1).setVar (by simp [SN]) _).setVar (by simp [SN]) _).setVar
      (by simp [SN]) _).setVar (by simp [SN]) _
  have har : σ3.arrs = σ.arrs := by rw [e3]; simp [A1.1]
  refine ⟨σ3, (r1.seq r3).mono (by omega), k1.trans k3, har, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv3 "c" (by simp), hc1]; simp
  · rw [hv3 "s" (by simp), hs']
  · rw [hv3 "ot" (by simp), hot']
  · rw [hv3 "cw" (by simp), hcw']
  · rw [e3]; simp [Env.setVar]
  · rw [e3]; simp [Env.setVar]
  · rw [e3]; simp [Env.setVar]
  · rw [e3]; simp [Env.setVar]

/-! ### The row of the bag -/

/-- The value of the cell of the new bag: the child's entry. -/
def bgPreJoin : Com := .assign "val" (G "BG" (add (V "cw") (V "fc")))

theorem bgPreJoin_run (σ : Env) (l : List ℕ) (cw : ℕ) (hcw : σ.vars "cw" = cw)
    (hrd : ∀ t < l.length, (σ.arrs "BG").getD (cw + t) 0 = l[t]!)
    (hf : σ.vars "fc" < l.length) (hlen : cw + l.length ≤ (σ.arrs "BG").length)
    (hbd : ∀ t : ℕ, l[t]! < B) (hb : cw + l.length + 8 < B) :
    ∃ σ', Run B bgPreJoin σ σ' 10 ∧ σ'.vars "val" = l[σ.vars "fc"]! ∧ σ'.arrs = σ.arrs ∧
      (∀ y, y ≠ "val" → σ'.vars y = σ.vars y) ∧ σ'.out = σ.out := by
  have hrd' : ∀ t < l.length, (σ.arrs "BG").getD (σ.vars "cw" + t) 0 = l[t]! := by
    rw [hcw]; exact hrd
  unfold bgPreJoin
  run_vcg
  all_goals first
    | (refine ⟨?_, rfl, fun y hy => by simp [Env.setVar, hy], rfl⟩
       nrmA
       rw [hrd' _ (by omega)])
    | omega
    | (rw [hrd' _ (by omega)]; exact hbd _)

/-- **The state after the head of a join node**, without the description of the arrays. -/
structure HQj (P : Params) (B : ℕ) (i0 : ℕ) (σ : Env) : Prop where
  C : NC P B σ
  iN : i0 + 1 < P.N
  i_ : σ.vars "i" = i0 + 1
  c_ : σ.vars "c" = i0
  s_ : σ.vars "s" = (bagL P.D i0).length
  ot_ : σ.vars "ot" = other P.D (i0 + 1)
  cw_ : σ.vars "cw" = i0 * P.wid
  s1_ : σ.vars "s1" = (bagL P.D i0).length
  iw_ : σ.vars "iw" = (i0 + 1) * P.wid
  bs_ : σ.vars "bs" = (i0 + 1) * P.wid
  fn_ : σ.vars "fn" = (bagL P.D i0).length
  k_ : kind P.D (i0 + 1) = 3

/-- The state after the head of a join node. -/
structure HPj (P : Params) (B : ℕ) (i0 : ℕ) (σ : Env) : Prop extends HQj P B i0 σ where
  N : NI P.I P.kk P.D P.wid P.tabs (i0 + 1) σ

lemma HQj.transfer {i0 : ℕ} {σ σ' : Env} (h : HQj P B i0 σ) (k : Keep σ σ')
    (hv : ∀ y ∈ ["i", "c", "s", "ot", "cw", "s1", "iw", "bs", "fn"],
      σ'.vars y = σ.vars y) : HQj P B i0 σ' :=
  ⟨k.nc h.C, h.iN, by rw [hv "i" (by simp)]; exact h.i_, by rw [hv "c" (by simp)]; exact h.c_,
    by rw [hv "s" (by simp)]; exact h.s_, by rw [hv "ot" (by simp)]; exact h.ot_,
    by rw [hv "cw" (by simp)]; exact h.cw_,
    by rw [hv "s1" (by simp)]; exact h.s1_, by rw [hv "iw" (by simp)]; exact h.iw_,
    by rw [hv "bs" (by simp)]; exact h.bs_, by rw [hv "fn" (by simp)]; exact h.fn_, h.k_⟩

theorem joinBG_run {i0 : ℕ} (h : HPj P B i0 σ) :
    ∃ σ4, Run B (fillLoop "BG" bgPreJoin) σ σ4 ((10 + 20 + 4) * (bagL P.D i0).length + 6) ∧
      AgrA ["fc", "val"] "BG" σ σ4 ∧ σ4.out = σ.out ∧
      (σ4.arrs "BG").length = (σ.arrs "BG").length ∧
      RowDesc "BG" ((i0 + 1) * P.wid) (bagL P.D (i0 + 1)).length
        (fun t => (bagL P.D (i0 + 1))[t]!) σ σ4 := by
  have hC := h.C
  have hiN := h.iN
  have hl1 : bagL P.D (i0 + 1) = bagL P.D i0 := bagL_join h.k_
  have hle0 := bagL_len_le P (j := i0) (by omega)
  have hb2 := hC.b2
  have hb3 := hC.b3
  have hb8 := hC.b8
  have hBpos : 0 < B := by omega
  have hNw : (i0 + 2) * P.wid ≤ P.N * P.wid := Nat.mul_le_mul_right _ h.iN
  have hi2' : (i0 + 2) * P.wid = i0 * P.wid + P.wid + P.wid := by ring
  have hi1' : (i0 + 1) * P.wid = i0 * P.wid + P.wid := by ring
  have hlenBG := hC.lenBG
  have hres := fillLoop_run (B := B) "BG" bgPreJoin (fun t => (bagL P.D (i0 + 1))[t]!)
    ["fc", "val"] 10 (bagL P.D i0).length σ h.fn_ (by omega)
    (by rw [h.bs_]; omega) (fun t => by
      have := bagL_get_le P (j := i0 + 1) h.iN t; omega) (by simp) (by rw [h.bs_]; omega) (by
    intro σ' hF hA hlt
    have e3 : σ'.vars "cw" = σ.vars "cw" := hA.1 "cw" (by simp)
    have hbsl : σ.vars "bs" = (i0 + 1) * P.wid := h.bs_
    obtain ⟨σ'', r, hv, ha, hfr, ho⟩ := bgPreJoin_run (B := B) σ' (bagL P.D i0) (i0 * P.wid)
      (by rw [e3, h.cw_])
      (fun t ht => by
        rw [hF.2, if_neg (by rw [hbsl]; omega)]
        exact h.N.bg i0 (by omega) t ht) (by omega)
      (by rw [hF.1]; omega)
      (fun t => by have := bagL_get_le P (j := i0) (by omega) t; omega) (by omega)
    refine ⟨σ'', r, ?_, by rw [ha], fun y hy => hfr y (by intro e; exact hy (by simp [e])),
      hfr "fc" (by decide), ho⟩
    rw [hv, hl1])
  obtain ⟨σ4, r, hl, hg, hA, ho⟩ := hres
  refine ⟨σ4, r, hA, ho, hl, fun k => ?_⟩
  rw [hg k, h.bs_, hl1]

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwJoin2` -/

section
/-!
The program of a join node: the size, the table, and the whole program.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- Store the size, and set the parameters of the fill of the table. -/
def joinMid : Com := seqs
  [ .store "SZ" (V "i") (V "s1"),
    .assign "cbase" (mul (V "c") (V "Tm")),
    .assign "ob" (mul (V "ot") (V "Tm")),
    .assign "bs" (mul (V "i") (V "Tm")),
    .assign "fn" (.bin .shiftl (L 1) (mul (V "m") (V "s1"))) ]

/-- The state after `joinMid`. -/
def midStateJ (P : Params) (i0 : ℕ) (σ : Env) : Env :=
  (((σ.setArr "SZ" (i0 + 1) (bagL P.D i0).length).setVar "cbase" (i0 * P.tabs)).setVar "ob"
    (other P.D (i0 + 1) * P.tabs)).setVar "bs" ((i0 + 1) * P.tabs) |>.setVar "fn"
    (2 ^ (P.m * (bagL P.D i0).length))

theorem joinMid_run {i0 : ℕ} (h : HQj P B i0 σ) :
    ∃ σ', Run B joinMid σ σ' 100 ∧ σ' = midStateJ P i0 σ := by
  have hC := h.C
  have hiN := h.iN
  have hjf := join_facts P h.iN h.k_
  have hle0 := bagL_len_le P (j := i0) (by omega)
  have hb1 := hC.b1
  have hb9 := hC.b9
  have hb3 := hC.b3
  have hb2 := hC.b2
  have hlenSZ := hC.lenSZ
  have hNt : (i0 + 2) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ h.iN
  have hi2 : (i0 + 2) * P.tabs = i0 * P.tabs + P.tabs + P.tabs := by ring
  have hi1 : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
  have hp2 : 2 ^ (P.m * (bagL P.D i0).length) ≤ P.tabs := pow_le_tabs P hle0
  have hms1 : P.m * (bagL P.D i0).length ≤ P.m * P.wid := Nat.mul_le_mul_left _ hle0
  have hmw : P.m * (P.wid + 1) = P.m * P.wid + P.m := by ring
  have hct : i0 * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ (by omega)
  have hot : other P.D (i0 + 1) * P.tabs ≤ i0 * P.tabs := Nat.mul_le_mul_right _ (by omega)
  unfold joinMid seqs
  run_vcg
  all_goals (try nrmA)
  all_goals try (first | omega | (simp only [h.i_, h.s1_, hC.m_, hC.Tm_, h.c_, h.ot_, one_mul]; omega))
  all_goals (try simp only [midStateJ, h.i_, h.s1_, hC.m_, hC.Tm_, h.c_, h.ot_, one_mul])

/-- The cell of the table of a join node: the product of the entries of the two children. -/
def joinCell : Com :=
  .assign "val" (mul (G "TB" (add (V "cbase") (V "fc"))) (G "TB" (add (V "ob") (V "fc"))))

/-- **The context of a cell of the table of a join node.** -/
structure TCj (P : Params) (B : ℕ) (i0 : ℕ) (σ : Env) : Prop where
  C : NC P B σ
  iN : i0 + 1 < P.N
  k_ : kind P.D (i0 + 1) = 3
  tb : ∀ e < (2 ^ P.m) ^ (bagL P.D i0).length,
    (σ.arrs "TB").getD (i0 * P.tabs + e) 0 = tbv P.I P.kk P.D i0 e
  tbo : ∀ e < (2 ^ P.m) ^ (bagL P.D i0).length,
    (σ.arrs "TB").getD (other P.D (i0 + 1) * P.tabs + e) 0 =
      tbv P.I P.kk P.D (other P.D (i0 + 1)) e
  cbase_ : σ.vars "cbase" = i0 * P.tabs
  ob_ : σ.vars "ob" = other P.D (i0 + 1) * P.tabs

theorem joinCell_run {i0 : ℕ} (hT : TCj P B i0 σ)
    (hfc : σ.vars "fc" < 2 ^ (P.m * (bagL P.D i0).length)) :
    ∃ σ', Run B joinCell σ σ' 30 ∧
      σ'.vars "val" = tbv P.I P.kk P.D (i0 + 1) (σ.vars "fc") ∧ σ'.arrs = σ.arrs ∧
      (∀ y, y ≠ "val" → σ'.vars y = σ.vars y) ∧ σ'.out = σ.out := by
  have hC := hT.C
  have hiN := hT.iN
  have hjf := join_facts P hiN hT.k_
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  have hb1 := hC.b1
  have hlenTB := hC.lenTB
  have hfc' : σ.vars "fc" < (2 ^ P.m) ^ (bagL P.D i0).length := by rw [bpow']; exact hfc
  have hpt : 2 ^ (P.m * (bagL P.D i0).length) ≤ P.tabs := pow_le_tabs P hlen0
  have hNt : (i0 + 1) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ (by omega)
  have hi1 : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
  have hoi : (other P.D (i0 + 1) + 1) * P.tabs ≤ i0 * P.tabs := Nat.mul_le_mul_right _ (by omega)
  have hoi1 : (other P.D (i0 + 1) + 1) * P.tabs = other P.D (i0 + 1) * P.tabs + P.tabs := by ring
  have hv1 := hT.tb _ hfc'
  have hv2 := hT.tbo _ hfc'
  have hle1 := tbv_le_one (I := P.I) (kk := P.kk) (D := P.D) (j := i0) (e := σ.vars "fc")
  have hle2 := tbv_le_one (I := P.I) (kk := P.kk) (D := P.D) (j := other P.D (i0 + 1))
    (e := σ.vars "fc")
  have hprod : tbv P.I P.kk P.D i0 (σ.vars "fc") *
      tbv P.I P.kk P.D (other P.D (i0 + 1)) (σ.vars "fc") ≤ 1 :=
    calc _ ≤ 1 * 1 := Nat.mul_le_mul hle1 hle2
      _ = 1 := rfl
  unfold joinCell
  run_vcg
  all_goals first
    | (refine ⟨?_, rfl, fun y hy => by simp [Env.setVar, hy], rfl⟩
       nrmA
       rw [hT.cbase_, hT.ob_, hv1, hv2, tbv_join hT.k_ (by omega)])
    | (simp only [hT.cbase_, hT.ob_, hv1, hv2]; omega)
    | omega

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwJoin3` -/

section
/-!
The fill of the table of a join node, and the whole program of a join node.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

theorem joinTB_run {i0 : ℕ} (hT : TCj P B i0 σ) (hbs : σ.vars "bs" = (i0 + 1) * P.tabs)
    (hfn : σ.vars "fn" = 2 ^ (P.m * (bagL P.D i0).length)) :
    ∃ σ', Run B (fillLoop "TB" joinCell) σ σ'
        ((30 + 20 + 4) * 2 ^ (P.m * (bagL P.D i0).length) + 6) ∧
      AgrA ["fc", "val"] "TB" σ σ' ∧ σ'.out = σ.out ∧
      (σ'.arrs "TB").length = (σ.arrs "TB").length ∧
      RowDesc "TB" ((i0 + 1) * P.tabs) ((2 ^ P.I.days) ^ (bagL P.D (i0 + 1)).length)
        (fun e => tbv P.I P.kk P.D (i0 + 1) e) σ σ' := by
  have hC := hT.C
  have hiN := hT.iN
  have hjf := join_facts P hiN hT.k_
  have hl1 : bagL P.D (i0 + 1) = bagL P.D i0 := bagL_join hT.k_
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  have hb1 := hC.b1
  have hlenTB := hC.lenTB
  have hpt : 2 ^ (P.m * (bagL P.D i0).length) ≤ P.tabs := pow_le_tabs P hlen0
  have hpt0 : (2 ^ P.m) ^ (bagL P.D i0).length ≤ P.tabs := by
    rw [bpow']; exact hpt
  have hNt : (i0 + 2) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ hiN
  have hi2t : (i0 + 2) * P.tabs = (i0 + 1) * P.tabs + P.tabs := by ring
  have hi1t : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
  have hoi : (other P.D (i0 + 1) + 1) * P.tabs ≤ i0 * P.tabs := Nat.mul_le_mul_right _ (by omega)
  have hoi1 : (other P.D (i0 + 1) + 1) * P.tabs = other P.D (i0 + 1) * P.tabs + P.tabs := by ring
  have hres := fillLoop_run (B := B) "TB" joinCell (fun e => tbv P.I P.kk P.D (i0 + 1) e)
    ["fc", "val"] 30 (2 ^ (P.m * (bagL P.D i0).length))
    σ hfn (by omega) (by rw [hbs]; omega)
    (fun k => lt_of_le_of_lt tbv_le_one (by omega)) (by simp)
    (by rw [hbs]; omega) (by
      intro σ' hF hA hlt
      have hC' : NC P B σ' := hC.of_agrA hA hF.1
        (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
            rcases hy with rfl | rfl <;> simp [SN]) (Or.inr (Or.inr rfl))
      have hS : ∀ y, y ∈ ["cbase", "ob"] → σ'.vars y = σ.vars y :=
        fun y hy => hA.1 y (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl <;> simp)
      have hT' : TCj P B i0 σ' :=
        ⟨hC', hiN, hT.k_, fun e he => by
            rw [hF.2, if_neg (by rw [hbs]; omega)]; exact hT.tb e he,
          fun e he => by
            rw [hF.2, if_neg (by rw [hbs]; omega)]; exact hT.tbo e he,
          by rw [hS "cbase" (by simp)]; exact hT.cbase_,
          by rw [hS "ob" (by simp)]; exact hT.ob_⟩
      obtain ⟨σ'', r, hv, ha, hfr, ho⟩ := joinCell_run hT' hlt
      exact ⟨σ'', r.mono (by omega), hv, ha, fun y hy => hfr y (fun h => hy (by simp [h])),
        hfr "fc" (by decide), ho⟩)
  obtain ⟨σ', r, hl, hg, hA, ho⟩ := hres
  refine ⟨σ', r, hA, ho, hl, fun k => ?_⟩
  rw [hg k, hbs, hl1, bpow]

/-- **The program of a join node.** -/
def joinCom : Com :=
  .seq joinHead (.seq (fillLoop "BG" bgPreJoin) (.seq joinMid (fillLoop "TB" joinCell)))

/-- What a join node costs. -/
def joinCost (P : Params) : ℕ :=
  100 + ((10 + 20 + 4) * P.wid + 6) + 100 + ((30 + 20 + 4) * P.tabs + 6)

theorem joinCom_run {i0 : ℕ} (hC : NC P B σ) (hN : NI P.I P.kk P.D P.wid P.tabs (i0 + 1) σ)
    (hi : σ.vars "i" = i0 + 1) (hiN : i0 + 1 < P.N) (hk : kind P.D (i0 + 1) = 3) :
    ∃ σ', Run B joinCom σ σ' (joinCost P) ∧ Keep σ σ' ∧
      NI P.I P.kk P.D P.wid P.tabs (i0 + 1 + 1) σ' ∧ σ'.out = σ.out := by
  have hjf := join_facts P hiN hk
  have hl1 : bagL P.D (i0 + 1) = bagL P.D i0 := bagL_join hk
  have hle0 := bagL_len_le P (j := i0) (by omega)
  obtain ⟨σ3, r3, k3, har3, hc3, hs3, hot3, hcw3, hs13, hiw3, hbs3, hfn3⟩ :=
    joinHead_run hC hN hi hiN
  have hQ3 : HQj P B i0 σ3 :=
    ⟨k3.nc hC, hiN, (k3.vars "i" (by simp [SN, SV, Stt, St2, SD])).trans hi, hc3, hs3, hot3,
      hcw3, hs13, hiw3, hbs3, hfn3, hk⟩
  have hP3 : HPj P B i0 σ3 := ⟨hQ3, hN.of_arrs har3⟩
  obtain ⟨σ4, r4, hA4, o4, hl4, hrow4⟩ := joinBG_run hP3
  have k4 : Keep σ3 σ4 := Keep.of_agrA hA4 hl4
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> simp [SN]) (Or.inr (Or.inl rfl)) o4
  have hQ4 : HQj P B i0 σ4 := hQ3.transfer k4 (fun y hy => hA4.1 y (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  obtain ⟨σ5, r5, e5⟩ := joinMid_run hQ4
  have k5 : Keep σ4 σ5 := by
    rw [e5]; unfold midStateJ
    exact (((((Keep.refl σ4).setArr (Or.inl rfl) _ _).setVar (by simp [SN]) _).setVar
      (by simp [SN]) _).setVar (by simp [SN]) _).setVar (by simp [SN]) _
  have hTB5 : σ5.arrs "TB" = σ.arrs "TB" := by
    rw [e5]; simp [midStateJ, hA4.2 "TB" (by decide), har3]
  have hSZ5 : σ5.arrs "SZ" = (σ.arrs "SZ").set (i0 + 1) (bagL P.D i0).length := by
    rw [e5]; simp [midStateJ, hA4.2 "SZ" (by decide), har3]
  have hBG5 : σ5.arrs "BG" = σ4.arrs "BG" := by
    rw [e5]; simp [midStateJ]
  have hT5 : TCj P B i0 σ5 := by
    refine ⟨k5.nc hQ4.C, hiN, hk, fun e he => ?_, fun e he => ?_, ?_, ?_⟩
    · rw [hTB5]; exact hN.tb i0 (by omega) e he
    · rw [hTB5]
      exact hN.tb (other P.D (i0 + 1)) (by omega) e (by rw [hjf.2]; exact he)
    · rw [e5]; simp [midStateJ]
    · rw [e5]; simp [midStateJ]
  have hbs5 : σ5.vars "bs" = (i0 + 1) * P.tabs := by rw [e5]; simp [midStateJ]
  have hfn5 : σ5.vars "fn" = 2 ^ (P.m * (bagL P.D i0).length) := by
    rw [e5]; simp [midStateJ]
  obtain ⟨σ6, r6, hA6, o6, hl6, hrow6⟩ := joinTB_run hT5 hbs5 hfn5
  have k6 : Keep σ5 σ6 := Keep.of_agrA hA6 hl6
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> simp [SN]) (Or.inr (Or.inr rfl)) o6
  have hpt : 2 ^ (P.m * (bagL P.D i0).length) ≤ P.tabs := pow_le_tabs P hle0
  have hK : (30 + 20 + 4) * 2 ^ (P.m * (bagL P.D i0).length) ≤ (30 + 20 + 4) * P.tabs :=
    Nat.mul_le_mul le_rfl hpt
  refine ⟨σ6, (r3.seq (r4.seq (r5.seq r6))).mono (by unfold joinCost; omega),
    k3.trans (k4.trans (k5.trans k6)), ?_, by rw [o6, e5]; simp [midStateJ, o4, k3.out]⟩
  refine NI_next (i := i0 + 1) (σ0 := σ) hN (fun j hj => bagL_len_le P (by omega))
    (fun s hs => by rw [bpow]; exact pow_le_tabs P hs) ?_ ?_ ?_
  · intro k
    rw [hA6.2 "SZ" (by decide), hSZ5, getD_set']
    by_cases hk1 : k = i0 + 1
    · subst hk1
      rw [if_pos ⟨rfl, by have := hC.lenSZ; omega⟩, if_pos (by omega), hl1]
    · rw [if_neg (by omega), if_neg (by omega)]
  · intro k
    rw [hA6.2 "BG" (by decide), hBG5, hrow4, har3]
  · intro k
    rw [hrow6, hTB5]

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwLoop1` -/

section
/-!
The program of a node of any kind: the leaf, and the dispatch on the kind.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

lemma bagL_leaf' (P : Params) {i : ℕ} (hk : i = 0 ∨ kind P.D i = 0) : bagL P.D i = [] := by
  rcases hk with rfl | hk
  · simp [bagL]
  · cases i with
    | zero => simp [bagL]
    | succ j => exact bagL_leaf hk

lemma tbv_leaf0 {I : Lax117284.Scheduling.Instance} {kk : ℕ} {D : List ℕ} {i : ℕ}
    (hk : i = 0 ∨ kind D i = 0) : tbv I kk D i 0 = 1 := by
  rcases hk with rfl | hk
  · exact tbv_one (by simp [TB])
  · cases i with
    | zero => exact tbv_one (by simp [TB])
    | succ j => exact tbv_one ((TB_leaf hk).2 rfl)

theorem leafCom_ok {i : ℕ} (hC : NC P B σ) (hN : NI P.I P.kk P.D P.wid P.tabs i σ)
    (hi : σ.vars "i" = i) (hiN : i < P.N) (hk : i = 0 ∨ kind P.D i = 0) :
    ∃ σ', Run B leafCom σ σ' 40 ∧ Keep σ σ' ∧ NI P.I P.kk P.D P.wid P.tabs (i + 1) σ' ∧
      σ'.out = σ.out := by
  have hb1 := hC.b1
  have htab : 0 < P.tabs := by unfold Params.tabs Params.bs; positivity
  have hNt : (i + 1) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ hiN
  have hi1 : (i + 1) * P.tabs = i * P.tabs + P.tabs := by ring
  obtain ⟨σ', r, e⟩ := leafCom_run (B := B) (Tm := P.tabs) hi hC.Tm_
    (by have := hC.lenSZ; omega) (by have := hC.lenTB; omega)
    (by omega) (by have := hC.b3; omega)
  have hl0 := bagL_leaf' P hk
  have hleaf := tbv_leaf0 (I := P.I) (kk := P.kk) (D := P.D) hk
  have hSZ : σ'.arrs "SZ" = (σ.arrs "SZ").set i 0 := by rw [e]; simp
  have hBG : σ'.arrs "BG" = σ.arrs "BG" := by rw [e]; simp
  have hTB : σ'.arrs "TB" = (σ.arrs "TB").set (i * P.tabs) 1 := by rw [e]; simp
  refine ⟨σ', r, ?_, ?_, by rw [e]; simp⟩
  · rw [e]
    exact (((Keep.refl σ).setArr (Or.inl rfl) _ _).setVar (by simp [SN]) _).setArr
      (Or.inr (Or.inr rfl)) _ _
  · refine NI_next (i := i) (σ0 := σ) hN (fun j hj => ?_)
      (fun s hs => by rw [bpow]; exact pow_le_tabs P hs) ?_ ?_ ?_
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · exact bagL_len_le P (by omega)
      · subst h; rw [hl0]; simp
    · intro k
      rw [hSZ, getD_set']
      by_cases hk1 : k = i
      · subst hk1
        rw [if_pos ⟨rfl, by have := hC.lenSZ; omega⟩]
        simp [hl0]
      · rw [if_neg (by omega), if_neg (by omega)]
    · intro k
      simp [hBG, hl0]
    · intro k
      rw [hTB, getD_set']
      simp only [hl0, List.length_nil, pow_zero]
      by_cases hk1 : k = i * P.tabs
      · subst hk1
        rw [if_pos ⟨rfl, by have := hC.lenTB; omega⟩]
        simp [hleaf]
      · rw [if_neg (by omega), if_neg (by omega)]

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwLoop2` -/

section
/-!
The program of a node of any kind: the dispatch on the kind.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- **The program of a node.** -/
def nodeCom : Com :=
  .seq (.assign "kd" (G "O" (add (L 2) (mul (L 3) (V "i")))))
    (.ite (.eq (V "kd") (L 0)) leafCom
      (.ite (.eq (V "kd") (L 1)) introCom
        (.ite (.eq (V "kd") (L 2)) forgetCom joinCom)))

/-- What a node costs. -/
def nodeCost (P : Params) : ℕ := 60 + introCost P + forgetCost P + joinCost P

lemma kd_cond (hk : σ.vars "kd" < B) {k : ℕ} (hkB : k < B) :
    (Cond.eq (V "kd") (L k)).evalB B σ = some (σ.vars "kd" == k) :=
  evalB_condEq (evalB_var hk) (evalB_lit hkB)

theorem kd_run (hC : NC P B σ) {i : ℕ} (hi : σ.vars "i" = i) (hiN : i < P.N) :
    Run B (.assign "kd" (G "O" (add (L 2) (mul (L 3) (V "i"))))) σ
      (σ.setVar "kd" (kind P.D i)) 20 := by
  have hk := kind_eq P hC hiN
  have hlD : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have hb3 := hC.b3
  have hlenO := hC.lenO
  have hBpos : 0 < B := by omega
  have hidx : (σ.arrs "O")[2 + 3 * i]? = some (kind P.D i) := by
    rw [List.getElem?_eq_getElem (by omega)]
    have := hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
    simpa using this
  have hkB : kind P.D i < B := by rw [← hk]; exact hC.O_lt (by omega) (by omega)
  refine (Run.assign (v := kind P.D i) ?_).mono (by simp [Expr.size])
  refine evalB_get (k := 2 + 3 * i) ?_ hidx hkB
  have := evalB_bin (B := B) (σ := σ) (op := .add) (e := L 2) (f := mul (L 3) (V "i"))
    (m := 2) (n := 3 * i) (evalB_lit (by omega))
    (evalB_bin (op := .mul) (m := 3) (n := i) (evalB_lit (by omega))
      (by rw [evalB_var (by omega)]; exact congrArg some hi) (by simp; omega)) (by simp; omega)
  simpa using this

theorem nodeCom_run {i : ℕ} (hC : NC P B σ) (hN : NI P.I P.kk P.D P.wid P.tabs i σ)
    (hi : σ.vars "i" = i) (hiN : i < P.N) :
    ∃ σ', Run B nodeCom σ σ' (nodeCost P) ∧ Keep σ σ' ∧
      NI P.I P.kk P.D P.wid P.tabs (i + 1) σ' ∧ σ'.out = σ.out := by
  have r1 := kd_run hC hi hiN
  set σ1 := σ.setVar "kd" (kind P.D i) with hσ1
  have kk1 : Keep σ σ1 := (Keep.refl σ).setVar (by simp [SN]) _
  have hC1 : NC P B σ1 := kk1.nc hC
  have hN1 : NI P.I P.kk P.D P.wid P.tabs i σ1 := hN.of_arrs (by simp [hσ1])
  have hi1 : σ1.vars "i" = i := by simp [hσ1, hi]
  have hkd : σ1.vars "kd" = kind P.D i := by simp [hσ1]
  have hkdB : kind P.D i < B := by
    have := hC.b3; have := (P.hD.shape i hiN)
    rcases this with h | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> omega
  have hb3 := hC.b3
  have hcs := P.hD.shape i hiN
  have hc0 := kd_cond (σ := σ1) (by rw [hkd]; exact hkdB) (k := 0) (by omega)
  have hc1 := kd_cond (σ := σ1) (by rw [hkd]; exact hkdB) (k := 1) (by omega)
  have hc2 := kd_cond (σ := σ1) (by rw [hkd]; exact hkdB) (k := 2) (by omega)
  rw [hkd] at hc0 hc1 hc2
  have hnc : ∀ K, K ≤ 100 → 20 + (1 + (Cond.eq (V "kd") (L 0)).size + K) ≤ nodeCost P := by
    intro K hK
    simp only [Cond.size, Expr.size]
    unfold nodeCost introCost forgetCost joinCost
    omega
  rcases hcs with h0 | ⟨hpos, h1, _⟩ | ⟨hpos, h2, _⟩ | ⟨hpos, h3, _⟩
  · -- a leaf
    obtain ⟨σ', r, kk2, hN', ho⟩ := leafCom_ok (B := B) hC1 hN1 hi1 hiN (Or.inr h0)
    refine ⟨σ', (r1.seq (Run.ite_true (by rw [hc0, h0]; rfl) r)).mono
      (by simp only [Cond.size, Expr.size]; unfold nodeCost introCost forgetCost joinCost; omega),
      kk1.trans kk2, hN', by rw [ho]; simp [hσ1]⟩
  · -- an introduce node
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    obtain ⟨σ', r, kk2, hN', ho⟩ := introCom_run (B := B) hC1 hN1 hi1 hiN h1
    refine ⟨σ', (r1.seq (Run.ite_false (by rw [hc0, h1]; rfl)
      (Run.ite_true (by rw [hc1, h1]; rfl) r))).mono
      (by simp only [Cond.size, Expr.size]; unfold nodeCost introCost forgetCost joinCost; omega),
      kk1.trans kk2, hN', by rw [ho]; simp [hσ1]⟩
  · -- a forget node
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    obtain ⟨σ', r, kk2, hN', ho⟩ := forgetCom_run (B := B) hC1 hN1 hi1 hiN h2
    refine ⟨σ', (r1.seq (Run.ite_false (by rw [hc0, h2]; rfl)
      (Run.ite_false (by rw [hc1, h2]; rfl) (Run.ite_true (by rw [hc2, h2]; rfl) r)))).mono
      (by simp only [Cond.size, Expr.size]; unfold nodeCost introCost forgetCost joinCost; omega),
      kk1.trans kk2, hN', by rw [ho]; simp [hσ1]⟩
  · -- a join node
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    obtain ⟨σ', r, kk2, hN', ho⟩ := joinCom_run (B := B) hC1 hN1 hi1 hiN h3
    refine ⟨σ', (r1.seq (Run.ite_false (by rw [hc0, h3]; rfl)
      (Run.ite_false (by rw [hc1, h3]; rfl) (Run.ite_false (by rw [hc2, h3]; rfl) r)))).mono
      (by simp only [Cond.size, Expr.size]; unfold nodeCost introCost forgetCost joinCost; omega),
      kk1.trans kk2, hN', by rw [ho]; simp [hσ1]⟩

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwLoop3` -/

section
/-!
The loop over the nodes.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

lemma NC.setVar_i (h : NC P B σ) (v : ℕ) : NC P B (σ.setVar "i" v) :=
  h.transfer (fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Env.setVar])
    (by simp) (by simp) (by simp) (by simp) (by simp)

/-- **The loop over the nodes.** -/
def nodeLoop : Com := fLoop "i" "N" nodeCom

/-- What the loop over the nodes costs. -/
def loopCost (P : Params) : ℕ := (nodeCost P + 10 + 4) * P.N + 6

theorem nodeLoop_run (hC : NC P B σ) :
    ∃ σ', Run B nodeLoop σ σ' (loopCost P) ∧ NC P B σ' ∧
      NI P.I P.kk P.D P.wid P.tabs P.N σ' ∧ σ'.vars "i" = P.N ∧ σ'.out = σ.out := by
  let I : Env → Prop := fun τ => NC P B τ ∧ NI P.I P.kk P.D P.wid P.tabs (τ.vars "i") τ ∧
    τ.vars "i" ≤ P.N ∧ τ.out = σ.out
  have hb3 := hC.b3
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "i" < P.N)
      (.seq nodeCom (.assign "i" (.bin .add (.var "i") (.lit 1))))
      (fun τ τ' => I τ' ∧ τ'.vars "i" = τ.vars "i" + 1) (nodeCost P + 10) := by
    rintro τ ⟨⟨hC1, hN1, hle, ho⟩, hlt⟩
    obtain ⟨τ1, r1, kk1, hN2, ho1⟩ := nodeCom_run hC1 hN1 rfl hlt
    have hi1 : τ1.vars "i" = τ.vars "i" := kk1.vars "i" (by simp [SN, SV, Stt, St2, SD])
    have hlt1 : τ1.vars "i" + 1 < B := by
      have := hC1.b3; rw [hi1]; omega
    have r2 : Run B (.assign "i" (.bin .add (.var "i") (.lit 1))) τ1
        (τ1.setVar "i" (τ1.vars "i" + 1)) (1 + (Expr.bin .add (.var "i") (.lit 1)).size) :=
      Run.assign (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; try omega))
    refine ⟨_, (r1.seq r2).mono (by simp [Expr.size]; try omega), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · exact (kk1.nc hC1).setVar_i _
    · simp only [vars_setVar, if_true, hi1]
      exact hN2.of_arrs (by simp)
    · simp only [vars_setVar, if_true, hi1]; omega
    · simp [ho1, ho]
    · simp [hi1]
  have hres := (Spec.forRangeZero (B := B)
    (c := .seq nodeCom (.assign "i" (.bin .add (.var "i") (.lit 1)))) "i" "N" I P.N
    (nodeCost P + 10) (by omega) (fun τ h => h.2.2.1) (fun τ h => h.1.N_) hbody) σ (by
      refine ⟨hC.setVar_i _, ?_, by simp, by simp⟩
      exact ⟨fun j hj => by simp at hj, fun j hj => by simp at hj, fun j hj => by simp at hj⟩)
  obtain ⟨σ', r, hI, hi⟩ := hres
  refine ⟨σ', r.mono (by unfold loopCost; omega), hI.1, ?_, hi, hI.2.2.2⟩
  have := hI.2.1
  rwa [hi] at this

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwAnswer` -/

section
/-!
The answer: some restriction is in the table of the last node.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- One step of the search for a one in the last row of the table. -/
def orBody : Com := .assign "ac" (.bin .or (V "ac") (G "TB" (add (V "bs") (V "so"))))

theorem orBody_run (σ : Env) (hidx : σ.vars "bs" + σ.vars "so" < (σ.arrs "TB").length)
    (hixB : σ.vars "bs" + σ.vars "so" < B) (hac : σ.vars "ac" ≤ 1)
    (hT : (σ.arrs "TB").getD (σ.vars "bs" + σ.vars "so") 0 ≤ 1) (hB : 2 < B)
    (hso : σ.vars "so" < B) (hbs : σ.vars "bs" < B) :
    ∃ σ', Run B orBody σ σ' 20 ∧
      σ'.vars "ac" = Nat.lor (σ.vars "ac") ((σ.arrs "TB").getD (σ.vars "bs" + σ.vars "so") 0) ∧
      Agr ["ac"] σ σ' ∧ σ'.vars "so" = σ.vars "so" ∧ σ'.out = σ.out := by
  have hlor := lor_le_one hac hT
  unfold orBody
  run_vcg
  all_goals try (nrmA; first | omega | exact lt_of_le_of_lt hlor (by omega))
  refine ⟨?_, ⟨rfl, fun y hy => ?_⟩, ?_, rfl⟩
  · nrmA
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [Env.setVar, hy]
  · nrmA

/-- The loop over the last row of the table. -/
def orLoop : Com := fLoop "so" "fn" orBody

/-- The preparation of the answer: the last node, its size, the search range. -/
def answerPre : Com := seqs
  [ .assign "c" (sub (V "N") (L 1)),
    .assign "s" (G "SZ" (V "c")),
    .assign "bs" (mul (V "c") (V "Tm")),
    .assign "fn" (.bin .shiftl (L 1) (mul (V "m") (V "s"))),
    .assign "ac" (L 0) ]

/-- **The answer.** -/
def answerCom : Com := .seq answerPre (.seq orLoop (.write (V "ac")))

/-- The state after `answerPre`. -/
def preState (P : Params) (σ : Env) : Env :=
  ((((σ.setVar "c" (P.N - 1)).setVar "s" (bagL P.D (P.N - 1)).length).setVar "bs"
    ((P.N - 1) * P.tabs)).setVar "fn" (2 ^ (P.m * (bagL P.D (P.N - 1)).length))).setVar "ac" 0

theorem answerPre_run (hC : NC P B σ) (hN : NI P.I P.kk P.D P.wid P.tabs P.N σ) :
    ∃ σ1, Run B answerPre σ σ1 60 ∧ σ1 = preState P σ := by
  have hNpos : 0 < P.N := P.hD.nonempty
  have hsz := hN.sz (P.N - 1) (by omega)
  have hle := bagL_len_le P (j := P.N - 1) (by omega)
  have hb1 := hC.b1
  have hb3 := hC.b3
  have hb9 := hC.b9
  have hb2 := hC.b2
  have hNt : (P.N - 1) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ (by omega)
  have hpt : 2 ^ (P.m * (bagL P.D (P.N - 1)).length) ≤ P.tabs := pow_le_tabs P hle
  have hms : P.m * (bagL P.D (P.N - 1)).length ≤ P.m * P.wid := Nat.mul_le_mul_left _ hle
  have hmw : P.m * (P.wid + 1) = P.m * P.wid + P.m := by ring
  have hlenSZ := hC.lenSZ
  unfold answerPre seqs
  run_vcg
  all_goals (try nrmA)
  all_goals try (first | omega | (simp only [hC.N_, hC.Tm_, hC.m_, hsz, one_mul]; omega))
  all_goals (try simp only [preState, hC.N_, hC.Tm_, hC.m_, hsz, one_mul])

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwAnswer2` -/

section
/-!
The answer: the correctness.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- What the answer costs. -/
def answerCost (P : Params) : ℕ := 60 + ((20 + 10 + 4) * P.tabs + 6) + 10

open Classical in
theorem answerCom_run (hC : NC P B σ) (hN : NI P.I P.kk P.D P.wid P.tabs P.N σ) :
    ∃ σ', Run B answerCom σ σ' (answerCost P) ∧
      σ'.out = σ.out ++ [if P.I.HasKFairSchedule P.kk then 1 else 0] := by
  have hNpos : 0 < P.N := P.hD.nonempty
  obtain ⟨σ1, r1, e1⟩ := answerPre_run hC hN
  have hle := bagL_len_le P (j := P.N - 1) (by omega)
  have hb1 := hC.b1
  have hlenTB := hC.lenTB
  have hpt : 2 ^ (P.m * (bagL P.D (P.N - 1)).length) ≤ P.tabs := pow_le_tabs P hle
  have hNt : P.N * P.tabs = (P.N - 1) * P.tabs + P.tabs := by
    have : P.N = (P.N - 1) + 1 := by omega
    conv_lhs => rw [this]
    ring
  have hTBl : (σ1.arrs "TB").length = (σ.arrs "TB").length := by
    rw [show σ1.arrs = σ.arrs by rw [e1]; simp [preState]]
  have hbs1 : σ1.vars "bs" = (P.N - 1) * P.tabs := by rw [e1]; simp [preState]
  have hfn1 : σ1.vars "fn" = 2 ^ (P.m * (bagL P.D (P.N - 1)).length) := by
    rw [e1]; simp [preState]
  have hac1 : σ1.vars "ac" = 0 := by rw [e1]; simp [preState]
  have har1 : σ1.arrs = σ.arrs := by rw [e1]; simp [preState]
  have ho1 : σ1.out = σ.out := by rw [e1]; simp [preState]
  have hrowT : ∀ j < 2 ^ (P.m * (bagL P.D (P.N - 1)).length),
      (σ1.arrs "TB").getD ((P.N - 1) * P.tabs + j) 0 = tbv P.I P.kk P.D (P.N - 1) j := by
    intro j hj
    rw [har1]; exact hN.tb (P.N - 1) (by omega) j (by rw [bpow]; exact hj)
  have hf := fLoop_spec (B := B) "so" "fn" "ac" orBody ["so", "ac"]
    (fun j a => if j < 2 ^ (P.m * (bagL P.D (P.N - 1)).length) then Nat.lor a
      ((σ1.arrs "TB").getD ((P.N - 1) * P.tabs + j) 0) else a)
    (fun _ a => a ≤ 1) 20 (2 ^ (P.m * (bagL P.D (P.N - 1)).length)) σ1 (by simp) (by simp)
    (by decide) hfn1 (by omega) (by rw [hac1]; omega)
    (fun j a h => by
      by_cases hj : j < 2 ^ (P.m * (bagL P.D (P.N - 1)).length)
      · simp only [hj, if_true]; rw [hrowT j hj]; exact lor_le_one h tbv_le_one
      · simp only [hj, if_false]; exact h) (by
      intro τ hA hlt hQ
      have hfr : ∀ y, y ∉ ["so", "ac"] → τ.vars y = σ1.vars y := hA.2
      have e4 : τ.vars "bs" = (P.N - 1) * P.tabs := by rw [hfr "bs" (by simp), hbs1]
      have e5 : τ.arrs "TB" = σ1.arrs "TB" := by rw [hA.1]
      have hlt' : τ.vars "so" < 2 ^ (P.m * (bagL P.D (P.N - 1)).length) := hlt
      have hb : (τ.arrs "TB").getD (τ.vars "bs" + τ.vars "so") 0 = tbv P.I P.kk P.D (P.N - 1)
          (τ.vars "so") := by rw [e4, e5]; exact hrowT _ hlt'
      obtain ⟨τ', r, hv, hA', hso, ho⟩ := orBody_run (B := B) τ (by rw [e4, e5]; omega)
        (by rw [e4]; omega) hQ (by rw [hb]; exact tbv_le_one) (by omega) (by omega)
        (by rw [e4]; omega)
      refine ⟨τ', r, ?_, agr_comp (S := ["so", "ac"]) hA hA' (by intro x hx; exact hx)
        (by intro x hx; simp at hx; simp; tauto), hso, ho⟩
      rw [hv, hb, if_pos hlt', hrowT _ hlt'])
  obtain ⟨σ2, r2, hv2, hA2, o2⟩ := hf
  have hfold := or_fold (2 ^ (P.m * (bagL P.D (P.N - 1)).length))
    (fun j => (σ1.arrs "TB").getD ((P.N - 1) * P.tabs + j) 0)
    (fun j hj => by
      show (σ1.arrs "TB").getD _ 0 ≤ 1
      rw [hrowT j hj]; exact tbv_le_one) _ le_rfl
  have hac2 : σ2.vars "ac" ≤ 1 := by
    rw [hv2, hac1, hfold]; split_ifs <;> omega
  have r3 : Run B (.write (V "ac")) σ2
      { σ2 with out := σ2.out ++ [σ2.vars "ac"] } (1 + (V "ac").size) :=
    Run.write (evalB_var (by omega))
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp [Expr.size]; unfold answerCost; omega), ?_⟩
  have hdp := dp_correct P.hD P.kk
  have hans : σ2.vars "ac" = if P.I.HasKFairSchedule P.kk then 1 else 0 := by
    rw [hv2, hac1, hfold]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨j, hj, hT1⟩
      rw [hrowT j hj] at hT1
      refine hdp.1 ⟨j, by rw [bpow]; exact hj, ?_⟩
      by_contra hn
      have hn' : ¬ TB P.I P.kk P.D (P.N - 1) j := hn
      rw [tbv_zero hn'] at hT1; omega
    · intro h
      obtain ⟨e, he, hTB⟩ := hdp.2 h
      rw [bpow] at he
      exact ⟨e, he, by rw [hrowT e he]; exact tbv_one (show TB P.I P.kk P.D (P.N - 1) e from hTB)⟩
  show σ2.out ++ [σ2.vars "ac"] = _
  rw [o2, ho1, hans]

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwDpRun` -/

section
/-!
The whole dynamic program: the loop over the nodes, then the answer.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP

variable {P : Params} {B : ℕ} {σ : Env}

/-- **The dynamic program.** -/
def dpCom : Com := .seq nodeLoop answerCom

/-- What the dynamic program costs. -/
def dpCost (P : Params) : ℕ := loopCost P + answerCost P

open Classical in
/-- **The dynamic program answers the question**, on an environment that meets the context. -/
theorem dpCom_run (hC : NC P B σ) :
    ∃ σ', Run B dpCom σ σ' (dpCost P) ∧
      σ'.out = σ.out ++ [if P.I.HasKFairSchedule P.kk then 1 else 0] := by
  obtain ⟨σ1, r1, hC1, hN1, -, ho1⟩ := nodeLoop_run hC
  obtain ⟨σ2, r2, ho2⟩ := answerCom_run hC1 hN1
  exact ⟨σ2, r1.seq r2, by rw [ho2, ho1]⟩

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwDpSetup` -/

section
/-!
The setup of the dynamic program: the scalars it reads, and the proof that the context it needs
holds once they are set.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.Machine.TwViol

variable {P : Params} {B : ℕ}

/-- The scalars the dynamic program reads. -/
def dpSetup : Com := seqs
  [ .assign "kk" (V "k"),
    .assign "w1" (add (V "w") (Expr.lit 1)),
    .assign "Tm" (.bin .shiftl (Expr.lit 1) (mul (V "m") (V "w1"))),
    .assign "N" (G "O" (Expr.lit 1)) ]

/-- The state after `dpSetup`. -/
def setupState (σ : Env) (kv wv tabs : ℕ) : Env :=
  (((σ.setVar "kk" kv).setVar "w1" (wv + 1)).setVar "Tm" tabs).setVar "N"
    ((σ.arrs "O").getD 1 0)

theorem dpSetup_run (σ : Env) (kv wv m : ℕ) (hk : σ.vars "k" = kv) (hw : σ.vars "w" = wv)
    (hm : σ.vars "m" = m) (hkB : kv + 3 < B) (hwB : wv + 3 < B) (hmw : m * (wv + 1) + 3 < B)
    (hT : 2 ^ (m * (wv + 1)) + 3 < B) (hO : 1 < (σ.arrs "O").length)
    (hO1 : (σ.arrs "O").getD 1 0 < B) :
    ∃ σ1, Run B dpSetup σ σ1 60 ∧ σ1 = setupState σ kv wv (2 ^ (m * (wv + 1))) := by
  have hmm : m ≤ m * (wv + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold dpSetup seqs
  run_vcg
  all_goals (try nrmA)
  all_goals try (first | omega | (simp only [hk, hw, hm, one_mul]; omega))
  all_goals (try simp only [setupState, hk, hw, hm, one_mul])

lemma tabs_eq (P : Params) : 2 ^ (P.m * (P.w + 1)) = P.tabs := by
  unfold Params.tabs Params.bs Params.wid
  rw [← pow_mul]

/-- **The context of the dynamic program holds after the setup.** -/
theorem nc_of_setup (P : Params) (σ : Env) (hn : σ.vars "n" = P.n) (hm : σ.vars "m" = P.m)
    (hmask : σ.vars "mask" = 2 ^ P.m - 1) (hbb : σ.vars "bb" = 2 ^ P.m)
    (hmn : σ.vars "mn" = P.m * P.n)
    (hX : σ.arrs "X" = P.y ++ [P.kk]) (hXB : ∀ v ∈ σ.arrs "X", v < B)
    (hO : ∀ k < P.D.length, (σ.arrs "O").getD (k + 1) 0 = P.D.getD k 0)
    (hOB : ∀ k < P.D.length, (σ.arrs "O").getD (k + 1) 0 < B)
    (lenO : 3 * P.N + 5 ≤ (σ.arrs "O").length) (lenSZ : P.N ≤ (σ.arrs "SZ").length)
    (lenBG : P.N * P.wid ≤ (σ.arrs "BG").length)
    (lenTB : P.N * P.tabs ≤ (σ.arrs "TB").length)
    (b1 : P.N * P.tabs + P.tabs + 32 < B) (b2 : P.N * P.wid + P.wid + 32 < B)
    (b3 : 3 * P.N + 32 < B) (b4 : P.tabs * P.bs + 32 < B)
    (b5 : P.wid * (P.wid * P.m + 1) + P.wid * P.m + P.m + 32 < B)
    (b6 : (σ.arrs "X").length + 32 < B) (b7 : (σ.arrs "O").length + 32 < B)
    (b8 : P.n + P.m + P.kk + 32 < B) (b9 : P.m * (P.wid + 1) + P.wid + 32 < B)
    (b10 : 2 ^ P.m + 32 < B) :
    NC P B (setupState σ P.kk P.w P.tabs) := by
  have hDl : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have harr : (setupState σ P.kk P.w P.tabs).arrs = σ.arrs := by simp [setupState, Env.setVar]
  have hN : (σ.arrs "O").getD 1 0 = P.N := by
    have := hO 0 (by omega)
    rw [show (0 : ℕ) + 1 = 1 from rfl] at this
    rw [this]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setupState, Env.setVar, hn]
  · simp [setupState, Env.setVar, hm]
  · simp [setupState, Env.setVar]
  · simp [setupState, Env.setVar, Params.wid]
  · simp [setupState, Env.setVar]
  · simp [setupState, Env.setVar, hmask]
  · simp [setupState, Env.setVar, hbb]
  · simp [setupState, Env.setVar, hmn]
  · simp only [setupState, vars_setVar, if_true, hN]
  · intro j hj; rw [harr, hX]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  · rw [harr, hX]; simp
  · intro v hv; rw [harr] at hv; exact hXB v hv
  · intro k hk; rw [harr]; exact hO k hk
  · intro k hk; rw [harr]; exact hOB k hk
  · rw [harr]; exact lenO
  · rw [harr]; exact lenSZ
  · rw [harr]; exact lenBG
  · rw [harr]; exact lenTB
  · exact b1
  · exact b2
  · exact b3
  · exact b4
  · exact b5
  · rw [harr]; exact b6
  · rw [harr]; exact b7
  · exact b8
  · exact b9
  · exact b10

end Lax117284Proofs.Machine.TwNode

end

/-! ### `Lax117284Proofs.Machine.TwMain1` -/

section
/-!
The main program of the treewidth algorithm: read the word, decide from its length whether the
memory of the decomposition step is admitted, and then either build the graph, run the cited
program on it through the interpreter and run the dynamic program on what it returns, or
enumerate the schedules.
-/

namespace Lax117284Proofs.Machine.TwMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol
open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding

variable {B : ℕ}

/-- The enumeration of the schedules, and its answer. -/
def brute : Com := .seq ClBrute.bruteCom (.write (V "bfans"))

/-- The answer for an instance with no day: `1` exactly when there is no client or `k = 0`. -/
def zeroCom : Com :=
  .ite (.eq (V "n") (Expr.lit 0)) (.write (Expr.lit 1))
    (.ite (.eq (V "k") (Expr.lit 0)) (.write (Expr.lit 1)) (.write (Expr.lit 0)))

/-- What the main program does when it does not run the dynamic program. -/
def brute0 : Com := .ite (.lt (Expr.lit 0) (V "m")) brute zeroCom

/-- The dynamic program. -/
def dpBranch : Com := .seq TwNode.dpSetup TwNode.dpCom

/-- The branch for a word that admits the decomposition step. -/
def guarded (prog : Program) : Com :=
  .seq (.seq TwPrep.maskCom (.seq TwGraph.gwCom (TwSetup.interpCom prog)))
    (.ite (.eq (G "O" (Expr.lit 0)) (Expr.lit 1)) dpBranch brute)

/-- **The main program.** -/
def mainCom (prog : Program) (cc plit : ℕ) : Com := seqs
  [ ClMain.readCom, TwPrep.prepCom cc plit,
    .ite (.lt (Expr.lit 0) (V "ok")) (guarded prog) brute0 ]

open Classical in
/-- **The enumeration answers.** -/
theorem brute_run {x : List ℕ} {I : Instance} {k : ℕ} (hdec : EncodesUniform x I k)
    (hB : 4 * x.length + 64 < B) (hX : ∀ v ∈ x, v < B) (σ : Env)
    (hXa : σ.arrs "X" = x) (hn : σ.vars "n" = I.clients) (hm : σ.vars "m" = I.days)
    (hk : σ.vars "k" = k) (hsc : σ.arrs "bfsc" = List.replicate (I.days * I.clients) 0)
    (ho : σ.out = []) :
    ∃ σ', Run B brute σ σ' (ClBrute.bruteCost I.days I.clients + 3) ∧
      σ'.out = [if I.HasKFairSchedule k then 1 else 0] := by
  have hbr := ClBrute.brute_spec I x k B hdec hB hX σ ⟨hXa, hn, hm, hk, hsc⟩
  obtain ⟨σ1, r1, hans, -, -, -, -, -, ho1⟩ := hbr
  have hv1 : (if I.HasKFairSchedule k then 1 else 0) < B := by split_ifs <;> omega
  obtain ⟨σ2, r2, e2⟩ : ∃ σ2, Run B (.write (V "bfans")) σ1 σ2 3 ∧
      σ2 = { σ1 with out := σ1.out ++ [σ1.vars "bfans"] } := by
    have := Run.write (B := B) (σ := σ1) (e := V "bfans") (v := σ1.vars "bfans")
      (evalB_var (by rw [hans]; exact hv1))
    exact ⟨_, this.mono (by simp [Expr.size]), rfl⟩
  refine ⟨σ2, r1.seq r2, ?_⟩
  rw [e2]; simp [ho1, ho, hans]

open Classical in
/-- **The answer for an instance with no day**, in a constant number of steps. -/
theorem zero_run {I : Instance} {k : ℕ} (hd : I.days = 0) (hB : 1 < B) (σ : Env)
    (hn : σ.vars "n" = I.clients) (hk : σ.vars "k" = k) (hnB : I.clients < B) (hkB : k < B)
    (ho : σ.out = []) :
    ∃ σ', Run B zeroCom σ σ' 12 ∧ σ'.out = [if I.HasKFairSchedule k then 1 else 0] := by
  have hw1 : ∀ v, v < B → Run B (.write (Expr.lit v)) σ { σ with out := σ.out ++ [v] } 2 :=
    fun v hv => (Run.write (B := B) (σ := σ) (e := Expr.lit v) (v := v) (evalB_lit hv)).mono
      (by simp [Expr.size])
  have hiff := hasK_days_zero I hd k
  by_cases hc : I.clients = 0
  · have hcond : (Cond.eq (V "n") (Expr.lit 0)).evalB B σ = some true := by
      rw [evalB_condEq (evalB_var (by rw [hn]; exact hnB)) (evalB_lit (by omega))]
      simp [hn, hc]
    refine ⟨_, (Run.ite_true hcond (hw1 1 hB)).mono ?_, ?_⟩
    · simp [Cond.size, Expr.size]
    · have : I.HasKFairSchedule k := hiff.2 (Or.inl hc)
      simp [ho, this]
  · have hcond : (Cond.eq (V "n") (Expr.lit 0)).evalB B σ = some false := by
      rw [evalB_condEq (evalB_var (by rw [hn]; exact hnB)) (evalB_lit (by omega))]
      simp [hn, hc]
    by_cases hk0 : k = 0
    · have hcond2 : (Cond.eq (V "k") (Expr.lit 0)).evalB B σ = some true := by
        rw [evalB_condEq (evalB_var (by rw [hk]; exact hkB)) (evalB_lit (by omega))]
        simp [hk, hk0]
      have hin := Run.ite_true (d := .write (Expr.lit 0)) hcond2 (hw1 1 hB)
      refine ⟨_, (Run.ite_false (c := .write (Expr.lit 1)) hcond hin).mono ?_, ?_⟩
      · simp [Cond.size, Expr.size]
      · have : I.HasKFairSchedule k := hiff.2 (Or.inr hk0)
        simp [ho, this]
    · have hcond2 : (Cond.eq (V "k") (Expr.lit 0)).evalB B σ = some false := by
        rw [evalB_condEq (evalB_var (by rw [hk]; exact hkB)) (evalB_lit (by omega))]
        simp [hk, hk0]
      have hin := Run.ite_false (c := .write (Expr.lit 1)) hcond2 (hw1 0 (by omega))
      refine ⟨_, (Run.ite_false (c := .write (Expr.lit 1)) hcond hin).mono ?_, ?_⟩
      · simp [Cond.size, Expr.size]
      · have : ¬ I.HasKFairSchedule k := fun h => by
          rcases hiff.1 h with h | h <;> omega
        simp [ho, this]

open Classical in
/-- **The answer when the decomposition step is not used**: the enumeration for an instance with a
day, a constant-time answer for one without. -/
theorem brute0_run {x : List ℕ} {I : Instance} {k : ℕ} (hdec : EncodesUniform x I k)
    (hB : 4 * x.length + 64 < B) (hX : ∀ v ∈ x, v < B) (σ : Env)
    (hXa : σ.arrs "X" = x) (hn : σ.vars "n" = I.clients) (hm : σ.vars "m" = I.days)
    (hk : σ.vars "k" = k) (hsc : σ.arrs "bfsc" = List.replicate (I.days * I.clients) 0)
    (hnB : I.clients + 8 < B) (hmB : I.days + 8 < B) (hkB : k < B)
    (ho : σ.out = []) :
    ∃ σ', Run B brute0 σ σ'
        (1 + 3 + (if 0 < I.days then ClBrute.bruteCost I.days I.clients + 3 else 12)) ∧
      σ'.out = [if I.HasKFairSchedule k then 1 else 0] := by
  by_cases hd : 0 < I.days
  · obtain ⟨σ', r, ho'⟩ := brute_run hdec hB hX σ hXa hn hm hk hsc ho
    have hcond : (Cond.lt (Expr.lit 0) (V "m")).evalB B σ = some true := by
      rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (by rw [hm]; omega))]
      simp [hm, hd]
    refine ⟨σ', (Run.ite_true hcond r).mono ?_, ho'⟩
    simp [Cond.size, Expr.size, if_pos hd]
  · have hd0 : I.days = 0 := by omega
    obtain ⟨σ', r, ho'⟩ := zero_run (B := B) hd0 (by omega) σ hn hk (by omega) hkB ho
    have hcond : (Cond.lt (Expr.lit 0) (V "m")).evalB B σ = some false := by
      rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (by rw [hm]; omega))]
      simp [hm, hd0]
    refine ⟨σ', (Run.ite_false hcond r).mono ?_, ho'⟩
    simp [Cond.size, Expr.size, if_neg hd]

end Lax117284Proofs.Machine.TwMain

end

/-! ### `Lax117284Proofs.Machine.TwMain2` -/

section
/-!
The main program, phase by phase: the reading and the preparation.
-/

namespace Lax117284Proofs.Machine.TwMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol
open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding

variable {B : ℕ}

/-- **What is known of an environment**: the arrays outside `T` are the zeros the machine started
with, and the scalars outside `V0` are zero. -/
structure W (ext : String → ℕ) (T V0 : List String) (σ : Env) : Prop where
  arrs : ∀ a, a ∉ T → σ.arrs a = List.replicate (ext a) 0
  vars : ∀ v, v ∉ V0 → σ.vars v = 0

/-- The scalars the reading writes. -/
def VR : List String := ["n", "m", "L", "rt", "k", "rv"]

theorem phaseR {x : List ℕ} {I : Instance} {k : ℕ} (hdec : EncodesUniform x I k)
    (hL : x.length < B) (hX : ∀ v ∈ x, v < B) (ext : String → ℕ) (hext : ext "X" = x.length)
    (σ0 : Env) (hin : σ0.inp = x) (hout : σ0.out = []) (hW : W ext [] [] σ0) :
    ∃ σ1, Run B ClMain.readCom σ0 σ1 (24 * x.length + 60) ∧ ClBuild.Ctx0 I x k σ1 ∧
      σ1.vars "L" = x.length ∧ σ1.inp = [] ∧ σ1.out = [] ∧ W ext ["X"] VR σ1 := by
  obtain ⟨σ1, r, hC, hLv, hi, ho, hA, hV⟩ := ClMain.readCom_spec hdec hL hX σ0
    ⟨hin, hout, by rw [hW.arrs "X" (by simp), hext]; simp⟩
  refine ⟨σ1, r, hC, hLv, hi, ho, ⟨fun a ha => ?_, fun v hv => ?_⟩⟩
  · have : a ≠ "X" := by simpa using ha
    rw [hA a this, hW.arrs a (by simp)]
  · have hv' : v ∉ ["n", "m", "L", "rt", "k", "rv"] := hv
    rw [hV v hv', hW.vars v (by simp)]

/-- What the preparation costs. -/
def Kprep (L lg : ℕ) : ℕ :=
  40 + ((20 + 10 + 4) * L + 6) + 20 + ((40 + 10 + 4) * (lg + 1) + 6) + 100

theorem phaseP (cc plit : ℕ) (hcc : 1 ≤ cc) {x : List ℕ} {I : Instance} {k : ℕ}
    (σ1 : Env) (hn : σ1.vars "n" = I.clients) (hm : σ1.vars "m" = I.days)
    (hLv : σ1.vars "L" = x.length) (hL0 : 0 < x.length)
    (hmn : I.days * I.clients + 8 < B) (hnB : I.clients + 8 < B) (hmB : I.days + 8 < B)
    (hLB : x.length + 8 < B)
    (hge : TwPrep.geE cc I.days (Nat.log 2 x.length) + 8 < B) (hccB : 2 * cc + 8 < B)
    (hplB : plit + 8 < B)
    (hwp : (2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit + 8 < B)
    (hP : 2 ^ ((2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit) + 8 < B) :
    ∃ σ2, Run B (TwPrep.prepCom cc plit) σ1 σ2 (Kprep x.length (Nat.log 2 x.length)) ∧
      σ2.vars "mn" = I.days * I.clients ∧ σ2.vars "lg" = Nat.log 2 x.length ∧
      σ2.vars "wc" = TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧
      σ2.vars "ok" = (if 0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days
        then 1 else 0) ∧
      σ2.vars "w" = TwPrep.wcnt cc I.days (Nat.log 2 x.length) - 1 ∧
      σ2.vars "wp" = (2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit ∧
      σ2.vars "P" = 2 ^ ((2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit) ∧
      (∀ v, v ∉ TwPrep.SPrep → σ2.vars v = σ1.vars v) ∧ σ2.arrs = σ1.arrs ∧
      σ2.out = σ1.out := by
  have hlgL : Nat.log 2 x.length ≤ x.length := Nat.log_le_self 2 _
  obtain ⟨hw1, hw2, hw3⟩ := TwPrep.wcnt_spec hcc I.days (Nat.log 2 x.length)
  obtain ⟨σa, ra, ea⟩ := TwPrep.prepPre_run (B := B) σ1 I.clients I.days hn hm (by omega) (by omega)
    (by omega)
  have hva : ∀ v, v ≠ "mn" → v ≠ "lg" → σa.vars v = σ1.vars v := by
    intro v h1 h2; rw [ea]; simp [Env.setVar, h1, h2]
  have hLa : σa.vars "L" = x.length := by rw [hva "L" (by decide) (by decide), hLv]
  have hlga : σa.vars "lg" = 0 := by rw [ea]; simp [Env.setVar]
  obtain ⟨σb, rb, hlgb, Ab, ob⟩ := TwPrep.lgLoop_run (B := B) σa x.length hL0 hLa (by omega) hlga
  have hvb : ∀ v, v ∉ ["j", "lg"] → σb.vars v = σa.vars v := Ab.2
  obtain ⟨σc, rc, ec⟩ := TwPrep.prepMid_run (B := B) σb (Nat.log 2 x.length) hlgb (by omega)
  have hvc : ∀ v, v ≠ "lg1" → v ≠ "wc" → σc.vars v = σb.vars v := by
    intro v h1 h2; rw [ec]; simp [Env.setVar, h1, h2]
  have hmc : σc.vars "m" = I.days := by
    rw [hvc "m" (by decide) (by decide), hvb "m" (by decide), hva "m" (by decide) (by decide), hm]
  have hlg1c : σc.vars "lg1" = Nat.log 2 x.length + 1 := by rw [ec]; simp [Env.setVar]
  have hwcc : σc.vars "wc" = 0 := by rw [ec]; simp [Env.setVar]
  obtain ⟨σd, rd, hwcd, Ad, od⟩ := TwPrep.wcLoop_run (B := B) cc σc I.days (Nat.log 2 x.length) hcc
    (by omega) hmc hlg1c hwcc (by omega) (by omega)
  have hvd : ∀ v, v ∉ ["j", "wc"] → σd.vars v = σc.vars v := Ad.2
  have hme : σd.vars "m" = I.days := by rw [hvd "m" (by decide), hmc]
  have hlgd : σd.vars "lg" = Nat.log 2 x.length := by
    rw [hvd "lg" (by decide), hvc "lg" (by decide) (by decide), hlgb]
  obtain ⟨σe, re, hok, hw, hwp', hP', Ae, oe⟩ := TwPrep.prepPost_run (B := B) cc plit σd
    (TwPrep.wcnt cc I.days (Nat.log 2 x.length)) I.days (Nat.log 2 x.length) hwcd hme hlgd
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨σe, ?_, ?_, ?_, ?_, hok, hw, hwp', hP', ?_, ?_, ?_⟩
  · have := ra.seq (rb.seq (rc.seq (rd.seq re)))
    exact this.mono (by unfold Kprep; omega)
  · rw [Ae.2 "mn" (by simp), hvd "mn" (by decide), hvc "mn" (by decide) (by decide),
      hvb "mn" (by decide), ea]; simp [Env.setVar]
  · rw [Ae.2 "lg" (by simp), hlgd]
  · rw [Ae.2 "wc" (by simp), hwcd]
  · intro v hv
    have h1 : v ∉ ["ok", "w", "wp", "P"] := fun h => hv (by
      simp only [TwPrep.SPrep, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
    have h2 : v ∉ ["j", "wc"] := fun h => hv (by
      simp only [TwPrep.SPrep, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
    have h3 : v ∉ ["j", "lg"] := fun h => hv (by
      simp only [TwPrep.SPrep, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
    have h4 : v ≠ "lg1" := fun h => hv (by simp [TwPrep.SPrep, h])
    have h5 : v ≠ "wc" := fun h => hv (by simp [TwPrep.SPrep, h])
    have h6 : v ≠ "mn" := fun h => hv (by simp [TwPrep.SPrep, h])
    have h7 : v ≠ "lg" := fun h => hv (by simp [TwPrep.SPrep, h])
    rw [Ae.2 v h1, hvd v h2, hvc v h4 h5, hvb v h3, hva v h6 h7]
  · rw [Ae.1, Ad.1, show σc.arrs = σb.arrs by rw [ec]; simp [Env.setVar], Ab.1,
      show σa.arrs = σ1.arrs by rw [ea]; simp [Env.setVar]]
  · rw [oe, od, show σc.out = σb.out by rw [ec]; simp [Env.setVar], ob,
      show σa.out = σ1.out by rw [ea]; simp [Env.setVar]]

end Lax117284Proofs.Machine.TwMain

end

/-! ### `Lax117284Proofs.Machine.TwMain3` -/

section
/-!
The main program, phase by phase: the word of the graph and the run of the decomposition step.
-/

namespace Lax117284Proofs.Machine.TwMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol
open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding
open Lax117284Proofs.Machine.TwRam (opcode fa fb fc Small)

variable {B : ℕ}

/-- The scalars the guarded branch writes before the choice of the answer. -/
def VG : List String := ["mask", "bb"] ++ TwGraph.SGW ++ TwSetup.SI

/-- The arrays it writes. -/
def AG : List String := ["Y", "OP", "XA", "XB", "XC", "M", "O"]

/-- What the graph and the run of the decomposition step cost. -/
def Kgi (m n t : ℕ) (plen : ℕ) : ℕ :=
  30 + ((214 * m + 90 + 20 + 4) * (n * n) + 6 + 60) + (13 * plen + 1 + 30 + 250 * (t + 1))

theorem phaseGI {x : List ℕ} {I : Instance} {k : ℕ} (hdec : EncodesUniform x I k)
    (prog : Program) (ext : String → ℕ) (Wp Pn OL w t : ℕ) (z : List ℕ) (σ2 : Env)
    (hW : W ext ["X"] (VR ++ TwPrep.SPrep) σ2)
    (hXa : σ2.arrs "X" = x) (hn : σ2.vars "n" = I.clients) (hm : σ2.vars "m" = I.days)
    (hmn : σ2.vars "mn" = I.days * I.clients) (hw2 : σ2.vars "w" = w)
    (hwp : σ2.vars "wp" = Wp) (hP : σ2.vars "P" = Pn)
    (hextY : ext "Y" = I.clients * I.clients + 2) (hextOP : ext "OP" = prog.length)
    (hextXA : ext "XA" = prog.length) (hextXB : ext "XB" = prog.length)
    (hextXC : ext "XC" = prog.length) (hextM : ext "M" = Pn) (hextO : ext "O" = OL)
    (hPn : Pn = 2 ^ Wp) (hsm : Small Wp prog)
    (hRuns : RunsTo Wp prog (TwGraph.gwList x I.clients I.days ++ [w]) z t) (hOLt : t < OL)
    (hlit : ∀ ins ∈ prog, opcode ins + 3 < B ∧ fa ins + 3 < B ∧ fb ins + 3 < B ∧ fc ins + 3 < B)
    -- the bounds
    (h2m : 2 ^ I.days + 8 < B) (hnB : I.clients + 8 < B) (hmB : I.days + 8 < B)
    (hnn : I.clients * I.clients + 8 < B) (hLX : x.length + 8 < B) (hXB : ∀ v ∈ x, v < B)
    (hwB : w + 8 < B)
    (hyP : ∀ v ∈ TwGraph.gwList x I.clients I.days ++ [w], v < Pn)
    (hyPn : I.clients * I.clients + 2 < Pn)
    (bPP : Pn * Pn < B) (b2 : Pn + Pn < B)
    (bnd : prog.length + OL + (I.clients * I.clients + 2) + Pn + 24 < B) (hOL : 0 < OL) :
    ∃ σ5, Run B (.seq TwPrep.maskCom (.seq TwGraph.gwCom (TwSetup.interpCom prog))) σ2 σ5
        (Kgi I.days I.clients t prog.length) ∧
      z = (σ5.arrs "O").take (σ5.vars "ol") ∧ (σ5.arrs "O").length = OL ∧
      σ5.arrs "Y" = TwGraph.gwList x I.clients I.days ++ [w] ∧
      σ5.arrs "X" = x ∧ W ext ("X" :: AG) (VR ++ TwPrep.SPrep ++ VG) σ5 ∧
      (∀ v, v ∉ VG → σ5.vars v = σ2.vars v) ∧ σ5.vars "mask" = 2 ^ I.days - 1 ∧
      σ5.vars "bb" = 2 ^ I.days ∧ σ5.out = σ2.out := by
  have hmB' : I.days + 3 < B := by omega
  obtain ⟨σ3, r3, e3⟩ := TwPrep.maskCom_run (B := B) σ2 I.days hm (by omega)
  have hv3 : ∀ v, v ≠ "mask" → v ≠ "bb" → σ3.vars v = σ2.vars v := by
    intro v h1 h2; rw [e3]; simp [Env.setVar, h1, h2]
  have ha3 : σ3.arrs = σ2.arrs := by rw [e3]; simp [Env.setVar]
  have ho3 : σ3.out = σ2.out := by rw [e3]; simp [Env.setVar]
  have hmask3 : σ3.vars "mask" = 2 ^ I.days - 1 := by rw [e3]; simp [Env.setVar]
  have hXlen : 2 + 2 * (I.days * I.clients) + 1 ≤ x.length := by
    have := ClientsWord.len_eq hdec; omega
  have hY3 : σ3.arrs "Y" = List.replicate (I.clients * I.clients + 2) 0 := by
    rw [ha3, hW.arrs "Y" (by simp), hextY]
  obtain ⟨σ4, r4, hY4, hoth4, hv4, ho4⟩ := TwGraph.gwCom_run (B := B) x I.clients I.days σ3
    (by rw [ha3]; exact hXa) (by rw [hv3 "n" (by decide) (by decide)]; exact hn)
    (by rw [hv3 "m" (by decide) (by decide)]; exact hm)
    (by rw [hv3 "mn" (by decide) (by decide)]; exact hmn) hmask3 hY3 hXlen hXB (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (by rw [hv3 "w" (by decide) (by decide), hw2]; omega)
  have hw4 : σ4.vars "w" = w := by
    rw [hv4 "w" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD]), hv3 "w" (by decide) (by decide), hw2]
  have hv34 : ∀ v, v ∉ TwGraph.SGW → v ≠ "mask" → v ≠ "bb" → σ4.vars v = σ2.vars v := by
    intro v h1 h2 h3; rw [hv4 v h1, hv3 v h2 h3]
  have hZ4 : ∀ a, a ≠ "Y" → σ4.arrs a = σ2.arrs a := by
    intro a ha; rw [hoth4 a ha, ha3]
  have hyl : (TwGraph.gwList x I.clients I.days ++ [w]).length = I.clients * I.clients + 2 := by
    simp [TwGraph.gwList_length]; omega
  have hn4 : σ4.vars "n" = I.clients := by
    rw [hv34 "n" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD]) (by decide) (by decide), hn]
  have hY4' : σ4.arrs "Y" = TwGraph.gwList x I.clients I.days ++ [w] := by rw [hY4, hv3 "w" (by decide) (by decide), hw2]
  obtain ⟨σ5, r5, hz, hOlen, hv5, ha5, ho5⟩ := TwSetup.interpCom_run (B := B) prog
    (TwGraph.gwList x I.clients I.days ++ [w]) z I.clients Pn Wp OL t σ4 hY4' hn4 hyl
    (by rw [hZ4 "OP" (by decide), hW.arrs "OP" (by simp), hextOP])
    (by rw [hZ4 "XA" (by decide), hW.arrs "XA" (by simp), hextXA])
    (by rw [hZ4 "XB" (by decide), hW.arrs "XB" (by simp), hextXB])
    (by rw [hZ4 "XC" (by decide), hW.arrs "XC" (by simp), hextXC])
    (by rw [hZ4 "M" (by decide), hW.arrs "M" (by simp), hextM])
    (by rw [hZ4 "O" (by decide), hW.arrs "O" (by simp), hextO])
    (by rw [hv34 "pc" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD]) (by decide) (by decide)]
        exact hW.vars "pc" (by simp [VR, TwPrep.SPrep]))
    (by rw [hv34 "cur" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD]) (by decide) (by decide)]
        exact hW.vars "cur" (by simp [VR, TwPrep.SPrep]))
    (by rw [hv34 "ol" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD]) (by decide) (by decide)]
        exact hW.vars "ol" (by simp [VR, TwPrep.SPrep]))
    (by rw [hv34 "P" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD]) (by decide) (by decide), hP])
    (by rw [hv34 "wp" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD]) (by decide) (by decide), hwp])
    hPn hsm hyP (by rw [hyl]; exact hyPn) bPP b2 (by rw [hyl]; exact bnd) hOL hOLt hlit hRuns
  have hZ5 : ∀ a, a ∉ AG → σ5.arrs a = σ2.arrs a := by
    intro a ha
    rw [ha5 a (fun h => ha (by simp only [AG, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)),
      hZ4 a (fun h => ha (by simp [AG, h]))]
  refine ⟨σ5, (r3.seq (r4.seq r5)).mono (by unfold Kgi; omega), hz, hOlen, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [ha5 "Y" (by decide), hY4']
  · rw [ha5 "X" (by decide), hZ4 "X" (by decide), hXa]
  · intro a ha
    have h1 : a ∉ AG := fun h => ha (by simp [h])
    have h2 : a ∉ ["X"] := fun h => ha (by simp at h ⊢; tauto)
    rw [hZ5 a h1, hW.arrs a h2]
  · intro v hv
    have h1 : v ∉ TwSetup.SI := fun h => hv (by simp [VG, h])
    have h2 : v ∉ TwGraph.SGW := fun h => hv (by simp [VG, h])
    have h3 : v ≠ "mask" := fun h => hv (by simp [VG, h])
    have h4 : v ≠ "bb" := fun h => hv (by simp [VG, h])
    have h5 : v ∉ VR ++ TwPrep.SPrep := fun h => hv (by simp at h ⊢; tauto)
    rw [hv5 v h1, hv34 v h2 h3 h4, hW.vars v h5]
  · intro v hv
    have h1 : v ∉ TwSetup.SI := fun h => hv (by simp [VG, h])
    have h2 : v ∉ TwGraph.SGW := fun h => hv (by simp [VG, h])
    have h3 : v ≠ "mask" := fun h => hv (by simp [VG, h])
    have h4 : v ≠ "bb" := fun h => hv (by simp [VG, h])
    rw [hv5 v h1, hv34 v h2 h3 h4]
  · rw [hv5 "mask" (by simp [TwSetup.SI]), hv4 "mask" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD]), hmask3]
  · rw [hv5 "bb" (by simp [TwSetup.SI]), hv4 "bb" (by simp [TwGraph.SGW, TwGraph.SG, TwViol.SD])]
    rw [e3]; simp [Env.setVar]
  · rw [ho5, ho4, ho3]

end Lax117284Proofs.Machine.TwMain

end

/-! ### `Lax117284Proofs.Machine.TwMain4` -/

section
/-!
The main program, phase by phase: the dynamic program on what the decomposition step returned.
-/

namespace Lax117284Proofs.Machine.TwMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol
open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding
open Lax117284Proofs.Machine.TwNode (Params NC)

variable {B : ℕ}

lemma getD_of_take {a z : List ℕ} {n i : ℕ} (h : z = a.take n) (hi : i < z.length) :
    a.getD i 0 = z.getD i 0 := by
  subst h
  have h1 : i < a.length := by
    have := hi; simp only [List.length_take] at this; omega
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ hi, List.getElem_take]

open Classical in
/-- **The dynamic program answers**, on the environment the decomposition step leaves. -/
theorem phaseDP (P : Params) (ext : String → ℕ) (z : List ℕ) (σ5 : Env)
    (hzD : z = 1 :: P.D) (hz : z = (σ5.arrs "O").take (σ5.vars "ol"))
    (hzB : ∀ v ∈ z, v < B)
    (hW : W ext ("X" :: AG) (VR ++ TwPrep.SPrep ++ VG) σ5)
    (hXa : σ5.arrs "X" = P.y ++ [P.kk]) (hn : σ5.vars "n" = P.n) (hm : σ5.vars "m" = P.m)
    (hk : σ5.vars "k" = P.kk) (hw : σ5.vars "w" = P.w) (hmn : σ5.vars "mn" = P.m * P.n)
    (hmask : σ5.vars "mask" = 2 ^ P.m - 1) (hbb : σ5.vars "bb" = 2 ^ P.m)
    (hXB : ∀ v ∈ σ5.arrs "X", v < B)
    (hextSZ : P.N ≤ ext "SZ") (hextBG : P.N * P.wid ≤ ext "BG")
    (hextTB : P.N * P.tabs ≤ ext "TB") (hlenO : 3 * P.N + 5 ≤ (σ5.arrs "O").length)
    (b1 : P.N * P.tabs + P.tabs + 32 < B) (b2 : P.N * P.wid + P.wid + 32 < B)
    (b3 : 3 * P.N + 32 < B) (b4 : P.tabs * P.bs + 32 < B)
    (b5 : P.wid * (P.wid * P.m + 1) + P.wid * P.m + P.m + 32 < B)
    (b6 : (σ5.arrs "X").length + 32 < B) (b7 : (σ5.arrs "O").length + 32 < B)
    (b8 : P.n + P.m + P.kk + 32 < B) (b9 : P.m * (P.wid + 1) + P.wid + 32 < B)
    (b10 : 2 ^ P.m + 32 < B) :
    ∃ σ7, Run B dpBranch σ5 σ7 (60 + TwNode.dpCost P) ∧
      σ7.out = σ5.out ++ [if P.I.HasKFairSchedule P.kk then 1 else 0] := by
  have hDl : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have hwid : P.wid = P.w + 1 := rfl
  have hO : ∀ j < P.D.length, (σ5.arrs "O").getD (j + 1) 0 = P.D.getD j 0 := by
    intro j hj
    have hzl : j + 1 < z.length := by rw [hzD]; simp; omega
    rw [getD_of_take hz hzl, hzD]; simp
  have hOB : ∀ j < P.D.length, (σ5.arrs "O").getD (j + 1) 0 < B := by
    intro j hj
    rw [hO j hj]
    have hmem : P.D.getD j 0 ∈ z := by
      rw [hzD]
      have : P.D.getD j 0 ∈ P.D := by
        rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
      exact List.mem_cons_of_mem _ this
    exact hzB _ hmem
  have hSZ : (σ5.arrs "SZ").length = ext "SZ" := by rw [hW.arrs "SZ" (by simp [AG])]; simp
  have hBG : (σ5.arrs "BG").length = ext "BG" := by rw [hW.arrs "BG" (by simp [AG])]; simp
  have hTB : (σ5.arrs "TB").length = ext "TB" := by rw [hW.arrs "TB" (by simp [AG])]; simp
  have hN : (σ5.arrs "O").getD 1 0 = P.N := by
    have := hO 0 (by omega)
    rw [show (0 : ℕ) + 1 = 1 from rfl] at this
    rw [this]; rfl
  have htab : 2 ^ (P.m * (P.w + 1)) = P.tabs := TwNode.tabs_eq P
  obtain ⟨σ6, r6, e6⟩ := TwNode.dpSetup_run (B := B) σ5 P.kk P.w P.m hk hw hm (by omega) (by omega)
    (by have : P.m * (P.w + 1) ≤ P.m * (P.wid + 1) := Nat.mul_le_mul_left _ (by unfold Params.wid; omega)
        omega)
    (by rw [htab]; omega) (by omega) (by rw [hN]; omega)
  rw [htab] at e6
  have hNC : NC P B σ6 := by
    rw [e6]
    exact TwNode.nc_of_setup P σ5 hn hm hmask hbb hmn hXa hXB hO hOB hlenO (by omega) (by omega)
      (by omega) b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  obtain ⟨σ7, r7, ho7⟩ := TwNode.dpCom_run hNC
  refine ⟨σ7, (r6.seq r7).mono (by omega), ?_⟩
  rw [ho7, e6]; simp [TwNode.setupState, Env.setVar]

end Lax117284Proofs.Machine.TwMain

end

/-! ### `Lax117284Proofs.Machine.TwMain5` -/

section
/-!
The main program is correct: it answers `1` exactly for the instances that have a fair schedule,
at a cost that depends on which branch it takes.
-/

namespace Lax117284Proofs.Machine.TwMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol
open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding
open Lax117284Proofs.Machine.TwRam (opcode fa fb fc Small)
open Lax117284Proofs.Machine.TwNode (Params)

variable {B : ℕ}

/-- **The numbers the dynamic program needs, for the decomposition `D`.** -/
structure DPB (B Lx OL Kdp : ℕ) (ext : String → ℕ) (P : Params) : Prop where
  sz : P.N ≤ ext "SZ"
  bg : P.N * P.wid ≤ ext "BG"
  tb : P.N * P.tabs ≤ ext "TB"
  lenO : 3 * P.N + 5 ≤ OL
  b1 : P.N * P.tabs + P.tabs + 32 < B
  b2 : P.N * P.wid + P.wid + 32 < B
  b3 : 3 * P.N + 32 < B
  b4 : P.tabs * P.bs + 32 < B
  b5 : P.wid * (P.wid * P.m + 1) + P.wid * P.m + P.m + 32 < B
  b6 : Lx + 32 < B
  b7 : OL + 32 < B
  b8 : P.n + P.m + P.kk + 32 < B
  b9 : P.m * (P.wid + 1) + P.wid + 32 < B
  b10 : 2 ^ P.m + 32 < B
  cost : 60 + TwNode.dpCost P ≤ Kdp

/-- **The numbers the guarded branch needs.** -/
structure GB (B : ℕ) (prog : Program) (x : List ℕ) (n m OL Wp Pn w : ℕ) : Prop where
  h2m : 2 ^ m + 8 < B
  hnn : n * n + 8 < B
  hwB : w + 8 < B
  hsm : Small Wp prog
  hyP : ∀ v ∈ TwGraph.gwList x n m ++ [w], v < Pn
  hyPn : n * n + 2 < Pn
  bPP : Pn * Pn < B
  b2 : Pn + Pn < B
  bnd : prog.length + OL + (n * n + 2) + Pn + 24 < B
  hOL : 0 < OL
  hlit : ∀ ins ∈ prog, opcode ins + 3 < B ∧ fa ins + 3 < B ∧ fb ins + 3 < B ∧ fc ins + 3 < B
  hPn : Pn = 2 ^ Wp

open Classical in
/-- **The cost of the main program.** -/
noncomputable def Kmain (L lg m n t plen Kdp : ℕ) (g : Prop) (z0 : Prop) : ℕ :=
  (24 * L + 60) + (Kprep L lg + (10 + (if g then
    (Kgi m n t plen + (10 + (if z0 then ClBrute.bruteCost m n + 3 else Kdp))) else
      (4 + (if 0 < m then ClBrute.bruteCost m n + 3 else 12)))))

open Classical in
/-- **The main program answers correctly.** -/
theorem main_run {x y0 : List ℕ} {I : Instance} {k : ℕ} (hx : x = y0 ++ [k])
    (hy : EncodesInstance y0 I) (prog : Program) (cc plit : ℕ) (hcc : 1 ≤ cc)
    (ext : String → ℕ) (OL Kdp : ℕ) (z : List ℕ) (t : ℕ) (σ0 : Env)
    (hin : σ0.inp = x) (hout : σ0.out = []) (hW0 : W ext [] [] σ0)
    (hextX : ext "X" = x.length) (hextY : ext "Y" = I.clients * I.clients + 2)
    (hextOP : ext "OP" = prog.length) (hextXA : ext "XA" = prog.length)
    (hextXB : ext "XB" = prog.length) (hextXC : ext "XC" = prog.length)
    (hextM : ext "M" = 2 ^ ((2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit))
    (hextO : ext "O" = OL) (hextbf : ext "bfsc" = I.days * I.clients)
    (hL : x.length + 8 < B) (hbr : 4 * x.length + 64 < B) (hXB : ∀ v ∈ x, v < B)
    (hn : I.clients + 8 < B) (hm : I.days + 8 < B) (hmn : I.days * I.clients + 8 < B)
    (hge : TwPrep.geE cc I.days (Nat.log 2 x.length) + 8 < B) (hccB : 2 * cc + 8 < B)
    (hplB : plit + 8 < B)
    (hwp : (2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit + 8 < B)
    (hPB : 2 ^ ((2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit) + 8 < B)
    (hG : 0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days →
      GB B prog x I.clients I.days OL ((2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit)
        (2 ^ ((2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit))
        (TwPrep.wcnt cc I.days (Nat.log 2 x.length) - 1))
    (hcit : 0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days →
      RunsTo ((2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit) prog
        (TwGraph.gwList x I.clients I.days ++
          [TwPrep.wcnt cc I.days (Nat.log 2 x.length) - 1]) z t ∧ t < OL ∧
      (z = [0] ∨ ∃ D, z = 1 :: D))
    (hDP : ∀ D (hD : Lax117284.Bodlaender.NiceDecomposition I
        (TwPrep.wcnt cc I.days (Nat.log 2 x.length) - 1) D), z = 1 :: D →
      DPB B x.length OL Kdp ext ⟨I, y0, k, D, TwPrep.wcnt cc I.days (Nat.log 2 x.length) - 1, hy, hD⟩)
    (hnice : ∀ D, 0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days → z = 1 :: D →
      Lax117284.Bodlaender.NiceDecomposition I
        (TwPrep.wcnt cc I.days (Nat.log 2 x.length) - 1) D) :
    ∃ σ', Run B (mainCom prog cc plit) σ0 σ'
        (Kmain x.length (Nat.log 2 x.length) I.days I.clients t prog.length Kdp
          (0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days) (z = [0])) ∧
      σ'.out = [if I.HasKFairSchedule k then 1 else 0] := by
  have hdec : EncodesUniform x I k := ⟨y0, hx, hy⟩
  have hlen := ClientsWord.len_eq hdec
  have hL0 : 0 < x.length := by omega
  obtain ⟨σ1, r1, hC1, hL1, hin1, hout1, hW1⟩ := phaseR hdec (by omega) hXB ext hextX σ0 hin hout
    hW0
  obtain ⟨σ2, r2, hmn2, hlg2, hwc2, hok2, hw2, hwp2, hP2, hfr2, har2, ho2⟩ := phaseP (B := B) (k := 0) cc
    plit hcc σ1 hC1.n hC1.m hL1 hL0 hmn hn hm hL hge hccB hplB hwp hPB
  have hn2 : σ2.vars "n" = I.clients := by rw [hfr2 "n" (by decide)]; exact hC1.n
  have hm2 : σ2.vars "m" = I.days := by rw [hfr2 "m" (by decide)]; exact hC1.m
  have hk2 : σ2.vars "k" = k := by rw [hfr2 "k" (by decide)]; exact hC1.k
  have hX2 : σ2.arrs "X" = x := by rw [har2]; exact hC1.X
  have hW2 : W ext ["X"] (VR ++ TwPrep.SPrep) σ2 := by
    refine ⟨fun a ha => ?_, fun v hv => ?_⟩
    · rw [har2]; exact hW1.arrs a ha
    · rw [hfr2 v (fun h => hv (by simp [h]))]
      exact hW1.vars v (fun h => hv (by simp [h]))
  have ho2' : σ2.out = [] := by rw [ho2]; exact hout1
  have hbf2 : σ2.arrs "bfsc" = List.replicate (I.days * I.clients) 0 := by
    rw [hW2.arrs "bfsc" (by simp), hextbf]
  unfold mainCom seqs
  by_cases hg : 0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days
  · -- the guard holds
    have hok1 : σ2.vars "ok" = 1 := by rw [hok2, if_pos hg]
    have hcond : (Cond.lt (Expr.lit 0) (V "ok")).evalB B σ2 = some true := by
      rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (by rw [hok1]; omega))]
      simp [hok1]
    obtain hGB := hG hg
    obtain ⟨hRuns, hOLt, hzc⟩ := hcit hg
    obtain ⟨σ5, r5, hz5, hOlen5, hY5, hX5, hW5, hv5, hmask5, hbb5, ho5⟩ :=
      phaseGI (B := B) hdec prog ext _ _ OL _ t z σ2 hW2 hX2 hn2 hm2 hmn2 hw2 hwp2 hP2 hextY hextOP
        hextXA hextXB hextXC hextM hextO hGB.hPn hGB.hsm hRuns hOLt hGB.hlit hGB.h2m hn hm hGB.hnn
        hL hXB hGB.hwB hGB.hyP hGB.hyPn hGB.bPP hGB.b2 hGB.bnd hGB.hOL
    have hn5 : σ5.vars "n" = I.clients := by
      rw [hv5 "n" (by simp [VG, TwGraph.SGW, TwGraph.SG, TwViol.SD, TwSetup.SI]), hn2]
    have hm5 : σ5.vars "m" = I.days := by
      rw [hv5 "m" (by simp [VG, TwGraph.SGW, TwGraph.SG, TwViol.SD, TwSetup.SI]), hm2]
    have hk5 : σ5.vars "k" = k := by
      rw [hv5 "k" (by simp [VG, TwGraph.SGW, TwGraph.SG, TwViol.SD, TwSetup.SI]), hk2]
    have hbf5 : σ5.arrs "bfsc" = List.replicate (I.days * I.clients) 0 := by
      rw [hW5.arrs "bfsc" (by simp [AG]), hextbf]
    have ho5' : σ5.out = [] := by rw [ho5, ho2']
    have hnn : 0 < z.length := by rcases hzc with rfl | ⟨D, rfl⟩ <;> simp
    have hO0 : (σ5.arrs "O").getD 0 0 = z.getD 0 0 := getD_of_take hz5 hnn
    have hidx : 0 < (σ5.arrs "O").length := by
      have : z.length ≤ (σ5.arrs "O").length := by
        rw [hz5]; exact List.length_take_le' _ _
      omega
    have hOB0 : (σ5.arrs "O").getD 0 0 < B := by
      rw [hO0]
      rcases hzc with rfl | ⟨D, rfl⟩ <;> simp <;> omega
    have hcond2 : ∀ v : ℕ, (σ5.arrs "O").getD 0 0 = v → 1 < B →
        (Cond.eq (G "O" (Expr.lit 0)) (Expr.lit 1)).evalB B σ5 = some (v == 1) := by
      intro v hv hB1
      rw [evalB_condEq (m := (σ5.arrs "O").getD 0 0) (n := 1) ?_ (evalB_lit hB1), hv]
      exact evalB_get (k := 0) (evalB_lit (by omega)) (by
        rw [List.getElem?_eq_getElem hidx]; simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hidx]) hOB0
    unfold guarded
    rcases hzc with hz0 | ⟨D, hzD⟩
    · -- the decomposition step found no decomposition: enumerate
      have hO00 : (σ5.arrs "O").getD 0 0 = 0 := by rw [hO0, hz0]; rfl
      obtain ⟨σ6, r6, ho6⟩ := brute_run hdec hbr hXB σ5 hX5 hn5 hm5 hk5 hbf5 ho5'
      have hite := Run.ite_false (c := TwMain.dpBranch) (hcond2 0 hO00 (by omega)) r6
      have hRG := r5.seq hite
      refine ⟨σ6, (r1.seq (r2.seq (Run.ite_true hcond hRG))).mono ?_, ho6⟩
      simp only [Kmain, if_pos hg, if_pos hz0, Cond.size, Expr.size]
      omega
    · -- the decomposition step returned a decomposition: the dynamic program
      have hD := hnice D hg hzD
      have hO01 : (σ5.arrs "O").getD 0 0 = 1 := by rw [hO0, hzD]; rfl
      have hDPB := hDP D hD hzD
      have hPn1 : 1 ≤ 2 ^ ((2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit) := Nat.one_le_two_pow
      have hzB : ∀ v ∈ z, v < B := by
        intro v hv
        have h1 := TwSetup.RunsTo.out_lt hRuns v hv
        rw [← hGB.hPn] at h1
        exact lt_of_lt_of_le h1 (le_trans (Nat.le_mul_self _) hGB.bPP.le)
      obtain ⟨σ7, r7, ho7⟩ := phaseDP (B := B) ⟨I, y0, k, D, _, hy, hD⟩ ext z σ5 hzD hz5 hzB hW5
        (hX5.trans hx) hn5 hm5 hk5
        (by rw [hv5 "w" (by simp [VG, TwGraph.SGW, TwGraph.SG, TwViol.SD, TwSetup.SI]), hw2])
        (by rw [hv5 "mn" (by simp [VG, TwGraph.SGW, TwGraph.SG, TwViol.SD, TwSetup.SI]), hmn2]; rfl)
        hmask5 hbb5 (by rw [hX5]; exact hXB) hDPB.sz hDPB.bg hDPB.tb (by rw [hOlen5]; exact hDPB.lenO)
        hDPB.b1 hDPB.b2 hDPB.b3 hDPB.b4 hDPB.b5 (by rw [hX5]; exact hDPB.b6)
        (by rw [hOlen5]; exact hDPB.b7) hDPB.b8 hDPB.b9 hDPB.b10
      have hite := Run.ite_true (d := TwMain.brute) (hcond2 1 hO01 (by omega)) r7
      have hRG := r5.seq hite
      refine ⟨σ7, (r1.seq (r2.seq (Run.ite_true hcond hRG))).mono ?_, ?_⟩
      · have hc := hDPB.cost
        have hz0 : ¬ z = [0] := by rw [hzD]; simp
        simp only [Kmain, if_pos hg, if_neg hz0, Cond.size, Expr.size]
        omega
      · rw [ho7, ho5']; simp
  · -- the guard fails: enumerate
    have hok0 : σ2.vars "ok" = 0 := by rw [hok2, if_neg hg]
    have hcond : (Cond.lt (Expr.lit 0) (V "ok")).evalB B σ2 = some false := by
      rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (by rw [hok0]; omega))]
      simp [hok0]
    obtain ⟨σ6, r6, ho6⟩ := brute0_run hdec hbr hXB σ2 hX2 hn2 hm2 hk2 hbf2 hn hm
      (hXB k (by rw [hx]; simp)) ho2'
    refine ⟨σ6, (r1.seq (r2.seq (Run.ite_false hcond r6))).mono ?_, ho6⟩
    simp only [Kmain, if_neg hg, Cond.size, Expr.size]
    omega

end Lax117284Proofs.Machine.TwMain

end

/-! ### `Lax117284Proofs.Machine.TwNum0` -/

section
/-!
A run of a machine program writes at most one number per step, so the output is no longer than the
running time.
-/

namespace Lax117284Proofs.Machine.TwSetup

open Lax808846.Ram

lemma step_out_len {w : ℕ} {p : Program} {s s' : State} (h : step w p s = some s') :
    s'.out.length ≤ s.out.length + 1 := by
  unfold step at h
  cases hi : p[s.pc]? with
  | none => rw [hi] at h; simp at h
  | some i =>
    rw [hi] at h
    simp only [Option.bind_some] at h
    cases i <;> simp only [Instr.effect, Option.some.injEq] at h <;>
      first
      | (simp at h; done)
      | (subst h; omega)
      | (subst h; simp)
      | (cases hh : s.inp.head? <;> simp only [hh, Option.map] at h
         · exact absurd h (by simp)
         · rename_i v
           simp only [Option.some.injEq] at h
           subst h; simp)
      | skip

lemma run_out_len {w : ℕ} {p : Program} : ∀ (n : ℕ) (s s' : State),
    run w p n s = some s' → s'.out.length ≤ s.out.length + n
  | 0, s, s', h => by
    simp only [run, Option.some.injEq] at h; subst h; omega
  | n + 1, s, s', h => by
    simp only [run] at h
    cases hs : step w p s with
    | none => rw [hs] at h; simp at h
    | some s1 =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      have := run_out_len n s1 s' h
      have := step_out_len hs
      omega

/-- **The output is no longer than the time.** -/
theorem RunsTo.out_length_le {w : ℕ} {p : Program} {x y : List ℕ} {t : ℕ} (h : RunsTo w p x y t) :
    y.length ≤ t := by
  obtain ⟨k, s, hrun, -, hout, ht⟩ := h
  subst hout
  have := run_out_len k _ s hrun
  simp [initState] at this
  omega

end Lax117284Proofs.Machine.TwSetup

end

/-! ### `Lax117284Proofs.Machine.TwNum1` -/

section
/-!
The arithmetic of the guard: when the guard of the main program holds for a width `w`, the tables
of the dynamic program, the running time of the decomposition step and the word length it needs are
all at most polynomial in the length `L` of the word.
-/

namespace Lax117284Proofs.Machine.TwNum

open TwPrep

/-- **What the guard says**: `L` has binary length `lg + 1`, and the width `w` is admitted for `m`
days at that length. -/
structure Gd (ca cc L lg m w : ℕ) : Prop where
  hca : 1 ≤ ca
  hcc : ca + 1 ≤ cc
  hL : 3 ≤ L
  hlg1 : 2 ^ lg ≤ L
  hlg2 : L < 2 ^ (lg + 1)
  hw : geE cc m w ≤ lg

variable {ca cc L lg m w : ℕ}

theorem Gd.cw (h : Gd ca cc L lg m w) : cc * ((w + 1) * (w + 1) * (w + 1)) ≤ lg := by
  have := h.hw; unfold geE at this; omega

theorem Gd.mw (h : Gd ca cc L lg m w) : m * (w + 1) ≤ lg := by
  have := h.hw; unfold geE at this; omega

theorem Gd.wlg (h : Gd ca cc L lg m w) : w + 1 ≤ lg := by
  have h1 := h.cw
  have h2 : w + 1 ≤ (w + 1) * (w + 1) * (w + 1) := by
    calc w + 1 = (w + 1) * 1 * 1 := by ring
      _ ≤ (w + 1) * (w + 1) * (w + 1) := by gcongr <;> omega
  have h3 : (w + 1) * (w + 1) * (w + 1) ≤ cc * ((w + 1) * (w + 1) * (w + 1)) :=
    Nat.le_mul_of_pos_left _ (by have := h.hcc; omega)
  omega

theorem Gd.mlg (h : Gd ca cc L lg m w) : m ≤ lg := by
  have := h.mw
  have : m ≤ m * (w + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem Gd.lgL (h : Gd ca cc L lg m w) : lg < L :=
  lt_of_lt_of_le (Nat.lt_two_pow_self) h.hlg1

theorem Gd.pm (h : Gd ca cc L lg m w) : 2 ^ m ≤ L :=
  le_trans (Nat.pow_le_pow_right (by norm_num) h.mlg) h.hlg1

theorem Gd.tabs (h : Gd ca cc L lg m w) : (2 ^ m) ^ (w + 1) ≤ L := by
  rw [← pow_mul]
  exact le_trans (Nat.pow_le_pow_right (by norm_num) h.mw) h.hlg1

theorem Gd.pw (h : Gd ca cc L lg m w) : 2 ^ (ca * w ^ 3) ≤ L := by
  have h1 : ca * w ^ 3 ≤ lg := by
    have := h.cw
    have e1 : w ^ 3 ≤ (w + 1) * (w + 1) * (w + 1) := by
      calc w ^ 3 = w * w * w := by ring
        _ ≤ (w + 1) * (w + 1) * (w + 1) := by gcongr <;> omega
    have e2 : ca * w ^ 3 ≤ cc * ((w + 1) * (w + 1) * (w + 1)) :=
      Nat.mul_le_mul (by have := h.hcc; omega) e1
    omega
  exact le_trans (Nat.pow_le_pow_right (by norm_num) h1) h.hlg1

/-- **The word length of the decomposition step is enough**: the hypothesis of the cited theorem,
for a word of `n * n + 2` entries each at most `L`, on `Wp = (2 * cc + 1) * lg + 4 * cc + plit`
bits. -/
theorem Gd.ax (h : Gd ca cc L lg m w) {n v plit : ℕ} (hn : n ≤ L) (hv : v ≤ L) (hpl : ca ≤ plit) :
    ca * 2 ^ (ca * w ^ 3) * (n * n + 2 + v + 1) ^ ca ≤
      2 ^ ((2 * cc + 1) * lg + 4 * cc + plit) := by
  have hL := h.hL
  have hcc := h.hcc
  have hca := h.hca
  have h1 : n * n + 2 + v + 1 ≤ 2 * (L * L) := by
    have : n * n ≤ L * L := Nat.mul_le_mul hn hn
    nlinarith
  have h2 : (n * n + 2 + v + 1) ^ ca ≤ 2 ^ ca * L ^ (2 * ca) := by
    calc (n * n + 2 + v + 1) ^ ca ≤ (2 * (L * L)) ^ ca := Nat.pow_le_pow_left h1 _
      _ = 2 ^ ca * L ^ (2 * ca) := by rw [mul_pow, ← pow_two, ← pow_mul, mul_comm 2 ca]
  have h3 : ca * 2 ^ (ca * w ^ 3) * (n * n + 2 + v + 1) ^ ca ≤ ca * L * (2 ^ ca * L ^ (2 * ca)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ h.pw) h2
  have h4 : ca * L * (2 ^ ca * L ^ (2 * ca)) = ca * 2 ^ ca * L ^ (2 * ca + 1) := by ring
  have h5 : L ^ (2 * ca + 1) ≤ L ^ (2 * cc + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : L ^ (2 * cc + 1) ≤ (2 * 2 ^ lg) ^ (2 * cc + 1) :=
    Nat.pow_le_pow_left (by have := h.hlg2; rw [pow_succ] at this; omega) _
  have h7 : (2 * 2 ^ lg) ^ (2 * cc + 1) = 2 ^ (2 * cc + 1) * 2 ^ ((2 * cc + 1) * lg) := by
    rw [mul_pow, ← pow_mul, mul_comm lg]
  have h8 : ca ≤ 2 ^ plit := le_trans hpl (le_of_lt Nat.lt_two_pow_self)
  have h9 : 2 ^ ca * 2 ^ (2 * cc + 1) ≤ 2 ^ (4 * cc) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hE : 2 ^ ((2 * cc + 1) * lg + 4 * cc + plit) =
      2 ^ ((2 * cc + 1) * lg) * 2 ^ (4 * cc) * 2 ^ plit := by
    rw [pow_add, pow_add]
  rw [hE]
  calc ca * 2 ^ (ca * w ^ 3) * (n * n + 2 + v + 1) ^ ca
      ≤ ca * 2 ^ ca * L ^ (2 * ca + 1) := by rw [← h4]; exact h3
    _ ≤ ca * 2 ^ ca * (2 ^ (2 * cc + 1) * 2 ^ ((2 * cc + 1) * lg)) := by
        rw [← h7]; exact Nat.mul_le_mul_left _ (h5.trans h6)
    _ = ca * (2 ^ ca * 2 ^ (2 * cc + 1)) * 2 ^ ((2 * cc + 1) * lg) := by ring
    _ ≤ 2 ^ plit * 2 ^ (4 * cc) * 2 ^ ((2 * cc + 1) * lg) := by
        gcongr
    _ = 2 ^ ((2 * cc + 1) * lg) * 2 ^ (4 * cc) * 2 ^ plit := by ring

end Lax117284Proofs.Machine.TwNum

end

/-! ### `Lax117284Proofs.Machine.TwNum2` -/

section
/-!
Polynomial bounds: a quantity depending on the word is *polynomially bounded* on a set of words
when some `C * a x ^ E`, with `C` and `E` fixed, bounds it on every word of the set, where `a x`
is a size of the word. These are closed under sums and products.
-/

namespace Lax117284Proofs.Machine.TwNum

/-- `f` is at most `C * a x ^ E` on the words satisfying `P`, for some constants. -/
def PlOn (a : List ℕ → ℕ) (P : List ℕ → Prop) (f : List ℕ → ℕ) : Prop :=
  ∃ C E : ℕ, ∀ x, P x → f x ≤ C * a x ^ E

variable {a : List ℕ → ℕ} {P : List ℕ → Prop} {f g : List ℕ → ℕ}

theorem PlOn.mono (h : PlOn a P g) (hle : ∀ x, P x → f x ≤ g x) : PlOn a P f := by
  obtain ⟨C, E, h⟩ := h
  exact ⟨C, E, fun x hx => (hle x hx).trans (h x hx)⟩

theorem PlOn.const (c : ℕ) : PlOn a P (fun _ => c) := ⟨c, 0, fun x _ => by simp⟩

theorem PlOn.base : PlOn a P a := ⟨1, 1, fun x _ => by simp⟩

theorem PlOn.add (ha : ∀ x, P x → 1 ≤ a x) (hf : PlOn a P f) (hg : PlOn a P g) :
    PlOn a P (fun x => f x + g x) := by
  obtain ⟨C1, E1, h1⟩ := hf
  obtain ⟨C2, E2, h2⟩ := hg
  refine ⟨C1 + C2, max E1 E2, fun x hx => ?_⟩
  have h3 : a x ^ E1 ≤ a x ^ max E1 E2 := Nat.pow_le_pow_right (ha x hx) (le_max_left _ _)
  have h4 : a x ^ E2 ≤ a x ^ max E1 E2 := Nat.pow_le_pow_right (ha x hx) (le_max_right _ _)
  calc f x + g x ≤ C1 * a x ^ E1 + C2 * a x ^ E2 := Nat.add_le_add (h1 x hx) (h2 x hx)
    _ ≤ C1 * a x ^ max E1 E2 + C2 * a x ^ max E1 E2 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h3) (Nat.mul_le_mul_left _ h4)
    _ = (C1 + C2) * a x ^ max E1 E2 := by ring

theorem PlOn.mul (hf : PlOn a P f) (hg : PlOn a P g) : PlOn a P (fun x => f x * g x) := by
  obtain ⟨C1, E1, h1⟩ := hf
  obtain ⟨C2, E2, h2⟩ := hg
  refine ⟨C1 * C2, E1 + E2, fun x hx => ?_⟩
  calc f x * g x ≤ (C1 * a x ^ E1) * (C2 * a x ^ E2) := Nat.mul_le_mul (h1 x hx) (h2 x hx)
    _ = C1 * C2 * a x ^ (E1 + E2) := by ring

theorem PlOn.pow (hf : PlOn a P f) (e : ℕ) : PlOn a P (fun x => f x ^ e) := by
  obtain ⟨C, E, h⟩ := hf
  refine ⟨C ^ e, E * e, fun x hx => ?_⟩
  calc f x ^ e ≤ (C * a x ^ E) ^ e := Nat.pow_le_pow_left (h x hx) _
    _ = C ^ e * a x ^ (E * e) := by rw [mul_pow, ← pow_mul]

open Classical in
/-- A quantity that is set to zero unless a condition holds, bounded where it holds. -/
theorem PlOn.guard {Q : List ℕ → Prop} (h : PlOn a (fun x => P x ∧ Q x) f) :
    PlOn a P (fun x => if Q x then f x else 0) := by
  obtain ⟨C, E, h⟩ := h
  refine ⟨C, E, fun x hx => ?_⟩
  by_cases hq : Q x
  · show (if Q x then f x else 0) ≤ _
    rw [if_pos hq]; exact h x ⟨hx, hq⟩
  · show (if Q x then f x else 0) ≤ _
    rw [if_neg hq]; exact Nat.zero_le _

/-- A bigger size gives the same bounds. -/
theorem PlOn.base_mono {b : List ℕ → ℕ} (h : PlOn a P f) (hab : ∀ x, P x → a x ≤ b x) :
    PlOn b P f := by
  obtain ⟨C, E, h⟩ := h
  exact ⟨C, E, fun x hx => (h x hx).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hab x hx) _))⟩

end Lax117284Proofs.Machine.TwNum

end

/-! ### `Lax117284Proofs.Machine.TwNum3` -/

section
/-!
The numbers of a word as functions of it: the guard, the width the decomposition step is run at,
the sizes of the tables, and their polynomial bounds.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax117284.InstanceEncoding Lax117284.Scheduling Lax808846.Ram
open Lax117284Proofs.Machine.ClMain (Mx le_Mx Mx_mem_or_zero mem_x)

/-- The number of clients a word declares. -/
def nx (x : List ℕ) : ℕ := x.getD 0 0
/-- The number of days a word declares. -/
def mx (x : List ℕ) : ℕ := x.getD 1 0
/-- The binary logarithm of the length of a word. -/
def lgx (x : List ℕ) : ℕ := Nat.log 2 x.length
/-- The number of widths the guard admits. -/
def wcx (cc : ℕ) (x : List ℕ) : ℕ := TwPrep.wcnt cc (mx x) (lgx x)
/-- The width at which the decomposition step is run. -/
def wx (cc : ℕ) (x : List ℕ) : ℕ := wcx cc x - 1
/-- The guard: some width is admitted, and there is a day. -/
def gdx (cc : ℕ) (x : List ℕ) : Prop := 0 < wcx cc x ∧ 0 < mx x
/-- The word length of the decomposition step. -/
def Wpx (cc plit : ℕ) (x : List ℕ) : ℕ := (2 * cc + 1) * lgx x + 4 * cc + plit
/-- The bound on the running time of the decomposition step. -/
def Tbx (ca cc : ℕ) (x : List ℕ) : ℕ := ca * 2 ^ (ca * wx cc x ^ 3) * (nx x * nx x + 3) ^ ca
/-- The number of restrictions of the dynamic program. -/
def tabsx (cc : ℕ) (x : List ℕ) : ℕ := (2 ^ mx x) ^ (wx cc x + 1)
/-- The size of a word. -/
def Aw (x : List ℕ) : ℕ := x.length + Mx x + 1
/-- The size of a word for time. -/
def Lp (x : List ℕ) : ℕ := x.length + 1
/-- The words of the domain. -/
def Dm (x : List ℕ) : Prop := x ∈ UniformInstances

theorem Aw_pos (x : List ℕ) : 1 ≤ Aw x := by unfold Aw; omega
theorem Lp_pos (x : List ℕ) : 1 ≤ Lp x := by unfold Lp; omega
theorem Lp_le_Aw (x : List ℕ) : Lp x ≤ Aw x := by unfold Lp Aw; omega

variable {ca cc plit : ℕ} {x : List ℕ}

theorem Dm.len (hx : Dm x) : ∃ I k, EncodesUniform x I k ∧ x.length = 3 + 2 * (I.days * I.clients) ∧
    nx x = I.clients ∧ mx x = I.days := by
  obtain ⟨I, k, hdec⟩ := hx
  exact ⟨I, k, hdec, ClientsWord.len_eq hdec, ClientsWord.x0 hdec, ClientsWord.x1 hdec⟩

theorem Dm.three (hx : Dm x) : 3 ≤ x.length := by
  obtain ⟨I, k, -, h, -⟩ := hx.len; omega

theorem Dm.nMx (hx : Dm x) : nx x ≤ Mx x ∧ mx x ≤ Mx x := by
  obtain ⟨I, k, hdec, -⟩ := hx.len
  exact ⟨mem_x hdec 0, mem_x hdec 1⟩

theorem Dm.gd (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) (hx : Dm x) (hg : gdx cc x) :
    Gd ca cc x.length (lgx x) (mx x) (wx cc x) := by
  have hL0 := hx.three
  refine ⟨hca, hcc, hL0, Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) _,
    ?_⟩
  have := (TwPrep.wcnt_spec (cc := cc) (by omega) (mx x) (lgx x)).2.1 (wcx cc x - 1)
    (by have := hg.1; unfold wcx at this ⊢; omega)
  exact this

theorem Dm.nL (hx : Dm x) (hg : 0 < mx x) : nx x ≤ x.length := by
  obtain ⟨I, k, hdec, h, hn, hm⟩ := hx.len
  have : I.clients ≤ I.days * I.clients := Nat.le_mul_of_pos_left _ (by omega)
  omega

end Lax117284Proofs.Machine.TwNum

end

/-! ### `Lax117284Proofs.Machine.TwNum4` -/

section
/-!
Polynomial bounds for the numbers of a word: the length, the logarithm, the word length of the
decomposition step, the sizes of the tables and the running time of the decomposition step.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax117284Proofs.Machine.ClMain (Mx le_Mx Mx_mem_or_zero mem_x)

theorem PlOn.addL {P : List ℕ → Prop} {f g : List ℕ → ℕ} (hf : PlOn Lp P f) (hg : PlOn Lp P g) :
    PlOn Lp P (fun x => f x + g x) := PlOn.add (fun x _ => Lp_pos x) hf hg

theorem PlOn.addA {P : List ℕ → Prop} {f g : List ℕ → ℕ} (hf : PlOn Aw P f) (hg : PlOn Aw P g) :
    PlOn Aw P (fun x => f x + g x) := PlOn.add (fun x _ => Aw_pos x) hf hg

variable {P : List ℕ → Prop} {ca cc plit : ℕ}

theorem atom_len : PlOn Lp P (fun x => x.length) :=
  PlOn.base.mono (fun x _ => by unfold Lp; omega)

theorem atom_lg : PlOn Lp P lgx :=
  atom_len.mono (fun x _ => by unfold lgx; exact Nat.log_le_self 2 _)

theorem atom_Wp : PlOn Lp P (Wpx cc plit) := by
  have h : PlOn Lp P (fun x => (2 * cc + 1) * lgx x + 4 * cc + plit) :=
    (((PlOn.const _).mul atom_lg).addL (PlOn.const _)).addL (PlOn.const _)
  exact h

theorem atom_Pn (hP : ∀ x, P x → Dm x) : PlOn Lp P (fun x => 2 ^ Wpx cc plit x) := by
  have h : PlOn Lp P (fun x => 2 ^ (4 * cc + plit) * x.length ^ (2 * cc + 1)) :=
    (PlOn.const _).mul (atom_len.pow _)
  refine h.mono (fun x hx => ?_)
  have hL := (hP x hx).three
  have h1 : 2 ^ lgx x ≤ x.length := Nat.pow_log_le_self 2 (by omega)
  unfold Wpx
  have : 2 ^ ((2 * cc + 1) * lgx x + 4 * cc + plit) =
      2 ^ (4 * cc + plit) * (2 ^ lgx x) ^ (2 * cc + 1) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  rw [this]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)

/-- Under the guard. -/
theorem atom_m (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    PlOn Lp (fun x => Dm x ∧ gdx cc x) mx := by
  refine atom_len.mono (fun x hx => ?_)
  have := (hx.1.gd hca hcc hx.2).mlg
  have := (hx.1.gd hca hcc hx.2).lgL
  omega

theorem atom_n (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    PlOn Lp (fun x => Dm x ∧ gdx cc x) nx :=
  atom_len.mono (fun x hx => hx.1.nL hx.2.2)

theorem atom_w (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    PlOn Lp (fun x => Dm x ∧ gdx cc x) (wx cc) := by
  refine atom_len.mono (fun x hx => ?_)
  have := (hx.1.gd hca hcc hx.2).wlg
  have := (hx.1.gd hca hcc hx.2).lgL
  omega

theorem atom_pm (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    PlOn Lp (fun x => Dm x ∧ gdx cc x) (fun x => 2 ^ mx x) :=
  atom_len.mono (fun x hx => (hx.1.gd hca hcc hx.2).pm)

theorem atom_tabs (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    PlOn Lp (fun x => Dm x ∧ gdx cc x) (tabsx cc) :=
  atom_len.mono (fun x hx => (hx.1.gd hca hcc hx.2).tabs)

theorem atom_Tb (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    PlOn Lp (fun x => Dm x ∧ gdx cc x) (Tbx ca cc) := by
  have h : PlOn Lp (fun x => Dm x ∧ gdx cc x)
      (fun x => ca * x.length * (x.length * x.length + 3) ^ ca) :=
    ((PlOn.const ca).mul atom_len).mul (((atom_len.mul atom_len).addL (PlOn.const 3)).pow ca)
  refine h.mono (fun x hx => ?_)
  have hg := hx.1.gd hca hcc hx.2
  have hn := hx.1.nL hx.2.2
  unfold Tbx
  have h1 : nx x * nx x + 3 ≤ x.length * x.length + 3 := by have := Nat.mul_le_mul hn hn; omega
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hg.pw) (Nat.pow_le_pow_left h1 _)

end Lax117284Proofs.Machine.TwNum

end
