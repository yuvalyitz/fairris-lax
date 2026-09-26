import Lax117284Proofs.Machine.URow
import Lax117284Proofs.Machine.ILoop
import Lax117284Proofs.Machine.Flag
import Lax117284Proofs.Machine.MisBlk

/-!
The accepting phase of the reduction of the unit processing times to matching: the check of the
table, the header of the graph, and the rows.
-/

namespace Lax117284Proofs.Machine.UAcc

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.UEmit Lax117284Proofs.Machine.URow Lax117284Proofs.Machine.USem
open Lax117284Proofs.UnitPGraph Lax117284Proofs.Machine.ILoop Lax117284Proofs.Machine.FoldLoop
open Lax117284Proofs.Machine.Flag

variable {B : ℕ}

/-- What every row shares. -/
structure Ctx0 (arr : List ℕ) (n m kp : ℕ) (σ : Env) : Prop where
  tk : σ.arrs "TK" = arr
  vn : σ.vars "n" = n
  vm : σ.vars "m" = m
  vN : σ.vars "N" = m * n
  vq : σ.vars "q" = m - kp
  vC : σ.vars "C" = m * n + n * (m - kp)

theorem rctx_toC {arr : List ℕ} {n m kp r : ℕ} {σ : Env} (h : RCtx arr n m kp r σ) :
    Ctx0 arr n m kp σ := ⟨h.tk, h.vn, h.vm, h.vN, h.vq, h.vC⟩

theorem Ctx0.toR {arr : List ℕ} {n m kp : ℕ} {σ : Env} (h : Ctx0 arr n m kp σ) {r : ℕ}
    (hr : σ.vars "r" = r) : RCtx arr n m kp r σ := ⟨h.tk, h.vn, h.vm, h.vN, h.vq, h.vC, hr⟩

theorem Ctx0.setR {arr : List ℕ} {n m kp : ℕ} {σ : Env} (h : Ctx0 arr n m kp σ) (v : ℕ) :
    Ctx0 arr n m kp (σ.setVar "r" v) :=
  ⟨by simpa [Env.setVar] using h.tk, by simpa [Env.setVar] using h.vn,
    by simpa [Env.setVar] using h.vm, by simpa [Env.setVar] using h.vN,
    by simpa [Env.setVar] using h.vq, by simpa [Env.setVar] using h.vC⟩

/-- All the rows of the table. -/
def rowsLoop : Com := fLoop "r" "N" rowBody

theorem flatMap_range_succ (f : ℕ → List ℕ) (j : ℕ) :
    (List.range (j + 1)).flatMap f = (List.range j).flatMap f ++ f j := by
  simp [List.range_succ, List.flatMap_append]

/-- **The rows are written.** -/
theorem rowsLoop_run (arr : List ℕ) (n m kp : ℕ) (hk : kp ≤ m) (σ : Env)
    (hlen : 3 + 2 * (m * n) ≤ arr.length)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 < B)
    (hB : 3 + 2 * (m * n) + 8 < B) (hnB : n + 8 < B) (hmB : m + 8 < B)
    (hC : Ctx0 arr n m kp σ) :
    ∃ σ', Run B rowsLoop σ σ' ((400 + 40 * n + 50 * (m * n + n * (m - kp)) + 10 + 4) * (m * n) + 6) ∧
      σ'.out = σ.out ++ (List.range (m * n)).flatMap (rowR n m kp (dA arr)) ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp := by
  obtain ⟨σ', r, hQ⟩ := iLoop_spec (B := B) "r" "N" rowBody
    (fun j σ' => Ctx0 arr n m kp σ' ∧
      σ'.out = σ.out ++ (List.range j).flatMap (rowR n m kp (dA arr)) ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp)
    (400 + 40 * n + 50 * (m * n + n * (m - kp))) (m * n) σ hC.vN
    (fun j σ' h => h.1.vN) (by decide) (by omega)
    ⟨hC.setR 0, by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar]⟩
    (fun j σ' v h => ⟨h.1.setR v, by simpa [Env.setVar] using h.2.1,
      by simpa [Env.setVar] using h.2.2.1, by simpa [Env.setVar] using h.2.2.2⟩)
    (fun j σ' h hj hlt => by
      obtain ⟨σ'', r', ho, hR, ha, hi⟩ := rowBody_spec (B := B) arr n m kp j hk hlt hlen hE hB
        hnB hmB σ' (h.1.toR hj)
      refine ⟨σ'', r', ⟨rctx_toC hR, ?_, ?_, ?_⟩, hR.vr⟩
      · rw [ho, h.2.1, flatMap_range_succ, List.append_assoc]
      · rw [ha, h.2.2.1]
      · rw [hi, h.2.2.2])
  exact ⟨σ', r, hQ.2.1, hQ.2.2.1, hQ.2.2.2⟩

/-! ### The check of the table -/

/-- The job of the cell `t` has processing time one and a positive due date. -/
def PassU (arr : List ℕ) (t : ℕ) : Prop :=
  arr.getD (2 + 2 * t) 0 = 1 ∧ 0 < arr.getD (3 + 2 * t) 0

open Classical in
noncomputable instance (arr : List ℕ) : DecidablePred (PassU arr) := fun _ => Classical.propDecidable _

/-- The test of the cell `i`. -/
def okChkU : Com :=
  .seq (.assign "p" (.get "TK" (.bin .add (.lit 2) (.bin .mul (.lit 2) (.var "i")))))
    (.seq (.assign "d" (.get "TK" (.bin .add (.lit 3) (.bin .mul (.lit 2) (.var "i")))))
      (.ite (.eq (.var "p") (.lit 1))
        (.ite (.lt (.lit 0) (.var "d")) .skip (.assign "ok" (.lit 0)))
        (.assign "ok" (.lit 0))))

def okBodyU : Com := .seq okChkU (.assign "i" (.bin .add (.var "i") (.lit 1)))

def okLoopU : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") (.var "N")) okBodyU)

/-- The invariant of the pass over the table. -/
structure OkInvU (arr : List ℕ) (N ok0 : ℕ) (σ0 σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  inp : σ.inp = σ0.inp
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vN : σ.vars "N" = N
  hi : σ.vars "i" ≤ N
  hok : σ.vars "ok" = flagTo (PassU arr) ok0 (σ.vars "i")
  fr : ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → y ≠ "d" → σ.vars y = σ0.vars y

lemma flag_failU (arr : List ℕ) (ok0 i : ℕ) (h : ¬ PassU arr i) :
    flagTo (PassU arr) ok0 (i + 1) = 0 := by
  rw [flagTo_succ]; simp [h]

lemma flag_passU (arr : List ℕ) (ok0 i : ℕ) (h : PassU arr i) (hok : ok0 ≤ 1) :
    flagTo (PassU arr) ok0 (i + 1) = flagTo (PassU arr) ok0 i := by
  rw [flagTo_succ]
  have := flagTo_le (PassU arr) ok0 i
  by_cases h1 : flagTo (PassU arr) ok0 i = 1
  · simp [h1, h]
  · have : flagTo (PassU arr) ok0 i = 0 := by omega
    simp [this]

theorem okBodyU_spec (arr : List ℕ) (N ok0 : ℕ) (σ0 : Env)
    (hE : ∀ k < 3 + 2 * N, arr.getD k 0 + 8 < B) (hL : 3 + 2 * N + 8 < B)
    (hN : 3 + 2 * N ≤ arr.length) (hNB : N + 8 < B) (hok0 : ok0 ≤ 1) :
    Spec B (fun σ => OkInvU arr N ok0 σ0 σ ∧ σ.vars "i" < N) okBodyU
      (fun σ σ' => OkInvU arr N ok0 σ0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  unfold okBodyU okChkU
  run_vcg
  all_goals (
    have hI := ‹OkInvU arr N ok0 σ0 σ›
    have hlt := ‹σ.vars "i" < N›
    have hsa := hI.arrs
    have hsi := hI.inp
    have hso := hI.out
    have hA0 := hI.hA
    have hNv := hI.vN
    have hi := hI.hi
    have hok := hI.hok
    have hfr := hI.fr
    clear hI
    have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
    have h1 := hE (2 + 2 * σ.vars "i") (by omega)
    have h2 := hE (3 + 2 * σ.vars "i") (by omega)
    subst hA
    try simp only [Env.setVar] at *
    try simp at *)
  all_goals try omega
  all_goals (refine ⟨hsa, hsi, hso, hA0, ?_, ?_, ?_, fun y a b c d => ?_⟩)
  · simp [hNv]
  · simp; omega
  · simp
    rw [flag_passU _ ok0 _ (by simp [PassU, List.getD_eq_getElem?_getD]; omega) hok0, hok]
  · simp [a, b, c, d]; exact hfr y a b c d
  · simp [hNv]
  · simp; omega
  · simp
    exact (flag_failU _ ok0 _ (by simp [PassU, List.getD_eq_getElem?_getD]; omega)).symm
  · simp [a, b, c, d]; exact hfr y a b c d
  · simp [hNv]
  · simp; omega
  · simp
    exact (flag_failU _ ok0 _ (by simp [PassU, List.getD_eq_getElem?_getD]; omega)).symm
  · simp [a, b, c, d]; exact hfr y a b c d

theorem okLoopU_run (arr : List ℕ) (N ok0 : ℕ) (σ : Env)
    (hE : ∀ k < 3 + 2 * N, arr.getD k 0 + 8 < B) (hL : 3 + 2 * N + 8 < B)
    (hN : 3 + 2 * N ≤ arr.length) (hNB : N + 8 < B) (hok0 : ok0 ≤ 1)
    (hA : σ.arrs "TK" = arr) (hNv : σ.vars "N" = N) (hok : σ.vars "ok" = ok0) :
    ∃ σ', Run B okLoopU σ σ' ((40 + 4) * N + 6) ∧ σ'.vars "ok" = flagTo (PassU arr) ok0 N ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
      ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → y ≠ "d" → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := okBodyU) "i" "N"
    (OkInvU arr N ok0 σ) N 40 (by omega) (fun _ h => h.hi) (fun _ h => h.vN)
    (okBodyU_spec arr N ok0 σ hE hL hN hNB hok0)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar], hA, hNv,
      by simp [Env.setVar], by
        simp only [Env.setVar]
        simp [flagTo_zero (PassU arr) ok0 hok0, hok], fun y a b c d => by
      simp [Env.setVar, b]⟩
  refine ⟨σ', r, ?_, hI.arrs, hI.out, hI.inp, ?_⟩
  · rw [hI.hok, hi]
  · intro y a b c d
    rw [hI.fr y a b c d]

/-! ### The header -/

/-- Read the counts, the size of the table and the parameter. -/
def prepU : Com :=
  .seq (.assign "n" (.get "TK" (.lit 0)))
  (.seq (.assign "m" (.get "TK" (.lit 1)))
  (.seq (.assign "N" (.bin .mul (.var "m") (.var "n")))
  (.seq (.assign "kp" (.get "TK" (.bin .add (.lit 2) (.bin .mul (.lit 2) (.var "N")))))
    (.assign "ok" (.lit 1)))))

theorem prepU_spec (arr : List ℕ) (hlen : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) ≤ arr.length)
    (hE : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), arr.getD k 0 + 8 < B)
    (hB : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B) :
    Spec B (fun σ => σ.arrs "TK" = arr) prepU
      (fun σ σ' => σ'.vars "n" = arr.getD 0 0 ∧ σ'.vars "m" = arr.getD 1 0 ∧
        σ'.vars "N" = arr.getD 1 0 * arr.getD 0 0 ∧
        σ'.vars "kp" = arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 ∧ σ'.vars "ok" = 1 ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
        ∀ y, y ≠ "n" → y ≠ "m" → y ≠ "N" → y ≠ "kp" → y ≠ "ok" → σ'.vars y = σ.vars y) 60 := by
  intro σ hA
  have h0 := hE 0 (by omega)
  have h1 := hE 1 (by omega)
  have h2 := hE (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) (by omega)
  have hTKl : (σ.arrs "TK").length = arr.length := by rw [hA]
  simp only [List.getD_eq_getElem?_getD] at h0 h1 h2 hlen hB
  unfold prepU
  run_vcg
  all_goals (try simp [hA])
  all_goals (try omega)
  intro y a b c d e
  simp [a, b, c, d, e]

/-! ### The graph -/

/-- The header of the graph and the rows. -/
def mainU : Com :=
  .seq (.write (.var "N"))
  (.seq (.assign "q" (.bin .sub (.var "m") (.var "kp")))
  (.seq (.assign "C" (.bin .add (.var "N") (.bin .mul (.var "n") (.var "q"))))
  (.seq (.write (.var "C")) rowsLoop)))

/-- The cost of the rows. -/
def Kmain (n m kp : ℕ) : ℕ :=
  (400 + 40 * n + 50 * (m * n + n * (m - kp)) + 10 + 4) * (m * n) + 6

theorem rowsLoop_spec (arr : List ℕ) (n m kp : ℕ) (hk : kp ≤ m)
    (hlen : 3 + 2 * (m * n) ≤ arr.length)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 < B)
    (hB : 3 + 2 * (m * n) + 8 < B) (hnB : n + 8 < B) (hmB : m + 8 < B) :
    Spec B (fun σ => Ctx0 arr n m kp σ) rowsLoop
      (fun σ σ' => σ'.out = σ.out ++ (List.range (m * n)).flatMap (rowR n m kp (dA arr)) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp) (Kmain n m kp) := by
  intro σ hC
  obtain ⟨σ', r, h⟩ := rowsLoop_run arr n m kp hk σ hlen hE hB hnB hmB hC
  exact ⟨σ', r, h⟩

theorem mainU_spec (arr : List ℕ) (n m kp : ℕ) (hk : kp ≤ m)
    (hlen : 3 + 2 * (m * n) ≤ arr.length)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 < B)
    (hB : 3 + 2 * (m * n) + 8 < B) (hnB : n + 8 < B) (hmB : m + 8 < B) :
    Spec B (fun σ => σ.arrs "TK" = arr ∧ σ.vars "n" = n ∧ σ.vars "m" = m ∧ σ.vars "N" = m * n ∧
        σ.vars "kp" = kp) mainU
      (fun σ σ' => σ'.out = σ.out ++ ([m * n, cols n m kp] ++
        (List.range (m * n)).flatMap (rowR n m kp (dA arr))) ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp) (14 + Kmain n m kp) := by
  rintro σ ⟨tk, vn, vm, vN, vkp⟩
  have hC : n * (m - kp) ≤ m * n := by
    have := Nat.mul_le_mul_left n (Nat.sub_le m kp)
    rw [Nat.mul_comm n m] at this; exact this
  unfold mainU
  run_vcg [rowsLoop_spec (B := B) arr n m kp hk hlen hE hB hnB hmB]
  all_goals first
    | (simp [Env.setVar, vn, vm, vN, vkp]; omega)
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Env.setVar, tk, vn, vm, vN, vkp]; done)
    | (obtain ⟨ho, ha, hi⟩ := ‹_ ∧ _ ∧ _›
       refine ⟨?_, ?_, ?_⟩
       · rw [ho]; simp [Env.setVar, vN, vn, vm, vkp, cols]
       · rw [ha]; simp [Env.setVar]
       · rw [hi]; simp [Env.setVar])

/-! ### The whole phase -/

/-- Write the graph without a full matching. -/
def rejCom : Com := .seq (.write (.lit 1)) (.write (.lit 0))

/-- The parameter is above the number of days: the empty graph if there is no client, the graph
of one left vertex and no right vertex if there is one. -/
def kBigCom : Com :=
  .ite (.eq (.var "n") (.lit 0)) (.seq (.write (.lit 0)) (.write (.lit 0))) rejCom

/-- **The accepting phase**: check the table, then write the graph. -/
def accU : Com :=
  .seq prepU (.seq okLoopU (.ite (.eq (.var "ok") (.lit 1))
    (.ite (.lt (.var "m") (.var "kp")) kBigCom mainU) rejCom))

theorem write_lit_run {σ : Env} (v : ℕ) (hv : v < B) :
    Run B (.write (.lit v)) σ { σ with out := σ.out ++ [v] } 2 :=
  (Run.write (evalB_lit hv)).mono (by simp [Expr.size])

theorem rejCom_run (σ : Env) (hB : 2 < B) :
    ∃ σ', Run B rejCom σ σ' 4 ∧ σ'.out = σ.out ++ rejU := by
  refine ⟨_, (write_lit_run (σ := σ) 1 (by omega)).seq (write_lit_run 0 (by omega)), ?_⟩
  simp [rejU]

theorem kBigCom_run (σ : Env) (hB : 2 < B) (hn : σ.vars "n" < B) :
    ∃ σ', Run B kBigCom σ σ' 8 ∧
      σ'.out = σ.out ++ (if σ.vars "n" = 0 then [0, 0] else [1, 0]) := by
  by_cases h : σ.vars "n" = 0
  · have hc : (Cond.eq (.var "n") (.lit 0)).evalB B σ = some true :=
      Lax117284Proofs.Machine.MisBlk.condEq_true _ _ σ (by simpa using hn) (by simp; omega)
        (by simp [h])
    refine ⟨_, ((Run.ite_true hc ((write_lit_run (σ := σ) 0 (by omega)).seq
      (write_lit_run 0 (by omega)))).mono (by simp [Cond.size, Expr.size])), ?_⟩
    simp [h]
  · have hc : (Cond.eq (.var "n") (.lit 0)).evalB B σ = some false :=
      Lax117284Proofs.Machine.MisBlk.condEq_false _ _ σ (by simpa using hn) (by simp; omega)
        (by simp [h])
    obtain ⟨σ', r, ho⟩ := rejCom_run σ hB
    refine ⟨σ', (Run.ite_false hc r).mono (by simp [Cond.size, Expr.size]), ?_⟩
    simp [h, ho, rejU]

theorem Kmain_le (n m kp : ℕ) :
    Kmain n m kp ≤ 414 * (m * n) + 140 * (m * n) * (m * n) + 6 := by
  unfold Kmain
  rcases Nat.eq_zero_or_pos (m * n) with h | h
  · rw [h]; simp
  · have hn : n ≤ m * n := by
      have : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0] at h; simp at h
        · exact h0
      exact Nat.le_mul_of_pos_left n this
    have hC : n * (m - kp) ≤ m * n := by
      have := Nat.mul_le_mul_left n (Nat.sub_le m kp)
      rw [Nat.mul_comm n m] at this; exact this
    have : (400 + 40 * n + 50 * (m * n + n * (m - kp)) + 10 + 4) * (m * n) ≤
        (414 + 40 * (m * n) + 100 * (m * n)) * (m * n) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith

theorem accU_run (arr : List ℕ) (n m kp : ℕ) (hn : arr.getD 0 0 = n) (hm : arr.getD 1 0 = m)
    (hkp : arr.getD (2 + 2 * (m * n)) 0 = kp) (σ : Env) (hA : σ.arrs "TK" = arr)
    (hlen : 3 + 2 * (m * n) ≤ arr.length)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 + 8 < B) (hB : 3 + 2 * (m * n) + 8 < B) :
    ∃ σ', Run B accU σ σ' (200 + 460 * (m * n) + 140 * (m * n) * (m * n)) ∧
      σ'.out = σ.out ++
        (if (∀ t < m * n, PassU arr t) then graphNums n m kp (dA arr) else rejU) := by
  subst hn; subst hm
  have hnB : arr.getD 0 0 + 8 < B := hE 0 (by omega)
  have hmB : arr.getD 1 0 + 8 < B := hE 1 (by omega)
  have hKm := Kmain_le (arr.getD 0 0) (arr.getD 1 0) kp
  obtain ⟨σ1, r1, e1n, e1m, e1N, e1kp, e1ok, e1a, e1o, e1i, e1f⟩ :=
    (prepU_spec (B := B) arr hlen hE hB) σ hA
  obtain ⟨σ2, r2, e2ok, e2a, e2o, e2i, e2f⟩ := okLoopU_run (B := B) arr
    (arr.getD 1 0 * arr.getD 0 0) 1 σ1 hE (by omega) hlen (by omega) le_rfl
    (by rw [e1a]; exact hA) e1N e1ok
  have hA2 : σ2.arrs "TK" = arr := by rw [e2a, e1a]; exact hA
  have hn2 : σ2.vars "n" = arr.getD 0 0 := by
    rw [e2f "n" (by decide) (by decide) (by decide) (by decide)]; exact e1n
  have hm2 : σ2.vars "m" = arr.getD 1 0 := by
    rw [e2f "m" (by decide) (by decide) (by decide) (by decide)]; exact e1m
  have hN2 : σ2.vars "N" = arr.getD 1 0 * arr.getD 0 0 := by
    rw [e2f "N" (by decide) (by decide) (by decide) (by decide)]; exact e1N
  have hkp2 : σ2.vars "kp" = kp := by
    rw [e2f "kp" (by decide) (by decide) (by decide) (by decide), e1kp]; exact hkp
  have hflag := flagTo_eq_one (P := PassU arr) (okin := 1) (k := arr.getD 1 0 * arr.getD 0 0)
  have hokB : σ2.vars "ok" < B := by
    rw [e2ok]; have := flagTo_le (PassU arr) 1 (arr.getD 1 0 * arr.getD 0 0); omega
  have hkpB : kp < B := by
    rw [← hkp]; have := hE (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) (by omega); omega
  by_cases hpass : ∀ t < arr.getD 1 0 * arr.getD 0 0, PassU arr t
  · have hok1 : σ2.vars "ok" = 1 := by rw [e2ok]; exact hflag.2 ⟨rfl, hpass⟩
    have hcT : (Cond.eq (.var "ok") (.lit 1)).evalB B σ2 = some true :=
      Lax117284Proofs.Machine.MisBlk.condEq_true _ _ σ2 (by simpa using hokB) (by simp; omega)
        (by simp [hok1])
    by_cases hbig : arr.getD 1 0 < kp
    · have hcb : (Cond.lt (.var "m") (.var "kp")).evalB B σ2 = some true :=
        Lax117284Proofs.Machine.MisBlk.condLt_true _ _ σ2 (by simp; omega) (by simp; omega)
          (by simp only [Lax117284Proofs.Machine.MisBlk.den_var, hm2, hkp2]; exact hbig)
      obtain ⟨σ3, r3, o3⟩ := kBigCom_run (B := B) σ2 (by omega) (by omega)
      have hr : Run B accU σ σ3 (60 + ((40 + 4) * (arr.getD 1 0 * arr.getD 0 0) + 6 +
          (1 + (Cond.eq (.var "ok") (.lit 1)).size +
            (1 + (Cond.lt (.var "m") (.var "kp")).size + 8)))) :=
        r1.seq (r2.seq (Run.ite_true hcT (Run.ite_true hcb r3)))
      refine ⟨σ3, hr.mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      rw [o3, e2o, e1o, if_pos hpass, hn2]
      unfold graphNums
      rw [if_neg (show ¬ kp ≤ arr.getD 1 0 by omega)]
    · have hcb : (Cond.lt (.var "m") (.var "kp")).evalB B σ2 = some false :=
        Lax117284Proofs.Machine.MisBlk.condLt_false _ _ σ2 (by simp; omega) (by simp; omega)
          (by simp only [Lax117284Proofs.Machine.MisBlk.den_var, hm2, hkp2]; omega)
      obtain ⟨σ3, r3, o3, -, -⟩ := mainU_spec (B := B) arr (arr.getD 0 0) (arr.getD 1 0) kp
        (by omega) hlen (fun k hk => by have := hE k hk; omega) hB hnB hmB σ2
        ⟨hA2, hn2, hm2, hN2, hkp2⟩
      have hr : Run B accU σ σ3 (60 + ((40 + 4) * (arr.getD 1 0 * arr.getD 0 0) + 6 +
          (1 + (Cond.eq (.var "ok") (.lit 1)).size +
            (1 + (Cond.lt (.var "m") (.var "kp")).size + (14 + Kmain (arr.getD 0 0)
              (arr.getD 1 0) kp))))) :=
        r1.seq (r2.seq (Run.ite_true hcT (Run.ite_false hcb r3)))
      refine ⟨σ3, hr.mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      rw [o3, e2o, e1o, if_pos hpass, graphNums_rows (show kp ≤ arr.getD 1 0 by omega)]
  · have hok0 : σ2.vars "ok" = 0 := by
      have h1 := flagTo_le (PassU arr) 1 (arr.getD 1 0 * arr.getD 0 0)
      have h2 : ¬ flagTo (PassU arr) 1 (arr.getD 1 0 * arr.getD 0 0) = 1 := fun h =>
        hpass (hflag.1 h).2
      rw [e2ok]; omega
    have hcF : (Cond.eq (.var "ok") (.lit 1)).evalB B σ2 = some false :=
      Lax117284Proofs.Machine.MisBlk.condEq_false _ _ σ2 (by simpa using hokB) (by simp; omega)
        (by simp [hok0])
    obtain ⟨σ3, r3, o3⟩ := rejCom_run (B := B) σ2 (by omega)
    have hr : Run B accU σ σ3 (60 + ((40 + 4) * (arr.getD 1 0 * arr.getD 0 0) + 6 +
        (1 + (Cond.eq (.var "ok") (.lit 1)).size + 4))) :=
      r1.seq (r2.seq (Run.ite_false hcF r3))
    refine ⟨σ3, hr.mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
    rw [o3, e2o, e1o, if_neg hpass]

end Lax117284Proofs.Machine.UAcc
