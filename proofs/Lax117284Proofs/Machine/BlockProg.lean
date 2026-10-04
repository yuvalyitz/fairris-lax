import Lax117284Proofs.Machine.FreeCheck
import Lax117284Proofs.Machine.BlockSem
import Lax117284Proofs.Machine.Emit
import Lax117284Proofs.Machine.FreeProg

/-! ### `Lax117284Proofs.Machine.BlockCheck` -/

section
/-!
The pass over the table that finds the largest due date.
-/

namespace Lax117284Proofs.Machine.BlockCheck

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.BlockSem

variable {B : ℕ}

def dmaxChk : Com :=
  .seq (.assign "p" (.get "TK" (add (add (.lit 2) (mul (.lit 2) (V "i"))) (.lit 1))))
    (.ite (.lt (V "g") (V "p")) (.assign "g" (V "p")) .skip)

def dmaxBody : Com := .seq dmaxChk (.assign "i" (.bin .add (V "i") (.lit 1)))

def dmaxLoop : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "N")) dmaxBody)

/-- The running maximum of the due dates after `i` cells. -/
def runMaxD (arr : List ℕ) (i : ℕ) : ℕ :=
  (List.range i).foldl (fun g j => max g (arr.getD (2 + 2 * j + 1) 0)) 0

lemma runMaxD_succ (arr : List ℕ) (i : ℕ) :
    runMaxD arr (i + 1) = max (runMaxD arr i) (arr.getD (2 + 2 * i + 1) 0) := by
  unfold runMaxD
  rw [List.range_succ, List.foldl_append]
  simp

structure DInv (B : ℕ) (arr : List ℕ) (N : ℕ) (σ0 : Env) (σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vN : σ.vars "N" = N
  hi : σ.vars "i" ≤ N
  hg : σ.vars "g" = runMaxD arr (σ.vars "i")
  hgB : σ.vars "g" < B
  fr : ∀ y, y ≠ "g" → y ≠ "i" → y ≠ "p" → σ.vars y = σ0.vars y

theorem dmaxBody_spec (arr : List ℕ) (N : ℕ) (σ0 : Env)
    (hE : ∀ k < 2 + 2 * N, arr.getD k 0 + 8 < B) (hL : 2 + 2 * N + 8 < B)
    (hn : 2 + 2 * N ≤ arr.length) (hnB : N + 8 < B) :
    Spec B (fun σ => DInv B arr N σ0 σ ∧ σ.vars "i" < N) dmaxBody
      (fun σ σ' => DInv B arr N σ0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  run_vcg
  all_goals (
    have hI := ‹DInv B arr N σ0 σ›
    have hlt := ‹σ.vars "i" < N›
    have hA0 := hI.hA
    have hgB := hI.hgB
    obtain ⟨hsa, hso, -, hnv, hi, hg, -, hfr⟩ := hI
    have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
    have h1 := hE (2 + 2 * σ.vars "i" + 1) (by omega)
    have hrm := runMaxD_succ arr (σ.vars "i")
    have hg8 : runMaxD arr (σ.vars "i") ≤ σ.vars "g" := by omega
    subst hA
    try simp only [Env.setVar] at *
    try simp at *)
  all_goals try omega
  all_goals (
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun y a b c => ?_⟩
    · exact hsa
    · exact hso
    · exact hA0
    · simp [hnv]
    · simp; omega
    · simp only [Env.setVar]
      simp [hrm, max_def]
      first | omega | (split_ifs <;> omega) | (intro h; omega)
    · simp; omega
    · simp [a, b, c]; exact hfr y a b c)

theorem dmaxLoop_spec (arr : List ℕ) (N : ℕ) (σ : Env)
    (hE : ∀ k < 2 + 2 * N, arr.getD k 0 + 8 < B) (hL : 2 + 2 * N + 8 < B)
    (hn : 2 + 2 * N ≤ arr.length) (hnB : N + 8 < B)
    (hA : σ.arrs "TK" = arr) (hnv : σ.vars "N" = N) (hg0 : σ.vars "g" = 0) :
    ∃ σ', Run B dmaxLoop σ σ' ((40 + 4) * N + 6) ∧ σ'.vars "g" = runMaxD arr N ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ≠ "g" → y ≠ "i" → y ≠ "p" → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := dmaxBody) "i" "N"
    (DInv B arr N σ) N 40 (by omega) (fun _ h => h.hi) (fun _ h => h.vN)
    (dmaxBody_spec arr N σ hE hL hn hnB)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, hnv, by simp [Env.setVar], by
      simp only [Env.setVar]
      simp [runMaxD, hg0], by simp [Env.setVar, hg0]; omega, fun y a b c => by
      simp [Env.setVar, b]⟩
  refine ⟨σ', r, ?_, hI.arrs.trans (by simp [Env.setVar]), hI.out.trans (by simp [Env.setVar]), ?_⟩
  · rw [hI.hg, hi]
  · intro y a b c
    rw [hI.fr y a b c]

end Lax117284Proofs.Machine.BlockCheck

end

/-! ### `Lax117284Proofs.Machine.BlockProg` -/

section
/-!
The program that writes the reduction of Corollary 8 that adds a blocking client and a blocking
day, once the numbers of its input are in an array: the counts plus one, the new table cell by
cell, and the parameter `1`.
-/

namespace Lax117284Proofs.Machine.BlockProg

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.BlockSem
open Lax117284Proofs.Machine.InstSem

variable {B : ℕ}

/-- The two numbers of cell `t` of the new table, read off an array. -/
def cellG (arr : List ℕ) (n m bd t : ℕ) : List ℕ :=
  if t % (n + 1) < n then
    (if t / (n + 1) < m then
      [arr.getD (2 + 2 * (t / (n + 1) * n + t % (n + 1))) 0,
       arr.getD (2 + 2 * (t / (n + 1) * n + t % (n + 1)) + 1) 0]
    else [arr.getD (2 + 2 * (t % (n + 1))) 0, bd])
  else [bd, bd]

lemma cellB_eq (ns : List ℕ) (t : ℕ) :
    cellB ns t = cellG ns (ns.getD 0 0) (ns.getD 1 0) (bdOf ns) t := rfl

/-- Write a cell of the new table. -/
def cellBody : Com :=
  .seq (.assign "ca" (.bin .div (V "i") (V "n1")))
  (.seq (.assign "cb" (sub (V "i") (mul (V "ca") (V "n1"))))
   (.ite (.lt (V "cb") (V "n"))
     (.ite (.lt (V "ca") (V "m"))
        (.seq (.assign "cs" (add (mul (V "ca") (V "n")) (V "cb")))
          (.seq (emitCell "cs" 0) (emitCell "cs" 1)))
        (.seq (emitCell "cb" 0) (emitVar "bd")))
     (.seq (emitVar "bd") (emitVar "bd"))))

/-- Scratch scalars of a cell. -/
def SCB : List String := SCR ++ ["ca", "cb", "cs"]

/-- The cost of a cell. -/
def Kcell (Sz : ℕ) : ℕ := 100 + 2 * (48 * Sz + 60)

lemma mem_scb_iff {y : String} : y ∈ SCB ↔ y ∈ SCR ∨ y = "ca" ∨ y = "cb" ∨ y = "cs" := by
  simp [SCB, or_assoc]

lemma numBits_pair (a b : ℕ) : numBits [a, b] = bitsNat a ++ bitsNat b := by simp [numBits]

/-- **A cell of the old table.** -/
theorem branchOld (Sz : ℕ) (arr : List ℕ) (n m : ℕ) (σ : Env) (a b : ℕ)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ.arrs "TK" = arr) (hca : σ.vars "ca" = a) (hcb : σ.vars "cb" = b)
    (hn : σ.vars "n" = n) (ham : a < m) (hbn : b < n) (hnB : n + 8 < B)
    (hab : a * n + b < m * n) (haB : a + 8 < B)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 + 8 < B) (hL : 3 + 2 * (m * n) + 8 < B)
    (hlen : 3 + 2 * (m * n) ≤ arr.length) :
    ∃ σ', Run B (.seq (.assign "cs" (add (mul (V "ca") (V "n")) (V "cb")))
        (.seq (emitCell "cs" 0) (emitCell "cs" 1))) σ σ' (8 + 2 * (10 + (48 * Sz + 50))) ∧
      σ'.out = σ.out ++ (bitsNat (arr.getD (2 + 2 * (a * n + b)) 0) ++
        bitsNat (arr.getD (2 + 2 * (a * n + b) + 1) 0)) ∧
      (∀ y ∉ SCB, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  have hanB : a * n < B := by
    have : a * n ≤ a * n + b := by omega
    omega
  have e1 : (mul (V "ca") (V "n")).evalB B σ = some (a * n) := by
    have h := evalB_bin (B := B) (op := .mul) (evalB_var (B := B) (x := "ca") (σ := σ) (by omega))
      (evalB_var (B := B) (x := "n") (σ := σ) (by omega)) (by simp [hca, hn]; omega)
    simpa [hca, hn] using h
  have ev : (add (mul (V "ca") (V "n")) (V "cb")).evalB B σ = some (a * n + b) := by
    have h := evalB_bin (B := B) (op := .add) e1
      (evalB_var (B := B) (x := "cb") (σ := σ) (by omega)) (by simp [hcb]; omega)
    simpa [hcb] using h
  have r1 := Run.assign (x := "cs") ev
  set σ1 := σ.setVar "cs" (a * n + b) with hσ1
  have hcs : σ1.vars "cs" = a * n + b := by simp [hσ1, Env.setVar]
  have hA1 : σ1.arrs "TK" = arr := by simp [hσ1, Env.setVar, hA]
  have hidx : 2 + 2 * (a * n + b) + 1 < 3 + 2 * (m * n) := by omega
  obtain ⟨σ2, r2, o2, s2⟩ := emitCell_run (B := B) "cs" 0 Sz σ1
    (by rw [hcs, hA1]; omega) (by rw [hcs]; omega)
    (by rw [hcs, hA1]; have := hE (2 + 2 * (a * n + b) + 0) (by omega); omega)
    (by rw [hcs, hA1]; exact hs _ (by have := hE (2 + 2 * (a * n + b) + 0) (by omega); omega))
  have hcs2 : σ2.vars "cs" = a * n + b := by
    rw [s2.1 "cs" (by decide)]; exact hcs
  have hA2 : σ2.arrs "TK" = arr := by rw [s2.2]; exact hA1
  obtain ⟨σ3, r3, o3, s3⟩ := emitCell_run (B := B) "cs" 1 Sz σ2
    (by rw [hcs2, hA2]; omega) (by rw [hcs2]; omega)
    (by rw [hcs2, hA2]; have := hE (2 + 2 * (a * n + b) + 1) (by omega); omega)
    (by rw [hcs2, hA2]; exact hs _ (by have := hE (2 + 2 * (a * n + b) + 1) (by omega); omega))
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by simp [Expr.size] <;> omega), ?_, fun y hy => ?_, ?_⟩
  · rw [o3, o2, hcs2, hcs, hA2, hA1]
    simp [hσ1, Env.setVar]
  · have hy' : y ∉ SCR ∧ y ≠ "cs" := by
      rw [mem_scb_iff] at hy; tauto
    rw [s3.1 y hy'.1, s2.1 y hy'.1]
    simp [hσ1, Env.setVar, hy'.2]
  · rw [s3.2, s2.2]; simp [hσ1, Env.setVar]


/-- **A cell of the new day.** -/
theorem branchNew (Sz : ℕ) (arr : List ℕ) (n m bd : ℕ) (σ : Env) (b : ℕ)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ.arrs "TK" = arr) (hcb : σ.vars "cb" = b) (hbd : σ.vars "bd" = bd)
    (hbn : b < n) (hmpos : 0 < m) (hbdB : bd + 8 < B)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 + 8 < B) (hL : 3 + 2 * (m * n) + 8 < B)
    (hlen : 3 + 2 * (m * n) ≤ arr.length) :
    ∃ σ', Run B (.seq (emitCell "cb" 0) (emitVar "bd")) σ σ'
        (10 + (48 * Sz + 50) + (48 * Sz + 50)) ∧
      σ'.out = σ.out ++ (bitsNat (arr.getD (2 + 2 * b) 0) ++ bitsNat bd) ∧
      (∀ y ∉ SCB, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  have hnm : n ≤ m * n := Nat.le_mul_of_pos_left n hmpos
  have hidx : 2 + 2 * b < 3 + 2 * (m * n) := by omega
  obtain ⟨σ1, r1, o1, s1⟩ := emitCell_run (B := B) "cb" 0 Sz σ
    (by rw [hcb, hA]; omega) (by rw [hcb]; omega)
    (by rw [hcb, hA]; have := hE (2 + 2 * b + 0) (by omega); omega)
    (by rw [hcb, hA]; exact hs _ (by have := hE (2 + 2 * b + 0) (by omega); omega))
  have hbd1 : σ1.vars "bd" = bd := by rw [s1.1 "bd" (by decide)]; exact hbd
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitVar_spec (B := B) "bd" Sz σ1
    ⟨by rw [hbd1]; omega, by rw [hbd1]; exact hs _ (by omega)⟩
  have s2 : Same σ1 σ2 := same_of_frame v2 a2
  refine ⟨σ2, (r1.seq r2).mono (by omega), ?_, fun y hy => ?_, ?_⟩
  · rw [o2, o1, hbd1, hcb, hA]
    simp
  · have hy' : y ∉ SCR := by rw [mem_scb_iff] at hy; tauto
    rw [s2.1 y hy', s1.1 y hy']
  · rw [s2.2, s1.2]

/-- **A cell of the new client.** -/
theorem branchBlk (Sz : ℕ) (σ : Env) (bd : ℕ)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hbd : σ.vars "bd" = bd) (hbdB : bd + 8 < B) :
    ∃ σ', Run B (.seq (emitVar "bd") (emitVar "bd")) σ σ' ((48 * Sz + 50) + (48 * Sz + 50)) ∧
      σ'.out = σ.out ++ (bitsNat bd ++ bitsNat bd) ∧
      (∀ y ∉ SCB, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "bd" Sz σ
    ⟨by rw [hbd]; omega, by rw [hbd]; exact hs _ (by omega)⟩
  have s1 : Same σ σ1 := same_of_frame v1 a1
  have hbd1 : σ1.vars "bd" = bd := by rw [s1.1 "bd" (by decide)]; exact hbd
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitVar_spec (B := B) "bd" Sz σ1
    ⟨by rw [hbd1]; omega, by rw [hbd1]; exact hs _ (by omega)⟩
  have s2 : Same σ1 σ2 := same_of_frame v2 a2
  refine ⟨σ2, r1.seq r2, ?_, fun y hy => ?_, ?_⟩
  · rw [o2, o1, hbd1, hbd, List.append_assoc]
  · have hy' : y ∉ SCR := by rw [mem_scb_iff] at hy; tauto
    rw [s2.1 y hy', s1.1 y hy']
  · rw [s2.2, s1.2]


/-- **A cell of the new table.** -/
theorem cellBody_run (Sz : ℕ) (arr : List ℕ) (n m bd : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hm : σ.vars "m" = m)
    (hn1 : σ.vars "n1" = n + 1) (hbd : σ.vars "bd" = bd)
    (ht : σ.vars "i" < (m + 1) * (n + 1)) (hM1 : (m + 1) * (n + 1) + 8 < B)
    (hbdB : bd + 8 < B) (hnB : n + 8 < B) (hmB : m + 8 < B) (hmpos : 0 < m)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 + 8 < B) (hL : 3 + 2 * (m * n) + 8 < B)
    (hlen : 3 + 2 * (m * n) ≤ arr.length) :
    ∃ σ', Run B cellBody σ σ' (Kcell Sz) ∧
      σ'.out = σ.out ++ numBits (cellG arr n m bd (σ.vars "i")) ∧
      (∀ y ∉ SCB, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨t, ht'⟩ : ∃ t, σ.vars "i" = t := ⟨_, rfl⟩
  rw [ht'] at ht ⊢
  have hn1p : 0 < n + 1 := by omega
  obtain ⟨a, ha⟩ : ∃ a, a = t / (n + 1) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = t % (n + 1) := ⟨_, rfl⟩
  have hdm : (n + 1) * a + b = t := by rw [ha, hb]; exact Nat.div_add_mod t (n + 1)
  have hale : a ≤ t := by rw [ha]; exact Nat.div_le_self _ _
  have hb_lt : b < n + 1 := by rw [hb]; exact Nat.mod_lt _ hn1p
  have ha_lt : a < m + 1 := by rw [ha, Nat.div_lt_iff_lt_mul hn1p]; exact ht
  have hmc : a * (n + 1) = (n + 1) * a := Nat.mul_comm _ _
  have hiB : t < B := by omega
  -- the row
  have ev1 : (Expr.bin .div (V "i") (V "n1")).evalB B σ = some a := by
    have h := evalB_bin (B := B) (op := .div) (evalB_var (B := B) (x := "i") (σ := σ) (by omega))
      (evalB_var (B := B) (x := "n1") (σ := σ) (by omega)) (by simp [hn1, ht']; omega)
    simpa [hn1, ht', ha] using h
  have r1 := Run.assign (x := "ca") ev1
  set σ1 := σ.setVar "ca" a with hσ1
  have h1i : σ1.vars "i" = t := by simp [hσ1, Env.setVar, ht']
  have h1n1 : σ1.vars "n1" = n + 1 := by simp [hσ1, Env.setVar, hn1]
  have h1ca : σ1.vars "ca" = a := by simp [hσ1, Env.setVar]
  -- the column
  have ev2a : (mul (V "ca") (V "n1")).evalB B σ1 = some (a * (n + 1)) := by
    have h := evalB_bin (B := B) (op := .mul) (evalB_var (B := B) (x := "ca") (σ := σ1) (by omega))
      (evalB_var (B := B) (x := "n1") (σ := σ1) (by omega)) (by simp [h1ca, h1n1]; omega)
    simpa [h1ca, h1n1] using h
  have ev2 : (sub (V "i") (mul (V "ca") (V "n1"))).evalB B σ1 = some b := by
    have h := evalB_bin (B := B) (op := .sub) (evalB_var (B := B) (x := "i") (σ := σ1) (by omega))
      ev2a (by simp [h1i]; omega)
    have e : t - a * (n + 1) = b := by omega
    simpa [h1i, e] using h
  have r2 := Run.assign (x := "cb") ev2
  set σ2 := σ1.setVar "cb" b with hσ2
  have h2ca : σ2.vars "ca" = a := by simp [hσ2, Env.setVar, h1ca]
  have h2cb : σ2.vars "cb" = b := by simp [hσ2, Env.setVar]
  have h2n : σ2.vars "n" = n := by simp [hσ2, hσ1, Env.setVar, hn]
  have h2m : σ2.vars "m" = m := by simp [hσ2, hσ1, Env.setVar, hm]
  have h2bd : σ2.vars "bd" = bd := by simp [hσ2, hσ1, Env.setVar, hbd]
  have h2A : σ2.arrs "TK" = arr := by simp [hσ2, hσ1, Env.setVar, hA]
  have h2i : σ2.vars "i" = t := by simp [hσ2, hσ1, Env.setVar, ht']
  have hc1 : (Cond.lt (V "cb") (V "n")).evalB B σ2 = some (decide (b < n)) := by
    have h := evalB_condLt (B := B) (σ := σ2) (evalB_var (B := B) (x := "cb") (σ := σ2) (by omega))
      (evalB_var (B := B) (x := "n") (σ := σ2) (by omega))
    simpa [h2cb, h2n] using h
  have hc2 : (Cond.lt (V "ca") (V "m")).evalB B σ2 = some (decide (a < m)) := by
    have h := evalB_condLt (B := B) (σ := σ2) (evalB_var (B := B) (x := "ca") (σ := σ2) (by omega))
      (evalB_var (B := B) (x := "m") (σ := σ2) (by omega))
    simpa [h2ca, h2m] using h
  have hbase : ∀ σ' : Env, (∀ y ∉ SCB, σ'.vars y = σ2.vars y) → σ'.arrs = σ2.arrs →
      ∀ y ∉ SCB, σ'.vars y = σ.vars y := by
    intro σ' hv _ y hy
    have hyc : y ≠ "ca" := fun h => hy (by simp [SCB, h])
    have hyb : y ≠ "cb" := fun h => hy (by simp [SCB, h])
    rw [hv y hy]
    simp [hσ2, hσ1, Env.setVar, hyc, hyb]
  have hbase2 : ∀ σ' : Env, σ'.arrs = σ2.arrs → σ'.arrs = σ.arrs := by
    intro σ' h; rw [h]; simp [hσ2, hσ1, Env.setVar]
  by_cases hbn : b < n
  · by_cases ham : a < m
    · have hab : a * n + b < m * n := cell_lt ham hbn
      obtain ⟨σ3, r3, o3, v3, a3⟩ := branchOld (B := B) Sz arr n m σ2 a b hs h2A h2ca h2cb h2n ham hbn
        hnB hab (by omega) hE hL hlen
      have hcell : cellG arr n m bd t = [arr.getD (2 + 2 * (a * n + b)) 0,
          arr.getD (2 + 2 * (a * n + b) + 1) 0] := by
        unfold cellG; rw [← ha, ← hb, if_pos hbn, if_pos ham]
      refine ⟨σ3, (r1.seq (r2.seq (Run.ite_true (by simpa [hbn] using hc1)
        (Run.ite_true (by simpa [ham] using hc2) r3)))).mono ?_, ?_, hbase σ3 v3 a3,
        (a3.trans (hbase2 _ rfl))⟩
      · simp [Cond.size, Expr.size, Kcell]; omega
      · rw [o3, hcell, numBits_pair]
        simp [hσ2, hσ1, Env.setVar]
    · have ha' : a = m := by omega
      obtain ⟨σ3, r3, o3, v3, a3⟩ := branchNew (B := B) Sz arr n m bd σ2 b hs h2A h2cb h2bd hbn hmpos
        hbdB hE hL hlen
      have hcell : cellG arr n m bd t = [arr.getD (2 + 2 * b) 0, bd] := by
        unfold cellG; rw [← ha, ← hb, if_pos hbn, if_neg ham]
      refine ⟨σ3, (r1.seq (r2.seq (Run.ite_true (by simpa [hbn] using hc1)
        (Run.ite_false (by simpa [ham] using hc2) r3)))).mono ?_, ?_, hbase σ3 v3 a3,
        (a3.trans (hbase2 _ rfl))⟩
      · simp [Cond.size, Expr.size, Kcell]; omega
      · rw [o3, hcell, numBits_pair]
        simp [hσ2, hσ1, Env.setVar]
  · obtain ⟨σ3, r3, o3, v3, a3⟩ := branchBlk (B := B) Sz σ2 bd hs h2bd hbdB
    have hcell : cellG arr n m bd t = [bd, bd] := by
      unfold cellG; rw [← hb, if_neg hbn]
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_false (by simpa [hbn] using hc1) r3))).mono ?_, ?_,
      hbase σ3 v3 a3, (a3.trans (hbase2 _ rfl))⟩
    · simp [Cond.size, Expr.size, Kcell]; omega
    · rw [o3, hcell, numBits_pair]
      simp [hσ2, hσ1, Env.setVar]


/-! ### The loop over the cells and the whole output -/

lemma numBits_flatMap {α : Type} (L : List α) (f : α → List ℕ) :
    numBits (L.flatMap f) = L.flatMap (fun a => numBits (f a)) := by
  simp only [numBits, List.flatMap_assoc]

/-- The numbers of the output. -/
def outG (arr : List ℕ) (n m bd : ℕ) : List ℕ :=
  [n + 1, m + 1] ++ (List.range ((m + 1) * (n + 1))).flatMap (cellG arr n m bd) ++ [1]

/-- **The loop over the cells.** -/
theorem cellLoop_run (Sz : ℕ) (arr : List ℕ) (n m bd : ℕ) (σ0 : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ0.arrs "TK" = arr) (hn : σ0.vars "n" = n) (hm : σ0.vars "m" = m)
    (hn1 : σ0.vars "n1" = n + 1) (hbd : σ0.vars "bd" = bd)
    (hM : σ0.vars "M1" = (m + 1) * (n + 1)) (hM1 : (m + 1) * (n + 1) + 8 < B)
    (hbdB : bd + 8 < B) (hnB : n + 8 < B) (hmB : m + 8 < B) (hmpos : 0 < m)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 + 8 < B) (hL : 3 + 2 * (m * n) + 8 < B)
    (hlen : 3 + 2 * (m * n) ≤ arr.length) :
    ∃ σ', Run B (outLoop "M1" cellBody) σ0 σ' ((Kcell Sz + 10 + 4) * ((m + 1) * (n + 1)) + 6) ∧
      σ'.out = σ0.out ++ numBits ((List.range ((m + 1) * (n + 1))).flatMap (cellG arr n m bd)) ∧
      (∀ y ∉ "i" :: SCB, σ'.vars y = σ0.vars y) ∧ σ'.arrs = σ0.arrs := by
  obtain ⟨σ', r, o, hAg⟩ := eLoop (B := B) "M1" cellBody ("i" :: SCB)
    (fun t => numBits (cellG arr n m bd t)) (Kcell Sz) ((m + 1) * (n + 1)) σ0
    (by simp) (by decide) hM (by omega) (by
      intro σ hAg hlt
      have hA' : σ.arrs "TK" = arr := by rw [hAg.1]; exact hA
      have hn' : σ.vars "n" = n := by rw [hAg.2 "n" (by decide)]; exact hn
      have hm' : σ.vars "m" = m := by rw [hAg.2 "m" (by decide)]; exact hm
      have hn1' : σ.vars "n1" = n + 1 := by rw [hAg.2 "n1" (by decide)]; exact hn1
      have hbd' : σ.vars "bd" = bd := by rw [hAg.2 "bd" (by decide)]; exact hbd
      obtain ⟨σ1, r1, o1, v1, a1⟩ := cellBody_run (B := B) Sz arr n m bd σ hs hA' hn' hm' hn1' hbd'
        hlt hM1 hbdB hnB hmB hmpos hE hL hlen
      refine ⟨σ1, r1, o1, ⟨a1.trans hAg.1, fun y hy => ?_⟩, ?_⟩
      · have hy' : y ∉ SCB := fun h => hy (List.mem_cons_of_mem _ h)
        rw [v1 y hy', hAg.2 y hy]
      · exact v1 "i" (by decide))
  refine ⟨σ', r, ?_, hAg.2, hAg.1⟩
  rw [o, numBits_flatMap]

/-- Write the whole output. -/
def printBlock : Com :=
  .seq (emitVar "n1") (.seq (emitVar "m1") (.seq (outLoop "M1" cellBody) (emitLit 1)))

/-- The cost of writing the output. -/
def Kprint (Sz M1 : ℕ) : ℕ := 3 * (48 * Sz + 50) + (Kcell Sz + 10 + 4) * M1 + 6

/-- **Writing the output.** -/
theorem printBlock_run (Sz : ℕ) (arr : List ℕ) (n m bd : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hm : σ.vars "m" = m)
    (hn1 : σ.vars "n1" = n + 1) (hm1 : σ.vars "m1" = m + 1) (hbd : σ.vars "bd" = bd)
    (hM : σ.vars "M1" = (m + 1) * (n + 1)) (hM1 : (m + 1) * (n + 1) + 8 < B)
    (hbdB : bd + 8 < B) (hnB : n + 8 < B) (hmB : m + 8 < B) (hmpos : 0 < m)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 + 8 < B) (hL : 3 + 2 * (m * n) + 8 < B)
    (hlen : 3 + 2 * (m * n) ≤ arr.length) :
    ∃ σ', Run B printBlock σ σ' (Kprint Sz ((m + 1) * (n + 1))) ∧
      σ'.out = σ.out ++ numBits (outG arr n m bd) := by
  -- the number of clients plus one
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "n1" Sz σ
    ⟨by rw [hn1]; omega, by rw [hn1]; exact hs _ (by omega)⟩
  have z1 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ1.vars y = σ.vars y := v1
  -- the number of days plus one
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitVar_spec (B := B) "m1" Sz σ1
    ⟨by rw [v1 "m1" (by decide), hm1]; omega, by rw [v1 "m1" (by decide), hm1]; exact hs _ (by omega)⟩
  have z2 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ2.vars y = σ.vars y := fun y hy => by
    rw [v2 y hy, v1 y hy]
  have A2 : σ2.arrs "TK" = arr := by rw [a2, a1]; exact hA
  -- the cells
  obtain ⟨σ3, r3, o3, v3, a3⟩ := cellLoop_run (B := B) Sz arr n m bd σ2 hs A2
    (by rw [z2 "n" (by decide)]; exact hn) (by rw [z2 "m" (by decide)]; exact hm)
    (by rw [z2 "n1" (by decide)]; exact hn1) (by rw [z2 "bd" (by decide)]; exact hbd)
    (by rw [z2 "M1" (by decide)]; exact hM) hM1 hbdB hnB hmB hmpos hE hL hlen
  obtain ⟨σ4, r4, o4, v4, a4⟩ := (emitLit_spec (B := B) 1 Sz (by omega) (hs _ (by omega))) σ3 trivial
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by unfold Kprint; omega), ?_⟩
  rw [o4, o3, o2, o1, z1 "m1" (by decide), hm1, hn1]
  unfold outG
  simp only [numBits_append, numBits_cons, numBits_nil, List.append_nil, List.append_assoc]

end Lax117284Proofs.Machine.BlockProg

end
