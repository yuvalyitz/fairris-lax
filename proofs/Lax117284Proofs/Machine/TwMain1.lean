import Lax117284Proofs.Machine.ClMainRead
import Lax117284Proofs.Machine.ClBruteFinal
import Lax117284Proofs.Machine.TwPrep3
import Lax117284Proofs.Machine.TwGraph3
import Lax117284Proofs.Machine.TwSetup4
import Lax117284Proofs.Machine.TwDpSetup
import Lax117284Proofs.Machine.TwZero

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
