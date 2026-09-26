import Lax117284.BipartiteDecision
import Lax117284Proofs.Bipartite.Ram2.TotalMain
import Lax117284Proofs.Bipartite.Ram2.Bits

/-!
The total decider on the machine: the layout, the transfer of `Ram2.tot_run` to the word RAM,
and the two statements.

`ramPolytime_saturating` is the concept's statement: one program reads the length-prefixed word
and writes `saturatingAnswer` within `20000 · (bitSize x + 1)²` instructions at every word length
from `bitSize x + 11` on.

`decides_saturating_all` is the concept's statement, whose domain asks the length and every entry
to fit, `∀ v ∈ x, c · (v + 1) ≤ 2 ^ w`. The clause on the entries is necessary: the domain
`c · (|x| + 1) ≤ 2 ^ w` alone admits no program: the machine reads an entry `v ≥ 2 ^ w` as
`v mod 2 ^ w`, so the well-formed word `[1, 0, 0, 0, 0]` (answer `[1]`) and the malformed word
`[1 + 2 ^ w, 0, 0, 0, 0]` (answer `[0]`) are indistinguishable to every program at word length
`w`, and both are in that domain once `6 c ≤ 2 ^ w`.
-/

namespace Lax117284Proofs.Bipartite.MachineTotal

open Lax808846.Ram Lax808846.RamComputes
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846Proofs.Simulation Lax808846Proofs.Machine
open Lax117284Proofs.Bipartite.Ram2
open Lax271696.GraphEncoding Lax117284.BipartiteGraph Lax117284.BipartiteMatching Lax117284.BipartiteDecision
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open scoped Classical

/-- The layout: every scalar and array of the total program. -/
def layoutT : Layout :=
  ⟨["len", "rt", "v", "V", "E", "n", "ok", "i", "j", "je", "e2", "u", "tt", "l", "m", "l0",
    "top", "result", "t1", "x", "xe", "found", "foundJ", "cand", "cont", "occ", "k", "rr",
    "ll", "count"],
   ["t", "a", "deg", "pos", "vis", "mu", "stkL", "stkR", "stkX"], 8⟩

theorem totCom_ok : Com.Ok layoutT totCom := by
  simp [totCom, readT, readTBody, hdrT, chk1, guarded, chk2, chk2Body, chk3, chk3Body, degPass,
    rowIter, degBody, degThen, degElse, heavyTot, prefixCom, prefixBody, prefixThen, prefixElse,
    posCom, posBody, fillPass, fillBody, fillThen, fillElse, finalC, outerLoop, outerBody,
    restartCom, restartHead, clearVis, clearVisBody, searchCom, turnCom, preludeCom, scanRowEarly,
    computeCont, scanBody, candExpr, afterScanCom, popCom, foundCom, readMu, pushCom, applyCom,
    applyBodyCom, writeMu, countCom, countBody, layoutT, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem const_eq : layoutT.const = 10 := by simp [Layout.const]

theorem BofT_hx (x : List ℕ) : ∀ v ∈ x, v < BofT x := fun v hv => by
  have := le_mxE hv
  unfold BofT; omega

/-- The cost, in terms of the concept's `leftCount`. -/
theorem totCost_le (x : List ℕ) :
    totCost x ≤ 600 * (x.length + 1) + 400 * ((x.length + 1) * leftCount x) := by
  unfold totCost
  rw [← nw_eq_leftCount]
  split_ifs <;> omega

/-- On a well-formed word the left count is below the length. -/
theorem leftCount_lt_of_wf {x : List ℕ} (hw : WellFormed x) : leftCount x < x.length := by
  have := hw.left_le; have := hw.length_eq; omega

theorem totCost_le_sq (x : List ℕ) : totCost x ≤ 1000 * ((x.length + 1) * (x.length + 1)) := by
  unfold totCost
  split_ifs with hw
  · have h1 := leftCount_lt_of_wf hw
    rw [nw_eq_leftCount] at *
    have h2 : (x.length + 1) * leftCount x ≤ (x.length + 1) * (x.length + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : x.length + 1 ≤ (x.length + 1) * (x.length + 1) := Nat.le_mul_self _
    omega
  · have h3 : x.length + 1 ≤ (x.length + 1) * (x.length + 1) := Nat.le_mul_self _
    omega

/-! ### The theorem on the length-prefixed word -/

/-- The program on the length-prefixed word. -/
def pcomT : Com := .seq (.read "len") totCom

theorem pcomT_ok : Com.Ok layoutT pcomT := ⟨by simp [layoutT, Com.Ok], totCom_ok⟩

theorem pcomT_run (x : List ℕ) :
    ∃ σ', Run (BofT x) pcomT (initEnv (extT x) (x.length :: x)) σ' (1 + totCost x) ∧
      σ'.out = saturatingAnswer x := by
  obtain ⟨σ', K, hr, hK, hout⟩ := tot_run x
  have h1 : Run (BofT x) (.read "len") (initEnv (extT x) (x.length :: x))
      (lenEnv (extT x) x) 1 := Run.read (by rfl)
  exact ⟨σ', (h1.seq hr).mono (by omega), hout⟩

theorem solvesT (x : List ℕ) :
    Solves layoutT pcomT {z | z = x.length :: x} (fun _ => saturatingAnswer x) (fun _ => BofT x)
      (fun _ => 1 + totCost x) where
  ok := pcomT_ok
  inp := by
    intro z hz v hv
    rw [hz] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · unfold BofT; omega
    · exact BofT_hx x v hv'
  run := by
    intro z hz
    rw [hz]
    obtain ⟨σ', hr, ho⟩ := pcomT_run x
    exact ⟨extT x, σ', hr, ho⟩

theorem span_le (x : List ℕ) :
    max (BofT x) (layoutT.span (BofT x)) ≤ 72 * (x.length + 3 * mxE x + 1) + 402 := by
  simp only [Layout.span, layoutT, List.length_cons, List.length_nil, max_le_iff]
  unfold BofT
  omega

theorem fitT (x : List ℕ) : max (BofT x) (layoutT.span (BofT x)) ≤ 2 ^ (bitSize x + 10) := by
  have hlen := length_le_bitSize x
  have hmx : mxE x < 2 ^ (bitSize x + 1) := by
    rcases mxE_cases x with h | h
    · rw [h]; exact Nat.pos_of_ne_zero (by positivity)
    · exact mem_lt_two_pow_bitSize_add_one h
  have hs : bitSize x < 2 ^ bitSize x := Nat.lt_two_pow_self
  have e1 : (2 : ℕ) ^ (bitSize x + 1) = 2 * 2 ^ bitSize x := by ring
  have e2 : (2 : ℕ) ^ (bitSize x + 10) = 1024 * 2 ^ bitSize x := by ring
  have := span_le x
  omega

theorem time_boundT (x : List ℕ) :
    10 * (1 + totCost x) + 1 ≤ 20000 * (bitSize x + 1) ^ 2 := by
  have hlen := length_le_bitSize x
  have h1 := totCost_le_sq x
  have h2 : (x.length + 1) * (x.length + 1) ≤ (bitSize x + 1) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have h3 : 1 ≤ (bitSize x + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem prog_runsT (w : ℕ) (x : List ℕ) (hw : bitSize x + 11 ≤ w) :
    ∃ t ≤ 20000 * (bitSize x + 1) ^ 2,
      RunsTo w (compileProgram layoutT pcomT) (x.length :: x) (saturatingAnswer x) t := by
  have hfit : layoutT.FitsWords (BofT x) w := by
    refine fitsWords_of_max_le (by unfold BofT; omega) ?_
    exact (fitT x).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h := computesInTime_of_solves (w := w) (T := fun _ => 10 * (1 + totCost x) + 1)
    (solvesT x) (fun z hz => hfit) (fun z hz => by rw [const_eq])
  obtain ⟨t, ht, hrun⟩ := h (x.length :: x) rfl
  exact ⟨t, ht.trans (time_boundT x), hrun⟩

/--
---
conclusion: Lax117284.BipartiteDecision.ramPolytime_saturating
---
The total program reads the word into an array, validates the syntactic conditions of
`WellFormed` in linear time, checks that every listed edge crosses the split while counting the
degrees of the symmetrized word, builds that word by a counting sort (each left row the union of
its own row and the transposed right rows), runs Kuhn's algorithm on it and compares the size
of the matching with the number of left vertices; on any failed check it answers `0`. The
program is compiled for the length-prefixed word, runs at every word length from
`bitSize x + 11` on, and within `20000 · (bitSize x + 1)²` instructions.
-/
theorem ramPolytime_saturating : RamPolytime saturatingAnswer := by
  refine ramPolytime_of_wordlen (d := 1) (K := 10) (prog := compileProgram layoutT pcomT)
    (Polynomial.C 20000 * (Polynomial.X + Polynomial.C 1) ^ 2) le_rfl ?_ ?_
  · intro x v hv
    unfold saturatingAnswer at hv
    have h2 : (2 : ℕ) ^ 10 ≤ 2 ^ (1 * bitSize x + 10) := Nat.pow_le_pow_right (by omega) (by omega)
    split_ifs at hv <;> simp at hv <;> omega
  · intro w x hw
    obtain ⟨t, ht, hr⟩ := prog_runsT w x (by omega)
    refine ⟨t, ?_, hr⟩
    simpa [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add] using ht

/-! ### The theorem on the plain word, on the fitting domain -/

/-- The constant of the time bound. -/
def cst : ℕ := 20000

theorem fit_plain {x : List ℕ} {w : ℕ} (h1 : cst * (x.length + 1) ≤ 2 ^ w)
    (h2 : ∀ v ∈ x, cst * (v + 1) ≤ 2 ^ w) : layoutT.FitsWords (BofT x) w := by
  refine fitsWords_of_max_le (by unfold BofT; omega) ?_
  have hm : cst * (mxE x + 1) ≤ 2 ^ w := by
    rcases mxE_cases x with h | h
    · rw [h]; unfold cst at *; omega
    · exact h2 _ h
  have := span_le x
  unfold cst at h1 hm
  omega

theorem time_plain (x : List ℕ) {k : ℕ} (hk : k ≤ totCost x) :
    10 * k + 2 ≤ cst * (leftCount x + 1) * (x.length + 1) := by
  have h1 := totCost_le x
  have e : cst * (leftCount x + 1) * (x.length + 1) =
      cst * ((x.length + 1) * leftCount x) + cst * (x.length + 1) := by unfold cst; ring
  rw [e]
  unfold cst
  omega

/--
---
conclusion: Lax117284.BipartiteDecision.decides_saturating_all
---
On every word whose length and entries fit the word length, the total program — the linear
well-formedness check, the symmetrization of the adjacency lists into left rows, one search of
Kuhn's algorithm per left vertex, and the comparison of the count with `n` — decides the
saturating question within `c · (n + 1) · (|x| + 1)` instructions, `c = 20000`.
-/
theorem decides_saturating_all : ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog {x | c * (x.length + 1) ≤ 2 ^ w ∧ ∀ v ∈ x, c * (v + 1) ≤ 2 ^ w}
      saturatingAnswer (fun x => c * (leftCount x + 1) * (x.length + 1)) := by
  refine ⟨wrapProgram layoutT totCom, cst, fun w => ?_⟩
  rintro x ⟨h1, h2⟩
  obtain ⟨σ', K, ⟨k, hk, hbs⟩, hK, hout⟩ := tot_run x
  obtain ⟨t, ht, hrun⟩ := wrap_runsTo (fit_plain h1 h2) totCom_ok (by simp [layoutT])
    (BofT_hx x) (by unfold BofT; omega) hbs
  refine ⟨t, ?_, hout ▸ hrun⟩
  rw [const_eq] at ht
  exact ht.trans (time_plain x (hk.trans hK))

end Lax117284Proofs.Bipartite.MachineTotal
