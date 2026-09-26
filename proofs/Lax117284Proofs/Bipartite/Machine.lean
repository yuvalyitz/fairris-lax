import Lax117284.BipartiteKuhnTime
import Lax117284.BipartiteDecision
import Lax117284Proofs.Bipartite.GraphBridge
import Lax117284Proofs.Bipartite.Ram2.MainProg
import Lax117284Proofs.Bipartite.Ram2.Bridge

/-!
Kuhn's algorithm as a word RAM program: the layout, the value bound, the word-length hypothesis,
the running-time inequality, and the transfer to the machine, for the three concept statements
`Lax117284.BipartiteKuhnTime.computes`, `Lax117284.BipartiteDecision.decides_saturating` and
`Lax117284.BipartiteDecision.decides_perfect`.

The three programs share `Ram2.preCom` (read the word, one search per left vertex, count the
matched right vertices) and differ in their last command: write the count; compare it with `n`;
compare it with `V - count` (that is, test `2 · count = V` without a value above the bound). All
three run within `c · (n + 1) · (|x| + 1)` machine instructions with `c = 5000`, at every word
length `w` with `c · (|x| + 1) ≤ 2 ^ w`, under the value bound `|x| + 8`.
-/

namespace Lax117284Proofs.Bipartite.Machine

open Lax808846.Ram Lax808846.RamComputes
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846Proofs.Simulation Lax808846Proofs.Machine
open Lax117284Proofs.Bipartite.Ram2
open Lax271696.GraphEncoding Lax117284.BipartiteGraph Lax117284.BipartiteMatching Lax117284.BipartiteKuhn
open scoped Classical

/-! ### The programs -/

/-- Write the count. -/
def outCount : Com := .write (.var "count")

/-- Write whether the count is `n`. -/
def outSat : Com :=
  .ite (.eq (.var "count") (.var "n")) (.write (.lit 1)) (.write (.lit 0))

/-- Write whether the count is `V - count`, that is, whether `2 · count = V`. -/
def outPerf : Com :=
  .ite (.eq (.var "count") (.sub (.var "V") (.var "count"))) (.write (.lit 1)) (.write (.lit 0))

/-- The program with its final command. -/
def progCom (fin : Com) : Com := .seq preCom fin

/-- The layout: every scalar and array of the programs. -/
def layout : Layout :=
  ⟨["len", "rt", "v", "V", "n", "m", "l0", "top", "result", "t1", "i", "x", "xe", "found",
    "foundJ", "cand", "cont", "occ", "k", "rr", "ll", "j", "count"],
   ["a", "vis", "mu", "stkL", "stkR", "stkX"], 8⟩

theorem preCom_ok : Com.Ok layout preCom := by
  simp [preCom, readAll, readBody, hdrCom, outerLoop, outerBody, restartCom, restartHead,
    clearVis, clearVisBody, searchCom, turnCom, preludeCom, scanRowEarly, computeCont, scanBody,
    candExpr, afterScanCom, popCom, foundCom, readMu, pushCom, applyCom, applyBodyCom, writeMu,
    countCom, countBody, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem outCount_ok : Com.Ok layout (progCom outCount) :=
  ⟨preCom_ok, by simp [outCount, layout, Com.Ok, Expr.Ok]⟩

theorem outSat_ok : Com.Ok layout (progCom outSat) :=
  ⟨preCom_ok, by simp [outSat, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]⟩

theorem outPerf_ok : Com.Ok layout (progCom outPerf) :=
  ⟨preCom_ok, by simp [outPerf, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]⟩

theorem const_eq : layout.const = 10 := by simp [Layout.const]

/-! ### The value bound and the word length -/

/-- The value bound the programs run under. -/
def Bof (x : List ℕ) : ℕ := x.length + 8

/-- The constant of the time bound. -/
def cst : ℕ := 5000

theorem fits {x : List ℕ} {w : ℕ} (hx : cst * (x.length + 1) ≤ 2 ^ w) :
    layout.FitsWords (Bof x) w := by
  refine fitsWords_of_max_le (by unfold Bof; omega) ?_
  simp only [Layout.span, layout, List.length_cons, List.length_nil, max_le_iff, Bof]
  unfold cst at hx
  constructor <;> omega

/-! ### The running time -/

theorem time_arith (n l I K : ℕ) (hI : I ≤ 400 * (l + 1))
    (hK : K ≤ 14 * l + 18 * l + I * n + 40) : 10 * K + 2 ≤ cst * (n + 1) * (l + 1) := by
  have h2 : I * n ≤ 400 * (l + 1) * n := Nat.mul_le_mul_right n hI
  have h3 : cst * (n + 1) * (l + 1) = 5000 * ((l + 1) * n) + 5000 * (l + 1) := by unfold cst; ring
  have h4 : 400 * (l + 1) * n = 400 * ((l + 1) * n) := by ring
  rw [h3]; rw [h4] at h2
  generalize (l + 1) * n = P at h2 ⊢
  omega

theorem iterCost_le {x : List ℕ} (hg : Good x) : iterCost x ≤ 400 * (x.length + 1) := by
  have h1 := hg.m_lt
  have h2 := hg.off_lt_len (i := Vw x) le_rfl
  unfold iterCost restartCost searchCost potD potW
  omega

theorem preCost_le {x : List ℕ} (hg : Good x) :
    preCost x ≤ 14 * x.length + 18 * x.length + iterCost x * nw x + 32 := by
  have h1 := hg.m_lt
  unfold preCost
  omega

/-- **From an IMP+ run to the machine**, with the concept's time bound. -/
theorem run_to_machine {x : List ℕ} {w : ℕ} (hg : Good x) (hfit : cst * (x.length + 1) ≤ 2 ^ w)
    {c : Com} (hok : Com.Ok layout c) {σ' : Env} {K : ℕ}
    (hr : Run (Bof x) c (lenEnv (extOf x) x) σ' K) (hK : K ≤ preCost x + 8) :
    ∃ t ≤ cst * (nw x + 1) * (x.length + 1), RunsTo w (wrapProgram layout c) x σ'.out t := by
  obtain ⟨k, hk, hbs⟩ := hr
  obtain ⟨t, ht, hrun⟩ := wrap_runsTo (fits hfit) hok (by simp [layout])
    (fun v hv => lt_of_lt_of_le (hg.ent_lt v hv) (by unfold Bof; omega)) (by unfold Bof; omega)
    hbs
  refine ⟨t, ?_, hrun⟩
  rw [const_eq] at ht
  have h1 := iterCost_le hg
  have h2 := preCost_le hg
  have h3 := time_arith (nw x) x.length (iterCost x) k h1 (by omega)
  omega

/-! ### The final commands -/

section Fin

variable {x : List ℕ} {σ : Env}

theorem outCount_run (hg : Good x) (hc : σ.vars "count" ≤ mw x) :
    Run (Bof x) outCount σ { σ with out := σ.out ++ [σ.vars "count"] } 2 := by
  have := hg.m_lt
  exact RunStep.write (Bof x) σ (.var "count") _ (RunStep.eval_var _ σ "count" (by unfold Bof; omega))

theorem outSat_run (hg : Good x) (hc : σ.vars "count" ≤ mw x) (hn : σ.vars "n" = nw x) :
    Run (Bof x) outSat σ { σ with out := σ.out ++ [if σ.vars "count" = nw x then 1 else 0] } 6 := by
  have := hg.m_lt
  have := hg.n_lt
  have e1 := RunStep.eval_var (Bof x) σ "count" (by unfold Bof; omega)
  have e2 := RunStep.eval_var (Bof x) σ "n" (by unfold Bof; omega)
  have w1 := RunStep.write (Bof x) σ (.lit 1) 1 (RunStep.eval_lit _ 1 σ (by unfold Bof; omega))
  have w0 := RunStep.write (Bof x) σ (.lit 0) 0 (RunStep.eval_lit _ 0 σ (by unfold Bof; omega))
  by_cases h : σ.vars "count" = nw x
  · rw [if_pos h]
    exact RunStep.ite_true _ _ _ _ σ _ _ (RunStep.cond_eq_true _ σ _ _ _ _ e1 e2 (by rw [hn]; exact h)) w1
  · rw [if_neg h]
    exact RunStep.ite_false _ _ _ _ σ _ _ (RunStep.cond_eq_false _ σ _ _ _ _ e1 e2 (by rw [hn]; exact h)) w0

theorem outPerf_run (hg : Good x) (hc : σ.vars "count" ≤ mw x) (hV : σ.vars "V" = Vw x) :
    Run (Bof x) outPerf σ
      { σ with out := σ.out ++ [if 2 * σ.vars "count" = Vw x then 1 else 0] } 8 := by
  have := hg.m_lt
  have := hg.V_lt
  have hcV : σ.vars "count" ≤ Vw x := by unfold mw at hc; omega
  have e1 := RunStep.eval_var (Bof x) σ "count" (by unfold Bof; omega)
  have e2 := RunStep.eval_var (Bof x) σ "V" (by unfold Bof; omega)
  have e3 := RunStep.eval_sub (Bof x) σ (.var "V") (.var "count") _ _ e2 e1 (by unfold Bof; omega)
  have w1 := RunStep.write (Bof x) σ (.lit 1) 1 (RunStep.eval_lit _ 1 σ (by unfold Bof; omega))
  have w0 := RunStep.write (Bof x) σ (.lit 0) 0 (RunStep.eval_lit _ 0 σ (by unfold Bof; omega))
  by_cases h : 2 * σ.vars "count" = Vw x
  · rw [if_pos h]
    exact RunStep.ite_true _ _ _ _ σ _ _
      (RunStep.cond_eq_true _ σ _ _ _ _ e1 e3 (by rw [hV]; omega)) w1
  · rw [if_neg h]
    exact RunStep.ite_false _ _ _ _ σ _ _
      (RunStep.cond_eq_false _ σ _ _ _ _ e1 e3 (by rw [hV]; omega)) w0

end Fin

/-! ### The word determines the answer -/

/-- What an admissible word gives: the machine's size is the matching number of the word's graph,
the word's graph is split at `n = nw x`, and the header values are the concept's. -/
theorem admissible_facts {x : List ℕ} {V : ℕ} {G : SimpleGraph (Fin V)} {n : ℕ}
    (h : EncodesBipartite x V G n) :
    Good x ∧ leftCount x = nw x ∧ vertexCount x = Vw x ∧ nw x ≤ Vw x ∧
      SplitAt (wordGraph x) (nw x) ∧ kuhnSize x = matchingNumber (wordGraph x) := by
  have hg := good_of_encodes h
  have hVe := vertexCount_eq h
  have hne := nw_eq h
  have hlc := leftCount_eq h
  subst hVe
  subst hne
  have h' := h
  obtain ⟨-, -, -, hnV, hs⟩ := h'
  have hwg : wordGraph x = G := wordGraph_eq h
  have hadj : adjF (adjw x) (nw x) (mw x) = Lax117284.BipartiteKuhnCorrect.leftRel G (nw x) hnV := by
    funext i j
    exact propext (adjw_iff h i j i.2 j.2)
  refine ⟨hg, hlc, rfl, hnV, by rw [hwg]; exact hs, ?_⟩
  unfold kuhnSize
  rw [hadj, hwg]
  exact Lax117284Proofs.Bipartite.GraphBridge.kuhn_matchingNumber G (nw x) hnV hs

theorem kuhnSize_le (x : List ℕ) : kuhnSize x ≤ mw x := by
  unfold kuhnSize
  have := Lax117284Proofs.Bipartite.GraphBridge.size_le_card_right (kuhn (adjF (adjw x) (nw x) (mw x)))
  rwa [Fintype.card_fin] at this

/-! ### The theorems -/

/-- The common run: `preCom` on an admissible word, then the final command. -/
theorem prog_run {x : List ℕ} {w : ℕ} {V : ℕ} {G : SimpleGraph (Fin V)} {n : ℕ}
    (h : EncodesBipartite x V G n) (hfit : cst * (x.length + 1) ≤ 2 ^ w) (fin : Com)
    (hok : Com.Ok layout (progCom fin)) (f : ℕ → List ℕ) (Kf : ℕ) (hKf : Kf ≤ 8)
    (hfin : ∀ σ : Env, σ.vars "count" = kuhnSize x → σ.vars "n" = nw x → σ.vars "V" = Vw x →
      σ.out = [] → Run (Bof x) fin σ { σ with out := f (kuhnSize x) } Kf) :
    ∃ t ≤ cst * (leftCount x + 1) * (x.length + 1),
      RunsTo w (wrapProgram layout (progCom fin)) x (f (kuhnSize x)) t := by
  obtain ⟨hg, hlc, -, -, -, -⟩ := admissible_facts h
  obtain ⟨σ', K, hr, hK, hcount, hn', hV', hout⟩ := pre_run (B := Bof x) hg le_rfl
  have hf := hfin σ' hcount hn' hV' hout
  obtain ⟨t, ht, hrun⟩ := run_to_machine hg hfit hok (hr.seq hf) (by omega)
  rw [hlc]
  exact ⟨t, ht, hrun⟩

/--
---
conclusion: Lax117284.BipartiteKuhnTime.computes
---
Kuhn's algorithm as a word RAM program. The program stores the input length, reads the word into
an array, and runs one augmenting search per left vertex in the order of the word, each scanning
the compressed sparse rows it reaches at most once and visiting each right vertex at most once,
paid for by a potential linear in the word; it then counts the matched right vertices and writes
the count, which is the size of Kuhn's matching of the adjacency across the split
(`Ram2.OuterMath.MatchInv.size_eq_kuhn`), hence the matching number of the graph
(`GraphBridge.kuhn_matchingNumber`), with `c = 5000`.
-/
theorem computes : ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog
      {x | (∃ (V : ℕ) (G : SimpleGraph (Fin V)) (n : ℕ), EncodesBipartite x V G n) ∧
        c * (x.length + 1) ≤ 2 ^ w}
      (fun x => [matchingNumber (wordGraph x)])
      (fun x => c * (leftCount x + 1) * (x.length + 1)) := by
  refine ⟨wrapProgram layout (progCom outCount), cst, fun w => ?_⟩
  rintro x ⟨⟨V, G, n, h⟩, hfit⟩
  obtain ⟨hg, -, -, -, -, hsize⟩ := admissible_facts h
  have := prog_run h hfit outCount outCount_ok (fun k => [k]) 2 (by omega) (fun σ hc hn hV hout => by
    have := outCount_run hg (σ := σ) (by rw [hc]; exact kuhnSize_le x)
    rw [hout, hc] at this
    simpa using this)
  rwa [hsize] at this

/--
---
conclusion: Lax117284.BipartiteDecision.decides_saturating
---
The same program, ending with a comparison of the count with `n`: a matching saturating the left
side exists exactly when the matching number is `n` (`GraphBridge.exists_saturating_iff`).
-/
theorem decides_saturating : ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog (Lax117284.BipartiteDecision.Dom c w)
      (fun x => if ∃ M : (wordGraph x).Subgraph, M.IsMatching ∧
          Saturates (wordGraph x) M (leftSide (vertexCount x) (leftCount x)) then [1] else [0])
      (fun x => c * (leftCount x + 1) * (x.length + 1)) := by
  refine ⟨wrapProgram layout (progCom outSat), cst, fun w => ?_⟩
  rintro x ⟨⟨V, G, n, h⟩, hfit⟩
  obtain ⟨hg, hlc, hVc, hnV, hs, hsize⟩ := admissible_facts h
  have := prog_run h hfit outSat outSat_ok (fun k => [if k = nw x then 1 else 0]) 6 (by omega)
    (fun σ hc hn hV hout => by
      have := outSat_run hg (σ := σ) (by rw [hc]; exact kuhnSize_le x) hn
      rw [hout, hc] at this
      simpa using this)
  have hiff := Lax117284Proofs.Bipartite.GraphBridge.exists_saturating_iff (wordGraph x) (nw x) hnV hs
  beta_reduce
  rw [hlc] at this ⊢
  rw [hsize] at this
  by_cases hex : ∃ M : (wordGraph x).Subgraph, M.IsMatching ∧
      Saturates (wordGraph x) M (leftSide (vertexCount x) (nw x))
  · rw [if_pos hex]
    rw [if_pos (hiff.1 hex)] at this
    exact this
  · rw [if_neg hex]
    rw [if_neg (fun h' => hex (hiff.2 h'))] at this
    exact this

/--
---
conclusion: Lax117284.BipartiteDecision.decides_perfect
---
The same program, ending with the test `count = V - count`, that is `2 · count = V` (the count is
at most `V`, so the subtraction is exact): a perfect matching exists exactly when twice the
matching number is the number of vertices (`GraphBridge.exists_perfect_iff`).
-/
theorem decides_perfect : ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog (Lax117284.BipartiteDecision.Dom c w)
      (fun x => if ∃ M : (wordGraph x).Subgraph, M.IsPerfectMatching then [1] else [0])
      (fun x => c * (leftCount x + 1) * (x.length + 1)) := by
  refine ⟨wrapProgram layout (progCom outPerf), cst, fun w => ?_⟩
  rintro x ⟨⟨V, G, n, h⟩, hfit⟩
  obtain ⟨hg, hlc, hVc, hnV, hs, hsize⟩ := admissible_facts h
  have := prog_run h hfit outPerf outPerf_ok (fun k => [if 2 * k = Vw x then 1 else 0]) 8
    (by omega) (fun σ hc hn hV hout => by
      have := outPerf_run hg (σ := σ) (by rw [hc]; exact kuhnSize_le x) hV
      rw [hout, hc] at this
      simpa using this)
  have hiff := Lax117284Proofs.Bipartite.GraphBridge.exists_perfect_iff (wordGraph x) (nw x) hnV hs
  beta_reduce
  rw [hsize, ← hVc] at this
  by_cases hex : ∃ M : (wordGraph x).Subgraph, M.IsPerfectMatching
  · rw [if_pos hex]
    rw [if_pos (hiff.1 hex)] at this
    exact this
  · rw [if_neg hex]
    rw [if_neg (fun h' => hex (hiff.2 h'))] at this
    exact this

end Lax117284Proofs.Bipartite.Machine
