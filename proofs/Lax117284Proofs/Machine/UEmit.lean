import Lax808846Proofs.Tactic
import Lax117284Proofs.UnitPGraph
import Lax117284Proofs.Machine.MisBlk

/-!
Writing a run of equal numbers: `emitRep val e` writes `val` as many times as `e` says. It is the
one output loop of the reduction of the unit processing times to matching: every row of the
table is a few runs of zeros and one run of ones.
-/

namespace Lax117284Proofs.Machine.UEmit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

variable {B : ℕ}

/-- One round: write `val` and count. -/
def repBody (val : ℕ) : Com :=
  .seq (.write (.lit val)) (.assign "cc" (.bin .add (.var "cc") (.lit 1)))

/-- Count from zero to `cn`, writing `val` every round. -/
def repLoop (val : ℕ) : Com :=
  .seq (.assign "cc" (.lit 0)) (.while (.lt (.var "cc") (.var "cn")) (repBody val))

/-- Write `val` as many times as `e` says. -/
def emitRep (val : ℕ) (e : Expr) : Com := .seq (.assign "cn" e) (repLoop val)

/-- The invariant of the loop: how many have been written, and nothing else has moved. -/
structure RInv (val N : ℕ) (σ0 σ : Env) : Prop where
  out : σ.out = σ0.out ++ List.replicate (σ.vars "cc") val
  cc : σ.vars "cc" ≤ N
  cn : σ.vars "cn" = N
  arrs : σ.arrs = σ0.arrs
  inp : σ.inp = σ0.inp
  fr : ∀ y, y ≠ "cc" → y ≠ "cn" → σ.vars y = σ0.vars y

theorem repBody_spec (val N : ℕ) (σ0 : Env) (hval : val < B) (hN : N + 1 < B) :
    Spec B (fun σ => RInv val N σ0 σ ∧ σ.vars "cc" < N) (repBody val)
      (fun σ σ' => RInv val N σ0 σ' ∧ σ'.vars "cc" = σ.vars "cc" + 1) 6 := by
  rintro σ ⟨⟨hout, hcc, hcn, harr, hinp, hfr⟩, hlt⟩
  unfold repBody
  run_vcg
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [Env.setVar, if_true]
    rw [hout, List.append_assoc, List.replicate_succ' (n := σ.vars "cc") (a := val)]
  · simp only [Env.setVar, if_true]; omega
  · simpa [Env.setVar] using hcn
  · simpa [Env.setVar] using harr
  · simpa [Env.setVar] using hinp
  · intro y a b
    simp only [Env.setVar, if_neg a]
    exact hfr y a b
  · simp [Env.setVar]

theorem repLoop_run (val N : ℕ) (σ : Env) (hval : val < B) (hN : N + 1 < B)
    (hcn : σ.vars "cn" = N) :
    ∃ σ', Run B (repLoop val) σ σ' ((6 + 4) * N + 6) ∧ σ'.out = σ.out ++ List.replicate N val ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.vars "cn" = N ∧
      ∀ y, y ≠ "cc" → y ≠ "cn" → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hcc⟩ := (Spec.forRangeZero (B := B) (c := repBody val) "cc" "cn"
    (RInv val N σ) N 6 (by omega) (fun _ h => h.cc) (fun _ h => h.cn)
    (repBody_spec val N σ hval hN)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], by simpa [Env.setVar] using hcn,
      by simp [Env.setVar], by simp [Env.setVar], fun y a b => by simp [Env.setVar, a]⟩
  refine ⟨σ', r, ?_, hI.arrs, hI.inp, hI.cn, hI.fr⟩
  rw [hI.out, hcc]

/-- **Writing a run of equal numbers.** -/
theorem emitRep_run (val : ℕ) (e : Expr) (N : ℕ) (σ : Env) (hval : val < B) (hN : N + 1 < B)
    (he : e.evalB B σ = some N) :
    ∃ σ', Run B (emitRep val e) σ σ' ((1 + e.size) + ((6 + 4) * N + 6)) ∧
      σ'.out = σ.out ++ List.replicate N val ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
      ∀ y, y ≠ "cc" → y ≠ "cn" → σ'.vars y = σ.vars y := by
  have r1 : Run B (.assign "cn" e) σ (σ.setVar "cn" N) (1 + e.size) := Run.assign he
  obtain ⟨σ', r2, ho, ha, hi, -, hf⟩ := repLoop_run val N (σ.setVar "cn" N) hval hN
    (by simp [Env.setVar])
  refine ⟨σ', r1.seq r2, ?_, ?_, ?_, fun y a b => ?_⟩
  · simpa [Env.setVar] using ho
  · simpa [Env.setVar] using ha
  · simpa [Env.setVar] using hi
  · rw [hf y a b]; simp [Env.setVar, b]

/-! ### The six runs of a row -/

/-- The row of the table: zeros, the one, zeros, then the runs of the rejection columns, the
lengths held by `a1` to `a5`. -/
def emit6 : Com :=
  .seq (emitRep 0 (.var "a1")) (.seq (.write (.lit 1)) (.seq (emitRep 0 (.var "a2"))
    (.seq (emitRep 0 (.var "a3")) (.seq (emitRep 1 (.var "a4")) (emitRep 0 (.var "a5"))))))

/-- What the runs of a row leave behind. -/
def Frm (σ σ' : Env) : Prop :=
  σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ ∀ y, y ≠ "cc" → y ≠ "cn" → σ'.vars y = σ.vars y

theorem Frm.trans {σ σ' σ'' : Env} (h : Frm σ σ') (h' : Frm σ' σ'') : Frm σ σ'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, fun y a b => (h'.2.2 y a b).trans (h.2.2 y a b)⟩

theorem emitRepV_spec (val : ℕ) (x : String) (v M : ℕ) (hval : val < B) (hM : M + 1 < B)
    (hv : v ≤ M) (hx : x ≠ "cc" ∧ x ≠ "cn") (σ : Env) (hσ : σ.vars x = v) :
    ∃ σ', Run B (emitRep val (.var x)) σ σ' ((1 + 1) + ((6 + 4) * M + 6)) ∧
      σ'.out = σ.out ++ List.replicate v val ∧ Frm σ σ' := by
  obtain ⟨σ', r, ho, ha, hi, hf⟩ := emitRep_run val (.var x) v σ hval (by omega)
    (evalB_var (by omega) |>.trans (by rw [hσ]))
  exact ⟨σ', r.mono (by simp [Expr.size]; omega), ho, ha, hi, hf⟩

theorem emit6_run (v1 v2 v3 v4 v5 M : ℕ) (hM : M + 1 < B) (h1 : v1 ≤ M) (h2 : v2 ≤ M)
    (h3 : v3 ≤ M) (h4 : v4 ≤ M) (h5 : v5 ≤ M) (σ : Env)
    (e1 : σ.vars "a1" = v1) (e2 : σ.vars "a2" = v2) (e3 : σ.vars "a3" = v3)
    (e4 : σ.vars "a4" = v4) (e5 : σ.vars "a5" = v5) :
    ∃ σ', Run B emit6 σ σ' (5 * ((1 + 1) + ((6 + 4) * M + 6)) + 2) ∧
      σ'.out = σ.out ++ (List.replicate v1 0 ++ [1] ++ List.replicate v2 0 ++
        List.replicate v3 0 ++ List.replicate v4 1 ++ List.replicate v5 0) ∧ Frm σ σ' := by
  obtain ⟨σ1, r1, o1, f1⟩ := emitRepV_spec (B := B) 0 "a1" v1 M (by omega) hM h1 (by decide) σ e1
  have hw : Run B (.write (.lit 1)) σ1 { σ1 with out := σ1.out ++ [1] } 2 :=
    (Run.write (evalB_lit (by omega))).mono (by simp [Expr.size])
  set σ2 : Env := { σ1 with out := σ1.out ++ [1] } with hσ2
  have f2 : Frm σ1 σ2 := ⟨rfl, rfl, fun _ _ _ => rfl⟩
  obtain ⟨σ3, r3, o3, f3⟩ := emitRepV_spec (B := B) 0 "a2" v2 M (by omega) hM h2 (by decide) σ2
    (by rw [hσ2]; simp only; rw [f1.2.2 "a2" (by decide) (by decide)]; exact e2)
  obtain ⟨σ4, r4, o4, f4⟩ := emitRepV_spec (B := B) 0 "a3" v3 M (by omega) hM h3 (by decide) σ3
    (by rw [f3.2.2 "a3" (by decide) (by decide), hσ2]; simp only
        rw [f1.2.2 "a3" (by decide) (by decide)]; exact e3)
  obtain ⟨σ5, r5, o5, f5⟩ := emitRepV_spec (B := B) 1 "a4" v4 M (by omega) hM h4 (by decide) σ4
    (by rw [f4.2.2 "a4" (by decide) (by decide), f3.2.2 "a4" (by decide) (by decide), hσ2]
        simp only
        rw [f1.2.2 "a4" (by decide) (by decide)]; exact e4)
  obtain ⟨σ6, r6, o6, f6⟩ := emitRepV_spec (B := B) 0 "a5" v5 M (by omega) hM h5 (by decide) σ5
    (by rw [f5.2.2 "a5" (by decide) (by decide), f4.2.2 "a5" (by decide) (by decide),
          f3.2.2 "a5" (by decide) (by decide), hσ2]
        simp only
        rw [f1.2.2 "a5" (by decide) (by decide)]; exact e5)
  refine ⟨σ6, ((r1.seq (hw.seq (r3.seq (r4.seq (r5.seq r6)))))).mono (by omega), ?_,
    f1.trans (f2.trans (f3.trans (f4.trans (f5.trans f6))))⟩
  rw [o6, o5, o4, o3, hσ2]
  simp only [o1, List.append_assoc]

end Lax117284Proofs.Machine.UEmit
