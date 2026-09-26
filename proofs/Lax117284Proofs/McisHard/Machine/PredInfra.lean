import Lax117284Proofs.McisHard.Defs
import Lax117284Proofs.Machine.SatAccept

/-!
# Machine predicates for the adjacency bit: shared definitions (WP6)

The context every predicate command runs in: the token array `TK` holds the stream `ns`, the scalars
`N` and `A2` hold the number of positions and twice the number of two-clauses (as left by
`SatAccept.prepSat`).  Booleans are `0`/`1` scalars, `ind P`.

-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Bit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284Proofs.Machine.SatRank Lax117284Proofs.Machine.SatOps Lax117284Proofs.Machine.T9Ops

abbrev V (s : String) : Expr := .var s
abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev div (e f : Expr) : Expr := .bin .div e f
abbrev add (e f : Expr) : Expr := .bin .add e f

open Classical in
/-- The `0`/`1` value of a proposition. -/
noncomputable def ind (P : Prop) : ℕ := if P then 1 else 0

lemma ind_true {P : Prop} (h : P) : ind P = 1 := by unfold ind; simp [h]
lemma ind_false {P : Prop} (h : ¬ P) : ind P = 0 := by unfold ind; simp [h]
lemma ind_le (P : Prop) : ind P ≤ 1 := by unfold ind; split <;> omega
lemma ind_congr {P Q : Prop} (h : P ↔ Q) : ind P = ind Q := by
  rw [propext h]
lemma ind_eq_one {P : Prop} : ind P = 1 ↔ P := by
  unfold ind; split <;> simp_all
lemma ind_eq_zero {P : Prop} : ind P = 0 ↔ ¬ P := by
  unfold ind; split <;> simp_all

variable {B : ℕ}

attribute [simp] Lax117284Proofs.Machine.SatRank.AR Lax117284Proofs.Machine.SatRank.ARC

open Lean Elab Tactic Meta in
/-- Drop the `Run` hypotheses `run_vcg` leaves behind. -/
elab "clear_runs" : tactic => withMainContext do
  let lctx ← getLCtx
  for d in lctx do
    if !d.isImplementationDetail && d.type.getAppFn.isConstOf ``Run then
      try liftMetaTactic fun g => do return [← g.clear d.fvarId] catch _ => pure ()

/-- The standing assumptions on the stream and the bound. -/
structure Pars (B : ℕ) (ns : List ℕ) : Prop where
  hlen : ns.length = 3 + 2 * SlotsN ns
  hE : ∀ k, ns.getD k 0 + 8 < B
  hB : 60 * (SlotsN ns + 4) < B
  hsg : ∀ o < SlotsN ns, ns.getD (4 + 2 * o) 0 ≤ 1

lemma Pars.hE1 {ns : List ℕ} (hP : Pars B ns) (k : ℕ) : ns[k]?.getD 0 < B := by
  have := hP.hE k; simp only [List.getD_eq_getElem?_getD] at this; omega

lemma Pars.hE8 {ns : List ℕ} (hP : Pars B ns) (k : ℕ) : ns[k]?.getD 0 + 8 < B := by
  have := hP.hE k; simpa only [List.getD_eq_getElem?_getD] using this

lemma Pars.hE2 {ns : List ℕ} (hP : Pars B ns) (k : ℕ) (hk : k < ns.length) : ns[k] < B := by
  have := hP.hE1 k; simpa [List.getElem?_eq_getElem hk] using this

/-- What the commands read of the state: the token array and the two scalars (a plain conjunction, so
that `run_vcg` and `simp_all` take it apart). -/
notation "Ctx[" ns ", " σ "]" =>
  (Env.arrs σ "TK" = ns ∧ Env.vars σ "N" = SlotsN ns ∧ Env.vars σ "A2" = 2 * List.getD ns 1 0)

theorem ctx_of_eq {ns : List ℕ} {σ σ' : Env} (h : Ctx[ns, σ]) (ha : σ'.arrs = σ.arrs)
    (hN : σ'.vars "N" = σ.vars "N") (hA2 : σ'.vars "A2" = σ.vars "A2") : Ctx[ns, σ'] :=
  ⟨by rw [ha]; exact h.1, by rw [hN]; exact h.2.1, by rw [hA2]; exact h.2.2⟩

/-- Nothing changed but the scalars in `L`. -/
abbrev Fr (L : List String) (σ σ' : Env) : Prop :=
  σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧ ∀ y, y ∉ L → σ'.vars y = σ.vars y

/-- A specification framed by an explicit list of scalars. -/
theorem frSpec {P : Env → Prop} {c : Com} {Q : Env → Env → Prop} {K : ℕ}
    (h : Spec B P c Q K) (L : List String) (hw : ∀ y ∈ c.wvars, y ∈ L) (ha : c.warrs = [])
    (hr : ¬ c.reads) (hn : c.NoWrite) :
    Spec B P c (fun σ σ' => Q σ σ' ∧ Fr L σ σ') K := by
  refine h.frame.post ?_
  rintro σ σ' - ⟨hq, hv, harr, hinp, hout⟩
  exact ⟨hq, funext fun a => harr a (by simp [ha]), hout hn, hinp hr,
    fun y hy => hv y fun hm => hy (hw y hm)⟩

/-- A specification framed by an explicit list of scalars, which also keeps the context. -/
theorem frSpecC {ns : List ℕ} {R : Env → Prop} {c : Com} {Q : Env → Env → Prop} {K : ℕ}
    (h : Spec B (fun σ => Ctx[ns, σ] ∧ R σ) c Q K) (L : List String) (hw : ∀ y ∈ c.wvars, y ∈ L)
    (ha : c.warrs = []) (hr : ¬ c.reads) (hn : c.NoWrite) (hN : "N" ∉ L) (hA2 : "A2" ∉ L) :
    Spec B (fun σ => Ctx[ns, σ] ∧ R σ) c (fun σ σ' => Q σ σ' ∧ Fr L σ σ' ∧ Ctx[ns, σ']) K := by
  refine (frSpec h L hw ha hr hn).post ?_
  rintro σ σ' ⟨hc, -⟩ ⟨hq, hf⟩
  exact ⟨hq, hf, ctx_of_eq hc hf.1 (hf.2.2.2 "N" hN) (hf.2.2.2 "A2" hA2)⟩

-- The bookkeeping after `run_vcg`: drop the runs, normalise the environments.
macro "vcg_norm" : tactic => `(tactic| (
  all_goals clear_runs
  all_goals try (simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *)))

-- The generic closing steps after `vcg_norm`: `simp_all` rewrites with the context, `omega` finishes bounds.
macro "vcg_fin" : tactic => `(tactic| (
  all_goals try omega
  all_goals (simp_all [Fr, SlotsN, List.getD_eq_getElem?_getD, -getElem?_pos])
  all_goals try omega))

end Lax117284Proofs.McisHard.Bit
