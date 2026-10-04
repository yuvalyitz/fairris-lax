import Lax117284Proofs.McisHard.Defs
import Lax117284Proofs.Machine.SatAccept
import Lax117284Proofs.McisHard.FormulaPorts

/-! ### `Lax117284Proofs.McisHard.Machine.PredInfra` -/

section
/-!
# Machine Predicates for the Adjacency Bit: Shared Definitions (WP6)

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

end

/-! ### `Lax117284Proofs.McisHard.Machine.PredBase` -/

section
/-!
# Clause-Level Commands for the Adjacency Bit (WP6)

`compCom` (the literals of two positions are complementary), `cidCom` (the clause number of a position),
`clauseCom` (the size of the clause of a position and the position `mateN`).
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Bit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284Proofs.Machine.SatRank Lax117284Proofs.Machine.SatOps Lax117284Proofs.Machine.T9Ops

variable {B : ℕ}

/-! ### The comparison of the literals of two positions -/

def compCom : Com :=
  .seq (.assign "bv1" (.get "TK" (add (.lit 3) (mul (.lit 2) (V "ba")))))
  (.seq (.assign "bs1" (.get "TK" (add (.lit 4) (mul (.lit 2) (V "ba")))))
  (.seq (.assign "bv2" (.get "TK" (add (.lit 3) (mul (.lit 2) (V "bb")))))
  (.seq (.assign "bs2" (.get "TK" (add (.lit 4) (mul (.lit 2) (V "bb")))))
  (.ite (.eq (V "bv1") (V "bv2"))
    (.ite (.eq (V "bs1") (V "bs2")) (.assign "bc" (.lit 0)) (.assign "bc" (.lit 1)))
    (.assign "bc" (.lit 0))))))

@[simp] def AComp : List String := ["bv1", "bs1", "bv2", "bs2", "bc"]

set_option maxHeartbeats 1600000 in
theorem compCom_spec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns ∧ σ.vars "bb" < SlotsN ns) compCom
      (fun σ σ' => σ'.vars "bc" = ind (compN ns (σ.vars "ba") (σ.vars "bb"))) 60 := by
  have hE1 := hP.hE1
  have hE2 := hP.hE2
  have hlen := hP.hlen
  have hB := hP.hB
  run_vcg
  vcg_norm
  vcg_fin
  all_goals first
    | (refine (ind_true ?_).symm; simp_all [compN, litV, litS, List.getD_eq_getElem?_getD]; done)
    | (refine (ind_false ?_).symm; simp_all [compN, litV, litS, List.getD_eq_getElem?_getD]; done)

theorem compCom_fspec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns ∧ σ.vars "bb" < SlotsN ns) compCom
      (fun σ σ' => (σ'.vars "bc" = ind (compN ns (σ.vars "ba") (σ.vars "bb")) ∧ σ'.vars "bc" ≤ 1) ∧
        Fr AComp σ σ' ∧ Ctx[ns, σ']) 60 :=
  (frSpecC (compCom_spec ns hP) AComp (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).post fun _ σ' _ ⟨hq, hf⟩ => ⟨⟨hq, hq ▸ ind_le _⟩, hf⟩

/-! ### The clause number of a position -/

/-- Read the position in `x`, write its clause number to `z`. -/
def cidCom (x z : String) : Com :=
  .ite (.lt (V x) (V "A2")) (.assign z (div (V x) (.lit 2)))
    (.assign z (add (div (V "A2") (.lit 2)) (div (sub (V x) (V "A2")) (.lit 3))))

theorem cidCom_spec (ns : List ℕ) (hP : Pars B ns) (x z : String) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars x < SlotsN ns) (cidCom x z)
      (fun σ σ' => σ'.vars z = clId ns (σ.vars x)) 20 := by
  have hB := hP.hB
  run_vcg
  vcg_norm
  vcg_fin
  all_goals (simp only [clId, List.getD_eq_getElem?_getD]; split_ifs <;> omega)

theorem cidCom_fspec (ns : List ℕ) (hP : Pars B ns) (x z : String) (hzN : z ≠ "N")
    (hzA : z ≠ "A2") :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars x < SlotsN ns) (cidCom x z)
      (fun σ σ' => σ'.vars z = clId ns (σ.vars x) ∧ Fr [z] σ σ' ∧ Ctx[ns, σ']) 20 :=
  frSpecC (cidCom_spec ns hP x z) [z] (by simp [cidCom, Com.wvars]) (by simp [cidCom, Com.warrs])
    (by simp [cidCom, Com.reads]) (by simp [cidCom, Com.NoWrite]) (by simp [Ne.symm hzN])
    (by simp [Ne.symm hzA])

/-! ### The size of the clause of a position and its mate -/

/-- Read the position in `ba` and the port in `bj`: `bs` is the size of the clause of the position, `bm` is
`mateN ns ba bj`. -/
def clauseCom : Com :=
  .ite (.lt (V "ba") (V "A2"))
    (.seq (.assign "bs" (.lit 2))
      (.seq (.assign "bq1" (div (V "ba") (.lit 2)))
      (.seq (.assign "bx" (sub (V "ba") (mul (V "bq1") (.lit 2))))
      (.seq (.assign "by" (add (add (V "bx") (V "bj")) (.lit 1)))
      (.seq (.assign "bz" (div (V "by") (.lit 2)))
      (.seq (.assign "bz" (sub (V "by") (mul (V "bz") (.lit 2))))
        (.assign "bm" (add (sub (V "ba") (V "bx")) (V "bz")))))))))
    (.seq (.assign "bs" (.lit 3))
      (.seq (.assign "bd0" (sub (V "ba") (V "A2")))
      (.seq (.assign "bq1" (div (V "bd0") (.lit 3)))
      (.seq (.assign "bx" (sub (V "bd0") (mul (V "bq1") (.lit 3))))
      (.seq (.assign "by" (add (add (V "bx") (V "bj")) (.lit 1)))
      (.seq (.assign "bz" (div (V "by") (.lit 3)))
      (.seq (.assign "bz" (sub (V "by") (mul (V "bz") (.lit 3))))
        (.assign "bm" (add (sub (V "ba") (V "bx")) (V "bz"))))))))))

@[simp] def AClause : List String := ["bs", "bq1", "bx", "by", "bz", "bd0", "bm"]

theorem clauseCom_spec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns ∧ σ.vars "bj" < 8) clauseCom
      (fun σ σ' => σ'.vars "bs" = clSz ns (σ.vars "ba") ∧
        σ'.vars "bm" = mateN ns (σ.vars "ba") (σ.vars "bj")) 80 := by
  have hB := hP.hB
  run_vcg
  vcg_norm
  vcg_fin
  all_goals (simp only [clSz, mateN, clIx, List.getD_eq_getElem?_getD]; split_ifs <;> omega)

/-- The mate of a position is a position. -/
theorem mateN_lt (ns : List ℕ) {o : ℕ} (ho : o < SlotsN ns) (j : ℕ) : mateN ns o j < SlotsN ns := by
  unfold mateN clIx clSz SlotsN at *
  split_ifs <;> omega

theorem clSz_le (ns : List ℕ) (o : ℕ) : clSz ns o ≤ 3 := by unfold clSz; split <;> omega

theorem clauseCom_fspec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns ∧ σ.vars "bj" < 8) clauseCom
      (fun σ σ' => (σ'.vars "bs" = clSz ns (σ.vars "ba") ∧
        σ'.vars "bm" = mateN ns (σ.vars "ba") (σ.vars "bj") ∧ σ'.vars "bs" ≤ 3 ∧
        σ'.vars "bm" < SlotsN ns) ∧ Fr AClause σ σ' ∧ Ctx[ns, σ']) 80 :=
  (frSpecC (clauseCom_spec ns hP) AClause (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).post fun σ σ' hP' ⟨hq, hf⟩ =>
      ⟨⟨hq.1, hq.2, hq.1 ▸ clSz_le _ _, hq.2 ▸ mateN_lt ns hP'.2.1 _⟩, hf⟩

end Lax117284Proofs.McisHard.Bit

end

/-! ### `Lax117284Proofs.McisHard.Machine.PredUnm` -/

section
/-!
# The Predicate `unmatchedN` on the Machine (WP6)

`coCntCom`: the number of positions carrying the complementary literal of a position (a wrapper of
`SatRank.rankLoop_spec` with the sign `1 - sign`), and `unmatchedCom`.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Bit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284Proofs.Machine.SatRank Lax117284Proofs.Machine.SatOps Lax117284Proofs.Machine.T9Ops

variable {B : ℕ}

/-! ### The counting loop as a `Spec` -/

theorem rankLoopS (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => σ.arrs "TK" = ns ∧ σ.vars "o" ≤ SlotsN ns ∧ σ.vars "vo" + 8 < B ∧
        σ.vars "so" + 8 < B ∧ σ.vars "cnt" = 0) rankLoop
      (fun σ σ' => σ'.vars "cnt" = (List.range (σ.vars "o")).countP (rpred ns (σ.vars "vo") (σ.vars "so")) ∧
        Fr AR σ σ') (64 * SlotsN ns + 6) := by
  rintro σ ⟨hA, ho, hv, hs, hc⟩
  have hB := hP.hB
  have hlen := hP.hlen
  obtain ⟨σ', r, c, a, o, f⟩ := rankLoop_spec (B := B) ns (σ.vars "vo") (σ.vars "so") (σ.vars "o") σ
    (fun k hk => by have := hP.hE (3 + 2 * k); omega) (fun k hk => by have := hP.hE (4 + 2 * k); omega)
    (by omega) (by omega) (by omega) (by omega) hA rfl rfl rfl hc
  refine ⟨σ', r.mono ?_, c, a, o, r.frame_inp (by decide), f⟩
  have := Nat.mul_le_mul_left 64 ho
  omega

/-! ### The number of complementary positions -/

theorem coCountN_eq (ns : List ℕ) (hP : Pars B ns) {o : ℕ} (ho : o < SlotsN ns) :
    coCountN ns o = (List.range (SlotsN ns)).countP
      (rpred ns (ns.getD (3 + 2 * o) 0) (1 - ns.getD (4 + 2 * o) 0)) := by
  unfold coCountN
  rw [List.countP_eq_length_filter]
  refine congrArg List.length (List.filter_congr fun x hx => ?_)
  have hx' := List.mem_range.mp hx
  have h1 := hP.hsg x hx'
  have h2 := hP.hsg o ho
  simp only [rpred, litV, litS]
  apply decide_eq_decide.mpr
  omega

/-- Read the position in `ba`; `cnt` is the number of positions with the complementary literal. -/
def coCntCom : Com :=
  .seq (.assign "o" (V "N"))
  (.seq (.assign "vo" (.get "TK" (add (.lit 3) (mul (.lit 2) (V "ba")))))
  (.seq (.assign "so" (sub (.lit 1) (.get "TK" (add (.lit 4) (mul (.lit 2) (V "ba"))))))
  (.seq (.assign "cnt" (.lit 0)) rankLoop)))

@[simp] def ACo : List String := ["o", "vo", "so", "cnt", "j", "vj", "sj"]

set_option maxHeartbeats 1600000 in
theorem coCntCom_spec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns) coCntCom
      (fun σ σ' => σ'.vars "cnt" = coCountN ns (σ.vars "ba") ∧ Fr ACo σ σ')
      (64 * SlotsN ns + 60) := by
  have hE1 := hP.hE1
  have hE8 := hP.hE8
  have hlen := hP.hlen
  have hB := hP.hB
  run_vcg [rankLoopS ns hP]
  vcg_norm
  vcg_fin
  have hba : σ.vars "ba" < SlotsN ns := by simp only [SlotsN, List.getD_eq_getElem?_getD]; omega
  rw [coCountN_eq ns hP hba]
  simp [List.getD_eq_getElem?_getD, SlotsN]

theorem coCountN_le (ns : List ℕ) (o : ℕ) : coCountN ns o ≤ SlotsN ns := by
  unfold coCountN
  exact (List.length_filter_le _ _).trans (by simp)

theorem coCntCom_fspec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns) coCntCom
      (fun σ σ' => (σ'.vars "cnt" = coCountN ns (σ.vars "ba") ∧ σ'.vars "cnt" ≤ SlotsN ns) ∧
        Fr ACo σ σ' ∧ Ctx[ns, σ']) (64 * SlotsN ns + 60) :=
  (coCntCom_spec ns hP).post fun σ σ' hpre ⟨hq, hf⟩ =>
    ⟨⟨hq, hq ▸ coCountN_le ns _⟩, hf, ctx_of_eq hpre.1 hf.1 (hf.2.2.2 "N" (by decide))
      (hf.2.2.2 "A2" (by decide))⟩

/-! ### `unmatchedN` -/

/-- Read the position in `ba` and the port in `bj`; `bu` is `unmatchedN ns ba bj`. -/
def unmatchedCom : Com :=
  .ite (.eq (V "bj") (.lit 4)) (.assign "bu" (.lit 1))
    (.ite (.lt (V "bj") (.lit 2))
      (.seq clauseCom
        (.ite (.lt (V "bs") (add (V "bj") (.lit 2))) (.assign "bu" (.lit 1))
          (.seq (.assign "bb" (V "bm")) (.seq compCom (.assign "bu" (V "bc"))))))
      (.ite (.lt (V "bj") (.lit 4))
        (.seq coCntCom
          (.ite (.lt (V "cnt") (sub (V "bj") (.lit 1))) (.assign "bu" (.lit 1)) (.assign "bu" (.lit 0))))
        (.assign "bu" (.lit 0))))

@[simp] def AUnm : List String := AClause ++ AComp ++ ACo ++ ["bu", "bb"]

theorem unmatchedCom_spec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns ∧ σ.vars "bj" < 8) unmatchedCom
      (fun σ σ' => σ'.vars "bu" = ind (unmatchedN ns (σ.vars "ba") (σ.vars "bj")))
      (64 * SlotsN ns + 200) := by
  have hE1 := hP.hE1
  have hB := hP.hB
  run_vcg [clauseCom_fspec ns hP, compCom_fspec ns hP, coCntCom_fspec ns hP]
  vcg_norm
  vcg_fin
  all_goals first
    | (refine (ind_true ?_).symm; unfold unmatchedN
       first
         | exact Or.inl (by omega)
         | exact Or.inr (Or.inl ⟨by omega, Or.inl (by omega)⟩)
         | exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))
    | (refine (ind_false ?_).symm; unfold unmatchedN
       rintro (h | ⟨h, -⟩ | ⟨h1, h2, h3⟩) <;> omega)
    | (apply ind_congr
       unfold unmatchedN
       constructor
       · intro h; exact Or.inr (Or.inl ⟨by omega, Or.inr h⟩)
       · rintro (h | ⟨-, h | h⟩ | ⟨h, -⟩) <;> first | omega | exact h)

theorem unmatchedCom_fspec (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "ba" < SlotsN ns ∧ σ.vars "bj" < 8) unmatchedCom
      (fun σ σ' => (σ'.vars "bu" = ind (unmatchedN ns (σ.vars "ba") (σ.vars "bj")) ∧
        σ'.vars "bu" ≤ 1) ∧ Fr AUnm σ σ' ∧ Ctx[ns, σ']) (64 * SlotsN ns + 200) :=
  (frSpecC (unmatchedCom_spec ns hP) AUnm (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).post fun _ σ' _ ⟨hq, hf⟩ => ⟨⟨hq, hq ▸ ind_le _⟩, hf⟩

end Lax117284Proofs.McisHard.Bit

end

/-! ### `Lax117284Proofs.McisHard.Machine.PredMath` -/

section
/-!
# The Mathematics Behind the Adjacency Bit (WP6)

`PEP`, `portAdjM`, `adjM`: `portAdjN (RN ns)` with the two quantified pieces replaced by the predicates
the machine computes; `adjM_iff_adjF` shows they agree with `adjF`.  The only facts about `RN` that are used are
`pe_iff` (proved here) and `unmatched_iff` (the WP3 statement in `Defs`).
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Bit

open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem

/-- The positions are different and in one clause or complementary. -/
def PEP (ns : List ℕ) (o o' : ℕ) : Prop := o ≠ o' ∧ (clId ns o = clId ns o' ∨ compN ns o o')

/-- `portAdjN (RN ns)` with `∃ j j', RN` replaced by `PEP` and `¬ ∃ o' j', RN` by `unmatchedN`, written as the case
tree the machine walks. -/
def treeP (ns : List ℕ) (u v : ℕ) : Prop :=
  if u % 36 = 0 then
    (if v % 36 = 0 then PEP ns (u / 36) (v / 36)
     else u / 36 = v / 36 ∧ (v % 36 - 1) % 7 = 0 ∧ unmatchedN ns (u / 36) ((v % 36 - 1) / 7))
  else
    (if v % 36 = 0 then
       u / 36 = v / 36 ∧ (u % 36 - 1) % 7 = 0 ∧ unmatchedN ns (v / 36) ((u % 36 - 1) / 7)
     else
       (u / 36 = v / 36 ∧ (u % 36 - 1) / 7 = (v % 36 - 1) / 7 ∧
          gadAdj ((u % 36 - 1) % 7) ((v % 36 - 1) % 7)) ∨
       ((u % 36 - 1) % 7 = 0 ∧ (v % 36 - 1) % 7 = 0 ∧
          RN ns (u / 36) ((u % 36 - 1) / 7) (v / 36) ((v % 36 - 1) / 7)))

/-- The adjacency of `H`, in the shape the machine computes it. -/
def adjM (ns : List ℕ) (w w' : ℕ) : Prop :=
  w / nOf ns ≠ w' / nOf ns ∧
    (w % nOf ns = w' % nOf ns ∨ (SlotsN ns ≠ 0 ∧ treeP ns (w % nOf ns) (w' % nOf ns)))

/-! ### `PEP` is "some ports are matched" -/

theorem rank_le_one (ns : List ℕ) (hc : CondN ns) {o : ℕ} (ho : o < SlotsN ns) : rankN ns o ≤ 1 :=
  (hc.2 o ho).2


theorem pe_iff (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) {o o' : ℕ} (ho : o < SlotsN ns)
    (ho' : o' < SlotsN ns) : PEP ns o o' ↔ ∃ j j', RN ns o j o' j' := by
  constructor
  · rintro ⟨hne, hcl | hcomp⟩
    · by_cases hcomp : compN ns o o'
      · refine ⟨rankN ns o' + 2, rankN ns o + 2, ho, ho', Or.inr ?_⟩
        have h1 := rank_le_one ns hc ho
        have h2 := rank_le_one ns hc ho'
        exact ⟨by omega, by omega, by omega, by omega, hcomp, by omega, by omega⟩
      · -- the same clause, not complementary: a mate port
        unfold clId at hcl
        unfold SlotsN at ho ho'
        by_cases h1 : o < 2 * ns.getD 1 0 <;> by_cases h2 : o' < 2 * ns.getD 1 0
        · rw [if_pos h1, if_pos h2] at hcl
          refine ⟨0, 0, by unfold SlotsN; omega, by unfold SlotsN; omega, Or.inl ⟨by omega, by omega, ?_, ?_, hcomp⟩⟩
          · unfold clSz; rw [if_pos h1]
          · unfold mateN clIx clSz; simp only [if_pos h1]; omega
        · rw [if_pos h1, if_neg h2] at hcl; omega
        · rw [if_neg h1, if_pos h2] at hcl; omega
        · rw [if_neg h1, if_neg h2] at hcl
          by_cases hj : (o - 2 * ns.getD 1 0) % 3 + 1 = (o' - 2 * ns.getD 1 0) % 3 ∨
              ((o - 2 * ns.getD 1 0) % 3 = 2 ∧ (o' - 2 * ns.getD 1 0) % 3 = 0)
          · refine ⟨0, 1, by unfold SlotsN; omega, by unfold SlotsN; omega,
              Or.inl ⟨by omega, by omega, ?_, ?_, hcomp⟩⟩
            · unfold clSz; rw [if_neg h1]
            · unfold mateN clIx clSz; simp only [if_neg h1]; omega
          · refine ⟨1, 0, by unfold SlotsN; omega, by unfold SlotsN; omega,
              Or.inl ⟨by omega, by omega, ?_, ?_, hcomp⟩⟩
            · unfold clSz; rw [if_neg h1]
            · unfold mateN clIx clSz; simp only [if_neg h1]; omega
    · refine ⟨rankN ns o' + 2, rankN ns o + 2, ho, ho', Or.inr ?_⟩
      have h1 := rank_le_one ns hc ho
      have h2 := rank_le_one ns hc ho'
      exact ⟨by omega, by omega, by omega, by omega, hcomp, by omega, by omega⟩
  · rintro ⟨j, j', -, -, ⟨hj, hj', hsz, hmate, hncomp⟩ | ⟨-, -, -, -, hcomp, -, -⟩⟩
    · refine ⟨?_, Or.inl ?_⟩
      · subst hmate
        unfold mateN clIx clSz at *
        split_ifs at * <;> omega
      · subst hmate
        unfold mateN clIx clSz clId at *
        unfold SlotsN at ho
        split_ifs at * <;> omega
    · refine ⟨?_, Or.inr hcomp⟩
      rintro rfl
      exact hcomp.2 rfl

/-! ### `treeP` and `adjM` -/

theorem treeP_iff (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) {u v : ℕ}
    (hu : u < 36 * SlotsN ns) (hv : v < 36 * SlotsN ns) :
    treeP ns u v ↔ portAdjN (RN ns) u v := by
  have hoN : u / 36 < SlotsN ns := by omega
  have hoN' : v / 36 < SlotsN ns := by omega
  unfold treeP portAdjN
  by_cases hu0 : u % 36 = 0 <;> by_cases hv0 : v % 36 = 0
  · rw [if_pos hu0, if_pos hv0]
    constructor
    · intro h; exact Or.inl ⟨hu0, hv0, (pe_iff ns hs hc hoN hoN').1 h⟩
    · rintro (⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩)
      · exact (pe_iff ns hs hc hoN hoN').2 h
      · exact absurd hv0 h
      · exact absurd hu0 h
      · exact absurd hu0 h
  · rw [if_pos hu0, if_neg hv0]
    have hj : (v % 36 - 1) / 7 < 5 := by omega
    constructor
    · rintro ⟨a, b, c⟩; exact Or.inr (Or.inl ⟨hu0, hv0, a, b, (Proved.unmatched_iff ns hs hc hoN hj).2 c⟩)
    · rintro (⟨-, h, -⟩ | ⟨-, -, a, b, c⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩)
      · exact absurd h hv0
      · exact ⟨a, b, (Proved.unmatched_iff ns hs hc hoN hj).1 c⟩
      · exact absurd hu0 h
      · exact absurd hu0 h
  · rw [if_neg hu0, if_pos hv0]
    have hj : (u % 36 - 1) / 7 < 5 := by omega
    constructor
    · rintro ⟨a, b, c⟩; exact Or.inr (Or.inr (Or.inl ⟨hu0, hv0, a, b, (Proved.unmatched_iff ns hs hc hoN' hj).2 c⟩))
    · rintro (⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨-, -, a, b, c⟩ | ⟨-, h, -⟩)
      · exact absurd h hu0
      · exact absurd h hu0
      · exact ⟨a, b, (Proved.unmatched_iff ns hs hc hoN' hj).1 c⟩
      · exact absurd hv0 h
  · rw [if_neg hu0, if_neg hv0]
    constructor
    · intro h; exact Or.inr (Or.inr (Or.inr ⟨hu0, hv0, h⟩))
    · rintro (⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩)
      · exact absurd h hu0
      · exact absurd h hu0
      · exact absurd h hv0
      · exact h

theorem adjM_iff_adjF (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) (w w' : ℕ) :
    adjM ns w w' ↔ adjF ns w w' := by
  unfold adjM adjF
  refine and_congr_right fun _ => or_congr_right (and_congr_right fun h0 => ?_)
  have hn : nOf ns = SlotsN ns * 36 := by unfold nOf; rw [if_neg h0]
  have hpos : 0 < nOf ns := by rw [hn]; omega
  have h1 := Nat.mod_lt w hpos
  have h2 := Nat.mod_lt w' hpos
  rw [hn] at h1 h2 ⊢
  exact treeP_iff ns hs hc (by omega) (by omega)

end Lax117284Proofs.McisHard.Bit

end

/-! ### `Lax117284Proofs.McisHard.Machine.PredLink` -/

section
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

end

/-! ### `Lax117284Proofs.McisHard.Machine.PredMain` -/

section
/-!
# The Adjacency Bit of `H`: the Case Tree and the Whole Command (WP6)

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

end

/-! ### `Lax117284Proofs.McisHard.Machine.PredFinal` -/

section
/-!
# The Adjacency Bit of `H` on the Machine: the Final Theorem (WP6)

`bitCom_run`: given the state `SatAccept.prepSat` leaves (the stream `ns` in `TK`, `N`, `A2`), the command `bitCom`
writes `adjF ns w w2` to `bt`; `bitCom_run_M` is the same about `adjM`.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Bit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem

/-- The cost of one bit, on `N` positions. -/
def Kbit (N : ℕ) : ℕ := 128 * N + 1500

/-- The scratch scalars of `bitCom`: `bt`, the scalars of `SatRank.rankCom` (`o vo so j vj sj cnt`) and names
starting with `b`. -/
@[simp] def AB : List String := ["bTi", "bTj", "bTu", "bTv", "bTn"] ++ ATree

set_option maxRecDepth 100000 in
theorem bitCom_fspec {B : ℕ} (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "w" < B ∧ σ.vars "w2" < B) bitCom
      (fun σ σ' => (σ'.vars "bt" = ind (adjM ns (σ.vars "w") (σ.vars "w2")) ∧ σ'.vars "bt" ≤ 1) ∧
        Fr AB σ σ' ∧ Ctx[ns, σ']) (Kbit (SlotsN ns)) :=
  (frSpecC (bitCom_spec ns hP) AB (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).post fun _ σ' _ ⟨hq, hf⟩ => ⟨⟨hq, hq ▸ ind_le _⟩, hf⟩

/-- The standing assumptions of the commands, from the hypotheses of the reduction. -/
theorem pars_of (B : ℕ) (ns : List ℕ) (hs : ShapeF ns) (hB : 60 * (SlotsN ns + 4) < B)
    (hE : ∀ k < 3 + 2 * SlotsN ns, ns.getD k 0 + 8 < B) : Pars B ns :=
  ⟨hs.2.1, fun k => by
    by_cases hk : k < 3 + 2 * SlotsN ns
    · exact hE k hk
    · rw [List.getD_eq_default _ _ (by have := hs.2.1; omega)]; omega,
    hB, fun o ho => hs.2.2 o ho⟩

/-- **The adjacency bit, in the shape the machine computes it.** -/
theorem bitCom_run_M (B : ℕ) (ns : List ℕ) (hs : ShapeF ns) (hB : 60 * (SlotsN ns + 4) < B)
    (hE : ∀ k < 3 + 2 * SlotsN ns, ns.getD k 0 + 8 < B)
    (σ : Env) (hA : σ.arrs "TK" = ns) (hN : σ.vars "N" = SlotsN ns)
    (hA2 : σ.vars "A2" = 2 * ns.getD 1 0) (w w2 : ℕ) (hw : σ.vars "w" = w) (hw2 : σ.vars "w2" = w2)
    (hwB : w < B) (hw2B : w2 < B) :
    ∃ σ', Run B bitCom σ σ' (Kbit (SlotsN ns)) ∧ σ'.vars "bt" = ind (adjM ns w w2) ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
      ∀ y, y ∉ AB → σ'.vars y = σ.vars y := by
  obtain ⟨σ', hr, ⟨hq, -⟩, ⟨harr, hout, hinp, hfr⟩, -⟩ :=
    bitCom_fspec ns (pars_of B ns hs hB hE) σ ⟨⟨hA, hN, hA2⟩, hw ▸ hwB, hw2 ▸ hw2B⟩
  refine ⟨σ', hr, ?_, harr, hout, hinp, hfr⟩
  rw [hq, hw, hw2]

open Classical in
/-- **The adjacency bit.**  Started with the stream `ns` in `TK`, `N`, `A2` as `prepSat` leaves them, and
two vertex numbers `w`, `w2` (below the word bound) in the scalars `w`, `w2`, the command leaves the bit
`adjF ns w w2` in `bt`. -/
theorem bitCom_run (B : ℕ) (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns)
    (hB : 60 * (SlotsN ns + 4) < B) (hE : ∀ k < 3 + 2 * SlotsN ns, ns.getD k 0 + 8 < B)
    (σ : Env) (hA : σ.arrs "TK" = ns) (hN : σ.vars "N" = SlotsN ns)
    (hA2 : σ.vars "A2" = 2 * ns.getD 1 0) (w w2 : ℕ) (hw : σ.vars "w" = w) (hw2 : σ.vars "w2" = w2)
    (hwB : w < B) (hw2B : w2 < B) :
    ∃ σ', Run B bitCom σ σ' (Kbit (SlotsN ns)) ∧
      σ'.vars "bt" = (if decide (adjF ns w w2) then 1 else 0) ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
      ∀ y, y ∉ AB → σ'.vars y = σ.vars y := by
  obtain ⟨σ', hr, hbt, h1, h2, h3, h4⟩ := bitCom_run_M B ns hs hB hE σ hA hN hA2 w w2 hw hw2 hwB hw2B
  refine ⟨σ', hr, ?_, h1, h2, h3, h4⟩
  rw [hbt, ind_congr (adjM_iff_adjF ns hs hc w w2)]
  unfold ind
  simp

end Lax117284Proofs.McisHard.Bit

end
