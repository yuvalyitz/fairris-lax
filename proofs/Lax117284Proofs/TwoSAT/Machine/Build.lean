import Lax117284Proofs.TwoSAT.Machine.BuildMath
import Lax808846Proofs.Lib.Csr

/-!
Building the implication graph's CSR representation from the scanned formula, by counting
sort: three passes over the clauses.

* **degrees** — one pass over the clauses, incrementing `deg[src]` for every edge a clause
  contributes;
* **prefix sums** — `off[u + 1] = off[u] + deg[u]`, with `pos[u] = off[u]` the next free
  slot of each row, and the scalar `E` set to `off[N]`, the number of edges;
* **fill** — the same walk as the first pass, writing every edge `(src, dst)` at slot
  `pos[src]` of `tgt` and advancing `pos[src]`.

Each pass over the clauses keeps a running literal pointer `i`, which stands at `start F c`
at the top of the turn for clause `c`; a clause with `cnt[c] = 1` literal reads position `i`
and moves the pointer by one, a clause with two literals reads `i` and `i + 1` and moves it
by two. The unit clause `[a]` contributes the edge `¬a → a`; the clause `[a, b]` the edges
`¬a → b` and `¬b → a`, in that order (`clauseEdges`).

The specification `build_spec` says that afterwards `off`/`tgt` form a CSR structure
(`Lib.Csr`) whose row `u` lists exactly the out-neighbours of `u` in `edges F`.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Build

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax429075.CNF Lax391470Proofs.L2ScanModel Lax117284Proofs.TwoSAT.Machine.Model

/-- Collapse a chain of `setVar`/`setArr` updates: the projections, the string keys decided,
and whatever else is handed over. -/
syntax "env_simp" (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
  Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| env_simp) =>
    `(tactic| simp only [Env.setVar, Env.setArr, String.reduceEq, reduceIte])
  | `(tactic| env_simp [$ts,*]) =>
    `(tactic| simp only [Env.setVar, Env.setArr, String.reduceEq, reduceIte, $ts,*])

/-! ### The program -/

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.add (V s) (.lit 1))

/-- `2 * vr[e] + sg[e]`: the code of the literal at position `e`. -/
abbrev codeAt (e : Expr) : Expr := .add (.mul (.lit 2) (.get "vr" e)) (.get "sg" e)

/-- `2 * vr[e] + (1 - sg[e])`: the code of the negation of the literal at position `e`. -/
abbrev ncodeAt (e : Expr) : Expr := .add (.mul (.lit 2) (.get "vr" e)) (.sub (.lit 1) (.get "sg" e))

/-- `a[x] := a[x] + 1`. -/
abbrev inc (a x : String) : Com := .store a (V x) (.add (.get a (V x)) (.lit 1))

/-- The turn of the degree pass for a unit clause. -/
def degUnit : Com := .seq (.assign "na" (ncodeAt (V "i"))) (.seq (inc "deg" "na") (bump "i"))

/-- The turn of the degree pass for a clause of two literals. -/
def degPair : Com :=
  .seq (.assign "na" (ncodeAt (V "i")))
    (.seq (.assign "nb" (ncodeAt (.add (V "i") (.lit 1))))
      (.seq (inc "deg" "na") (.seq (inc "deg" "nb") (.assign "i" (.add (V "i") (.lit 2))))))

def degBody : Com := .seq (.ite (.eq (.get "cnt" (V "c")) (.lit 1)) degUnit degPair) (bump "c")

/-- Pass (a): the out-degrees. -/
def degPass : Com :=
  .seq (.assign "i" (.lit 0))
    (.seq (.assign "c" (.lit 0)) (.while (.lt (V "c") (V "C")) degBody))

/-- One turn of the prefix sums: `pos[u] := off[u]; off[u + 1] := off[u] + deg[u]`. -/
def prefBody : Com :=
  .seq (.store "pos" (V "u") (.get "off" (V "u")))
    (.seq (.store "off" (.add (V "u") (.lit 1)) (.add (.get "off" (V "u")) (.get "deg" (V "u"))))
      (bump "u"))

/-- Pass (b): the offsets, the free-slot pointers, and the edge count `E`. -/
def prefPass : Com :=
  .seq (.store "off" (.lit 0) (.lit 0))
    (.seq (.seq (.assign "u" (.lit 0)) (.while (.lt (V "u") (V "N")) prefBody))
      (.assign "E" (.get "off" (V "N"))))

/-- Emit the edge `(x, y)`: `tgt[pos[x]] := y; pos[x] := pos[x] + 1`. -/
abbrev put (x y : String) : Com := .seq (.store "tgt" (.get "pos" (V x)) (V y)) (inc "pos" x)

def fillUnit : Com :=
  .seq (.assign "ca" (codeAt (V "i")))
    (.seq (.assign "na" (ncodeAt (V "i"))) (.seq (put "na" "ca") (bump "i")))

def fillPair : Com :=
  .seq (.assign "ca" (codeAt (V "i")))
    (.seq (.assign "na" (ncodeAt (V "i")))
      (.seq (.assign "cb" (codeAt (.add (V "i") (.lit 1))))
        (.seq (.assign "nb" (ncodeAt (.add (V "i") (.lit 1))))
          (.seq (put "na" "cb") (.seq (put "nb" "ca") (.assign "i" (.add (V "i") (.lit 2))))))))

def fillBody : Com := .seq (.ite (.eq (.get "cnt" (V "c")) (.lit 1)) fillUnit fillPair) (bump "c")

/-- Pass (c): the targets. -/
def fillPass : Com :=
  .seq (.assign "i" (.lit 0))
    (.seq (.assign "c" (.lit 0)) (.while (.lt (V "c") (V "C")) fillBody))

/-- The whole construction. -/
def build : Com := .seq degPass (.seq prefPass fillPass)

/-! ### What every pass keeps -/

/-- The scalars and arrays the scan left, which no pass changes. -/
def Static (F : Formula) (σ : Env) : Prop :=
  σ.vars "k" = (lits F).length ∧ σ.vars "C" = F.length ∧ σ.vars "N" = N F ∧
    (lits F).length ≤ (σ.arrs "vr").length ∧ (lits F).length ≤ (σ.arrs "sg").length ∧
    F.length + 1 ≤ (σ.arrs "cnt").length ∧
    (∀ i, i < (lits F).length → (σ.arrs "vr").getD i 0 = iv F i) ∧
    (∀ i, i < (lits F).length → (σ.arrs "sg").getD i 0 = sv F i) ∧
    (∀ c, c < F.length → (σ.arrs "cnt").getD c 0 = (F.getD c []).length)

theorem Static.of_eq {F : Formula} {σ σ' : Env} (h : Static F σ) (hk : σ'.vars "k" = σ.vars "k")
    (hC : σ'.vars "C" = σ.vars "C") (hN : σ'.vars "N" = σ.vars "N")
    (hvr : σ'.arrs "vr" = σ.arrs "vr") (hsg : σ'.arrs "sg" = σ.arrs "sg")
    (hcnt : σ'.arrs "cnt" = σ.arrs "cnt") : Static F σ' := by
  unfold Static at h ⊢
  rw [hk, hC, hN, hvr, hsg, hcnt]; exact h

/-- The degree array holds the out-degrees in `L`. -/
def Deg (F : Formula) (L : List (ℕ × ℕ)) (σ : Env) : Prop :=
  ∃ g, σ.arrs "deg" = arrOf (N F + 1) g ∧ ∀ u, u < N F + 1 → g u = cntSrc L u

theorem Deg.of_eq {F : Formula} {L : List (ℕ × ℕ)} {σ σ' : Env} (h : Deg F L σ)
    (hd : σ'.arrs "deg" = σ.arrs "deg") : Deg F L σ' := by
  unfold Deg at h ⊢; rw [hd]; exact h

/-- The free-slot pointers and the targets, with `L` emitted. -/
def Rows (F : Formula) (L : List (ℕ × ℕ)) (σ : Env) : Prop :=
  ∃ p t, σ.arrs "pos" = arrOf (N F + 1) p ∧ σ.arrs "tgt" = arrOf (edges F).length t ∧
    RowState F L p t

theorem Rows.of_eq {F : Formula} {L : List (ℕ × ℕ)} {σ σ' : Env} (h : Rows F L σ)
    (hp : σ'.arrs "pos" = σ.arrs "pos") (ht : σ'.arrs "tgt" = σ.arrs "tgt") : Rows F L σ' := by
  unfold Rows at h ⊢; rw [hp, ht]; exact h

/-! ### Pass (a): the degrees -/

def DegInv (F : Formula) (σ : Env) : Prop :=
  Static F σ ∧ σ.vars "c" ≤ F.length ∧ σ.vars "i" = start F (σ.vars "c") ∧
    Deg F (edgesUpTo F (σ.vars "c")) σ

variable {F : Formula}

theorem degBody_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => DegInv F σ ∧ σ.vars "c" < F.length) degBody
      (fun σ σ' => DegInv F σ' ∧ σ'.vars "c" = σ.vars "c" + 1) 50 := by
  intro σ hσ
  obtain ⟨⟨hS, hcC, hi, hD⟩, hc⟩ := hσ
  have hS' := hS
  obtain ⟨hk, hC, hN, hvrl, hsgl, hcntl, hvr, hsg, hcnt⟩ := hS'
  obtain ⟨g, hdeg, hg⟩ := hD
  have hlen := hcnt _ hc
  have hst := start_add_le F _ hc
  have hcases := clause_length_cases F hw _ hc
  have hvr0 : (σ.arrs "vr").getD (σ.vars "i") 0 = iv F (σ.vars "i") := hvr (σ.vars "i") (by omega)
  have hsg0 : (σ.arrs "sg").getD (σ.vars "i") 0 = sv F (σ.vars "i") := hsg (σ.vars "i") (by omega)
  have hiv0 := two_iv_add_two_le F (σ.vars "i")
  have hiv1 := two_iv_add_two_le F (σ.vars "i" + 1)
  have hsv0 := sv_le F (σ.vars "i")
  have hsv1 := sv_le F (σ.vars "i" + 1)
  have hdegl : (σ.arrs "deg").length = N F + 1 := by rw [hdeg, length_arrOf]
  have hgle : ∀ u, u < N F + 1 → g u ≤ (lits F).length := fun u hu => by
    rw [hg u hu]
    exact (cntSrc_le_length _ _).trans (length_le_of_prefix F (edgesUpTo_prefix F _))
  have hX : 2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")) < N F + 1 := by omega
  have hY : 2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1)) < N F + 1 := by omega
  have hd0 : (σ.arrs "deg").getD (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) 0
      ≤ (lits F).length := by
    rw [hdeg, getD_arrOf _ hX]; exact hgle _ hX
  rcases hcases with h1 | h2
  · -- a unit clause
    run_vcg
    all_goals try (env_simp [List.length_set, hvr0, hsg0]; omega)
    refine ⟨⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), ?_, ?_, ?_⟩, ?_⟩
    · env_simp; omega
    · env_simp
      rw [start_succ F _ hc]; omega
    · refine ⟨upd g (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
        (g (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1), ?_, ?_⟩
      · env_simp [hvr0, hsg0]
        rw [hdeg, getD_arrOf _ hX, set_arrOf_eq_upd]
      · env_simp
        rw [edgesUpTo_succ F _ hc, clauseEdges_unit F _ hc h1, ← hi]
        exact cntSrc_step1 hg _ _
    · env_simp
  · -- a clause of two literals
    have hvr1 : (σ.arrs "vr").getD (σ.vars "i" + 1) 0 = iv F (σ.vars "i" + 1) :=
      hvr (σ.vars "i" + 1) (by omega)
    have hsg1 : (σ.arrs "sg").getD (σ.vars "i" + 1) 0 = sv F (σ.vars "i" + 1) :=
      hsg (σ.vars "i" + 1) (by omega)
    have hd1 : ((σ.arrs "deg").set (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
          ((σ.arrs "deg").getD (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) 0 + 1)).getD
          (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1))) 0 ≤ (lits F).length + 1 := by
      rw [hdeg, getD_arrOf _ hX, set_arrOf_eq_upd, getD_arrOf _ hY]
      exact upd_le (by have := hgle _ hX; omega) (by have := hgle _ hY; omega)
    run_vcg
    all_goals try (env_simp [List.length_set, hvr0, hsg0, hvr1, hsg1]; omega)
    refine ⟨⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), ?_, ?_, ?_⟩, ?_⟩
    · env_simp; omega
    · env_simp
      rw [start_succ F _ hc]; omega
    · refine ⟨upd (upd g (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
          (g (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1))
          (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1)))
          (upd g (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
            (g (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1)
            (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1))) + 1), ?_, ?_⟩
      · env_simp [hvr0, hsg0, hvr1, hsg1]
        rw [hdeg, getD_arrOf _ hX, set_arrOf_eq_upd, getD_arrOf _ hY, set_arrOf_eq_upd]
      · env_simp
        rw [edgesUpTo_succ F _ hc, clauseEdges_pair F _ hc h2, ← hi]
        exact cntSrc_step2 hg _ _ _ _
    · env_simp

theorem degLoop_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => DegInv F (σ.setVar "c" 0))
      (.seq (.assign "c" (.lit 0)) (.while (.lt (V "c") (V "C")) degBody))
      (fun _ σ' => DegInv F σ' ∧ σ'.vars "c" = F.length) (54 * F.length + 6) :=
  Spec.forRangeZero "c" "C" (DegInv F) F.length 50 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2.1) (degBody_spec hw hB)

theorem degPass_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => Static F σ ∧ σ.arrs "deg" = List.replicate (N F + 1) 0) degPass
      (fun _ σ' => Static F σ' ∧ Deg F (edges F) σ') (54 * F.length + 8) := by
  refine (Spec.seq (Spec.assign (x := "i") (e := .lit 0) (f := fun _ => 0)
    (fun _ _ => evalB_lit (by omega))) (degLoop_spec hw hB) ?_ ?_).mono (by simp only [size_lit]; omega)
  · rintro σ σ' ⟨hS, hdeg⟩ rfl
    refine ⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), by simp,
      by simp [start_zero], fun _ => 0, ?_, ?_⟩
    · simp [hdeg, replicate_eq_arrOf]
    · simp [edgesUpTo_zero]
  · rintro σ σ' σ'' - - ⟨⟨hS, -, -, hD⟩, hc⟩
    rw [hc, edgesUpTo_length] at hD
    exact ⟨hS, hD⟩

/-! ### Pass (b): the prefix sums -/

def PInv (F : Formula) (σ : Env) : Prop :=
  Static F σ ∧ σ.vars "u" ≤ N F ∧ Deg F (edges F) σ ∧
    (∃ o, σ.arrs "off" = arrOf (N F + 1) o ∧ ∀ v, v ≤ σ.vars "u" → o v = S F v) ∧
    (∃ p, σ.arrs "pos" = arrOf (N F + 1) p ∧ ∀ v, v < σ.vars "u" → p v = S F v)

theorem prefBody_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => PInv F σ ∧ σ.vars "u" < N F) prefBody
      (fun σ σ' => PInv F σ' ∧ σ'.vars "u" = σ.vars "u" + 1) 20 := by
  intro σ hσ
  obtain ⟨⟨hS, huN, ⟨g, hdeg, hg⟩, ⟨o, hoff, ho⟩, ⟨p, hpos, hp⟩⟩, hu⟩ := hσ
  have hEk : (edges F).length ≤ (lits F).length := length_edges_le F
  have hSE := S_succ_le_E F hw (σ.vars "u")
  have hoffl : (σ.arrs "off").length = N F + 1 := by rw [hoff, length_arrOf]
  have hposl : (σ.arrs "pos").length = N F + 1 := by rw [hpos, length_arrOf]
  have hdegl : (σ.arrs "deg").length = N F + 1 := by rw [hdeg, length_arrOf]
  have hoff0 : (σ.arrs "off").getD (σ.vars "u") 0 = S F (σ.vars "u") := by
    rw [hoff, getD_arrOf _ (by omega)]; exact ho _ le_rfl
  have hdeg0 : (σ.arrs "deg").getD (σ.vars "u") 0 = degF F (σ.vars "u") := by
    rw [hdeg, getD_arrOf _ (by omega)]; exact hg _ (by omega)
  run_vcg
  all_goals try (env_simp [List.length_set, hoff0, hdeg0]; omega)
  refine ⟨⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), ?_, ?_, ?_, ?_⟩, ?_⟩
  · env_simp; omega
  · refine ⟨g, ?_, hg⟩
    env_simp; exact hdeg
  · refine ⟨upd o (σ.vars "u" + 1) (S F (σ.vars "u") + degF F (σ.vars "u")), ?_, ?_⟩
    · env_simp [hoff0, hdeg0]
      rw [hoff, set_arrOf_eq_upd]
    · env_simp
      intro v hv
      rw [upd_apply]
      split_ifs with h
      · rw [h, S_succ]
      · exact ho v (by omega)
  · refine ⟨upd p (σ.vars "u") (S F (σ.vars "u")), ?_, ?_⟩
    · env_simp [hoff0]
      rw [hpos, set_arrOf_eq_upd]
    · env_simp
      intro v hv
      rw [upd_apply]
      split_ifs with h
      · rw [h]
      · exact hp v (by omega)
  · env_simp

theorem prefLoop_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => PInv F (σ.setVar "u" 0))
      (.seq (.assign "u" (.lit 0)) (.while (.lt (V "u") (V "N")) prefBody))
      (fun _ σ' => PInv F σ' ∧ σ'.vars "u" = N F) (24 * N F + 6) :=
  Spec.forRangeZero "u" "N" (PInv F) (N F) 20 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2.2.1) (prefBody_spec hw hB)

/-- The loop and the final `E := off[N]`. -/
theorem prefTail_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => PInv F (σ.setVar "u" 0))
      (.seq (.seq (.assign "u" (.lit 0)) (.while (.lt (V "u") (V "N")) prefBody))
        (.assign "E" (.get "off" (V "N"))))
      (fun _ σ' => Static F σ' ∧ σ'.arrs "off" = arrOf (N F + 1) (S F) ∧
        (∃ p, σ'.arrs "pos" = arrOf (N F + 1) p ∧ ∀ v, v < N F → p v = S F v) ∧
        σ'.vars "E" = (edges F).length) (24 * N F + 10) := by
  have hEk : (edges F).length ≤ (lits F).length := length_edges_le F
  refine (Spec.seq (prefLoop_spec hw hB)
    (Spec.assign (P := fun σ => PInv F σ ∧ σ.vars "u" = N F) (x := "E") (e := .get "off" (V "N"))
      (f := fun σ => (σ.arrs "off").getD (σ.vars "N") 0) ?_) (fun _ _ _ h => h) ?_).mono ?_
  · rintro σ ⟨⟨hS, -, -, ⟨o, hoff, ho⟩, -⟩, hu⟩
    have hN := hS.2.2.1
    have hoN : o (N F) = S F (N F) := ho _ (by omega)
    show (Expr.get "off" (V "N")).evalB B σ = some ((σ.arrs "off").getD (σ.vars "N") 0)
    rw [hN]
    refine evalB_get (evalB_var (by omega)) ?_ ?_
    · rw [hN, hoff, getElem?_arrOf _ (by omega), getD_arrOf _ (by omega)]
    · rw [hoff, getD_arrOf _ (by omega), hoN, S_N F hw]; omega
  · rintro σ σ' σ'' - ⟨⟨hS, -, -, ⟨o, hoff, ho⟩, ⟨p, hpos, hp⟩⟩, hu⟩ rfl
    refine ⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), ?_, ?_, ?_⟩
    · simp only [arrs_setVar]
      rw [hoff]; exact arrOf_congr fun v hv => ho v (by omega)
    · exact ⟨p, by simp only [arrs_setVar]; exact hpos, fun v hv => hp v (by omega)⟩
    · env_simp
      rw [hS.2.2.1, hoff, getD_arrOf _ (by omega), ho _ (by omega), S_N F hw]
  · simp only [size_get, size_var]; omega

theorem prefPass_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => Static F σ ∧ Deg F (edges F) σ ∧
        σ.arrs "off" = List.replicate (N F + 1) 0 ∧ σ.arrs "pos" = List.replicate (N F + 1) 0)
      prefPass
      (fun _ σ' => Static F σ' ∧ σ'.arrs "off" = arrOf (N F + 1) (S F) ∧
        (∃ p, σ'.arrs "pos" = arrOf (N F + 1) p ∧ ∀ v, v < N F → p v = S F v) ∧
        σ'.vars "E" = (edges F).length) (24 * N F + 13) := by
  refine (Spec.seq (Spec.store (a := "off") (i := .lit 0) (e := .lit 0) (idx := fun _ => 0)
      (f := fun _ => 0) (fun _ _ => evalB_lit (by omega)) (fun _ _ => evalB_lit (by omega))
      (fun σ h => by rw [h.2.2.1]; simp))
    (prefTail_spec hw hB) ?_ (fun _ _ _ _ _ h => h)).mono ?_
  · rintro σ σ' ⟨hS, hD, hoff, hpos⟩ rfl
    refine ⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), by simp,
      hD.of_eq (by simp), ⟨upd (fun _ => 0) 0 0, ?_, ?_⟩, ⟨fun _ => 0, ?_, ?_⟩⟩
    · env_simp
      rw [hoff, replicate_eq_arrOf, set_arrOf_eq_upd]
    · env_simp
      intro v hv
      have : v = 0 := by omega
      subst this; simp [S_zero]
    · env_simp
      rw [hpos, replicate_eq_arrOf]
    · simp
  · simp only [size_lit]; omega

/-! ### Pass (c): the fill -/

def FInv (F : Formula) (σ : Env) : Prop :=
  Static F σ ∧ σ.vars "c" ≤ F.length ∧ σ.vars "i" = start F (σ.vars "c") ∧
    σ.vars "E" = (edges F).length ∧ σ.arrs "off" = arrOf (N F + 1) (S F) ∧
    Rows F (edgesUpTo F (σ.vars "c")) σ

set_option maxHeartbeats 4000000 in
theorem fillBody_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => FInv F σ ∧ σ.vars "c" < F.length) fillBody
      (fun σ σ' => FInv F σ' ∧ σ'.vars "c" = σ.vars "c" + 1) 80 := by
  intro σ hσ
  obtain ⟨⟨hS, hcC, hi, hE, hoff, hR⟩, hc⟩ := hσ
  have hS' := hS
  obtain ⟨hk, hC, hN, hvrl, hsgl, hcntl, hvr, hsg, hcnt⟩ := hS'
  obtain ⟨p, t, hpos, htgt, hRS⟩ := hR
  have hlen := hcnt _ hc
  have hst := start_add_le F _ hc
  have hcases := clause_length_cases F hw _ hc
  have hvr0 : (σ.arrs "vr").getD (σ.vars "i") 0 = iv F (σ.vars "i") := hvr (σ.vars "i") (by omega)
  have hsg0 : (σ.arrs "sg").getD (σ.vars "i") 0 = sv F (σ.vars "i") := hsg (σ.vars "i") (by omega)
  have hiv0 := two_iv_add_two_le F (σ.vars "i")
  have hiv1 := two_iv_add_two_le F (σ.vars "i" + 1)
  have hsv0 := sv_le F (σ.vars "i")
  have hsv1 := sv_le F (σ.vars "i" + 1)
  have hEk : (edges F).length ≤ (lits F).length := length_edges_le F
  have hposl : (σ.arrs "pos").length = N F + 1 := by rw [hpos, length_arrOf]
  have htgtl : (σ.arrs "tgt").length = (edges F).length := by rw [htgt, length_arrOf]
  have hX : 2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")) < N F := by omega
  have hY : 2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1)) < N F := by omega
  have hpX : (σ.arrs "pos").getD (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) 0 =
      p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) := by
    rw [hpos, getD_arrOf _ (by omega)]
  rcases hcases with h1 | h2
  · -- a unit clause: the edge `(¬a, a)`
    have hpre : edgesUpTo F (σ.vars "c") ++
        [(2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")), 2 * iv F (σ.vars "i") + sv F (σ.vars "i"))]
        <+: edges F := by
      have := edgesUpTo_succ_prefix F _ hc
      rwa [clauseEdges_unit F _ hc h1, ← hi] at this
    have hpXE := hRS.p_lt_E F hw hpre hX
    run_vcg
    all_goals try (env_simp [List.length_set, hvr0, hsg0, hpX]; omega)
    refine ⟨⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), ?_, ?_, ?_, ?_,
      ?_⟩, ?_⟩
    · env_simp; omega
    · env_simp
      rw [start_succ F _ hc]; omega
    · env_simp; exact hE
    · env_simp; exact hoff
    · refine ⟨upd p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
          (p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1),
        upd t (p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))))
          (2 * iv F (σ.vars "i") + sv F (σ.vars "i")), ?_, ?_, ?_⟩
      · env_simp [hvr0, hsg0, hpX]
        rw [hpos, set_arrOf_eq_upd]
      · env_simp [hvr0, hsg0, hpX]
        rw [htgt, set_arrOf_eq_upd]
      · env_simp
        rw [edgesUpTo_succ F _ hc, clauseEdges_unit F _ hc h1, ← hi]
        exact hRS.emit F hw hpre hX
    · env_simp
  · -- a clause of two literals: the edges `(¬a, b)` then `(¬b, a)`
    have hvr1 : (σ.arrs "vr").getD (σ.vars "i" + 1) 0 = iv F (σ.vars "i" + 1) :=
      hvr (σ.vars "i" + 1) (by omega)
    have hsg1 : (σ.arrs "sg").getD (σ.vars "i" + 1) 0 = sv F (σ.vars "i" + 1) :=
      hsg (σ.vars "i" + 1) (by omega)
    have hpre2 : edgesUpTo F (σ.vars "c") ++
        [(2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")),
            2 * iv F (σ.vars "i" + 1) + sv F (σ.vars "i" + 1)),
          (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1)),
            2 * iv F (σ.vars "i") + sv F (σ.vars "i"))] <+: edges F := by
      have := edgesUpTo_succ_prefix F _ hc
      rwa [clauseEdges_pair F _ hc h2, ← hi] at this
    have hpre2' : (edgesUpTo F (σ.vars "c") ++
        [(2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")),
            2 * iv F (σ.vars "i" + 1) + sv F (σ.vars "i" + 1))]) ++
          [(2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1)),
            2 * iv F (σ.vars "i") + sv F (σ.vars "i"))] <+: edges F := by
      rw [List.append_assoc, List.singleton_append]; exact hpre2
    have hpre1 : edgesUpTo F (σ.vars "c") ++
        [(2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")),
            2 * iv F (σ.vars "i" + 1) + sv F (σ.vars "i" + 1))] <+: edges F :=
      (List.prefix_append _ _).trans hpre2'
    have hR1 := hRS.emit F hw hpre1 hX
    have hR2 := hR1.emit F hw hpre2' hY
    rw [List.append_assoc, List.singleton_append] at hR2
    have hpXE := hRS.p_lt_E F hw hpre1 hX
    have hpY : ((σ.arrs "pos").set (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
          (p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1)).getD
          (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1))) 0 =
        upd p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
          (p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1)
          (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1))) := by
      rw [hpos, set_arrOf_eq_upd, getD_arrOf _ (by omega)]
    have hpYE := hR1.p_lt_E F hw hpre2' hY
    run_vcg
    all_goals try (env_simp [List.length_set, hvr0, hsg0, hvr1, hsg1, hpX, hpY]; omega)
    refine ⟨⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), ?_, ?_, ?_, ?_,
      ?_⟩, ?_⟩
    · env_simp; omega
    · env_simp
      rw [start_succ F _ hc]; omega
    · env_simp; exact hE
    · env_simp; exact hoff
    · refine ⟨upd (upd p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
            (p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1))
          (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1)))
          (upd p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
            (p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1)
            (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1))) + 1),
        upd (upd t (p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))))
            (2 * iv F (σ.vars "i" + 1) + sv F (σ.vars "i" + 1)))
          (upd p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i")))
            (p (2 * iv F (σ.vars "i") + (1 - sv F (σ.vars "i"))) + 1)
            (2 * iv F (σ.vars "i" + 1) + (1 - sv F (σ.vars "i" + 1))))
          (2 * iv F (σ.vars "i") + sv F (σ.vars "i")), ?_, ?_, ?_⟩
      · env_simp [hvr0, hsg0, hvr1, hsg1, hpX, hpY]
        rw [hpos, set_arrOf_eq_upd, set_arrOf_eq_upd]
      · env_simp [hvr0, hsg0, hvr1, hsg1, hpX, hpY]
        rw [htgt, set_arrOf_eq_upd, set_arrOf_eq_upd]
      · env_simp
        rw [edgesUpTo_succ F _ hc, clauseEdges_pair F _ hc h2, ← hi]
        exact hR2
    · env_simp

theorem fillLoop_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => FInv F (σ.setVar "c" 0))
      (.seq (.assign "c" (.lit 0)) (.while (.lt (V "c") (V "C")) fillBody))
      (fun _ σ' => FInv F σ' ∧ σ'.vars "c" = F.length) (84 * F.length + 6) :=
  Spec.forRangeZero "c" "C" (FInv F) F.length 80 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2.1) (fillBody_spec hw hB)

theorem fillPass_spec {B : ℕ} (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (fun σ => Static F σ ∧ σ.vars "E" = (edges F).length ∧
        σ.arrs "off" = arrOf (N F + 1) (S F) ∧
        (∃ p, σ.arrs "pos" = arrOf (N F + 1) p ∧ ∀ v, v < N F → p v = S F v) ∧
        σ.arrs "tgt" = List.replicate (edges F).length 0)
      fillPass
      (fun _ σ' => Static F σ' ∧ σ'.vars "E" = (edges F).length ∧
        σ'.arrs "off" = arrOf (N F + 1) (S F) ∧ Rows F (edges F) σ') (84 * F.length + 8) := by
  refine (Spec.seq (Spec.assign (x := "i") (e := .lit 0) (f := fun _ => 0)
    (fun _ _ => evalB_lit (by omega))) (fillLoop_spec hw hB) ?_ ?_).mono
    (by simp only [size_lit]; omega)
  · rintro σ σ' ⟨hS, hE, hoff, ⟨p, hpos, hp⟩, htgt⟩ rfl
    refine ⟨hS.of_eq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), by simp,
      by simp [start_zero], by simp [hE], by simp [hoff], p, fun _ => 0, by simp [hpos],
      by simp [htgt, replicate_eq_arrOf], ?_⟩
    env_simp
    rw [edgesUpTo_zero]; exact rowState_nil F hp
  · rintro σ σ' σ'' - - ⟨⟨hS, -, -, hE, hoff, hR⟩, hc⟩
    rw [hc, edgesUpTo_length] at hR
    exact ⟨hS, hE, hoff, hR⟩

/-! ### The whole construction -/

/-- What the earlier phases leave: the scan's scalars and arrays (`Static`, plus the clause
numbers `cl`, which the construction does not read), and the four fresh arrays. -/
def Pre (F : Formula) (σ : Env) : Prop :=
  Static F σ ∧ (lits F).length ≤ (σ.arrs "cl").length ∧
    (∀ i, i < (lits F).length → (σ.arrs "cl").getD i 0 = cv F i) ∧
    σ.arrs "deg" = List.replicate (N F + 1) 0 ∧ σ.arrs "off" = List.replicate (N F + 1) 0 ∧
    σ.arrs "pos" = List.replicate (N F + 1) 0 ∧
    σ.arrs "tgt" = List.replicate (edges F).length 0

theorem off_not_warrs_degPass : "off" ∉ degPass.warrs := by decide
theorem pos_not_warrs_degPass : "pos" ∉ degPass.warrs := by decide
theorem tgt_not_warrs_degPass : "tgt" ∉ degPass.warrs := by decide
theorem tgt_not_warrs_prefPass : "tgt" ∉ prefPass.warrs := by decide

/-- **The construction is correct**: from the scanned formula it builds the CSR
representation of the implication graph — offsets `off`, targets `tgt`, with row `u`
listing exactly the out-neighbours of `u` — and sets `E` to the number of edges, in time
linear in the size of the formula. -/
theorem build_spec {B : ℕ} (F : Formula) (hw : WidthOk F)
    (hB : 2 * (lits F).length + N F + F.length + 16 < B) :
    Spec B (Pre F) build
      (fun _ σ' => ∃ off tgt : ℕ → ℕ,
        Lax808846Proofs.Reasoning.Lib.Csr "off" "tgt" (N F) (edges F).length (N F) off tgt σ' ∧
        (∀ u v, (∃ j, off u ≤ j ∧ j < off (u + 1) ∧ tgt j = v) ↔ E F u v) ∧
        σ'.vars "E" = (edges F).length ∧ σ'.vars "N" = N F ∧ σ'.vars "k" = (lits F).length ∧
        σ'.vars "C" = F.length)
      (138 * ((lits F).length + N F + F.length + 1)) := by
  have h2 := ((prefPass_spec hw hB).frame).conseq
    (P' := fun σ => (Static F σ ∧ Deg F (edges F) σ ∧
        σ.arrs "off" = List.replicate (N F + 1) 0 ∧ σ.arrs "pos" = List.replicate (N F + 1) 0) ∧
      σ.arrs "tgt" = List.replicate (edges F).length 0)
    (Q' := fun _ σ' => (Static F σ' ∧ σ'.arrs "off" = arrOf (N F + 1) (S F) ∧
        (∃ p, σ'.arrs "pos" = arrOf (N F + 1) p ∧ ∀ v, v < N F → p v = S F v) ∧
        σ'.vars "E" = (edges F).length) ∧ σ'.arrs "tgt" = List.replicate (edges F).length 0)
    (fun _ h => h.1) (fun _ _ hP hQ => ⟨hQ.1, (hQ.2.2.1 "tgt" tgt_not_warrs_prefPass).trans hP.2⟩)
    le_rfl
  have h1 := ((degPass_spec hw hB).frame).conseq (P' := Pre F)
    (Q' := fun _ σ' => (Static F σ' ∧ Deg F (edges F) σ' ∧
        σ'.arrs "off" = List.replicate (N F + 1) 0 ∧ σ'.arrs "pos" = List.replicate (N F + 1) 0) ∧
      σ'.arrs "tgt" = List.replicate (edges F).length 0)
    (fun _ h => ⟨h.1, h.2.2.2.1⟩)
    (fun _ _ hP hQ => ⟨⟨hQ.1.1, hQ.1.2, (hQ.2.2.1 "off" off_not_warrs_degPass).trans hP.2.2.2.2.1,
      (hQ.2.2.1 "pos" pos_not_warrs_degPass).trans hP.2.2.2.2.2.1⟩,
      (hQ.2.2.1 "tgt" tgt_not_warrs_degPass).trans hP.2.2.2.2.2.2⟩) le_rfl
  refine (Spec.seq h1 (Spec.seq h2 (fillPass_spec hw hB)
    (R := fun _ σ'' => Static F σ'' ∧ σ''.vars "E" = (edges F).length ∧
      σ''.arrs "off" = arrOf (N F + 1) (S F) ∧ Rows F (edges F) σ'')
    ?_ (fun _ _ _ _ _ h => h)) (fun _ _ _ h => h) ?_).mono ?_
  · rintro σ σ' - ⟨⟨hS, hoff, hpos, hE⟩, htgt⟩
    exact ⟨hS, hE, hoff, hpos, htgt⟩
  · rintro σ σ' σ'' - - ⟨hS, hE, hoff, p, t, hpos, htgt, hRS⟩
    refine ⟨S F, t, ⟨hoff, htgt, fun i _ => S_le_succ F i, S_N F hw,
      fun j hj => hRS.target_lt F hw hj⟩, hRS.done F hw, hE, hS.2.2.1, hS.1, hS.2.1⟩
  · omega

end Lax117284Proofs.TwoSAT.Machine.Build
