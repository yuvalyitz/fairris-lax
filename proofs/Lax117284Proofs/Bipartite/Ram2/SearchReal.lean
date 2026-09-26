import Lax117284Proofs.Bipartite.Ram2.SearchAbs
import Lax117284Proofs.Bipartite.Ram2.Scan
import Lax117284Proofs.Bipartite.Ram2.Mu

/-!
Tying the abstract search state `AS` to an IMP+ environment, and the straight-line phases of one
turn of the backtracking search.

Layout. Scalars: `top` (stack height), `result` (`2` = still searching, `1` = augmented, `0` = no
augmenting path), `t1 = top - 1`, `occ` (encoded occupant of the candidate), `k`/`rr`/`ll` (the
apply loop), the word's `V n m`, and the scan's `i x xe found foundJ cand cont`. Arrays: `a` (the
word), `vis`, `mu` (`0` = free, `l + 1` = matched to `l`), and the three parallel stacks `stkL`
(left vertex), `stkR` (chosen right vertex), `stkX` (resume slot), all of length `m + 1`.

`Real a σ` says the environment's arrays are exactly the abstract state's functions. Everything
about *correctness* lives in `SearchAbs`; this file only shows that the machine's stores realize
the abstract transitions `AS.choose`, `AS.push`, `AS.pop`.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching
open scoped Classical

variable {B : ℕ}

/-- **The environment realizes the abstract state.** -/
structure Real (x : List ℕ) (μ₀ : ℕ → Option ℕ) (a : AS) (σ : Env) : Prop where
  top : σ.vars "top" = a.top
  V : σ.vars "V" = Vw x
  n : σ.vars "n" = nw x
  m : σ.vars "m" = mw x
  arr : ArrOK x σ
  vis : VisOK a.visB (mw x) σ
  mu : MuOK μ₀ (mw x) σ
  stkL : σ.arrs "stkL" = arrOf (mw x + 1) a.Ls
  stkR : σ.arrs "stkR" = arrOf (mw x + 1) a.Rs
  stkX : σ.arrs "stkX" = arrOf (mw x + 1) a.Xs

/-- Everything fixed about a search: the word, the bound, the matching, the start vertex. -/
structure Ctx (B : ℕ) (x : List ℕ) (μ₀ : ℕ → Option ℕ) (l₀ : ℕ) : Prop where
  good : Good x
  hB : x.length + 8 ≤ B
  hl₀ : l₀ < nw x
  res : Respects (adjw x) μ₀
  inj : InjOnSupport μ₀
  unm : ¬ Matched μ₀ l₀
  hμn : ∀ j l, μ₀ j = some l → l < nw x
  supp : ∀ j l, μ₀ j = some l → j < mw x

theorem set_arrOf_update (n i v : ℕ) (f : ℕ → ℕ) :
    (arrOf n f).set i v = arrOf n (Function.update f i v) := by
  rw [set_arrOf]
  exact arrOf_congr (fun k _ => by simp [Function.update_apply])

section Access

variable {x : List ℕ} {μ₀ : ℕ → Option ℕ} {a : AS} {σ : Env}

theorem Real.getL (hR : Real x μ₀ a σ) {k : ℕ} (hk : k < mw x + 1) :
    (σ.arrs "stkL").getD k 0 = a.Ls k := by rw [hR.stkL]; exact getD_arrOf _ hk

theorem Real.getR (hR : Real x μ₀ a σ) {k : ℕ} (hk : k < mw x + 1) :
    (σ.arrs "stkR").getD k 0 = a.Rs k := by rw [hR.stkR]; exact getD_arrOf _ hk

theorem Real.getX (hR : Real x μ₀ a σ) {k : ℕ} (hk : k < mw x + 1) :
    (σ.arrs "stkX").getD k 0 = a.Xs k := by rw [hR.stkX]; exact getD_arrOf _ hk

theorem Real.lenL (hR : Real x μ₀ a σ) : (σ.arrs "stkL").length = mw x + 1 := by
  rw [hR.stkL]; simp

theorem Real.lenR (hR : Real x μ₀ a σ) : (σ.arrs "stkR").length = mw x + 1 := by
  rw [hR.stkR]; simp

theorem Real.lenX (hR : Real x μ₀ a σ) : (σ.arrs "stkX").length = mw x + 1 := by
  rw [hR.stkX]; simp

theorem Real.congr {σ' : Env} (hR : Real x μ₀ a σ)
    (ht : σ'.vars "top" = σ.vars "top") (hV : σ'.vars "V" = σ.vars "V")
    (hn : σ'.vars "n" = σ.vars "n") (hm : σ'.vars "m" = σ.vars "m")
    (ha : ∀ b, σ'.arrs b = σ.arrs b) : Real x μ₀ a σ' := by
  refine ⟨by rw [ht]; exact hR.top, by rw [hV]; exact hR.V, by rw [hn]; exact hR.n,
    by rw [hm]; exact hR.m, hR.arr.congr (ha _), hR.vis.congr (ha _), ?_, ?_, ?_, ?_⟩
  · unfold MuOK; rw [ha]; exact hR.mu
  · rw [ha]; exact hR.stkL
  · rw [ha]; exact hR.stkR
  · rw [ha]; exact hR.stkX

/-- Setting a scalar other than the four the realization reads keeps it. -/
theorem Real.setVar (hR : Real x μ₀ a σ) (y : String) (hy : y ∉ ["top", "V", "n", "m"]) (v : ℕ) :
    Real x μ₀ a (σ.setVar y v) :=
  hR.congr (by simp; rintro rfl; simp at hy) (by simp; rintro rfl; simp at hy)
    (by simp; rintro rfl; simp at hy) (by simp; rintro rfl; simp at hy) (fun _ => rfl)

theorem Real.pop {σ' : Env} (hR : Real x μ₀ a σ) (ht : σ'.vars "top" = a.top - 1)
    (hV : σ'.vars "V" = σ.vars "V") (hn : σ'.vars "n" = σ.vars "n")
    (hm : σ'.vars "m" = σ.vars "m") (ha : ∀ b, σ'.arrs b = σ.arrs b) :
    Real x μ₀ a.pop σ' := by
  refine ⟨ht, by rw [hV]; exact hR.V, by rw [hn]; exact hR.n, by rw [hm]; exact hR.m,
    hR.arr.congr (ha _), hR.vis.congr (ha _), ?_, ?_, ?_, ?_⟩
  · unfold MuOK; rw [ha]; exact hR.mu
  · rw [ha]; exact hR.stkL
  · rw [ha]; exact hR.stkR
  · rw [ha]; exact hR.stkX

theorem Real.withMu {μ' : ℕ → Option ℕ} {σ' : Env} (hR : Real x μ₀ a σ)
    (ht : σ'.vars "top" = σ.vars "top") (hV : σ'.vars "V" = σ.vars "V")
    (hn : σ'.vars "n" = σ.vars "n") (hm : σ'.vars "m" = σ.vars "m")
    (ha : ∀ b, b ≠ "mu" → σ'.arrs b = σ.arrs b) (hmu : MuOK μ' (mw x) σ') :
    Real x μ' a σ' := by
  refine ⟨by rw [ht]; exact hR.top, by rw [hV]; exact hR.V, by rw [hn]; exact hR.n,
    by rw [hm]; exact hR.m, hR.arr.congr (ha _ (by decide)), hR.vis.congr (ha _ (by decide)), hmu,
    ?_, ?_, ?_⟩
  · rw [ha _ (by decide)]; exact hR.stkL
  · rw [ha _ (by decide)]; exact hR.stkR
  · rw [ha _ (by decide)]; exact hR.stkX

end Access

/-! ### The phases of a turn -/

/-- Load the pending frame: `t1 := top - 1; i := stkL[t1]; x := stkX[t1]; xe := a[3 + i];
found := 0; foundJ := 0`. -/
def preludeCom : Com :=
  .seq (.assign "t1" (.sub (.var "top") (.lit 1)))
    (.seq (.assign "i" (.get "stkL" (.var "t1")))
      (.seq (.assign "x" (.get "stkX" (.var "t1")))
        (.seq (.assign "xe" (.get "a" (.add (.lit 3) (.var "i"))))
          (.seq (.assign "found" (.lit 0)) (.assign "foundJ" (.lit 0))))))

/-- The scan found nothing: pop the frame, and if it was the last, the search has failed. -/
def popCom : Com :=
  .seq (.assign "top" (.var "t1"))
    (.ite (.eq (.var "top") (.lit 0)) (.assign "result" (.lit 0)) .skip)

/-- The scan found `foundJ` at the slot before `x`: remember it, resume at `x`, mark it visited,
read its occupant. -/
def foundCom : Com :=
  .seq (.store "stkR" (.var "t1") (.var "foundJ"))
    (.seq (.store "stkX" (.var "t1") (.var "x"))
      (.seq (.store "vis" (.var "foundJ") (.lit 1)) (readMu "foundJ" "occ")))

/-- The candidate is occupied by `occ - 1`: push a frame for it, at the start of its row. -/
def pushCom : Com :=
  .seq (.store "stkL" (.var "top") (.sub (.var "occ") (.lit 1)))
    (.seq (.store "stkX" (.var "top") (.get "a" (.add (.lit 2) (.sub (.var "occ") (.lit 1)))))
      (.assign "top" (.add (.var "top") (.lit 1))))

/-- One iteration of the apply loop: `mu[stkR[k]] := stkL[k] + 1; k := k + 1`. -/
def applyBodyCom : Com :=
  .seq (.assign "rr" (.get "stkR" (.var "k")))
    (.seq (.assign "ll" (.get "stkL" (.var "k")))
      (.seq (writeMu "rr" "ll") (.assign "k" (.add (.var "k") (.lit 1)))))

/-- The candidate is free: write every frame's choice into `mu`, bottom to top. -/
def applyCom : Com :=
  .seq (.assign "k" (.lit 0)) (.while (.lt (.var "k") (.var "top")) applyBodyCom)

/-- The apply loop's invariant: the first `k` frames' choices are in `mu`. -/
def ApplyInv (x : List ℕ) (μ₀ : ℕ → Option ℕ) (b : AS) (σ : Env) : Prop :=
  Real x (applyN μ₀ b.Ls b.Rs (σ.vars "k")) b σ ∧ σ.vars "k" ≤ b.top

/-- What a turn does once the scan is done: pop if nothing was found, otherwise record the
candidate and either succeed (free) or push (occupied). -/
def afterScanCom : Com :=
  .ite (.eq (.var "found") (.lit 0)) popCom
    (.seq foundCom
      (.ite (.eq (.var "occ") (.lit 0)) (.seq applyCom (.assign "result" (.lit 1))) pushCom))

/-- **One turn of the search.** -/
def turnCom : Com := .seq preludeCom (.seq scanRowEarly afterScanCom)

/-- **The search**: turn until `result` leaves `2`. -/
def searchCom : Com := .while (.eq (.var "result") (.lit 2)) turnCom

/-! ### The phases, proved -/

section Phases

variable {x : List ℕ} {μ₀ : ℕ → Option ℕ} {l₀ : ℕ}

theorem offw_succ (x : List ℕ) (l : ℕ) : offw x (l + 1) = x.getD (3 + l) 0 := by
  unfold offw; congr 1; omega

theorem prelude_spec (ctx : Ctx B x μ₀ l₀) {a : AS} :
    Spec B (fun σ => Real x μ₀ a σ ∧ AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a) preludeCom
      (fun σ σ' => σ' = (((((σ.setVar "t1" (a.top - 1)).setVar "i" (a.Ls (a.top - 1))).setVar "x"
        (a.Xs (a.top - 1))).setVar "xe" (offw x (a.Ls (a.top - 1) + 1))).setVar "found" 0).setVar
        "foundJ" 0) 20 := by
  rintro σ ⟨hR, hI⟩
  have hg := ctx.good
  have hB := ctx.hB
  have hpos := hI.top_pos
  have hle : a.top ≤ mw x + 1 := top_le_succ hI
  have hk : a.top - 1 < mw x + 1 := by omega
  have hL := hR.getL hk
  have hX := hR.getX hk
  have hLn := hI.Lbd (a.top - 1) (by omega)
  have hXhi := hI.Xhi (a.top - 1) (by omega)
  have htop := hR.top
  have hlenL := hR.lenL
  have hlenX := hR.lenX
  have hlenA := hR.arr.length
  have hmB : mw x + 1 < B := by have := hg.m_lt; omega
  have htopB : a.top < B := by omega
  have hnB : nw x < B := by have := hg.n_lt; omega
  have hoffB : offw x (a.Ls (a.top - 1) + 1) < B := by
    have := hg.off_lt_len (i := a.Ls (a.top - 1) + 1) (by have := hg.nV; omega); omega
  have h3pos : 3 + a.Ls (a.top - 1) < x.length := by have := hg.len; have := hg.nV; omega
  have hXE : (σ.arrs "a").getD (3 + a.Ls (a.top - 1)) 0 = offw x (a.Ls (a.top - 1) + 1) := by
    rw [hR.arr.getD h3pos, offw_succ]
  rw [List.getD_eq_getElem?_getD] at hL hX hXE
  unfold preludeCom
  run_vcg
  all_goals (simp [htop, hL, hX, hXE]; try omega)

theorem pop_spec {a : AS} (h1B : 3 < B) (hbt : a.top ≤ mw x + 1) (hpos : 1 ≤ a.top)
    (hmB : mw x + 1 < B) :
    Spec B (fun σ => Real x μ₀ a σ ∧ σ.vars "result" = 2 ∧ σ.vars "t1" + 1 = a.top) popCom
      (fun _ σ' => Real x μ₀ a.pop σ' ∧ (a.top = 1 → σ'.vars "result" = 0) ∧
        (2 ≤ a.top → σ'.vars "result" = 2)) 8 := by
  rintro σ ⟨hR, hres, ht1⟩
  unfold popCom
  run_vcg
  · rename_i hc
    simp at hc
    refine ⟨hR.pop (by simp; omega) (by simp) (by simp) (by simp) (by simp), fun _ => by simp,
      fun h => by omega⟩
  · rename_i hc
    simp at hc
    refine ⟨hR.pop (by simp; omega) (by simp) (by simp) (by simp) (by simp), fun h => by omega,
      fun _ => by simp [hres]⟩

theorem found_spec {a : AS} {j xv : ℕ} (h1B : 3 < B) (hbt : a.top ≤ mw x + 1) (hpos : 1 ≤ a.top)
    (hmB : mw x + 1 < B) (hjm : j < mw x) (hμB : ∀ l, μ₀ j = some l → l + 1 < nw x + 1)
    (hnB : nw x + 1 ≤ B) (hxB : xv < B) :
    Spec B (fun σ => Real x μ₀ a σ ∧ σ.vars "t1" + 1 = a.top ∧ σ.vars "foundJ" = j ∧
        σ.vars "x" = xv)
      foundCom
      (fun σ σ' => σ' = (((σ.setArr "stkR" (a.top - 1) j).setArr "stkX" (a.top - 1) xv).setArr
        "vis" j 1).setVar "occ" (match μ₀ j with | none => 0 | some l => l + 1)) 14 := by
  rintro σ ⟨hR, ht1, hjv, hxv⟩
  have hlenR := hR.lenR
  have hlenX := hR.lenX
  have hmu := hR.mu
  have hvis := hR.vis
  have hvislen : (σ.arrs "vis").length = mw x := hvis.length
  have hmuv : (σ.arrs "mu").getD j 0 = (match μ₀ j with | none => 0 | some l => l + 1) :=
    hmu.2 j hjm
  have hmulen : (σ.arrs "mu").length = mw x := hmu.1
  have hoccB : (match μ₀ j with | none => 0 | some l => l + 1) < B := by
    rcases hμ : μ₀ j with _ | l
    · show 0 < B; omega
    · show l + 1 < B; have := hμB l hμ; omega
  rw [List.getD_eq_getElem?_getD] at hmuv
  have ht1' : σ.vars "t1" = a.top - 1 := by omega
  unfold foundCom readMu
  run_vcg
  all_goals (simp [ht1', hjv, hxv, hmuv]; try omega)

theorem Real.found {a : AS} {σ : Env} {s j : ℕ} (hR : Real x μ₀ a σ) (occv : ℕ) :
    Real x μ₀ (a.choose s j)
      ((((σ.setArr "stkR" (a.top - 1) j).setArr "stkX" (a.top - 1) (s + 1)).setArr "vis" j 1).setVar
        "occ" occv) := by
  refine ⟨by simpa [AS.choose] using hR.top, by simpa using hR.V, by simpa using hR.n,
    by simpa using hR.m, hR.arr.congr (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · unfold VisOK
    simp only [arrs_setVar, arrs_setArr]
    simp
    rw [hR.vis, set_arrOf_update]
    exact arrOf_congr (fun k hk => by
      simp [Function.update_apply, AS.choose]; try split_ifs <;> simp_all)
  · simpa [MuOK] using hR.mu
  · simpa [AS.choose] using hR.stkL
  · simp [hR.stkR, set_arrOf_update, AS.choose]
  · simp [hR.stkX, set_arrOf_update, AS.choose]

theorem push_spec (hg : Good x) (hB : x.length + 8 ≤ B) {b : AS} {l' : ℕ} (h1B : 3 < B)
    (hbt : b.top ≤ mw x) (hmB : mw x + 1 < B) (hnB : nw x + 2 ≤ B) (hl' : l' < nw x) :
    Spec B (fun σ => Real x μ₀ b σ ∧ σ.vars "occ" = l' + 1) pushCom
      (fun σ σ' => σ' = ((σ.setArr "stkL" b.top l').setArr "stkX" b.top (offw x l')).setVar "top"
        (b.top + 1)) 18 := by
  rintro σ ⟨hR, hocc⟩
  have hlenL := hR.lenL
  have hlenX := hR.lenX
  have hlenA := hR.arr.length
  have htop := hR.top
  have h2pos : 2 + l' < x.length := hg.offPos_lt (by have := hg.nV; omega)
  have hoff : (σ.arrs "a").getD (2 + l') 0 = offw x l' := hR.arr.getD h2pos
  have hoffB : offw x l' < B := by
    have := hg.off_lt_len (i := l') (by have := hg.nV; omega); omega
  rw [List.getD_eq_getElem?_getD] at hoff
  unfold pushCom
  run_vcg
  all_goals (simp [htop, hocc, hoff]; try omega)

theorem Real.push {b : AS} {σ : Env} {l' : ℕ} (hR : Real x μ₀ b σ) :
    Real x μ₀ (b.push (offw x) l')
      (((σ.setArr "stkL" b.top l').setArr "stkX" b.top (offw x l')).setVar "top" (b.top + 1)) := by
  refine ⟨by simp [AS.push], by simpa using hR.V, by simpa using hR.n, by simpa using hR.m,
    hR.arr.congr (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · unfold VisOK
    simp only [arrs_setVar, arrs_setArr]
    simp
    exact hR.vis
  · simpa [MuOK] using hR.mu
  · simp [hR.stkL, set_arrOf_update, AS.push]
  · simpa [AS.push] using hR.stkR
  · simp [hR.stkX, set_arrOf_update, AS.push]

theorem applyBody_spec {b : AS} (h1B : 3 < B) (hbt : b.top ≤ mw x + 1) (hmB : mw x + 1 < B)
    (hnB : nw x + 2 ≤ B) (hRb : ∀ k < b.top, b.Rs k < mw x) (hLb : ∀ k < b.top, b.Ls k < nw x) :
    Spec B (fun σ => ApplyInv x μ₀ b σ ∧ σ.vars "k" < b.top) applyBodyCom
      (fun σ σ' => ApplyInv x μ₀ b σ' ∧ σ'.vars "k" = σ.vars "k" + 1) 15 := by
  rintro σ ⟨⟨hR, hkt⟩, hk⟩
  have hk' : σ.vars "k" < mw x + 1 := by omega
  have hRk := hR.getR hk'
  have hLk := hR.getL hk'
  have hRkm := hRb _ hk
  have hLkn := hLb _ hk
  have hlenR := hR.lenR
  have hlenL := hR.lenL
  rw [List.getD_eq_getElem?_getD] at hRk hLk
  unfold applyBodyCom
  run_vcg [(writeMu_spec (B := B) (μ := applyN μ₀ b.Ls b.Rs (σ.vars "k")) (m := mw x)
    (j := b.Rs (σ.vars "k")) (lv := b.Ls (σ.vars "k")) (nB := nw x + 1) (by omega) (by omega)
    (by omega) (by omega) hRkm "rr" "ll").frame]
  · rename_i w hw
    obtain ⟨hmu, hv, ha, -, -⟩ := hw
    have hv' : ∀ y, w.vars y = ((σ.setVar "rr" ((σ.arrs "stkR").getD (σ.vars "k") 0)).setVar "ll"
        (((σ.setVar "rr" ((σ.arrs "stkR").getD (σ.vars "k") 0)).arrs "stkL").getD
          ((σ.setVar "rr" ((σ.arrs "stkR").getD (σ.vars "k") 0)).vars "k") 0)).vars y :=
      fun y => hv y (by simp [writeMu, Com.wvars])
    have ha' : ∀ c, c ≠ "mu" → w.arrs c = σ.arrs c := fun c hc => by
      have := ha c (by simp [warrs_writeMu, hc]); simpa using this
    refine ⟨⟨hR.withMu (σ' := w.setVar "k" (w.vars "k" + 1)) ?_ ?_ ?_ ?_
      (fun c hc => by simpa using ha' c hc) ?_, ?_⟩, ?_⟩
    · simp [hv']
    · simp [hv']
    · simp [hv']
    · simp [hv']
    · have hk1 : (w.setVar "k" (w.vars "k" + 1)).vars "k" = σ.vars "k" + 1 := by simp [hv']
      rw [hk1]
      show MuOK (Function.update (applyN μ₀ b.Ls b.Rs (σ.vars "k")) (b.Rs (σ.vars "k"))
        (some (b.Ls (σ.vars "k")))) (mw x) _
      simpa [MuOK] using hmu
    · simp [hv']; omega
    · simp [hv']
  · refine ⟨by simpa [MuOK] using hR.mu, by simp [hRk], by simp [hLk]⟩
  all_goals
    rename_i w hw
    have hwk := hw.2.1 "k" (by simp [writeMu, Com.wvars])
    simp at hwk
    omega

/-- **The apply loop writes every frame's choice into `mu`.** -/
theorem apply_spec {b : AS} (h1B : 3 < B) (hbt : b.top ≤ mw x + 1) (hmB : mw x + 1 < B)
    (hnB : nw x + 2 ≤ B) (hRb : ∀ k < b.top, b.Rs k < mw x) (hLb : ∀ k < b.top, b.Ls k < nw x) :
    Spec B (fun σ => Real x μ₀ b σ) applyCom
      (fun _ σ' => Real x (applyN μ₀ b.Ls b.Rs b.top) b σ') (19 * b.top + 6) := by
  have hloop := Spec.forRangeZero (B := B) (c := applyBodyCom) "k" "top"
    (ApplyInv x μ₀ b) b.top 15 (by omega) (fun σ hσ => hσ.2) (fun σ hσ => hσ.1.top)
    (applyBody_spec h1B hbt hmB hnB hRb hLb)
  refine (hloop.conseq ?_ ?_ (by omega))
  · intro σ hσ
    refine ⟨?_, by simp⟩
    have := hσ.setVar "k" (by simp) 0
    simpa [applyN] using this
  · intro σ σ' _ h
    obtain ⟨⟨hR, -⟩, hk⟩ := h
    rwa [hk] at hR

end Phases

end Lax117284Proofs.Bipartite.Ram2
