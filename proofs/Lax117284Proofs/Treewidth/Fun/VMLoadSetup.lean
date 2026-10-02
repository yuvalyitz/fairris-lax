import Lax117284Proofs.Treewidth.Fun.VMLoadK
import Lax117284Proofs.Treewidth.Fun.ToVal

/-!
# WP V3 (5): the second heap array `HB` and the initial scalars

After reading, `HA[j] = x_j`.  The heap of the input list `x₀ :: x₁ :: … :: xₙ₋₁ :: nil` is laid out *forwards*: cell `j` is
`(x_j, B + j + 1)` for `j + 1 < n` and `(x_{n-1}, 0)` for the last one, root `B` (cell `0`).  `hbLoop` fills `HB[j] := B + j + 1`
for `j < n - 1` (the last cell keeps `HB = 0`, the empty list), and `setupCom` sets `sp hp run` and `STK[0] := B`.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning ToVal

def hbBody : Com := .seq (.store "HB" (V "i") (pl (pl (V "B") (V "i")) (L 1))) (bump "i")

/-- `i := 0; while i < tot do HB[i] := B + i + 1; i++`. -/
def hbLoop : Com := .seq (.assign "i" (L 0)) (.while (.lt (V "i") (V "tot")) hbBody)

def hbCom : Com := .seq (.assign "tot" (mi (V "len") (L 1))) hbLoop

/-- The invariant of the `HB` fill. -/
def HbInv (A Bv N : ℕ) (σ : IEnv) : Prop :=
  σ.vars "tot" = N ∧ σ.vars "i" ≤ N ∧ σ.vars "B" = Bv ∧
    σ.arrs "HB" = arrOf A (fun j => if j < σ.vars "i" then Bv + j + 1 else 0)

theorem hbBody_spec {A Bv N Bi : ℕ} (hNA : N ≤ A) (hb : Bv + N + 1 < Bi) :
    Spec Bi (fun σ => HbInv A Bv N σ ∧ σ.vars "i" < N) hbBody
      (fun σ σ' => HbInv A Bv N σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 12 := by
  refine Spec.pre (P := fun σ => HbInv A Bv N σ ∧ σ.vars "i" < N ∧ σ.vars "i" < (σ.arrs "HB").length ∧
    Bv + σ.vars "i" + 1 < Bi ∧ σ.vars "i" + 1 < Bi) ?_ ?_
  · unfold hbBody bump
    run_vcg
    all_goals try dsimp only at *
    all_goals try nrmAt
    all_goals have hI : HbInv A Bv N σ := ‹_›
    all_goals have hBv : σ.vars "B" = Bv := hI.2.2.1
    all_goals have hlt : σ.vars "i" < N := ‹_›
    all_goals try (first | assumption | omega)
    all_goals refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try nrmAt
    all_goals first
      | exact hI.1
      | omega
      | trivial
      | (rw [hI.2.2.2, set_arrOf]; congr 1; funext k
         rw [hBv]
         split_ifs with h1 h2 <;>
           first | rfl | (exfalso; omega) | (have : k = σ.vars "i" := by omega
                                             subst this; rfl))
  · intro σ ⟨hI, hlt⟩
    obtain ⟨_, _, hBv, hHB⟩ := hI
    have hl : (σ.arrs "HB").length = A := by rw [hHB]; simp
    exact ⟨⟨‹_›, ‹_›, hBv, hHB⟩, hlt, by omega, by omega, by omega⟩

theorem hbLoop_spec {A Bv N Bi : ℕ} (hNA : N ≤ A) (hb : Bv + N + 1 < Bi) (hNB : N < Bi) :
    Spec Bi (fun σ => HbInv A Bv N (σ.setVar "i" 0)) hbLoop
      (fun _ σ' => HbInv A Bv N σ' ∧ σ'.vars "i" = N) ((12 + 4) * N + 6) :=
  Spec.forRangeZero "i" "tot" (HbInv A Bv N) N 12 hNB (fun _ h => h.2.1) (fun _ h => h.1)
    (hbBody_spec hNA hb)

/-- The whole `HB` phase: from `len = |x|`, `B = Bv` and `HB` all zero. -/
theorem hbCom_spec {A Bv n Bi : ℕ} (hnA : n ≤ A) (hn : 1 ≤ n) (hb : Bv + n + 1 < Bi) (hnB : n < Bi) :
    Spec Bi (fun σ => σ.vars "len" = n ∧ σ.vars "B" = Bv ∧ σ.arrs "HB" = arrOf A (fun _ => 0)) hbCom
      (fun _ σ' => HbInv A Bv (n - 1) σ' ∧ σ'.vars "i" = n - 1 ∧ σ'.vars "len" = n) (12 + (16 * n + 6)) := by
  have h1 : Spec Bi (fun σ : IEnv => σ.vars "len" = n ∧ σ.vars "B" = Bv ∧ σ.arrs "HB" = arrOf A (fun _ => 0))
      (.assign "tot" (mi (V "len") (L 1))) (fun σ σ' => σ' = σ.setVar "tot" (σ.vars "len" - 1)) 4 := by
    have := Spec.assign (B := Bi) (P := fun σ : IEnv => σ.vars "len" = n ∧ σ.vars "B" = Bv ∧
        σ.arrs "HB" = arrOf A (fun _ => 0)) (x := "tot") (e := mi (V "len") (L 1))
      (f := fun σ => σ.vars "len" - 1) (by
        intro σ ⟨hl, _, _⟩
        exact RunStep.eval_sub Bi σ _ _ _ 1 (RunStep.eval_var Bi σ "len" (by omega))
          (RunStep.eval_lit Bi 1 σ (by omega)) (by omega))
    exact this.mono (by simp)
  have h2 := (hbLoop_spec (A := A) (Bv := Bv) (N := n - 1) (Bi := Bi) (by omega) (by omega) (by omega)).frame
  refine Spec.mono (Spec.seq h1 h2 ?_ ?_) (by omega)
  · intro σ σ' ⟨hl, hB, hHB⟩ hq
    subst hq
    refine ⟨by simp; omega, by simp, by simpa using hB, ?_⟩
    simpa using hHB
  · intro σ σ' σ'' ⟨hl, _, _⟩ hq hq'
    subst hq
    refine ⟨hq'.1.1, hq'.1.2, ?_⟩
    rw [hq'.2.1 "len" (by decide)]
    simpa using hl

/-! ## The initial scalars -/

/-- `sp := 1; hp := len; run := 1; STK[0] := B`. -/
def setupCom : Com :=
  .seq (.assign "sp" (L 1)) (.seq (.assign "hp" (V "len"))
    (.seq (.assign "run" (L 1)) (.store "STK" (L 0) (V "B"))))

def afterSetup (n Bv : ℕ) (σ : IEnv) : IEnv :=
  (((σ.setVar "sp" 1).setVar "hp" n).setVar "run" 1).setArr "STK" 0 Bv

theorem setup_run {Bi n Bv : ℕ} (h1 : 1 < Bi) {σ : IEnv} (hlen : σ.vars "len" = n) (hB : σ.vars "B" = Bv) (hn : n < Bi)
    (hBv : Bv < Bi) (hSTK : 0 < (σ.arrs "STK").length) :
    Run Bi setupCom σ (afterSetup n Bv σ) 12 := by
  have r1 : Run Bi (.assign "sp" (L 1)) σ (σ.setVar "sp" 1) 2 :=
    (Run.assign (B := Bi) (x := "sp") (RunStep.eval_lit Bi 1 σ h1)).mono (by simp)
  have r2 : Run Bi (.assign "hp" (V "len")) (σ.setVar "sp" 1) ((σ.setVar "sp" 1).setVar "hp" n) 2 := by
    have := Run.assign (B := Bi) (x := "hp") (e := V "len") (σ := σ.setVar "sp" 1) (v := n)
      (by have := RunStep.eval_var Bi (σ.setVar "sp" 1) "len" (by simp; omega); simpa [hlen] using this)
    exact this.mono (by simp)
  have r3 : Run Bi (.assign "run" (L 1)) ((σ.setVar "sp" 1).setVar "hp" n)
      (((σ.setVar "sp" 1).setVar "hp" n).setVar "run" 1) 2 :=
    (Run.assign (B := Bi) (x := "run") (RunStep.eval_lit Bi 1 _ h1)).mono (by simp)
  have r4 : Run Bi (.store "STK" (L 0) (V "B")) (((σ.setVar "sp" 1).setVar "hp" n).setVar "run" 1)
      ((((σ.setVar "sp" 1).setVar "hp" n).setVar "run" 1).setArr "STK" 0 Bv) 3 := by
    have := Run.store (B := Bi) (a := "STK") (i := L 0) (e := V "B") (idx := 0) (v := Bv)
      (σ := ((σ.setVar "sp" 1).setVar "hp" n).setVar "run" 1) (RunStep.eval_lit Bi 0 _ (by omega))
      (by have := RunStep.eval_var Bi (((σ.setVar "sp" 1).setVar "hp" n).setVar "run" 1) "B" (by simp; omega)
          simpa [hB] using this) (by simpa using hSTK)
    exact this.mono (by simp)
  unfold setupCom afterSetup
  exact (r1.seq (r2.seq (r3.seq r4))).mono (by omega)

/-! ## The heap of the input list -/

/-- The tail pointer of cell `j` of the forward layout of a list of length `n`. -/
def hbF (Bv n j : ℕ) : ℕ := if j + 1 < n then Bv + j + 1 else 0

/-- The heap of the input word: cell `j = (x_j, hbF)`. -/
def heapOf (x : List ℕ) (Bv : ℕ) : List (ℕ × ℕ) :=
  (List.range x.length).map (fun j => (x.getD j 0, hbF Bv x.length j))

theorem heapOf_length (x : List ℕ) (Bv : ℕ) : (heapOf x Bv).length = x.length := by simp [heapOf]

theorem heapOf_get {x : List ℕ} {Bv j : ℕ} (hj : j < x.length) :
    (heapOf x Bv)[j]? = some (x.getD j 0, hbF Bv x.length j) := by
  simp [heapOf, hj]

/-- Every suffix of the input list is represented in the forward layout. -/
theorem rep_suffix {x : List ℕ} {Bv : ℕ} (hB : 0 < Bv) (hxB : ∀ v ∈ x, v < Bv) :
    ∀ m j, x.length - j = m → j ≤ x.length →
      Rep Bv (heapOf x Bv) (if j < x.length then Bv + j else 0) (listVal (x.drop j)) := by
  intro m
  induction m with
  | zero =>
    intro j hm hj
    have : x.length ≤ j := by omega
    rw [if_neg (by omega), List.drop_of_length_le this]
    exact Rep.nat hB
  | succ m ih =>
    intro j hm hj
    have hlt : j < x.length := by omega
    rw [if_pos hlt, List.drop_eq_getElem_cons hlt]
    have hxj : x[j] = x.getD j 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
    have hxjB : x[j] < Bv := hxB _ (List.getElem_mem _)
    have := ih (j + 1) (by omega) (by omega)
    have hcell := heapOf_get (x := x) (Bv := Bv) hlt
    show Rep Bv (heapOf x Bv) (Bv + j) (Val.cons (Val.nat x[j]) (listVal (x.drop (j + 1))))
    refine Rep.cons hcell (a := x.getD j 0) (b := hbF Bv x.length j) ?_ ?_
    · rw [← hxj]; exact Rep.nat hxjB
    · unfold hbF
      by_cases h : j + 1 < x.length
      · rw [if_pos h]
        have e : Bv + j + 1 = Bv + (j + 1) := by ring
        rw [e]
        simpa [if_pos h] using this
      · rw [if_neg h]
        simpa [if_neg h] using this

theorem rep_input {x : List ℕ} {Bv : ℕ} (hB : 0 < Bv) (hxB : ∀ v ∈ x, v < Bv) (hx : x ≠ []) :
    Rep Bv (heapOf x Bv) Bv (toVal x) := by
  have hpos : 0 < x.length := List.length_pos_iff.mpr hx
  have := rep_suffix (x := x) hB hxB x.length 0 (by omega) (by omega)
  rw [if_pos hpos, List.drop_zero, Nat.add_zero] at this
  rw [toVal_list]
  exact this

end Lax117284Proofs.Treewidth.Fun.VM.Ram
