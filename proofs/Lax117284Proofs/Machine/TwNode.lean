import Lax117284Proofs.Machine.TwFill
import Lax117284Proofs.Theorem4TwList

/-!
The dynamic program over the decomposition word, in IMP+: what the arrays hold after the first `i`
nodes have been processed, and the arithmetic the cell computations use.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

lemma land_mask (e k : ℕ) : Nat.land e (2 ^ k - 1) = e % 2 ^ k :=
  Nat.and_two_pow_sub_one_eq_mod e k

lemma pow_step (m p : ℕ) : (2 ^ m) ^ p * 2 ^ m = 2 ^ (m * (p + 1)) := by
  rw [← pow_mul, ← pow_add, mul_add, mul_one]

/-- The digit-shift form of `rmN`. -/
lemma rmN_shift (m p e : ℕ) :
    rmN (2 ^ m) p e = Nat.land e (2 ^ (m * p) - 1) + e / 2 ^ (m * (p + 1)) * 2 ^ (m * p) := by
  unfold rmN
  rw [land_mask, pow_step, ← pow_mul]

/-- The digit-shift form of `insN`. -/
lemma insN_shift (m p S e : ℕ) :
    insN (2 ^ m) p S e =
      Nat.land e (2 ^ (m * p) - 1) + S * 2 ^ (m * p) + e / 2 ^ (m * p) * 2 ^ (m * (p + 1)) := by
  unfold insN
  rw [land_mask, pow_step, ← pow_mul]

/-- The table entry of a restriction in the table of a node, as a number. -/
noncomputable def tbv (I : Lax117284.Scheduling.Instance) (kk : ℕ) (D : List ℕ) (j e : ℕ) : ℕ := by
  classical exact if TB I kk D j e then 1 else 0

variable (I : Lax117284.Scheduling.Instance) (kk : ℕ) (D : List ℕ) (w1 Tm : ℕ)

/-- **What the arrays hold after the first `i0` nodes have been processed**: the size, the sorted
bag and the table of each of them. -/
structure NI (i0 : ℕ) (σ : Env) : Prop where
  sz : ∀ j < i0, (σ.arrs "SZ").getD j 0 = (bagL D j).length
  bg : ∀ j < i0, ∀ t < (bagL D j).length,
    (σ.arrs "BG").getD (j * w1 + t) 0 = (bagL D j)[t]!
  tb : ∀ j < i0, ∀ e < (2 ^ I.days) ^ (bagL D j).length,
    (σ.arrs "TB").getD (j * Tm + e) 0 = tbv I kk D j e

variable {I kk D w1 Tm}

lemma row_lt {j i e T : ℕ} (hj : j < i) (he : e < T) : j * T + e < i * T := by
  have : (j + 1) * T ≤ i * T := Nat.mul_le_mul_right T hj
  rw [Nat.succ_mul] at this; omega

/-- What a fill left in an array, as a description of the array. -/
def RowDesc (arr : String) (bs N : ℕ) (g : ℕ → ℕ) (σ0 σ : Env) : Prop :=
  ∀ k, (σ.arrs arr).getD k 0 =
    if bs ≤ k ∧ k < bs + N then g (k - bs) else (σ0.arrs arr).getD k 0

/-- **The step of the invariant**: once the size, the bag and the table of node `i` have been
written, the arrays describe the first `i + 1` nodes. -/
theorem NI_next {i : ℕ} {σ0 σ : Env} (hσ0 : NI I kk D w1 Tm i σ0)
    (hw : ∀ j, j < i + 1 → (bagL D j).length ≤ w1) (hTm : ∀ s ≤ w1, (2 ^ I.days) ^ s ≤ Tm)
    (sz : RowDesc "SZ" i 1 (fun _ => (bagL D i).length) σ0 σ)
    (bg : RowDesc "BG" (i * w1) (bagL D i).length (fun t => (bagL D i)[t]!) σ0 σ)
    (tb : RowDesc "TB" (i * Tm) ((2 ^ I.days) ^ (bagL D i).length) (fun e => tbv I kk D i e) σ0 σ) :
    NI I kk D w1 Tm (i + 1) σ := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [sz j]
    by_cases hji : j = i
    · subst hji; simp
    · have : j < i := by omega
      rw [if_neg (by omega)]; exact hσ0.sz j this
  · intro j hj t ht
    rw [bg (j * w1 + t)]
    by_cases hji : j = i
    · subst hji
      rw [if_pos (by omega)]; congr 1; omega
    · have hj' : j < i := by omega
      have := row_lt (T := w1) (j := j) (i := i) (e := t) hj' (lt_of_lt_of_le ht (hw j (by omega)))
      rw [if_neg (by omega)]
      exact hσ0.bg j hj' t ht
  · intro j hj e he
    rw [tb (j * Tm + e)]
    by_cases hji : j = i
    · subst hji
      rw [if_pos (by omega)]; congr 1; omega
    · have hj' : j < i := by omega
      have hlt : e < Tm := lt_of_lt_of_le he (hTm _ (hw j (by omega)))
      have := row_lt (T := Tm) (j := j) (i := i) (e := e) hj' hlt
      rw [if_neg (by omega)]
      exact hσ0.tb j hj' e he

/-! ### Leaves -/

/-- Normalize reads of updated environments, arrays included. -/
macro "nrmA" : tactic => `(tactic| simp only [vars_setVar, arrs_setVar, inp_setVar, out_setVar,
  vars_setArr, arrs_setArr, length_arrs_setArr, ↓reduceIte, String.reduceEq, eq_self])

variable {B : ℕ}

/-- A leaf: the bag is empty and the table holds the one restriction. -/
def leafCom : Com :=
  .seq (.store "SZ" (V "i") (L 0)) (.seq (.assign "tbs" (mul (V "i") (V "Tm")))
    (.store "TB" (V "tbs") (L 1)))

theorem leafCom_run {i : ℕ} {σ : Env} (hi : σ.vars "i" = i)
    (hTm : σ.vars "Tm" = Tm) (hSZ : i < (σ.arrs "SZ").length)
    (hTB : i * Tm < (σ.arrs "TB").length) (hB : i * Tm + Tm + 4 < B) (hB2 : i + 4 < B) :
    ∃ σ', Run B leafCom σ σ' 40 ∧
      σ' = ((σ.setArr "SZ" i 0).setVar "tbs" (i * Tm)).setArr "TB" (i * Tm) 1 := by
  unfold leafCom
  run_vcg
  all_goals try (nrmA; rw [hi, hTm]; omega)
  all_goals try (rw [hi]; omega)
  nrmA
  rw [hi, hTm]

/-! ### Reading the record of a node and finding the position -/

/-- The record of node `i` and the size of its child's bag. -/
def recCom : Com := seqs
  [ .assign "c" (sub (V "i") (L 1)),
    .assign "vx" (G "O" (add (L 3) (mul (L 3) (V "i")))),
    .assign "ot" (G "O" (add (L 4) (mul (L 3) (V "i")))),
    .assign "s" (G "SZ" (V "c")),
    .assign "cw" (mul (V "c") (V "w1")),
    .assign "p" (L 0) ]

/-- The body of the count of the entries of the child's bag below `vx`. -/
def posBody : Com :=
  .ite (.lt (G "BG" (add (V "cw") (V "pt"))) (V "vx")) (.assign "p" (add (V "p") (L 1))) .skip

/-- The count of the entries of the child's bag below `vx`. -/
def posLoop : Com := fLoop "pt" "s" posBody

/-- The scalars the reading of the record writes. -/
def SR : List String := ["c", "vx", "ot", "s", "cw", "p"]

theorem recCom_run {σ : Env} {i N : ℕ} (hi : σ.vars "i" = i) (hiN : i < N)
    (hSZ : N ≤ (σ.arrs "SZ").length) (hO : 3 * i + 5 ≤ (σ.arrs "O").length)
    (hO3 : (σ.arrs "O").getD (3 + 3 * i) 0 < B) (hO4 : (σ.arrs "O").getD (4 + 3 * i) 0 < B)
    (hSc : (σ.arrs "SZ").getD (i - 1) 0 < B)
    (hB : 3 * N + 16 < B) (hcw : (i - 1) * σ.vars "w1" + 8 < B) (hw1 : σ.vars "w1" + 8 < B) :
    ∃ σ', Run B recCom σ σ' 60 ∧ σ'.vars "c" = i - 1 ∧
      σ'.vars "vx" = (σ.arrs "O").getD (3 + 3 * i) 0 ∧
      σ'.vars "ot" = (σ.arrs "O").getD (4 + 3 * i) 0 ∧
      σ'.vars "s" = (σ.arrs "SZ").getD (i - 1) 0 ∧
      σ'.vars "cw" = (i - 1) * σ.vars "w1" ∧ σ'.vars "p" = 0 ∧
      Agr SR σ σ' ∧ σ'.out = σ.out := by
  unfold recCom seqs
  run_vcg
  all_goals try (nrmA; rw [hi]; omega)
  all_goals try (nrmA; rw [hi]; first | exact hO3 | exact hO4)
  all_goals try (nrmA; first | exact hO3 | exact hO4)
  all_goals try (nrmA; rw [hi]; exact hSc)
  all_goals try omega
  all_goals (try nrmA)
  rw [hi]
  refine ⟨rfl, rfl, rfl, rfl, rfl, trivial, ⟨rfl, ?_⟩, trivial⟩
  intro y hy
  simp only [SR, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2]

theorem posBody_run (σ : Env) (hlt : σ.vars "cw" + σ.vars "pt" < (σ.arrs "BG").length)
    (hBG : (σ.arrs "BG").getD (σ.vars "cw" + σ.vars "pt") 0 < B) (hvx : σ.vars "vx" < B)
    (hp : σ.vars "p" + 2 < B) (hcw : σ.vars "cw" + σ.vars "pt" < B) :
    ∃ σ', Run B posBody σ σ' 20 ∧
      σ'.vars "p" = σ.vars "p" +
        (if (σ.arrs "BG").getD (σ.vars "cw" + σ.vars "pt") 0 < σ.vars "vx" then 1 else 0) ∧
      Agr ["p"] σ σ' ∧ σ'.vars "pt" = σ.vars "pt" ∧ σ'.out = σ.out := by
  unfold posBody
  run_vcg
  · refine ⟨?_, agr_set (by simp) _, ?_, rfl⟩
    · rw [if_pos (by omega)]; nrmA
    · nrmA
  · refine ⟨?_, Agr.refl _ _, rfl, rfl⟩
    rw [if_neg (by omega)]; rfl

theorem posLoop_run {σ0 : Env} {f : ℕ → ℕ} {s0 cw0 : ℕ} (hs : σ0.vars "s" = s0)
    (hcw : σ0.vars "cw" = cw0) (hp0 : σ0.vars "p" = 0)
    (hrow : ∀ t < s0, (σ0.arrs "BG").getD (cw0 + t) 0 = f t)
    (hlen : cw0 + s0 ≤ (σ0.arrs "BG").length) (hfB : ∀ t, f t < B) (hvx : σ0.vars "vx" < B)
    (hB : cw0 + s0 + s0 + 8 < B) :
    ∃ σ', Run B posLoop σ0 σ' ((20 + 10 + 4) * s0 + 6) ∧
      σ'.vars "p" = ∑ t ∈ Finset.range s0, (if f t < σ0.vars "vx" then 1 else 0) ∧
      Agr ["pt", "p"] σ0 σ' ∧ σ'.out = σ0.out := by
  have hf := fLoop_spec (B := B) "pt" "s" "p" posBody ["pt", "p"]
    (fun t a => a + (if f t < σ0.vars "vx" then 1 else 0)) (fun j a => a ≤ j) 20 s0 σ0
    (by simp) (by simp) (by decide) hs (by omega) (by rw [hp0])
    (fun j a h => by split_ifs <;> omega) (by
      intro σ hA hlt hQ
      have hfr : ∀ y, y ∉ ["pt", "p"] → σ.vars y = σ0.vars y := hA.2
      have e1 : σ.vars "cw" = cw0 := by rw [hfr "cw" (by simp), hcw]
      have e2 : σ.vars "vx" = σ0.vars "vx" := hfr "vx" (by simp)
      have e3 : (σ.arrs "BG") = σ0.arrs "BG" := by rw [hA.1]
      have hq : σ.vars "p" ≤ σ.vars "pt" := hQ
      have hrow' := hrow (σ.vars "pt") hlt
      obtain ⟨σ', r, hv, hA', h2', ho'⟩ := posBody_run σ (by rw [e1, e3]; omega)
        (by rw [e1, e3, hrow']; exact hfB _) (by rw [e2]; exact hvx) (by omega) (by rw [e1]; omega)
      refine ⟨σ', r, ?_, agr_comp (S := ["pt", "p"]) hA hA' (by intro x hx; exact hx)
        (by intro x hx; simp at hx ⊢; tauto), h2', ho'⟩
      rw [hv, e1, e3, hrow', e2])
  obtain ⟨σ', r, hv, hA, ho⟩ := hf
  refine ⟨σ', r, ?_, hA, ho⟩
  rw [hv, Lax117284Proofs.TwViol.foldl_add_range, hp0]
  simp

/-! ### The parameters and the context of the program -/

set_option genSizeOfSpec false in
set_option genInjectivity false in
open Lax117284.InstanceEncoding in
/-- The data a run of the dynamic program is about: an instance with its word, the fairness
parameter, and a nice tree decomposition of its overall conflict graph in the word `D`. -/
structure Params where
  I : Lax117284.Scheduling.Instance
  y : List ℕ
  kk : ℕ
  D : List ℕ
  w : ℕ
  hy : Lax117284.InstanceEncoding.EncodesInstance y I
  hD : NiceDecomposition I w D

namespace Params

variable (P : Params)

/-- The number of clients. -/
def n : ℕ := P.I.clients
/-- The number of days. -/
def m : ℕ := P.I.days
/-- The number of nodes. -/
def N : ℕ := nodeCount P.D
/-- The largest size of a bag. -/
def wid : ℕ := P.w + 1
/-- The base of the digits. -/
def bs : ℕ := 2 ^ P.m
/-- The number of restrictions to a bag of the largest size. -/
def tabs : ℕ := P.bs ^ P.wid

end Params

/-! ### The context of the node programs -/

variable (P : Params)

/-- **Everything the node programs know about the environment** apart from the arrays they fill:
the constants, the instance word, the decomposition word, the sizes of the arrays and the bounds. -/
structure NC (B : ℕ) (σ : Env) : Prop where
  n_ : σ.vars "n" = P.n
  m_ : σ.vars "m" = P.m
  kk_ : σ.vars "kk" = P.kk
  w1_ : σ.vars "w1" = P.wid
  Tm_ : σ.vars "Tm" = P.tabs
  mask_ : σ.vars "mask" = 2 ^ P.m - 1
  bb_ : σ.vars "bb" = 2 ^ P.m
  mn_ : σ.vars "mn" = P.m * P.n
  N_ : σ.vars "N" = P.N
  Xy : ∀ j < P.y.length, (σ.arrs "X").getD j 0 = P.y.getD j 0
  lenX : P.y.length + 1 ≤ (σ.arrs "X").length
  XB : ∀ v ∈ σ.arrs "X", v < B
  O_ : ∀ k < P.D.length, (σ.arrs "O").getD (k + 1) 0 = P.D.getD k 0
  OB : ∀ k < P.D.length, (σ.arrs "O").getD (k + 1) 0 < B
  lenO : 3 * P.N + 5 ≤ (σ.arrs "O").length
  lenSZ : P.N ≤ (σ.arrs "SZ").length
  lenBG : P.N * P.wid ≤ (σ.arrs "BG").length
  lenTB : P.N * P.tabs ≤ (σ.arrs "TB").length
  b1 : P.N * P.tabs + P.tabs + 32 < B
  b2 : P.N * P.wid + P.wid + 32 < B
  b3 : 3 * P.N + 32 < B
  b4 : P.tabs * P.bs + 32 < B
  b5 : P.wid * (P.wid * P.m + 1) + P.wid * P.m + P.m + 32 < B
  b6 : (σ.arrs "X").length + 32 < B
  b7 : (σ.arrs "O").length + 32 < B
  b8 : P.n + P.m + P.kk + 32 < B
  b9 : P.m * (P.wid + 1) + P.wid + 32 < B
  b10 : 2 ^ P.m + 32 < B

variable {P}

lemma NC.O_lt {B : ℕ} {σ : Env} (h : NC P B σ) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ P.D.length) :
    (σ.arrs "O").getD j 0 < B := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact h.OB k (by omega)

/-- The constants of the context survive a run that keeps them and the arrays' sizes. -/
lemma NC.transfer {B : ℕ} {σ0 σ : Env} (h : NC P B σ0)
    (hv : ∀ y ∈ ["n", "m", "kk", "w1", "Tm", "mask", "bb", "mn", "N"], σ.vars y = σ0.vars y)
    (hX : σ.arrs "X" = σ0.arrs "X") (hO : σ.arrs "O" = σ0.arrs "O")
    (hSZ : (σ.arrs "SZ").length = (σ0.arrs "SZ").length)
    (hBG : (σ.arrs "BG").length = (σ0.arrs "BG").length)
    (hTB : (σ.arrs "TB").length = (σ0.arrs "TB").length) : NC P B σ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.b1, h.b2, h.b3, h.b4,
    h.b5, ?_, ?_, h.b8, h.b9, h.b10⟩
  · rw [hv "n" (by simp)]; exact h.n_
  · rw [hv "m" (by simp)]; exact h.m_
  · rw [hv "kk" (by simp)]; exact h.kk_
  · rw [hv "w1" (by simp)]; exact h.w1_
  · rw [hv "Tm" (by simp)]; exact h.Tm_
  · rw [hv "mask" (by simp)]; exact h.mask_
  · rw [hv "bb" (by simp)]; exact h.bb_
  · rw [hv "mn" (by simp)]; exact h.mn_
  · rw [hv "N" (by simp)]; exact h.N_
  · rw [hX]; exact h.Xy
  · rw [hX]; exact h.lenX
  · rw [hX]; exact h.XB
  · rw [hO]; exact h.O_
  · rw [hO]; exact h.OB
  · rw [hO]; exact h.lenO
  · rw [hSZ]; exact h.lenSZ
  · rw [hBG]; exact h.lenBG
  · rw [hTB]; exact h.lenTB
  · rw [hX]; exact h.b6
  · rw [hO]; exact h.b7

end Lax117284Proofs.Machine.TwNode
