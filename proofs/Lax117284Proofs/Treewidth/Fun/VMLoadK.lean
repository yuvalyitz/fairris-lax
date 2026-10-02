import Lax117284Proofs.Treewidth.Fun.VMLoadRead

/-!
# WP V3 (4): the cost bound `K` and the tag bound `B` as IMP+ expressions

The loader cannot receive `Bv` or `K` from outside: the program is fixed before them.  What it *can* do is compute them
from the input, when they are given by a closed formula.  The interface of `compile_solves` therefore fixes

    `K x = c₀ · 2^(c₁ · kw³) · (|x| + c₂)^c₃`     (`KP.k`),     `B x = (maxEntry x + K x + 2)² + 1`     (`bexp`)

with `kw` the parameter entry of the word (`k` or `l`), and the loader evaluates both by a straight-line command:
`kw³` and the exponent by multiplications, `2^e` by one `shiftl`, the power `(|x|+c₂)^c₃` by `c₃` multiplications.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-- The four constants of the cost formula. -/
structure KP where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ

/-- The cost bound `c₀ · 2^(c₁ kw³) · (len + c₂)^c₃`. -/
def KP.k (p : KP) (len kw : ℕ) : ℕ := p.c0 * 2 ^ (p.c1 * kw ^ 3) * (len + p.c2) ^ p.c3

/-- The tag bound: strictly above `(M + K + 2)²`, where `M` bounds the input entries. -/
def bexp (M K : ℕ) : ℕ := (M + K + 2) ^ 2 + 1

/-- `e^n` by `n` multiplications. -/
def pwE (e : Expr) : ℕ → Expr
  | 0 => L 1
  | n + 1 => ml e (pwE e n)

/-- The expression of `KP.k`, over the scalars `len` and `kw`. -/
def kE (p : KP) : Expr :=
  ml (ml (L p.c0) (.bin .shiftl (L 1) (ml (L p.c1) (ml (V "kw") (ml (V "kw") (V "kw"))))))
    (pwE (pl (V "len") (L p.c2)) p.c3)

/-- The expression of `bexp`, over the scalars `M` and `K`. -/
def bE : Expr :=
  pl (ml (pl (pl (V "M") (V "K")) (L 2)) (pl (pl (V "M") (V "K")) (L 2))) (L 1)

theorem pwE_eval {Bi : ℕ} {σ : IEnv} {e : Expr} {v : ℕ} (he : e.evalB Bi σ = some v) (hv : 1 ≤ v) (h1 : 1 < Bi) :
    ∀ n : ℕ, v ^ n < Bi → (pwE e n).evalB Bi σ = some (v ^ n) := by
  intro n
  induction n with
  | zero => intro _; simpa [pwE] using RunStep.eval_lit Bi 1 σ h1
  | succ n ih =>
    intro h
    have hle : v ^ n ≤ v ^ (n + 1) := Nat.pow_le_pow_right hv (by omega)
    have := RunStep.eval_mul Bi σ e (pwE e n) v (v ^ n) he (ih (by omega)) (by rw [← pow_succ']; exact h)
    rw [← pow_succ'] at this
    exact this

/-- The evaluation of `kE`: every subterm value stays below `K`. -/
theorem kE_eval {Bi : ℕ} {σ : IEnv} (p : KP) (h0 : 1 ≤ p.c0) (h1 : 1 ≤ p.c1) (h2 : 1 ≤ p.c2)
    {len kw : ℕ} (hlen : σ.vars "len" = len) (hkw : σ.vars "kw" = kw)
    (hc1 : p.c1 < Bi) (hlB : len + p.c2 < Bi) (hkwB : kw < Bi) (hK : p.k len kw < Bi) :
    (kE p).evalB Bi σ = some (p.k len kw) := by
  have hBi : 1 < Bi := by
    unfold KP.k at hK
    have a1 : 1 ≤ 2 ^ (p.c1 * kw ^ 3) := Nat.one_le_two_pow
    have a2 : 1 ≤ (len + p.c2) ^ p.c3 := Nat.one_le_pow p.c3 (len + p.c2) (by omega)
    have a3 := Nat.mul_le_mul h0 (Nat.mul_le_mul a1 a2)
    have a4 : p.c0 * (2 ^ (p.c1 * kw ^ 3) * (len + p.c2) ^ p.c3) = p.c0 * 2 ^ (p.c1 * kw ^ 3) * (len + p.c2) ^ p.c3 := by ring
    omega
  -- the quantities
  set s2 := kw * kw with hs2
  set s3 := kw * s2 with hs3
  set e := p.c1 * s3 with he
  have hs3e : s3 = kw ^ 3 := by rw [hs3, hs2]; ring
  have he' : e = p.c1 * kw ^ 3 := by rw [he, hs3e]
  have hP1 : 1 ≤ (len + p.c2) ^ p.c3 := Nat.one_le_pow _ _ (by omega)
  have h2e : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hU : 2 ^ e ≤ p.c0 * 2 ^ e := Nat.le_mul_of_pos_left _ (by omega)
  have hK' : p.k len kw = p.c0 * 2 ^ e * (len + p.c2) ^ p.c3 := by rw [KP.k, he']
  have hKU : p.c0 * 2 ^ e ≤ p.k len kw := by rw [hK']; exact Nat.le_mul_of_pos_right _ (by omega)
  have h1U : 1 ≤ p.c0 * 2 ^ e := by omega
  have hKP : (len + p.c2) ^ p.c3 ≤ p.k len kw := by
    rw [hK']; exact Nat.le_mul_of_pos_left _ (by omega)
  have hes : e < 2 ^ e := Nat.lt_two_pow_self
  have hs3e' : s3 ≤ e := by rw [he]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hs2s3 : s2 ≤ s3 := by
    rcases Nat.eq_zero_or_pos kw with h | h
    · rw [hs2, h]; simp
    · rw [hs3]; exact Nat.le_mul_of_pos_left _ h
  have hbig : e < Bi := by omega
  have hsh : 1 * 2 ^ e < Bi := by rw [one_mul]; omega
  have hmid : p.c0 * (1 * 2 ^ e) < Bi := by rw [one_mul]; omega
  have hfin : p.c0 * (1 * 2 ^ e) * (len + p.c2) ^ p.c3 < Bi := by rw [one_mul, ← hK']; exact hK
  have hc0le : p.c0 ≤ p.c0 * 2 ^ e := Nat.le_mul_of_pos_right _ (by omega)
  have hc0B : p.c0 < Bi := by omega
  have hvkw : (Expr.var "kw").evalB Bi σ = some kw := by rw [← hkw]; exact RunStep.eval_var Bi σ "kw" (by omega)
  have hvlen : (Expr.var "len").evalB Bi σ = some len := by
    rw [← hlen]; exact RunStep.eval_var Bi σ "len" (by omega)
  have e2 : (ml (V "kw") (V "kw")).evalB Bi σ = some s2 :=
    RunStep.eval_mul Bi σ _ _ kw kw hvkw hvkw (by omega)
  have e3 : (ml (V "kw") (ml (V "kw") (V "kw"))).evalB Bi σ = some s3 :=
    RunStep.eval_mul Bi σ _ _ kw s2 hvkw e2 (by omega)
  have ee : (ml (L p.c1) (ml (V "kw") (ml (V "kw") (V "kw")))).evalB Bi σ = some e :=
    RunStep.eval_mul Bi σ _ _ p.c1 s3 (RunStep.eval_lit Bi _ σ hc1) e3 (by omega)
  have esh : (Expr.bin .shiftl (L 1) (ml (L p.c1) (ml (V "kw") (ml (V "kw") (V "kw"))))).evalB Bi σ
      = some (1 * 2 ^ e) :=
    RunStep.eval_shiftl Bi σ _ _ 1 e (RunStep.eval_lit Bi 1 σ hBi) ee hsh
  have eu : (ml (L p.c0) (.bin .shiftl (L 1) (ml (L p.c1) (ml (V "kw") (ml (V "kw") (V "kw")))))).evalB Bi σ
      = some (p.c0 * (1 * 2 ^ e)) :=
    RunStep.eval_mul Bi σ _ _ p.c0 (1 * 2 ^ e) (RunStep.eval_lit Bi _ σ hc0B) esh hmid
  have ebase : (pl (V "len") (L p.c2)).evalB Bi σ = some (len + p.c2) :=
    RunStep.eval_add Bi σ _ _ len p.c2 hvlen (RunStep.eval_lit Bi _ σ (by omega)) hlB
  have ep := pwE_eval ebase (by omega) hBi p.c3 (by omega)
  have := RunStep.eval_mul Bi σ _ _ _ _ eu ep hfin
  have h' : p.k len kw = p.c0 * (1 * 2 ^ e) * (len + p.c2) ^ p.c3 := by rw [one_mul]; exact hK'
  unfold kE
  rw [h']
  exact this

end Lax117284Proofs.Treewidth.Fun.VM.Ram

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-- `len := i`; `kw := HA[HA[0]² + off]`; `K := kE`; `B := bE`. -/
def setKB (off : ℕ) (p : KP) : Com :=
  .seq (.assign "len" (V "i"))
    (.seq (.assign "kw" (G "HA" (pl (ml (G "HA" (L 0)) (G "HA" (L 0))) (L off))))
      (.seq (.assign "K" (kE p)) (.assign "B" bE)))

/-- The scalars set by `setKB`, as one environment. -/
def afterKB (x : List ℕ) (off : ℕ) (p : KP) (σ : IEnv) : IEnv :=
  (((σ.setVar "len" x.length).setVar "kw" (x.getD (x.getD 0 0 * x.getD 0 0 + off) 0)).setVar "K"
    (p.k x.length (x.getD (x.getD 0 0 * x.getD 0 0 + off) 0))).setVar "B"
    (bexp (wordMax x) (p.k x.length (x.getD (x.getD 0 0 * x.getD 0 0 + off) 0)))

theorem bE_size : bE.size = 13 := by simp [bE]

theorem setKB_run {x : List ℕ} {A Bi off : ℕ} (p : KP) (h0 : 1 ≤ p.c0) (h1 : 1 ≤ p.c1) (h2 : 1 ≤ p.c2)
    (hA : x.length ≤ A) (hxB : ∀ v ∈ x, v < Bi) (hidx : x.getD 0 0 * x.getD 0 0 + off < x.length)
    (hc1 : p.c1 < Bi) (hlB : x.length + p.c2 < Bi)
    (hK : p.k x.length (x.getD (x.getD 0 0 * x.getD 0 0 + off) 0) < Bi)
    (hB : bexp (wordMax x) (p.k x.length (x.getD (x.getD 0 0 * x.getD 0 0 + off) 0)) < Bi)
    {σ : IEnv} (hi : σ.vars "i" = x.length) (hha : σ.arrs "HA" = arrOf A (fun j => x.getD j 0))
    (hM : σ.vars "M" = wordMax x) :
    Run Bi (setKB off p) σ (afterKB x off p σ) ((kE p).size + 40) := by
  set n := x.getD 0 0 with hn
  set kwv := x.getD (n * n + off) 0 with hkwv
  set Kv := p.k x.length kwv with hKv
  have hBi : 0 < Bi := by omega
  have hlenA : (σ.arrs "HA").length = A := by rw [hha]; simp
  have hnB : n < Bi := getD_lt hBi hxB 0
  have hkwB : kwv < Bi := getD_lt hBi hxB _
  -- step 1
  have r1 : Run Bi (.assign "len" (V "i")) σ (σ.setVar "len" x.length) 2 := by
    have := Run.assign (B := Bi) (x := "len") (e := V "i") (v := x.length)
      (by rw [← hi]; exact RunStep.eval_var Bi σ "i" (by omega))
    simpa using this.mono (by simp)
  set σ1 := σ.setVar "len" x.length with hσ1
  -- step 2
  have hσ1i : σ1.vars "i" = x.length := by simp [hσ1, hi]
  have hσ1a : σ1.arrs "HA" = arrOf A (fun j => x.getD j 0) := by simp [hσ1, hha]
  have hg0 : (G "HA" (L 0)).evalB Bi σ1 = some n := by
    have := RunStep.eval_get Bi σ1 "HA" (L 0) 0 (RunStep.eval_lit Bi 0 σ1 (by omega))
      (by rw [hσ1a]; simp; omega) (by rw [hσ1a, getD_arrOf _ (by omega)]; exact hnB)
    rw [hσ1a, getD_arrOf _ (by omega)] at this
    exact this
  have hsq : (ml (G "HA" (L 0)) (G "HA" (L 0))).evalB Bi σ1 = some (n * n) :=
    RunStep.eval_mul Bi σ1 _ _ n n hg0 hg0 (by omega)
  have hpl : (pl (ml (G "HA" (L 0)) (G "HA" (L 0))) (L off)).evalB Bi σ1 = some (n * n + off) :=
    RunStep.eval_add Bi σ1 _ _ (n * n) off hsq (RunStep.eval_lit Bi off σ1 (by omega)) (by omega)
  have hgk : (G "HA" (pl (ml (G "HA" (L 0)) (G "HA" (L 0))) (L off))).evalB Bi σ1 = some kwv := by
    have := RunStep.eval_get Bi σ1 "HA" _ (n * n + off) hpl
      (by rw [hσ1a]; simp; omega) (by rw [hσ1a, getD_arrOf _ (by omega)]; exact hkwB)
    rw [hσ1a, getD_arrOf _ (by omega)] at this
    exact this
  have r2 : Run Bi (.assign "kw" (G "HA" (pl (ml (G "HA" (L 0)) (G "HA" (L 0))) (L off)))) σ1
      (σ1.setVar "kw" kwv) 9 := by
    have := Run.assign (B := Bi) (x := "kw") hgk
    exact this.mono (by simp)
  set σ2 := σ1.setVar "kw" kwv with hσ2
  -- step 3
  have hσ2l : σ2.vars "len" = x.length := by simp [hσ2, hσ1]
  have hσ2k : σ2.vars "kw" = kwv := by simp [hσ2]
  have r3 : Run Bi (.assign "K" (kE p)) σ2 (σ2.setVar "K" Kv) ((kE p).size + 1) := by
    have := Run.assign (B := Bi) (x := "K") (kE_eval (σ := σ2) p h0 h1 h2 hσ2l hσ2k hc1 hlB hkwB hK)
    exact this.mono (by omega)
  set σ3 := σ2.setVar "K" Kv with hσ3
  -- step 4
  have hσ3M : σ3.vars "M" = wordMax x := by simp [hσ3, hσ2, hσ1, hM]
  have hσ3K : σ3.vars "K" = Kv := by simp [hσ3]
  have hMB : wordMax x < Bi := wordMax_lt hBi hxB
  have hKb : Kv < bexp (wordMax x) Kv := by
    unfold bexp; nlinarith [Nat.zero_le (wordMax x)]
  have hMK : wordMax x + Kv + 2 ≤ (wordMax x + Kv + 2) ^ 2 := by nlinarith [Nat.zero_le (wordMax x + Kv)]
  have hb1 : (pl (V "M") (V "K")).evalB Bi σ3 = some (wordMax x + Kv) :=
    RunStep.eval_add Bi σ3 _ _ _ _ (by rw [← hσ3M]; exact RunStep.eval_var Bi σ3 "M" (by omega))
      (by rw [← hσ3K]; exact RunStep.eval_var Bi σ3 "K" (by omega)) (by unfold bexp at hB; omega)
  have hb2 : (pl (pl (V "M") (V "K")) (L 2)).evalB Bi σ3 = some (wordMax x + Kv + 2) :=
    RunStep.eval_add Bi σ3 _ _ _ 2 hb1 (RunStep.eval_lit Bi 2 σ3 (by unfold bexp at hB; omega))
      (by unfold bexp at hB; omega)
  have hb3 : (ml (pl (pl (V "M") (V "K")) (L 2)) (pl (pl (V "M") (V "K")) (L 2))).evalB Bi σ3
      = some ((wordMax x + Kv + 2) * (wordMax x + Kv + 2)) :=
    RunStep.eval_mul Bi σ3 _ _ _ _ hb2 hb2 (by unfold bexp at hB; rw [← pow_two]; omega)
  have hb4 : bE.evalB Bi σ3 = some (bexp (wordMax x) Kv) := by
    have := RunStep.eval_add Bi σ3 _ _ _ 1 hb3 (RunStep.eval_lit Bi 1 σ3 (by unfold bexp at hB; omega)) (by
      unfold bexp at hB; rw [← pow_two]; omega)
    unfold bE bexp
    rw [← pow_two] at this
    exact this
  have r4 : Run Bi (.assign "B" bE) σ3 (σ3.setVar "B" (bexp (wordMax x) Kv)) 14 := by
    have := Run.assign (B := Bi) (x := "B") hb4
    exact this.mono (by rw [bE_size])
  unfold setKB afterKB
  exact (r1.seq (r2.seq (r3.seq r4))).mono (by omega)

end Lax117284Proofs.Treewidth.Fun.VM.Ram
