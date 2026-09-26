import Lax117284Proofs.IlpClients.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

/-!
# The family of integer programs of the reduction

A self-contained restatement (nothing of `fairris-lax` is imported) of the integer programs that
the reduction of the clients problem produces: for `n` clients, `nT n = 2^(n*n)` types,
`nZ n = 2^n` subsets, `nV n` pair columns `(t, s)`, `nN n = nV n + n` variables (the pairs and one
slack per client), `nM n = nT n + n` constraints (a row per type, a row per client).

The definitions `nT … coef`, `zFunRaw`, `zList` restate `ClientsILPRaw.lean` of `fairris-lax`
(`coefRaw`, `zFunRaw`, `zList`) formula by formula; `decodeILP` restates `Lax117284.IlpClients.decodeILP`.
`ilpWord n cnt B` is `zList n m k cnt` with the number `B = m - k` of days a client may go unserved
(`zList_eq_ilpWord`).
-/

namespace Lax117284Proofs.IlpClients

open Finset

/-- The number of day types, `2 ^ (n * n)`. -/
def nT (n : ℕ) : ℕ := 2 ^ (n * n)
/-- The number of subsets of the clients, `2 ^ n`. -/
def nZ (n : ℕ) : ℕ := 2 ^ n
/-- The number of pairs (type, subset). -/
def nV (n : ℕ) : ℕ := nT n * nZ n
/-- The number of variables: the pairs and one slack variable per client. -/
def nN (n : ℕ) : ℕ := nV n + n
/-- The number of constraints: one per type and one per client. -/
def nM (n : ℕ) : ℕ := nT n + n

/-- The subset `S` (a number) is independent for the type `t` (a number). -/
def indepB (n t S : ℕ) : Bool :=
  decide (∀ a < n, ∀ b < n, a ≠ b → S.testBit a = true → S.testBit b = true →
    t.testBit (a * n + b) = false)

/-- The coefficient of variable `c` in constraint `r`. -/
def coef (n r c : ℕ) : ℕ :=
  if c < nV n then
    (if indepB n (c / nZ n) (c % nZ n) then
      (if r < nT n then (if c / nZ n = r then 1 else 0)
       else (if (c % nZ n).testBit (r - nT n) = false then 1 else 0))
     else 0)
  else (if nT n ≤ r ∧ c - nV n = r - nT n then 1 else 0)

/-- The number of entries of the word of the program. -/
def zLen (n : ℕ) : ℕ := 2 + nM n * nN n + nM n

/-- The right-hand side of constraint `r`: `cnt r` days of type `r`, and `B` unserved days allowed
to each client. -/
def rhs (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) (r : ℕ) : ℕ := if r < nT n then cnt r else B

/-- The right-hand side of constraint `r` in the reduction of `fairris-lax`
(`ClientsILPRaw.rhsRaw`, restated): `B = m - k`. -/
def rhsRaw (n m k : ℕ) (cnt : ℕ → ℕ) (r : ℕ) : ℕ := if r < nT n then cnt r else m - k

/-- The entry `idx` of the word of the program. -/
def wordFun (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) (idx : ℕ) : ℕ :=
  if idx = 0 then nN n else if idx = 1 then nM n
  else if idx < 2 + nM n * nN n then coef n ((idx - 2) / nN n) ((idx - 2) % nN n)
  else rhs n cnt B (idx - 2 - nM n * nN n)

/-- **The word of the integer program** of `n` clients, `cnt r` days of type `r`, and `B`. -/
def ilpWord (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) : List ℕ := (List.range (zLen n)).map (wordFun n cnt B)

/-- The word, the other way: the two counts, the coefficients row by row, the right-hand sides. -/
theorem ilpWord_eq_append (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) :
    ilpWord n cnt B = [nN n, nM n] ++
      (List.range (nM n * nN n)).map (fun i => coef n (i / nN n) (i % nN n)) ++
      (List.range (nM n)).map (fun r => if r < nT n then cnt r else B) := by
  apply List.ext_getElem
  · simp [ilpWord, zLen]; omega
  · intro i h1 h2
    have hi : i < zLen n := by simpa [ilpWord] using h1
    simp only [ilpWord, List.getElem_map, List.getElem_range, wordFun]
    by_cases h0 : i = 0
    · subst h0; simp
    by_cases h1' : i = 1
    · subst h1'; simp
    have hcases : i < 2 + nM n * nN n ∨ 2 + nM n * nN n ≤ i := by omega
    rw [if_neg h0, if_neg h1']
    rcases hcases with h | h
    · rw [if_pos h]
      rw [List.getElem_append_left (by simp [List.length_append]; omega)]
      rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_cons, List.length_nil, List.getElem_map, List.getElem_range]
    · rw [if_neg (by omega)]
      rw [List.getElem_append_right (by simp [List.length_append]; omega)]
      have hl : ([nN n, nM n] ++
          (List.range (nM n * nN n)).map (fun i => coef n (i / nN n) (i % nN n))).length =
          2 + nM n * nN n := by simp; omega
      simp only [List.getElem_map, List.getElem_range, rhs, hl]
      have e : i - 2 - nM n * nN n = i - (2 + nM n * nN n) := by omega
      rw [e]

/-- The integer program of a word (a restatement of `Lax117284.IlpClients.ILP`). -/
structure ILP where
  /-- The number of variables. -/
  N : ℕ
  /-- The number of constraints. -/
  M : ℕ
  /-- The coefficient of variable `i` in constraint `j`. -/
  a : Fin M → Fin N → ℕ
  /-- The right-hand side of constraint `j`. -/
  b : Fin M → ℕ

/-- **`E` is feasible.** -/
def ILP.Feasible (E : ILP) : Prop := ∃ x : Fin E.N → ℕ, ∀ j, ∑ i, E.a j i * x i = E.b j

/-- The integer program of a word (a restatement of `Lax117284.IlpClients.decodeILP`). -/
def decodeILP (w : List ℕ) : ILP where
  N := w.getD 0 0
  M := w.getD 1 0
  a := fun j i => w.getD (2 + j.val * w.getD 0 0 + i.val) 0
  b := fun j => w.getD (2 + w.getD 1 0 * w.getD 0 0 + j.val) 0

theorem nT_pos (n : ℕ) : 0 < nT n := Nat.two_pow_pos _
theorem nZ_pos (n : ℕ) : 0 < nZ n := Nat.two_pow_pos _
theorem nN_pos (n : ℕ) : 0 < nN n := by
  have := Nat.mul_pos (nT_pos n) (nZ_pos n); simp only [nN, nV]; omega

theorem ilpWord_getD (n : ℕ) (cnt : ℕ → ℕ) (B idx : ℕ) :
    (ilpWord n cnt B).getD idx 0 = if idx < zLen n then wordFun n cnt B idx else 0 := by
  by_cases h : idx < zLen n
  · simp [ilpWord, List.getD_eq_getElem?_getD, h, List.getElem?_map, List.getElem?_range h]
  · rw [if_neg h]
    have : (ilpWord n cnt B).length ≤ idx := by simp [ilpWord]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]

theorem decode_N (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) : (decodeILP (ilpWord n cnt B)).N = nN n := by
  simp only [decodeILP, ilpWord_getD, zLen, wordFun]
  have : 0 < 2 + nM n * nN n + nM n := by omega
  simp [this]

theorem decode_M (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) : (decodeILP (ilpWord n cnt B)).M = nM n := by
  simp only [decodeILP, ilpWord_getD, zLen, wordFun]
  have : 1 < 2 + nM n * nN n + nM n := by omega
  simp [this]

theorem decode_a (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) (j i : ℕ)
    (hj : j < (decodeILP (ilpWord n cnt B)).M) (hi : i < (decodeILP (ilpWord n cnt B)).N) :
    (decodeILP (ilpWord n cnt B)).a ⟨j, hj⟩ ⟨i, hi⟩ = coef n j i := by
  have hN := decode_N n cnt B
  have hM := decode_M n cnt B
  have hj' : j < nM n := hM ▸ hj
  have hi' : i < nN n := hN ▸ hi
  have h0 : (ilpWord n cnt B).getD 0 0 = nN n := hN
  simp only [decodeILP]
  rw [h0, ilpWord_getD]
  have hN' := nN_pos n
  have h1 : j * nN n + i < nM n * nN n := by
    have : (j + 1) * nN n ≤ nM n * nN n := Nat.mul_le_mul_right _ hj'
    nlinarith
  rw [if_pos (by simp only [zLen]; omega)]
  simp only [wordFun]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have e : 2 + j * nN n + i - 2 = j * nN n + i := by omega
  rw [e, mul_comm j, Nat.mul_add_div hN', Nat.div_eq_of_lt hi', Nat.mul_add_mod,
    Nat.mod_eq_of_lt hi']
  simp

theorem decode_b (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) (j : ℕ)
    (hj : j < (decodeILP (ilpWord n cnt B)).M) :
    (decodeILP (ilpWord n cnt B)).b ⟨j, hj⟩ = rhs n cnt B j := by
  have hN := decode_N n cnt B
  have hM := decode_M n cnt B
  have hj' : j < nM n := hM ▸ hj
  have h0 : (ilpWord n cnt B).getD 0 0 = nN n := hN
  have h1 : (ilpWord n cnt B).getD 1 0 = nM n := hM
  simp only [decodeILP]
  rw [h0, h1, ilpWord_getD]
  rw [if_pos (by simp only [zLen]; omega)]
  simp only [wordFun]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

/-- **Feasibility of the word of the program, as a statement about natural numbers.** -/
theorem feasible_iff_nat (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) :
    (decodeILP (ilpWord n cnt B)).Feasible ↔
      ∃ y : ℕ → ℕ, ∀ r < nM n, ∑ c ∈ range (nN n), coef n r c * y c = rhs n cnt B r := by
  have hN := decode_N n cnt B
  have hM := decode_M n cnt B
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun c => if h : c < (decodeILP (ilpWord n cnt B)).N then x ⟨c, h⟩ else 0,
      fun r hr => ?_⟩
    have hr' : r < (decodeILP (ilpWord n cnt B)).M := hM ▸ hr
    have := hx ⟨r, hr'⟩
    rw [decode_b n cnt B r hr'] at this
    rw [← this]
    have h2 : ∑ c ∈ range (decodeILP (ilpWord n cnt B)).N, coef n r c *
        (if h : c < (decodeILP (ilpWord n cnt B)).N then x ⟨c, h⟩ else 0) =
        ∑ i : Fin (decodeILP (ilpWord n cnt B)).N,
          (decodeILP (ilpWord n cnt B)).a ⟨r, hr'⟩ i * x i := by
      rw [← Fin.sum_univ_eq_sum_range (fun c => coef n r c *
        (if h : c < (decodeILP (ilpWord n cnt B)).N then x ⟨c, h⟩ else 0))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [decode_a n cnt B r i.val hr' i.isLt]
      simp
    rw [← hN, h2]
  · rintro ⟨y, hy⟩
    refine ⟨fun i => y i.val, fun j => ?_⟩
    have hj : j.val < nM n := hM ▸ j.isLt
    have := hy j.val hj
    rw [← decode_b n cnt B j.val j.isLt] at this
    rw [← this]
    rw [← hN, ← Fin.sum_univ_eq_sum_range (fun c => coef n j.val c * y c)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [decode_a n cnt B j.val i.val j.isLt i.isLt]

/-- The word of the reduction of `fairris-lax` (`ClientsILPRaw.zList`), restated. -/
def zFunRaw (n m k : ℕ) (cnt : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx = 0 then nN n else if idx = 1 then nM n
  else if idx < 2 + nM n * nN n then coef n ((idx - 2) / nN n) ((idx - 2) % nN n)
  else rhsRaw n m k cnt (idx - 2 - nM n * nN n)

/-- `ClientsILPRaw.zList`, restated. -/
def zList (n m k : ℕ) (cnt : ℕ → ℕ) : List ℕ := (List.range (zLen n)).map (zFunRaw n m k cnt)

/-- The word of the reduction is the word of the program with `B = m - k`. -/
theorem zList_eq_ilpWord (n m k : ℕ) (cnt : ℕ → ℕ) : zList n m k cnt = ilpWord n cnt (m - k) := rfl

end Lax117284Proofs.IlpClients
