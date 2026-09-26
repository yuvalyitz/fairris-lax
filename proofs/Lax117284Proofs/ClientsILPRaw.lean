import Lax117284Proofs.ClientsILPBits
import Lax117284.IlpClients

/-!
The integer program of Theorem 4's third bullet, as numbers: its coefficients and right-hand sides
as functions of the number `n` of clients, the number `m` of days, the fairness parameter `k` and
the table `cnt` of how many days have each type.
-/

namespace Lax117284Proofs.ClientsILP

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
def coefRaw (n r c : ℕ) : ℕ :=
  if c < nV n then
    (if indepB n (c / nZ n) (c % nZ n) then
      (if r < nT n then (if c / nZ n = r then 1 else 0)
       else (if (c % nZ n).testBit (r - nT n) = false then 1 else 0))
     else 0)
  else (if nT n ≤ r ∧ c - nV n = r - nT n then 1 else 0)

/-- The right-hand side of constraint `r`. -/
def rhsRaw (n m k : ℕ) (cnt : ℕ → ℕ) (r : ℕ) : ℕ := if r < nT n then cnt r else m - k

/-- The number of entries of the word of the program. -/
def zLen (n : ℕ) : ℕ := 2 + nM n * nN n + nM n

/-- The entry `idx` of the word of the program: the two counts, the coefficients row by row, the
right-hand sides. -/
def zFunRaw (n m k : ℕ) (cnt : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx = 0 then nN n else if idx = 1 then nM n
  else if idx < 2 + nM n * nN n then coefRaw n ((idx - 2) / nN n) ((idx - 2) % nN n)
  else rhsRaw n m k cnt (idx - 2 - nM n * nN n)

/-- The word of the program. -/
def zList (n m k : ℕ) (cnt : ℕ → ℕ) : List ℕ := (List.range (zLen n)).map (zFunRaw n m k cnt)

theorem nT_pos (n : ℕ) : 0 < nT n := Nat.two_pow_pos _
theorem nZ_pos (n : ℕ) : 0 < nZ n := Nat.two_pow_pos _
theorem nN_pos (n : ℕ) : 0 < nN n := by
  have := Nat.mul_pos (nT_pos n) (nZ_pos n); simp only [nN, nV]; omega

theorem zList_getD (n m k : ℕ) (cnt : ℕ → ℕ) (idx : ℕ) :
    (zList n m k cnt).getD idx 0 = if idx < zLen n then zFunRaw n m k cnt idx else 0 := by
  by_cases h : idx < zLen n
  · simp [zList, List.getD_eq_getElem?_getD, h, List.getElem?_map, List.getElem?_range h]
  · rw [if_neg h]
    have : (zList n m k cnt).length ≤ idx := by simp [zList]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]

open Lax117284.IlpClients (decodeILP) in
theorem decode_N (n m k : ℕ) (cnt : ℕ → ℕ) : (decodeILP (zList n m k cnt)).N = nN n := by
  simp only [decodeILP, zList_getD, zLen, zFunRaw]
  have : 0 < 2 + nM n * nN n + nM n := by omega
  simp [this]

open Lax117284.IlpClients (decodeILP) in
theorem decode_M (n m k : ℕ) (cnt : ℕ → ℕ) : (decodeILP (zList n m k cnt)).M = nM n := by
  simp only [decodeILP, zList_getD, zLen, zFunRaw]
  have : 1 < 2 + nM n * nN n + nM n := by omega
  simp [this]

open Lax117284.IlpClients (decodeILP) in
theorem decode_a (n m k : ℕ) (cnt : ℕ → ℕ) (j i : ℕ)
    (hj : j < (decodeILP (zList n m k cnt)).M) (hi : i < (decodeILP (zList n m k cnt)).N) :
    (decodeILP (zList n m k cnt)).a ⟨j, hj⟩ ⟨i, hi⟩ = coefRaw n j i := by
  have hN := decode_N n m k cnt
  have hM := decode_M n m k cnt
  have hj' : j < nM n := hM ▸ hj
  have hi' : i < nN n := hN ▸ hi
  have h0 : (zList n m k cnt).getD 0 0 = nN n := hN
  simp only [decodeILP]
  rw [h0, zList_getD]
  have hN' := nN_pos n
  have h1 : j * nN n + i < nM n * nN n := by
    have : (j + 1) * nN n ≤ nM n * nN n := Nat.mul_le_mul_right _ hj'
    nlinarith
  rw [if_pos (by simp only [zLen]; omega)]
  simp only [zFunRaw]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have e : 2 + j * nN n + i - 2 = j * nN n + i := by omega
  rw [e, mul_comm j, Nat.mul_add_div hN', Nat.div_eq_of_lt hi', Nat.mul_add_mod,
    Nat.mod_eq_of_lt hi']
  simp

open Lax117284.IlpClients (decodeILP) in
theorem decode_b (n m k : ℕ) (cnt : ℕ → ℕ) (j : ℕ) (hj : j < (decodeILP (zList n m k cnt)).M) :
    (decodeILP (zList n m k cnt)).b ⟨j, hj⟩ = rhsRaw n m k cnt j := by
  have hN := decode_N n m k cnt
  have hM := decode_M n m k cnt
  have hj' : j < nM n := hM ▸ hj
  have h0 : (zList n m k cnt).getD 0 0 = nN n := hN
  have h1 : (zList n m k cnt).getD 1 0 = nM n := hM
  simp only [decodeILP]
  rw [h0, h1, zList_getD]
  rw [if_pos (by simp only [zLen]; omega)]
  simp only [zFunRaw]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

open Lax117284.IlpClients (decodeILP) in
theorem feasible_iff_nat (n m k : ℕ) (cnt : ℕ → ℕ) :
    (decodeILP (zList n m k cnt)).Feasible ↔
      ∃ y : ℕ → ℕ, ∀ r < nM n, ∑ c ∈ range (nN n), coefRaw n r c * y c = rhsRaw n m k cnt r := by
  have hN := decode_N n m k cnt
  have hM := decode_M n m k cnt
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun c => if h : c < (decodeILP (zList n m k cnt)).N then x ⟨c, h⟩ else 0, fun r hr => ?_⟩
    have hr' : r < (decodeILP (zList n m k cnt)).M := hM ▸ hr
    have := hx ⟨r, hr'⟩
    rw [decode_b n m k cnt r hr'] at this
    rw [← this]
    have h2 : ∑ c ∈ range (decodeILP (zList n m k cnt)).N, coefRaw n r c *
        (if h : c < (decodeILP (zList n m k cnt)).N then x ⟨c, h⟩ else 0) =
        ∑ i : Fin (decodeILP (zList n m k cnt)).N, (decodeILP (zList n m k cnt)).a ⟨r, hr'⟩ i * x i := by
      rw [← Fin.sum_univ_eq_sum_range (fun c => coefRaw n r c *
        (if h : c < (decodeILP (zList n m k cnt)).N then x ⟨c, h⟩ else 0))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [decode_a n m k cnt r i.val hr' i.isLt]
      simp
    rw [← hN, h2]
  · rintro ⟨y, hy⟩
    refine ⟨fun i => y i.val, fun j => ?_⟩
    have hj : j.val < nM n := hM ▸ j.isLt
    have := hy j.val hj
    rw [← decode_b n m k cnt j.val j.isLt] at this
    rw [← this]
    rw [← hN, ← Fin.sum_univ_eq_sum_range (fun c => coefRaw n j.val c * y c)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [decode_a n m k cnt j.val i.val j.isLt i.isLt]

end Lax117284Proofs.ClientsILP
