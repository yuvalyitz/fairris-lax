import Lax117284Proofs.IlpClients.Structure
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Alg F: the Certificate and Its Decoding

A certificate is `ω = (d, Hp, Hn, δ)`: a digit `d c ∈ [0, K]` for every column (`K = Kn n`; the
digit `K` means "large"), a matrix `H = Hp - Hn` with entries of absolute value `≤ n!` (an integer
left inverse of the difference matrix of the large columns) and a common denominator `δ ∈ [1, n!]`.

`decode n cnt B ω` reads the certificate as follows (all passes are loops over columns in index
order; see `PLAN-fixedmatrix.md` §4):

1. digits of zero columns are ignored;
2. for every type `t`, `sigma t` is the sum of the small digits (`< K`) of the live pairs of type `t`;
   the large columns of the type are `hasL t`; the *base* of a type is its least large column;
   if the type has no large column `sigma t` must be `cnt t`, else `sigma t ≤ cnt t` and the rest
   `cp t = cnt t - sigma t` goes to the large columns;
3. the *extras* are the large columns that are not bases (large slacks included), `E ≤ n` of them,
   ranked in index order by `rk`;
4. `Sj j` is the contribution of the small digits and of the bases (each base carries `cp t`) to the
   client row `j`;
5. for the `i`-th extra, `P_i = ∑_j Hp_ij B + Hn_ij S_j`, `Q_i = ∑_j Hp_ij S_j + Hn_ij B`; it is
   required that `Q_i ≤ P_i` and `δ ∣ P_i - Q_i`; the value of the extra is `(P_i - Q_i)/δ`
   (this is `(H (B - S))_i / δ`);
6. every base gets `cp t` minus the sum of the values of the extras of its type (which must be `≤ cp t`).

The candidate `x` is then *checked* against the program (`Checks`); soundness is thus trivial, all
the work is in completeness (`Complete.lean`).
-/

namespace Lax117284Proofs.IlpClients

open Finset
open Classical

noncomputable section

set_option genSizeOfSpec false in
/-- A certificate of Alg F. -/
structure Cert where
  /-- The digits, one per column. -/
  d : ℕ → ℕ
  /-- The positive part of the integer left inverse `H`. -/
  Hp : ℕ → ℕ → ℕ
  /-- The negative part of `H`. -/
  Hn : ℕ → ℕ → ℕ
  /-- The common denominator. -/
  δ : ℕ

/-- The certificates of the search space: digits `≤ K`, entries of `H` and `δ` `≤ n!`, `δ ≥ 1`
(only the digits of the columns and the `n × n` block of `H` matter). -/
def InBox (n : ℕ) (ω : Cert) : Prop :=
  (∀ c < nN n, ω.d c ≤ Kn n) ∧ (∀ i < n, ∀ j < n, ω.Hp i j ≤ n.factorial ∧ ω.Hn i j ≤ n.factorial) ∧
    1 ≤ ω.δ ∧ ω.δ ≤ n.factorial

/-- The column `c` is live: a slack or a live pair (not a zero column). -/
def isLive (n c : ℕ) : Prop := c < nN n ∧ (nV n ≤ c ∨ liveP n c)

/-- The large columns: the live columns with digit `K`. -/
def Lset (n : ℕ) (d : ℕ → ℕ) : Finset ℕ :=
  (range (nN n)).filter (fun c => isLive n c ∧ d c = Kn n)

/-- The type of a typed column (junk `0` for untyped columns). -/
def tyIdx (n c : ℕ) : ℕ := (tyOf n c).getD 0

/-- `c` is the base of its type: the least large column of its type. -/
def isBase (n : ℕ) (d : ℕ → ℕ) (c : ℕ) : Prop :=
  c ∈ Lset n d ∧ tyOf n c ≠ none ∧ bs (tyOf n) (Lset n d) c = c

/-- `c` is an extra: a large column that is not a base. -/
def isExtra (n : ℕ) (d : ℕ → ℕ) (c : ℕ) : Prop := c ∈ Lset n d ∧ ¬ isBase n d c

/-- The extras. -/
def Ext (n : ℕ) (d : ℕ → ℕ) : Finset ℕ := (range (nN n)).filter (isExtra n d)

/-- The rank of a column among the extras. -/
def rk (n : ℕ) (d : ℕ → ℕ) (c : ℕ) : ℕ := ((range c).filter (isExtra n d)).card

/-- The sum of the small digits of the live pairs of type `t`. -/
def sigma (n : ℕ) (d : ℕ → ℕ) (t : ℕ) : ℕ :=
  ∑ c ∈ range (nN n), if tyOf n c = some t ∧ d c < Kn n then d c else 0

/-- The type `t` has a large column. -/
def hasL (n : ℕ) (d : ℕ → ℕ) (t : ℕ) : Prop := ∃ c ∈ Lset n d, tyOf n c = some t

/-- What is left of the demand of type `t` for the large columns. -/
def cp (n : ℕ) (cnt : ℕ → ℕ) (d : ℕ → ℕ) (t : ℕ) : ℕ := cnt t - sigma n d t

/-- The contribution of the small digits and of the bases to client row `j`. -/
def Sj (n : ℕ) (cnt : ℕ → ℕ) (d : ℕ → ℕ) (j : ℕ) : ℕ :=
  (∑ c ∈ range (nN n), if d c < Kn n then d c * coef n (nT n + j) c else 0) +
    ∑ c ∈ range (nN n), if isBase n d c then cp n cnt d (tyIdx n c) * coef n (nT n + j) c else 0

/-- `P_i`. -/
def Pi (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) (ω : Cert) (i : ℕ) : ℕ :=
  ∑ j ∈ range n, (ω.Hp i j * B + ω.Hn i j * Sj n cnt ω.d j)

/-- `Q_i`. -/
def Qi (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) (ω : Cert) (i : ℕ) : ℕ :=
  ∑ j ∈ range n, (ω.Hp i j * Sj n cnt ω.d j + ω.Hn i j * B)

/-- The value of the extra `c`. -/
def wcol (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) (ω : Cert) (c : ℕ) : ℕ :=
  (Pi n cnt B ω (rk n ω.d c) - Qi n cnt B ω (rk n ω.d c)) / ω.δ

/-- The sum of the values of the extras of type `t`. -/
def extraSum (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) (ω : Cert) (t : ℕ) : ℕ :=
  ∑ c ∈ range (nN n), if isExtra n ω.d c ∧ tyOf n c = some t then wcol n cnt B ω c else 0

/-- The conditions under which `decode` accepts. -/
def Guards (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) (ω : Cert) : Prop :=
  (∀ t < nT n, (hasL n ω.d t → sigma n ω.d t ≤ cnt t) ∧ (¬ hasL n ω.d t → sigma n ω.d t = cnt t)) ∧
  (Ext n ω.d).card ≤ n ∧
  (∀ c ∈ Ext n ω.d, Qi n cnt B ω (rk n ω.d c) ≤ Pi n cnt B ω (rk n ω.d c) ∧
      ω.δ ∣ Pi n cnt B ω (rk n ω.d c) - Qi n cnt B ω (rk n ω.d c)) ∧
  (∀ t < nT n, hasL n ω.d t → extraSum n cnt B ω t ≤ cp n cnt ω.d t)

/-- The candidate solution read off the certificate. -/
def xval (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) (ω : Cert) (c : ℕ) : ℕ :=
  if isLive n c ∧ ω.d c < Kn n then ω.d c
  else if isExtra n ω.d c then wcol n cnt B ω c
  else if isBase n ω.d c then
    cp n cnt ω.d (tyIdx n c) - extraSum n cnt B ω (tyIdx n c)
  else 0

/-- **Decoding.** -/
def decode (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) (ω : Cert) : Option (ℕ → ℕ) :=
  if Guards n cnt B ω then some (xval n cnt B ω) else none

/-- `x` solves the integer program. -/
def Checks (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) (x : ℕ → ℕ) : Prop :=
  ∀ r < nM n, ∑ c ∈ range (nN n), coef n r c * x c = rhs n cnt B r


end

end Lax117284Proofs.IlpClients
