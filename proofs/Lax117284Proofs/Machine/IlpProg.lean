import Lax808846Proofs.Tactic

/-!
Alg F as an IMP+ command.

The word of the integer program is read into the array `z`.  For the words of the family with
`n ≥ 1` clients the command counts through *all* vectors of `D = nN n + 2 n² + 1` digits below
`R = Kn n + 1` (the array `dg`, an odometer), and for each of them decodes a candidate solution
`xv` and checks it against the program stored in `z`.  Names:

* constants (set once): `N M zl n T Z V K R D rb bb tn nn`;
* arrays: `z` the word, `dg` the digits, `hl` (per type: has a large column so far), `kd` (the kind
  of each column), `rkA` (the rank of each column among the extras), `sg` (`sigma` per type),
  `S` (`Sj` per client), `wv` (values of the extras), `es` (`extraSum` per type), `xv` (the
  candidate).
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp

abbrev V (s : String) : Expr := .var s
abbrev lit (n : ℕ) : Expr := .lit n
abbrev asg (x : String) (e : Expr) : Com := .assign x e

/-- Right-nested sequence. -/
def seqs : List Com → Com
  | [] => .skip
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- `x := 0; while x < m do c`. -/
abbrev forZ (x m : String) (c : Com) : Com :=
  .seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) c)

/-- `x := x + 1`. -/
abbrev bump (x : String) : Com := asg x (.add (V x) (lit 1))

/-- `1` when `e < f`, `0` otherwise. -/
abbrev ltF (e f : Expr) : Expr := .sub (lit 1) (.sub (lit 1) (.sub f e))

/-- `1` when `e = f`, `0` otherwise. -/
abbrev eqF (e f : Expr) : Expr := .sub (lit 1) (.add (.sub e f) (.sub f e))

/-! ### Zeroing -/

/-- Set the first `len` cells of the array `a` to `0`. -/
def fillCom (a len : String) : Com :=
  forZ "fi" len (.seq (.store a (V "fi") (lit 0)) (bump "fi"))

/-! ### The kinds of the columns -/

/-- The kind of column `i`, and the flag of its type. -/
def kdBody : Com := seqs [
  asg "dv" (.get "dg" (V "i")),
  .ite (.lt (V "i") (V "V"))
    (seqs [
      asg "t" (.div (V "i") (V "Z")),
      asg "cf" (.get "z" (.add (.add (lit 2) (.mul (V "t") (V "N"))) (V "i"))),
      .ite (.eq (V "cf") (lit 1))
        (.ite (.lt (V "dv") (V "K"))
          (.store "kd" (V "i") (lit 3))
          (seqs [
            asg "hv" (.get "hl" (V "t")),
            .ite (.eq (V "hv") (lit 0))
              (.seq (.store "hl" (V "t") (lit 1)) (.store "kd" (V "i") (lit 1)))
              (.store "kd" (V "i") (lit 2))]))
        (.store "kd" (V "i") (lit 0))])
    (.ite (.lt (V "dv") (V "K"))
      (.store "kd" (V "i") (lit 3))
      (.store "kd" (V "i") (lit 2))),
  bump "i"]

def kdCom : Com := forZ "i" "N" kdBody

/-- The ranks of the columns among the extras; `E` ends the number of extras. -/
def rkBody : Com := seqs [
  .store "rkA" (V "i") (V "E"),
  .ite (.eq (.get "kd" (V "i")) (lit 2)) (asg "E" (.add (V "E") (lit 1))) .skip,
  bump "i"]

def rkCom : Com := .seq (asg "E" (lit 0)) (forZ "i" "N" rkBody)

/-! ### `sigma` -/

def sgBody : Com := seqs [
  .ite (.eq (.get "kd" (V "i")) (lit 3))
    (seqs [
      asg "t" (.div (V "i") (V "Z")),
      .store "sg" (V "t") (.add (.get "sg" (V "t")) (.get "dg" (V "i")))])
    .skip,
  bump "i"]

def sgCom : Com := forZ "i" "V" sgBody

/-! ### `Sj` -/

/-- Add `mv` times the coefficient of client `j` in column `i` to `S[j]`, for every client. -/
def addRowBody : Com := seqs [
  .store "S" (V "j")
    (.add (.get "S" (V "j"))
      (.mul (V "mv")
        (.get "z" (.add (.add (V "tn") (.mul (V "j") (V "N"))) (V "i"))))),
  bump "j"]

def addRow : Com := forZ "j" "n" addRowBody

def s1Body : Com := seqs [
  asg "mv" (.mul (.get "dg" (V "i")) (ltF (.get "dg" (V "i")) (V "K"))),
  addRow,
  bump "i"]

def s1Com : Com := forZ "i" "N" s1Body

/-- Add the rest of the demand of the type of the base `i` times its coefficients. -/
def s2Body : Com := seqs [
  asg "t" (.mul (.div (V "i") (V "Z")) (ltF (V "i") (V "V"))),
  asg "mv" (.mul (eqF (.get "kd" (V "i")) (lit 1))
    (.sub (.get "z" (.add (V "rb") (V "t"))) (.get "sg" (V "t")))),
  addRow,
  bump "i"]

def s2Com : Com := forZ "i" "N" s2Body

/-! ### The values of the extras -/

/-- `P` and `Q` of row `r` of `H`. -/
def pqInner : Com := seqs [
  asg "hp" (.get "dg" (.add (.add (V "N") (.mul (V "r") (V "n"))) (V "j"))),
  asg "hn" (.get "dg" (.add (.add (.add (V "N") (V "nn")) (.mul (V "r") (V "n"))) (V "j"))),
  asg "sj" (.get "S" (V "j")),
  asg "P" (.add (V "P") (.add (.mul (V "hp") (V "bb")) (.mul (V "hn") (V "sj")))),
  asg "Q" (.add (V "Q") (.add (.mul (V "hp") (V "sj")) (.mul (V "hn") (V "bb")))),
  bump "j"]

def pqCom : Com := seqs [asg "P" (lit 0), asg "Q" (lit 0), forZ "j" "n" pqInner]

def wvBody : Com := seqs [
  asg "r" (.mul (.get "rkA" (V "i")) (ltF (.get "rkA" (V "i")) (V "n"))),
  pqCom,
  .store "wv" (V "i")
    (.mul (.mul (eqF (.get "kd" (V "i")) (lit 2)) (ltF (.get "rkA" (V "i")) (V "n")))
      (.div (.sub (V "P") (V "Q")) (V "dl"))),
  bump "i"]

def wvCom : Com := .seq (asg "dl" (.get "dg" (.add (V "N") (.mul (lit 2) (V "nn"))))) (forZ "i" "N" wvBody)

/-- The sums of the values of the extras of a type. -/
def esBody : Com := seqs [
  asg "t" (.mul (.div (V "i") (V "Z")) (ltF (V "i") (V "V"))),
  .store "es" (V "t")
    (.add (.get "es" (V "t"))
      (.mul (.mul (eqF (.get "kd" (V "i")) (lit 2)) (ltF (V "i") (V "V"))) (.get "wv" (V "i")))),
  bump "i"]

def esCom : Com := forZ "i" "N" esBody

/-! ### The candidate -/

def xvBody : Com := seqs [
  asg "t" (.mul (.div (V "i") (V "Z")) (ltF (V "i") (V "V"))),
  .store "xv" (V "i")
    (.add
      (.add (.mul (eqF (.get "kd" (V "i")) (lit 3)) (.get "dg" (V "i")))
        (.mul (eqF (.get "kd" (V "i")) (lit 2)) (.get "wv" (V "i"))))
      (.mul (eqF (.get "kd" (V "i")) (lit 1))
        (.sub (.sub (.get "z" (.add (V "rb") (V "t"))) (.get "sg" (V "t")))
          (.get "es" (V "t"))))),
  bump "i"]

def xvCom : Com := forZ "i" "N" xvBody

/-! ### The check -/

def ckInner : Com := seqs [
  asg "acc" (.add (V "acc")
    (.mul (.get "z" (.add (V "rowb") (V "c"))) (.get "xv" (V "c")))),
  bump "c"]

def ckBody : Com := seqs [
  asg "rowb" (.add (lit 2) (.mul (V "r") (V "N"))),
  asg "acc" (lit 0),
  forZ "c" "N" ckInner,
  asg "ok" (.mul (V "ok") (eqF (V "acc") (.get "z" (.add (V "rb") (V "r"))))),
  bump "r"]

/-- `ok` ends `1` exactly when `xv` solves the program of `z`. -/
def ckCom : Com := .seq (asg "ok" (lit 1)) (forZ "r" "M" ckBody)

/-! ### One certificate -/

/-- Decode the candidate of the digits and test it: `ok` ends `1` exactly when it is accepted. -/
def evalCom : Com := seqs [
  fillCom "hl" "T", fillCom "sg" "T", fillCom "S" "n", fillCom "es" "T",
  kdCom, rkCom, sgCom, s1Com, s2Com, wvCom, esCom, xvCom, ckCom,
  .ite (.lt (V "E") (.add (V "n") (lit 1))) .skip (asg "ok" (lit 0))]

/-! ### The odometer -/

def odoBody : Com := seqs [
  asg "ov" (.add (.get "dg" (V "q")) (V "cy")),
  asg "cy" (.div (V "ov") (V "R")),
  .store "dg" (V "q") (.sub (V "ov") (.mul (V "cy") (V "R"))),
  bump "q"]

/-- Add one to the number whose digits are in `dg`; the carry `cy` ends `1` exactly when the
number was the largest one. -/
def odoCom : Com := .seq (asg "cy" (lit 1)) (forZ "q" "D" odoBody)

/-! ### The search -/

def searchBody : Com := seqs [
  evalCom,
  .ite (.eq (V "ok") (lit 1)) (asg "found" (lit 1)) .skip,
  odoCom,
  asg "done" (V "cy")]

def searchCom : Com := seqs [
  asg "found" (lit 0), asg "done" (lit 0),
  .while (.eq (V "done") (lit 0)) searchBody]

/-! ### Reading the word and the header -/

/-- Read the word into `z`: its two counts, then the other `M * N + M` entries. -/
def readBody : Com := seqs [.read "rv", .store "z" (.add (V "q") (lit 2)) (V "rv"), bump "q"]

def readHead : Com := seqs [
  .read "N", .read "M",
  .store "z" (lit 0) (V "N"), .store "z" (lit 1) (V "M"),
  asg "tl" (.add (.mul (V "M") (V "N")) (V "M"))]

def readCom : Com := .seq readHead (forZ "q" "tl" readBody)

/-- The number `n` of clients: the least `n` with `2 ^ (n * n) + n ≥ M`; then `nT n`, `nZ n`,
`nV n`, `Kn n`, `Rd n` and the other constants. -/
def nCom : Com := .seq (asg "n" (lit 0))
  (.while (.lt (.add (.shiftl (lit 1) (.mul (V "n") (V "n"))) (V "n")) (V "M")) (bump "n"))

def h2Com : Com := seqs [
  asg "nn" (.mul (V "n") (V "n")),
  asg "T" (.sub (V "M") (V "n")),
  asg "Z" (.shiftl (lit 1) (V "n")),
  asg "V" (.mul (V "T") (V "Z")),
  asg "np" (.add (V "n") (lit 1)),
  asg "pw" (lit 1)]

def pwCom : Com := forZ "i" "np" (.seq (asg "pw" (.mul (V "pw") (V "np"))) (bump "i"))

def h4Com : Com := seqs [
  asg "K" (.add (V "pw") (lit 1)),
  asg "R" (.add (V "K") (lit 1)),
  asg "D" (.add (.add (V "N") (.mul (lit 2) (V "nn"))) (lit 1)),
  asg "rb" (.add (lit 2) (.mul (V "M") (V "N"))),
  asg "tn" (.add (lit 2) (.mul (V "T") (V "N"))),
  asg "bb" (.get "z" (.add (V "rb") (V "T")))]

def hdrCom : Com := .seq nCom (.seq h2Com (.seq pwCom h4Com))

/-- The program `a x = b`. -/
def smallCom : Com := seqs [
  asg "a" (.get "z" (lit 2)), asg "b" (.get "z" (lit 3)),
  .ite (.eq (V "a") (lit 0))
    (.ite (.eq (V "b") (lit 0)) (.write (lit 1)) (.write (lit 0)))
    (.ite (.eq (.sub (V "b") (.mul (.div (V "b") (V "a")) (V "a"))) (lit 0))
      (.write (lit 1)) (.write (lit 0)))]

/-- The program of the family with `n ≥ 1` clients. -/
def bigCom : Com := seqs [hdrCom, searchCom, .write (V "found")]

/-- **The solver.** -/
def ilpCom : Com := seqs [readCom, .ite (.eq (V "N") (lit 1)) smallCom bigCom]

end Lax117284Proofs.Machine.Ilp
