import Lax808846Proofs.Tactic
import Lax117284Proofs.Machine.ClBruteDefs

/-!
The brute force as an IMP+ command.

The array `bfsc` is the schedule, one bit per cell (`i * n + j` is client `j` on day `i`), read as
a binary counter. One pass over the counter checks the bits (`evalCom`: no two conflicting
clients on one day, every client served on at least `k` days), records a success, and adds one
(`odoCom`), the carry out of the last cell ending the loop.

Every test is arithmetic on the values `0` and `1` (`ltF e f` is `1` exactly when `e < f`), so
that a pass costs the same whatever it finds.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

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

/-- `1` when `e < f`, `0` otherwise. -/
abbrev ltF (e f : Expr) : Expr := .sub (lit 1) (.sub (lit 1) (.sub f e))

/-! ### One pair of clients `a < b` of a day -/

/-- The pair `(a, b)` on day `i`: does it clash? Remove it from the flag. -/
def bStep : Com := seqs [
  asg "bfqb" (.add (V "bfro") (V "bfb")),
  asg "bfbb" (.get "bfsc" (V "bfqb")),
  asg "bfpb" (.get "X" (.add (lit 2) (V "bfqb"))),
  asg "bfdb" (.get "X" (.add (.add (lit 2) (V "bfmn")) (V "bfqb"))),
  asg "bfsb" (.sub (V "bfdb") (V "bfpb")),
  asg "bfx" (.mul (V "bfba") (V "bfbb")),
  asg "bfx" (.mul (V "bfx") (ltF (V "bfa") (V "bfb"))),
  asg "bfx" (.mul (V "bfx") (ltF (V "bfsa") (V "bfdb"))),
  asg "bfx" (.mul (V "bfx") (ltF (V "bfsb") (V "bfda"))),
  asg "bfok" (.sub (V "bfok") (V "bfx")),
  asg "bfb" (.add (V "bfb") (lit 1))]

/-- The pair loop of one client `a`. -/
abbrev bLoop : Com := forZ "bfb" "n" bStep

/-- Read client `a` of day `i`: its bit, its due date, its start. -/
def aSetup : Com := seqs [
  asg "bfqa" (.add (V "bfro") (V "bfa")),
  asg "bfba" (.get "bfsc" (V "bfqa")),
  asg "bfpa" (.get "X" (.add (lit 2) (V "bfqa"))),
  asg "bfda" (.get "X" (.add (.add (lit 2) (V "bfmn")) (V "bfqa"))),
  asg "bfsa" (.sub (V "bfda") (V "bfpa"))]

/-- One client `a` of day `i` against every client. -/
def aStep : Com := .seq aSetup (.seq bLoop (asg "bfa" (.add (V "bfa") (lit 1))))

/-- One day. -/
def iStep : Com := seqs [
  asg "bfro" (.mul (V "bfi") (V "n")),
  forZ "bfa" "n" aStep,
  asg "bfi" (.add (V "bfi") (lit 1))]

/-- Feasibility: no day serves two conflicting clients. -/
abbrev feasCom : Com := forZ "bfi" "m" iStep

/-! ### Fairness: every client is served on `k` days -/

/-- Add the cell of day `i`, client `j`. -/
def cStep : Com := seqs [
  asg "bfc" (.add (V "bfc") (.get "bfsc" (.add (.mul (V "bfi") (V "n")) (V "bfj")))),
  asg "bfi" (.add (V "bfi") (lit 1))]

/-- Compare the count with `k`; move to the next client. -/
def jTail : Com := seqs [
  asg "bfx" (ltF (V "bfc") (V "k")),
  asg "bfok" (.sub (V "bfok") (V "bfx")),
  asg "bfj" (.add (V "bfj") (lit 1))]

/-- One client: count its days, compare with `k`. -/
def jStep : Com := .seq (asg "bfc" (lit 0)) (.seq (forZ "bfi" "m" cStep) jTail)

abbrev fairCom : Com := forZ "bfj" "n" jStep

/-- The feasibility scan, unless there is no client (then the scan over the days would cost
a number of steps that the word does not bound). -/
def feasG : Com := .ite (.lt (lit 0) (V "n")) feasCom .skip

/-- Test the vector in `bfsc`: `bfok` ends `1` exactly when it is feasible and fair. -/
def evalCom : Com := seqs [asg "bfok" (lit 1), feasG, fairCom]

/-! ### The odometer -/

/-- One cell of the increment: add the carry; the cell keeps the parity, the carry the rest. -/
def oStep : Com := seqs [
  asg "bft" (.add (.get "bfsc" (V "bfq")) (V "bfcy")),
  asg "bfcy" (.div (V "bft") (lit 2)),
  .store "bfsc" (V "bfq") (.sub (V "bft") (.mul (V "bfcy") (lit 2))),
  asg "bfq" (.add (V "bfq") (lit 1))]

/-- Add one to the vector; the carry out of the last cell is `1` exactly when it was the last
vector, and the vector is then all zeros again. -/
def odoCom : Com := .seq (asg "bfcy" (lit 1)) (forZ "bfq" "bfmn" oStep)

/-! ### The search -/

/-- Record a success. -/
def recCom : Com := .ite (.eq (V "bfok") (lit 1)) (asg "bfans" (lit 1)) .skip

/-- Test a vector, record a success, move on. -/
def bodyCom : Com := seqs [evalCom, recCom, odoCom, asg "bfdn" (V "bfcy")]

/-- **The brute force**: `bfans` ends `1` exactly when some vector of `m * n` bits reads a
feasible schedule serving every client on `k` days. -/
def bruteCom : Com := seqs [
  asg "bfmn" (.mul (V "n") (V "m")),
  asg "bfans" (lit 0),
  asg "bfdn" (lit 0),
  .while (.eq (V "bfdn") (lit 0)) bodyCom]

end Lax117284Proofs.Machine.ClBrute
