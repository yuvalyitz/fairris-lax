import Lax117284Proofs.Machine.T9Accept
import Lax117284Proofs.Machine.X1Accept
import Lax117284Proofs.Machine.D3Pow
import Lax117284Proofs.Machine.D3Did
import Lax117284Proofs.Machine.D3Setup
import Lax117284Proofs.Machine.D3Sem

/-!
The command and the cost of the whole algorithm for a fixed positive number `m` of days, split
out from `D3Accept` so that files that only need to unfold the command or the cost (not the
correctness proof) don't have to elaborate the whole of `D3Accept`.
-/

namespace Lax117284Proofs.Machine.D3Accept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.T9Sem Lax117284Proofs.Machine.FreeAccept
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.T9Accept Lax117284Proofs.Machine.X1Accept
open Lax117284Proofs.Machine.MisBlk (asgE)
open Lax117284Proofs.Machine.D3Pow (checkM checkM_run KcheckM powCom powCom_run KpowCom)
open Lax117284Proofs.Machine.D3Did (didCom didCom_run DIDp SDID)
open Lax117284Proofs.Machine.D3Ops Lax117284Proofs.Machine.D3Rk Lax117284Proofs.Machine.D3Sweep
open Lax117284Proofs.Machine.D3Coll Lax117284Proofs.Machine.D3Client Lax117284Proofs.Machine.D3Setup
open Lax117284Proofs.Machine.D3Sem (DID did_iff goodM qF_eq_qI eOrd_eq_eI ddA_eq_ddI)
open Lax117284Proofs.D3DP Lax117284Proofs.D3Code Lax117284Proofs.D3Tab Lax117284Proofs.D3Rank
open Lax117284Proofs.D3Prog Lax117284Proofs.D3Link

/-- The body run once the gate `m0 = m` has passed: check the table, check the due dates are
day-independent, order the clients, run the dynamic program, and scan the table for a mark. -/
def dpBody (m : ℕ) : Com :=
  .seq (okLoop) (.seq (.assign "b1" (add (V "n") (.lit 1))) (.seq (powCom m)
    (.seq (.assign "PK" (mul (V "PP") (add (V "kp") (.lit 1))))
    (.seq (.assign "pk" (mul (V "PP") (V "kp"))) (.seq (didCom) (.seq (rkLoop)
    (.seq (.store "R" (.lit 0) (.lit 1)) (.seq (clientLoop)
    (.seq (.assign "fnd" (.lit 0)) (scanLoop))))))))))

/-- The gate on the parameter: with a client present and more required days `kp` than the `m`
days there are, no fair schedule exists, so the check flag `ok` is cleared before the (exponential
in `kp`) table is ever sized. -/
def gateK : Com :=
  .ite (.lt (V "m") (V "kp"))
    (.ite (.lt (.lit 0) (V "n")) (.assign "ok" (.lit 0)) (.assign "ok" (.lit 1)))
    (.assign "ok" (.lit 1))

/-- The whole algorithm, after the tokenizer has accepted. -/
def acceptDPos (m : ℕ) : Com :=
  .seq prepT
  (.seq fixOk
  (.seq gateK
  (.seq (checkM m)
  (.ite (.eq (V "ok") (.lit 1))
    (.seq (dpBody m) (.ite (.eq (V "ok") (.lit 1))
      (.ite (.eq (V "fnd") (.lit 1)) printZ rejT9) rejT9))
    rejT9))))

/-- The class the fixed number of days singles out, on the numbers of the table, together with a
fair schedule for it. -/
def decideOk (arr : List ℕ) (m : ℕ) : Prop :=
  ∃ hv : Valid arr, DID arr ∧ arr.getD 1 0 = m ∧ (instOf arr hv).HasKFairSchedule (paramOf arr)

/-- The cost of the accepting phase, on an input of `l` numbers, at a fixed number `m` of days. -/
def KaccDPos (m Sz l : ℕ) : ℕ :=
  200 + 80 + 20 + KcheckM m +
  (((40 + 4) * l + 6) + 20 + KpowCom m + 20 + 20 +
    ((80 + 10 + 4) * l + 6) +
    (((100 + 10 + 4) * l + 60 + 10 + 4) * l + 6) + 3 +
    ((((((400 + 10 + 4) * ((l + 1) ^ m * (m + 1)) + 6 + 60) + 10 + 4) * m + 6 + 60 + ((60 + 10 + 4) * ((l + 1) ^ m * (m + 1)) + 6)) + 10 + 4) * l + 6) +
    20 + ((20 + 10 + 4) * (l + 1) ^ m + 6)) +
  20 + 20 + (48 * Sz + 50 + (48 * Sz + 50)) + Krej9 Sz

end Lax117284Proofs.Machine.D3Accept
