import Lax117284Proofs.Machine.ClSimEff

/-!
The interpreter of word RAM programs, as an IMP+ command.

One iteration fetches the instruction at the counter `spc` from the program arrays, computes the
five numbers of `EffData` (`wf wa wv npc rdi wo wov`) in the block of its opcode, and commits them:
the memory write, the output, the counter, the tape position.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

abbrev V (s : String) : Expr := .var s
abbrev lit (n : ℕ) : Expr := .lit n
abbrev asg (x : String) (e : Expr) : Com := .assign x e

/-- Right-nested sequence. -/
def seqs : List Com → Com
  | [] => .skip
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- Fetch the instruction and the cells it names; reset the five numbers. -/
def fetchCom : Com := seqs [
  asg "op" (.get "ip0" (V "spc")), asg "fa" (.get "ip1" (V "spc")),
  asg "fb" (.get "ip2" (V "spc")), asg "fc" (.get "ip3" (V "spc")),
  asg "ra" (.and (V "fa") (V "mk")), asg "rb" (.and (V "fb") (V "mk")),
  asg "rc" (.and (V "fc") (V "mk")),
  asg "xa" (.get "om" (V "ra")), asg "xv" (.get "om" (V "rb")), asg "yv" (.get "om" (V "rc")),
  asg "xx" (.get "om" (V "xv")),
  asg "wf" (lit 0), asg "wa" (lit 0), asg "wv" (lit 0), asg "npc" (.add (V "spc") (lit 1)),
  asg "rdi" (lit 0), asg "wo" (lit 0), asg "wov" (lit 0)]

/-- The product of `xv` and `yv` modulo the word, from halves. -/
abbrev mulE : Expr :=
  .and (.add (.mul (.and (V "xv") (V "hm")) (.and (V "yv") (V "hm")))
    (.shiftl (.and (.add (.mul (.shiftr (V "xv") (V "hh")) (.and (V "yv") (V "hm")))
      (.mul (.and (V "xv") (V "hm")) (.shiftr (V "yv") (V "hh")))) (V "hm2")) (V "hh")))
    (V "mk")

/-- The left shift of `xv` by `yv` modulo the word. -/
abbrev shlBlock : Com :=
  .ite (.lt (V "yv") (V "wpv"))
    (asg "wv" (.shiftl (.and (V "xv") (.sub (.shiftl (lit 1) (.sub (V "wpv") (V "yv"))) (lit 1)))
      (V "yv")))
    .skip

/-- The block of each opcode. -/
def blk : ℕ → Com
  | 0 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" (.and (V "fb") (V "mk"))]
  | 1 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" (V "xx")]
  | 2 => seqs [asg "wf" (lit 1), asg "wa" (V "xa"), asg "wv" (V "xv")]
  | 3 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"),
      asg "wv" (.and (.add (V "xv") (V "yv")) (V "mk"))]
  | 4 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" (.sub (V "xv") (V "yv"))]
  | 5 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" mulE]
  | 6 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" (.div (V "xv") (V "yv"))]
  | 7 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" (.and (V "xv") (V "yv"))]
  | 8 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), shlBlock]
  | 9 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" (.sub (V "mk") (V "xv"))]
  | 10 => asg "npc" (V "fa")
  | 11 => .ite (.eq (V "xa") (lit 0)) (asg "npc" (V "fb")) .skip
  | 12 => .ite (.eq (V "rd") (V "zl")) (asg "npc" (V "fa")) .skip
  | 13 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" (.and (V "zl") (V "mk"))]
  | 14 => seqs [asg "wf" (lit 1), asg "wa" (V "ra"),
      .ite (.lt (V "xv") (V "zl")) (asg "wv" (.and (.get "z" (V "xv")) (V "mk"))) .skip]
  | 15 => asg "npc" (V "plen")
  | 16 => .ite (.lt (V "rd") (V "zl"))
      (seqs [asg "wf" (lit 1), asg "wa" (V "ra"), asg "wv" (.and (.get "z" (V "rd")) (V "mk")),
        asg "rdi" (lit 1)])
      (asg "npc" (V "plen"))
  | 17 => seqs [asg "wo" (lit 1), asg "wov" (V "xa")]
  | _ => .skip

/-- The ladder of tests on the opcode, from `k`, for `n` more steps. -/
def dispN : ℕ → ℕ → Com
  | 0, _ => .skip
  | n + 1, k => .ite (.eq (V "op") (lit k)) (blk k) (dispN n (k + 1))

def dispatch : Com := dispN 18 0

/-- Commit: the memory write, the output, the counter, the tape position. -/
def commitCom : Com := seqs [
  .ite (.eq (V "wf") (lit 1)) (.store "om" (V "wa") (V "wv")) .skip,
  .ite (.eq (V "wo") (lit 1)) (.seq (asg "outv" (V "wov")) (asg "nout" (lit 1))) .skip,
  asg "spc" (V "npc"), asg "rd" (.add (V "rd") (V "rdi"))]

/-- One iteration. -/
def bodyCom : Com := .seq fetchCom (.seq dispatch commitCom)

/-- The interpreter: run until the counter leaves the program. -/
def interpLoop : Com := .while (.lt (V "spc") (V "plen")) bodyCom

end Lax117284Proofs.Machine.ClSim
