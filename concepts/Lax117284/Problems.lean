import Lax117284.Scheduling
import Lax429075.Reductions
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits

/-!
---
title: The decision problems as languages
type: definition
---
Instances as binary words, the representation against which classical complexity measures
running time, and the two decision problems as languages of such words.

A natural number is written as its binary digits preceded by their number in unary, which
makes the code self-delimiting. An instance is the number of clients, the number of days,
and then, day by day and client by client, the processing time and the due date of that
client's job on that day. An instance of $1 \mid \mathrm{rep} \mid \min_j \sum_i Z_{i,j}$
appends the fairness parameter $k$; an instance of
$1 \mid k_j, \mathrm{rep} \mid \min_j \sum_i Z_{i,j}$ appends one parameter per client.

The language of the problem consists of the words encoding an instance and a parameter for
which a fair schedule exists. Every complexity claim of the source concerns a *class* of
instances — those with day-independent due dates, those whose fairness parameter is $m-1$,
those whose overall conflict graph has small treewidth — so the language is taken relative
to such a class: a word belongs to it if it encodes an instance in the class, together with
a parameter, that admits a fair schedule. A language is NP-hard if every language in NP
reduces to it in polynomial time.

# Formalization notes

Numbers are written in binary. Under a unary encoding the input would be exponentially
longer, a polynomial-time reduction correspondingly easier to achieve, and every hardness
claim weaker.

Restricting the class shrinks the language on both sides at once, so a reduction into it
witnesses hardness on the class: a word outside the class is not in the language, whatever
else it encodes, and a reduction must therefore produce instances of the class for the
yes-instances it is given. This is what is usually called para-NP-hardness when the class
is one on which a parameter is bounded by a constant — the conclusion being that no
algorithm runs in time $f(\tau)\cdot\mathrm{poly}(n)$ for any function $f$ unless
$\mathrm{P} = \mathrm{NP}$.

The class is a predicate on the instance and the parameter rather than a bound on a
parameter function, so that a claim reads as the condition a reader checks the construction
against.
-/

namespace Lax117284.Problems

open Lax117284.Scheduling Lax434930.PolynomialTime
open Lax434930.NondeterministicPolynomialTime Lax429075.Reductions

/-- A natural number as a binary word: its digits, least significant first, preceded by
their number in unary. -/
def encodeNat (n : ℕ) : Word :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- An instance as a binary word: the number of clients, the number of days, then the
processing time and the due date of every job. -/
def encodeInstance (I : Instance) : Word :=
  encodeNat I.clients ++ encodeNat I.days ++
    (List.finRange I.days).flatMap fun i =>
      (List.finRange I.clients).flatMap fun j => encodeNat (I.p i j) ++ encodeNat (I.d i j)

/-- An instance of `1 | rep | min_j ∑_i Z_{i,j}`: an instance followed by the fairness
parameter. -/
def encodeUniform (I : Instance) (k : ℕ) : Word := encodeInstance I ++ encodeNat k

/-- An instance of `1 | k_j, rep | min_j ∑_i Z_{i,j}`: an instance followed by one
fairness parameter per client. -/
def encodePerClient (I : Instance) (k : Fin I.clients → ℕ) : Word :=
  encodeInstance I ++ (List.finRange I.clients).flatMap fun j => encodeNat (k j)

/-- **`1 | rep | min_j ∑_i Z_{i,j}` on the class `C`**, as a language: the words encoding
an instance of `C` with a fairness parameter for which a fair schedule exists. -/
def Uniform (C : Instance → ℕ → Prop) : Language :=
  {w | ∃ (I : Instance) (k : ℕ), encodeUniform I k = w ∧ C I k ∧ I.HasKFairSchedule k}

/-- **`1 | k_j, rep | min_j ∑_i Z_{i,j}` on the class `C`**, as a language. -/
def PerClient (C : (I : Instance) → (Fin I.clients → ℕ) → Prop) : Language :=
  {w | ∃ (I : Instance) (k : Fin I.clients → ℕ),
    encodePerClient I k = w ∧ C I k ∧ I.HasFairSchedule k}

/-- The class of all instances and parameters. -/
def any : Instance → ℕ → Prop := fun _ _ => True

/-- An instance with one client and no day, whose only client cannot be served at all. -/
def blocked : Instance where
  clients := 1
  days := 0
  p := fun i => i.elim0
  d := fun i => i.elim0
  p_pos := fun i => i.elim0
  p_le_d := fun i => i.elim0

/-- A word belonging to no language of this submission: the instance `blocked` with the
fairness parameter `1`. It is the image a reduction gives the words it must reject. -/
def rejected : Word := encodeUniform blocked 1

/-- A word belonging to no per-client language: the instance `blocked` with the fairness
parameter `1` for its only client. -/
def rejectedPerClient : Word := encodePerClient blocked fun _ => 1

/-- **A word encodes at most one instance with at most one fairness parameter.** -/
axiom encodeUniform_inj {I I' : Instance} {k k' : ℕ}
    (h : encodeUniform I k = encodeUniform I' k') : I = I' ∧ k = k'

/-- **A word encodes at most one instance with at most one family of fairness
parameters.** -/
axiom encodePerClient_inj {I I' : Instance} {k : Fin I.clients → ℕ}
    {k' : Fin I'.clients → ℕ} (h : encodePerClient I k = encodePerClient I' k') :
    I = I' ∧ HEq k k'

/-- **The rejected word lies in no version of the language.** -/
axiom rejected_notMem (C : Instance → ℕ → Prop) : rejected ∉ Uniform C

/-- **The rejected word of the per-client problem lies in no version of its language.** -/
axiom rejectedPerClient_notMem (C : (I : Instance) → (Fin I.clients → ℕ) → Prop) :
    rejectedPerClient ∉ PerClient C

/-- A language is **NP-hard** if every language in NP reduces to it in polynomial time. -/
def NPHard (L : Language) : Prop := ∀ A : Language, A ∈ NP → ManyOne A L

end Lax117284.Problems
