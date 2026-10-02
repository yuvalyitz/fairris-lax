import Lax117284.ConflictGraph

/-!
---
title: Word Encoding of an Instance
type: definition
---
An instance is handed to a word random access machine as a word of numbers: the number $n$
of clients, the number $m$ of days, then the $nm$ processing times day by day, then the $nm$
due dates day by day. A decision instance of
$1 \mid \mathrm{rep} \mid \min_j \sum_i Z_{i,j}$ appends the fairness parameter as a final
entry, and a decision instance of the per-client problem appends one parameter per client.

A word determines the instance it encodes, so notions defined for instances — the number of
days, the treewidth of the overall conflict graph — are notions of the word as well.

# Formalization Notes

This is the point at which magnitudes stop being free. The processing times and due dates
are entries of the word, so a claim about a program reading it has to say that they are
words, which the fitting condition of the parameterized notions does. A size measure
counting only the number of clients and days would make the due dates of an instance
invisible and a running time stated against it would not be a claim about anything a
machine does.

Cells are read with `List.getD`, which returns `0` outside the word; the length condition
pins the word down completely, so the default is never reached at a position the other
conditions constrain.

The parameter is appended last, so that the instance block sits at the same positions
whether or not a parameter follows it, and the split of the word into its two parts is
determined by the word rather than chosen.

Decoding is stated as a function into instances, undefined — an instance with no client and
no day — on the words that encode none. That a word encodes at most one instance is a
statement rather than a convention, and it is what makes the decoded instance a function of
the word.
-/

namespace Lax117284.InstanceEncoding

open Lax117284.Scheduling

/-- The number of clients declared by a word: its first entry. -/
def clientCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The number of days declared by a word: its second entry. -/
def dayCount (x : List ℕ) : ℕ := x.getD 1 0

/-- The processing time of client `j`'s job on day `i`: the processing times follow the two
header entries, day by day. -/
def proc (x : List ℕ) (i j : ℕ) : ℕ := x.getD (2 + i * clientCount x + j) 0

/-- The due date of client `j`'s job on day `i`: the due dates follow the processing
times. -/
def due (x : List ℕ) (i j : ℕ) : ℕ :=
  x.getD (2 + dayCount x * clientCount x + i * clientCount x + j) 0

/-- The word `x` encodes the instance `I`. -/
structure EncodesInstance (x : List ℕ) (I : Instance) : Prop where
  /-- The word declares `I`'s clients. -/
  clientCount_eq : clientCount x = I.clients
  /-- The word declares `I`'s days. -/
  dayCount_eq : dayCount x = I.days
  /-- The word consists of the two header entries and the two arrays of one number per
  job. -/
  length_eq : x.length = 2 + 2 * I.days * I.clients
  /-- The processing times are `I`'s. -/
  proc_eq : ∀ (i : Fin I.days) (j : Fin I.clients), proc x i j = I.p i j
  /-- The due dates are `I`'s. -/
  due_eq : ∀ (i : Fin I.days) (j : Fin I.clients), due x i j = I.d i j

/-- The word `x` presents the instance `I` together with the fairness parameter `k`: an
instance block followed by the single entry `k`. -/
def EncodesUniform (x : List ℕ) (I : Instance) (k : ℕ) : Prop :=
  ∃ y, x = y ++ [k] ∧ EncodesInstance y I

/-- The word `x` presents the instance `I` together with one fairness parameter per
client. -/
def EncodesPerClient (x : List ℕ) (I : Instance) (k : Fin I.clients → ℕ) : Prop :=
  ∃ y, x = y ++ (List.ofFn k) ∧ EncodesInstance y I

/-- The words that encode an instance and a fairness parameter. -/
def UniformInstances : Set (List ℕ) := {x | ∃ I k, EncodesUniform x I k}

/-- The instance with no client and no day, the value of the decoding on a word that
encodes no instance. -/
def empty : Instance where
  clients := 0
  days := 0
  p := fun i => i.elim0
  d := fun i => i.elim0
  p_pos := fun i => i.elim0
  p_le_d := fun i => i.elim0

open Classical in
/-- The instance a word encodes, and `empty` on a word that encodes none. -/
noncomputable def decode (x : List ℕ) : Instance :=
  if h : ∃ I, EncodesInstance x I then h.choose else empty

/-- The fairness parameter a word declares: its last entry. -/
def parameter (x : List ℕ) : ℕ := (x.getLast? ).getD 0

/-- **A word encodes at most one instance.** -/
axiom encodesInstance_unique {x : List ℕ} {I J : Instance} (hI : EncodesInstance x I)
    (hJ : EncodesInstance x J) : I = J

/-- **The decoding of a word that encodes an instance is that instance.** -/
axiom decode_eq {x : List ℕ} {I : Instance} (h : EncodesInstance x I) : decode x = I

end Lax117284.InstanceEncoding
