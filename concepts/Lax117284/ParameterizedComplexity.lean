import Lax496464.WH_A2_FptReductions
import Lax888481.ParameterizedComplexity

/-!
---
title: Parameterized Problems on a Word RAM
type: definition
---
Parameterized problems use the archive's `Lax888481.ParameterizedComplexity.Problem`.
The decision bounds use `Lax496464.WH_A1_FptTime.FptTimeOn`: one program,
a computable function of the parameter, and a polynomial in binary input size.
For the structural parameter involving treewidth, the time bound does not require
polynomial-time computation of the parameter itself.

The local `Fits` and `Decides` predicates record the unprefixed machine interface
used by the scheduling programs. They are intermediate specifications; the public
tractability statements use the imported fixed-parameter time definition.
-/

namespace Lax117284.ParameterizedComplexity

open Lax808846.Ram Lax808846.RamComputes

abbrev Problem := Lax888481.ParameterizedComplexity.Problem

/-- The word `x` fits at word length `w`, with room for `c` times its length: every entry
`v` of `x` satisfies `c * (x.length + v + 1) ^ c ≤ 2 ^ w`. -/
def Fits (c w : ℕ) (x : List ℕ) : Prop := ∀ v ∈ x, c * (x.length + v + 1) ^ c ≤ 2 ^ w

open Classical in
/-- At every word length, the program decides `P` on every admissible word that fits,
within `c * g k * (|x| + 1) ^ c` instructions, where `k` is the word's parameter. It writes `1`
for a yes-instance and `0` for a no-instance. -/
def Decides (P : Problem) (prog : Program) (c : ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ w : ℕ, ComputesInTime w prog
    {x | x ∈ P.Domain ∧ Fits c w x}
    (fun x => if P.Yes x then [1] else [0])
    (fun x => c * g (P.param x) * (x.length + 1) ^ c)

/-- The shared fixed-parameter time predicate applied to a decision problem. -/
noncomputable abbrev FptDecision (P : Problem) : Prop :=
  open Classical in
  Lax496464.WH_A1_FptTime.FptTimeOn P.Domain P.param
    (fun x => if P.Yes x then [1] else [0])

/-- Intermediate machine specification for a reduction computed by `prog` within
`c * g k * (|x| + 1) ^ c` instructions on the admissible words that fit and whose image fits,
and raising the parameter to at most `h k`. -/
structure MachineReduction (P Q : Problem) (f : List ℕ → List ℕ) (prog : Program)
    (c : ℕ) (g h : ℕ → ℕ) : Prop where
  /-- The image of an admissible word is admissible. -/
  maps_domain : ∀ x ∈ P.Domain, f x ∈ Q.Domain
  /-- Yes-instances go to yes-instances, and no-instances to no-instances. -/
  correct : ∀ x ∈ P.Domain, (P.Yes x ↔ Q.Yes (f x))
  /-- The new parameter is bounded by a function of the old one alone. -/
  param_le : ∀ x ∈ P.Domain, Q.param (f x) ≤ h (P.param x)
  /-- At every word length, the program computes `f` on every admissible word that fits and
  whose image fits, within the stated bound. -/
  time : ∀ w : ℕ, ComputesInTime w prog
    {x | x ∈ P.Domain ∧ Fits c w x ∧ Fits c w (f x)}
    f (fun x => c * g (P.param x) * (x.length + 1) ^ c)

/-- The archive's shared fixed-parameter reduction relation. -/
abbrev FptReduces := Lax496464.WH_A2_FptReductions.FptReduces

end Lax117284.ParameterizedComplexity
