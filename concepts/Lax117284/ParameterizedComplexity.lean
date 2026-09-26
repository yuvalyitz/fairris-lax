import Lax808846.RamComputes

/-!
---
title: Parameterized problems on a word RAM
type: definition
---
A *parameterized problem* is a set of admissible input words, a yes-instance predicate on
them, and a parameter read off the word. It is *fixed-parameter tractable* if one word RAM
program decides it, on every admissible word $x$ of parameter $k$, within
$c\,g(k)\,(|x|+1)^c$ instructions for a constant $c$ and a function $g$ of the parameter
alone: the running time is a function of the parameter times a polynomial in the length.

# Formalization notes

The parameter is a function of the input word rather than something carried alongside it.
This is what lets one program serve every parameter: a program that must be told the
parameter from outside would be a family of programs, one per parameter, and could hide
unbounded advice in its literals. The quantifier order says so — the program and the
constant come before the instance, the parameter and the word length. A parameter that is a
structural property of the encoded object, such as the treewidth of a graph read off the
word, is a function of the word all the same, and no computability of that function is
required or used.

`Fits` is the fitting condition, stated as an explicit inequality against $2^w$ rather than
through logarithms. It says of each entry $v$ of a word that $c(|x|+v+1)^c \le 2^w$, which at
once makes every entry a genuine word and leaves polynomial room in the length, the usual
word RAM assumption of a word of at least $c\log|x|$ bits: the memory a polynomial-time
algorithm addresses is a polynomial in the length, and a table of size $|x|^2$, such as the
adjacency matrix of a graph read off the word, must fit. Entries are not bounded by the length
in general: a due date may be any number at all, so quantifying over the entries is what
makes a claim about them honest instead of silently assuming they are small.

The bound is $c\,g(k)\,(|x|+1)^c$, elementary rather than asymptotic, with the $+1$ making it
meaningful on the empty word. The length enters through a polynomial, the usual form of
fixed-parameter tractability, and not linearly: a linear bound would be strictly stronger than
the notion the source uses, and would not hold for the algorithms the source cites, such as
Lenstra's, whose dependence on the length is polynomial and not linear (nor for an algorithm that
first builds a graph from the word, which takes more than linear time in the word). `g` is an arbitrary function of the parameter: it bounds a
fixed program's running time rather than defining it, so no computability requirement on
`g` is needed or intended.

An *fpt-reduction* from `P` to `Q` is a map `f` on words, computed by one program within
$c\,g(k)\,(|x|+1)^c$ instructions, that sends admissible words to admissible words, preserves the
answer, and raises the parameter by at most a function of the old parameter. The program is
required to run on the admissible words that fit *and whose image fits*: the image of a word may
be exponentially longer than the word (a parameter-sized table), and a machine whose word length is
only logarithmic in the input cannot address it, exactly as a decision procedure is only required to
run on the words that fit. This is the notion that splits a fixed-parameter tractability proof into
a reduction, proved here, and a cited algorithm for the target problem.
-/

namespace Lax117284.ParameterizedComplexity

open Lax808846.Ram Lax808846.RamComputes

/-- A parameterized problem: the words that encode an instance, which of them are
yes-instances, and the parameter each one carries. -/
structure Problem where
  /-- The words that encode an instance. A program may do anything on the others. -/
  Domain : Set (List ℕ)
  /-- The yes-instances. -/
  Yes : List ℕ → Prop
  /-- The parameter, a function of the word. -/
  param : List ℕ → ℕ

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

/-- `P` is **fixed-parameter tractable**: one program and one constant decide it within
`c * g k * (|x| + 1) ^ c` instructions, for some function `g` of the parameter alone. -/
def FPT (P : Problem) : Prop := ∃ (prog : Program) (c : ℕ) (g : ℕ → ℕ), Decides P prog c g

/-- The map `f` is an **fpt-reduction** from `P` to `Q`, computed by `prog` within
`c * g k * (|x| + 1) ^ c` instructions on the admissible words that fit and whose image fits,
and raising the parameter to at most `h k`. -/
structure IsFptReduction (P Q : Problem) (f : List ℕ → List ℕ) (prog : Program)
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

/-- `P` **fpt-reduces** to `Q`. -/
def FptReduces (P Q : Problem) : Prop :=
  ∃ (f : List ℕ → List ℕ) (prog : Program) (c : ℕ) (g h : ℕ → ℕ),
    IsFptReduction P Q f prog c g h

@[inherit_doc] infix:50 " ≤fpt " => FptReduces

end Lax117284.ParameterizedComplexity
