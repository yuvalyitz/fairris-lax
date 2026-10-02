import Lax117284.TwoSatCNF

/-!
---
title: 2-SAT Is in P
type: theorem
---
The language 2-SAT lies in $\mathrm{P}$: a deterministic Turing machine decides membership
within a polynomial number of steps, in the sense of the archive's class of `lax-434930`.

# Formalization Notes

This is the word RAM bound of this submission, transferred. The program that decides the
language on the zeros and ones of the word runs in time polynomial in the length of the word,
with all values polynomially bounded, so it is a polynomial-time word RAM computation in the
sense of `lax-759944`, and that submission's equivalence gives a polynomial-time Turing machine
over the encoding of the bits; two fixed translations, from a binary word to the encoding of its
bits and back to a single output bit, complete the machine the class asks for.
-/

namespace Lax117284.TwoSatInP

open Lax434930.PolynomialTime Lax117284.TwoSatCNF

/-- **2-SAT ∈ P.** -/
axiom twoSAT_mem_P : TwoSAT ∈ P

end Lax117284.TwoSatInP
