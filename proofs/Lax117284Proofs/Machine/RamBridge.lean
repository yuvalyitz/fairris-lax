import Lax808846.RamComputes
import Lax759944.RamPolytime
import Lax759944Proofs.Encoding

/-!
From a running-time statement in the archive's word RAM style to the polynomial-time
predicate of the RAM/Turing equivalence.

The two say the same thing in different currencies. `Lax808846` measures the input by
its length as a list of numbers and states an explicit bound at every word length that
admits the input; `Lax759944` measures it by its bit size, prefixes the physical input
with its length, and asks for a polynomial. This file converts one into the other once,
so that a program written and costed in the first style can be cited in the second.
-/

namespace Lax117284Proofs.Machine.RamBridge

open Lax808846.Ram Lax808846.RamComputes
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax759944Proofs.Encoding

end Lax117284Proofs.Machine.RamBridge
