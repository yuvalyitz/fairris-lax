# Fair repetitive interval scheduling

A [Lax archive](https://github.com/lax-archive/lax) submission (`lax-117284`) formalizing
Heeger, Hermelin, Itzhaki, Molter and Shabtay, *Fair repetitive interval scheduling*,
Algorithmica (2025): each of `n` clients submits one job on each of `m` days, jobs are
just-in-time, and every client must be served on at least `k` days. The submission states the
paper's theorems, proves every construction correct, and proves the running times of the
reductions and of the algorithms as programs for the word RAM. See `abstract.md` for the
mathematics.

**Status: complete.** Every statement is proved, with no `sorry`, and no result of the
literature is cited: the results that the paper takes from elsewhere are proved here or in the
sibling submissions listed under Dependencies.

| Result taken from the literature | Proved in |
|---|---|
| 2-SAT is in P (Aspvall, Plass, Tarjan 1979) | `TwoSAT/` |
| A nice tree decomposition of small width in fixed-parameter time (Bodlaender 1996, Kloks 1994) | `lax-689794`, through `BodlaenderProved.lean` |
| The integer programs of Theorem 4 are solved in fixed-parameter time (the paper cites Lenstra) | `IlpClients/`, `Machine/Ilp*.lean`: the programs of the family have a fixed constraint matrix, and a guess-and-verify algorithm solves them, so Lenstra's algorithm is not needed |
| Bounded-occurrence 3-SAT is NP-hard (Tovey 1984) | `lax-345332`, through `BoundedSatProved.lean` |
| Multicoloured Independent Set is NP-hard on regular instances | `McisHard/`: from bounded-occurrence 3-SAT, through the occurrence graph, a regularisation gadget and a copy of the graph for every clause |
| Hitting Set is NP-hard (Karp 1972), and hardness of interval scheduling with eligible machine sets | `lax-496464` and `lax-470956` |

Besides Lean's three standard axioms, the 84 proofs depend only on statements of other archive
submissions: the Cook–Levin theorem and the encoding of formulas of `lax-429075`
(`Lax429075.SATHard.hardness`, `Lax429075.EncodingCorrect.roundtrip`), the equivalence of word RAM
and Turing machine polynomial time of `lax-759944`
(`Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime`), and the hardness of
interval scheduling with eligible machine sets of `lax-470956` (`Lax470956.Theorem2.npHard_allSchedulable`).

Several statements of the first draft were false or vacuous as printed — a running-time bound
that is `0` at the empty word, an empty word admitted at word length `0`, a decoder applied to
a word one entry too long, so that every instance decoded to the empty one — and were repaired;
the formalization notes of the affected concept modules record each repair.

## Prerequisites

Lean `v4.33.0` via [elan](https://github.com/leanprover/elan), and the
[`lax` CLI](https://github.com/lax-archive/lax). The mathlib revision is pinned in
`manifest.yaml`; Lake fetches it on first build.

## Verifying it

The one command that checks everything:

    lax build .

Its last stage, *Inspecting the statements*, pairs every statement with its proof and reports
`38 concepts · 84 proofs`. The proofs cite statements of the sibling submissions `lax-470956`
(interval scheduling with eligible machine sets), `lax-496464` (Hitting Set), `lax-689794`
(treewidth) and `lax-345332` (bounded-occurrence satisfiability), and require the scanner of
`lax-391470`, none of which is registered yet, so until then the build has to admit them as
sibling checkouts and drafts:

    lax build . --nonstrict

(`lax build` rewrites `proofs/lake-manifest.json`, which is not tracked, turning the `lax-391470`
entries into path entries; a plain `lake build` afterwards still succeeds.)

The full build takes a while; on a machine with limited memory, cap Lake's parallelism, for
example `LEAN_NUM_THREADS=2 lake build` from `proofs/`, or it will start one Lean process per
core.

To audit axioms yourself, write a scratch file **outside** the package:

    cat > /tmp/ax.lean <<'LEAN'
    import Lax117284Proofs
    #print axioms Lax117284Proofs.Theorem4Clients.fpt_byClients
    #print axioms Lax117284Proofs.TreewidthReal.fpt_byDaysAndTreewidth
    #print axioms Lax117284Proofs.McisHard.normalMulticolouredIndepSet_npHard_proved
    LEAN

and run `lake env lean /tmp/ax.lean` from `proofs/`. The first two depend on the three standard
axioms only; the third adds the three axioms of `lax-429075` and `lax-759944` named above. Each
concept is discharged by a proof whose docstring carries `conclusion: <that concept>`; a
theorem that uses a concept of this submission shows it in `#print axioms` until that proof is
substituted, which is why the audit is best run on the tagged proofs themselves.

> Anything placed inside `proofs/Lax117284Proofs/` must also be imported by
> `Lax117284Proofs.lean`, or the build is rejected. Keep scratch work elsewhere.

## Reading it

Read `concepts/` and let the build vouch for `proofs/`: about 3,400 lines of statements
against about 88,000 lines of proof. Lean's kernel checks the proofs; only a reader can judge
whether the statements say what they claim. The statements are grouped by theorem
(`Theorem1.lean` … `Theorem13.lean`, `Lemma14.lean`, `Lemma15.lean`, `Corollary8.lean`),
with the shared definitions in `Scheduling.lean`, `Problems.lean`, `InstanceEncoding.lean`
and `ParameterizedComplexity.lean`.

Suggested order:

1. `abstract.md` — the argument in prose.
2. `concepts/Lax117284/Scheduling.lean` — instances, feasibility, fairness.
3. `concepts/Lax117284/Problems.lean` and `ParameterizedComplexity.lean` — how a problem
   is a language of words, and what polynomial time and fixed-parameter tractability mean.
4. The theorem files, in the order of the paper.
5. `concepts/Lax117284/TwoSat*.lean` — 2-satisfiability, self-contained: 2-CNF as a restriction of
   the formulas of `lax-429075`, the implication graph, the criterion of Aspvall, Plass and
   Tarjan, the algorithm by breadth-first searches, its correctness, its running time
   `c · (|x| + 1) · (v + 1)` on the word RAM, and 2-SAT ∈ P.
6. `concepts/Lax117284/Bipartite*.lean` — bipartite matching, self-contained: a graph split at
   `n` on Mathlib's graphs, in the compressed sparse row word of `lax-271696`, Kuhn's algorithm,
   its correctness (a maximum matching, the matching number), its running time
   `c · (n + 1) · (|x| + 1)`, and the decision of saturating and perfect matchings, also on
   every word and as polynomial time in the sense of `lax-759944` (`BipartiteDecision`), which
   is what Theorem 2's unit-time algorithm composes with.

In `proofs/`, the correctness of each construction is in its own files (`Theorem7*.lean`,
`Lemma14*.lean`, `Lemma15*.lean`, `Theorem11*.lean`, `Corollary8*.lean`, `Theorem12_DP.lean`,
`Theorem4ILP.lean`, `Theorem4TreewidthDP.lean`, ...), the running times are word-RAM programs
under `Machine/` (reductions, the fixed-day dynamic program `D3*`, the unit-time matching
reduction `U*`, whose second stage (`Match*`) converts its table into the compressed sparse row
word on which the bipartite matching decider of `Bipartite/` answers, the client-parameter
program `Cl*` and the reduction to
integer programming `ClRed*` that `Theorem4_ClientsReduction.lean` assembles, the treewidth program `Tw*`), and each theorem is assembled in the file named after it.
The 2-SAT development is under `TwoSAT/` (`Math/`, `Bridge.lean`, `Correct.lean`, and the program
under `TwoSAT/Machine/`) and the bipartite matching development under `Bipartite/` (`Matching.lean`,
`Maximum.lean`, `KuhnCorrect.lean`, `GraphBridge.lean`, the program under `Bipartite/Ram2/`, and
`Machine.lean`/`MachineTotal.lean` for the running-time statements).

## Layout

    manifest.yaml     id, title, authors, pinned Lean + mathlib, bibliography
    abstract.md       the prose account, rendered on the archive website
    concepts/         statements only, as axioms — 38 modules
    proofs/           the proofs, each tagged with the statement it discharges — 462 modules

A concept module states results as `axiom`s. A proof is a `theorem` whose docstring carries
`conclusion: <that axiom's full name>`; the build checks the pairing.

## Dependencies

Beyond mathlib, this submission builds on other archive submissions:

- `lax-434930`, *Classical Complexity Classes* (Édouard Bonnet): P and NP.
- `lax-429075`, *The Cook–Levin Theorem* (Édouard Bonnet): CNF formulas and polynomial
  many-one reductions.
- `lax-808846`, *The Word RAM* (Jan Dreier): the machine model, the IMP+ language and its
  verified compiler.
- `lax-759944`, *Computability and polynomial-time equivalence of Turing machines and word
  RAMs* (Szymon Toruńczyk).
- `lax-228581`, *Twin-width can be exponential in treewidth* (Édouard Bonnet, Jan Dreier,
  Claude): treewidth.
- `lax-271696`, the compressed sparse row encoding of a graph for the word RAM (the bipartite
  matching modules).
- `lax-470956`, interval scheduling with eligible machine sets: the hardness of the problem that the
  just-in-time hardness reduces from, and multicoloured cliques. A draft at the time of writing.
- `lax-496464`, just-in-time scheduling in two-stage flexible flow shops: Hitting Set and its
  NP-hardness, the source of the reduction of `FromHittingSet`. A draft at the time of writing.
- `lax-689794`, treewidth: Bodlaender's algorithm on the word RAM, proved there, from which
  `BodlaenderProved.lean` derives the statement used here. A draft at the time of writing.
- `lax-345332`, Tovey's bounded-occurrence satisfiability, proved there and identified with
  `BoundedSat` in `BoundedSatProved.lean`. A draft at the time of writing.
- `lax-391470`, *Scheduling with two non-unit job lengths is NP-complete* (Yuval Itzhaki,
  Claude): its verified scanner of an encoded formula and its transfer of a RAM computation to a
  Turing machine (the 2-SAT modules). A draft at the time of writing; the build warns
  (`draft-dependency`) until it is registered.

Several packages are required with their proofs, and the build warns about each
(`proof-dependency`): none of the results used from them is stated as a statement of its
submission, so there is nothing to cite instead.

The archive itself is described in `lax-242665`, *An Introduction to Lax* (Édouard Bonnet,
Jan Dreier, Clemens Kuske).

## License

Apache 2.0, as required by the archive. See `LICENSE`.
