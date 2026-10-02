# Fair Repetitive Interval Scheduling

A [Lax archive](https://github.com/lax-archive/lax) submission (`lax-117284`) formalizing
Heeger, Hermelin, Itzhaki, Molter and Shabtay, *Fair Repetitive Interval Scheduling*,
Algorithmica (2025): each of `n` clients submits one job on each of `m` days, jobs are
just-in-time, and every client must be served on at least `k` days. The submission states the
paper's theorems, proves every construction correct, and proves the running times of the
reductions and of the algorithms as programs for the word RAM. See `abstract.md` for the
mathematics.

The development contains 41 concepts and 86 tagged proofs. Supporting results are proved
locally or supplied by the archive dependencies listed below. Final archive validation
requires all external dependencies to be registered and pinned to their registered commits.

| Result taken from the literature | Proved in |
|---|---|
| 2-SAT is in P (Aspvall, Plass, Tarjan 1979) | `TwoSAT/` |
| A nice tree decomposition of small width in fixed-parameter time (Bodlaender 1996, Kloks 1994) | `Treewidth/` (the exact dynamic program of Bodlaender and Kloks on the word RAM), through `BodlaenderProved.lean` |
| The integer programs of Theorem 4 are solved in fixed-parameter time (the paper cites Lenstra) | `IlpClients/`, `Machine/Ilp*.lean`: the programs of the family have a fixed constraint matrix, and a guess-and-verify algorithm solves them, so Lenstra's algorithm is not needed |
| Bounded-occurrence 3-SAT is NP-hard (Tovey 1984) | `lax-345332`, through `BoundedSatProved.lean` |
| Multicoloured Independent Set is NP-hard on regular instances | `McisHard/`: from bounded-occurrence 3-SAT, through the occurrence graph, a regularisation gadget and a copy of the graph for every clause |
| Hitting Set is NP-hard (Karp 1972), and hardness of interval scheduling with eligible machine sets | `lax-496464` and `lax-888481`, through `JitHard/Sat34Wired.lean` |

The hardness arguments use the archive's Cook–Levin theorem and CNF encoding
(`lax-429075`), the equivalence of word RAM and Turing-machine polynomial time
(`lax-759944`), and the registered Tovey and ISEM developments. The bridge in
`JitHard/Sat34Wired.lean` composes their proofs for the scheduling reduction.
The archive's proof network records the declared assumptions and their proofs.

The concept pages explain the encoding conventions, boundary cases, and the placement
of inactive jobs used to preserve the conflict graph in the treewidth construction.

## Prerequisites

Lean `v4.33.0` via [elan](https://github.com/leanprover/elan), and the
[`lax` CLI](https://github.com/lax-archive/lax). The mathlib revision is pinned in
`manifest.yaml`; Lake fetches it on first build.

## Verifying It

For archive validation, run:

    lax build .

Every dependency is pinned to a git commit: ISEM (`lax-888481`), Tovey (`lax-345332`) and
RJLMax (`lax-391470`) are registered; flexflowjit (`lax-496464`) is pinned to its submitted commit
and `lax build .` reports it as a draft dependency until it is registered.

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

## Reading It

Start with `concepts/` for the statements and their hypotheses. Lean's kernel checks
the proofs; the definitions and hypotheses still require mathematical review. The statements are grouped by theorem
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
The algorithm of Bodlaender and Kloks for nice tree decompositions of small width is under
`Treewidth/`, with the concepts `GraphWords` (graphs and nice decompositions as words),
`BodlaenderKloks` (the improvement step) and `BodlaenderGeneral` (Bodlaender's theorem for an
arbitrary graph). It is the exact dynamic program over characteristics of partial decompositions,
not the linear-time algorithm of the paper: `Seq/`, `Trees/`, `Chars/` and `Wrap/` prove its
correctness, `Size/` bounds the tables, and `Fun/` runs the Lean functions themselves on a
verified virtual machine and transfers the runs to the word RAM (`Fun/Final.lean`). The concept
`Bodlaender` of Theorem 4 is the case of the overall conflict graph and is derived from
`BodlaenderGeneral` in `BodlaenderProved.lean`.

## Layout

    manifest.yaml     id, title, authors, pinned Lean + mathlib, bibliography
    abstract.md       the prose account, rendered on the archive website
    concepts/         statements only, as axioms — 41 modules
    proofs/           the proofs, each tagged with the statement it discharges

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
- `lax-888481`, interval scheduling with eligible machine sets: the hardness of the problem that
  the just-in-time hardness reduces from, imported and composed (not cited as an axiom) in
  `JitHard/Sat34Wired.lean`. Registered as the successor of `lax-470956`.
- `lax-496464`, just-in-time scheduling in two-stage flexible flow shops: Hitting Set and its
  NP-hardness, the source of the reduction of `FromHittingSet`. Registered.
- `lax-345332`, Tovey's bounded-occurrence satisfiability, proved there and identified with
  `BoundedSat` in `BoundedSatProved.lean`; also, through `JitHard/Sat34Wired.lean`, the source of
  the `(3,4)`-SAT hardness `lax-888481`'s reduction needs. Registered.
- `lax-391470`, *Scheduling with Two Non-Unit Job Lengths Is NP-Complete* (Yuval Itzhaki,
  Claude): its verified scanner of an encoded formula and its transfer of a RAM computation to a
  Turing machine (the 2-SAT modules). Registered.

Several dependencies include proof packages to reuse verified implementations and
compose proofs. Lax reports these requirements as `proof-dependency` warnings.

The archive itself is described in `lax-242665`, *An Introduction to Lax* (Édouard Bonnet,
Jan Dreier, Clemens Kuske).

## License

Apache 2.0, as required by the archive. See `LICENSE`.
