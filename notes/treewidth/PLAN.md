# PLAN — discharging `improveDecomposition` and `niceDecomposition_computable` (lax-117284)

Architect's blueprint.  Companion files (all new, nothing existing touched):

* `blueprint/BP1…BP7*.lean` — the definitions and *all key statements* in Lean (proofs are `sorry`); they compile
  (`sh blueprint/build.sh BP1_Seq.lean BP3_Chars.lean BP4_Tables.lean BP5_Extract.lean BP6_Count.lean BP7_Machine.lean`;
  BP2 needs only the concept packages).  Kept outside the proofs package.
* `reference/*.py` — an executable reference implementation of exactly the algorithm of BP3–BP5 and a test harness
  against brute-force treewidth.  **It found two real errors in my first version of the algorithm** (§i) — the
  algorithm below is the corrected, tested one.

## 0. Verdict in five lines

1. The exact route (Bodlaender–Kloks, corrected and made explicit) is **feasible but large: ≈ 100 k lines** of
   Lean (range 80–140 k): ≈ 45 k pure mathematics (of which ≈ 5 k is the sequence layer already done by another
   agent), ≈ 55 k for the word-RAM layer.  That is about **2× a FairRIS-scale effort** (FairRIS `Machine/` alone is 43 k).
2. The paper's treewidth section (§5–§6) is *not* a proof: I list 20 gaps (§f); the two that mattered were found
   only by running the algorithm (§i).  The mathematics is nevertheless sound — ≈ 4 500 exhaustive/random/structured
   test instances agree with brute force (§i).
3. **Only the vertex-by-vertex wrapper with ℓ = k+1 is ever executed by the machine**; `improveDecomposition` for
   arbitrary ℓ follows from it by ignoring the given decomposition (§e.4) — so the machine layer has *one* parameter.
4. Soundness needs **no** "repair" lemma (paper Lemma 4.5): a dominance-based formulation + two new sequence
   lemmas (numerically verified, requested from `Seq/`) replaces it.  Extraction *is* the soundness proof.
5. The three biggest risks: the exact-layer introduce lemma (`char_intro_dom`), the RAM extraction (real trees),
   and the two bridges (`RT ↔ TreeDecomposition`, `NT ↔ NiceDecomposition` word with its `IsTree` proof).

---------------------------------------------------------------------------------------------------------------

## (a) Definitions and representations chosen — and why

| object | representation | why |
|---|---|---|
| graph | `Adj := ℕ → ℕ → Bool`, denoting `SimpleGraph ℕ` by `fromRel`; concept graphs (`Fin n`) lifted along `Fin.val` (`liftGraph`) | computable adjacency for the algorithm; vertices are naturals, so bags are `Finset ℕ` and never carry a `Fin n` proof |
| decompositions | `inductive RT | node (bag : Finset ℕ) (kids : List RT)`; validity **recursive** (`RT.Conn`, `IsTD`, `Width`) | every surgery of the algorithm (join, add a vertex to a region, cut a chain, duplicate a node, prune, hang a leaf) is a structural operation; no node type, no `SimpleGraph` tree, no isomorphism.  `Conn` says: below a child, a vertex of the parent bag sits in the child's root bag; a vertex not in the bag occurs below ≤ 1 child |
| nice trees | `inductive NT | leaf | intro v c | forget v c | join a b`, bags *computed* (as in the word format); `NT.Good adj` = shapes + *closedness* (a vertex is introduced with all its already-present neighbours in the bag) + *separation* (join sides meet in the bag) | these are exactly the two properties of a nice TD the DP uses; both are consequences of validity (`good_of_isNiceTD`) |
| **bridge 1** | `hasTreewidthAtMost_iff_rt : HasTreewidthAtMost G w ↔ ∃ t : RT, t.IsTD (liftGraph G) (range n) ∧ t.Width w`, and induced-subgraph monotonicity | the *only* place `Lax228581.TreeDecomposition` appears; used for the negative answer of the concept statement. (→) roots the abstract tree (induction on the number of nodes by removing a leaf; `Conn` from the connectedness of the induced subgraphs); (←) nodes-as-paths |
| **bridge 2** | `NT.encode`, `niceDecomposition_encode` (output) and `niceDecomposition_parse` (input) against `GraphWords.NiceDecomposition` | the *only* place the word format appears.  The encoding is a post-order listing, first child immediately before its parent, second child of a join by index (`recs`); the proof obligations are those of the structure (`length_eq`, `shape`, `parent`, `isTree`, `covers`, `edges`, `connected`, `width`) |
| **characteristic** | `inductive CT | node (S : Finset ℕ) (y : List ℕ) (kids : List CT)` — a **rooted tree of runs**: a run = a maximal chain of tree nodes with the same restricted bag `S = bag ∩ B`, `y` = typical sequence of the bag sizes along it, `kids` hang below its last node, in canonical order | see below |

**Why rooted run trees rather than the paper's trunk/tree model.**  The paper's tree model is an *unrooted* tree
(trunk with degree-2 nodes suppressed, interval model + typical list per edge) compared "for equality" in joins.
Formalising that means graph isomorphism of labelled trees, or canonical forms of unrooted trees.  I instead
**root every partial decomposition at its origin** (the root of the `RT`, never pruned): all of the
operations act on decompositions on *one tree* and keep the root; a join identifies the two roots.  The
characteristic is then a canonically ordered rooted tree: kids are sorted by the least vertex they *own*
(`key S k = min (verts k ∖ S)`), which are distinct and non-empty by connectedness (a non-root leaf owns a private
vertex).  Equality of characteristics is structural equality, `joinC` is a structural zip, `norm` a structural
recursion.  (Rejected alternatives: unrooted + canonical DFS from the leaf with the smallest private vertex;
split systems of the leaves; chordal-graph states; elimination-ordering states.)

**Normal form** `norm` (this is the paper's "core + compact representation", made total):
(i) drop a leaf run whose label ⊆ its parent's; (ii) merge a run with its only kid if they have the same label
(`τ` of the concatenation); (iii) a run without kids keeps only its first entry (**correction found by the
reference**: the further nodes of a leaf chain are junk leaves); kids sorted by `key`.

Shape invariants `CT.Wf B kmax`: labels ⊆ `B`, `⋃ labels = B`, typical & ≥ `|S|` entries, leaf runs have one
entry, no prunable leaf kid, single-kid runs change label, kids strictly ordered by key, connected occurrences
(`CT.Conn`), entries ≤ `kmax = k+1`.

---------------------------------------------------------------------------------------------------------------

## (b) The mathematics, at statement level

Everything is in `BP3`–`BP5` with the exact Lean statements.  Notation: `char B t = norm (prof B t)` where
`prof B` replaces every bag `X` by the run `(X ∩ B, [|X|])` (un-normalised); `DomC a b` (`a` at least as good as
`b`) = same shape and run-wise `Seq.Dom`.

### b.1 Tables (algorithm A, BP4)
`tables adj k : NT → List CT` — leaf `[start]`; forget: `forgetC x`; introduce: `introC (k+1) v (nbrs v bag)`;
join: `joinC (k+1)` over all pairs; each deduplicated.  **No dominance pruning** (not needed for correctness or
counting; the reference shows it cuts tables ≈ 2×, it is an optimisation).

### b.2 The three ingredients per node kind
| layer | statement (BP4) | content |
|---|---|---|
| exact | `char_leaf`, `char_forget` (equality), `char_join_dom`, `char_intro_dom` | how the characteristic of a *real* tree relates to those of its restrictions |
| typical | `forgetC_mono`, `joinC_mono`, `introC_mono` | the typical-level operations are monotone for `DomC` |
| realisation | `realize_intro`, `realize_join` (BP4), `applyPlan_spec`, `mergeReal_spec` (BP5) | real trees realising typical results (soundness) |

* **forget** — the tree is unchanged, `B ↦ B∖x`: `norm (relabel f (norm p)) = norm (relabel f p)` (confluence of the
  normal form: pruned leaves stay prunable, equal labels stay equal; proof by structural induction with a one-step
  invariance lemma `Rewrite p p' → norm p = norm p'`).
* **join** — both restrictions live on the same tree; pruning and merging depend only on labels, so the two exact
  chars have the same shape and the exact join is the run-wise *pointwise sum of equal-length exact sequences minus
  `|S|`*; the sizes of the junk are dropped (a hidden constraint at junk nodes present in both sides is harmless: on
  realisation the junk of the two sides is disjoint).  Then `τ(a+b) ⪰` an element of `τa ⊕ τb` (Lemma 3.14).
  `joinC_mono` is Lemma 3.13 per run; `realize_join`: lattice path over the *exact* sequences whose `τ`-sum is
  dominated (`Seq.ringSum_realise`, NEW), nodes paired along the path, junk of both sides hung at the first paired node.
* **introduce** — let `W` be the region of `v` in the real tree.  Case (a) `W` meets the core: `W ∩ core` is
  connected, so it cuts each run in an interval (prefix if the parent is in `W`, suffix/whole if kids are, arbitrary
  if it is the top run); junk in `W` becomes prunable again (`S_junk ∪ {v} ⊆ S_parent ∪ {v}`) — plans `winPlans`,
  `wtopPlans`.  Case (b) `W` lies in a junk subtree hanging at a core node `x`: the nested bags from `x` down to
  `W` become a **branch of nested labels** `S_x ⊇ M₁ ⊋ … ⊋ M_r ⊇ M ⊇ N` ending in a leaf `M ∪ {v}`
  (`attachPlans`; *all* nested chains are needed, §f G6).  `char_intro_dom` = the case analysis + `Seq.split_transport_up`;
  `introC_mono` = same transport lifted along plans; `realize_intro` = `Seq.split_transport_down` (cut the exact chain at
  the witnesses of its typical sequence: a first-type cut duplicates a node, a second-type cut puts the entries
  between two witnesses on the side where they are dominated) + surgery on the tree.
* **start** — `start = node ∅ [0] []`; all bags empty ⇒ `norm` collapses to it (`char_leaf`).

### b.3 Correctness (BP4, BP5)
* `tables_complete : nt.Good adj → ∀ t, PTD adj nt k t → ∃ c ∈ tables adj k nt, DomC c (t.char nt.bag)` — induction on
  `nt`: forget by `forgetC_mono` + `char_forget`; join by `char_join_dom`, restrictions, `joinC_mono`, transitivity;
  introduce by `char_intro_dom`, `introC_mono`.
* `extract_spec : c ∈ tables adj k nt → ∃ t, extract adj k nt c = some t ∧ PTD adj nt k t ∧ DomC (t.char nt.bag) c` —
  **soundness = extraction** (§c).
* `tables_ne_nil_iff : tables adj k nt ≠ [] ↔ ∃ t, PTD adj nt k t`, hence at the root: `tables ≠ [] ↔ tw(G) ≤ k`.
* `improve_correct`, `decompose_correct`, `decompose_words` (BP5): the two algorithms; `decompose_words` is the
  statement of the concept, on `SimpleGraph (Fin n)` and words.

### b.4 What the sequence layer must provide (BP1)
From `Seq/` (all already proved, per its README): `typical`, `Ext`, `Dom`, `RingSum`, `ringTyp`, `splits`, Lemmas
3.2, 3.3, 3.5, 3.13, 3.14, 3.17–3.20, `domB`.  **New, requested** (BP1): `split_transport_up`,
`split_transport_down`, `ringSum_realise` — checked numerically (`/tmp` script quoted in §i: all `typical` sequences
over `{0..3}` of length ≤ 5 against random exact sequences, both directions, both split types: 0 counterexamples).

---------------------------------------------------------------------------------------------------------------

## (c) The algorithm as computable functions; extraction

**Phase A** = `tables` (above).  **Phase B** = `extract adj k nt c` (BP5): top-down over a derivation of the chosen
root entry, bottom-up construction of a real `RT` *whose actual characteristic is dominated by the chosen entry*:

* leaf — one empty node; forget — the same tree;
* introduce — analyse the realiser's actual characteristic (`analyze`: runs with their node lists and exact
  sizes); among `introPlans v N (char B t)` take the first whose normalised result is `domCB`-dominated by the target
  (existence: `introC_mono` + `realize_intro`); `applyPlan` cuts/duplicates/adds `v`/hangs the branch;
* join — per run a monotone lattice path over the two *exact* size sequences with `τ`-sum dominated by the target
  (DP with back-pointers, state = `(i, j, τ-prefix)`), then `mergeReal`.

This replaces the paper's pointer structures (§6): time is polynomial, not linear (the paper's linear-time
extraction is not needed).  Then `niceOf` (Kloks, BP5) and `NT.encode`.

**Why dominance and not exactness.**  An exact realiser for a table entry would need the paper's Lemma 4.5 (raise
bags by adding vertices from a neighbour so that the exact sizes become an extension of the typical sequence) after
*every* operation.  With `Dom`-based invariants the realiser's exact sequences are arbitrary; existence of the
next step is proved by the transport lemmas (which are the completeness arguments run backwards).  Tested: in the
reference every `realize` step asserts `dom_char(actual, target)`; 0 failures in ≈ 3 400 runs.

**Vertex-by-vertex wrapper (T2, BP5 `decompose`)**: `G_i = G[0..i-1]`; keep a nice TD of `G_i` of width ≤ k;
`NT.addEverywhere i` (an introduce node above every leaf; nothing else changes since bags are computed from the
leaves) gives a nice TD of `G_{i+1}` of width ≤ k+1 (`addEverywhere_isNiceTD`); `improve … k` returns width ≤ k or
`none`, and `none` at round `i` proves `tw(G) > k` by `hasTW_mono` (induced subgraphs).  Round `i` takes
`T1(n = i)`; `n` rounds are polynomial.  (The paper's route through Bodlaender's `2k+1` reduction is not used.)

---------------------------------------------------------------------------------------------------------------

## (d) Counting: `2^{O(ℓ³)}`

`Wf.count_le : count ≤ (2b+2)²` for a boundary of `b` vertices (non-root leaf runs own a private vertex, ≤ b;
branching runs ≤ leaf runs; a downward path of single-kid runs changes its label at every step and each vertex
enters and leaves once: ≤ 2b+1 runs per path).  Measured maxima over all table entries of ≈ 90 instances
(`b = 2,3,4,5`): 5, 8, 10, 10 runs; ≤ b leaf runs; ≤ b−1 branching; longest single-kid path 2b−1 — consistent.
A tree of ≤ M runs is a parent array (`M^M`), a label per run (`2^{bM}`), a typical sequence per run over `{0..kmax}`
(`≤ (8/3)4^{kmax}`, Lemma 3.5): `log₂ ≤ M(log₂ M + b + 2kmax + 2) ≤ 16(b+1)²(b+kmax+2)`.
`charBound b kmax = 2^{16(b+1)²(b+kmax+2)}`; for `b = ℓ+1`, `k < ℓ`: `≤ 2^{720 ℓ³}` (`charBound_le`).  Tables are
duplicate-free, so `|tables| ≤ charBound` (`tables_length_le`, needs `tables_wf`: **`Wf` is preserved by the three
operations** — one lemma per operation, the connectedness clause being the laborious part).

---------------------------------------------------------------------------------------------------------------

## (e) Machine layer (BP7)

### e.1 Encoding and tables
A characteristic over the sorted bag list has a **bit-packed code** (`codeOf`, BP7): runs in preorder, each with
parent index, label mask over bag positions, sequence length and entries.  `< 2^{64(b+1)²(b+kmax+2)}` — under the concept's
word-length hypothesis (`c·2^{cℓ³}·(|x|+v+1)^c ≤ 2^W`) **a characteristic is one word and a table is an addressable bit
array indexed by code** (address = `node·N + code` with `N = 2^{64(ℓ+2)²(ℓ+k+3)}`).  This is precisely what the
hypothesis of the concept statements buys.  Deduplication is then free (mark array).

### e.2 Loop structure (naive on purpose)
For each node of the nice word, in word order (children first): **forget** — loop over all codes present in the child
table, decode to run arrays, apply `forgetC`, encode, set flag: `N·poly(ℓ)`.  **introduce** — for each source code and each *plan number*
(a mixed-radix counter over per-run statuses `{out, whole, end at cut c, top with pre-cut, attach at cut c with chain
number}`; the status-vector form of `introPlans`, to be proved equal to the nested-plan form as the first step of
the introduce WP), validity check, apply, normalise, encode: `N·2^{O(ℓ²)}`.  **join** — a *triple* loop over (source code `a`, source code `b`, target code `c`), each triple checked run by run
(shape equality, and per run membership of `c`'s sequence in the lattice DP of `ringTypList`, entries ≤ `kmax`): the product over runs
is never enumerated.  `N³·poly(ℓ) = 2^{3·720ℓ³}·poly`, absorbed by the constant `c` of the statement.  Total tables: `|D|·N³·poly(ℓ)`.
The concept bound `c·2^{cℓ³}(|x|+2)^c` is met with `c ≥ 3·720 + O(1)`.

### e.3 Extraction on the RAM
An arena of real trees (append-only arrays `abag[node·(k+2)+slot], apar, achild-lists`): `analyze` (bottom-up pruning,
runs with node lists and exact sizes) is `O(size·poly)`; `applyPlan` and `mergeReal` are `O(size + path DP)`
(`|a|·|b|·2^{2k}` states per run pair); the derivation search scans tables (`N` or `N²` per node).  Tree sizes stay
polynomial: each operation adds `O(ℓ²)` nodes, a join adds at most the path length.  Output: `niceOf` (linear in the
arena) + `NT.encode`.

### e.4 T1 for *arbitrary* ℓ from T2 (a simplification)
`improveDecomposition` quantifies over all `ℓ`; the machine never runs `improve` on a given decomposition of
large width.  The T1 program is T2's IMP+ command behind one `ite` (`wDispatch`, BP7): if `ℓ ≤ k`, output `1 :: D` (the given
decomposition already has width `ℓ ≤ k`); otherwise run T2 on `g ++ [k]` and ignore `D`.  T2's specification is stated
on *all* inputs (it reads the graph word by its length header and `k`, nothing after), so no black-box simulation of a
program is needed.  Time and guard are dominated by those of T2 (`k < ℓ`, `|g ++ [k]| ≤ |input|`).  So **the machine layer has the single parameter `k`** (`ℓ = k+1` inside T2), and the concept's
`improveDecomposition` is a corollary of `niceDecomposition_computable` (BP7 `T1_of_parts` (`dispatch_solves`)).
(The mathematical `improve` for arbitrary ℓ is still proved: it costs nothing extra.)

### e.5 The wrapper on words
`prefixGraphWord g i` (first `i` rows/columns), `addEverywhereWord` (a `(1,v,0)` record above each leaf record,
`oth` indices shifted; `encode_addEverywhere` connects it to `NT.addEverywhere`), and the loop over `i`.
Guard bookkeeping: every value the program holds is `≤ |D|·N + n + …`, which the guard bounds.

### e.6 A shortcut worth considering for the machine layer
Because every operation is a *pure list function on small structures*, a verified compiler for a first-order
functional fragment (lists, bounded folds, `Finset`-free arithmetic) into IMP+ would replace most of WP-M1…M5 by
`by simp`-level cost lemmas; it costs ≈ 12–15 k lines once and halves the rest.  Risky (it is a compiler); listed as a
decision for the user (§g).

---------------------------------------------------------------------------------------------------------------

## (f) Gaps in the paper, by lemma

(BK = Bodlaender–Kloks tech. report, page = printed page; AZ = Althaus–Ziegler.)

| # | where | gap / imprecision | resolution |
|---|---|---|---|
| G1 | BK Def. 5.6–5.9, Lemma 5.3 | trunk, tree model and characteristic are for *unrooted* trees, compared for equality in joins; "same tree model" is never defined (isomorphism?) | rooted at the origin, canonical kid order, structural equality (§a) |
| G2 | BK Def. 5.6 (removal of non-maximal leaves) | with sequences attached to *runs*, a leaf run whose tail nodes have the same label as their predecessor keeps the tail's sizes in a naive compaction; the reference **failed** here (`char(forget) ≠ forget(char)`) | normal form (iii): a leaf run keeps its first entry |
| G3 | BK §5.5, Step 3 (2 cases) ; AZ §3.3 (only informally: "an arbitrary path… nested sequence of subsets") | in case 2 the new leaf is only `{v} ∪ N`; joins need the *shape of the sibling* to match, so *every* nested chain of labels `S_x ⊇ M₁ ⊋ … ⊋ M ⊇ N` is needed (BK Step 1 lists all tree models, Step 3/4 does not) | `allChains` / `attachPlans`; the reference **failed** without it (first mismatch found) |
| G4 | BK Lemma 5.5, 5.6 ("easy to verify") | joining two decompositions with equal characteristic needs their *trees* aligned (`TA* = TB*`); with independent junk the union tree differs from the restriction tree | realiser trees are merged by lattice paths; junk of both sides disjoint; hidden constraint at common junk nodes shown harmless (§b.2) |
| G5 | BK Lemma 4.5, Thm 4.10–4.14, 5.9–5.14 | soundness uses a realiser whose sequences are extensions of the typical ones (Lemma 4.5: raise bags from neighbours); the proofs of 4.10/4.13/5.13 say "the other cases are similar" | dominance-based soundness; NEW `Seq` lemmas replace 4.5 |
| G6 | BK Thm 5.14 (6 lines) | completeness of introduce for trees: the change of trunk (new leaf in junk) and the change of tree model are asserted | `char_intro_dom` + `introC_mono` (BP4): the heart of the theory |
| G7 | BK Lemma 5.7/5.12 | trunk changes at forget/introduce: "exactly one leaf" claims | `norm` commutes with relabelling (confluence lemma) |
| G8 | BK Thm 4.10 proof, 4.9 case list | forget for paths lists 4 cases for the merging of the interval model | subsumed: `norm` merges by structural recursion; `Typical.append` (Lemma 3.17) |
| G9 | BK §6 (representation with pointers `L_i, R_i`), "checking all details is easy, but tedious, omitted" | extraction unspecified; linear time only | `extract` (polynomial), greedy realisation (§c) |
| G10 | BK Lemma 5.2 | node bound `(2n−1)²` for minimal decompositions | not needed: junk is never represented |
| G11 | BK Def. 5.1–5.3 (non-trivial, minimal decompositions) | assumed w.l.o.g. in completeness | not needed: completeness for *arbitrary* partial decompositions via `norm` |
| G12 | BK §4.4, 5.4 | at a forget node "`X_p ⊂ X_q` and `X_q` has exactly one vertex `x` not in `X_p`" — the nice TD's start nodes have `|X| = 1` | our leaves have the *empty* bag (word format): `start` |
| G13 | BK Thm 4.3 (join) | `max([c]) ≤ k+1` filter mentioned once | in `joinC`, `introC` |
| G14 | BK Lemma 2.3 | conversion to nice (with `4n` nodes) "omitted" | `niceOf` (Kloks; BP5) — `niceOf_spec` |
| G15 | BK Thm 6.1 (i) | linear time; `O(|V|+|I|)` counting hides `2^{O(ℓ³)}`?  (it is `2^{O(ℓ k²)}` in the paper; AZ give `2^{O(ℓ³)}`) | we prove `2^{O(ℓ³)}` (BP6) |
| G16 | AZ Lemma 2 (moving vertices out of pruned leaves), Lemma 3 (nested subsets) | sketches (the "core" and the property that only nested chains matter) | absorbed in `norm` + `attachPlans`; no separate lemma |
| G17 | AZ (P1)–(P5) proofs | sketched | provided by `Seq/` (Lemmas 3.2–3.20 of BK are fully proved there) |
| G18 | BK Lemma 3.15/3.16, §7 | polynomial-time pathwidth part | not used |
| G19 | AZ §4.1 (simple wrapper) | contracts an edge; needs "shrinking an edge lowers tw by ≤ 1" | replaced by **vertex-by-vertex** (`addEverywhere`, `hasTW_mono`) |
| G20 | concept statement itself | `improveDecomposition` for large `ℓ` | corollary of T2 (§e.4) |

---------------------------------------------------------------------------------------------------------------

## (g) Modules, dependency DAG, work packages, estimates, risks

### Modules (proofs package `Lax117284Proofs.Treewidth/`)
```
Seq/                      (done; + NEW lemmas)                                    ~5.5 k
Trees/Basic               RT, NT, Conn, IsTD, Width, under, Good                  ~1.0 k
Trees/Bridge1             RT ↔ TreeDecomposition; hasTW_mono/prefix               ~2.0 k
Trees/Bridge2             encode / parse / addEverywhere / IsTree of the word    ~2.5 k
Chars/Defs                CT, norm, forgetC, joinC, introPlans, introC, DomC      ~1.0 k
Chars/Norm                confluence, idempotence, Wf preservation (forget)       ~2.5 k
Chars/Exact               prof/char/restrict, char_leaf, char_forget, PTD.restrict_*, good_of_isNiceTD   ~3.0 k
Chars/Join                char_join_dom, joinC_mono, Wf, realize_join (mergeReal) ~6.0 k
Chars/Intro               char_intro_dom, introC_mono, Wf                         ~9.0 k
Chars/Realize             applyPlan, realize_intro                                ~6.0 k
Chars/Tables              tables_complete/sound/ne_nil, extract                   ~3.0 k
Chars/Count               Wf.count_le, card_wf_le, charBound_le                   ~3.0 k
Chars/Nice                niceOf_spec, improve_correct, decompose_correct, decompose_words  ~3.5 k
Machine/Codec             codeOf / ofCode / bit tables                            ~3.0 k
Machine/Norm              norm + τ (stack) on flat arrays                         ~4.0 k
Machine/Forget+Join       ringTypList DP, joinStep, forgetStep                    ~5.5 k
Machine/Intro             status vectors ↔ plans; introStep                       ~7.0 k
Machine/Tables            parse, bags, table loop, costs                          ~5.0 k
Machine/Extract           analyze, plan search, applyPlan, mergeReal, driver, emit ~20.0 k
Machine/Wrapper           prefix word, addEverywhere word, T2 loop, dispatcher    ~4.0 k
Machine/Final             guards, constants, the two concept statements           ~3.0 k
```
Total ≈ 100 k.

### DAG
`Seq → Chars/{Norm,Exact,Join,Intro}`; `Trees/Basic → everything`; `Chars/Exact → Chars/Join,Intro → Chars/Tables → Chars/Nice`;
`Chars/Count` needs `Chars/{Join,Intro}` (Wf preservation); `Trees/Bridge{1,2}` needed by `Chars/Nice` and `Machine/Final` only;
`Machine/Codec → Machine/{Norm,Forget+Join,Intro} → Tables → Extract → Wrapper → Final`; `Machine/*` needs `Chars/Defs` and
the *statements* of `Chars/Tables` (not their proofs) — so machine work can start after `Chars/Defs`.

### Work packages for independent agents (each with its exact Lean statements in `blueprint/`)
| WP | deliverable (statements) | depends on | lines | risk |
|---|---|---|---|---|
| S1 | `split_transport_up/down`, `ringSum_realise` (BP1) | Seq | 1.5 k | M |
| T1 | `hasTreewidthAtMost_iff_rt`, `hasTreewidthAtMost_prefix` (BP2) | – | 2 k | M |
| T2 | `niceDecomposition_encode/parse`, `bag_addEverywhere`, `addEverywhere_isNiceTD` (BP2) | – | 2.5 k | M |
| C1 | `norm` laws (confluence, `Wf` preservation for forget), `forgetC_mono` | Defs | 2.5 k | L |
| C2 | `char_leaf`, `char_forget`, `PTD.restrict_*`, `good_of_isNiceTD` | C1 | 3 k | L |
| C3 | `char_join_dom`, `joinC_mono`, `mergeReal_spec`, `realize_join` | C2, S1 | 6 k | M |
| C4 | `char_intro_dom`, `introC_mono` | C2, S1 | 9 k | **H** |
| C5 | `applyPlan_spec`, `realize_intro` | C4, S1 | 6 k | H |
| C6 | `tables_complete`, `extract_spec`, `tables_ne_nil_iff` | C3–C5 | 3 k | L |
| C7 | `Wf.count_le`, `card_wf_le`, `tables_wf`, `charBound_le` | C3, C4 | 3 k | M |
| C8 | `niceOf_spec`, `improve_correct`, `decompose_correct`, `decompose_words` | C6, T1, T2 | 3.5 k | M |
| M0 | codec (`wp_codec`) | Defs | 3 k | L |
| M1 | `wp_norm` | M0 | 4 k | M |
| M2 | `wp_forget_step`, `wp_join_step`, `wp_intro_step` | M0, M1 | 12.5 k | H |
| M3 | `wp_tables` | M2, T2 | 5 k | M |
| M4 | `wp_extract` | M3, C6 (statements) | 20 k | **H** |
| M5 | `wp_wrapper_words`, T2 loop, dispatcher | M3, M4 | 4 k | M |
| M6 | costs, guards, `decompose_solves`, the two concept statements | all | 3 k | M |

### Top-5 risks (ranked)
1. **`char_intro_dom` (C4)** — the case analysis of a region `W` against the core/junk decomposition, plan
   transport under dominance; the part BK wave through.  Mitigation: the reference (Python) is the executable
   oracle (`oracle.py`, `test_oracle.py`: restrict a real global decomposition to every nice node, check domination);
   prove first the *profile-level* statement on `PT`-shaped trees without vertex sets.
2. **Machine extraction (M4)** — 20 k lines of real-tree surgery on arrays; largest single item.  Mitigation: arena is
   append-only; every step has a functional spec in BP5; consider the functional-compiler shortcut (§e.6).
3. **The bridges (T1, T2)** — Mathlib-API-heavy (`IsTree` of the word's `treeGraph`, rooting an abstract tree),
   not conceptually hard but long and easy to underestimate.
4. **Introduce on the machine (M2)** — status vectors, validity, apply, normalise, with cost bounds `N·2^{O(ℓ²)}`.
5. **An undiscovered algorithmic bug at larger parameters.**  Tests cover `n ≤ 8`, `ℓ ≤ 5`, `k ≤ 3`; the two bugs found were
   both visible at `n ≤ 6`.  Mitigation: keep the oracle running during proof development (it checks each lemma's
   statement before it is proved).

### Decisions needed from the user
1. **Scope/size**: accept ≈ 100 k lines (≈ 2× FairRIS), or restrict? (§0.)
2. **Functional-language compiler** (§e.6): invest ≈ 12–15 k lines to save ≈ 25 k of RAM programs?
3. **T1 via T2** (§e.4): accept that `improveDecomposition` is a corollary of `niceDecomposition_computable`
   (so the concept order is reversed: prove T2 first, T1 for free)?
4. **Concept decomposition** (§h): OK to propose the module split to the concept package, and to state the RAM-level
   intermediate statements (BP7) there?
5. **Seq**: OK to ask the Seq agent for the three NEW lemmas (BP1) now?
6. Whether to prove niceness with *empty root bag* (not required by `GraphWords`; nothing changes).

---------------------------------------------------------------------------------------------------------------

## (h) Proposal for the concept side (not an edit)

Break the two monolithic axioms into a chain; each item is a *definition* or a *statement about a defined object*
(the archive convention: concept files hold statements, the proofs package proves them).

| concept module (`Lax117284/…`) | kind | content | proved by |
|---|---|---|---|
| `NiceTrees` | definition | `RT`, `NT`, `IsTD`, `IsNiceTD`, `NT.encode`; **bridge statements** `hasTreewidthAtMost_iff_rt`, `niceDecomposition_encode/parse` | T1, T2 |
| `TypicalSequences` | definition + theorems | `typical`, `Ext`, `Dom`, `RingSum`, `splits`; Lemmas 3.2–3.20 (BK) | Seq/ |
| `Characteristics` | definition | `prof`, `char`, `CT`, `norm`, `DomC`, `Wf` | (definition only) |
| `BodlaenderKloksAlgorithm` | definition | `tables`, `introC/joinC/forgetC`, `extract`, `niceOf`, `improve`, `decompose` | (definition only) |
| `BodlaenderKloksCorrect` | theorem statements | `tables_complete`, `extract_spec`, `tables_ne_nil_iff`, `improve_correct`, `decompose_correct`, `decompose_words` | C1–C8 |
| `BodlaenderKloksCount` | theorem statements | `card_wf_le`, `tables_length_le`, `charBound_le` | C7 |
| `BodlaenderKloksTime` | theorem statement (word RAM) | `decompose_solves`-shaped: *the* RAM program computes `wDecompose` within `costBound` (BP7) | M0–M6 |
| `BodlaenderKloks` | theorem | **`improveDecomposition`** (unchanged statement), from the two above and the dispatcher | M5/M6 |
| `Bodlaender` | theorem | **`niceDecomposition_computable`** (unchanged statement) | M6 |

The two headline statements keep their exact form (`fairris-lax` cites the second).  The intermediate statements
are the ones a reader can check against the paper; only `BodlaenderKloksTime` mentions a machine.

---------------------------------------------------------------------------------------------------------------

## (i) The reference implementation and what it found

Files (`reference/`): `typical.py` (τ, ring sum, splits, domination — tested against direct Definition 3.5 and brute-force
extension enumeration), `chars.py` (BP3), `nice.py` (nice TDs from elimination orders, checker, exact treewidth),
`dp.py` (BP4), `real.py` (BP5: `analyze`, `applyPlan`, `mergeReal`, `realize`, `niceify`), `improve.py` (T1, T2),
`oracle.py` (completeness oracle), `test_all.py`, `test_named.py`, `test_oracle.py`.
Run: `cd reference && PYTHONPATH=. python3 test_all.py improve 6 3 1 2` (atlas graphs ≤ 6 vertices, `k ≤ 3`, `ℓ ≤ k+2`),
`… wrapper 6 3`, `… random 8 0.3 2 1 40`, `python3 test_named.py`, `python3 test_oracle.py 400`.

Results (final algorithm):
* T1 with extraction, all atlas graphs `n ≤ 5`, `k ≤ 3`: 398/398 correct, output validated as a nice TD of width ≤ k.
* `n = 6`: ≈ 1 400 correct, **0 mismatches**, 0 dominance-assertion failures, ≈ 30 timeouts (> 60 s, Python).
* `n = 7` (`k ≤ 2`): 800 correct before stopping, 0 mismatches.  Random `G(8, .3)`: 75 correct, 0 mismatches.
* T2 (wrapper), `n ≤ 6`, `k ≤ 3`: ≈ 760 correct, 0 mismatches.
* Named graphs (cycles, grids `2×3, 2×4, 3×3`, `K₂,₃`, `K₃,₃`, `K₄`, `K₅`, wheels, prism, cube, Petersen, trees): all completed cases correct; the rest time out.

**Bugs found by the reference (both in my first reading of the paper):**
1. *(first mismatch; G3)* a new leaf hung with label exactly `N ∪ {v}` loses completeness — the shape of a sibling
   decomposition may force a leaf label `M ∪ {v}` with `N ⊆ M ⊆ S_x`, plus nested intermediate labels.  Fix: `allChains`.
2. *(G2)* `char(forget) ≠ forget(char)`: a leaf run with several nodes of equal label must keep only its first size
   (its tail is a junk leaf).  Fix: `norm` (iii).

Exact-layer statements checked directly on *actual* characteristics of restrictions of random real decompositions (`test_oracle.py`, 294 instances, 0 failures): `tables_complete`, `char_forget` (equation), `char_join_dom`, `char_intro_dom`; typical-layer `forgetC_mono`, `joinC_mono`, `introC_mono` on pairs `a' ⪯ a` of table entries (`test_mono.py`: 162 / 387 / 12 pairs, 0 failures; the introduce count is small because results are large).

Sanity checks recorded along the way: `plans consistent` (the plan-annotated enumeration equals the plain one on 54 table entries);
run counts vs `(2b+2)²` (§d); pruning by dominance does not change any decision.

**Caveat.**  Python cost is exponential in the number of runs; the reference is a *specification*, not a benchmark.
