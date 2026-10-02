# PLAN-machine — the machine layer of `niceDecomposition_computable` / `improveDecomposition`

Status 2026-09-25.  Read-only architecture pass; the typed statements are in `proofs-todo/Machine.lean`
(`sorry` = work-package goal).  Companion to `PLAN.md` §e, §g (this replaces its M0–M6).

## 0. Verdict

1. **The wrapper `decompose` as defined has exponential nice-tree growth** (Lean `#eval`, path, k = 1:
   sizes 1,2,7,17,39,85 for i = 0..5, ×2.2 per round; Python reference: 3,8,21,44,92,189,384,775,1558).
   Cause: `improve` returns `niceOf t` of an arbitrary extracted `RT`, which is fed to the next round.
   Fix (checked in Lean): dissolve kids whose bag ⊆ parent bag before `niceOf` (`compress`); sizes become
   1,2,3,5,7,9,11,13 (path) and 1,2,3,4,6 (C6, k = 2).  Under `RT.Conn` a compressed tree has `size ≤ |V|+1`,
   so with `niceOf_size_le` every round has `size ≤ (i+2)²`.  This is WP **P0** (≈2.5k lines math) and is needed by
   *every* machine design (PLAN §e's bit array `|D|·N` and "polynomial tree sizes" are false without it).
2. **The concept's bound and guard share one constant `c` and an unbounded `2^{c·k³}`.**  So the machine may run the
   *literal Lean functions* (`decomposeC`) on a cons-heap with quadratic dedup — no packed codes, no mark arrays, no flat
   models.  Everything then reduces to (a) a verified functional→IMP+ compiler, (b) embeddings of ~60 Lean functions
   with output-sensitive cost, (c) size bounds already proved or cheap (P1).
3. **Recommendation: build the compiler (fragment F), gated.**  ≈35k lines (28–48k) vs ≈55k (60–75k) direct.
   Gate G1 after V1–V3 (≈8k lines) with a toy end-to-end `Solves`.
4. **Go exact.**  Reroute to 4k+4 is *not* cheaper (Mathlib has no Menger/max-flow/separators; that route starts from zero
   and needs the same compiler).  Reroute only if G1 fails (then compare direct-RAM 60–75k vs approx 40–65k).

## 1. Existing reusable machinery

Nothing compiles or reasons about functional programs; there is no heap/list/arena library, no recursion support
(IMP+ has `while`, no procedures), and `Bnd` is a per-project record.  What exists (all IMP+, `Lax808846Proofs`):

* `Spec B P c Q K := ∀ σ, P σ → ∃ σ', Run B c σ σ' K ∧ Q σ σ'`; `Spec.seq/seq'/ite/conseq/pre/post/mono/frame`,
  `Spec.assign/store/read/write`; `Spec.while_potential I Φ …`, `Spec.while_count I V Kb …`, `Spec.forRange`,
  `Spec.forRangeZero x m I N Kb hNB hxN hm hbody : Spec B (fun σ => I (σ.setVar x 0)) (seq (assign x 0) (while (lt x m) c)) (fun _ σ' => I σ' ∧ σ'.vars x = N) ((Kb+4)*N+6)`.
* `run_vcg [specs]` (Tactic.lean): symbolic walk of straight-line IMP+; loops are handed in as specs.
* `Lib/{Fill,Stack,Queue,Ind,Csr,Trail}` (≈3.3k l.): one abstraction relation over `arrOf n f` each, `push_spec … 7`, `pop_spec … 7`,
  `Fill.loop_spec`, `Queue.drain_spec`, `Ind.mark_spec/test_spec`.
* `Transfer.Solves L c D f B K` (ok / inp / run), `computesInTime_of_solves (h) (hfit : ∀ x∈D, L.FitsWords (B x) w)
  (hT : ∀ x∈D, L.const*K x+1 ≤ T x) : ComputesInTime w (compileProgram L c) D f T`; `Layout.FitsWords B w` =
  `1<B ∧ B ≤ 2^w ∧ span B ≤ 2^w`, `span B = temps+2+#scalars+#arrays·B`.
* fairris `Machine/`: `FoldLoop.fLoop_spec`, `ILoop.iLoop_spec`; `Emit.eLoop`, `Emit.Agr`; `ReadAll.readAll_spec`; `EmitNat.emitNat_spec`;
  `TwRam*` (1.9k l.): a *universal RAM-program interpreter in IMP+* (`interp_run … cost 250*(t+1)`) — the calibration for our VM
  (needs memory 2^Wp, so not directly usable); `Tw*` (8.5k l.) mask-based treewidth DP.  `Machine/` as a whole = 51.5k lines.
* flexflowjit `Ram/`: `Fits.fitsWords_of_fits`, `computesInTime_of_solves_fits` (our guard has the extra `2^{c k³}` factor so
  `fits_of_guard` is new, same proof shape); `Sort.sort_spec`, `CopyArr.copyLoop_spec`; `ScanModel`; `TotalBnd`/`Gen.Bnd`.
* temporal-lax `EmitGreedy/EmitPeo`: loop specs parametrised by the entry state with `Agree`; no generics.

## 2. Direct RAM vs compiler

| | direct (PLAN M0–M6 + P0) | compiler F |
|---|---|---|
| lines | 55k (60–75k realistic) | 35k (28–48k) |
| risk | H: M4 real-tree surgery on arrays (20k), M2 intro status vectors (12.5k), flat-model↔math proofs everywhere | M: VM foundation (V1–V3), volume of E-proofs; risk is front-loaded and gated |
| cleverness | packed codes, mark arrays, status vectors, arenas | none: run the Lean functions |

**Fragment F (minimal).**
* Values `Val := nat ℕ | cons Val Val`; lists end in `nat 0`; Bool 0/1; Option; `Finset ℕ` = strictly sorted list;
  CT/RT/NT/AR/Plan as trees via `ToVal` (injective).  No arrays: adjacency = `nth` on the input list (O(len), affordable).
* Terms: `lit var add sub mul lt eq cons fst snd isNat ite letE call callv` (first order, de Bruijn env, recursion through a function
  table Δ; `callv` = call by run-time function id, giving map/foldl/flatMap/filter/dedup/sort as ordinary F functions).
* Semantics `Ev Δ B ρ t v c` (big-step, `c` = number of constructs, every produced ℕ `< B`); `Runs Δ B f xs y c`.
* Library (F1): append, length, nth, take/drop, map, filter, foldl, flatMap, any/all, range, zip, mem, `dedup` (Lean-exact
  `pwFilter` order), sort (`List.mergeSort`), sublists, min/max, `eqV`, the sorted-list Finset operations, plus an `ev_step` kit.
* **Costs compose** by `Ev` cost = derivation size; every algorithm function is stated `Embeds Δ fid P f cost` with cost
  *output-sensitive polynomial* (`64·(sz a+sz(f a)+1)^d`) or `poly·2^{K}` with `K` from P1.
* **Word-length guard `Fits`.**  Inside F: `Fits B v c := (maxNat v + c + 2)^2 < B`.  `compile_solves` takes
  `B x := 2·Bv x + 4(K x+|x|+8)+κ`.  The concept's guard is used once, in `fits_of_guard` with
  `Bfun c' e x = c'·2^{c' e³}(|x|+maxEntry x+1)^{c'}` and `c ≥ (temps+2+#scalars+#arrays)·c'`; for T1, `e = l`.
* VM (V1–V2): ≤ 18 instructions (`lit var add sub mul lt eq cons fst snd isNat jz jmp slide call callv ret halt`), arrays
  `HA HB` (car/cdr, append-only ⇒ `Rep` monotone), `STK`, `RET`, `OP/OA`; the IMP+ interpreter is `while run=1 do dispatch`.
  The input reader is format-specific (`Fmt.graphK`, `Fmt.graphKLD`: IMP+ has no EOF test).

## 3. Work packages; statements in `proofs-todo/Machine.lean`

| WP | goal (Machine.lean) | lines | risk | deps |
|---|---|---|---|---|
| P0 | `compress_isTD/width/size_le`, `improveC_correct`, `decomposeC_words_final`, `decomposeC_size_le` | 2.5k | L–M | – |
| P1 | `introPlans_length_le`, `joinC_length_le`, `extract_size_le` (constants indicative; must stay ≤ 2^{O(k³)}) | 3k | M | Chars (done) |
| F0 | `Val Tm Ev EvL Runs ToVal` + determinism, weakening, `Runs.bind` | 0.6k | L | – |
| F1 | combinator library + sorted-list Finset layer + `ev_step` | 3.5k | L–M | F0 |
| V1 | VM semantics, `compileTm`, `Ev ⇒ VM run` (call/ret, cost ≤ κ·c) | 2.5k | M | F0 |
| V2 | VM step ⇒ IMP+ `Spec`, heap `Rep` (monotone), dispatch loop (template `TwRam*`) | 3k | M–H | V1 defs |
| V3 | reader for `Fmt`, loader (`foldr` builder, `Com.Ok` by induction), writer, `compile_solves`, `fits_of_guard` | 1.8k | M | V2 |
| E1 | `E_typical/domB/ringTypList` (+ `latticeStates`, `findPath`) | 1.5k | L | F1 |
| E2 | `E_norm/forgetC/joinC`, `domCB`, CT codec, `key/sortKids` | 2.5k | M | F1 |
| E3 | `E_introC` (`winPlans, kidChoices, wtopPlans, allChains, attachPlans, introKids`) | 2.5k | M | E2 |
| E4 | `E_tables` (`nbrs, adjOfWord, forget/intro/joinTable`, dedup) | 1k | L | E2,E3,P1 |
| E5 | `E_realIntro/realJoin` (`analyze, applyPlan, mergeReal, cutAt, witnesses`) | 3.5k | M–H | F1,E1 |
| E6 | `E_extract/niceOf/compress/addEverywhere/encode`, `improveC`, `decomposeC` | 1.5k | L–M | E4,E5,P0 |
| A1 | `decompose_embeds`, `outWord_spec` (cost arithmetic with P1, `Fits`) | 2.5k | M | E*, P0, P1 |
| A2 | T2 final: `niceDecomposition_computable_target` | 1k | L–M | V3, A1 |
| A3 | T1: `NiceDecomposition.mono_width`, `outWord1_spec`, `improve_embeds`, `improveDecomposition_target` | 1k | L | A2 |

Total ≈ 35k.  Parallel schedule (≤ 4 agents): phase 1 {P0, P1, F0→F1, V1}; phase 2 {V2, E1, E2, E3}; phase 3 {V3, E4, E5};
phase 4 {E6, A1, A2, A3}.  Critical path: F0→V1→V2→V3 (≈8k) and F1→E2→E3→E4→E6→A1 (≈12k).
**Gate G1** (after V3): `compile_solves` for the full fragment + a toy (`typical`) `Solves`/`ComputesInTime` instance; ≤ 9k lines
incl. F0/F1.  If not met by ≈ 10k lines: stop and re-plan (direct RAM or reroute).

## 4. Representation and exponents

* Cheapest correct representation: **the Lean data structure itself** — a CT is a cons-tree of O(k³) cells; a table is a cons-list of
  ≤ 2^{720(k+1)³} of them (`charBound_le`, `l = k+1`, `tables_length_le'`; needs bags ≤ k+2: true after `addEverywhere`).
  Membership/dedup by structural equality, quadratic.
* PLAN's bit-array plan: code space `N ≤ 2^{2880(k+1)³}`, join triple loop `N³ ≤ 2^{8640(k+1)³} ≤ 2^{69120·k³}` for k ≥ 1; at k = 0 it is the
  constant `2^{8640}`, absorbed by `c` (so `c ≥ 2^{8640}`; proofs must treat `c` symbolically).  **Fits the stated bound — provided tree sizes
  are polynomial, i.e. after P0.**
* Naive route exponent ≈ `2^{24000·k³}`; `C0 = 30000` on `(k+2)³` is safe.
* Time: rounds n × (tables |nt|·N^c + extract |nt|²·N^c), |nt| ≤ 2(n+2)² ⇒ poly(n)·2^{O((k+2)³)} ≤ `c·2^{c k³}(|g|+2)^c` for large `c`.
* T1: dispatcher (`l ≤ k` ⇒ output `1 :: D`, else run T2 on `g ++ [k]`); `k < l` gives `2^{c k³} ≤ 2^{c l³}`, lengths only shrink.
* Mismatches found: (i) exponential growth (P0); (ii) `extract` recomputes `tables` per node (polynomial, fine);
  (iii) machine order must replicate Lean `dedup`/`findSome?` to equal `decompose`, or extraction needs a relational spec;
  (iv) all `E_*` preconditions need the hidden hypotheses of the math layer (`SymmOn`, `Good`, `Conn`, `Wf`).

## 5. Risks, go/no-go

1. VM foundation (V1–V3): novel, heap `Rep`, call/ret; mitigation: gate G1, `TwRam` template, append-only heap, ≤ 18 instrs.
2. Volume of E-proofs (~15k); mitigation: uniform `Embeds` shape, output-sensitive costs, `ev_step` kit, per-function parallelism.
3. Value-bound bookkeeping (`Fits`); mitigation: only `+,-,*,<,=`, one weakening lemma.
4. P1 constants may need adjustment (real bounds are ~2^{O(k² log k)}); P0 is numerically verified.
5. Loader `Com` has ~50k stores: never `simp`/`decide` on it; `foldr` builder + induction.
6. Agent capacity (≤ 4 concurrent, host load).

Total remaining ≈ 35k (28–48k) plus rewiring FairRIS.  **GO exact, gated at G1.**  4k+4 reroute: 40–65k from scratch, no Menger in
Mathlib, same compiler needed, and FairRIS must restate its width bound — not cheaper.
