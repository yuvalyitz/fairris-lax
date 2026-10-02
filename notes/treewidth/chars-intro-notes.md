# C4 — the introduce case: proof architecture (`Chars/Intro*.lean`)

Statements proved (exactly as typed in `proofs-todo/Statements.lean`): `mem_allChains`, `witnesses_spec`, `introC_mono`,
`char_intro_dom` (the last one is the assembly `IntroMain.lean`).

## 0. Files

| file | content |
|---|---|
| `IntroChains` | `mem_allChains` (fuel of `chainsGo` never cuts a chain) |
| `IntroWitness` | `witnesses_spec` (`wpush` mirrors `Seq.push` on `(value, index)` pairs) |
| `IntroPlansMem` | the *results* of `introPlans` as inductive predicates: `WinR`, `KidR`, `WtopR`, `AttR`, `IR`; `mem_introPlans : (∃ path plan, (path, plan, r) ∈ introPlans v N t) ↔ IR v N t r`. The enumeration by `Cut`s / `List.range`s becomes membership in `Seq.splits` (`mem_splits_iff`, `mem_splits_drop`; `winPlans_mem` handles the shift `lo` by `winPlans v lo (node S y ks) ~ winPlans v 0 (node S (y.drop lo) ks)`) |
| `IntroMono` | `IR_mono` (raw results) ⇒ `introC_mono` (+ `mem_introC`, `maxEntry_dom_le`) |
| `IntroNorm` | `normF_merge` (merge law), `align` (perm + `normF_perm` + `normF_mono`), `Nested`/`keep_norm_false_iff`/`norm_of_nested` (junk), `yne_norm` |
| `IntroFT` | flagged profile trees `FT`, `uT`, `fT`, `occ`, `cov`, `FOk`; `keep_flag`, `keep_occ`, `nested_flag` |
| `IntroJunk` | Lemma J `junk_branch` (case (b)); `FT.ind` |
| `IntroPrefix` | exact-prefix lemmas `winR_prefix`, `winR_end`, `wtopR_wrap`, `IR_prefix`, `attR_junction` |
| `IntroSetup` | `align'`, `merge_cmp`, `kept`/`order`/`fkept`, `a_nonmerge`, `a_merge`, `T_eq` |
| `IntroMainR` / `IntroMainI` | `step_R`, `step_I` (the induction steps) |
| `IntroMain` | `main_intro` (FT induction), `mkFT` + `FOk_mkFT`/`occ_mkFT`/`mem_cov_mkFT`, `char_intro_dom` |

## 1. `introC_mono` (done)

`DomC t t'` and `r' ∈ IR t'` ⇒ `∃ r ∈ IR t, DomC r r'`.  Induction on `IR t'`; the run-level cases are the three cut
families (`WinR` ends, `WtopR` pre-cut, `AttR` cut) and each is one application of `split_up_of_dom`
(`Seq/Transport.lean`): a cut of `y'` is an `IsSplit` of `y'`, hence `y ≺ y'` has a split whose parts dominate.
`whole` is `KidR` (per kid, leave or continue), recursion on the kids (mutual `winR_mono`/`kidR_mono`), the
`kid` case of `IR` is `domCL_split`.  Then `norm_mono` (C1) and `maxEntry_dom_le` (the size filter).
*No* hypothesis is needed (sort ties are irrelevant: every comparison is positional).

## 2. `char_intro_dom`: the reduction to a statement about flagged profile trees

Let `U = c.under`, `B = c.bag`, `B' = insert v B`.  `t.restrict U` and `t` have the *same* tree; only the label /
size of the nodes of the region `W` (bags containing `v`) differ.  Put `FT.node S e w ks` (label `S = X ∩ B`,
size `e = |X ∩ U|`, flag `w = [v ∈ X]`) and
`uT P = prof B (t.restrict U)` (label `S`, size `e`), `fT P = prof B' t` (label `S ∪ {v}` and size `e + 1` on `W`).
Then `a := norm (uT P)` is the source characteristic and `T := norm (fT P)` the target of `char_intro_dom`.

*Hypotheses of the FT-level statement* (`FOk`): `v ∉ S` everywhere; `|S| ≤ e`; `W` connected (a flagged node has
only flagged occupied kids, an unflagged node has at most one occupied kid) — all from `RT.Conn` / the sizes.
And `N ⊆ cov P` (the labels of `W`): the closedness `NT.Good` puts every neighbour of `v` inside `c.bag`, the edge
of the tree decomposition then puts it in a bag of `W`.

`Main (R)`: `P.w` ⇒ `∃ (r, c) ∈ WinR v a, cov P ⊆ c ∧ DomC (norm r) T`.
`Main (I)`: `¬P.w ∧ occ P ∧ N ⊆ cov P` ⇒ `∃ r ∈ IR v N a, DomC (norm r) T`.
(Statement audit: `nc_test.py` in the scratchpad checked `∃ c ∈ introduce(...), c ≤ T` on 12 000 random Conn
trees with random regions `W`, random `B`, random `N ⊆ B ∩ cov`; 0 failures.  `test_oracle.py` covers real instances.)

## 3. The induction (one induction on `P`, typical `a`)

`a = normF S [e] F` with `F = filter keep (map norm kids)`; as `sortKids S F = τ.map g` for `τ` a permutation
(`List.map_mergeSort`) of the kept kids, the shapes of `a` are: *non-merge* (`node S [e] (τ.map g)`, uniform for
`F = []`, `F = [k]` with `k.S ≠ S`, `|F| ≥ 2`) and *merge* (`F = [k]`, `k.S = S`; `a = node S τ([e] ++ yk) kk`).
`T` is the same computation on the flagged kids; the lists are aligned by `align` (perm + `normF_perm` with the
keys of `T` distinct, `survivors_keys_distinct`, then `normF_mono`).

* **flag / prune correspondences** (`IntroNested`): `Nested σ p` (every label inside its parent's, root inside `σ`)
  iff `keep σ (norm p) = false`; flagging a nested tree below a flagged node keeps it nested; an occupied subtree
  below an unflagged parent is never pruned (`Nested σ (fT K)` would force `v ∈ σ` or no flag).
* **case (b), junk `W`** (`IntroJunk`, lemma J): if the occupied kid `K0` is junk in `a` (`Nested σ (uT K0)`), then
  `norm (fT K0)` is a chain of strictly nested runs ending in the leaf `S_w ∪ {v}` and `DomC (pathSubtree chain M) (..)`
  for some `(chain, M) ∈ allChains σ N` — the sizes of the plan's branch are the *labels'* sizes, dominated by the
  real sizes because `|S| ≤ e`.  The plan is `att` (none, or with the cut between the run's first entry and the rest).
* **merges** (`IntroPrefix`): for `k = node S yk kk` and the exact chain `k' = node S (s ++ yk) kk`
  (`DomC (node S τ(s++yk) kk) k'`), the options of `k` lift syntactically to options of `k'`
  (`WinR`: prefix `plus1 s`; `WtopR` pre-cut at `|s|` to wrap; `AttR`/kid: prefix), and `IR_mono` moves them to the
  typical run.  The merge law `normF S s [normF S y F] = normF S (τ(s ++ y)) F` closes the comparison.

## 4. What the induction needs (list of lemmas)

`keep`/`Nested`/`norm_of_nested`; `keep_flag` (flagged parent: `keep (insert v σ) (norm (fT K)) = keep σ (norm (uT K))`);
`cov_subset_of_nested`; `kidR_of_forall` (per-kid options to `KidR`); `align`; `normF` merge law;
`PL-*` prefix lemmas; `IR_kid_at` (option inside the `i`-th kid of `τ.map g`).
