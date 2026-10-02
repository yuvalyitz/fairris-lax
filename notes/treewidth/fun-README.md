# The functional fragment F: meta-theory, tactic kit, library (WPs F0, F1)

Definitions (`Val Tm Ev EvL Runs Fits`) are in `Defs.lean` (shared, do not edit).  Everything below is built on them.

| file | content |
|---|---|
| `Meta.lean` | `Δ ⊑ Δ'` (`Ext`), `layerΔ`, `lookupL`; weakening in `B` and `Δ` (`Ev.weaken`); determinism (`Ev.det`, `Runs.det`); environment extension (`Ev.envLe`, `Ev.envExt`); `EvLe`/`EvLL` (evaluation *within a cost bound*) with constructor lemmas; `Runs.mk/mono/mono_B/weaken/evle/evle_v/bind`; `Tm.vars`, `EvLL.varsAt` |
| `ToVal.lean` | class `ToVal` (`toVal`, `inj`) with instances `ℕ Val Bool Unit List Prod Option Finset ℕ`; simp set `toVal_*`; `sz`, `mx` (largest natural) and their list lemmas (`sz_list`, `sz_list_nat`, `sz_append`, `mx_*`) |
| `Kit.lean` | tactics `ev_start ev_run ev_step ev_sub ev_side ev_iteT ev_iteF ev_call ev_callv` |
| `Embeds.lean` | `Embeds`, `osCost`, `Fits` lemmas (`Fits.cost_lt : c+3 < B`, `Fits.maxNat_lt`, `mono_*`), `FitsL`, `EmbedsE` (term-level, over an environment) with closure lemmas `call1 ite letE pair var lit mono_cost mono_pre congr ext`, `Embeds.of_body` |
| `Lib1.lean` | ids 0–17: `append length nth take drop map filter foldl flatMap any all rangeAux range zip eqV mem min max` |
| `Lib2.lean` | ids 32–37: `foldr revAux reverse dedup ins isort` (`List.dedup`, `List.mergeSort` on a total preorder) |
| `Lib3.lean` | ids 48–54: `Finset ℕ` as strictly sorted list: `memS insertS eraseS unionS interS diffS subsetS` |
| `Lib4.lean` | ids 64–71: `find? findSome? filterMap sum head? toFinset sublists pairUp`; `card_runs` |
| `Lib.lean` | the library as one table `Lib.Δ = lookupL Lib.entries`, ids `< 128` reserved; `Lib.extend tbl` |
| `LibEmbeds.lean` | unary `Embeds` instances (`length reverse dedup card toFinset`) and a toy composition through the closure lemmas |

## Conventions

* **Calling convention.**  `call f [t₀,…,tₙ]` evaluates the arguments in the caller's environment and runs the body of `f`
  in the environment `[v₀,…,vₙ]`; `var 0` is the first argument.  `letE a b` pushes the value in front (indices shift).
* **Higher order.**  `map f ctx xs` etc. take the function id `f` (a natural, passed as `Val.nat f`) and a *context* value
  `ctx`; the callee `f` runs on `[ctx, x]` (`foldl`: `[ctx, acc, x]`, `foldr`: `[ctx, x, acc]`, `isort`: `[ctx, a, b]`).
  Every lemma takes `hf : ∀ a ∈ l, Runs Δ B f [ctx, toVal a] (toVal (g a)) (cf a)` and states the cost as
  `κ·(1+|l|) + Σ cf`.
* **Costs.**  `Runs Δ B f xs y c` bounds the number of constructs evaluated by the *body* of `f` (the `call` construct
  itself is counted by the caller: `Runs.evle` adds `+1`).  Every library cost is an explicit polynomial in list lengths
  (`sz` where the element size matters: `mem_runs` `(30·sz a+24)·(|l|+1)+8`, `dedup_runs` `60·(s+1)·(|l|+1)²`).
* **Naturals.**  `Ev.lit n` needs `n < B`, `add`/`mul` their result `< B`.  The library lemmas that produce or compare
  naturals take a hypothesis such as `hB : 1 < B` or `8·|l|+8 < B`; it follows from `Fits B v c` by `Fits.cost_lt`.
* **Booleans.**  Boolean-valued library lemmas (`mem_runs`, `eqV_runs`, `subset_runs`, …) are stated for *any* `b : Bool`
  with `b = true ↔ …` (no decidability instance leaks into the statement).
* **`Finset ℕ` = strictly sorted list**, so `Finset.sort` is the identity on values (`toVal S = toVal (S.sort _)`,
  `toVal_finset`).  `toVal_finset_of_sorted` identifies any strictly sorted list with the right members.

## The table `Δ` and how to extend it (without editing these files)

* Library ids are `0 … 71` (`< Lib.reserved = 128`).  **Algorithm functions use ids `≥ 128`.**
* `Lib.extend eTbl := layerΔ Lib.Δ 128 eTbl` where `eTbl : ℕ → Option Tm` is *your* table (ids `≥ 128` only; typically
  a `match` on numerals or `lookupL` of an association list).  `Lib.ext_extend eTbl : Lib.Δ ⊑ Lib.extend eTbl`.
* Every library lemma is stated for an arbitrary `Δ'` with `hΔ : Lib_i.Δ ⊑ Δ'`; obtain it from `Lib.Δ ⊑ Δ'` by
  `Ext.trans Lib.ext1 hΔ` (for `Lib1`; `ext2 ext3 ext4` likewise) — so your own `Δ'` may be *any* extension.
* Several owners: give each a disjoint id range and table; the assembly is
  `layerΔ Lib.Δ 128 (orElseΔ tbl₁ tbl₂)`; each owner's `Ext` fact for their own `layerΔ Lib.Δ 128 tbl_i`
  follows from `Ext.layer_mono (Ext.orElse_left …)` / `Ext.layer_mono (Ext.orElse_right …)`.
* The compiler may read `Lib.entries : List (ℕ × Tm)` (`Lib.Δ = lookupL Lib.entries`, `Lib.entries_lt`).

## Proving `Runs` facts: the kit

```lean
theorem append_runs (xs ys : List α) :
    Runs Δ' B fAppend [toVal xs, toVal ys] (toVal (xs ++ ys)) (10 * xs.length + 4) := by
  induction xs with
  | nil  => refine Runs.mk (hΔ _ _ Δ_append) ?_; ev_start; · ev_run; · simp
  | cons a xs ih => refine Runs.mk (hΔ _ _ Δ_append) ?_; ev_start; · ev_run; · simp; omega
```

* `Runs.mk h ?_` turns the goal into `EvLe Δ B env body value cost`.
* `ev_start` replaces the cost bound by a metavariable (assembled bottom-up as the *exact* cost) and leaves the side goal
  `?cost ≤ bound` last (`simp`/`omega`/`nlinarith`).
* `ev_run` solves the evaluation goals: it picks `iteT`/`iteF` and `isNatT`/`isNatF` by trying the condition
  (decided by a fully solved sub-derivation), looks calls up by `assumption` among the `Runs` facts in context
  (recursive calls: the induction hypothesis; other functions: `have := Lib1.…_runs …`), and closes side goals
  (`n < B`, `ρ[i]? = some v`, branch conditions) by `rfl`/`simp`/`omega`/`simp [*]`.  Case-split first when a branch
  depends on data (`rcases Bool.eq_false_or_eq_true (p a)`, `cases xs`, `by_cases`) and `simp only [hp] at h` the facts.
* If `ev_run` leaves goals, they are exactly the stuck constructs / side conditions: finish by `ev_call h`,
  `ev_callv h` or by hand with the `EvLe.*` lemmas.
* Gotcha: `abbrev` ids (`fPairUp`) are atoms for `omega`; add `have : fPairUp < B := by show 71 < B; omega`.
