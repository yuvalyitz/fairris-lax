# Reference implementation (Python) of the Bodlaender–Kloks algorithm as specified in `../PLAN.md`

Executable specification of exactly the algorithm of `../blueprint/BP3_Chars.lean`, `BP4_Tables.lean`, `BP5_Extract.lean`
(characteristics as rooted run trees; tables `FS(p)`; extraction by greedy realisation; Kloks niceification; the
vertex-by-vertex wrapper), plus tests against brute-force treewidth.  Python ≥ 3.9, `networkx` for the graph atlas.
It is a *specification*, not a benchmark (exponential in the number of runs).

| file | content |
|---|---|
| `typical.py` | `tau` (stack algorithm, tested against Definition 3.5), `dom` (≺), `ring` (τ of ring sums, lattice DP), `splits` |
| `chars.py` | run trees, `norm`, `forget`, `join`, `introduce` (+ plan-annotated `intro_plans`, `all_chains`), `dom_char` |
| `nice.py` | nice tree decompositions from elimination orders, checker `is_nice_td`/`is_td`, exact treewidth (subset DP) |
| `dp.py` | phase A: the tables (optional dominance pruning) |
| `real.py` | phase B: real trees, `analyze`, `applyPlan`, `mergeReal`, `realize`, `niceify` |
| `improve.py` | `improve` (T1) and `decompose` (T2) |
| `oracle.py`, `test_oracle.py` | completeness oracle: restrict a real global decomposition to every nice node, check domination |
| `test_all.py`, `test_named.py` | exhaustive/random/structured comparisons with brute force |

```
export PYTHONPATH=.
python3 test_all.py improve 5 3 1 2      # all atlas graphs <= 5 vertices, k <= 3, l <= k+2: T1 + extraction, output validated
python3 test_all.py wrapper 5 3          # T2
python3 test_all.py random 8 0.3 2 1 40  # random G(8, .3)
python3 test_named.py                    # cycles, grids, K_{3,3}, Petersen, ...
python3 test_oracle.py 300               # tables_complete + char_forget on random instances
```
