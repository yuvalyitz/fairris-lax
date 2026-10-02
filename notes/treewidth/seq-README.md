# `Lax117284Proofs.Treewidth.Seq` — typical sequences (Bodlaender–Kloks, §3)

Pure combinatorics of §3 of *Bodlaender, Kloks — Efficient and constructive algorithms for the
pathwidth and treewidth of graphs* (Utrecht tech. report 1993-27): Defs 3.5–3.10 and Lemmas
3.2–3.21 (3.1 is about interval models and is not part of this layer).  Everything is proved
(no `sorry`, no axioms beyond `propext`, `Classical.choice`, `Quot.sound`), namespace
`Lax117284Proofs.Treewidth.Seq`.  Every definition that an algorithm needs is computable / decidable.

**Conventions.**  An integer sequence is a `List ℕ`.  The paper's sequences are non-empty; the
definitions are total on `[]` (with `typical [] = []`, `Ext [] [] `, …) and the lemmas are stated
for all lists unless a hypothesis `a ≠ []` is shown (needed exactly where the statement is false or
degenerate for `[]`).  `ent a i = a.getD i 0` is entry `i` (0-based); `InR z x y` says `z` lies in
the closed interval spanned by `x,y` (`min x y ≤ z ≤ max x y`).  `LeSeq a b` (= `List.Forall₂ (·≤·) a b`)
is the paper's `a ≤ b` (same length, entrywise).  Notation such as `≺`, `≡`, `⊕`, `∘`, `E(a)` is
not used (clashes); the names below are the dictionary.

## Files (all in `Lax117284Proofs.Treewidth/Seq/`, imported by `Lax117284Proofs.Treewidth.lean`)

| file | content | paper |
|---|---|---|
| `Basic.lean` | `InR`, one reduction step `Red`, `Reach`, `NF`, index view `Dup`/`Win`, `nf_iff` | Def 3.5 |
| `Stack.lean` | stack algorithm `cut`/`push`/`typical`, absorption lemma `push_push`, window lemma | Def 3.5 |
| `Typical.lean` | uniqueness of the normal form, `typical` = the normal form | **Lemma 3.2** |
| `Symmetry.lean` | reversal (H1) and shift (H3) | Althaus–Ziegler |
| `Structure.lean` | `maxOf`/`minOf`, spirals, extremes cluster, length bound | **Lemma 3.3** |
| `Count.lean` | `typicalSeqs L` and its cardinality bound, sharpness | **Lemma 3.5**, Remark 3.4 |
| `Rel.lean` | entrywise order `LeSeq` | prelims |
| `Ext.lean` | `Ext` (= `E(a)`), stretching, lifting, Lemma 3.6, 3.18 | Def 3.6 |
| `ExtIdx.lean` | `Ext` is the paper's breakpoint definition | Def 3.6 |
| `ExtEnum.lean` | `extLen a k` (all extensions of length `k`), `2^(k-1)` bound | **Lemma 3.16** |
| `Dom.lean` | `Dom` (`≺`), `DomEquiv` (`≡`), 3.7–3.11, decision procedure `domB` | Defs 3.7, Lemmas 3.7–3.11 |
| `RingSum.lean` | `RingSum` (`⊕`), 3.12–3.14 | Def 3.8 |
| `RingTyp.lean` | `pathSums`, `ringTyp`, 3.15, covers | Lemma 3.15 |
| `Concat.lean` | `++`, 3.17–3.20, `splits` | Def 3.9–3.10 |
| `Lists.lean` | lists of sequences, Lemma 3.21 (1)–(7) | Def before 3.21 |
| `ListsMax.lean` | `max τ[a] = max [a]` | 3.3(i) for lists |

## Definitions ↔ paper

| paper | Lean |
|---|---|
| remove repetition / typical operation (Def 3.5) | `Red.dup l x r`, `Red.typ l x m y r hm hz` (`m ≠ []`, `∀ z ∈ m, InR z x y`); `typOp_iff` proves that this is the paper's "all `x ≤ a_k ≤ y` or all `x ≥ a_k ≥ y`" |
| iterating until none is possible | `Reach := ReflTransGen Red`, `NF a := ∀ b, ¬ Red a b` |
| `τ(a)` (computable) | `typical a` = `a.foldl push []` (stack algorithm; `cut`, `push`) |
| "a is a typical sequence" | `IsTypical a := typical a = a`; `isTypical_iff_nf`, `isTypical_iff_exists` |
| `l(a)`, `max(a)` | `List.length`, `maxOf a` (also `minOf`) |
| `a + A` (constant) | `a.map (· + A)` |
| `E(a)`, `a* ∈ E(a)` (Def 3.6) | `Ext a a*` (recursive, decidable `extB`); `ext_iff_extIdx` = paper's `t₁<…<t_{n+1}` definition |
| `a ≺ b`, `a ≡ b` (Def 3.7) | `Dom a b`, `DomEquiv a b`; decidable (`dom_iff_domB`, instances) |
| `a ⊕ b` (Def 3.8) | `RingSum a b c` / `ringSum a b : Set _`; computable representatives `pathSums a b`, typical ones `ringTyp a b` |
| `∘ab` (Def 3.9) | `a ++ b` |
| splits (Def 3.10) | `Split1`, `Split2`, computable `splits1 a`, `splits2 a`, `splits a` |
| lists `[a]` etc. | `List (List ℕ)`; `maxL`, `SameShape` (strong sense), `LeL`, `addL`, `typicalL`, `ExtL`, `RingSumL`, `DomL`, `DomEquivL` |

## Lemma index (paper → Lean)

| paper | Lean name(s) | statement |
|---|---|---|
| **3.2** | `typical_eq_iff`, `existsUnique_nf`, `eq_typical_of_reach_nf`, `reach_typical`, `typical_of_nf`, `nf_typical`, `typical_red` | `typical a = b ↔ Reach a b ∧ NF b`; exactly one normal form is reachable |
| **3.3(i)** | `maxOf_typical`, `minOf_typical`, `typical_upper_iff`, `mem_of_mem_typical` | `maxOf (typical a) = maxOf a` |
| **3.3(ii)** | `typical_length_le`, `typical_length_le'`, `nf_length_le` | `(typical a).length ≤ 2 * maxOf a + 1` |
| Remark 3.4 | `sharp L`, `typical_sharp` | the bound is attained for every `L` |
| **3.5** | `typicalSeqs L : Finset (List ℕ)`, `mem_typicalSeqs`, `mem_typicalSeqs_iff_exists`, `card_typicalSeqs_le` | `l ∈ typicalSeqs L ↔ l ≠ [] ∧ (∀ x∈l, x ≤ L) ∧ typical l = l`; `3 * card ≤ 8 * 4^L` (paper: `≤ 8/3·2^{2L}`) |
| **3.6** | `Ext.typical` (= `typical_ext`), `Ext.reach` | `Ext a a* → typical a* = typical a` (even `Reach a* a`) |
| **3.7** | `Dom.trans` (+ `Dom.refl`, `Trans` instance) | `≺` is transitive |
| Cor 3.8 | `DomEquiv.refl/symm/trans`, `domEquiv_equivalence` | `≡` is an equivalence |
| **3.9** | `below_of_red`, `above_of_red`, `dom_equiv_of_red` | one operation: extensions `a'* ≤ a ≤ a'**` (`Below a a'`, `Above a a'`), `a' ≡ a` |
| **3.10** | `below_typical`, `above_typical`, `domEquiv_typical` | `τ(a) ≡ a`, with extensions of `τ(a)` of the length of `a` below/above `a` |
| Cor 3.11 | `dom_typical_iff`, `domEquiv_typical_iff` | `a ≺ b ↔ τ a ≺ τ b` |
| **3.12** | `RingSum.of_ext` | `c ∈ a⊕b`, `a*∈E(a)`, `b*∈E(b)` ⇒ ∃ `c* ∈ E(c)` with `c* ∈ a*⊕b*` |
| **3.13** | `RingSum.dom_of_dom` (uses `ext_zip`) | `|a| = |b|`, `a₀ ≺ a`, `b₀ ≺ b` ⇒ ∃ `y₀ ∈ a₀⊕b₀`, `y₀ ≺ a+b` |
| **3.14** | `RingSum.dom_typical` | `c ∈ a⊕b` ⇒ ∃ `c' ∈ τa ⊕ τb`, `c' ≺ c` |
| **3.15** | `RingSum.short`, `pathSums_sound`, `pathSums_complete` | `c ∈ a⊕b`, `a ≠ []` ⇒ ∃ `c' ∈ pathSums a b` (a lattice-path sum) with `c' ∈ a⊕b`, `Ext c' c`, `typical c' = typical c`, `l(c') + 1 ≤ l(a)+l(b)` |
| computable ring sum | `ringTyp a b`, `mem_ringTyp` (`a ≠ []`), `ringTyp_cover_left/right` | `c ∈ ringTyp a b ↔ ∃ c' ∈ a⊕b, typical c' = c` |
| **3.16** | `extLen a k`, `mem_extLen`, `card_extLen_le` (`1 ≤ k`) | `#{a* ∈ E(a) : l(a*) = k} ≤ 2^(k-1)` |
| **3.17** | `typical_append_typical` (+ `_left`, `_right`) | `τ(∘ab) = τ(∘τ(a)τ(b))` |
| **3.18** | `ext_append` (= `Ext.append`) | `Ext a a* → Ext b b* → Ext (a++b) (a*++b*)` |
| **3.19** | `Dom.append`, `DomEquiv.append` | `a' ≺ a`, `b' ≺ b` ⇒ `a'++b' ≺ a++b` |
| **3.20** | `split1_ext_exists`, `split2_ext_exists` (existence of the split of `a`), `typical_of_split_ext` (the conclusion), packaged: `lemma_3_20_split1`, `lemma_3_20_split2` | hypothesis `Ext (typical a) a` |
| **3.21 (1)** | `DomL.trans`, `domEquivL_equivalence` | |
| **3.21 (2)** | `ExtL.typicalL_eq` | `τ[b] = τ[a]` for `[b] ∈ E[a]` |
| **3.21 (3)** | `domL_typicalL_iff` | `[a] ≺ [b] ↔ τ[a] ≺ τ[b]` |
| **3.21 (4)** | `lemma_3_21_4` | `τ[a] ≡ [a]`, extensions `[a'] ≤ [a] ≤ [a'']` of `τ[a]` |
| **3.21 (5)** | `RingSumL.of_ext` | list version of 3.12 |
| **3.21 (6)** | `RingSumL.dom_of_dom` (hypothesis `SameShape A B`) | list version of 3.13 |
| **3.21 (7)** | `RingSumL.dom_typicalL` | list version of 3.14 |
| (3.21 bridge) | `domL_iff_forall₂` | `DomL A B ↔ List.Forall₂ Dom A B` |
| (H1) | `typical_reverse` | `typical a.reverse = (typical a).reverse` (also `nf_reverse_iff`) |
| (H3) | `typical_map_add`, `typical_map_sub` (all entries `≥ c`) | `typical (a.map (· + c)) = (typical a).map (· + c)` |

## Computable API for a machine mirror

`typical`, `cut`, `push` (stack algorithm; `push t y` cuts `t` to the shortest prefix ending at an
index `i` with `t_{i+1},…` all in the interval of `t_i, y`, then appends `y`), `extB`/`Ext`
(recursion: `Ext (x::a) (y::w) ↔ y = x ∧ (Ext (x::a) w ∨ Ext a w)`), `domB` (lattice-path
recursion, `Dom a b ↔ domB a b = true`; `Decidable (Dom a b)` instance), `pathSums a b`
(finite set of sums along monotone lattice paths with steps `(1,0),(0,1),(1,1)`;
Althaus–Ziegler P5), `ringTyp a b := (pathSums a b).image typical`, `extLen a k`,
`splits1/splits2/splits`, `typicalSeqs L`.  Bounds for sizing memory: `typical_length_le`
(`2L+1`), `card_typicalSeqs_le` (`3·#≤8·4^L`), `card_extLen_le` (`2^(k-1)`), `RingSum.short`
(`|a|+|b|-1`), and every element of `pathSums a b` has length `≤ |a|+|b|-1`.

Also available for reuse (structure theory of normal forms, `Structure.lean`): `spiral_last_min/max`
(if `NF (v ++ [e] ++ [w])` and `w` is strictly above all of `v ++ [e]`, then `e` is a strict minimum of
`v ++ [e]`; mirror), `spiral_nodup`, `spiral_unique_lt/gt` (such a spiral is determined by its value
set), `nf_count_extreme` (a non-empty normal form contains its minimum or its maximum exactly once),
`nf_extreme_decomp`, `spiral_length_le`; `Count.lean`: `codesMin/codesMax`, `card_codesMin/Max`.

Also available for reuse: `nf_iff` (a list is typical iff no `Dup`/`Win` in index form; `Win a k j` is a
pair of indices `k+2 ≤ j` whose whole interior lies between `a_k` and `a_j`), `push_push`
(absorption), `stretch` (uniform repetition), `ext_lift`, `ext_stretch_of`, `ext_zip`.

## Paper statements found false / under-specified, and the repair

1. **Lemma 3.2, proof.**  The claim "if `a_k` can be removed by an operation, this remains true
   under any operation (unless it removes `a_k`)" is false at the level of positions.
   `a = (1,5,2,5,0)`: the second `5` is removable by the typical operation at positions
   (2nd,5th) (interior `2,5 ⊂ [0,5]`), but after the operation at positions (1st,4th) (which
   removes `5,2`) the surviving `5` is no longer removable.  The *statement* (uniqueness of
   `τ(a)` as a sequence of values) is true — checked by brute force for all sequences of length
   `≤ 7` over `{0..3}` — and needs a genuine confluence argument; it is proved by showing that the
   stack algorithm cannot distinguish `a` from the result of any single operation (the window
   lemma `foldl_push_window`, whose core is the absorption lemma `push_push`; it uses that the
   stack is itself a normal form).  The relational normal form is therefore unique and equals
   `typical`.
2. **`ringTyp a b` is *not* a function of `τ a, τ b`** (the requested `ringTyp a b =
   ringTyp (τ a) (τ b)` is false).  Counterexample (brute force): `a = (1,3,2,4)`, `b = (0,10,0,0)`,
   `τa = (1,4)`, `τb = (0,10,0)`: `ringTyp a b = {(1,11,1,4),(1,11,2,4),(1,12,2,4),(1,12,4),(1,13,2,4),(1,13,4),(1,14,4)}`
   while `ringTyp (τa) (τb) = {(1,11,1,4),(1,11,4),(1,14,4)}`.  What Lemmas 3.13/3.14 (and 3.10, 3.11)
   give, and what is proved, is equality *up to `≺`-covers*: every element of `ringTyp a b`
   dominates an element of `ringTyp (τa) (τb)` (`ringTyp_cover_left`) and every element of
   `ringTyp (τa) (τb)` is dominated by an element of `ringTyp a b` (`ringTyp_cover_right`).  (A
   brute-force run over all `a,b` of length `≤ 4` over `{0,1,2}` confirms the covers, and shows the
   sets differ in 2318 of 14400 cases.)
3. **Lemma 3.15, proof.**  The index set `I = {i | a*_i ≠ a*_{i+1} ∨ b*_i ≠ b*_{i+1}}` is defined
   by *values*; for non-typical `a,b` with adjacent equal entries the compressed sequence is not
   in `a ⊕ b` (e.g. `a=(3,3)`, `b=(1,1)`, `a*=a`, `b*=b`: `I = {2}`, `c' = (4)`, which has no
   extensions of length 2).  Repair: mark *index* changes, i.e. compress the pair of positions
   `(pos in a, pos in b)`; this is the lattice-path description (`pathSums`, `pathSums_complete`),
   giving `l(c') ≤ l(a) + l(b) - 1` for `a ≠ []`.
4. **Lemma 3.7, proof.**  "`b ≺ c ∧ b* ∈ E(b) ⇒ b* ≺ c`" is not obvious: it needs a common extension
   of two extensions of `b` (uniform stretching, `ext_stretch_of`); the rest is `ext_lift`.
5. **Lemma 3.13 / 3.12, proofs.**  Correct, but the choices ("`λ` large enough", "repeat `a_i`
   `p_i q_i` times") are implemented explicitly: `λ = l(a*) + l(b*) + 1` in `RingSum.of_ext`,
   and a common refinement lemma `ext_zip` in `RingSum.dom_of_dom`.
6. **Lemma 3.16.**  Needs `k ≥ 1` (the bound `2^(k-1)`); the hypothesis `l(a) ≤ k` is
   redundant (there are no extensions of length `k < l(a)`).
7. **Def. 3.10 / Lemma 3.20.**  A split of the second type needs `f < n` (so that `δ₂` is a
   sequence); the paper says "for length one there can only be a split of the first type".  The
   existence claim "(this split exists)" of Lemma 3.20 and the second-type case ("similar") are
   proved explicitly (`split1_ext_exists`, `split2_ext_exists`).
8. **Def. 3.5.**  The typical operation is `Red.typ` with "all interior entries in the
   closed interval spanned by the ends" (`typOp_iff`).  Note that windows with *equal* ends
   force all interior entries to be equal; after repetition removal these never occur.

No other defect was found: Lemmas 3.3, 3.5, 3.6, 3.9–3.14, 3.16–3.19, 3.21 and Remark 3.4 are correct
as printed (3.5 in the form `3·card ≤ 8·4^L`; exact numbers for `L = 0..3`: 1, 6, 27, 112).

## Verification

`cd treewidth-lax/proofs && export LEAN_NUM_THREADS=2 && lake build Lax117284Proofs.Treewidth` (or a single
module, e.g. `lake build Lax117284Proofs.Treewidth.Seq.Lists`).  Sanity checks were done by brute force
(Python: uniqueness of normal forms for all sequences of length ≤ 7 over `{0..3}`, agreement of
the stack algorithm with the rewriting normal form, the absorption lemma; `Dom` by explicit search over
pairs of extensions vs. the lattice-path recursion for all `a,b` of length ≤ 4 over `{0,1,2}`;
the `2^(k-1)` bound of Lemma 3.16; ring-sum covers) and
`#eval` (`typical`, `typicalSeqs`).
