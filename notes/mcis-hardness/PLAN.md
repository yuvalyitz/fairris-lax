# PLAN — Normal-form Multicoloured Independent Set NP-hardness, formalised in fairris-lax (developed in staging package mcis-wip/)

Target: `Lax117284.MulticolouredIndepSet.normalMulticolouredIndepSet_npHard` (currently a cited axiom) from
`Lax117284.BoundedSat.boundedSat_npHard`, via `Lax117284Proofs.Compose.npHard_of_manyOne`, with a `conclusion:`-tagged theorem
(see fairris-lax/proofs/Lax117284Proofs/BodlaenderProved.lean and Machine/IlpFinal.lean end for the convention).
Statements: mcis-wip/McisHard/Defs.lean (type-checked skeleton; every `sorry` is a work-package goal).  Design: DESIGN.md, check_ports.py (passes).

## Construction (uniform "port" numbering; no prefix sums, no arrays)
A = twoClauses, B = threeClauses, p = A+B, S = 2A+3B (positions o < S).  Positions read from the token stream `ns` as
(var, sign) = ns[3+2o], ns[4+2o] (sign ∈ {0,1}, `ShapeF`).
* G' vertex number u = 36·o + r; n' = 36·S.  r = 0: position o.  r = 1+7j+t: vertex t of slot (o,j), j<5, t<7, t = 0 is the attach vertex `a`.
* gadget X on 7 vertices: K7 minus {ab, ac, de, fg} (0=a,1=b,2=c,3=d,4=e,5=f,6=g): degrees 4 (a), 5 (others); α(X)=2, X−a has independent pair {d,e}.
* ports: R(o,j,o',j') (symmetric partial matching on (position,port) pairs, ports j<5):
  - mate ports j,j'<2: j+j'+2 = s (clause size), o' = mate(o,j) = o − t + (t+j+1) mod s (t = index of o in its clause), ¬comp(o,o');
  - complement ports j,j'∈{2,3}: comp(o,o') (same var, different sign), rank(o') = j−2, rank(o) = j'−2  (rank = number of earlier slots with the same literal = `rankN`, ≤ 1 under `CondN`);
  - port 4 never matched.
* G' adjacency (`portAdjN` in Defs): pos–pos: ∃ j j', R; pos–slot: same o, slot vertex t'=0, the port unmatched; slot–slot: same slot & gadAdj, or both t=0 and R links the ports.
* Each position has ≤ 4 matched ports (port 4 free) ⇒ G' is 5-regular; α(G') = α(G0) + 10·S (each of the 5S slots contributes exactly 2, live or dead).
* H = copyInst (p + 10 S) G' (classes k' = p+10S ≥ 21 when S ≥ 2; n' = 36 S ≥ 72).  Regular of degree 6(k'−1); edges 3 n' k'(k'−1) even.
* S = 0: fixed H0 = copyInst 2 (⊥ : SimpleGraph (Fin 4)) (regular of degree 1, size 4, 4 edges, has an independent transversal).
* Words that are not formula encodings (or vars > slots): reduce to [] which is not in the language (encodeInstance is never empty).

## Adjacency bit of H at (w,w')  (`adjF` in Defs)
w/n' ≠ w'/n' ∧ (w%n' = w'%n' ∨ (S ≠ 0 ∧ portAdjN R (w%n') (w'%n'))).  Machine: for w<Vv, w2<Vv (Vv = K·Nn, K = kOf, Nn = nOf):
i:=w/Nn; u:=w-i*Nn; j:=w2/Nn; v:=w2-j*Nn; bt := 0; if i≠j: if u=v then bt:=1 else if S≠0: o:=u/36; r:=u-36o; o2:=v/36; r2:=v-36 o2;
r=0: (r2=0 → PE(o,o2) | o=o2 ∧ (r2-1)%7=0 ∧ unmatched(o,(r2-1)/7)); r>0: (r2=0 → o=o2 ∧ (r-1)%7=0 ∧ unmatched(o,(r-1)/7))
| (o=o2 ∧ (r-1)/7=(r2-1)/7 ∧ gad((r-1)%7,(r2-1)%7)) ∨ ((r-1)%7=0 ∧ (r2-1)%7=0 ∧ link(o,(r-1)/7,o2,(r2-1)/7)); write bt.
(PE = o≠o2 ∧ (same clause ∨ comp); unmatched(o,j): j=4 ∨ (j<2 ∧ (s ≤ j+1 ∨ comp(o,mate(o,j)))) ∨ (2≤j<4 ∧ coCount(o) ≤ j−2); link = the R relation
above, checked with `rankN` (reuse `SatRank.rankCom_run`); coCount(o) = number of slots o' with (var,1−sign) — one count loop, reuse `SatRank.rankLoop_spec` with `so := 1 − sign`.)
Cost per bit ≈ 3(64N+46)+400; total ≈ Vv²(200N+400), Vv ≤ 400 N² ⇒ K ≤ C(Sz+1)(l+1)^5.

## Templates in fairris-lax (paths under fairris-lax/proofs/Lax117284Proofs/)
* Closer: `Compose.lean` `npHard_of_manyOne : NPHard A → ManyOne A B → NPHard B`; pattern `Hardness.lean:88-91`:
  `npHard_of_manyOne Lax117284.BoundedSat.boundedSat_npHard ⟨reduce, reduce_polyTime, reduce_correct⟩`; `JitHard/Final.lean` (tagged conclusion example).
* Machine skeleton for a Word→Word reduction over the `BoundedSat.encodeFormula` word: `Machine/WrapT.lean` (198), `Machine/WrapTFinal.lean` (140:
  `polyTimeE W layout com_ok rfl _ C e _ Kpoly _`, needs `layout.arrays.length = 2` ("a","TK"), `layout.temps + scalars.length ≤ 200`,
  `Kacc Sz l ≤ C (Sz+1)(l+1)^e`, `Krej Sz ≤ C(Sz+1)`); tokenizer `TokModel/TokScan/TokProg/TokLoop/TokBound`, format `SatFormat.EF`, `SatNk.nkF`;
  semantics `SatSem` (`valsOf`, `formulaOf`, `condN_valsOf`, `shape_valsOf`, `sat_gate`, `code_toksF`, `Agree`, `rankN`, `CondN`, `SlotsN`, `ShapeF`, `t7_eq`, `t7_rej` as models);
  nearest analogue: fairris Theorem 7 (`Machine/Sat*`: SatFormat 238, SatNk 115, SatSem 608, SatCong 67, SatOps 137, SatRank 243, SatCheck 237, SatDue 380, SatPrint 201, SatAccept 257, SatFinal 140).
* Output writers: `Out.emitVar/emitLit/emitVal`, `EmitNat.emitNat` (cost 48·Sz+50), raw bit `Com.write (.lit b)`; loops `Emit.eLoop` (counter "i"), `Out.outLoop`, generic-counter `ILoop.iLoop_spec` / `FoldLoop.fLoop`.
* Reuse unchanged: `SatCheck.chkLoop`, `SatAccept.prepSat` (gives `var<vars`, `rank ≤ 1`, scalars n, na, nb, A2, N).
* IMP+ has no `mod`: x % m = x − (x/m)*m.  Value bound `Bd y = 2^(2|y|+4) + 8|y| + 64 + Mx y`; in accRun: `2^(2L+4)+8L+64 ≤ B`, `ts.length ≤ L`, `∀ v, v+4<B → v.size ≤ Sz`.
* MCIS-side API: `Lemma14Graph.lean` (`num`, `adjAt_num : adjAt (num v) (num u) = true ↔ Adj v u`, `mem_nbrs`, `nbrs_nodup`, `exists_num`, `handshake : Regular r → 2·edgeCount = vertices·r`),
  `SourceInjectivity.mis_encode_inj`, `boundedSat_encode_inj`.

## Work packages (lanes)
| WP | content | lines |
|---|---|---|
| WP1 math (copy) | `copyInst_regular`, `copyInst_normal`, `H0_normal`, `H0_hasIndepSet` (`copyInst_hasIndepSet_iff` already proved) | 200 |
| WP2 math (ports) | `gad_facts`, `portGraph_adj`, `portGraph_regular`, `portGraph_indep_iff` | 750 |
| WP3 math (formula ports) | `isPortRel_RN`, `rank_initial`, `unmatched_iff`, `posGraph_RN` | 550 |
| WP4 math (SAT) | `sat_iff_indep`, `Hinst_hasIndepSet_iff` | 450 |
| WP5 math (bridge) | `encodeInstance_Hfin`, `Hinst_normal`, `formulaOf_valsOf`, `reduceMcis_code`, `reduceMcis_rej` | 450 |
| WP6 machine (predicates) | `compCom`, `clauseCom`, `PE`, `unmatched` (with coCount wrapper), `link`, `gad`, `bitCom_run` (statement: `σ'.vars "bt" = if adjF ns w w' then 1 else 0` given w,w' < Vv) | 1400 |
| WP7 machine (print) | header via `emitVar_spec`, nested `iLoop_spec`, S=0 branch, output = natBits of the matrix word (`natBits_encodeNat`) | 500 |
| WP8 machine (accept) | `accMcis = prepSat; chkLoop; ite ok print skip`, `accMcis_run` (arr ↔ ns via `Agree`, `valsOf_*`, `rank_valsOf`) | 500 |
| WP9 machine (final) | layout, `Com.Ok`, `Kpoly`, `poly_lt_pow`, `reduceMcis_polyTime` via `WrapTFinal.polyTimeE` | 250 |
| WP10 | Final assembly: `normalMulticolouredIndepSet_npHard_proved` tagged conclusion; move into fairris; root imports | 50 |

Math content notes (from the architect):
* copyInst_regular/normal: `(nbrs w).length` = card of {u' | Adj v u'} via `num`, `mem_nbrs`, `nbrs_nodup`, `exists_num`; edge count from `handshake` (2E = k·n·(k−1)(r+1)); positivity (k−1)(r+1) ≥ 1; for r=5, k(k−1) even ⇒ 4 ∣ k n (k−1)(r+1); H0: r=0,k=2,n=4 ⇒ degree 1, E = 4.
* gad_facts: `decide` over Fin 7 and its subsets.  portGraph_adj: `fromRel` + symmetry/irreflexivity of `portAdjN` from `IsPortRel`, `gadAdj_symm`.
* portGraph_regular: position vertex: neighbours = images of matched ports (injective partner map, `func`, `simple`) + slot-a vertices of unmatched ports = 5; slot vertex t≠0: 5 internal; t=0: 4 internal + exactly one external (position or partner's a).
* portGraph_indep_iff: (⇒) restrict to positions (independent in posGraph); each slot ≤ 2 (α(X)=2); (⇐) add pair {d,e} = vertices 3,4 from every slot (touches nothing outside the slot).
* isPortRel_RN: mate arithmetic (t+j+1) mod s with j' = s−2−j; `compN` symmetry; `func`/`simple` via `Theorem7Slots.occ_eq_of_lit_rank` (equal literal and rank ⇒ equal position); rank ≤ 1 from `CondN`.
* rank_initial: pigeonhole (rank injective on occurrences of a literal; each rank < count).  unmatched_iff: case split on j (port 4 none; j<2 partner = mate with j' = s−2−j; j∈{2,3} via rank_initial + rank ≤ 1, signs ≤ 1 so ≠ ↔ 1−sign).
* posGraph_RN: complementary pairs = matched complement-port pairs (ranks ≤ 1); complementary same-clause mates via complement ports; adjacency = o≠o' ∧ (same clause ∨ comp).
* sat_iff_indep: bridge via `Theorem7Slots` (`slotNum`, `exists_slotNum`, `litOfSlot_slotNum`), `litOfSlot_formulaOf`; (⇒) one true literal per clause ⇒ p pairwise non-adjacent positions; (⇐) an independent set has ≤ 1 position per clause and ≥ p ⇒ exactly one per clause; assignment a(x)=b if a chosen position has literal (x,b) (consistent since complementary positions adjacent).
* Hinst_hasIndepSet_iff: `copyInst_hasIndepSet_iff`, `portGraph_indep_iff` with q = p, `posGraph_RN`, `sat_iff_indep`.  Hinst_normal: `copyInst_normal` with k = p+10S ≥ 21 (S ≠ 0 ⇒ S ≥ 2), n = 36 S ≥ 72, 4 ∣ … (k(k−1) even).
* encodeInstance_Hfin: `adjAt` on w < vertices = decide(adjF …) via `adjAt_num`, `portGraph_adj`, div/mod decoding of `num`.  reduceMcis_code: copy `SatSem.t7_eq` (~30 lines); reduceMcis_rej: copy `t7_rej`.

Risks: bitCom_run is the largest single proof (isolate each subroutine with its own Spec + frame conditions as SatDue/SatRank; raise maxHeartbeats as SatAccept does; omega context pollution — isolate arithmetic in top-level lemmas);
regularity counting on div/mod numbers (one decode lemma u = 36·(u/36) + u%36; injective maps from Fin 5); polynomial bound with large constants (follow SatFinal.Kpoly, nlinarith on abstracted powers as BFinal.Kmain_le).
