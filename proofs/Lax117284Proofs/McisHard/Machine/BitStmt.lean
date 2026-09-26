import Lax117284Proofs.McisHard.Machine.PredFinal

/-!
# The adjacency bit of `H` on the machine: interface for WP7 (WP6)

Re-export of `McisHard.Machine.PredFinal`, the finished statement and proof.  Everything is in the namespace
`Lax117284Proofs.McisHard.Bit`:

* `bitCom : Com` -- the command;
* `AB : List String` -- the scalars it may assign (everything else, all arrays, the input and the output tape are unchanged);
  every name in it starts with `b`, except `o vo so j vj sj cnt` (the scalars of `SatRank.rankCom`);
* `Kbit N = 128 * N + 1500` -- its cost;
* `bitCom_run` -- the statement about `adjF`; `bitCom_run_M` -- the same about `adjM` (no dependence on the WP3 lemma
  `unmatched_iff`); `adjM_iff_adjF` -- the bridge.

Layout.  Read-only inputs: the array `TK` (the stream `ns`), the scalars `N` (= `SlotsN ns`) and `A2`
(= `2 * ns.getD 1 0`) as `SatAccept.prepSat` leaves them, and `w`, `w2` (the two vertex numbers of `H`, below `B`).
Output: the scalar `bt` (`0` or `1`).
-/
