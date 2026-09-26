Each of $n$ clients submits one job on every one of $m$ days. A job has a processing time
and a due date, and — the schedule being just-in-time — occupies exactly the interval
between them, so that on any single day the jobs a machine can accept are the ones whose
intervals are pairwise disjoint. The objective is fairness rather than throughput: every
client must be served on at least $k$ of the $m$ days. This submission formalizes the
theorems of Heeger, Hermelin, Itzhaki, Molter and Shabtay on this problem,
$1 \mid \mathrm{rep} \mid \min_j \sum_i Z_{i,j}$.

The fairness parameter alone settles the complexity: the problem is solvable in polynomial
time for $k \in \{0, m-1, m\}$ and NP-hard for every other value, already with identical
processing times and $m = 3$ days. Under day-independent processing times it remains
NP-hard and becomes a bipartite matching problem when the processing times are one. Under
day-independent due dates it remains NP-hard, and becomes tractable either for a constant
number of days, by a dynamic program over the clients in due-date order, or for
day-independent processing times, where a $k$-fair schedule exists exactly when $k$ times
the chromatic number of the one conflict graph is at most $m$. Measured against the
treewidth $\tau$ of the overall conflict graph, the problem is NP-hard for constant
$\tau$, fixed-parameter tractable for $m + \tau$, and fixed-parameter tractable for $n$.

Every gadget construction is given explicitly, with numbered clients and days, and each
statement about it is separate: that the construction is correct, that the instance it
produces has the structure claimed of it, and that it is computed within the stated
resources. The two objectives — the uniform one and the per-client generalization
$1 \mid k_j, \mathrm{rep} \mid \min_j \sum_i Z_{i,j}$, through which the treewidth
reduction passes — are one definition, the uniform case being the constant one. Hardness
is stated against the class NP of the archive; treewidth is the archive's, and the tree
decompositions the dynamic program of the treewidth algorithm runs on are nice ones in the
sense of Kloks.

The formalization repairs one gap in the published argument. The construction behind the
treewidth reduction gives every job that does not appear in a day's gadget the same job as
the dummy client's, which is what makes the dummy client block all of them at once; but
identical jobs conflict with each other as well, so any two clients that are irrelevant on
a common day become adjacent, and the overall conflict graph of the construction is
essentially complete rather than of treewidth four. The correctness argument uses only that
the dummy client blocks each irrelevant job, so it is unaffected: the repair gives the
dummy client a job covering a region in which every other job sits in a private slot of its
own, and the conflict graph is then the one the published tree decomposition describes.
