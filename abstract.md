Each of $n$ clients submits one job on every one of $m$ days. A job with processing time $p$ and due date $d$ occupies exactly the interval
$(d-p,d]$. On each day, a machine can accept jobs whose intervals are pairwise disjoint. The objective is fairness rather than throughput: every
client must be served on at least $k$ of the $m$ days. This submission formalizes the
theorems of Heeger, Hermelin, Itzhaki, Molter and Shabtay on this problem,
$1 \mid \mathrm{rep} \mid \min_j \sum_i Z_{i,j}$.

For $0 \le k \le m$, the problem is solvable in polynomial time when
$k \in \{0,m-1,m\}$ and NP-hard for every fixed pair $(m,k)$ with $0<k<m-1$.
Hardness already holds for $m=3$ and $k=1$, with identical processing times.
Under day-independent processing times it remains
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

The formalization adjusts the placement of inactive jobs to preserve the conflict graph
required by the treewidth argument. On each gadget day, the dummy client's interval
covers a region containing a separate, disjoint slot for every inactive client. This
preserves the blocking argument without introducing conflicts between inactive clients.
The concept pages specify the construction and its tree decomposition.
