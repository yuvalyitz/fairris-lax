import Lax117284.ConflictGraph
import Lax117284.MulticolouredIndepSet
import Lax117284.Problems

/-!
---
title: Per-Client Fairness Parameters at Treewidth Four
type: lemma
---
**Lemma 14.** The problem
$1 \mid k_j, \mathrm{rep} \mid \min_j \sum_i Z_{i,j}$ is NP-hard even when the overall
conflict graph has treewidth at most $4$.

Let $G$ be an instance of Multicoloured Independent Set in normal form: $r$-regular with
$r \ge 1$, $\ell$ classes $V_1, \ldots, V_\ell$ of $n \ge 4$ vertices, and an even number
$|E|$ of edges, every edge directed from the smaller class to the larger. The constructed
instance has $\ell(n+1) + |E|$ days — for every colour $n$ *vertex days* and one
*validation day*, and one *edge day* per edge — and the clients: a vertex client $c_v$ with
$k_{c_v} = 1$ for every vertex; a selection client $c_i$ with $k_{c_i} = 1$ for every
colour; two edge clients $c_{v,u}$ and $c_{u,v}$ with parameter $1$ for every edge $(v,u)$;
two interaction clients $c^+$ and $c^-$ with $k^+ = k^- = |E|/2$; and a dummy client $c_0$
with $k_0 = \ell(n+1) + |E|$.

For every colour the vertex days and the validation day form a *vertex-selection gadget*
which compels the selection of a single vertex client for that colour, and the edge days
form an *incidence-checking gadget* which certifies that all clients can be satisfied only
if the selected vertices form a multicoloured independent set. On each day only a few
clients take part in the gadget, and the job of $c_0$ blocks the jobs of all the others: it
starts right after the last job of the gadget, and every client not taking part has a
unit-length job of its own inside it. Writing $N$ for the number of clients other than
$c_0$ and $\pi$ for a bijection between them and $\{1, \ldots, N\}$, the job of $c_0$ has
processing time $N$, and the job of such a client $c$ occupies the $\pi(c)$'th time unit of
it. On the vertex day of a vertex $v$, the clients $c_v$ and $c_i$ of $v$'s colour have due
date $r$ and processing time $r$, the job of $c_0$ has due date $r + N$, and every other
client $c$ has due date $r + \pi(c)$ and processing time $1$. On the validation day of
colour $i$, the client of the $p$'th vertex of $V_i$ has due date $rp$ and processing time
$r$, the client $c_{v,u}$ of the $q$'th neighbour $u$ of that vertex has due date
$r(p-1) + q$ and processing time $1$, the job of $c_0$ has due date $rn + N$, and every
other client has due date $rn + \pi(c)$ and processing time $1$. On the edge day of an edge
$(v,u)$, the client $c^-$ has due date $2$ and processing time $2$, $c^+$ due date $3$ and
processing time $2$, $c_{v,u}$ due date $3$ and processing time $1$, $c_{u,v}$ due date $1$
and processing time $1$, the job of $c_0$ due date $3 + N$, and every other client due date
$3 + \pi(c)$ and processing time $1$.

The overall conflict graph of the constructed instance has a tree decomposition of width
four: a root bag $\{c_0, c^+, c^-\}$, a bag $\{c_0, c^+, c^-, c_i\}$ per colour below it, a
bag $\{c_0, c^+, c^-, c_v, c_i\}$ per vertex of that colour below that, and a bag
$\{c_0, c^+, c^-, c_v, c_{v,u}\}$ per neighbour $u$ of $v$ below that.

# Formalization Notes

The clients are numbered: $c_0$ is $0$, $c^+$ is $1$, $c^-$ is $2$, then one number per
colour, then one per vertex, then one per pair of a vertex and a neighbour index. So
$\pi(c) = c$, the bijection of the source being this numbering, and a client's job inside
the job of $c_0$ is its own numbered time unit. The days are numbered by colour blocks of
$n+1$ — the $n$ vertex days and then the validation day — followed by the edge days in the
order the edges are listed.

The slot for a vertex and a neighbour index exists for every index below the degree read off
the graph, whether or not the vertex has that many neighbours; on a regular graph, which is
what the statements assume, every slot is a neighbour. A closed formula for the number of a
client is what a reduction can compute, where enumerating only the admissible pairs would
need a search.

The degree is read off the graph as the number of neighbours of the vertex $0$, raised to
$1$ so that no processing time is zero on an instance outside the normal form; on an
instance in normal form it is $r$.

The correctness statement carries the normal form as a hypothesis. The treewidth statement
does not: the decomposition above is one of the constructed graph whatever the input, which
is what makes the reduction land in the slice.

The map on words checks the normal form before it builds anything, and sends a word that
fails the check to the rejected word. That check is part of the reduction and not of the
source: without it the map would send an instance outside the normal form — one with no
colour and one vertex per class, say, whose construction has no day and asks for nothing —
to a yes-instance, and would then not be a reduction from the language of the normal form.
It is a matter of counting neighbours and edges, and takes quadratic time.

That the selected vertices can be checked at all needs $r\ell \le |E|/2$, so that the edge
days incident to a multicoloured independent set do not exhaust the requirement of one
interaction client; this is where $n \ge 4$ enters, since $|E| = rn\ell/2$. The source does
not state it.
-/

namespace Lax117284.Lemma14

open Lax117284.Problems Lax117284.MulticolouredIndepSet
open Lax434930.PolynomialTime Lax429075.Reductions

variable (G : Instance)

/-- The degree of the graph, read off the vertex `0` and raised to `1`. -/
noncomputable def deg : ℕ := max 1 G.degree

/-- The number of clients: the dummy client, the two interaction clients, one per colour,
one per vertex, and one per pair of a vertex and a neighbour index. -/
noncomputable def clientCount : ℕ :=
  3 + G.colours + G.vertices + G.vertices * deg G

/-- The number `N` of clients other than the dummy client, which is the length of its job
and the number of time units inside it. -/
noncomputable def span : ℕ := 2 + G.colours + G.vertices + G.vertices * deg G

/-- The number of days: `n` vertex days and one validation day per colour, and one edge day
per edge. -/
noncomputable def dayCount : ℕ := G.colours * (G.size + 1) + G.edgeCount

/-- The number of the selection client of colour `i`. -/
def selId (i : ℕ) : ℕ := 3 + i

/-- The number of the vertex client of the vertex numbered `w`. -/
def vtxId (w : ℕ) : ℕ := 3 + G.colours + w

/-- The number of the edge client `c_{v,u}` where `v` is the vertex numbered `w` and `u` is
its `q`'th neighbour. -/
noncomputable def incId (w q : ℕ) : ℕ :=
  3 + G.colours + G.vertices + w * deg G + q

/-- The processing time and the due date of client `c` on the vertex day of the vertex
numbered `w₀`. -/
noncomputable def vertexDay (w₀ c : ℕ) : ℕ × ℕ :=
  if c = 0 then (span G, deg G + span G)
  else if c = vtxId G w₀ ∨ c = selId (G.classOf w₀) then (deg G, deg G)
  else (1, deg G + c)

/-- The processing time and the due date of client `c` on the validation day of colour
`i₀`. -/
noncomputable def validationDay (i₀ c : ℕ) : ℕ × ℕ :=
  if c = 0 then (span G, deg G * G.size + span G)
  else if 3 + G.colours ≤ c ∧ c < 3 + G.colours + G.vertices ∧
      G.classOf (c - (3 + G.colours)) = i₀ then
    (deg G, deg G * (G.indexOf (c - (3 + G.colours)) + 1))
  else if 3 + G.colours + G.vertices ≤ c ∧
      G.classOf ((c - (3 + G.colours + G.vertices)) / deg G) = i₀ then
    (1, deg G * G.indexOf ((c - (3 + G.colours + G.vertices)) / deg G)
      + (c - (3 + G.colours + G.vertices)) % deg G + 1)
  else (1, deg G * G.size + c)

/-- The processing time and the due date of client `c` on the edge day of the edge from the
vertex numbered `w` to the vertex numbered `w'`. -/
noncomputable def edgeDay (w w' c : ℕ) : ℕ × ℕ :=
  if c = 0 then (span G, 3 + span G)
  else if c = 2 then (2, 2)
  else if c = 1 then (2, 3)
  else if c = incId G w ((G.nbrs w).idxOf w') then (1, 3)
  else if c = incId G w' ((G.nbrs w').idxOf w) then (1, 1)
  else (1, 3 + c)

/-- The processing time and the due date of client `c` on day `i`: the colour blocks of `n`
vertex days and a validation day come first, then the edge days. -/
noncomputable def job (i c : ℕ) : ℕ × ℕ :=
  if i < G.colours * (G.size + 1) then
    (if i % (G.size + 1) < G.size then
      vertexDay G ((i / (G.size + 1)) * G.size + i % (G.size + 1)) c
    else validationDay G (i / (G.size + 1)) c)
  else
    edgeDay G (G.edgeList.getD (i - G.colours * (G.size + 1)) (0, 0)).1
      (G.edgeList.getD (i - G.colours * (G.size + 1)) (0, 0)).2 c

theorem one_le_deg : 1 ≤ deg G := le_max_left 1 _

theorem two_le_span : 2 ≤ span G := by unfold span; omega

theorem job_pos (i c : ℕ) : 0 < (job G i c).1 := by
  have hd := one_le_deg G
  have hs := two_le_span G
  unfold job vertexDay validationDay edgeDay
  split_ifs <;> simp only [] <;> omega

theorem job_le (i c : ℕ) : (job G i c).1 ≤ (job G i c).2 := by
  have hd := one_le_deg G
  have hs := two_le_span G
  have hm : ∀ a b : ℕ, a ≤ a * (b + 1) := fun a b => Nat.le_mul_of_pos_right a (Nat.succ_pos b)
  unfold job vertexDay validationDay edgeDay
  split_ifs <;> simp only [] <;> first
    | omega
    | exact hm _ _

/-- **The instance of Lemma 14.** -/
noncomputable def inst : Scheduling.Instance where
  clients := clientCount G
  days := dayCount G
  p i c := (job G i c).1
  d i c := (job G i c).2
  p_pos i c := job_pos G i c
  p_le_d i c := job_le G i c

/-- **The fairness parameters of the constructed instance**: the dummy client is required
on every day, the two interaction clients on half the edge days each, and every other
client once. -/
noncomputable def kvec : Fin (inst G).clients → ℕ := fun c =>
  if (c : ℕ) = 0 then dayCount G
  else if (c : ℕ) = 1 ∨ (c : ℕ) = 2 then G.edgeCount / 2
  else 1

/-- **The construction is correct**: the graph has a multicoloured independent set exactly
when the constructed instance admits a schedule meeting every client's own fairness
parameter. -/
axiom correct (hG : G.Normal) :
    G.HasIndepSet ↔ (inst G).HasFairSchedule (kvec G)

/-- **The overall conflict graph of the constructed instance has treewidth at most
four.** -/
axiom treewidth_le : ConflictGraph.treewidth (inst G) ≤ 4

/-- **No fairness parameter of the constructed instance exceeds its number of days.** -/
axiom kvec_le_days (j : Fin (inst G).clients) : kvec G j ≤ (inst G).days

open Classical in
/-- **The reduction**, as a map on words: a word encoding an instance of Multicoloured
Independent Set *in normal form* is sent to the encoding of the constructed instance with
its fairness parameters, and every other word — one that encodes an instance outside the
normal form as much as one that encodes nothing — to the rejected word. -/
noncomputable def reduce (w : Word) : Word :=
  if h : ∃ G : Instance, encodeInstance G = w ∧ G.Normal then
    encodePerClient (inst h.choose) (kvec h.choose)
  else rejectedPerClient

/-- **The reduction is correct.** -/
axiom reduce_correct (w : Word) :
    w ∈ NormalMulticolouredIndepSet ↔
      reduce w ∈ PerClient fun I k => ConflictGraph.treewidth I ≤ 4 ∧ ∀ j, k j ≤ I.days

/-- **The reduction runs in polynomial time.** -/
axiom reduce_polyTime : Nonempty (Turing.TM2ComputableInPolyTime id id reduce)

/-- **Lemma 14.** The per-client problem is NP-hard on the instances whose overall conflict
graph has treewidth at most `4`. -/
axiom perClient_npHard :
    NPHard (PerClient fun I k => ConflictGraph.treewidth I ≤ 4 ∧ ∀ j, k j ≤ I.days)

end Lax117284.Lemma14
