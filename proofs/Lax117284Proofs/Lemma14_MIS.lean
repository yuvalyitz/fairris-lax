import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Lax117284Proofs.Trivial
import Lax117284Proofs.ConflictGraph
import Lax117284Proofs.Treewidth

/-!
# Lemma 14: NP-hardness at treewidth 4

> **Lemma 14.** The `1 | k_j, rep | min_j ∑_i Z_{i,j}` problem is NP-hard even when the
> overall conflict graph has treewidth at most 4.
>
> *Proof.* We reduce from the NP-hard MULTICOLORED INDEPENDENT SET problem [33, 34]. […] We
> can assume without loss of generality that `G` is `r`-regular, that `|V₁| = ⋯ = |V_ℓ| = n`,
> and that `|E|` is even. […] The instance will contain `ℓ · (n + 1) + |E|` days: For every
> colour `i ∈ {1, …, ℓ}`, we create `n` vertex days and a single validation day. For every
> edge `e ∈ E` we create a single edge day.

## The gadget

Every job not named below has due date `1` and processing time `1` — including the dummy
client `c₀`'s, on every day. `c₀`'s fairness parameter is the total number of days, so it runs
every day, and therefore **no client whose job that day is the unit job can run at all**
(`not_mem_of_small`). Each day is thereby reduced to the handful of clients with a job of
their own:

* a **vertex day** of `v ∈ V_i` carries `c_v` and `c_i`, both occupying `(1, r+1]`. They
  conflict, so the day selects one of them; selecting `c_i` is what marks `v` as chosen.
* the **validation day** of colour `i` carries `c_w` for each `w ∈ V_i`, occupying the disjoint
  block `(r(p+1), r(p+2)]`, and each of `w`'s `r` edge clients, occupying one unit slot inside
  that block. So `c_w` blocks exactly its own edge clients.
* the **edge day** of `e = (v,u)` carries `c_{v,u}` on `(3,4]`, `c_{u,v}` on `(1,2]`, `c⁺` on
  `(2,4]` and `c⁻` on `(1,3]`: the conflict graph is the path
  `c_{u,v} — c⁻ — c⁺ — c_{v,u}`.

The interaction clients `c⁺` and `c⁻` have fairness parameter `|E|/2` each and can run only on
edge days, of which there are `|E|`; since they conflict, every edge day runs exactly one of
them, and hence *not both* edge clients of that edge. That is the incidence check: the chosen
vertices' edge clients are pushed onto the edge days, and two chosen vertices sharing an edge
would need both of that edge's clients on the same day.

## Indices are 0-based

The paper numbers vertices `v_1^i, …, v_n^i` and neighbours `1, …, r`; `Fin` counts from `0`,
so every due date here is the paper's with `p` replaced by `p + 1` and `q` by `q + 1`.

## ⚠ An erratum, repaired: the treewidth clause is false as the paper specifies the construction

Lemma 14 claims two things — that the reduction is correct, and that the overall conflict
graph of the constructed instance has treewidth at most `4` (Fig. 7). The first holds for the
paper's own construction and is proved here in full. **The second does not hold for that
construction as written**, and the reason is the sentence quoted above, together with Fig. 5's
caption: *"the jobs not appearing in the gadget are all identical to the job of client
`c₀`"*.

Identical jobs conflict (Definition 5 is about intersecting intervals, and a job intersects
itself). So on any one day, *every* client not named in that day's gadget would be pairwise
adjacent to every other such client in the overall conflict graph. On the vertex day of a
vertex `z ∈ V_i`, the clients not named are all vertex clients except `z`, all selection
clients except `c_i`, every edge client, `c⁺`, `c⁻` and `c₀`. The overall conflict graph would
then contain a clique on essentially all `ℓ·n + ℓ + 2|E| + 3` clients, and its treewidth would
be `Ω(ℓn)`, not `4`. Fig. 7's decomposition has no bag containing `c_v` and `c_w` for two
distinct vertices, so it would not be a tree decomposition of that graph.

**The repair, applied below.** `inst` does **not** give `c₀` and every irrelevant client the
same unit job; instead `c₀`'s job *covers a parking region*, and each irrelevant client gets
its own private unit slot inside that region: with `M` past every gadget due date of the day
and `N` the number of clients, `c₀`'s job is `(M, M + N]` and the `t`-th irrelevant client's
job is `(M + t, M + t + 1]`. `c₀` still conflicts with every irrelevant client — so it still
blocks them all, which is the only thing the correctness argument below uses — while two
irrelevant clients no longer conflict with each other, and neither conflicts with the day's
gadget clients. The conflict graph is then exactly the one Fig. 7 decomposes, and
`Proofs-FairRIS/Lemma14_Treewidth.lean` builds that decomposition and proves the treewidth
bound (`treewidth_overallGraph_le`). No repair can keep the unit-slot form: any job meeting
`(0,1]` starts at `0`, so any two of them meet each other.

## What is here, and what is in `Lemma14_Treewidth.lean`

* `MIS`, the normalized input (`r`-regular, `ℓ`-partite, `n` per class) with its incidence
  algebra — `rev` is an involution without fixed points, and every incidence belongs to
  exactly one `Edge`;
* `inst`, **the repaired instance** described above, and `kvec`, the per-client fairness
  vector;
* the `Small`/`Big` machinery and the per-day conflict analysis, stated so that the repair's
  parking region is transparent to everything that follows;
* **both directions of Lemma 14's correctness** (`hasFairSchedule_iff_hasIndepSet`), which
  are unaffected by the repair: they use only that `c₀` blocks every irrelevant client.

`Lemma14_Treewidth.lean` builds Fig. 7's decomposition of this repaired instance's overall
conflict graph and proves the treewidth clause; `FairRIS.lean`'s `theorem16_hard` assembles
both halves with Lemma 15 and the `multicoloredIndepSet_NPHard` axiom.

## One hypothesis the paper leaves implicit

The `⇒` direction has to schedule `c⁺` and `c⁻` on exactly `|E|/2` days each. The `ℓ · r` edge
days incident to a chosen vertex force one of the two, and the rest are free; balancing is
possible only if neither forced count exceeds `|E|/2`. With `|E| = ℓnr/2` that is `n ≥ 4`,
which the standard padding provides. It appears below as `hbal : G.ℓ * G.r ≤ half`.
-/


namespace Lax117284Proofs.Model

namespace Lemma14

open Instance

/-! ## 1. Multicolored Independent Set, in normalized form -/

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- An instance of **Multicolored Independent Set**, in the form Lemma 14 assumes: an
`ℓ`-partite graph with `n` vertices per colour class in which every vertex has exactly `r`
neighbours, presented through a numbering `nbr v q` of `v`'s neighbours together with the
matching back-index `revq`. -/
structure MIS where
  /-- The number of colour classes. -/
  ℓ : ℕ
  /-- The number of vertices in each class. -/
  n : ℕ
  /-- The common degree. -/
  r : ℕ
  r_pos : 0 < r
  /-- `nbr v q` is `v`'s `q`-th neighbour. -/
  nbr : Fin ℓ × Fin n → Fin r → Fin ℓ × Fin n
  /-- `v` is the `revq v q`-th neighbour of `nbr v q`. -/
  revq : Fin ℓ × Fin n → Fin r → Fin r
  nbr_rev : ∀ v q, nbr (nbr v q) (revq v q) = v
  revq_rev : ∀ v q, revq (nbr v q) (revq v q) = q
  /-- The graph is `ℓ`-partite: neighbours lie in different colour classes. -/
  colour_ne : ∀ v q, (nbr v q).1 ≠ v.1

namespace MIS

variable (G : MIS)

/-- A **vertex**, `v_p^i` in the paper. -/
abbrev Vtx : Type := Fin G.ℓ × Fin G.n

/-- An **incidence**: a vertex together with the index of one of its neighbours. The paper's
edge client `c_{v,u}` is the incidence `(v, q)` with `u = nbr v q`. -/
abbrev Inc : Type := G.Vtx × Fin G.r

/-- The opposite incidence of the same edge. -/
def rev (x : G.Inc) : G.Inc := (G.nbr x.1 x.2, G.revq x.1 x.2)

@[simp] lemma rev_rev (x : G.Inc) : G.rev (G.rev x) = x := by
  simp only [rev]
  rw [G.nbr_rev, G.revq_rev]

lemma rev_ne (x : G.Inc) : G.rev x ≠ x := by
  intro h
  exact G.colour_ne x.1 x.2 (congrArg (fun y => y.1.1) h)

/-- The incidence oriented from the lower colour class: the paper's directed edge. -/
def Tail (x : G.Inc) : Prop := x.1.1 < (G.nbr x.1 x.2).1

instance (x : G.Inc) : Decidable (G.Tail x) := by unfold Tail; infer_instance

lemma tail_or_tail_rev (x : G.Inc) : G.Tail x ∨ G.Tail (G.rev x) := by
  have h := G.colour_ne x.1 x.2
  simp only [Tail, rev, G.nbr_rev]
  omega

lemma not_tail_and_tail_rev {x : G.Inc} (h : G.Tail x) : ¬ G.Tail (G.rev x) := by
  simp only [Tail, rev, G.nbr_rev] at h ⊢
  omega

/-- The **edges**: one for each pair of opposite incidences, represented by the one oriented
from the lower colour class. -/
abbrev Edge : Type := {x : G.Inc // G.Tail x}

/-- The edge an incidence belongs to. -/
def edgeOf (x : G.Inc) : G.Edge :=
  if h : G.Tail x then ⟨x, h⟩ else ⟨G.rev x, (G.tail_or_tail_rev x).resolve_left h⟩

lemma edgeOf_tail {x : G.Inc} (h : G.Tail x) : G.edgeOf x = ⟨x, h⟩ := dif_pos h

lemma edgeOf_not_tail {x : G.Inc} (h : ¬ G.Tail x) :
    G.edgeOf x = ⟨G.rev x, (G.tail_or_tail_rev x).resolve_left h⟩ := dif_neg h

lemma edgeOf_rev (x : G.Inc) : G.edgeOf (G.rev x) = G.edgeOf x := by
  by_cases h : G.Tail x
  · rw [G.edgeOf_not_tail (G.not_tail_and_tail_rev h), G.edgeOf_tail h]
    simp [G.rev_rev]
  · have h' : G.Tail (G.rev x) := (G.tail_or_tail_rev x).resolve_left h
    rw [G.edgeOf_tail h', G.edgeOf_not_tail h]

/-- The two incidences of an edge are the edge's own and its reverse, and nothing else. -/
lemma mem_edgeOf {x : G.Inc} {e : G.Edge} (h : G.edgeOf x = e) : x = e.1 ∨ x = G.rev e.1 := by
  by_cases hx : G.Tail x
  · rw [G.edgeOf_tail hx] at h
    exact Or.inl (congrArg Subtype.val h)
  · rw [G.edgeOf_not_tail hx] at h
    have h1 : G.rev x = e.1 := congrArg Subtype.val h
    exact Or.inr (by rw [← h1, G.rev_rev])

/-- **Adjacency**: `u` is a neighbour of `v`. -/
def Adj (v u : G.Vtx) : Prop := ∃ q, G.nbr v q = u

/-- **The question of Multicolored Independent Set**: one vertex from each colour class, no
two of them adjacent. -/
def HasIndepSet : Prop :=
  ∃ sel : Fin G.ℓ → Fin G.n, ∀ i i' : Fin G.ℓ, ¬ G.Adj (i, sel i) (i', sel i')


/-! ## 2. The constructed instance

Two regions on every day. The **gadget region** `(0, M]` carries the jobs the paper names;
the **parking region** `(M, M + N]` carries everything else, one private unit slot per
client, and is covered end to end by the dummy client `c₀`'s job. So `c₀` conflicts with
every parked client — which is all the correctness argument uses — while parked clients
conflict neither with each other nor with the day's gadget jobs.

This is the repair described in the module doc: the paper puts every parked job in the *same*
slot as `c₀`'s, which blocks them just as well but makes them mutually adjacent and destroys
the treewidth bound. -/

/-- The clients: one per vertex, one per colour, one per incidence, the two interaction
clients `c⁺` (`inl true`) and `c⁻` (`inl false`), and the dummy `c₀`. -/
abbrev Client : Type := G.Vtx ⊕ (Fin G.ℓ ⊕ (G.Inc ⊕ (Bool ⊕ Unit)))

/-- The days: `n` vertex days per colour, one validation day per colour, one edge day per
edge. -/
abbrev Day : Type := G.Vtx ⊕ (Fin G.ℓ ⊕ G.Edge)

/-- The vertex client `c_v`. -/
abbrev cv (v : G.Vtx) : G.Client := Sum.inl v
/-- The selection client `c_i`. -/
abbrev cs (i : Fin G.ℓ) : G.Client := Sum.inr (Sum.inl i)
/-- The edge client `c_{v,u}` of the incidence `x`. -/
abbrev ce (x : G.Inc) : G.Client := Sum.inr (Sum.inr (Sum.inl x))
/-- The interaction client `c⁺` (`b = true`) or `c⁻` (`b = false`). -/
abbrev ci (b : Bool) : G.Client := Sum.inr (Sum.inr (Sum.inr (Sum.inl b)))
/-- The dummy client `c₀`. -/
abbrev c0 : G.Client := Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))

/-- The vertex day of `v`. -/
abbrev dV (v : G.Vtx) : G.Day := Sum.inl v
/-- The validation day of colour `i`. -/
abbrev dW (i : Fin G.ℓ) : G.Day := Sum.inr (Sum.inl i)
/-- The edge day of `e`. -/
abbrev dE (e : G.Edge) : G.Day := Sum.inr (Sum.inr e)

/-- Where the parking region starts: past every gadget due date on every day. -/
def M : ℕ := G.r * (G.n + 2) + 4

/-- The number of clients, and so the length of the parking region. -/
def N : ℕ := Fintype.card G.Client

/-- A private slot index for each client. -/
noncomputable def cidx (c : G.Client) : ℕ := (Fintype.equivFin G.Client c).val

lemma cidx_lt (c : G.Client) : G.cidx c < G.N := (Fintype.equivFin G.Client c).isLt

lemma cidx_injective : Function.Injective G.cidx := fun _ _ h =>
  (Fintype.equivFin G.Client).injective (Fin.ext h)

lemma N_pos : 0 < G.N := lt_of_le_of_lt (Nat.zero_le _) (G.cidx_lt G.c0)

/-- The due date of a parked job: its own slot inside the parking region. -/
noncomputable def parkD (c : G.Client) : ℕ := G.M + G.cidx c + 1

lemma M_lt_parkD (c : G.Client) : G.M < G.parkD c := by simp [parkD]

/-- The due dates of the construction. -/
noncomputable def dd : G.Day → G.Client → ℕ
  | Sum.inl v, Sum.inl w => if w = v then G.r + 1 else G.parkD (Sum.inl w)
  | Sum.inl v, Sum.inr (Sum.inl i) =>
      if i = v.1 then G.r + 1 else G.parkD (Sum.inr (Sum.inl i))
  | Sum.inl _, Sum.inr (Sum.inr (Sum.inl x)) => G.parkD (Sum.inr (Sum.inr (Sum.inl x)))
  | Sum.inl _, Sum.inr (Sum.inr (Sum.inr (Sum.inl b))) =>
      G.parkD (Sum.inr (Sum.inr (Sum.inr (Sum.inl b))))
  | Sum.inl _, Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => G.M + G.N
  | Sum.inr (Sum.inl i), Sum.inl w =>
      if w.1 = i then G.r * (w.2.val + 2) else G.parkD (Sum.inl w)
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inl i) => G.parkD (Sum.inr (Sum.inl i))
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inr (Sum.inl x)) =>
      if x.1.1 = i then G.r * (x.1.2.val + 1) + x.2.val + 1
      else G.parkD (Sum.inr (Sum.inr (Sum.inl x)))
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr (Sum.inr (Sum.inl b))) =>
      G.parkD (Sum.inr (Sum.inr (Sum.inr (Sum.inl b))))
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => G.M + G.N
  | Sum.inr (Sum.inr _), Sum.inl w => G.parkD (Sum.inl w)
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl i) => G.parkD (Sum.inr (Sum.inl i))
  | Sum.inr (Sum.inr e), Sum.inr (Sum.inr (Sum.inl x)) =>
      if x = e.1 then 4 else if x = G.rev e.1 then 2
      else G.parkD (Sum.inr (Sum.inr (Sum.inl x)))
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr (Sum.inr (Sum.inl b))) => if b then 4 else 3
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => G.M + G.N

/-- The processing times of the construction. -/
def pp : G.Day → G.Client → ℕ
  | Sum.inl v, Sum.inl w => if w = v then G.r else 1
  | Sum.inl v, Sum.inr (Sum.inl i) => if i = v.1 then G.r else 1
  | Sum.inl _, Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inl _, Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => 1
  | Sum.inl _, Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => G.N
  | Sum.inr (Sum.inl i), Sum.inl w => if w.1 = i then G.r else 1
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => 1
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => G.N
  | Sum.inr (Sum.inr _), Sum.inl _ => 1
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => 2
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => G.N

private lemma mul_mono {a b : ℕ} (h : a ≤ b) : G.r * a ≤ G.r * b :=
  Nat.mul_le_mul (le_refl _) h

lemma pp_pos (i : G.Day) (c : G.Client) : 0 < G.pp i c := by
  have hr := G.r_pos
  have hN := G.N_pos
  rcases i with v | (i | e) <;> rcases c with w | (i' | (x | (b | u))) <;>
    simp only [pp] <;> first | omega | (split <;> omega)

lemma pp_le_dd (i : G.Day) (c : G.Client) : G.pp i c ≤ G.dd i c := by
  have hr := G.r_pos
  have hpark : ∀ c' : G.Client, 1 ≤ G.parkD c' := fun c' => by simp [parkD]
  rcases i with v | (i | e) <;> rcases c with w | (i' | (x | (b | u))) <;>
    simp only [pp, dd]
  · split <;> [omega; exact hpark _]
  · split <;> [omega; exact hpark _]
  · exact hpark _
  · exact hpark _
  · omega
  · split
    · calc G.r = G.r * 1 := (Nat.mul_one G.r).symm
        _ ≤ G.r * (w.2.val + 2) := Nat.mul_le_mul (le_refl _) (by omega)
    · exact hpark _
  · exact hpark _
  · split <;> [omega; exact hpark _]
  · exact hpark _
  · omega
  · exact hpark _
  · exact hpark _
  · split <;> [omega; (split <;> [omega; exact hpark _])]
  · split <;> omega
  · omega

/-- **The instance of Lemma 14.** -/
@[reducible] noncomputable def inst : Instance where
  Client := G.Client
  Day := G.Day
  clientFintype := inferInstance
  clientDecEq := inferInstance
  dayFintype := inferInstance
  dayDecEq := inferInstance
  p := G.pp
  d := G.dd
  p_pos := G.pp_pos
  p_le_d := G.pp_le_dd

/-- The fairness vector: `1` for the vertex, selection and edge clients, `|E|/2` for the two
interaction clients, and every day for the dummy. -/
def kvec (half : ℕ) : G.Client → ℕ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => half
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => Fintype.card G.Day

/-! ## 3. Gadget jobs and parked jobs

A client's job on a day is one of three things: the dummy's covering job `(M, M + N]`; a
**gadget** job, inside `(0, M]`, one of the ones the paper names; or a **parked** job in its
own private slot `(M + idx c, M + idx c + 1]` inside the covering job. So the dummy conflicts
with exactly the parked clients — being forced onto every day, it blocks exactly them — and a
parked client conflicts with nothing else at all. -/

/-- `c` has a job of its own on day `i`: one inside the gadget region. -/
def Big (i : G.Day) (c : G.Client) : Prop := G.dd i c ≤ G.M

noncomputable instance (i : G.Day) (c : G.Client) : Decidable (G.Big i c) := by
  unfold Big; infer_instance

/-- `c` is parked on day `i`. -/
def Small (i : G.Day) (c : G.Client) : Prop := c ≠ G.c0 ∧ ¬ G.Big i c

noncomputable instance (i : G.Day) (c : G.Client) : Decidable (G.Small i c) := by
  unfold Small; infer_instance

@[simp] lemma dd_c0 (i : G.Day) : G.dd i G.c0 = G.M + G.N := by
  rcases i with _ | (_ | _) <;> rfl

@[simp] lemma pp_c0 (i : G.Day) : G.pp i G.c0 = G.N := by
  rcases i with _ | (_ | _) <;> rfl

private lemma hM_vertex : G.r + 1 ≤ G.M := by
  have h1 : G.r * 1 ≤ G.r * (G.n + 2) := G.mul_mono (by omega)
  simp only [M]
  omega

private lemma hM_block (w : G.Vtx) : G.r * (w.2.val + 2) ≤ G.M := by
  have h1 := G.mul_mono (a := w.2.val + 2) (b := G.n + 2) (by have := w.2.isLt; omega)
  simp only [M]
  omega

private lemma hM_slot (x : G.Inc) : G.r * (x.1.2.val + 1) + x.2.val + 1 ≤ G.M := by
  have h1 := G.mul_mono (a := x.1.2.val + 1) (b := G.n) (by have := x.1.2.isLt; omega)
  have h2 : G.r * G.n + G.r * 2 = G.r * (G.n + 2) := by ring
  have h4 := x.2.isLt
  simp only [M]
  omega

private lemma hM_four : 4 ≤ G.M := by simp only [M]; omega

/-- **Every client is the dummy, has a gadget job, or is parked in its own slot.** -/
lemma trichotomy (i : G.Day) (c : G.Client) :
    c = G.c0 ∨ G.Big i c ∨ (G.dd i c = G.parkD c ∧ G.pp i c = 1) := by
  have h1 := G.hM_vertex
  have h4 := G.hM_four
  rcases i with v | (j | e) <;> rcases c with w | (i' | (x | (b | u)))
  · by_cases h : w = v
    · exact Or.inr (Or.inl (by simp only [Big, dd, if_pos h]; omega))
    · exact Or.inr (Or.inr ⟨by simp only [dd, if_neg h], by simp only [pp, if_neg h]⟩)
  · by_cases h : i' = v.1
    · exact Or.inr (Or.inl (by simp only [Big, dd, if_pos h]; omega))
    · exact Or.inr (Or.inr ⟨by simp only [dd, if_neg h], by simp only [pp, if_neg h]⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exact Or.inl rfl
  · by_cases h : w.1 = j
    · refine Or.inr (Or.inl ?_)
      simp only [Big, dd, if_pos h]
      exact G.hM_block w
    · exact Or.inr (Or.inr ⟨by simp only [dd, if_neg h], by simp only [pp, if_neg h]⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · by_cases h : x.1.1 = j
    · refine Or.inr (Or.inl ?_)
      simp only [Big, dd, if_pos h]
      exact G.hM_slot x
    · exact Or.inr (Or.inr ⟨by simp only [dd, if_neg h], rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · by_cases hx1 : x = e.1
    · exact Or.inr (Or.inl (by simp only [Big, dd, if_pos hx1]; omega))
    · by_cases hx2 : x = G.rev e.1
      · exact Or.inr (Or.inl (by simp only [Big, dd, if_neg hx1, if_pos hx2]; omega))
      · exact Or.inr (Or.inr ⟨by simp only [dd, if_neg hx1, if_neg hx2], rfl⟩)
  · rcases b with _ | _
    · refine Or.inr (Or.inl ?_)
      have hv : G.dd (G.dE e) (G.ci false) = 3 := rfl
      simp only [Big, hv]
      omega
    · refine Or.inr (Or.inl ?_)
      have hv : G.dd (G.dE e) (G.ci true) = 4 := rfl
      simp only [Big, hv]
      omega
  · exact Or.inl rfl

/-- A parked client's job is exactly its own slot. -/
lemma small_dd {i : G.Day} {c : G.Client} (h : G.Small i c) :
    G.dd i c = G.parkD c ∧ G.pp i c = 1 := by
  rcases G.trichotomy i c with h1 | h1 | h1
  · exact absurd h1 h.1
  · exact absurd h1 h.2
  · exact h1

/-- **The dummy conflicts with every parked client**: their slots lie inside its job. -/
lemma conflict_c0_small {i : G.Day} {c : G.Client} (h : G.Small i c) :
    (G.inst).Conflict i G.c0 c := by
  obtain ⟨hd, hp⟩ := G.small_dd h
  have hc := G.cidx_lt c
  refine ⟨?_, ?_⟩ <;> show G.dd i _ - G.pp i _ < G.dd i _
  · rw [dd_c0, pp_c0, hd]
    simp only [parkD]
    omega
  · rw [hd, hp, dd_c0]
    simp only [parkD]
    omega

/-- …and with nothing that has a gadget job. -/
lemma not_conflict_c0_big {i : G.Day} {c : G.Client} (h : G.Big i c) :
    ¬ (G.inst).Conflict i G.c0 c := by
  refine not_conflict_of_le' ?_
  show G.dd i c ≤ G.dd i G.c0 - G.pp i G.c0
  rw [dd_c0, pp_c0]
  simpa [Big] using h

/-- A parked client conflicts with nothing that has a gadget job. -/
lemma not_conflict_small_big {i : G.Day} {c c' : G.Client}
    (h : G.Small i c) (h' : G.Big i c') : ¬ (G.inst).Conflict i c c' := by
  obtain ⟨hd, hp⟩ := G.small_dd h
  refine not_conflict_of_le' ?_
  show G.dd i c' ≤ G.dd i c - G.pp i c
  rw [hd, hp]
  simp only [Big] at h'
  simp only [parkD]
  omega

/-- Two parked clients occupy different slots. -/
lemma not_conflict_small_small {i : G.Day} {c c' : G.Client}
    (h : G.Small i c) (h' : G.Small i c') (hne : c ≠ c') :
    ¬ (G.inst).Conflict i c c' := by
  obtain ⟨hd, hp⟩ := G.small_dd h
  obtain ⟨hd', hp'⟩ := G.small_dd h'
  have hidx : G.cidx c ≠ G.cidx c' := fun hh => hne (G.cidx_injective hh)
  rcases Nat.lt_or_ge (G.cidx c) (G.cidx c') with hlt | hge
  · refine not_conflict_of_le ?_
    show G.dd i c ≤ G.dd i c' - G.pp i c'
    rw [hd, hd', hp']
    simp only [parkD]
    omega
  · refine not_conflict_of_le' ?_
    show G.dd i c' ≤ G.dd i c - G.pp i c
    rw [hd, hd', hp]
    simp only [parkD]
    omega

/-! ## 4. Which big jobs conflict

Three lemmas per day type: which clients are big, and which of the big ones conflict. Day
1's and day 3's are pure case analysis; day 2's is the block arithmetic of the validation
gadget. -/

private lemma mul_step (a : ℕ) : G.r * (a + 2) = G.r * (a + 1) + G.r := by ring

/-- A conflict, stated in terms of the raw due dates and processing times. -/
private lemma conflict_of_dd {i : G.Day} {c c' : G.Client}
    (h1 : G.dd i c - G.pp i c < G.dd i c') (h2 : G.dd i c' - G.pp i c' < G.dd i c) :
    (G.inst).Conflict i c c' := ⟨h1, h2⟩

/-! ### Vertex days -/

/-- On `v`'s vertex day only `c_v` and `c_{colour v}` have a job of their own. -/
lemma big_dV (v : G.Vtx) (c : G.Client) :
    G.Big (G.dV v) c ↔ (c = G.cv v ∨ c = G.cs v.1) := by
  have hpark : ∀ c' : G.Client, ¬ G.parkD c' ≤ G.M := fun c' => by
    have := G.M_lt_parkD c'; omega
  have hN := G.N_pos
  rcases c with w | (i' | (x | (b | u))) <;> simp only [Big, dd]
  · by_cases hw : w = v
    · rw [if_pos hw]
      have := G.hM_vertex
      simp [hw]
      omega
    · rw [if_neg hw]
      simp only [hpark, false_iff, not_or]
      exact ⟨fun h => hw (Sum.inl_injective h), by simp⟩
  · by_cases hw : i' = v.1
    · rw [if_pos hw]
      have := G.hM_vertex
      simp [hw]
      omega
    · rw [if_neg hw]
      simp only [hpark, false_iff, not_or]
      exact ⟨by simp, fun h => hw (Sum.inl_injective (Sum.inr_injective h))⟩
  · simp [hpark]
  · simp [hpark]
  · simp; omega

/-- …and they conflict: their jobs are the same job. -/
lemma conflict_dV (v : G.Vtx) : (G.inst).Conflict (G.dV v) (G.cv v) (G.cs v.1) := by
  refine conflict_of_eq ?_ ?_
  · show G.pp (G.dV v) (G.cv v) = G.pp (G.dV v) (G.cs v.1)
    simp [pp]
  · show G.dd (G.dV v) (G.cv v) = G.dd (G.dV v) (G.cs v.1)
    simp [dd]

/-! ### Validation days -/

/-- On colour `i`'s validation day, the big clients are the vertex clients of colour `i` and
their edge clients. -/
lemma big_dW (i : Fin G.ℓ) (c : G.Client) :
    G.Big (G.dW i) c ↔
      ((∃ w : G.Vtx, w.1 = i ∧ c = G.cv w) ∨ ∃ x : G.Inc, x.1.1 = i ∧ c = G.ce x) := by
  have hpark : ∀ c' : G.Client, ¬ G.parkD c' ≤ G.M := fun c' => by
    have := G.M_lt_parkD c'; omega
  have hN := G.N_pos
  constructor
  · intro h
    rcases c with w | (i' | (x | (b | u)))
    · refine Or.inl ⟨w, ?_, rfl⟩
      by_contra hw
      simp only [Big, dd, if_neg hw] at h
      exact hpark _ h
    · simp only [Big, dd] at h; exact absurd h (hpark _)
    · refine Or.inr ⟨x, ?_, rfl⟩
      by_contra hx
      simp only [Big, dd, if_neg hx] at h
      exact hpark _ h
    · simp only [Big, dd] at h; exact absurd h (hpark _)
    · simp only [Big, dd] at h; omega
  · rintro (⟨w, hw, rfl⟩ | ⟨x, hx, rfl⟩)
    · simp only [Big, dd, if_pos hw]; exact G.hM_block w
    · simp only [Big, dd, if_pos hx]; exact G.hM_slot x

/-- A vertex client blocks exactly its own edge clients. -/
lemma conflict_dW_self (w : G.Vtx) (q : Fin G.r) :
    (G.inst).Conflict (G.dW w.1) (G.cv w) (G.ce (w, q)) := by
  have hr := G.r_pos
  have hq := q.isLt
  have hstep := G.mul_step w.2.val
  have hdw : G.dd (G.dW w.1) (G.cv w) = G.r * (w.2.val + 2) := by simp [dd]
  have hpw : G.pp (G.dW w.1) (G.cv w) = G.r := by simp [pp]
  have hdx : G.dd (G.dW w.1) (G.ce (w, q)) = G.r * (w.2.val + 1) + q.val + 1 := by
    simp [dd]
  have hpx : G.pp (G.dW w.1) (G.ce (w, q)) = 1 := rfl
  refine G.conflict_of_dd ?_ ?_
  · rw [hdw, hpw, hdx]; omega
  · rw [hdx, hpx, hdw]; omega

/-- …and nothing else on that day. -/
lemma not_conflict_dW_cv_ce {i : Fin G.ℓ} {w : G.Vtx} {x : G.Inc}
    (hw : w.1 = i) (hx : x.1.1 = i) (hne : x.1 ≠ w) :
    ¬ (G.inst).Conflict (G.dW i) (G.cv w) (G.ce x) := by
  have hr := G.r_pos
  have hq := x.2.isLt
  have hdw : G.dd (G.dW i) (G.cv w) = G.r * (w.2.val + 2) := by simp only [dd, if_pos hw]
  have hpw : G.pp (G.dW i) (G.cv w) = G.r := by simp only [pp, if_pos hw]
  have hdx : G.dd (G.dW i) (G.ce x) = G.r * (x.1.2.val + 1) + x.2.val + 1 := by
    simp only [dd, if_pos hx]
  have hpx : G.pp (G.dW i) (G.ce x) = 1 := rfl
  have hp : x.1.2 ≠ w.2 := fun h => hne (Prod.ext (by rw [hx, hw]) h)
  rcases Nat.lt_or_ge x.1.2.val w.2.val with hlt | hge
  · refine not_conflict_of_le' ?_
    show G.dd (G.dW i) (G.ce x) ≤ G.dd (G.dW i) (G.cv w) - G.pp (G.dW i) (G.cv w)
    rw [hdw, hpw, hdx]
    have h1 := G.mul_step x.1.2.val
    have h2 := G.mul_mono (a := x.1.2.val + 2) (b := w.2.val + 1) (by omega)
    have h3 := G.mul_step w.2.val
    omega
  · have hlt' : w.2.val < x.1.2.val := by
      rcases Nat.lt_or_ge w.2.val x.1.2.val with h | h
      · exact h
      · exact absurd (Fin.ext (by omega)) hp
    refine not_conflict_of_le ?_
    show G.dd (G.dW i) (G.cv w) ≤ G.dd (G.dW i) (G.ce x) - G.pp (G.dW i) (G.ce x)
    rw [hdw, hdx, hpx]
    have h2 := G.mul_mono (a := w.2.val + 2) (b := x.1.2.val + 1) (by omega)
    omega

/-- Two different edge clients of the same colour occupy different unit slots. -/
lemma not_conflict_dW_ce_ce {i : Fin G.ℓ} {x x' : G.Inc}
    (hx : x.1.1 = i) (hx' : x'.1.1 = i) (hne : x ≠ x') :
    ¬ (G.inst).Conflict (G.dW i) (G.ce x) (G.ce x') := by
  have hr := G.r_pos
  have hq := x.2.isLt
  have hq' := x'.2.isLt
  have hdx : G.dd (G.dW i) (G.ce x) = G.r * (x.1.2.val + 1) + x.2.val + 1 := by
    simp only [dd, if_pos hx]
  have hdx' : G.dd (G.dW i) (G.ce x') = G.r * (x'.1.2.val + 1) + x'.2.val + 1 := by
    simp only [dd, if_pos hx']
  have hpx : G.pp (G.dW i) (G.ce x) = 1 := rfl
  have hpx' : G.pp (G.dW i) (G.ce x') = 1 := rfl
  have hslot : G.r * (x.1.2.val + 1) + x.2.val ≠ G.r * (x'.1.2.val + 1) + x'.2.val := by
    intro h
    refine hne ?_
    rcases Nat.lt_trichotomy x.1.2.val x'.1.2.val with hlt | heq | hgt
    · have h1 := G.mul_step x.1.2.val
      have h2 := G.mul_mono (a := x.1.2.val + 2) (b := x'.1.2.val + 1) (by omega)
      omega
    · have hpe : x.1.2 = x'.1.2 := Fin.ext heq
      have hqe : x.2 = x'.2 := Fin.ext (by rw [heq] at h; omega)
      exact Prod.ext (Prod.ext (by rw [hx, hx']) hpe) hqe
    · have h1 := G.mul_step x'.1.2.val
      have h2 := G.mul_mono (a := x'.1.2.val + 2) (b := x.1.2.val + 1) (by omega)
      omega
  rcases Nat.lt_or_ge (G.r * (x.1.2.val + 1) + x.2.val)
      (G.r * (x'.1.2.val + 1) + x'.2.val) with hlt | hge
  · refine not_conflict_of_le ?_
    show G.dd (G.dW i) (G.ce x) ≤ G.dd (G.dW i) (G.ce x') - G.pp (G.dW i) (G.ce x')
    rw [hdx, hdx', hpx']
    omega
  · refine not_conflict_of_le' ?_
    show G.dd (G.dW i) (G.ce x') ≤ G.dd (G.dW i) (G.ce x) - G.pp (G.dW i) (G.ce x)
    rw [hdx, hdx', hpx]
    omega

/-! ### Edge days -/

/-- On the edge day of `e`, the big clients are the edge's two edge clients and the two
interaction clients. -/
lemma big_dE (e : G.Edge) (c : G.Client) :
    G.Big (G.dE e) c ↔
      (c = G.ce e.1 ∨ c = G.ce (G.rev e.1) ∨ c = G.ci true ∨ c = G.ci false) := by
  have hpark : ∀ c' : G.Client, ¬ G.parkD c' ≤ G.M := fun c' => by
    have := G.M_lt_parkD c'; omega
  have hN := G.N_pos
  have h4 := G.hM_four
  constructor
  · intro h
    rcases c with w | (i' | (x | (b | u)))
    · simp only [Big, dd] at h; exact absurd h (hpark _)
    · simp only [Big, dd] at h; exact absurd h (hpark _)
    · by_cases h1 : x = e.1
      · exact Or.inl (by rw [h1])
      · by_cases h2 : x = G.rev e.1
        · exact Or.inr (Or.inl (by rw [h2]))
        · simp only [Big, dd, if_neg h1, if_neg h2] at h; exact absurd h (hpark _)
    · cases b
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl rfl))
    · simp only [Big, dd] at h; omega
  · have hne : G.rev e.1 ≠ e.1 := G.rev_ne e.1
    rintro (rfl | rfl | rfl | rfl)
    · have hv : G.dd (G.dE e) (G.ce e.1) = 4 := by simp [dd]
      simp only [Big, hv]; omega
    · have hv : G.dd (G.dE e) (G.ce (G.rev e.1)) = 2 := by simp [dd, if_neg hne]
      simp only [Big, hv]; omega
    · have hv : G.dd (G.dE e) (G.ci true) = 4 := rfl
      simp only [Big, hv]; omega
    · have hv : G.dd (G.dE e) (G.ci false) = 3 := rfl
      simp only [Big, hv]; omega

/-- The two interaction clients conflict on every edge day. -/
lemma conflict_dE_ci (e : G.Edge) : (G.inst).Conflict (G.dE e) (G.ci true) (G.ci false) :=
  G.conflict_of_dd (by simp [dd, pp]) (by simp [dd, pp])

/-- `c⁺` conflicts with the edge's tail client. -/
lemma conflict_dE_plus (e : G.Edge) :
    (G.inst).Conflict (G.dE e) (G.ce e.1) (G.ci true) :=
  G.conflict_of_dd (by simp [dd, pp]) (by simp [dd, pp])

/-- `c⁻` conflicts with the edge's head client. -/
lemma conflict_dE_minus (e : G.Edge) :
    (G.inst).Conflict (G.dE e) (G.ce (G.rev e.1)) (G.ci false) := by
  have hne : G.rev e.1 ≠ e.1 := G.rev_ne e.1
  exact G.conflict_of_dd (by simp [dd, pp, hne]) (by simp [dd, pp, hne])

/-- `c⁻` does **not** conflict with the edge's tail client: `(1,3]` and `(3,4]` are
disjoint. -/
lemma not_conflict_dE_tail_minus (e : G.Edge) :
    ¬ (G.inst).Conflict (G.dE e) (G.ce e.1) (G.ci false) := by
  refine not_conflict_of_le' ?_
  show G.dd (G.dE e) (G.ci false) ≤ G.dd (G.dE e) (G.ce e.1) - G.pp (G.dE e) (G.ce e.1)
  simp [dd, pp]

/-- `c⁺` does **not** conflict with the edge's head client: `(1,2]` and `(2,4]` are
disjoint. -/
lemma not_conflict_dE_head_plus (e : G.Edge) :
    ¬ (G.inst).Conflict (G.dE e) (G.ce (G.rev e.1)) (G.ci true) := by
  have hne : G.rev e.1 ≠ e.1 := G.rev_ne e.1
  refine not_conflict_of_le ?_
  show G.dd (G.dE e) (G.ce (G.rev e.1)) ≤
    G.dd (G.dE e) (G.ci true) - G.pp (G.dE e) (G.ci true)
  simp [dd, pp, hne]


/-! ## 5. Where each client can run

A parked job never runs, so a client's possible days are the few on which it is big. -/

private lemma small_of_not_big {i : G.Day} {c : G.Client} (hc : c ≠ G.c0)
    (h : ¬ G.Big i c) : G.Small i c := ⟨hc, h⟩

lemma small_cs_dW (i j : Fin G.ℓ) : G.Small (G.dW j) (G.cs i) :=
  G.small_of_not_big (by simp) fun hb => by
    rcases (G.big_dW j _).1 hb with ⟨w, -, h⟩ | ⟨x, -, h⟩ <;> exact absurd h (by simp)

lemma small_cs_dE (i : Fin G.ℓ) (e : G.Edge) : G.Small (G.dE e) (G.cs i) :=
  G.small_of_not_big (by simp) fun hb => by
    rcases (G.big_dE e _).1 hb with h | h | h | h <;> exact absurd h (by simp)

lemma small_cv_dE (w : G.Vtx) (e : G.Edge) : G.Small (G.dE e) (G.cv w) :=
  G.small_of_not_big (by simp) fun hb => by
    rcases (G.big_dE e _).1 hb with h | h | h | h <;> exact absurd h (by simp)

lemma small_ce_dV (x : G.Inc) (v : G.Vtx) : G.Small (G.dV v) (G.ce x) :=
  G.small_of_not_big (by simp) fun hb => by
    rcases (G.big_dV v _).1 hb with h | h <;> exact absurd h (by simp)

lemma small_ci_dV (b : Bool) (v : G.Vtx) : G.Small (G.dV v) (G.ci b) :=
  G.small_of_not_big (by simp) fun hb => by
    rcases (G.big_dV v _).1 hb with h | h <;> exact absurd h (by simp)

lemma small_ci_dW (b : Bool) (i : Fin G.ℓ) : G.Small (G.dW i) (G.ci b) :=
  G.small_of_not_big (by simp) fun hb => by
    rcases (G.big_dW i _).1 hb with ⟨w, -, h⟩ | ⟨x, -, h⟩ <;> exact absurd h (by simp)

lemma small_cs_dV_ne {i : Fin G.ℓ} {v : G.Vtx} (h : i ≠ v.1) : G.Small (G.dV v) (G.cs i) :=
  G.small_of_not_big (by simp) fun hb => by
    rcases (G.big_dV v _).1 hb with hh | hh
    · exact absurd hh (by simp)
    · exact h (Sum.inl_injective (Sum.inr_injective hh))

lemma small_cv_dV_ne {w v : G.Vtx} (h : w ≠ v) : G.Small (G.dV v) (G.cv w) :=
  G.small_of_not_big (by simp) fun hb => by
    rcases (G.big_dV v _).1 hb with hh | hh
    · exact h (Sum.inl_injective hh)
    · exact absurd hh (by simp)

lemma small_cv_dW_ne {w : G.Vtx} {i : Fin G.ℓ} (h : w.1 ≠ i) : G.Small (G.dW i) (G.cv w) :=
  G.small_of_not_big (by simp) fun hb => by
    rcases (G.big_dW i _).1 hb with ⟨w', hw', hh⟩ | ⟨x, -, hh⟩
    · exact h (by rw [Sum.inl_injective hh]; exact hw')
    · exact absurd hh (by simp)

lemma small_ce_dW_ne {x : G.Inc} {i : Fin G.ℓ} (h : x.1.1 ≠ i) : G.Small (G.dW i) (G.ce x) :=
  G.small_of_not_big (by simp) fun hb => by
    rcases (G.big_dW i _).1 hb with ⟨w, -, hh⟩ | ⟨x', hx', hh⟩
    · exact absurd hh (by simp)
    · exact h (by
        rw [Sum.inl_injective (Sum.inr_injective (Sum.inr_injective hh))]; exact hx')

lemma small_ce_dE_ne {x : G.Inc} {e : G.Edge} (h1 : x ≠ e.1) (h2 : x ≠ G.rev e.1) :
    G.Small (G.dE e) (G.ce x) :=
  G.small_of_not_big (by simp) fun hb => by
    rcases (G.big_dE e _).1 hb with hh | hh | hh | hh
    · exact h1 (Sum.inl_injective (Sum.inr_injective (Sum.inr_injective hh)))
    · exact h2 (Sum.inl_injective (Sum.inr_injective (Sum.inr_injective hh)))
    · exact absurd hh (by simp)
    · exact absurd hh (by simp)

/-! ## 6. From a fair schedule to a multicolored independent set -/

section Backward

variable {G} {half : ℕ} {σ : (G.inst).Schedule}

/-- The dummy client runs on every day. -/
lemma mem_c0 (hfair : Fair (G.kvec half) σ) (i : (G.inst).Day) : G.c0 ∈ σ i := by
  refine Instance.mem_of_served_eq_numDays ?_ i
  have h := hfair G.c0
  show (G.inst).numDays ≤ served σ G.c0
  exact h

/-- …so nothing else with a unit job that day runs. -/
lemma not_mem_of_small (hfeas : Feasible σ) (hfair : Fair (G.kvec half) σ)
    {i : G.Day} {c : G.Client} (hs : G.Small i c) (hne : c ≠ G.c0) : c ∉ σ i := fun hmem =>
  hfeas i c hmem G.c0 (mem_c0 hfair i) hne (conflict_symm (G.conflict_c0_small hs))

/-- Every selection client runs, and only on a vertex day of its own colour. -/
lemma exists_sel (hfeas : Feasible σ) (hfair : Fair (G.kvec half) σ) (i : Fin G.ℓ) :
    ∃ v : G.Vtx, v.1 = i ∧ G.cs i ∈ σ (G.dV v) := by
  obtain ⟨d, hd⟩ := Instance.exists_mem_of_served_pos
    (lt_of_lt_of_le Nat.zero_lt_one (hfair (G.cs i)))
  rcases d with v | (j | e)
  · by_cases hv : i = v.1
    · exact ⟨v, hv.symm, hd⟩
    · exact absurd hd (not_mem_of_small hfeas hfair (G.small_cs_dV_ne hv) (by simp))
  · exact absurd hd (not_mem_of_small hfeas hfair (G.small_cs_dW i j) (by simp))
  · exact absurd hd (not_mem_of_small hfeas hfair (G.small_cs_dE i e) (by simp))

/-- A vertex client whose own vertex day is taken by the selection client runs on its
colour's validation day instead. -/
lemma mem_cv_dW (hfeas : Feasible σ) (hfair : Fair (G.kvec half) σ)
    {v : G.Vtx} (hsel : G.cs v.1 ∈ σ (G.dV v)) : G.cv v ∈ σ (G.dW v.1) := by
  obtain ⟨d, hd⟩ := Instance.exists_mem_of_served_pos
    (lt_of_lt_of_le Nat.zero_lt_one (hfair (G.cv v)))
  rcases d with w | (j | e)
  · by_cases hw : v = w
    · subst hw
      exact absurd (G.conflict_dV v) (hfeas (G.dV v) _ hd _ hsel (by simp))
    · exact absurd hd (not_mem_of_small hfeas hfair (G.small_cv_dV_ne hw) (by simp))
  · by_cases hj : v.1 = j
    · exact hj ▸ hd
    · exact absurd hd (not_mem_of_small hfeas hfair (G.small_cv_dW_ne hj) (by simp))
  · exact absurd hd (not_mem_of_small hfeas hfair (G.small_cv_dE v e) (by simp))

/-- …and then each of its edge clients is pushed onto its own edge day. -/
lemma mem_ce_dE (hfeas : Feasible σ) (hfair : Fair (G.kvec half) σ)
    {v : G.Vtx} (hv : G.cv v ∈ σ (G.dW v.1)) (q : Fin G.r) :
    G.ce (v, q) ∈ σ (G.dE (G.edgeOf (v, q))) := by
  obtain ⟨d, hd⟩ := Instance.exists_mem_of_served_pos
    (lt_of_lt_of_le Nat.zero_lt_one (hfair (G.ce (v, q))))
  rcases d with w | (j | e)
  · exact absurd hd (not_mem_of_small hfeas hfair (G.small_ce_dV (v, q) w) (by simp))
  · by_cases hj : v.1 = j
    · subst hj
      exact absurd (G.conflict_dW_self v q) (hfeas (G.dW v.1) _ hv _ hd (by simp))
    · exact absurd hd (not_mem_of_small hfeas hfair (G.small_ce_dW_ne hj) (by simp))
  · by_cases h1 : (v, q) = e.1
    · have he : G.edgeOf (v, q) = e := by
        rw [h1, G.edgeOf_tail e.2]
      exact he ▸ hd
    · by_cases h2 : (v, q) = G.rev e.1
      · have he : G.edgeOf (v, q) = e := by
          rw [h2, G.edgeOf_rev, G.edgeOf_tail e.2]
        exact he ▸ hd
      · exact absurd hd (not_mem_of_small hfeas hfair (G.small_ce_dE_ne h1 h2) (by simp))


/-- The two interaction clients live only on edge days, where they conflict; since they need
`|E|/2` days each and there are `|E|` edge days, **every edge day runs exactly one of
them**. -/
lemma exists_ci_dE (hfeas : Feasible σ) (hfair : Fair (G.kvec half) σ)
    (hhalf : 2 * half = Fintype.card G.Edge) (e : G.Edge) :
    G.ci true ∈ σ (G.dE e) ∨ G.ci false ∈ σ (G.dE e) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  set f : G.Vtx ⊕ (Fin G.ℓ ⊕ G.Edge) → ℕ := fun d =>
    (if G.ci true ∈ σ d then 1 else 0) + (if G.ci false ∈ σ d then 1 else 0) with hf
  have hone : ∀ d, f d ≤ 1 := by
    intro d
    by_cases ha : G.ci true ∈ σ d
    · by_cases hb : G.ci false ∈ σ d
      · rcases d with v | (i | e')
        · exact absurd (not_mem_of_small hfeas hfair (G.small_ci_dV true v) (by simp)) (by
            simpa using ha)
        · exact absurd (not_mem_of_small hfeas hfair (G.small_ci_dW true i) (by simp)) (by
            simpa using ha)
        · exact absurd (G.conflict_dE_ci e') (hfeas (G.dE e') _ ha _ hb (by simp))
      · simp [hf, ha, hb]
    · by_cases hb : G.ci false ∈ σ d <;> simp [hf, ha, hb]
  have hzeroV : ∀ v : G.Vtx, f (G.dV v) = 0 := by
    intro v
    have ha := not_mem_of_small hfeas hfair (G.small_ci_dV true v) (by simp)
    have hb := not_mem_of_small hfeas hfair (G.small_ci_dV false v) (by simp)
    simp [hf, ha, hb]
  have hzeroW : ∀ i : Fin G.ℓ, f (G.dW i) = 0 := by
    intro i
    have ha := not_mem_of_small hfeas hfair (G.small_ci_dW true i) (by simp)
    have hb := not_mem_of_small hfeas hfair (G.small_ci_dW false i) (by simp)
    simp [hf, ha, hb]
  -- the total is the sum over the edge days alone
  have hsplit : (∑ d : G.Vtx ⊕ (Fin G.ℓ ⊕ G.Edge), f d)
      = ∑ e' : G.Edge, f (Sum.inr (Sum.inr e')) := by
    have e1 : (∑ d : G.Vtx ⊕ (Fin G.ℓ ⊕ G.Edge), f d)
        = (∑ v : G.Vtx, f (Sum.inl v)) + ∑ d : Fin G.ℓ ⊕ G.Edge, f (Sum.inr d) :=
      Fintype.sum_sum_type _
    have e2 : (∑ d : Fin G.ℓ ⊕ G.Edge, f (Sum.inr d))
        = (∑ i : Fin G.ℓ, f (Sum.inr (Sum.inl i))) + ∑ e' : G.Edge, f (Sum.inr (Sum.inr e')) :=
      Fintype.sum_sum_type _
    have e3 : (∑ v : G.Vtx, f (Sum.inl v)) = 0 := Finset.sum_eq_zero fun v _ => hzeroV v
    have e4 : (∑ i : Fin G.ℓ, f (Sum.inr (Sum.inl i))) = 0 :=
      Finset.sum_eq_zero fun i _ => hzeroW i
    omega
  -- but that sum misses `e`, so it is at most `|E| - 1`
  have hbound : ∑ e' : G.Edge, f (Sum.inr (Sum.inr e')) ≤ Fintype.card G.Edge - 1 := by
    rw [← Finset.sum_erase_add Finset.univ (fun e' => f (Sum.inr (Sum.inr e')))
      (Finset.mem_univ e)]
    have hfe : f (Sum.inr (Sum.inr e)) = 0 := by simp [hf, h1, h2]
    have hle : ∑ e' ∈ Finset.univ.erase e, f (Sum.inr (Sum.inr e'))
        ≤ (Finset.univ.erase e).card := by
      calc ∑ e' ∈ Finset.univ.erase e, f (Sum.inr (Sum.inr e'))
            ≤ ∑ _e' ∈ Finset.univ.erase e, 1 := Finset.sum_le_sum fun e' _ => hone _
        _ = (Finset.univ.erase e).card := by simp
    rw [Finset.card_erase_of_mem (Finset.mem_univ e), Finset.card_univ] at hle
    omega
  -- yet the two interaction clients need `2 · (|E|/2) = |E|` days between them
  have hsum : served σ (G.ci true) + served σ (G.ci false)
      = ∑ d : G.Vtx ⊕ (Fin G.ℓ ⊕ G.Edge), f d := by
    rw [served_eq_sum, served_eq_sum, ← Finset.sum_add_distrib]
  have hA : half ≤ served σ (G.ci true) := hfair (G.ci true)
  have hB : half ≤ served σ (G.ci false) := hfair (G.ci false)
  have hpos : 0 < Fintype.card G.Edge := Fintype.card_pos_iff.2 ⟨e⟩
  omega

/-- **Lemma 14, the `⇐` direction.** A feasible, fair schedule of the constructed instance
exhibits a multicolored independent set. -/
theorem hasIndepSet_of_fair (hhalf : 2 * half = Fintype.card G.Edge)
    (hfeas : Feasible σ) (hfair : Fair (G.kvec half) σ) : G.HasIndepSet := by
  choose selv hselc hselm using exists_sel hfeas hfair
  have hvert : ∀ i, selv i = (i, (selv i).2) := fun i => Prod.ext (hselc i) rfl
  refine ⟨fun i => (selv i).2, ?_⟩
  rintro i i' ⟨q, hq⟩
  -- rewrite the adjacency in terms of the chosen vertices
  rw [← hvert i, ← hvert i'] at hq
  -- both endpoints' edge clients are pushed onto the same edge day
  have hvi : G.cv (selv i) ∈ σ (G.dW (selv i).1) :=
    mem_cv_dW hfeas hfair (by rw [hselc i]; exact hselm i)
  have hvi' : G.cv (selv i') ∈ σ (G.dW (selv i').1) :=
    mem_cv_dW hfeas hfair (by rw [hselc i']; exact hselm i')
  have hx := mem_ce_dE hfeas hfair hvi q
  have hxr := mem_ce_dE hfeas hfair hvi' (G.revq (selv i) q)
  have hrevEq : (selv i', G.revq (selv i) q) = G.rev (selv i, q) := by
    rw [← hq]; rfl
  rw [hrevEq, G.edgeOf_rev] at hxr
  set e := G.edgeOf (selv i, q) with he
  -- both edge clients of `e` run on `e`'s day
  have hboth : G.ce e.1 ∈ σ (G.dE e) ∧ G.ce (G.rev e.1) ∈ σ (G.dE e) := by
    rcases G.mem_edgeOf (x := (selv i, q)) he.symm with h | h
    · exact ⟨h ▸ hx, h ▸ hxr⟩
    · refine ⟨?_, ?_⟩
      · have : G.rev (selv i, q) = e.1 := by rw [h, G.rev_rev]
        exact this ▸ hxr
      · exact h ▸ hx
  -- but one of the interaction clients also runs there, and it blocks one of them
  rcases exists_ci_dE hfeas hfair hhalf e with hci | hci
  · exact absurd (G.conflict_dE_plus e) (hfeas (G.dE e) _ hboth.1 _ hci (by simp))
  · exact absurd (G.conflict_dE_minus e) (hfeas (G.dE e) _ hboth.2 _ hci (by simp))

end Backward


/-! ## 7. From a multicolored independent set to a fair schedule

The chosen vertices push their edge clients onto the edge days, and each such edge day is
then forced to run one particular interaction client. Independence is exactly what stops one
edge day from being forced *both* ways. -/

section Forward

variable {G}
variable (sel : Fin G.ℓ → Fin G.n)

/-- An incidence is **selected** when its vertex is the chosen one of its colour. -/
def Sel (x : G.Inc) : Prop := x.1.2 = sel x.1.1

instance (x : G.Inc) : Decidable (Sel sel x) := by unfold Sel; infer_instance

/-- A selected incidence is determined by its colour and its neighbour index. -/
lemma inc_eq_of_sel {x y : G.Inc} (hx : Sel sel x) (hy : Sel sel y)
    (h1 : x.1.1 = y.1.1) (h2 : x.2 = y.2) : x = y := by
  refine Prod.ext (Prod.ext h1 ?_) h2
  simp only [Sel] at hx hy
  rw [hx, hy, h1]

/-- **Independence, in the form the construction uses**: no edge has both of its incidences
selected. -/
lemma not_sel_rev (hindep : ∀ i i' : Fin G.ℓ, ¬ G.Adj (i, sel i) (i', sel i'))
    {x : G.Inc} (hx : Sel sel x) : ¬ Sel sel (G.rev x) := by
  intro hr
  simp only [Sel, rev] at hx hr
  refine hindep x.1.1 (G.nbr x.1 x.2).1 ⟨x.2, ?_⟩
  have h1 : ((x.1.1, sel x.1.1) : G.Vtx) = x.1 := Prod.ext rfl hx.symm
  rw [h1]
  exact Prod.ext rfl hr

/-- The edges whose *tail* incidence is selected: their day is forced to run `c⁻`. -/
def AEdges : Finset G.Edge := Finset.univ.filter fun e => Sel sel e.1

/-- The edges whose *head* incidence is selected: their day is forced to run `c⁺`. -/
def BEdges : Finset G.Edge := Finset.univ.filter fun e => Sel sel (G.rev e.1)

lemma disjoint_AB (hindep : ∀ i i' : Fin G.ℓ, ¬ G.Adj (i, sel i) (i', sel i')) :
    Disjoint (AEdges sel) (BEdges sel) := by
  refine Finset.disjoint_left.2 fun e ha hb => ?_
  simp only [AEdges, BEdges, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact not_sel_rev sel hindep ha hb

/-- The forced edges number at most `ℓ · r`: each is charged to a chosen vertex together with
one of that vertex's `r` neighbour indices. -/
lemma card_AB_le (hindep : ∀ i i' : Fin G.ℓ, ¬ G.Adj (i, sel i) (i', sel i')) :
    (AEdges sel).card + (BEdges sel).card ≤ G.ℓ * G.r := by
  classical
  rw [← Finset.card_union_of_disjoint (disjoint_AB sel hindep)]
  set g : G.Edge → Fin G.ℓ × Fin G.r := fun e =>
    if Sel sel e.1 then (e.1.1.1, e.1.2) else ((G.rev e.1).1.1, (G.rev e.1).2) with hg
  have hinj : ∀ e ∈ AEdges sel ∪ BEdges sel, ∀ e' ∈ AEdges sel ∪ BEdges sel,
      g e = g e' → e = e' := by
    intro e he e' he' hEq
    -- the incidence each edge is charged with
    have hchoose : ∀ f ∈ AEdges sel ∪ BEdges sel,
        ∃ x : G.Inc, G.edgeOf x = f ∧ Sel sel x ∧ g f = (x.1.1, x.2) := by
      intro f hf
      simp only [AEdges, BEdges, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and] at hf
      by_cases hs : Sel sel f.1
      · exact ⟨f.1, G.edgeOf_tail f.2, hs, by simp [hg, hs]⟩
      · have hs' : Sel sel (G.rev f.1) := hf.resolve_left hs
        exact ⟨G.rev f.1, by rw [G.edgeOf_rev, G.edgeOf_tail f.2], hs', by simp [hg, hs]⟩
    obtain ⟨x, hx1, hx2, hx3⟩ := hchoose e he
    obtain ⟨y, hy1, hy2, hy3⟩ := hchoose e' he'
    have hpair : ((x.1.1, x.2) : Fin G.ℓ × Fin G.r) = (y.1.1, y.2) :=
      hx3.symm.trans (hEq.trans hy3)
    have hc1 : x.1.1 = y.1.1 := congrArg (fun p : Fin G.ℓ × Fin G.r => p.1) hpair
    have hc2 : x.2 = y.2 := congrArg (fun p : Fin G.ℓ × Fin G.r => p.2) hpair
    have hxy : x = y := inc_eq_of_sel sel hx2 hy2 hc1 hc2
    rw [← hx1, ← hy1, hxy]
  have := Finset.card_le_card_of_injOn g (fun e _ => Finset.mem_univ (g e)) hinj
  simpa [Fintype.card_prod] using this


/-! ### The schedule -/

variable (S : Finset G.Edge)

/-- A vertex is **chosen** when it is the selected vertex of its colour. -/
def SelV (v : G.Vtx) : Prop := v.2 = sel v.1

instance (v : G.Vtx) : Decidable (SelV sel v) := by unfold SelV; infer_instance

/-- **The schedule of Lemma 14's `⇒` direction.** Each day runs the dummy, plus: on a vertex
day, the selection client if the vertex is chosen and the vertex client otherwise; on a
validation day, the chosen vertex's client together with every *unchosen* vertex's edge
clients; on an edge day, the selected incidence's client (if any) and whichever interaction
client does not conflict with it. -/
noncomputable def sched : (G.inst).Schedule := fun d =>
  match d with
  | Sum.inl v => if SelV sel v then {G.c0, G.cs v.1} else {G.c0, G.cv v}
  | Sum.inr (Sum.inl i) =>
      insert G.c0 (insert (G.cv (i, sel i))
        ((Finset.univ.filter fun x : G.Inc => x.1.1 = i ∧ ¬ Sel sel x).image G.ce))
  | Sum.inr (Sum.inr e) =>
      insert G.c0 (insert (G.ci (decide (e ∈ BEdges sel ∪ S)))
        ((if Sel sel e.1 then ({G.ce e.1} : Finset G.Client) else ∅) ∪
         (if Sel sel (G.rev e.1) then ({G.ce (G.rev e.1)} : Finset G.Client) else ∅)))

lemma mem_sched_dV (v : G.Vtx) (c : G.Client) :
    c ∈ sched sel S (G.dV v) ↔
      (c = G.c0 ∨ (SelV sel v ∧ c = G.cs v.1) ∨ (¬ SelV sel v ∧ c = G.cv v)) := by
  by_cases h : SelV sel v <;> simp [sched, h]

lemma mem_sched_dW (i : Fin G.ℓ) (c : G.Client) :
    c ∈ sched sel S (G.dW i) ↔
      (c = G.c0 ∨ c = G.cv (i, sel i) ∨ ∃ x : G.Inc, x.1.1 = i ∧ ¬ Sel sel x ∧ c = G.ce x) := by
  simp only [sched, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro (h | h | ⟨x, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨x, h1, h2, rfl⟩)
  · rintro (h | h | ⟨x, h1, h2, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨x, ⟨h1, h2⟩, rfl⟩)

lemma mem_sched_dE (e : G.Edge) (c : G.Client) :
    c ∈ sched sel S (G.dE e) ↔
      (c = G.c0 ∨ c = G.ci (decide (e ∈ BEdges sel ∪ S)) ∨
        (Sel sel e.1 ∧ c = G.ce e.1) ∨ (Sel sel (G.rev e.1) ∧ c = G.ce (G.rev e.1))) := by
  simp only [sched, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases h with h | h
      · by_cases hs : Sel sel e.1
        · rw [if_pos hs, Finset.mem_singleton] at h
          exact Or.inr (Or.inr (Or.inl ⟨hs, h⟩))
        · rw [if_neg hs] at h
          exact absurd h (Finset.notMem_empty c)
      · by_cases hs : Sel sel (G.rev e.1)
        · rw [if_pos hs, Finset.mem_singleton] at h
          exact Or.inr (Or.inr (Or.inr ⟨hs, h⟩))
        · rw [if_neg hs] at h
          exact absurd h (Finset.notMem_empty c)
  · rintro (h | h | ⟨hs, h⟩ | ⟨hs, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (by rw [if_pos hs, Finset.mem_singleton]; exact h)))
    · exact Or.inr (Or.inr (Or.inr (by rw [if_pos hs, Finset.mem_singleton]; exact h)))


/-! ### The schedule is feasible -/

theorem feasible_sched (hindep : ∀ i i' : Fin G.ℓ, ¬ G.Adj (i, sel i) (i', sel i'))
    (hS : S ⊆ Finset.univ \ (AEdges sel ∪ BEdges sel)) : Feasible (sched sel S) := by
  classical
  rintro (v | (i | e)) c hc c' hc' hne
  · -- a vertex day
    have hbig : ∀ x : G.Client, ((SelV sel v ∧ x = G.cs v.1) ∨ (¬ SelV sel v ∧ x = G.cv v)) →
        G.Big (G.dV v) x := by
      rintro x (⟨-, rfl⟩ | ⟨-, rfl⟩) <;> rw [G.big_dV]
      · exact Or.inr rfl
      · exact Or.inl rfl
    rcases (mem_sched_dV sel S v c).1 hc with rfl | hx
    · rcases (mem_sched_dV sel S v c').1 hc' with rfl | hy
      · exact absurd rfl hne
      · exact G.not_conflict_c0_big (hbig c' hy)
    · rcases (mem_sched_dV sel S v c').1 hc' with rfl | hy
      · exact fun hcf => G.not_conflict_c0_big (hbig c hx) (conflict_symm hcf)
      · rcases hx with ⟨hs, rfl⟩ | ⟨hs, rfl⟩ <;> rcases hy with ⟨hs', rfl⟩ | ⟨hs', rfl⟩
        · exact absurd rfl hne
        · exact absurd hs hs'
        · exact absurd hs' hs
        · exact absurd rfl hne
  · -- a validation day
    have hbig : ∀ x : G.Client,
        (x = G.cv (i, sel i) ∨ ∃ y : G.Inc, y.1.1 = i ∧ ¬ Sel sel y ∧ x = G.ce y) →
        G.Big (G.dW i) x := by
      rintro x (rfl | ⟨y, hy1, -, rfl⟩) <;> rw [G.big_dW]
      · exact Or.inl ⟨(i, sel i), rfl, rfl⟩
      · exact Or.inr ⟨y, hy1, rfl⟩
    have hnesel : ∀ y : G.Inc, y.1.1 = i → ¬ Sel sel y → y.1 ≠ (i, sel i) := by
      intro y hy1 hy2 hcon
      exact hy2 (by simp only [Sel, hcon])
    rcases (mem_sched_dW sel S i c).1 hc with rfl | hx
    · rcases (mem_sched_dW sel S i c').1 hc' with rfl | hy
      · exact absurd rfl hne
      · exact G.not_conflict_c0_big (hbig c' hy)
    · rcases (mem_sched_dW sel S i c').1 hc' with rfl | hy
      · exact fun hcf => G.not_conflict_c0_big (hbig c hx) (conflict_symm hcf)
      · rcases hx with rfl | ⟨y, hy1, hy2, rfl⟩
        · rcases hy with rfl | ⟨z, hz1, hz2, rfl⟩
          · exact absurd rfl hne
          · exact G.not_conflict_dW_cv_ce rfl hz1 (hnesel z hz1 hz2)
        · rcases hy with rfl | ⟨z, hz1, hz2, rfl⟩
          · exact fun hcf =>
              G.not_conflict_dW_cv_ce rfl hy1 (hnesel y hy1 hy2) (conflict_symm hcf)
          · refine G.not_conflict_dW_ce_ce hy1 hz1 fun hcon => hne ?_
            rw [hcon]
  · -- an edge day
    have hnotBoth : ¬ (Sel sel e.1 ∧ Sel sel (G.rev e.1)) :=
      fun ⟨h1, h2⟩ => not_sel_rev sel hindep h1 h2
    have hbig : ∀ x : G.Client,
        (x = G.ci (decide (e ∈ BEdges sel ∪ S)) ∨
          (Sel sel e.1 ∧ x = G.ce e.1) ∨ (Sel sel (G.rev e.1) ∧ x = G.ce (G.rev e.1))) →
        G.Big (G.dE e) x := by
      rintro x (rfl | ⟨-, rfl⟩ | ⟨-, rfl⟩) <;> rw [G.big_dE]
      · cases (decide (e ∈ BEdges sel ∪ S))
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    -- the interaction client the day runs is the one that fits
    have hdecA : Sel sel e.1 → decide (e ∈ BEdges sel ∪ S) = false := by
      intro hA
      have heA : e ∈ AEdges sel := Finset.mem_filter.2 ⟨Finset.mem_univ e, hA⟩
      refine decide_eq_false fun hmem => ?_
      rcases Finset.mem_union.1 hmem with hB | hSm
      · exact (Finset.disjoint_left.1 (disjoint_AB sel hindep)) heA hB
      · have := hS hSm
        simp only [Finset.mem_sdiff, Finset.mem_union] at this
        exact this.2 (Or.inl heA)
    have hdecB : Sel sel (G.rev e.1) → decide (e ∈ BEdges sel ∪ S) = true := by
      intro hB
      exact decide_eq_true (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ e, hB⟩))
    rcases (mem_sched_dE sel S e c).1 hc with rfl | hx
    · rcases (mem_sched_dE sel S e c').1 hc' with rfl | hy
      · exact absurd rfl hne
      · exact G.not_conflict_c0_big (hbig c' hy)
    · rcases (mem_sched_dE sel S e c').1 hc' with rfl | hy
      · exact fun hcf => G.not_conflict_c0_big (hbig c hx) (conflict_symm hcf)
      · rcases hx with rfl | ⟨hA, rfl⟩ | ⟨hB, rfl⟩
        · rcases hy with rfl | ⟨hA, rfl⟩ | ⟨hB, rfl⟩
          · exact absurd rfl hne
          · rw [hdecA hA]
            exact fun hcf => G.not_conflict_dE_tail_minus e (conflict_symm hcf)
          · rw [hdecB hB]
            exact fun hcf => G.not_conflict_dE_head_plus e (conflict_symm hcf)
        · rcases hy with rfl | ⟨hA', rfl⟩ | ⟨hB', rfl⟩
          · rw [hdecA hA]
            exact G.not_conflict_dE_tail_minus e
          · exact absurd rfl hne
          · exact absurd ⟨hA, hB'⟩ hnotBoth
        · rcases hy with rfl | ⟨hA', rfl⟩ | ⟨hB', rfl⟩
          · rw [hdecB hB]
            exact G.not_conflict_dE_head_plus e
          · exact absurd ⟨hA', hB⟩ hnotBoth
          · exact absurd rfl hne


/-! ### The schedule is fair -/

private lemma card_filter_eq_sum {α : Type} [Fintype α] [DecidableEq α] (p : α → Prop)
    [DecidablePred p] : (Finset.univ.filter p).card = ∑ a : α, (if p a then 1 else 0) := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The interaction clients run on exactly the edge days that call for them. -/
lemma served_ci (b : Bool) :
    served (sched sel S) (G.ci b)
      = (Finset.univ.filter fun e : G.Edge => decide (e ∈ BEdges sel ∪ S) = b).card := by
  classical
  have h1 : served (sched sel S) (G.ci b)
      = ∑ d : G.Vtx ⊕ (Fin G.ℓ ⊕ G.Edge), (if G.ci b ∈ sched sel S d then 1 else 0) :=
    served_eq_sum _ _
  have h2 : (∑ d : G.Vtx ⊕ (Fin G.ℓ ⊕ G.Edge), (if G.ci b ∈ sched sel S d then 1 else 0))
      = (∑ v : G.Vtx, (if G.ci b ∈ sched sel S (Sum.inl v) then 1 else 0))
        + ∑ d : Fin G.ℓ ⊕ G.Edge, (if G.ci b ∈ sched sel S (Sum.inr d) then 1 else 0) :=
    Fintype.sum_sum_type _
  have h3 : (∑ d : Fin G.ℓ ⊕ G.Edge, (if G.ci b ∈ sched sel S (Sum.inr d) then 1 else 0))
      = (∑ i : Fin G.ℓ, (if G.ci b ∈ sched sel S (Sum.inr (Sum.inl i)) then 1 else 0))
        + ∑ e : G.Edge, (if G.ci b ∈ sched sel S (Sum.inr (Sum.inr e)) then 1 else 0) :=
    Fintype.sum_sum_type _
  have hV : ∀ v : G.Vtx, (if G.ci b ∈ sched sel S (Sum.inl v) then 1 else 0) = 0 := by
    intro v
    have : G.ci b ∉ sched sel S (G.dV v) := by
      rw [mem_sched_dV]
      rintro (h | ⟨-, h⟩ | ⟨-, h⟩) <;> exact absurd h (by simp)
    simp [this]
  have hW : ∀ i : Fin G.ℓ, (if G.ci b ∈ sched sel S (Sum.inr (Sum.inl i)) then 1 else 0) = 0 := by
    intro i
    have : G.ci b ∉ sched sel S (G.dW i) := by
      rw [mem_sched_dW]
      rintro (h | h | ⟨x, -, -, h⟩) <;> exact absurd h (by simp)
    simp [this]
  have hE : ∀ e : G.Edge, (if G.ci b ∈ sched sel S (Sum.inr (Sum.inr e)) then 1 else 0)
      = (if decide (e ∈ BEdges sel ∪ S) = b then 1 else 0) := by
    intro e
    by_cases hb : decide (e ∈ BEdges sel ∪ S) = b
    · have : G.ci b ∈ sched sel S (G.dE e) := by
        rw [mem_sched_dE]
        exact Or.inr (Or.inl (by rw [hb]))
      rw [if_pos this, if_pos hb]
    · have : G.ci b ∉ sched sel S (G.dE e) := by
        rw [mem_sched_dE]
        rintro (h | h | ⟨-, h⟩ | ⟨-, h⟩)
        · exact absurd h (by simp)
        · exact hb (by
            have := Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective h)))
            exact this.symm)
        · exact absurd h (by simp)
        · exact absurd h (by simp)
      rw [if_neg this, if_neg hb]
  rw [card_filter_eq_sum, h1, h2, h3, Finset.sum_congr rfl fun v _ => hV v,
    Finset.sum_congr rfl fun i _ => hW i, Finset.sum_congr rfl fun e _ => hE e]
  simp

/-- **Lemma 14, the `⇒` direction.** A multicolored independent set gives a feasible, fair
schedule of the constructed instance. -/
theorem hasFairSchedule_of_hasIndepSet {half : ℕ}
    (hhalf : 2 * half = Fintype.card G.Edge) (hbal : G.ℓ * G.r ≤ half)
    (h : G.HasIndepSet) : (G.inst).HasFairSchedule (G.kvec half) := by
  classical
  obtain ⟨sel, hindep⟩ := h
  have hAB := card_AB_le sel hindep
  have hdisj := disjoint_AB sel hindep
  -- pick the free edge days that will also run `c⁺`
  set Free : Finset G.Edge := Finset.univ \ (AEdges sel ∪ BEdges sel) with hFree
  have hcardFree : Free.card = Fintype.card G.Edge
      - ((AEdges sel).card + (BEdges sel).card) := by
    rw [hFree, ← Finset.compl_eq_univ_sdiff, Finset.card_compl,
      Finset.card_union_of_disjoint hdisj]
  obtain ⟨S, hSsub, hScard⟩ : ∃ S ⊆ Free, S.card = half - (BEdges sel).card :=
    Finset.exists_subset_card_eq (by omega)
  have hSB : Disjoint (BEdges sel) S := by
    refine Finset.disjoint_left.2 fun e hB hS => ?_
    have := hSsub hS
    rw [hFree, Finset.mem_sdiff] at this
    exact this.2 (Finset.mem_union_right _ hB)
  have hBS : (BEdges sel ∪ S).card = half := by
    rw [Finset.card_union_of_disjoint hSB, hScard]
    omega
  refine ⟨sched sel S, feasible_sched sel S hindep hSsub, ?_⟩
  rintro (v | (i | (x | (b | u))))
  · -- vertex clients
    show 1 ≤ _
    by_cases hs : SelV sel v
    · refine one_le_served_of_mem (i := G.dW v.1) ?_
      rw [mem_sched_dW]
      refine Or.inr (Or.inl ?_)
      have : v = (v.1, sel v.1) := Prod.ext rfl hs
      rw [← this]
    · exact one_le_served_of_mem (i := G.dV v) ((mem_sched_dV sel S v _).2
        (Or.inr (Or.inr ⟨hs, rfl⟩)))
  · -- selection clients
    show 1 ≤ _
    refine one_le_served_of_mem (i := G.dV (i, sel i)) ?_
    exact (mem_sched_dV sel S (i, sel i) _).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · -- edge clients
    show 1 ≤ _
    by_cases hs : Sel sel x
    · refine one_le_served_of_mem (i := G.dE (G.edgeOf x)) ?_
      rw [mem_sched_dE]
      rcases G.mem_edgeOf (x := x) rfl with hx | hx
      · exact Or.inr (Or.inr (Or.inl ⟨hx ▸ hs, congrArg G.ce hx⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hx ▸ hs, congrArg G.ce hx⟩))
    · refine one_le_served_of_mem (i := G.dW x.1.1) ?_
      rw [mem_sched_dW]
      exact Or.inr (Or.inr ⟨x, rfl, hs, rfl⟩)
  · -- interaction clients
    show half ≤ _
    rw [served_ci]
    cases b
    · have hfil : (Finset.univ.filter fun e : G.Edge =>
          decide (e ∈ BEdges sel ∪ S) = false) = Finset.univ \ (BEdges sel ∪ S) := by
        ext e; simp
      rw [hfil, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, hBS]
      omega
    · have hfil : (Finset.univ.filter fun e : G.Edge =>
          decide (e ∈ BEdges sel ∪ S) = true) = BEdges sel ∪ S := by
        ext e; simp
      rw [hfil, hBS]
  · -- the dummy
    show Fintype.card G.Day ≤ _
    have hall : ∀ d, G.c0 ∈ sched sel S d := by
      rintro (v | (i | e))
      · exact (mem_sched_dV sel S v _).2 (Or.inl rfl)
      · exact (mem_sched_dW sel S i _).2 (Or.inl rfl)
      · exact (mem_sched_dE sel S e _).2 (Or.inl rfl)
    exact le_of_eq (served_eq_numDays_of_mem hall).symm

end Forward

/-! ## 8. Lemma 14's correctness -/

/-- **Lemma 14's correctness.** The constructed instance admits a feasible schedule meeting
every client's own fairness parameter exactly when `G` has a multicolored independent set.

Both directions are proved. What is *not* established here is Lemma 14's other clause — that
the overall conflict graph has treewidth at most `4` — which, as the module doc explains, is
false for the construction as the paper specifies it. -/
theorem hasFairSchedule_iff_hasIndepSet {half : ℕ}
    (hhalf : 2 * half = Fintype.card G.Edge) (hbal : G.ℓ * G.r ≤ half) :
    (G.inst).HasFairSchedule (G.kvec half) ↔ G.HasIndepSet := by
  constructor
  · rintro ⟨σ, hfeas, hfair⟩
    exact hasIndepSet_of_fair hhalf hfeas hfair
  · exact hasFairSchedule_of_hasIndepSet hhalf hbal

end MIS

end Lemma14

end Lax117284Proofs.Model
