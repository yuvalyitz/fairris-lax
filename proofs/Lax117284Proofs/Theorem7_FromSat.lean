import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Lax117284Proofs.Defs
import Lax117284Proofs.TwoSat

/-!
# Theorem 7: NP-hardness for `k = 1`, `m = 3`, identical processing times

> **Theorem 7.** The `1 | rep, p_{i,j} = p | min_j ∑_i Z_{i,j}` problem is NP-hard for `k = 1`
> and `m = 3`.
>
> *Proof.* We present a polynomial-time many-one reduction from [2,3]-BOUNDED 3-SAT [29] to
> `1 | rep, p_{i,j} = p | min_j ∑_i Z_{i,j}` with `k = 1` and `m = 3`. […] Let
> `φ = ⋀_{j=1}^{ℓ} A_j ∧ ⋀_{j=1}^{m} B_j` be a [2,3]-BOUNDED 3-SAT formula over variables
> `{x_1,…,x_n}`, where `A_1,…,A_ℓ` are clauses with two literals and `B_1,…,B_m` are clauses
> with three literals. […] We can assume without loss of generality that each variable `x_i`
> appears at least once in some clause, and at most twice positive or twice negative overall.

This is the base case of Theorem 1's hardness half; `Corollary8_Induction.lean` lifts it to
every `0 < k < m − 1`, `m ≥ 3`.

## The construction

Every processing time is `2`, so a job is determined by its due date and **two jobs of a
day conflict exactly when their due dates differ by at most one** (`conflict_iff_close`).
The whole construction is therefore a matter of placing numbers on a line, three times.

* **Day 1 is the selection gadget.** Due dates `2` (the three dummies), `2i + 5` (both
  clients of variable `i`), `2n + 2j + 7` (both clients of the two-literal clause `j`), and
  `2n + 2ℓ + 2j + 9` (all three clients of the three-literal clause `j`). Clients sharing a
  due date conflict and nothing else does, so day 1 admits **one client out of each group**:
  one dummy, one of `x_i^0 / x_i^1` — this is the truth assignment — one client of each
  clause.
* **Day 2 is a blocking gadget.** Every dummy, variable and two-literal-clause client has
  due date `2`, so they are *all* mutually conflicting; the three-literal clause `j`'s
  clients sit alone at `3j + 6`. Since some dummy runs every day, day 2 is a dead end for
  everything except one client of each three-literal clause.
* **Day 3 is the incidence gadget.** `x_i^1` sits at `10i − 4` and `x_i^0` at `10i + 1`; the
  (at most two) occurrences of the literal `x_i` sit at `10i − 5` and `10i − 3`, and the (at
  most two) occurrences of `¬x_i` at `10i` and `10i + 2`. So on day 3 a literal client
  conflicts with exactly the variable client that *falsifies* it, and with nothing else.

The three dummies conflict with each other on all three days, so a `1`-fair schedule puts
exactly one on each day (`exists_dummy_each_day`) — that is what makes day 2 a dead end,
and what forces the selection on day 1.

## Tovey's degree bound, as an enumeration

*"at most twice positive or twice negative overall"* is carried by the `rank` field: every
occurrence gets a rank in `{0, 1}`, and `rank_inj` says an occurrence is determined by its
literal together with its rank. That is exactly "each literal occurs at most twice", in the
form the construction actually consumes — day 3 needs to know *which* of the two slots
`10i − 5` / `10i − 3` an occurrence takes, and a bare cardinality bound would have to be
turned into such a numbering anyway.

## Indices are 0-based

The paper's variables and clauses are numbered from `1`; `Fin` counts from `0`, so every
due date here is the paper's with `i` replaced by `i + 1`. Nothing else differs.
-/


namespace Lax117284Proofs.Model

namespace Theorem7

open Instance

/-! ## 1. [2,3]-bounded 3-SAT -/

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- A **[2,3]-bounded 3-SAT** formula: `nA` clauses of two literals and `nB` clauses of
three literals over `nv` variables, with each literal occurring at most twice
(`rank_inj`). -/
structure Bounded23 where
  /-- The number of variables. -/
  nv : ℕ
  /-- The number of two-literal clauses. -/
  nA : ℕ
  /-- The number of three-literal clauses. -/
  nB : ℕ
  /-- The literals of the two-literal clauses. -/
  aLit : Fin nA → Fin 2 → TwoSat.Lit (Fin nv)
  /-- The literals of the three-literal clauses. -/
  bLit : Fin nB → Fin 3 → TwoSat.Lit (Fin nv)
  /-- Which of its literal's (at most two) occurrences this one is. -/
  rank : (Fin nA × Fin 2) ⊕ (Fin nB × Fin 3) → Fin 2
  /-- Tovey's bound: an occurrence is determined by its literal together with its rank. -/
  rank_inj : ∀ o o' : (Fin nA × Fin 2) ⊕ (Fin nB × Fin 3),
    Sum.elim (fun q => aLit q.1 q.2) (fun q => bLit q.1 q.2) o
      = Sum.elim (fun q => aLit q.1 q.2) (fun q => bLit q.1 q.2) o' →
    rank o = rank o' → o = o'

namespace Bounded23

variable (φ : Bounded23)

/-- An **occurrence**: a literal position inside one of the clauses. -/
abbrev Occ : Type := (Fin φ.nA × Fin 2) ⊕ (Fin φ.nB × Fin 3)

/-- The literal an occurrence carries. -/
def lit (o : φ.Occ) : TwoSat.Lit (Fin φ.nv) :=
  Sum.elim (fun q => φ.aLit q.1 q.2) (fun q => φ.bLit q.1 q.2) o

variable {φ}

lemma occ_eq_of_lit_rank {o o' : φ.Occ} (hl : φ.lit o = φ.lit o')
    (hr : φ.rank o = φ.rank o') : o = o' := φ.rank_inj o o' hl hr

variable (φ)

/-- `val` satisfies `φ`: each clause, of either width, has a literal that holds. -/
def Satisfies (val : Fin φ.nv → Bool) : Prop :=
  (∀ j : Fin φ.nA, ∃ α, (φ.aLit j α).Holds val) ∧
  (∀ j : Fin φ.nB, ∃ α, (φ.bLit j α).Holds val)

/-- **The question of [2,3]-bounded 3-SAT.** -/
def Satisfiable : Prop := ∃ val : Fin φ.nv → Bool, φ.Satisfies val

/-! ## 2. The clients -/

/-- The clients: three dummies `h₁, h₂, h₃`, two clients `x_i^1 / x_i^0` per variable, and
one client per literal occurrence. -/
abbrev Client : Type := Fin 3 ⊕ ((Fin φ.nv × Bool) ⊕ φ.Occ)

/-- The dummy client `h_t`. -/
abbrev dum (t : Fin 3) : φ.Client := Sum.inl t

/-- The variable client `x_v^s`. -/
abbrev xcl (v : Fin φ.nv) (s : Bool) : φ.Client := Sum.inr (Sum.inl (v, s))

/-- The literal client of occurrence `o`. -/
abbrev ocl (o : φ.Occ) : φ.Client := Sum.inr (Sum.inr o)

/-! ## 3. The three days

Each day is given by its vector of due dates; the processing time is `2` throughout. -/

/-- Day 1's due dates: the selection gadget. Each group shares one due date and the groups
are at least two apart, so exactly one client of each group can run. -/
def d0 : φ.Client → ℕ
  | Sum.inl _ => 2
  | Sum.inr (Sum.inl (v, _)) => 2 * v.val + 5
  | Sum.inr (Sum.inr (Sum.inl (j, _))) => 2 * φ.nv + 2 * j.val + 7
  | Sum.inr (Sum.inr (Sum.inr (j, _))) => 2 * φ.nv + 2 * φ.nA + 2 * j.val + 9

/-- Day 1's group of a client: two clients conflict on day 1 exactly when their groups
agree (`conflict_day0_iff`). -/
def grp0 : φ.Client → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl (v, _)) => v.val + 1
  | Sum.inr (Sum.inr (Sum.inl (j, _))) => φ.nv + j.val + 1
  | Sum.inr (Sum.inr (Sum.inr (j, _))) => φ.nv + φ.nA + j.val + 1

/-- Day 2's due dates: the blocking gadget. Everything but the three-literal clause clients
sits at `2`. -/
def d1 : φ.Client → ℕ
  | Sum.inl _ => 2
  | Sum.inr (Sum.inl _) => 2
  | Sum.inr (Sum.inr (Sum.inl _)) => 2
  | Sum.inr (Sum.inr (Sum.inr (j, _))) => 3 * j.val + 6

/-- Day 2's group of a client. -/
def grp1 : φ.Client → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl _)) => 0
  | Sum.inr (Sum.inr (Sum.inr (j, _))) => j.val + 1

/-- Day 3's due dates: the incidence gadget. A literal client sits next to exactly the
variable client that falsifies it. -/
def d2 : φ.Client → ℕ
  | Sum.inl _ => 2
  | Sum.inr (Sum.inl (v, s)) => if s then 10 * v.val + 6 else 10 * v.val + 11
  | Sum.inr (Sum.inr o) =>
      if (φ.lit o).pos then 10 * (φ.lit o).var.val + 5 + 2 * (φ.rank o).val
      else 10 * (φ.lit o).var.val + 10 + 2 * (φ.rank o).val

/-- The due date of client `c` on day `i`. -/
def dueDate (i : Fin 3) (c : φ.Client) : ℕ :=
  if i.val = 0 then φ.d0 c else if i.val = 1 then φ.d1 c else φ.d2 c

@[simp] lemma dueDate_zero : φ.dueDate 0 = φ.d0 := rfl
@[simp] lemma dueDate_one : φ.dueDate 1 = φ.d1 := rfl
@[simp] lemma dueDate_two : φ.dueDate 2 = φ.d2 := rfl

lemma two_le_d0 (c : φ.Client) : 2 ≤ φ.d0 c := by
  rcases c with _ | (⟨v, s⟩ | (⟨j, α⟩ | ⟨j, α⟩)) <;> simp [d0]

lemma two_le_d1 (c : φ.Client) : 2 ≤ φ.d1 c := by
  rcases c with _ | (⟨v, s⟩ | (⟨j, α⟩ | ⟨j, α⟩)) <;> simp [d1]

lemma two_le_d2 (c : φ.Client) : 2 ≤ φ.d2 c := by
  rcases c with _ | (⟨v, s⟩ | o) <;> simp only [d2]
  · omega
  · cases s <;> simp
  · split <;> omega

lemma two_le_dueDate (i : Fin 3) (c : φ.Client) : 2 ≤ φ.dueDate i c := by
  simp only [dueDate]
  split
  · exact two_le_d0 φ c
  · split
    · exact two_le_d1 φ c
    · exact two_le_d2 φ c

/-! ## 4. The instance -/

/-- **The instance built from `φ`**: three days, all processing times `2`, `k = 1`.

`@[reducible]` so that `(inst φ).Day` and `(inst φ).Client` unfold during unification and
instance search — without it the numeral `(0 : (inst φ).Day)` has no `OfNat` instance. -/
@[reducible] def inst : Instance where
  Client := φ.Client
  Day := Fin 3
  clientFintype := inferInstance
  clientDecEq := inferInstance
  dayFintype := inferInstance
  dayDecEq := inferInstance
  p _ _ := 2
  d := φ.dueDate
  p_pos _ _ := by omega
  p_le_d := two_le_dueDate φ

/-- **Two jobs of a day conflict exactly when their due dates differ by at most one** —
the only consequence of `p ≡ 2` the construction uses. -/
theorem conflict_iff_close (i : Fin 3) (c c' : φ.Client) :
    (inst φ).Conflict i c c' ↔
      (φ.dueDate i c ≤ φ.dueDate i c' + 1 ∧ φ.dueDate i c' ≤ φ.dueDate i c + 1) := by
  have h1 := two_le_dueDate φ i c
  have h2 := two_le_dueDate φ i c'
  simp only [Conflict, Instance.start]
  omega


/-! ## 5. What conflicts with what

Days 1 and 2 are *partitions*: clients conflict exactly when they share a group. Day 3 is
not — it is the incidence structure of the formula — so it gets one lemma per pair of
kinds. -/

lemma d0_eq_of_grp0_eq {c c' : φ.Client} (h : φ.grp0 c = φ.grp0 c') : φ.d0 c = φ.d0 c' := by
  rcases c with t | (⟨⟨v, hv⟩, s⟩ | (⟨⟨j, hj⟩, α⟩ | ⟨⟨j, hj⟩, α⟩)) <;>
    rcases c' with t' | (⟨⟨v', hv'⟩, s'⟩ | (⟨⟨j', hj'⟩, α'⟩ | ⟨⟨j', hj'⟩, α'⟩)) <;>
      simp only [grp0, d0] at h ⊢ <;> omega

lemma d0_gap_of_grp0_lt {c c' : φ.Client} (h : φ.grp0 c < φ.grp0 c') :
    φ.d0 c + 2 ≤ φ.d0 c' := by
  rcases c with t | (⟨⟨v, hv⟩, s⟩ | (⟨⟨j, hj⟩, α⟩ | ⟨⟨j, hj⟩, α⟩)) <;>
    rcases c' with t' | (⟨⟨v', hv'⟩, s'⟩ | (⟨⟨j', hj'⟩, α'⟩ | ⟨⟨j', hj'⟩, α'⟩)) <;>
      simp only [grp0, d0] at h ⊢ <;> omega

lemma d1_eq_of_grp1_eq {c c' : φ.Client} (h : φ.grp1 c = φ.grp1 c') : φ.d1 c = φ.d1 c' := by
  rcases c with t | (⟨⟨v, hv⟩, s⟩ | (⟨⟨j, hj⟩, α⟩ | ⟨⟨j, hj⟩, α⟩)) <;>
    rcases c' with t' | (⟨⟨v', hv'⟩, s'⟩ | (⟨⟨j', hj'⟩, α'⟩ | ⟨⟨j', hj'⟩, α'⟩)) <;>
      simp only [grp1, d1] at h ⊢ <;> omega

lemma d1_gap_of_grp1_lt {c c' : φ.Client} (h : φ.grp1 c < φ.grp1 c') :
    φ.d1 c + 2 ≤ φ.d1 c' := by
  rcases c with t | (⟨⟨v, hv⟩, s⟩ | (⟨⟨j, hj⟩, α⟩ | ⟨⟨j, hj⟩, α⟩)) <;>
    rcases c' with t' | (⟨⟨v', hv'⟩, s'⟩ | (⟨⟨j', hj'⟩, α'⟩ | ⟨⟨j', hj'⟩, α'⟩)) <;>
      simp only [grp1, d1] at h ⊢ <;> omega

/-- **Day 1 is a partition.** Two clients conflict on day 1 exactly when they lie in the
same group: the dummies, the two clients of a variable, or the clients of one clause. -/
theorem conflict_day0_iff (c c' : φ.Client) :
    (inst φ).Conflict 0 c c' ↔ φ.grp0 c = φ.grp0 c' := by
  rw [conflict_iff_close, dueDate_zero]
  constructor
  · intro h
    by_contra hne
    rcases Nat.lt_or_ge (φ.grp0 c) (φ.grp0 c') with hlt | hge
    · have := d0_gap_of_grp0_lt φ hlt; omega
    · have := d0_gap_of_grp0_lt φ (show φ.grp0 c' < φ.grp0 c by omega); omega
  · intro h
    have := d0_eq_of_grp0_eq φ h
    omega

/-- **Day 2 is a partition.** Everything except the three-literal clause clients is in one
big group; each three-literal clause is a group of its own. -/
theorem conflict_day1_iff (c c' : φ.Client) :
    (inst φ).Conflict 1 c c' ↔ φ.grp1 c = φ.grp1 c' := by
  rw [conflict_iff_close, dueDate_one]
  constructor
  · intro h
    by_contra hne
    rcases Nat.lt_or_ge (φ.grp1 c) (φ.grp1 c') with hlt | hge
    · have := d1_gap_of_grp1_lt φ hlt; omega
    · have := d1_gap_of_grp1_lt φ (show φ.grp1 c' < φ.grp1 c by omega); omega
  · intro h
    have := d1_eq_of_grp1_eq φ h
    omega

/-! ### Day 3 -/

@[simp] lemma d2_dum (t : Fin 3) : φ.d2 (dum φ t) = 2 := Eq.trans rfl rfl

@[simp] lemma d2_xcl (v : Fin φ.nv) (s : Bool) :
    φ.d2 (xcl φ v s) = if s then 10 * v.val + 6 else 10 * v.val + 11 := Eq.trans rfl rfl

@[simp] lemma d2_ocl (o : φ.Occ) :
    φ.d2 (ocl φ o) = if (φ.lit o).pos then 10 * (φ.lit o).var.val + 5 + 2 * (φ.rank o).val
      else 10 * (φ.lit o).var.val + 10 + 2 * (φ.rank o).val := Eq.trans rfl rfl

private lemma occ_gap {V V' R R' : ℕ} {P P' : Bool} (hR : R < 2) (hR' : R' < 2)
    (hne : ¬ (V = V' ∧ P = P' ∧ R = R')) :
    ¬ ((if P then 10 * V + 5 + 2 * R else 10 * V + 10 + 2 * R)
          ≤ (if P' then 10 * V' + 5 + 2 * R' else 10 * V' + 10 + 2 * R') + 1
        ∧ (if P' then 10 * V' + 5 + 2 * R' else 10 * V' + 10 + 2 * R')
          ≤ (if P then 10 * V + 5 + 2 * R else 10 * V + 10 + 2 * R) + 1) := by
  cases P <;> cases P' <;> simp only [if_true, if_false, Bool.false_eq_true,
    true_and, and_false, false_and, not_and,
    not_false_eq_true] at hne ⊢ <;> omega

private lemma xcl_occ_gap {v V R : ℕ} {s P : Bool} (hR : R < 2) (hne : ¬ (V = v ∧ P = s)) :
    ¬ ((if s then 10 * v + 6 else 10 * v + 11)
          ≤ (if P then 10 * V + 5 + 2 * R else 10 * V + 10 + 2 * R) + 1
        ∧ (if P then 10 * V + 5 + 2 * R else 10 * V + 10 + 2 * R)
          ≤ (if s then 10 * v + 6 else 10 * v + 11) + 1) := by
  cases s <;> cases P <;> simp only [if_true, if_false, Bool.false_eq_true,
    and_true, and_false, not_and, not_false_eq_true] at hne ⊢ <;> omega

private lemma xcl_gap {v w : ℕ} {s s' : Bool} (hne : ¬ (v = w ∧ s = s')) :
    ¬ ((if s then 10 * v + 6 else 10 * v + 11) ≤ (if s' then 10 * w + 6 else 10 * w + 11) + 1
        ∧ (if s' then 10 * w + 6 else 10 * w + 11)
          ≤ (if s then 10 * v + 6 else 10 * v + 11) + 1) := by
  cases s <;> cases s' <;> simp only [if_true, if_false, Bool.false_eq_true,
    and_true, and_false, not_and, not_false_eq_true] at hne ⊢ <;> omega

/-- The dummies conflict with each other on day 3, as on the other two. -/
theorem conflict_day2_dum (t t' : Fin 3) : (inst φ).Conflict 2 (dum φ t) (dum φ t') := by
  rw [conflict_iff_close, dueDate_two]; simp

theorem not_conflict_day2_dum_xcl (t : Fin 3) (v : Fin φ.nv) (s : Bool) :
    ¬ (inst φ).Conflict 2 (dum φ t) (xcl φ v s) := by
  rw [conflict_iff_close, dueDate_two]
  simp only [d2_dum, d2_xcl]
  cases s <;> simp

theorem not_conflict_day2_dum_ocl (t : Fin 3) (o : φ.Occ) :
    ¬ (inst φ).Conflict 2 (dum φ t) (ocl φ o) := by
  rw [conflict_iff_close, dueDate_two]
  simp only [d2_dum, d2_ocl]
  cases (φ.lit o).pos <;> simp <;> omega

/-- **The incidence edge**: a literal client conflicts, on day 3, with exactly the variable
client that falsifies its literal. -/
theorem conflict_day2_xcl_ocl (o : φ.Occ) :
    (inst φ).Conflict 2 (xcl φ (φ.lit o).var (φ.lit o).pos) (ocl φ o) := by
  rw [conflict_iff_close, dueDate_two]
  have hr : (φ.rank o).val < 2 := (φ.rank o).isLt
  simp only [d2_xcl, d2_ocl]
  cases (φ.lit o).pos <;> simp only [if_true, if_false, Bool.false_eq_true] <;> omega

theorem not_conflict_day2_xcl_ocl {v : Fin φ.nv} {s : Bool} {o : φ.Occ}
    (h : ¬ ((φ.lit o).var = v ∧ (φ.lit o).pos = s)) :
    ¬ (inst φ).Conflict 2 (xcl φ v s) (ocl φ o) := by
  rw [conflict_iff_close, dueDate_two]
  simp only [d2_xcl, d2_ocl]
  refine xcl_occ_gap (φ.rank o).isLt ?_
  rintro ⟨hv, hp⟩
  exact h ⟨Fin.ext hv, hp⟩

theorem not_conflict_day2_xcl_xcl {v w : Fin φ.nv} {s s' : Bool} (h : ¬ (v = w ∧ s = s')) :
    ¬ (inst φ).Conflict 2 (xcl φ v s) (xcl φ w s') := by
  rw [conflict_iff_close, dueDate_two]
  simp only [d2_xcl]
  refine xcl_gap ?_
  rintro ⟨hv, hs⟩
  exact h ⟨Fin.ext hv, hs⟩

theorem not_conflict_day2_ocl_ocl {o o' : φ.Occ} (h : o ≠ o') :
    ¬ (inst φ).Conflict 2 (ocl φ o) (ocl φ o') := by
  rw [conflict_iff_close, dueDate_two]
  simp only [d2_ocl]
  refine occ_gap (φ.rank o).isLt (φ.rank o').isLt ?_
  rintro ⟨hv, hp, hr⟩
  refine h (occ_eq_of_lit_rank ?_ (Fin.ext hr))
  cases hl : φ.lit o
  cases hl' : φ.lit o'
  rw [hl, hl'] at hv hp
  simp only at hv hp
  subst hp
  rw [Fin.ext hv]


/-! ## 6. Reading a schedule as an assignment

The `⇐` direction. Two structural facts drive it: some dummy runs every day, and every
literal client that runs on day 3 has its literal satisfied by the assignment day 1
selects. -/

private lemma day_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide

variable {φ}

/-- The dummies conflict with one another on every day. -/
lemma conflict_dum (i : Fin 3) (t t' : Fin 3) :
    (inst φ).Conflict i (dum φ t) (dum φ t') := by
  rcases day_cases i with rfl | rfl | rfl
  · exact (conflict_day0_iff φ _ _).2 rfl
  · exact (conflict_day1_iff φ _ _).2 rfl
  · exact conflict_day2_dum φ t t'

/-- A client of a `1`-fair schedule runs on some day. -/
lemma exists_day {σ : (inst φ).Schedule} (hfair : Fair (fun _ => 1) σ) (c : φ.Client) :
    ∃ i, c ∈ σ i :=
  exists_mem_of_served_pos (lt_of_lt_of_le Nat.zero_lt_one (hfair c))

/-- **One dummy runs on every day.** Three dummies, pairwise conflicting on all three days,
each needing a day: the assignment of dummies to days is a bijection. -/
theorem exists_dummy_each_day {σ : (inst φ).Schedule} (hfeas : Feasible σ)
    (hfair : Fair (fun _ => 1) σ) (i : Fin 3) : ∃ t, dum φ t ∈ σ i := by
  choose g hg using fun t : Fin 3 => exists_day hfair (dum φ t)
  have hginj : Function.Injective g := by
    intro t t' hEq
    by_contra hne
    exact hfeas (g t) _ (hg t) _ (hEq ▸ hg t')
      (fun hh => hne (Sum.inl_injective hh)) (conflict_dum (g t) t t')
  obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.1 hginj) i
  exact ⟨t, ht ▸ hg t⟩

/-- Nothing that shares day 2's big group with the dummies can run on day 2. -/
lemma not_mem_day1_of_grp1_zero {σ : (inst φ).Schedule} (hfeas : Feasible σ)
    (hfair : Fair (fun _ => 1) σ) {c : φ.Client} (hg : φ.grp1 c = 0)
    (hdum : ∀ t : Fin 3, c ≠ dum φ t) : c ∉ σ 1 := by
  intro hmem
  obtain ⟨t, ht⟩ := exists_dummy_each_day hfeas hfair 1
  exact hfeas 1 _ ht _ hmem (fun hh => hdum t hh.symm)
    ((conflict_day1_iff φ _ _).2 (by rw [hg]; rfl))

/-- The assignment day 1's selection gadget encodes. -/
def valOf (σ : (inst φ).Schedule) (v : Fin φ.nv) : Bool := decide (xcl φ v true ∈ σ 0)

/-- **Every literal client that runs on day 3 has its literal satisfied.** This is the
heart of the `⇐` direction: running on day 3 forces the variable client that falsifies the
literal off days 2 and 3, hence onto day 1, which is exactly what `valOf` reads. -/
theorem lit_holds_of_mem_day2 {σ : (inst φ).Schedule} (hfeas : Feasible σ)
    (hfair : Fair (fun _ => 1) σ) {o : φ.Occ} (ho : ocl φ o ∈ σ 2) :
    (φ.lit o).Holds (valOf σ) := by
  have h2 : xcl φ (φ.lit o).var (φ.lit o).pos ∉ σ 2 := fun hmem =>
    hfeas 2 _ hmem _ ho (by simp) (conflict_day2_xcl_ocl φ o)
  have h1 : xcl φ (φ.lit o).var (φ.lit o).pos ∉ σ 1 :=
    not_mem_day1_of_grp1_zero hfeas hfair rfl (by simp)
  have h0 : xcl φ (φ.lit o).var (φ.lit o).pos ∈ σ 0 := by
    obtain ⟨i, hi⟩ := exists_day hfair (xcl φ (φ.lit o).var (φ.lit o).pos)
    rcases day_cases i with rfl | rfl | rfl
    · exact hi
    · exact absurd hi h1
    · exact absurd hi h2
  show valOf σ (φ.lit o).var = (φ.lit o).pos
  cases hs : (φ.lit o).pos
  · rw [hs] at h0
    have hnt : xcl φ (φ.lit o).var true ∉ σ 0 := fun hmem =>
      hfeas 0 _ hmem _ h0 (by simp) ((conflict_day0_iff φ _ _).2 rfl)
    simp [valOf, hnt]
  · rw [hs] at h0
    simp [valOf, h0]

/-- Each two-literal clause has an occurrence on day 3: neither can use day 2, and day 1
holds at most one of them. -/
theorem exists_mem_day2_two {σ : (inst φ).Schedule} (hfeas : Feasible σ)
    (hfair : Fair (fun _ => 1) σ) (j : Fin φ.nA) :
    ∃ α, ocl φ (Sum.inl (j, α)) ∈ σ 2 := by
  by_contra hcon
  push Not at hcon
  have hday : ∀ α : Fin 2, ocl φ (Sum.inl (j, α)) ∈ σ 0 := by
    intro α
    obtain ⟨i, hi⟩ := exists_day hfair (ocl φ (Sum.inl (j, α)))
    rcases day_cases i with rfl | rfl | rfl
    · exact hi
    · exact absurd hi (not_mem_day1_of_grp1_zero hfeas hfair rfl (by simp))
    · exact absurd hi (hcon α)
  have hne2 : (0 : Fin 2) ≠ 1 := by decide
  refine hfeas 0 _ (hday 0) _ (hday 1) ?_ ((conflict_day0_iff φ _ _).2 rfl)
  exact fun hh => hne2 (congrArg Prod.snd (Sum.inl_injective
    (Sum.inr_injective (Sum.inr_injective hh))))

/-- Each three-literal clause has an occurrence on day 3: its three clients conflict on
both day 1 and day 2, so those two days hold at most two of them. -/
theorem exists_mem_day2_three {σ : (inst φ).Schedule} (hfeas : Feasible σ)
    (hfair : Fair (fun _ => 1) σ) (j : Fin φ.nB) :
    ∃ α, ocl φ (Sum.inr (j, α)) ∈ σ 2 := by
  classical
  by_contra hcon
  push Not at hcon
  have hday : ∀ α : Fin 3,
      ocl φ (Sum.inr (j, α)) ∈ σ 0 ∨ ocl φ (Sum.inr (j, α)) ∈ σ 1 := by
    intro α
    obtain ⟨i, hi⟩ := exists_day hfair (ocl φ (Sum.inr (j, α)))
    rcases day_cases i with rfl | rfl | rfl
    · exact Or.inl hi
    · exact Or.inr hi
    · exact absurd hi (hcon α)
  set f : Fin 3 → Fin 2 := fun α => if ocl φ (Sum.inr (j, α)) ∈ σ 0 then 0 else 1 with hf
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    have := Fintype.card_le_of_injective f hinj
    simp at this
  obtain ⟨α, α', hEq, hne⟩ := Function.not_injective_iff.1 hnotinj
  have hocc : ocl φ (Sum.inr (j, α)) ≠ ocl φ (Sum.inr (j, α')) := by
    intro hh
    exact hne (congrArg Prod.snd (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective hh))))
  by_cases h0 : ocl φ (Sum.inr (j, α)) ∈ σ 0
  · have h0' : ocl φ (Sum.inr (j, α')) ∈ σ 0 := by
      by_contra hcc
      rw [hf] at hEq
      simp only [if_pos h0, if_neg hcc] at hEq
      exact absurd hEq (by decide)
    exact hfeas 0 _ h0 _ h0' hocc ((conflict_day0_iff φ _ _).2 rfl)
  · have h1 : ocl φ (Sum.inr (j, α)) ∈ σ 1 := (hday α).resolve_left h0
    have h1' : ocl φ (Sum.inr (j, α')) ∈ σ 1 := by
      rcases hday α' with hh | hh
      · rw [hf] at hEq
        simp only [if_neg h0, if_pos hh] at hEq
        exact absurd hEq (by decide)
      · exact hh
    exact hfeas 1 _ h1 _ h1' hocc ((conflict_day1_iff φ _ _).2 rfl)

/-- **The `⇐` direction of Theorem 7.** -/
theorem satisfies_valOf {σ : (inst φ).Schedule} (hfeas : Feasible σ)
    (hfair : Fair (fun _ => 1) σ) : φ.Satisfies (valOf σ) := by
  constructor
  · intro j
    obtain ⟨α, hα⟩ := exists_mem_day2_two hfeas hfair j
    exact ⟨α, lit_holds_of_mem_day2 hfeas hfair hα⟩
  · intro j
    obtain ⟨α, hα⟩ := exists_mem_day2_three hfeas hfair j
    exact ⟨α, lit_holds_of_mem_day2 hfeas hfair hα⟩


/-! ## 7. Building a schedule from an assignment

The `⇒` direction. Every client runs on exactly one day, so the schedule is given by a
function `dayOf : Client → ℕ`: the dummy `h_t` takes day `t`; the variable client agreeing
with the assignment takes day 1 and the other takes day 3; of a clause's clients the chosen
true one takes day 3 and the rest fill days 1 and 2. -/

/-- The first index of a three-literal clause other than `t`. -/
def first3 (t : Fin 3) : Fin 3 := if t = 0 then 1 else 0

lemma fin2_ne_ne {a a' b : Fin 2} (h : a ≠ b) (h' : a' ≠ b) : a = a' := by
  revert a a' b; decide

lemma fin3_third {a a' t : Fin 3} (h1 : a ≠ t) (h2 : a ≠ first3 t) (h1' : a' ≠ t)
    (h2' : a' ≠ first3 t) : a = a' := by
  revert a a' t; decide

variable (φ)

/-- The day each client runs on. -/
def dayOf (val : Fin φ.nv → Bool) (ta : Fin φ.nA → Fin 2) (tb : Fin φ.nB → Fin 3) :
    φ.Client → ℕ
  | Sum.inl t => t.val
  | Sum.inr (Sum.inl (v, s)) => if s = val v then 0 else 2
  | Sum.inr (Sum.inr (Sum.inl (j, α))) => if α = ta j then 2 else 0
  | Sum.inr (Sum.inr (Sum.inr (j, α))) =>
      if α = tb j then 2 else if α = first3 (tb j) then 0 else 1

variable {φ}

lemma dayOf_lt (val : Fin φ.nv → Bool) (ta : Fin φ.nA → Fin 2) (tb : Fin φ.nB → Fin 3)
    (c : φ.Client) : dayOf φ val ta tb c < 3 := by
  rcases c with t | (⟨v, s⟩ | (⟨j, α⟩ | ⟨j, α⟩)) <;> simp only [dayOf]
  · exact t.isLt
  · split <;> omega
  · split <;> omega
  · split <;> [omega; (split <;> omega)]

variable (φ)

/-- The schedule the `⇒` direction builds. -/
def sched (val : Fin φ.nv → Bool) (ta : Fin φ.nA → Fin 2) (tb : Fin φ.nB → Fin 3) :
    (inst φ).Schedule := fun i => Finset.univ.filter fun c => dayOf φ val ta tb c = i.val

variable {φ}

@[simp] lemma mem_sched {val ta tb} {i : Fin 3} {c : φ.Client} :
    c ∈ sched φ val ta tb i ↔ dayOf φ val ta tb c = i.val := by
  simp [sched]

/-- Every client runs on exactly one day, so the schedule is `1`-fair. -/
lemma served_sched (val : Fin φ.nv → Bool) (ta : Fin φ.nA → Fin 2) (tb : Fin φ.nB → Fin 3)
    (c : φ.Client) : served (sched φ val ta tb) c = 1 := by
  have hlt : dayOf φ val ta tb c < 3 := dayOf_lt val ta tb c
  refine served_eq_one_of_unique (i₀ := (⟨dayOf φ val ta tb c, hlt⟩ : Fin 3)) fun i => ?_
  rw [mem_sched]
  exact ⟨fun hh => Fin.ext hh.symm, fun hh => by rw [hh]⟩

/-! ### The schedule is feasible -/

lemma eq_of_day0 {val : Fin φ.nv → Bool} {ta : Fin φ.nA → Fin 2} {tb : Fin φ.nB → Fin 3}
    {c c' : φ.Client} (h : φ.grp0 c = φ.grp0 c')
    (hc : dayOf φ val ta tb c = 0) (hc' : dayOf φ val ta tb c' = 0) : c = c' := by
  rcases c with t | (⟨⟨v, hv⟩, s⟩ | (⟨⟨j, hj⟩, α⟩ | ⟨⟨j, hj⟩, α⟩)) <;>
    rcases c' with t' | (⟨⟨v', hv'⟩, s'⟩ | (⟨⟨j', hj'⟩, α'⟩ | ⟨⟨j', hj'⟩, α'⟩)) <;>
      simp only [grp0] at h <;> simp only [dayOf] at hc hc'
  all_goals try (exfalso; omega)
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · obtain rfl : v = v' := by omega
    have hs : s = val ⟨v, hv⟩ := by by_contra hcon; rw [if_neg hcon] at hc; omega
    have hs' : s' = val ⟨v, hv'⟩ := by by_contra hcon; rw [if_neg hcon] at hc'; omega
    rw [hs, hs']
  · obtain rfl : j = j' := by omega
    have ha : α ≠ ta ⟨j, hj⟩ := by intro hcon; rw [if_pos hcon] at hc; omega
    have ha' : α' ≠ ta ⟨j, hj'⟩ := by intro hcon; rw [if_pos hcon] at hc'; omega
    rw [fin2_ne_ne ha ha']
  · obtain rfl : j = j' := by omega
    have ha : α = first3 (tb ⟨j, hj⟩) := by
      by_cases h1 : α = tb ⟨j, hj⟩
      · rw [if_pos h1] at hc; omega
      · rw [if_neg h1] at hc
        by_contra h2
        rw [if_neg h2] at hc; omega
    have ha' : α' = first3 (tb ⟨j, hj'⟩) := by
      by_cases h1 : α' = tb ⟨j, hj'⟩
      · rw [if_pos h1] at hc'; omega
      · rw [if_neg h1] at hc'
        by_contra h2
        rw [if_neg h2] at hc'; omega
    rw [ha, ha']

lemma eq_of_day1 {val : Fin φ.nv → Bool} {ta : Fin φ.nA → Fin 2} {tb : Fin φ.nB → Fin 3}
    {c c' : φ.Client} (h : φ.grp1 c = φ.grp1 c')
    (hc : dayOf φ val ta tb c = 1) (hc' : dayOf φ val ta tb c' = 1) : c = c' := by
  rcases c with t | (⟨⟨v, hv⟩, s⟩ | (⟨⟨j, hj⟩, α⟩ | ⟨⟨j, hj⟩, α⟩)) <;>
    rcases c' with t' | (⟨⟨v', hv'⟩, s'⟩ | (⟨⟨j', hj'⟩, α'⟩ | ⟨⟨j', hj'⟩, α'⟩)) <;>
      simp only [grp1] at h <;> simp only [dayOf] at hc hc'
  all_goals try (exfalso; first | omega | (split_ifs at hc hc' <;> omega))
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · obtain rfl : j = j' := by omega
    have ha : α ≠ tb ⟨j, hj⟩ ∧ α ≠ first3 (tb ⟨j, hj⟩) := by
      constructor
      · intro h1; rw [if_pos h1] at hc; omega
      · intro h2
        by_cases h1 : α = tb ⟨j, hj⟩
        · rw [if_pos h1] at hc; omega
        · rw [if_neg h1, if_pos h2] at hc; omega
    have ha' : α' ≠ tb ⟨j, hj'⟩ ∧ α' ≠ first3 (tb ⟨j, hj'⟩) := by
      constructor
      · intro h1; rw [if_pos h1] at hc'; omega
      · intro h2
        by_cases h1 : α' = tb ⟨j, hj'⟩
        · rw [if_pos h1] at hc'; omega
        · rw [if_neg h1, if_pos h2] at hc'; omega
    rw [fin3_third ha.1 ha.2 ha'.1 ha'.2]

lemma holds_of_day2 {val : Fin φ.nv → Bool} {ta : Fin φ.nA → Fin 2} {tb : Fin φ.nB → Fin 3}
    (hta : ∀ j, (φ.aLit j (ta j)).Holds val) (htb : ∀ j, (φ.bLit j (tb j)).Holds val)
    {o : φ.Occ} (h : dayOf φ val ta tb (ocl φ o) = 2) : (φ.lit o).Holds val := by
  rcases o with ⟨j, α⟩ | ⟨j, α⟩ <;> simp only [dayOf] at h
  · by_cases hα : α = ta j
    · subst hα; exact hta j
    · rw [if_neg hα] at h; omega
  · by_cases hα : α = tb j
    · subst hα; exact htb j
    · rw [if_neg hα] at h; split at h <;> omega

lemma ne_val_of_day2 {val : Fin φ.nv → Bool} {ta : Fin φ.nA → Fin 2} {tb : Fin φ.nB → Fin 3}
    {v : Fin φ.nv} {s : Bool} (h : dayOf φ val ta tb (xcl φ v s) = 2) : s ≠ val v := by
  intro hs
  simp only [dayOf, if_pos hs] at h
  omega

lemma not_conflict_day2 {val : Fin φ.nv → Bool} {ta : Fin φ.nA → Fin 2}
    {tb : Fin φ.nB → Fin 3} (hta : ∀ j, (φ.aLit j (ta j)).Holds val)
    (htb : ∀ j, (φ.bLit j (tb j)).Holds val) {c c' : φ.Client} (hne : c ≠ c')
    (hc : dayOf φ val ta tb c = 2) (hc' : dayOf φ val ta tb c' = 2) :
    ¬ (inst φ).Conflict 2 c c' := by
  rcases c with t | (⟨v, s⟩ | o) <;> rcases c' with t' | (⟨v', s'⟩ | o')
  · exact absurd (congrArg Sum.inl (Fin.ext (by simp only [dayOf] at hc hc'; omega))) hne
  · exact not_conflict_day2_dum_xcl φ t v' s'
  · exact not_conflict_day2_dum_ocl φ t o'
  · exact fun hcf => not_conflict_day2_dum_xcl φ t' v s (conflict_symm hcf)
  · refine not_conflict_day2_xcl_xcl φ ?_
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  · refine not_conflict_day2_xcl_ocl φ ?_
    rintro ⟨hv, hp⟩
    have h1 := holds_of_day2 hta htb hc'
    have h2 := ne_val_of_day2 hc
    rw [TwoSat.Lit.Holds, hv, hp] at h1
    exact h2 h1.symm
  · exact fun hcf => not_conflict_day2_dum_ocl φ t' o (conflict_symm hcf)
  · refine fun hcf => not_conflict_day2_xcl_ocl φ ?_ (conflict_symm hcf)
    rintro ⟨hv, hp⟩
    have h1 := holds_of_day2 hta htb hc
    have h2 := ne_val_of_day2 hc'
    rw [TwoSat.Lit.Holds, hv, hp] at h1
    exact h2 h1.symm
  · exact not_conflict_day2_ocl_ocl φ (fun hh => hne (by rw [hh]))

theorem feasible_sched {val : Fin φ.nv → Bool} {ta : Fin φ.nA → Fin 2}
    {tb : Fin φ.nB → Fin 3} (hta : ∀ j, (φ.aLit j (ta j)).Holds val)
    (htb : ∀ j, (φ.bLit j (tb j)).Holds val) : Feasible (sched φ val ta tb) := by
  intro i c hc c' hc' hne
  rw [mem_sched] at hc hc'
  rcases day_cases i with rfl | rfl | rfl
  · have hc0 : dayOf φ val ta tb c = 0 := hc
    have hc0' : dayOf φ val ta tb c' = 0 := hc'
    rw [conflict_day0_iff]
    exact fun hgrp => hne (eq_of_day0 hgrp hc0 hc0')
  · have hc1 : dayOf φ val ta tb c = 1 := hc
    have hc1' : dayOf φ val ta tb c' = 1 := hc'
    rw [conflict_day1_iff]
    exact fun hgrp => hne (eq_of_day1 hgrp hc1 hc1')
  · exact not_conflict_day2 hta htb hne hc hc'

/-! ## 8. Theorem 7 -/

/-- **Theorem 7's correctness.** The constructed three-day instance admits a feasible
`1`-fair schedule exactly when the formula is satisfiable. -/
theorem satisfiable_iff_hasOneFairSchedule :
    φ.Satisfiable ↔ (inst φ).HasKFairSchedule 1 := by
  constructor
  · rintro ⟨val, hA, hB⟩
    choose ta hta using hA
    choose tb htb using hB
    exact ⟨sched φ val ta tb, feasible_sched hta htb,
      fun c => le_of_eq (served_sched val ta tb c).symm⟩
  · rintro ⟨σ, hfeas, hfair⟩
    exact ⟨valOf σ, satisfies_valOf hfeas hfair⟩

end Bounded23

end Theorem7

end Lax117284Proofs.Model
