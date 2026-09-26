import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Sort
import Lax117284Proofs.Defs

/-!
# Theorem 12: day-independent due dates, `m` constant

> **Theorem 12.** The `1 | rep, d_{i,j} = d_j | min_j ∑_i Z_{i,j}` problem is solvable in
> `O(m^{k+1} n^{m+1})` time.
>
> *Proof.* Given an instance […] we order the set of clients `{1,…,n}` in `O(n log n)` time
> in non-decreasing order of their due dates. […] We represent a schedule `σ ∈ Σ_{j*}` with
> the state `[j*, j₁, …, j_m]` in which `j_i` represents the index of the last scheduled
> client on day `i`. […] For every schedule `[j* − 1, j₁, …, j_m] ∈ Σ_{j*−1}` we check
> whether `p_{i,j*} ≤ d_{j*} − d_{j_i}` for every `i ∈ S`, i.e., if the jobs of client `j*`
> can be feasibly scheduled in the partial schedule.

## Why the last client is all the state you need

Day-independent due dates make the daily conflict relation *nested along the due-date
order*: process clients in non-decreasing `d_j`, and a newly added client `j` conflicts
with an earlier `j'` on day `i` exactly when `d_j − p_{i,j} < d_{j'}`. Since `d_{j'}`
increases along the order, clashing with *none* of the earlier clients is the same as
clashing with the *last* one — `notConflict_iff_le` and `notConflict_of_le_of_notConflict`
below. So a partial schedule need only be remembered through one number per day.

The state kept here is the last scheduled client's **due date** rather than its index, with
`0` standing for "nothing scheduled yet". That is the same information (`d` is what the
paper's check `p_{i,j*} ≤ d_{j*} − d_{j_i}` reads off the index) and it makes the empty
state `fun _ => 0` a genuine value of the state type rather than a special case.

`Dp` is the paper's table as a predicate, and `hasKFairSchedule_iff_dp` is its correctness.
The `O(m^{k+1} n^{m+1})` running time is a resource claim and lives in `FairRIS.lean`.
-/


namespace Lax117284Proofs.Model

namespace Instance

variable {I : Instance}

/-! ## 1. Conflict along the due-date order -/

/-- With a common due date function, "`j` does not conflict with the earlier `j'` on day
`i`" is the paper's arithmetic test `p_{i,j} ≤ d_j − d_{j'}`. -/
lemma notConflict_iff_le {i : I.Day} {j j' : I.Client} (hle : I.d i j' ≤ I.d i j) :
    ¬ I.Conflict i j j' ↔ I.p i j + I.d i j' ≤ I.d i j := by
  have h1 := I.p_le_d i j
  have h2 := I.p_le_d i j'
  have h3 := I.p_pos i j'
  simp only [Conflict, start, not_and, Nat.not_lt]
  omega

/-! ## 2. The dynamic program -/

/-- **The table of Theorem 12.** `Dp dd k l st` says: the clients of `l`, in the order
given, can each be served on exactly `k` days, given that day `i` currently ends with a job
of due date `st i`.

The recursion is the paper's: pick the `k` days `S` on which the next client `j` runs,
check `p_{i,j} + st i ≤ d_j` on each of them (the paper's `p_{i,j*} ≤ d_{j*} − d_{j_i}`),
and continue with `st` updated to `d_j` on the days of `S`. -/
def Dp (dd : I.Client → ℕ) (k : ℕ) : List I.Client → (I.Day → ℕ) → Prop
  | [], _ => True
  | j :: rest, st => ∃ S : Finset I.Day, S.card = k ∧ (∀ i ∈ S, I.p i j + st i ≤ dd j) ∧
      Dp dd k rest fun i => if i ∈ S then dd j else st i

instance decidableDp (dd : I.Client → ℕ) (k : ℕ) :
    ∀ (l : List I.Client) (st : I.Day → ℕ), Decidable (Dp dd k l st)
  | [], _ => isTrue trivial
  | j :: rest, st => by
      have inst : ∀ S : Finset I.Day,
          Decidable (S.card = k ∧ (∀ i ∈ S, I.p i j + st i ≤ dd j) ∧
            Dp dd k rest fun i => if i ∈ S then dd j else st i) := by
        intro S
        haveI := decidableDp dd k rest fun i => if i ∈ S then dd j else st i
        infer_instance
      exact @Fintype.decidableExistsFintype _ _ inst _

/-! ## 3. Correctness of the table -/

/-- **The invariant of Theorem 12's dynamic program.** A state `st` and a remaining list
`l` admit a table entry exactly when the clients of `l` can be scheduled — feasibly, `k`
days each, and compatibly with what `st` records as already running on each day. -/
theorem dp_iff (hd : I.DayIndepD) (i₀ : I.Day) (k : ℕ) :
    ∀ (l : List I.Client), l.Nodup → l.Pairwise (fun a b => I.d i₀ a ≤ I.d i₀ b) →
    ∀ st : I.Day → ℕ,
      Dp (I.d i₀) k l st ↔ ∃ σ : I.Schedule,
        (∀ i, ∀ j ∈ σ i, j ∈ l) ∧ Feasible σ ∧ (∀ j ∈ l, served σ j = k) ∧
        (∀ i, ∀ j ∈ σ i, I.p i j + st i ≤ I.d i₀ j) := by
  classical
  have hdd : ∀ (i : I.Day) (j : I.Client), I.d i j = I.d i₀ j := fun i j => hd i i₀ j
  intro l
  induction l with
  | nil =>
    intro _ _ st
    simp only [Dp, true_iff]
    exact ⟨fun _ => ∅, by simp, feasible_empty, by simp, by simp⟩
  | cons j rest ih =>
    intro hnd hsorted st
    have hjrest : j ∉ rest := (List.nodup_cons.1 hnd).1
    have hndrest : rest.Nodup := (List.nodup_cons.1 hnd).2
    have hhead : ∀ y ∈ rest, I.d i₀ j ≤ I.d i₀ y := (List.pairwise_cons.1 hsorted).1
    have hsortedrest : rest.Pairwise (fun a b => I.d i₀ a ≤ I.d i₀ b) :=
      (List.pairwise_cons.1 hsorted).2
    constructor
    · rintro ⟨S, hScard, hScompat, hrec⟩
      obtain ⟨σ', hsup', hfeas', hserved', hcompat'⟩ :=
        (ih hndrest hsortedrest _).1 hrec
      have hjnot : ∀ i, j ∉ σ' i := fun i hmem => hjrest (hsup' i j hmem)
      have key : ∀ (i : I.Day) (x : I.Client),
          x ∈ (if i ∈ S then insert j (σ' i) else σ' i) ↔ ((i ∈ S ∧ x = j) ∨ x ∈ σ' i) := by
        intro i x
        by_cases hi : i ∈ S
        · rw [if_pos hi]; simp [Finset.mem_insert, hi]
        · rw [if_neg hi]; simp [hi]
      -- a client already placed on day `i ∈ S` finishes late enough to clear `j`
      have hclear : ∀ i ∈ S, ∀ z ∈ σ' i, ¬ I.Conflict i j z := by
        intro i hi z hz
        have h := hcompat' i z hz
        rw [if_pos hi] at h
        refine not_conflict_of_le ?_
        simp only [start, hdd i z, hdd i j]
        omega
      refine ⟨fun i => if i ∈ S then insert j (σ' i) else σ' i, ?_, ?_, ?_, ?_⟩
      · -- support
        intro i x hx
        rcases (key i x).1 hx with ⟨-, rfl⟩ | hx'
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hsup' i x hx')
      · -- feasibility
        intro i x hx y hy hne
        rcases (key i x).1 hx with ⟨hiS, rfl⟩ | hx'
        · rcases (key i y).1 hy with ⟨-, rfl⟩ | hy'
          · exact absurd rfl hne
          · exact hclear i hiS y hy'
        · rcases (key i y).1 hy with ⟨hiS, rfl⟩ | hy'
          · exact fun hc => hclear i hiS x hx' (conflict_symm hc)
          · exact hfeas' i x hx' y hy' hne
      · -- every client is served exactly `k` times
        intro y hy
        rcases List.mem_cons.1 hy with heq | hy'
        · subst heq
          have hfil : (Finset.univ.filter fun i =>
              y ∈ (if i ∈ S then insert y (σ' i) else σ' i)) = S := by
            ext i
            rw [Finset.mem_filter]
            constructor
            · rintro ⟨-, hmem⟩
              rcases (key i y).1 hmem with ⟨hi, -⟩ | hmem'
              · exact hi
              · exact absurd hmem' (hjnot i)
            · intro hi
              exact ⟨Finset.mem_univ i, (key i y).2 (Or.inl ⟨hi, rfl⟩)⟩
          rw [served, hfil, hScard]
        · have hyj : y ≠ j := fun h => hjrest (h ▸ hy')
          have hfil : (Finset.univ.filter fun i =>
              y ∈ (if i ∈ S then insert j (σ' i) else σ' i))
              = Finset.univ.filter fun i => y ∈ σ' i := by
            ext i
            rw [Finset.mem_filter, Finset.mem_filter]
            constructor
            · rintro ⟨-, hmem⟩
              rcases (key i y).1 hmem with ⟨-, heq⟩ | hmem'
              · exact absurd heq hyj
              · exact ⟨Finset.mem_univ i, hmem'⟩
            · rintro ⟨-, hmem⟩
              exact ⟨Finset.mem_univ i, (key i y).2 (Or.inr hmem)⟩
          rw [served, hfil]
          exact hserved' y hy'
      · -- compatibility with the incoming state
        intro i x hx
        rcases (key i x).1 hx with ⟨hiS, rfl⟩ | hx'
        · exact hScompat i hiS
        · by_cases hi : i ∈ S
          · have h1 := hcompat' i x hx'
            rw [if_pos hi] at h1
            have h2 := hScompat i hi
            omega
          · have h1 := hcompat' i x hx'
            rwa [if_neg hi] at h1
    · rintro ⟨σ, hsup, hfeas, hserved, hcompat⟩
      refine ⟨Finset.univ.filter fun i => j ∈ σ i, ?_, ?_, ?_⟩
      · simpa [served] using hserved j (List.mem_cons_self ..)
      · intro i hi
        exact hcompat i j (Finset.mem_filter.1 hi).2
      · refine (ih hndrest hsortedrest _).2
          ⟨fun i => (σ i).erase j, ?_, ?_, ?_, ?_⟩
        · intro i x hx
          have hx' := Finset.mem_of_mem_erase hx
          rcases List.mem_cons.1 (hsup i x hx') with heq | h
          · exact absurd heq (Finset.ne_of_mem_erase hx)
          · exact h
        · exact hfeas.mono fun i => Finset.erase_subset _ _
        · intro y hy
          have hyj : y ≠ j := fun h => hjrest (h ▸ hy)
          have hfil : (Finset.univ.filter fun i => y ∈ (σ i).erase j)
              = Finset.univ.filter fun i => y ∈ σ i := by
            ext i; simp [Finset.mem_erase, hyj]
          rw [served, hfil]
          exact hserved y (List.mem_cons_of_mem _ hy)
        · intro i x hx
          have hxj : x ≠ j := Finset.ne_of_mem_erase hx
          have hxσ : x ∈ σ i := Finset.mem_of_mem_erase hx
          by_cases hi : j ∈ σ i
          · rw [if_pos (show i ∈ Finset.univ.filter (fun i' => j ∈ σ i') from
              Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)]
            -- `j` runs on day `i`, so `x` must clear it; `x` comes later in the order
            have hdx : I.d i₀ j ≤ I.d i₀ x := by
              rcases List.mem_cons.1 (hsup i x hxσ) with heq | h
              · exact absurd heq hxj
              · exact hhead x h
            have hnc : ¬ I.Conflict i x j := hfeas i x hxσ j hi hxj
            rw [notConflict_iff_le (by rw [hdd i j, hdd i x]; exact hdx)] at hnc
            rw [hdd i j, hdd i x] at hnc
            exact hnc
          · rw [if_neg (show i ∉ Finset.univ.filter (fun i' => j ∈ σ i') from
              fun hmem => hi (Finset.mem_filter.1 hmem).2)]
            exact hcompat i x hxσ

/-! ## 4. From "exactly `k`" to "at least `k`" -/

/-- Serving a client on *more* than `k` days is never necessary: drop the extra days. -/
lemma hasKFairSchedule_iff_exact (k : ℕ) :
    I.HasKFairSchedule k ↔ ∃ σ : I.Schedule, Feasible σ ∧ ∀ j, served σ j = k := by
  classical
  constructor
  · rintro ⟨σ, hfeas, hfair⟩
    have hT : ∀ j : I.Client, ∃ T : Finset I.Day,
        T ⊆ (Finset.univ.filter fun i => j ∈ σ i) ∧ T.card = k := fun j =>
      Finset.exists_subset_card_eq (hfair j)
    choose T hTsub hTcard using hT
    refine ⟨fun i => (σ i).filter fun j => i ∈ T j, hfeas.mono fun i => Finset.filter_subset _ _,
      fun j => ?_⟩
    have : (Finset.univ.filter fun i => j ∈ (σ i).filter fun j' => i ∈ T j') = T j := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.1 (hTsub j h)).2, h⟩⟩
    rw [served, this, hTcard]
  · rintro ⟨σ, hfeas, hexact⟩
    exact ⟨σ, hfeas, fun j => le_of_eq (hexact j).symm⟩

/-! ## 5. Theorem 12 -/

/-- **Theorem 12's correctness.** With day-independent due dates, a feasible `k`-fair
schedule exists exactly when the dynamic-programming table accepts, started from the empty
state on the clients listed in non-decreasing order of due date. -/
theorem hasKFairSchedule_iff_dp (hd : I.DayIndepD) (i₀ : I.Day) (k : ℕ)
    {l : List I.Client} (hnd : l.Nodup) (hall : ∀ c, c ∈ l)
    (hsorted : l.Pairwise fun a b => I.d i₀ a ≤ I.d i₀ b) :
    I.HasKFairSchedule k ↔ Dp (I.d i₀) k l fun _ => 0 := by
  rw [hasKFairSchedule_iff_exact, dp_iff hd i₀ k l hnd hsorted]
  constructor
  · rintro ⟨σ, hfeas, hexact⟩
    exact ⟨σ, fun i x _ => hall x, hfeas, fun y _ => hexact y, fun i x _ => by
      simpa [hd i i₀ x] using I.p_le_d i x⟩
  · rintro ⟨σ, -, hfeas, hexact, -⟩
    exact ⟨σ, hfeas, fun y => hexact y (hall y)⟩

end Instance

end Lax117284Proofs.Model
