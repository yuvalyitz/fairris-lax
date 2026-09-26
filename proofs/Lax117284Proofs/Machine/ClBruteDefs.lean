import Mathlib.Tactic
import Lax117284Proofs.ClientsWord

/-!
The brute force, the mathematics: a schedule is a string of `m * n` bits, the number it reads in
base two.

Nothing here mentions the machine. A schedule is a vector of `m * n` bits (cell `i * n + j` says
that client `j` is served on day `i`), and the vectors are the numbers below `2 ^ (m * n)`
(`enc`, `dig`). Feasibility is the scan of the ordered pairs `a < b` of one day (`FeasF`),
fairness is the scan of the column of each client (`FairF`), and `hasK_iff` says that a fair
schedule exists exactly when some number below `2 ^ (m * n)` passes both scans.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

/-! ### Numbers as bit vectors -/

/-- The number of the first `m` bits of `u`, in base two. -/
def enc (u : ℕ → ℕ) (m : ℕ) : ℕ := ∑ i ∈ Finset.range m, u i * 2 ^ i

/-- The `i`-th bit of `c`. -/
def dig (c i : ℕ) : ℕ := c / 2 ^ i % 2

lemma enc_zero (u : ℕ → ℕ) : enc u 0 = 0 := Eq.trans rfl rfl

lemma enc_succ (u : ℕ → ℕ) (m : ℕ) : enc u (m + 1) = enc u m + u m * 2 ^ m :=
  Finset.sum_range_succ _ _

lemma enc_congr {u v : ℕ → ℕ} {m : ℕ} (h : ∀ i, i < m → u i = v i) : enc u m = enc v m :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

lemma enc_lt {u : ℕ → ℕ} {m : ℕ} (hu : ∀ i, i < m → u i ≤ 1) : enc u m < 2 ^ m := by
  induction m with
  | zero => simp [enc]
  | succ m ih =>
      have h1 := ih fun i hi => hu i (by omega)
      have h2 : u m ≤ 1 := hu m (by omega)
      have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
      rw [enc_succ, pow_succ]
      nlinarith

lemma dig_le (c i : ℕ) : dig c i ≤ 1 := by
  have := Nat.mod_lt (c / 2 ^ i) (show 0 < 2 by omega)
  simp only [dig]; omega

/-- The bits of a number are the vector it encodes. -/
lemma dig_enc {u : ℕ → ℕ} {m : ℕ} (hu : ∀ i, i < m → u i ≤ 1) (i : ℕ) (hi : i < m) :
    dig (enc u m) i = u i := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_ge i m with h | h
      · have hkey : enc u (m + 1) / 2 ^ i % 2 = enc u m / 2 ^ i % 2 := by
          obtain ⟨c, hc⟩ : ∃ c, 2 ^ m = 2 ^ i * (2 * c) :=
            ⟨2 ^ (m - i - 1), by
              conv_lhs => rw [show m = i + 1 + (m - i - 1) by omega]
              rw [pow_add, pow_succ]; ring⟩
          have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
          have : u m * 2 ^ m = 2 ^ i * (2 * (u m * c)) := by rw [hc]; ring
          rw [enc_succ, this, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]
        rw [dig, hkey]
        exact ih (fun k hk => hu k (by omega)) i h
      · have him : i = m := by omega
        subst him
        have hlt : enc u i < 2 ^ i := enc_lt fun k hk => hu k (by omega)
        have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
        have h1 := hu i (by omega)
        rw [dig, enc_succ, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt,
          Nat.zero_add, Nat.mod_eq_of_lt (by omega)]

/-! ### Feasibility and fairness of a vector -/

section Vector

variable (I : Instance)

/-- Clients `a < b` are both served on day `i` by the vector `f` and conflict. -/
def Bad (f : ℕ → ℕ) (i a b : ℕ) : Prop :=
  a < b ∧ b < I.clients ∧ f (i * I.clients + a) = 1 ∧ f (i * I.clients + b) = 1 ∧
    I.ConflictAt i a b

/-- No day serves two clients that conflict. -/
def FeasF (f : ℕ → ℕ) : Prop := ∀ i, i < I.days → ∀ a b, ¬ Bad I f i a b

/-- Every client is served on at least `k` days. -/
def FairF (k : ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ j, j < I.clients → k ≤ ∑ i ∈ Finset.range I.days, f (i * I.clients + j)

/-- The vector `f` (a number, as its bits) passes both scans. -/
def Chk (k s : ℕ) : Prop := FeasF I (dig s) ∧ FairF I k (dig s)

lemma idx_lt {i a : ℕ} (hi : i < I.days) (ha : a < I.clients) :
    i * I.clients + a < I.days * I.clients := by
  have : (i + 1) * I.clients ≤ I.days * I.clients := Nat.mul_le_mul_right _ hi
  nlinarith

lemma feasF_congr {f g : ℕ → ℕ} (h : ∀ r, r < I.days * I.clients → f r = g r) :
    FeasF I f ↔ FeasF I g := by
  constructor
  · intro hf i hi a b ⟨hab, hb, h1, h2, hc⟩
    exact hf i hi a b ⟨hab, hb, by rw [h _ (idx_lt I hi (by omega))]; exact h1,
      by rw [h _ (idx_lt I hi hb)]; exact h2, hc⟩
  · intro hf i hi a b ⟨hab, hb, h1, h2, hc⟩
    exact hf i hi a b ⟨hab, hb, by rw [← h _ (idx_lt I hi (by omega))]; exact h1,
      by rw [← h _ (idx_lt I hi hb)]; exact h2, hc⟩

lemma fairF_congr {k : ℕ} {f g : ℕ → ℕ} (h : ∀ r, r < I.days * I.clients → f r = g r) :
    FairF I k f ↔ FairF I k g := by
  have hs : ∀ j, j < I.clients →
      ∑ i ∈ Finset.range I.days, f (i * I.clients + j) =
        ∑ i ∈ Finset.range I.days, g (i * I.clients + j) := fun j hj =>
    Finset.sum_congr rfl fun i hi => h _ (idx_lt I (Finset.mem_range.mp hi) hj)
  constructor
  · intro hf j hj; rw [← hs j hj]; exact hf j hj
  · intro hf j hj; rw [hs j hj]; exact hf j hj

/-- The schedule a vector reads: client `j` is served on day `i` when cell `i * n + j` is `1`. -/
def schedOf (f : ℕ → ℕ) : I.Schedule := fun i =>
  Finset.univ.filter fun j : Fin I.clients => f (i.val * I.clients + j.val) = 1

lemma conflict_symm' {i : Fin I.days} {j j' : Fin I.clients} (h : I.Conflict i j j') :
    I.Conflict i j' j := by
  unfold Instance.Conflict at *
  rwa [Set.inter_comm]

lemma feasible_iff (f : ℕ → ℕ) : Feasible (schedOf I f) ↔ FeasF I f := by
  constructor
  · intro h i hi a b ⟨hab, hb, h1, h2, hc⟩
    have ha : a < I.clients := by omega
    have := h ⟨i, hi⟩ (x := ⟨a, ha⟩) (by simp [schedOf, h1]) (y := ⟨b, hb⟩)
      (by simp [schedOf, h2]) (by simp [Fin.ext_iff]; omega)
    exact this ((Instance.conflictAt_iff I ⟨i, hi⟩ ⟨a, ha⟩ ⟨b, hb⟩).mp hc)
  · intro h i x hx y hy hne hconf
    simp only [schedOf, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
    have hne' : x.val ≠ y.val := fun e => hne (Fin.ext e)
    rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
    · exact h i.val i.isLt x.val y.val
        ⟨hlt, y.isLt, hx, hy, (Instance.conflictAt_iff I i x y).mpr hconf⟩
    · exact h i.val i.isLt y.val x.val
        ⟨hlt, x.isLt, hy, hx, (Instance.conflictAt_iff I i y x).mpr (conflict_symm' I hconf)⟩

lemma served_eq (f : ℕ → ℕ) (hf : ∀ r, r < I.days * I.clients → f r ≤ 1) (j : Fin I.clients) :
    served (schedOf I f) j = ∑ i ∈ Finset.range I.days, f (i * I.clients + j.val) := by
  unfold served
  rw [Finset.card_filter]
  have : ∀ i : Fin I.days, (if j ∈ schedOf I f i then 1 else 0) = f (i.val * I.clients + j.val) := by
    intro i
    have h1 := hf _ (idx_lt I i.isLt j.isLt)
    by_cases h : f (i.val * I.clients + j.val) = 1
    · simp [schedOf, h]
    · have : f (i.val * I.clients + j.val) = 0 := by omega
      simp [schedOf, this]
  simp only [this]
  exact Fin.sum_univ_eq_sum_range (fun i => f (i * I.clients + j.val)) I.days

lemma fair_iff (k : ℕ) (f : ℕ → ℕ) (hf : ∀ r, r < I.days * I.clients → f r ≤ 1) :
    Fair (fun _ => k) (schedOf I f) ↔ FairF I k f := by
  constructor
  · intro h j hj
    have := h ⟨j, hj⟩
    rwa [served_eq I f hf] at this
  · intro h j
    rw [served_eq I f hf]
    exact h j.val j.isLt

/-- The vector a schedule is. -/
def fOf (σ : I.Schedule) (q : ℕ) : ℕ :=
  if h : q / I.clients < I.days ∧ q % I.clients < I.clients then
    (if (⟨q % I.clients, h.2⟩ : Fin I.clients) ∈ σ ⟨q / I.clients, h.1⟩ then 1 else 0)
  else 0

lemma fOf_le (σ : I.Schedule) (q : ℕ) : fOf I σ q ≤ 1 := by
  unfold fOf; split_ifs <;> omega

lemma fOf_at (σ : I.Schedule) {i j : ℕ} (hi : i < I.days) (hj : j < I.clients) :
    fOf I σ (i * I.clients + j) = if (⟨j, hj⟩ : Fin I.clients) ∈ σ ⟨i, hi⟩ then 1 else 0 := by
  have hn : 0 < I.clients := by omega
  have h1 : (i * I.clients + j) / I.clients = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj, zero_add]
  have h2 : (i * I.clients + j) % I.clients = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  simp only [fOf, h1, h2, hi, hj, and_self, dite_true]

lemma schedOf_fOf (σ : I.Schedule) : schedOf I (fOf I σ) = σ := by
  funext i
  ext j
  simp only [schedOf, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [fOf_at I σ i.isLt j.isLt]
  simp

/-- **The brute force is correct**: a fair schedule exists exactly when one of the numbers below
`2 ^ (m * n)` reads a vector that passes both scans. -/
theorem hasK_iff (k : ℕ) :
    I.HasKFairSchedule k ↔ ∃ s, s < 2 ^ (I.days * I.clients) ∧ Chk I k s := by
  constructor
  · rintro ⟨σ, hfeas, hfair⟩
    have hb : ∀ r, r < I.days * I.clients → fOf I σ r ≤ 1 := fun r _ => fOf_le I σ r
    have hd : ∀ r, r < I.days * I.clients → dig (enc (fOf I σ) (I.days * I.clients)) r =
        fOf I σ r := fun r hr => dig_enc hb r hr
    refine ⟨enc (fOf I σ) (I.days * I.clients), enc_lt hb, ?_, ?_⟩
    · rw [feasF_congr I hd, ← feasible_iff, schedOf_fOf]; exact hfeas
    · rw [fairF_congr I hd, ← fair_iff I k _ hb, schedOf_fOf]; exact hfair
  · rintro ⟨s, -, hfeas, hfair⟩
    refine ⟨schedOf I (dig s), ?_, ?_⟩
    · exact (feasible_iff I _).mpr hfeas
    · exact (fair_iff I k _ (fun r _ => dig_le s r)).mpr hfair

end Vector

end Lax117284Proofs.Machine.ClBrute
