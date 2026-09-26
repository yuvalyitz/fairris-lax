import Lax117284Proofs.Theorem10_Decide
import Lax117284Proofs.Theorem2Decide
import Lax117284Proofs.Bridge

/-!
Theorem 2, tractability, mathematics: with unit processing times, the fair schedules of an
instance are the full matchings of an explicit bipartite graph, given as a flat table of zeros
and ones in the input format of the matching decider of `Machine/MatchGuard`.

The left vertices are the jobs `(i, j)` (day `i`, client `j`), row `r = i * n + j`.
The right vertices are, first, the `m * n` cells `(i, j')`, column `i * n + j'`: the cell
`(i, j')` stands for "the due date of client `j'` on day `i`", and only the first client `j'`
of a day with a given due date has edges (`repN`), so every due date of a day is one vertex;
then, client after client, `m - k` rejection vertices of the client.
-/

namespace Lax117284Proofs.UnitPGraph

open Lax117284.Scheduling

/-- The bipartite graph a table word carries: `n = x[0]` left vertices, `m = x[1]` right
vertices, and row `i` of the table (from position `2`) has a nonzero entry in column `j`
exactly when `i` and `j` are adjacent. Cells beyond the word read as `0`. -/
def decodeAdj (x : List ℕ) : Fin (x.getD 0 0) → Fin (x.getD 1 0) → Prop :=
  fun i j => x.getD (2 + i.val * x.getD 1 0 + j.val) 0 ≠ 0

/-- **The bipartite graph has a matching saturating every left vertex**: an injection of the
left vertices into the right ones along the edges. -/
def HasFullMatching {L R : Type*} (adj : L → R → Prop) : Prop :=
  ∃ f : L → R, Function.Injective f ∧ ∀ l, adj l (f l)

/-- The word carries a graph with a matching saturating its left side. -/
def Yes (x : List ℕ) : Prop := HasFullMatching (decodeAdj x)

/-- The first client of day `i` whose due date equals the due date of client `j`. `d` lists
the due dates day by day, `n` clients per day. -/
def repN (n : ℕ) (d : ℕ → ℕ) (i j : ℕ) : ℕ :=
  ((List.range n).find? (fun j' => decide (d (i * n + j') = d (i * n + j)))).getD j

/-- The entry of the table in row `r` and column `c`. -/
def entry (n m k : ℕ) (d : ℕ → ℕ) (r c : ℕ) : ℕ :=
  if c < m * n then (if c = (r / n) * n + repN n d (r / n) (r % n) then 1 else 0)
  else if (r % n) * (m - k) ≤ c - m * n ∧ c - m * n < (r % n + 1) * (m - k) then 1 else 0

/-- The number of columns. -/
def cols (n m k : ℕ) : ℕ := m * n + n * (m - k)

/-- The word of the graph, as a list of numbers: the numbers of rows and columns, then the
table row by row. A parameter above the number of days is answered by a graph with a full
matching if there is no client, and by one without if there is one. -/
def graphNums (n m k : ℕ) (d : ℕ → ℕ) : List ℕ :=
  if k ≤ m then
    [m * n, cols n m k] ++
      (List.range (m * n)).flatMap fun r => (List.range (cols n m k)).map (entry n m k d r)
  else if n = 0 then [0, 0] else [1, 0]

/-! ### Arithmetic of `i * n + j` -/

theorem pair_lt {i j m n : ℕ} (hi : i < m) (hj : j < n) : i * n + j < m * n := by
  have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at h
  omega

theorem block_lt {j n w ℓ : ℕ} (hj : j < n) (hℓ : ℓ < w) : j * w + ℓ < n * w := by
  have h := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hj)
  rw [Nat.succ_mul] at h
  omega

theorem div_pair {i j n : ℕ} (hj : j < n) : (i * n + j) / n = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < n), Nat.div_eq_of_lt hj,
    Nat.zero_add]

theorem mod_pair {i j n : ℕ} (hj : j < n) : (i * n + j) % n = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

theorem mul_add_inj {i i' j j' n : ℕ} (hj : j < n) (hj' : j' < n)
    (h : i * n + j = i' * n + j') : i = i' ∧ j = j' := by
  have hi : i = i' := by rw [← div_pair (i := i) hj, ← div_pair (i := i') hj', h]
  subst hi
  exact ⟨rfl, by omega⟩

/-! ### The word of the graph: header and table -/

private theorem flat_length (R C : ℕ) (g : ℕ → ℕ → ℕ) :
    ((List.range R).flatMap fun r => (List.range C).map (g r)).length = R * C := by
  induction R with
  | zero => simp
  | succ R ih => simp [List.range_succ, List.flatMap_append, ih, Nat.succ_mul]

private theorem flat_getD (R C : ℕ) (g : ℕ → ℕ → ℕ) (r c : ℕ) (hr : r < R) (hc : c < C) :
    ((List.range R).flatMap fun r => (List.range C).map (g r)).getD (r * C + c) 0 = g r c := by
  induction R with
  | zero => omega
  | succ R ih =>
    rw [List.range_succ, List.flatMap_append, List.getD_eq_getElem?_getD]
    by_cases h : r < R
    · rw [List.getElem?_append_left (by rw [flat_length]; exact pair_lt h hc),
        ← List.getD_eq_getElem?_getD]
      exact ih h
    · have hrR : r = R := by omega
      subst hrR
      rw [List.getElem?_append_right (by rw [flat_length]; omega), flat_length]
      simp [hc]

theorem getD_zero {n m k : ℕ} {d : ℕ → ℕ} (hk : k ≤ m) :
    (graphNums n m k d).getD 0 0 = m * n := by
  simp [graphNums, hk]

theorem getD_one {n m k : ℕ} {d : ℕ → ℕ} (hk : k ≤ m) :
    (graphNums n m k d).getD 1 0 = cols n m k := by
  simp [graphNums, hk]

theorem getD_tab {n m k : ℕ} {d : ℕ → ℕ} (hk : k ≤ m) {r c : ℕ} (hr : r < m * n)
    (hc : c < cols n m k) :
    (graphNums n m k d).getD (2 + r * cols n m k + c) 0 = entry n m k d r c := by
  have h := flat_getD (m * n) (cols n m k) (entry n m k d) r c hr hc
  rw [Nat.add_assoc]
  simp only [graphNums, hk, if_true]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simpa [List.getD_eq_getElem?_getD] using h

/-! ### Reading a matching off the word -/

theorem yes_iff_nat (x : List ℕ) :
    Yes x ↔ ∃ f : ℕ → ℕ,
      (∀ r < x.getD 0 0, f r < x.getD 1 0 ∧ x.getD (2 + r * x.getD 1 0 + f r) 0 ≠ 0) ∧
      ∀ r < x.getD 0 0, ∀ r' < x.getD 0 0, f r = f r' → r = r' := by
  constructor
  · rintro ⟨f, hinj, hadj⟩
    refine ⟨fun r => if h : r < x.getD 0 0 then (f ⟨r, h⟩).val else 0, ?_, ?_⟩
    · intro r hr
      have := hadj ⟨r, hr⟩
      simp only [dif_pos hr]
      exact ⟨(f ⟨r, hr⟩).isLt, this⟩
    · intro r hr r' hr' h
      simp only [dif_pos hr, dif_pos hr'] at h
      exact congrArg Fin.val (hinj (Fin.ext h))
  · rintro ⟨f, hf, hinj⟩
    refine ⟨fun r => ⟨f r.val, (hf r.val r.isLt).1⟩, ?_, ?_⟩
    · intro a b h
      exact Fin.ext (hinj a.val a.isLt b.val b.isLt (congrArg Fin.val h))
    · intro r
      exact (hf r.val r.isLt).2

/-! ### The client of a due date -/

theorem repN_spec {n : ℕ} {d : ℕ → ℕ} {i j : ℕ} (hj : j < n) :
    repN n d i j < n ∧ d (i * n + repN n d i j) = d (i * n + j) := by
  have hne : (List.range n).find? (fun j' => decide (d (i * n + j') = d (i * n + j))) ≠ none := by
    rw [Ne, List.find?_eq_none]
    intro h
    exact h j (List.mem_range.2 hj) (by simp)
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hne
  have h1 := List.find?_some ha
  have h2 := List.mem_of_find?_eq_some ha
  simp only [repN, ha, Option.getD_some]
  exact ⟨List.mem_range.1 h2, by simpa using h1⟩

theorem repN_congr {n : ℕ} {d : ℕ → ℕ} {i j j' : ℕ} (hj' : j' < n)
    (h : d (i * n + j) = d (i * n + j')) : repN n d i j = repN n d i j' := by
  have hne : (List.range n).find? (fun x => decide (d (i * n + x) = d (i * n + j'))) ≠ none := by
    rw [Ne, List.find?_eq_none]
    intro h'
    exact h' j' (List.mem_range.2 hj') (by simp)
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hne
  simp only [repN, h, ha, Option.getD_some]

/-! ### The graph on numbers -/

/-- The neighbours of the job `(i, j)`, as columns. -/
def Adj (n m k : ℕ) (d : ℕ → ℕ) (i j c : ℕ) : Prop :=
  c = i * n + repN n d i j ∨
    (m * n ≤ c ∧ j * (m - k) ≤ c - m * n ∧ c - m * n < (j + 1) * (m - k))

theorem entry_ne_zero_iff {n m k : ℕ} {d : ℕ → ℕ} {r i j c : ℕ} (hi : i < m) (hj : j < n)
    (hr : r / n = i) (hr' : r % n = j) :
    entry n m k d r c ≠ 0 ↔ Adj n m k d i j c := by
  have h1 := pair_lt hi (repN_spec (n := n) (d := d) (i := i) hj).1
  unfold entry Adj
  rw [hr, hr']
  split_ifs <;> omega

/-- A matching, as a function on the pairs of numbers. -/
def PairMatch (n m k : ℕ) (d : ℕ → ℕ) (f : ℕ → ℕ → ℕ) : Prop :=
  (∀ i < m, ∀ j < n, f i j < cols n m k ∧ Adj n m k d i j (f i j)) ∧
  ∀ i < m, ∀ j < n, ∀ i' < m, ∀ j' < n, f i j = f i' j' → i = i' ∧ j = j'

theorem yes_iff_pair {n m k : ℕ} {d : ℕ → ℕ} (hk : k ≤ m) :
    Yes (graphNums n m k d) ↔ ∃ f, PairMatch n m k d f := by
  rw [yes_iff_nat, getD_zero hk, getD_one hk]
  constructor
  · rintro ⟨f, hf, hinj⟩
    refine ⟨fun i j => f (i * n + j), fun i hi j hj => ?_, fun i hi j hj i' hi' j' hj' h => ?_⟩
    · have hr := pair_lt hi hj
      obtain ⟨h1, h2⟩ := hf _ hr
      rw [getD_tab hk hr h1] at h2
      exact ⟨h1, (entry_ne_zero_iff hi hj (div_pair hj) (mod_pair hj)).1 h2⟩
    · exact mul_add_inj hj hj' (hinj _ (pair_lt hi hj) _ (pair_lt hi' hj') h)
  · rintro ⟨g, hg, hinj⟩
    refine ⟨fun r => g (r / n) (r % n), fun r hr => ?_, fun r hr r' hr' h => ?_⟩
    · have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hr)
      have hi : r / n < m := (Nat.div_lt_iff_lt_mul hn).2 hr
      have hj : r % n < n := Nat.mod_lt _ hn
      obtain ⟨h1, h2⟩ := hg _ hi _ hj
      refine ⟨h1, ?_⟩
      rw [getD_tab hk hr h1]
      exact (entry_ne_zero_iff hi hj rfl rfl).2 h2
    · have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hr)
      have hm : ∀ q, q < m * n → q / n < m ∧ q % n < n := fun q hq =>
        ⟨(Nat.div_lt_iff_lt_mul hn).2 hq, Nat.mod_lt _ hn⟩
      obtain ⟨e1, e2⟩ := hinj _ (hm r hr).1 _ (hm r hr).2 _ (hm r' hr').1 _ (hm r' hr').2 h
      rw [← Nat.div_add_mod' r n, ← Nat.div_add_mod' r' n, e1, e2]

/-! ### The paper's graph -/

theorem blk_adj {W j w ℓ : ℕ} (hℓ : ℓ < w) :
    W ≤ W + j * w + ℓ ∧ j * w ≤ W + j * w + ℓ - W ∧ W + j * w + ℓ - W < (j + 1) * w := by
  have h3 : (j + 1) * w = j * w + w := by rw [Nat.add_mul, Nat.one_mul]
  omega

/-- The column a target of the paper's graph stands for, seen from the job `(i, j)`. -/
def colOf (I : Instance) (k : ℕ) (d : ℕ → ℕ) (i j : ℕ)
    (t : Lax117284Proofs.Model.Instance.MatchTarget (Bridge.model I)) : ℕ :=
  Sum.elim (α := Fin I.days × ℕ) (β := ℕ × Fin I.clients)
    (fun _ => i * I.clients + repN I.clients d i j)
    (fun p => I.days * I.clients + j * (I.days - k) + p.1) t

theorem colOf_spec (I : Instance) (k : ℕ) (d : ℕ → ℕ) {i j : ℕ} (hi : i < I.days)
    (hj : j < I.clients) (t : Lax117284Proofs.Model.Instance.MatchTarget (Bridge.model I))
    (ht : Lax117284Proofs.Model.Instance.Matchable (I := Bridge.model I) k
      ((⟨i, hi⟩ : Fin I.days), (⟨j, hj⟩ : Fin I.clients)) t) :
    colOf I k d i j t < cols I.clients I.days k ∧
      Adj I.clients I.days k d i j (colOf I k d i j t) := by
  have h1 := pair_lt hi (repN_spec (n := I.clients) (d := d) (i := i) hj).1
  rcases ht with h | ⟨ℓ, hℓ, h⟩
  · subst h
    change i * I.clients + repN I.clients d i j < _ ∧ Adj _ _ _ _ _ _ (i * I.clients + _)
    exact ⟨by unfold cols; omega, Or.inl rfl⟩
  · subst h
    have hℓ' : ℓ < I.days - k := by simpa using hℓ
    have h2 := block_lt hj hℓ'
    change I.days * I.clients + j * (I.days - k) + ℓ < _ ∧
      Adj _ _ _ _ _ _ (I.days * I.clients + j * (I.days - k) + ℓ)
    refine ⟨by unfold cols; omega, Or.inr ?_⟩
    exact blk_adj hℓ'

theorem colOf_inj (I : Instance) (k : ℕ) (d : ℕ → ℕ)
    (hd : ∀ (i : Fin I.days) (j : Fin I.clients), d (i * I.clients + j) = I.d i j)
    {i j i' j' : ℕ} (hi : i < I.days) (hj : j < I.clients) (hi' : i' < I.days)
    (hj' : j' < I.clients) (t t' : Lax117284Proofs.Model.Instance.MatchTarget (Bridge.model I))
    (ht : Lax117284Proofs.Model.Instance.Matchable (I := Bridge.model I) k
      ((⟨i, hi⟩ : Fin I.days), (⟨j, hj⟩ : Fin I.clients)) t)
    (ht' : Lax117284Proofs.Model.Instance.Matchable (I := Bridge.model I) k
      ((⟨i', hi'⟩ : Fin I.days), (⟨j', hj'⟩ : Fin I.clients)) t')
    (h : colOf I k d i j t = colOf I k d i' j' t') : t = t' := by
  have h1 := pair_lt hi (repN_spec (n := I.clients) (d := d) (i := i) hj).1
  have h1' := pair_lt hi' (repN_spec (n := I.clients) (d := d) (i := i') hj').1
  rcases ht with rfl | ⟨ℓ, hℓ, rfl⟩ <;> rcases ht' with rfl | ⟨ℓ', hℓ', rfl⟩
  · change i * I.clients + repN I.clients d i j = i' * I.clients + repN I.clients d i' j' at h
    obtain ⟨rfl, h2⟩ := mul_add_inj (repN_spec (d := d) (i := i) hj).1 (repN_spec (d := d) (i := i') hj').1 h
    have h3 := (repN_spec (d := d) (i := i) hj).2
    have h4 := (repN_spec (d := d) (i := i) hj').2
    rw [h2, h4] at h3
    have := hd ⟨i, hi⟩ ⟨j, hj⟩
    have := hd ⟨i, hi⟩ ⟨j', hj'⟩
    have h5 : I.d ⟨i, hi⟩ ⟨j, hj⟩ = I.d ⟨i, hi⟩ ⟨j', hj'⟩ := by simp_all
    exact congrArg Sum.inl (Prod.ext rfl h5)
  · change i * I.clients + repN I.clients d i j =
      I.days * I.clients + j' * (I.days - k) + ℓ' at h
    omega
  · change I.days * I.clients + j * (I.days - k) + ℓ =
      i' * I.clients + repN I.clients d i' j' at h
    omega
  · have hℓ2 : ℓ < I.days - k := by simpa using hℓ
    have hℓ2' : ℓ' < I.days - k := by simpa using hℓ'
    change I.days * I.clients + j * (I.days - k) + ℓ =
      I.days * I.clients + j' * (I.days - k) + ℓ' at h
    obtain ⟨rfl, rfl⟩ := mul_add_inj (i := j) (i' := j') hℓ2 hℓ2' (by omega)
    rfl

theorem paper_to_pair (I : Instance) (k : ℕ) (d : ℕ → ℕ)
    (hd : ∀ (i : Fin I.days) (j : Fin I.clients), d (i * I.clients + j) = I.d i j)
    (h : Lax117284Proofs.Model.Instance.HasFullMatching (Bridge.model I) k) :
    ∃ f, PairMatch I.clients I.days k d f := by
  obtain ⟨g, hg, hm⟩ := h
  refine ⟨fun i j => if h : i < I.days ∧ j < I.clients then
      colOf I k d i j (g ((⟨i, h.1⟩ : Fin I.days), (⟨j, h.2⟩ : Fin I.clients))) else 0,
    fun i hi j hj => ?_, fun i hi j hj i' hi' j' hj' h => ?_⟩
  · simp only [dif_pos (And.intro hi hj)]
    exact colOf_spec I k d hi hj _ (hm _)
  · simp only [dif_pos (And.intro hi hj), dif_pos (And.intro hi' hj')] at h
    have := hg (colOf_inj I k d hd hi hj hi' hj' _ _ (hm _) (hm _) h)
    exact ⟨congrArg Fin.val (congrArg Prod.fst this), congrArg Fin.val (congrArg Prod.snd this)⟩

/-- The target a column of the table stands for. -/
def toTarget (I : Instance) (k : ℕ) (f : ℕ → ℕ → ℕ) (v : Fin I.days × Fin I.clients) :
    Lax117284Proofs.Model.Instance.MatchTarget (Bridge.model I) :=
  if f v.1 v.2 < I.days * I.clients then Sum.inl (v.1, I.d v.1 v.2)
  else Sum.inr (f v.1 v.2 - I.days * I.clients - v.2 * (I.days - k), v.2)

theorem toTarget_matchable (I : Instance) (k : ℕ) (d : ℕ → ℕ) (f : ℕ → ℕ → ℕ)
    (hf : PairMatch I.clients I.days k d f) (v : Fin I.days × Fin I.clients) :
    Lax117284Proofs.Model.Instance.Matchable (I := Bridge.model I) k v (toTarget I k f v) := by
  obtain ⟨h1, h2⟩ := hf.1 v.1 v.1.isLt v.2 v.2.isLt
  have h0 := pair_lt v.1.isLt (repN_spec (n := I.clients) (d := d) (i := v.1) v.2.isLt).1
  by_cases hc : f v.1 v.2 < I.days * I.clients
  · have e : toTarget I k f v = Sum.inl (v.1, I.d v.1 v.2) := if_pos hc
    rw [e]
    exact Or.inl rfl
  · have e : toTarget I k f v =
        Sum.inr (f v.1 v.2 - I.days * I.clients - v.2 * (I.days - k), v.2) := if_neg hc
    rw [e]
    refine Or.inr ⟨f v.1 v.2 - I.days * I.clients - v.2 * (I.days - k), ?_, rfl⟩
    have h3 : ((v.2 : ℕ) + 1) * (I.days - k) = v.2 * (I.days - k) + (I.days - k) := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [Bridge.model_numDays]
    rcases h2 with h2 | h2
    · omega
    · omega

theorem toTarget_injective (I : Instance) (k : ℕ) (d : ℕ → ℕ)
    (hd : ∀ (i : Fin I.days) (j : Fin I.clients), d (i * I.clients + j) = I.d i j)
    (f : ℕ → ℕ → ℕ) (hf : PairMatch I.clients I.days k d f) :
    Function.Injective (toTarget I k f) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  obtain ⟨a1, a2⟩ := hf.1 i i.isLt j j.isLt
  obtain ⟨b1, b2⟩ := hf.1 i' i'.isLt j' j'.isLt
  have key : f i j = f i' j' → (i, j) = (i', j') := fun e => by
    obtain ⟨e1, e2⟩ := hf.2 i i.isLt j j.isLt i' i'.isLt j' j'.isLt e
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  apply key
  have h0 := pair_lt i.isLt (repN_spec (n := I.clients) (d := d) (i := i) j.isLt).1
  have h0' := pair_lt i'.isLt (repN_spec (n := I.clients) (d := d) (i := i') j'.isLt).1
  by_cases hc : f i j < I.days * I.clients <;> by_cases hc' : f i' j' < I.days * I.clients
  · have e : toTarget I k f (i, j) = Sum.inl (i, I.d i j) := if_pos hc
    have e' : toTarget I k f (i', j') = Sum.inl (i', I.d i' j') := if_pos hc'
    rw [e, e'] at h
    have hh := Sum.inl.inj h
    obtain rfl : i = i' := congrArg Prod.fst hh
    have hdd : I.d i j = I.d i j' := congrArg Prod.snd hh
    have hdd' : d (i * I.clients + j) = d (i * I.clients + j') := by
      rw [hd i j, hd i j', hdd]
    rcases a2 with a2 | a2 <;> rcases b2 with b2 | b2
    · rw [a2, b2, repN_congr j'.isLt hdd']
    all_goals omega
  · have e : toTarget I k f (i, j) = Sum.inl (i, I.d i j) := if_pos hc
    have e' : toTarget I k f (i', j') =
        Sum.inr (f i' j' - I.days * I.clients - j' * (I.days - k), j') := if_neg hc'
    rw [e, e'] at h
    cases h
  · have e : toTarget I k f (i, j) =
        Sum.inr (f i j - I.days * I.clients - j * (I.days - k), j) := if_neg hc
    have e' : toTarget I k f (i', j') = Sum.inl (i', I.d i' j') := if_pos hc'
    rw [e, e'] at h
    cases h
  · have e : toTarget I k f (i, j) =
        Sum.inr (f i j - I.days * I.clients - j * (I.days - k), j) := if_neg hc
    have e' : toTarget I k f (i', j') =
        Sum.inr (f i' j' - I.days * I.clients - j' * (I.days - k), j') := if_neg hc'
    rw [e, e'] at h
    have hh := Sum.inr.inj h
    obtain rfl : j = j' := congrArg Prod.snd hh
    have hn : f i j - I.days * I.clients - j * (I.days - k) =
        f i' j - I.days * I.clients - j * (I.days - k) := congrArg Prod.fst hh
    rcases a2 with a2 | a2 <;> rcases b2 with b2 | b2 <;> omega

theorem pair_to_paper (I : Instance) (k : ℕ) (d : ℕ → ℕ)
    (hd : ∀ (i : Fin I.days) (j : Fin I.clients), d (i * I.clients + j) = I.d i j)
    (f : ℕ → ℕ → ℕ) (hf : PairMatch I.clients I.days k d f) :
    Lax117284Proofs.Model.Instance.HasFullMatching (Bridge.model I) k :=
  ⟨toTarget I k f, toTarget_injective I k d hd f hf, toTarget_matchable I k d f hf⟩

/-! ### The word answered when the parameter exceeds the number of days -/

theorem yes_zero : Yes [0, 0] :=
  (yes_iff_nat _).2 ⟨fun r => r, by simp, by simp⟩

/-- The word answered to every word that is not an accepted instance has no full matching. -/
theorem not_yes_reject : ¬ Yes [1, 0] := by
  rw [yes_iff_nat]
  rintro ⟨f, hf, -⟩
  have := (hf 0 (by simp)).1
  simp at this

/-- **The graph has a full matching exactly when a fair schedule exists.** -/
theorem yes_graphNums (I : Instance) (hu : I.UnitP) (k : ℕ) (d : ℕ → ℕ)
    (hd : ∀ (i : Fin I.days) (j : Fin I.clients), d (i * I.clients + j) = I.d i j) :
    Yes (graphNums I.clients I.days k d) ↔ I.HasKFairSchedule k := by
  rw [Bridge.hasKFairSchedule_iff]
  by_cases hk : k ≤ I.days
  · rw [Lax117284Proofs.Model.Instance.hasKFairSchedule_iff_hasFullMatching
      ((Bridge.unitP_iff I).1 hu) (by rw [Bridge.model_numDays]; exact hk), yes_iff_pair hk]
    exact ⟨fun ⟨f, hf⟩ => pair_to_paper I k d hd f hf, paper_to_pair I k d hd⟩
  · have hlt : (Bridge.model I).numDays < k := by rw [Bridge.model_numDays]; omega
    rw [Lax117284Proofs.Model.Instance.hasKFairSchedule_iff_isEmpty_client_of_lt hlt]
    have e : IsEmpty (Bridge.model I).Client ↔ I.clients = 0 :=
      (Theorem2Decide.clients_eq_zero_iff I).symm
    rw [e]
    simp only [graphNums, hk, if_false]
    by_cases hn : I.clients = 0
    · simp only [hn, if_true, iff_true]
      exact yes_zero
    · simp only [hn, if_false, iff_false]
      exact not_yes_reject

end Lax117284Proofs.UnitPGraph
