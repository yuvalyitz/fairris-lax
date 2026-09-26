import Lax117284Proofs.UnitPGraph
import Lax117284Proofs.Machine.InstSem
import Lax117284Proofs.Machine.MatchGuard
import Lax117284Proofs.WordCorrect

/-!
The reduction of the unit processing times to matching, on the numbers of a stream: the graph of
`UnitPGraph`, row by row, as the matching decider reads it.
-/

namespace Lax117284Proofs.Machine.USem

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.UnitPGraph
open Lax117284Proofs.Machine.MatchGuard
open scoped Classical

/-- The due date of the job in the cell `t` (day by day, client by client) of a stream: the
table interleaves the processing time and the due date of a job. -/
def dU (ns : List ℕ) (t : ℕ) : ℕ := ns.getD (3 + 2 * t) 0

/-- The streams that are mapped to a graph: every job has processing time one and is due at a
positive time. -/
def condU (ns : List ℕ) : Prop :=
  ∀ t < ns.getD 1 0 * ns.getD 0 0, ns.getD (2 + 2 * t) 0 = 1 ∧ 0 < ns.getD (3 + 2 * t) 0

/-- The graph of a stream, as a list of numbers. -/
def outU (ns : List ℕ) : List ℕ := graphNums (ns.getD 0 0) (ns.getD 1 0) (paramOf ns) (dU ns)

/-- The graph every other word is sent to: one left vertex, no right vertex. -/
def rejU : List ℕ := [1, 0]

/-- The row `r` of the table, as the runs the program writes: zeros up to the column of the
first client with the same due date, a one, zeros up to the rejection columns of the client
`r % n`, ones for them, zeros. -/
def rowR (n m k : ℕ) (d : ℕ → ℕ) (r : ℕ) : List ℕ :=
  List.replicate (r / n * n + repN n d (r / n) (r % n)) 0 ++ [1] ++
    List.replicate (m * n - 1 - (r / n * n + repN n d (r / n) (r % n))) 0 ++
    List.replicate (r % n * (m - k)) 0 ++ List.replicate (m - k) 1 ++
    List.replicate ((n - 1 - r % n) * (m - k)) 0

theorem map_range_add {α : Type} (f : ℕ → α) (a b : ℕ) :
    (List.range (a + b)).map f = (List.range a).map f ++ (List.range b).map (fun x => f (a + x)) := by
  rw [List.range_add, List.map_append, List.map_map]
  rfl

/-- The row, with the numbers abstracted: `P` cells of the first block, `T` the marked one, `j`
the client, `W` the rejection columns of a client, `n` the clients. -/
theorem rowR_abs (P T j W n : ℕ) (e : ℕ → ℕ)
    (he : ∀ c, e c = if c < P then (if c = T then 1 else 0)
      else if j * W ≤ c - P ∧ c - P < (j + 1) * W then 1 else 0)
    (hT : T < P) (hj : j < n) :
    List.replicate T 0 ++ [1] ++ List.replicate (P - 1 - T) 0 ++ List.replicate (j * W) 0 ++
        List.replicate W 1 ++ List.replicate ((n - 1 - j) * W) 0 =
      (List.range (P + n * W)).map e := by
  obtain ⟨s, rfl⟩ : ∃ s, P = T + 1 + s := ⟨P - 1 - T, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, n = j + 1 + q := ⟨n - 1 - j, by omega⟩
  have e1 : T + 1 + s - 1 - T = s := by omega
  have e2 : j + 1 + q - 1 - j = q := by omega
  have e3 : (j + 1 + q) * W = j * W + W + q * W := by ring
  have e4 : (j + 1) * W = j * W + W := by ring
  rw [e1, e2, e3]
  simp only [map_range_add, List.append_assoc]
  congr 1
  · symm; rw [List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    have := List.mem_range.1 hc
    rw [he, if_pos (by omega), if_neg (by omega)]
  congr 1
  · rw [List.range_one]
    show [1] = [e (T + 0)]
    rw [he, if_pos (by omega), if_pos (by omega)]
  congr 1
  · symm; rw [List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    have := List.mem_range.1 hc
    rw [he, if_pos (by omega), if_neg (by omega)]
  congr 1
  · symm; rw [List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    have := List.mem_range.1 hc
    rw [he, if_neg (by omega), if_neg (by omega)]
  congr 1
  · symm; rw [List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    have := List.mem_range.1 hc
    rw [he, if_neg (by omega), if_pos (by omega)]
  · symm; rw [List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    have := List.mem_range.1 hc
    rw [he, if_neg (by omega), if_neg (by omega)]

/-- **The runs of a row are the row of the table.** -/
theorem rowR_eq {n m k : ℕ} {d : ℕ → ℕ} (hk : k ≤ m) {r : ℕ} (hr : r < m * n) :
    rowR n m k d r = (List.range (cols n m k)).map (entry n m k d r) := by
  have _ := hk
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hr)
  have hj : r % n < n := Nat.mod_lt _ hn
  have hi : r / n < m := (Nat.div_lt_iff_lt_mul hn).2 hr
  have hT := pair_lt hi (repN_spec (d := d) (i := r / n) hj).1
  have he : ∀ c, entry n m k d r c = if c < m * n then
      (if c = r / n * n + repN n d (r / n) (r % n) then 1 else 0)
      else if r % n * (m - k) ≤ c - m * n ∧ c - m * n < (r % n + 1) * (m - k) then 1 else 0 :=
    fun c => rfl
  unfold rowR cols
  exact rowR_abs (m * n) _ (r % n) (m - k) n _ he hT hj

/-- The graph, written as its rows. -/
theorem graphNums_rows {n m k : ℕ} {d : ℕ → ℕ} (hk : k ≤ m) :
    graphNums n m k d = [m * n, cols n m k] ++ (List.range (m * n)).flatMap (rowR n m k d) := by
  unfold graphNums
  rw [if_pos hk]
  congr 1
  exact (List.flatMap_congr fun r hr => (rowR_eq hk (List.mem_range.1 hr)).symm)

theorem valid_of_condU {ns : List ℕ} (hc : condU ns) : Valid ns := fun t ht => by
  have h := hc t ht
  have e : 2 + 2 * t + 1 = 3 + 2 * t := by omega
  rw [e]
  omega

theorem unitP_of_condU (ns : List ℕ) (hv : Valid ns) (hc : condU ns) : (instOf ns hv).UnitP :=
  fun i j => (hc _ (cell_lt i.isLt j.isLt)).1

/-- **The graph of a stream has a full matching exactly when its instance has a fair schedule.** -/
theorem yes_outU (ns : List ℕ) (hv : Valid ns) (hc : condU ns) :
    Yes (outU ns) ↔ (instOf ns hv).HasKFairSchedule (paramOf ns) := by
  refine yes_graphNums (instOf ns hv) (unitP_of_condU ns hv hc) (paramOf ns) (dU ns) ?_
  intro i j
  show ns.getD (3 + 2 * (i * ns.getD 0 0 + j)) 0 = ns.getD (2 + 2 * (i * ns.getD 0 0 + j) + 1) 0
  congr 1
  omega

/-- **The reduction**, as a map from words to lists of numbers. -/
noncomputable def redU (w : Word) : List ℕ :=
  if h : ∃ ns, w = numCode ns ∧ Shape eU ns ∧ condU ns then outU h.choose else rejU

theorem redU_acc (ns : List ℕ) (hs : Shape eU ns) (hc : condU ns) : redU (numCode ns) = outU ns := by
  have h : ∃ ns', numCode ns = numCode ns' ∧ Shape eU ns' ∧ condU ns' := ⟨ns, rfl, hs, hc⟩
  unfold redU
  rw [dif_pos h]
  exact congrArg outU (numCode_inj h.choose_spec.1).symm

theorem redU_rej (w : Word) (h : ¬ ∃ ns, w = numCode ns ∧ Shape eU ns ∧ condU ns) :
    redU w = rejU := by
  unfold redU
  exact dif_neg h

theorem encode_instOf (ns : List ℕ) (hv : Valid ns) (hs : Shape eU ns) :
    encodeUniform (instOf ns hv) (paramOf ns) = numCode ns := by
  rw [encodeUniform, encodeInstance_eq]
  conv_rhs => rw [← instToks_instOf ns hv hs]
  rw [numCode_append]
  simp [numCode]

theorem pAt_eq_one {I : Instance} (hu : I.UnitP) (i j : ℕ) : I.pAt i j = 1 := by
  unfold Instance.pAt
  split_ifs
  · exact hu _ _
  all_goals rfl

/-- **The words of the instances with unit processing times are the accepted streams.** -/
theorem stream_of_unit {w : Word} {I : Instance} {k : ℕ} (hw : encodeUniform I k = w)
    (hu : I.UnitP) : ∃ ns : List ℕ, w = numCode ns ∧ Shape eU ns ∧ condU ns := by
  have hl := instToks_length I
  have h0 : (instToks I ++ [k]).getD 0 0 = I.clients := by
    rw [List.getD_append _ _ _ _ (by omega)]; exact (instToks_getD_head I).1
  have h1 : (instToks I ++ [k]).getD 1 0 = I.days := by
    rw [List.getD_append _ _ _ _ (by omega)]; exact (instToks_getD_head I).2
  refine ⟨instToks I ++ [k], ?_, ⟨by simp; omega, ?_⟩, ?_⟩
  · rw [← hw, encodeUniform, encodeInstance_eq, numCode_append]
    simp
  · rw [h0, h1]
    simp only [List.length_append, List.length_singleton, eU, hl]
  · intro t ht
    rw [h0, h1] at ht
    have ht' : t < I.days * I.clients := ht
    have hp := instToks_getD_cell I ht'
    have e : 3 + 2 * t = 2 + 2 * t + 1 := by omega
    rw [e, List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), hp.1, hp.2]
    refine ⟨pAt_eq_one hu _ _, ?_⟩
    have := I.pAt_le_dAt (t / I.clients) (t % I.clients)
    rw [pAt_eq_one hu] at this
    exact this

/-- **The reduction is correct.** -/
theorem redU_correct (w : Word) :
    w ∈ Uniform (fun I _ => I.UnitP) ↔ Yes (redU w) := by
  by_cases h : ∃ ns, w = numCode ns ∧ Shape eU ns ∧ condU ns
  · obtain ⟨ns, hw, hs, hc⟩ := h
    have hv := valid_of_condU hc
    rw [hw, redU_acc ns hs hc, ← encode_instOf ns hv hs, WordCorrect.uniform_mem_encode, yes_outU ns hv hc]
    exact ⟨fun h => h.2, fun h => ⟨unitP_of_condU ns hv hc, h⟩⟩
  · rw [redU_rej w h]
    constructor
    · rintro ⟨I, k, hw, hu, -⟩
      exact absurd (stream_of_unit hw hu) h
    · intro hy
      exact absurd hy not_yes_reject

theorem flat_len (R C : ℕ) (g : ℕ → ℕ → ℕ) :
    ((List.range R).flatMap fun r => (List.range C).map (g r)).length = R * C := by
  induction R with
  | zero => simp
  | succ R ih => simp [List.range_succ, List.flatMap_append, ih, Nat.succ_mul]

theorem graphNums_length {n m k : ℕ} {d : ℕ → ℕ} (hk : k ≤ m) :
    (graphNums n m k d).length = 2 + m * n * cols n m k := by
  unfold graphNums
  rw [if_pos hk, List.length_append, flat_len]
  rfl

theorem heavy_arith (P C : ℕ) (hP : 1 ≤ P) (hC : 1 ≤ C) :
    (P - 1) * C < 2 + P * C - 2 ∧ C ≤ 2 + P * C := by
  obtain ⟨p, rfl⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
  have h : (p + 1) * C = p * C + C := by ring
  rw [Nat.add_sub_cancel]
  omega

theorem gfun_rejU : gfun rejU = [if Yes rejU then 1 else 0] := by
  have hn : ¬ Yes rejU := not_yes_reject
  have hH : ¬ Heavy rejU := by simp [Heavy, rejU]
  unfold gfun
  rw [if_neg hH, if_neg (by simp [rejU]), if_neg hn]

theorem gfun_zero : gfun [0, 0] = [if Yes [0, 0] then 1 else 0] := by
  have hH : ¬ Heavy [0, 0] := by simp [Heavy]
  unfold gfun
  rw [if_neg hH, if_pos (by simp), if_pos yes_zero]

theorem gfun_graph_empty {n m k : ℕ} {d : ℕ → ℕ} (hk : k ≤ m) (h0 : m * n = 0) :
    gfun (graphNums n m k d) = [if Yes (graphNums n m k d) then 1 else 0] := by
  have hy : Yes (graphNums n m k d) := (yes_iff_nat _).2
    ⟨id, fun r hr => by rw [getD_zero hk] at hr; omega, fun r _ r' _ h => h⟩
  have hH : ¬ Heavy (graphNums n m k d) := fun h => by
    have := h.1
    rw [getD_zero hk] at this
    omega
  unfold gfun
  rw [if_neg hH, if_pos (by rw [getD_zero hk]; exact h0), if_pos hy]

theorem gfun_graph_heavy {n m k : ℕ} {d : ℕ → ℕ} (hk : k ≤ m) (h0 : 1 ≤ m * n) :
    gfun (graphNums n m k d) = [if Yes (graphNums n m k d) then 1 else 0] := by
  have hc : 1 ≤ cols n m k := by unfold cols; omega
  have ha := heavy_arith _ _ h0 hc
  have hH : Heavy (graphNums n m k d) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [getD_zero hk, getD_one hk, graphNums_length hk]
    · exact h0
    · exact hc
    · exact ha.1
    · exact ha.2
  unfold gfun
  rw [if_pos hH]

/-- The guarded decider on the graphs. -/
theorem gfun_graphNums (n m k : ℕ) (d : ℕ → ℕ) :
    gfun (graphNums n m k d) = [if Yes (graphNums n m k d) then 1 else 0] := by
  by_cases hk : k ≤ m
  · by_cases h0 : m * n = 0
    · exact gfun_graph_empty hk h0
    · exact gfun_graph_heavy hk (by omega)
  · unfold graphNums
    rw [if_neg hk]
    by_cases hn : n = 0
    · rw [if_pos hn]; exact gfun_zero
    · rw [if_neg hn]; exact gfun_rejU

/-- The guarded matching decider answers `1` exactly on the graphs with a full matching, on every
image of the reduction. -/
theorem gfun_redU (w : Word) : gfun (redU w) = [if Yes (redU w) then 1 else 0] := by
  by_cases h : ∃ ns, w = numCode ns ∧ Shape eU ns ∧ condU ns
  · obtain ⟨ns, hw, hs, hc⟩ := h
    rw [hw, redU_acc ns hs hc]
    exact gfun_graphNums _ _ _ _
  · rw [redU_rej w h]
    exact gfun_rejU

theorem entry_le_one (n m k : ℕ) (d : ℕ → ℕ) (r c : ℕ) : entry n m k d r c ≤ 1 := by
  unfold entry
  split_ifs <;> omega

theorem cols_le (n m k : ℕ) : cols n m k ≤ 2 * (m * n) := by
  have : n * (m - k) ≤ n * m := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  unfold cols
  rw [Nat.mul_comm n m] at this
  omega

theorem le_length_numCode (l : List ℕ) : l.length ≤ (numCode l).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have : 0 < (encodeNat a).length := by simp [encodeNat]
    simp only [numCode_cons, List.length_append, List.length_cons]
    omega

theorem mem_graphNums_le {n m k : ℕ} {d : ℕ → ℕ} (h3 : 1 ≤ 2 * (m * n) + 1)
    {v : ℕ} (hv : v ∈ graphNums n m k d) : v ≤ 2 * (m * n) + 1 := by
  unfold graphNums at hv
  split_ifs at hv with hk hn
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_flatMap,
      List.mem_map] at hv
    rcases hv with rfl | rfl | ⟨r, -, c, -, rfl⟩
    · omega
    · exact (cols_le n m k).trans (by omega)
    · exact (entry_le_one n m k d r c).trans h3
  · simp at hv
    omega
  · simp at hv
    omega

/-- The numbers of the image are small: no larger than one more than the length of the word. -/
theorem redU_lt (w : Word) : ∀ v ∈ redU w, v ≤ w.length + 1 := by
  intro v hv
  by_cases h : ∃ ns, w = numCode ns ∧ Shape eU ns ∧ condU ns
  · obtain ⟨ns, hw, hs, hc⟩ := h
    rw [hw, redU_acc ns hs hc] at hv
    have hl : ns.length = 2 * (ns.getD 1 0 * ns.getD 0 0) + 3 := by
      have := hs.2
      simp only [eU] at this
      omega
    have h1 := mem_graphNums_le (n := ns.getD 0 0) (m := ns.getD 1 0) (k := paramOf ns)
      (d := dU ns) (by omega) hv
    have h2 := le_length_numCode ns
    rw [hw]
    omega
  · rw [redU_rej w h] at hv
    simp only [rejU, List.mem_cons, List.not_mem_nil, or_false] at hv
    omega

end Lax117284Proofs.Machine.USem
