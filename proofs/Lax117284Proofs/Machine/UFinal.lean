import Lax117284Proofs.UnitPGraph
import Lax117284Proofs.Machine.InstSem
import Lax117284Proofs.Machine.MatchGuard
import Lax117284Proofs.WordCorrect
import Lax117284Proofs.Machine.UEmit
import Lax117284Proofs.Machine.ILoop
import Lax117284Proofs.Machine.Flag
import Lax117284Proofs.Machine.MisBlk
import Lax117284Proofs.Machine.FreeAccept
import Lax117284Proofs.Machine.TokRun
import Lax117284Proofs.Machine.FreeMain
import Lax117284Proofs.Machine.FreeFinal
import Lax117284Proofs.Machine.UNk

/-! ### `Lax117284Proofs.Machine.USem` -/

section
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

end

/-! ### `Lax117284Proofs.Machine.URow` -/

section
/-!
One row of the table: the scan for the first client with the same due date, and the six runs
the row is written as.
-/

namespace Lax117284Proofs.Machine.URow

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.UEmit Lax117284Proofs.UnitPGraph Lax117284Proofs.Machine.USem
open Lax117284Proofs.Machine

variable {B : ℕ}

/-- The due date of the job in the cell `t` of the token array. -/
def dA (arr : List ℕ) (t : ℕ) : ℕ := arr.getD (3 + 2 * t) 0

/-- The index in the token array of the due date of the job in the cell `v`. -/
def idxD (v : Expr) : Expr := .bin .add (.lit 3) (.bin .mul (.lit 2) v)

/-- The cell of day `i`, client `jj`. -/
def cellE (jj : String) : Expr := .bin .add (.bin .mul (.var "i") (.var "n")) (.var jj)

/-- One client of the scan: the first one with the due date of `j` is remembered. -/
def repFindBody : Com :=
  .ite (.eq (.var "fnd") (.lit 0))
    (.ite (.eq (.get "TK" (idxD (cellE "jj"))) (.var "dj"))
      (.seq (.assign "rep" (.var "jj")) (.assign "fnd" (.lit 1))) .skip)
    .skip

/-- The scan over the clients of the day. -/
def repFind : Com :=
  .seq (.assign "jj" (.lit 0))
    (.while (.lt (.var "jj") (.var "n"))
      (.seq repFindBody (.assign "jj" (.bin .add (.var "jj") (.lit 1)))))

/-- The test of the scan for the client `jj'` of day `i`. -/
def hit (arr : List ℕ) (n i j : ℕ) (jj : ℕ) : Bool :=
  decide (dA arr (i * n + jj) = dA arr (i * n + j))

theorem find_succ (p : ℕ → Bool) (k : ℕ) :
    (List.range (k + 1)).find? p = ((List.range k).find? p).or (if p k then some k else none) := by
  rw [List.range_succ, List.find?_append, List.find?_singleton]

theorem find_hit (p : ℕ → Bool) (k : ℕ) (hnone : (List.range k).find? p = none) (hp : p k = true) :
    (List.range (k + 1)).find? p = some k := by
  rw [find_succ, hnone, hp]; rfl

theorem find_miss (p : ℕ → Bool) (k : ℕ) (hnone : (List.range k).find? p = none) (hp : p k = false) :
    (List.range (k + 1)).find? p = none := by
  rw [find_succ, hnone, hp]; rfl

theorem find_keep (p : ℕ → Bool) (k : ℕ) (hsome : ((List.range k).find? p).isSome = true) :
    (List.range (k + 1)).find? p = (List.range k).find? p := by
  rw [find_succ]
  cases h : (List.range k).find? p with
  | none => rw [h] at hsome; simp at hsome
  | some v => rfl

theorem flag_none {o : Option ℕ} {f : ℕ} (h : f = if o.isSome = true then 1 else 0) (h0 : f = 0) :
    o = none := by
  cases o with
  | none => rfl
  | some v => simp at h; omega

theorem flag_some {o : Option ℕ} {f : ℕ} (h : f = if o.isSome = true then 1 else 0) (h0 : f ≠ 0) :
    o.isSome = true := by
  cases o with
  | none => simp at h; omega
  | some v => rfl

/-- The invariant of the scan after `k` clients. -/
structure FInv (arr : List ℕ) (n i j k : ℕ) (σ0 σ : Env) : Prop where
  tk : σ.arrs "TK" = arr
  vn : σ.vars "n" = n
  vi : σ.vars "i" = i
  vdj : σ.vars "dj" = dA arr (i * n + j)
  rep : σ.vars "rep" = ((List.range k).find? (hit arr n i j)).getD j
  fnd : σ.vars "fnd" = if ((List.range k).find? (hit arr n i j)).isSome then 1 else 0
  arrs : σ.arrs = σ0.arrs
  inp : σ.inp = σ0.inp
  out : σ.out = σ0.out
  fr : ∀ y, y ≠ "jj" → y ≠ "rep" → y ≠ "fnd" → σ.vars y = σ0.vars y

theorem repFindBody_spec (arr : List ℕ) (n i j m k : ℕ) (σ0 : Env)
    (hi : i < m) (hj : j < n) (hk : k < n) (hlen : 3 + 2 * (m * n) ≤ arr.length)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 < B)
    (hB : 3 + 2 * (m * n) + 8 < B) (hnB : n + 8 < B) (hcell : ∀ jj < n, i * n + jj < m * n) :
    Spec B (fun σ => FInv arr n i j k σ0 σ ∧ σ.vars "jj" = k) repFindBody
      (fun σ σ' => FInv arr n i j (k + 1) σ0 σ' ∧ σ'.vars "jj" = k) 30 := by
  rintro σ ⟨hI, hjk⟩
  obtain ⟨tk, vn, vi, vdj, hrep, hfnd, harr, hinp, hout, hfr⟩ := hI
  have hc := hcell _ hk
  have hc' : σ.vars "i" * σ.vars "n" + σ.vars "jj" < m * n := by rw [vi, vn, hjk]; exact hc
  have hin : σ.vars "i" ≤ σ.vars "i" * σ.vars "n" := by
    rw [vi, vn]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hEk := hE (3 + 2 * (i * n + k)) (by omega)
  have hbf : σ.vars "fnd" < B := by rw [hfnd]; split_ifs <;> omega
  have hbi : σ.vars "i" < B := by rw [vi]; omega
  have hbn : σ.vars "n" < B := by rw [vn]; omega
  have hbjj : σ.vars "jj" < B := by omega
  have hbdj : σ.vars "dj" < B := by
    rw [vdj]; exact hE (3 + 2 * (i * n + j)) (by have := hcell j hj; omega)
  have hbr : σ.vars "rep" < B := by
    rw [hrep]
    rcases h : (List.find? (hit arr n i j) (List.range k)) with _ | v
    · simp; omega
    · simp
      have := List.mem_range.mp (List.mem_of_find?_eq_some h)
      omega
  have hget : (σ.arrs "TK").getD (3 + 2 * (σ.vars "i" * σ.vars "n" + σ.vars "jj")) 0 =
      dA arr (i * n + k) := by
    rw [tk, vi, vn, hjk]; rfl
  have hlenTK : (σ.arrs "TK").length = arr.length := by rw [tk]
  have hgetB : (σ.arrs "TK").getD (3 + 2 * (σ.vars "i" * σ.vars "n" + σ.vars "jj")) 0 < B := by
    rw [hget]; exact hEk
  unfold repFindBody idxD cellE
  run_vcg
  all_goals (try simp only [Env.setVar] at *)
  all_goals (try omega)
  · -- the scan finds the client
    have hn0 := flag_none hfnd ‹σ.vars "fnd" = 0›
    have hh : hit arr n i j k = true := by
      unfold hit; rw [← vdj, ← hget]; simpa using ‹_ = σ.vars "dj"›
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simpa using hjk⟩
    · exact tk
    · simpa using vn
    · simpa using vi
    · simpa using vdj
    · simp [find_hit _ _ hn0 hh, hjk]
    · simp [find_hit _ _ hn0 hh]
    · exact harr
    · exact hinp
    · exact hout
    · intro y a b c
      simp [a, b, c]
      exact hfr y a b c
  · have hn0 := flag_none hfnd ‹σ.vars "fnd" = 0›
    have hh : hit arr n i j k = false := by
      unfold hit; rw [← vdj, ← hget]; simpa using ‹¬ _›
    refine ⟨⟨tk, vn, vi, vdj, ?_, ?_, harr, hinp, hout, hfr⟩, hjk⟩
    · rw [find_miss _ _ hn0 hh]; rw [hrep, hn0]
    · rw [find_miss _ _ hn0 hh]; simpa using ‹σ.vars "fnd" = 0›
  · have hs := flag_some hfnd ‹¬σ.vars "fnd" = 0›
    refine ⟨⟨tk, vn, vi, vdj, ?_, ?_, harr, hinp, hout, hfr⟩, hjk⟩
    · rw [find_keep _ _ hs]; exact hrep
    · rw [find_keep _ _ hs]; exact hfnd

theorem FInv.setJJ {arr : List ℕ} {n i j k : ℕ} {σ0 σ : Env} (h : FInv arr n i j k σ0 σ) (v : ℕ) :
    FInv arr n i j k σ0 (σ.setVar "jj" v) where
  tk := by simpa [Env.setVar] using h.tk
  vn := by simpa [Env.setVar] using h.vn
  vi := by simpa [Env.setVar] using h.vi
  vdj := by simpa [Env.setVar] using h.vdj
  rep := by simpa [Env.setVar] using h.rep
  fnd := by simpa [Env.setVar] using h.fnd
  arrs := by simpa [Env.setVar] using h.arrs
  inp := by simpa [Env.setVar] using h.inp
  out := by simpa [Env.setVar] using h.out
  fr := fun y a b c => by simp only [Env.setVar, if_neg a]; exact h.fr y a b c

theorem repFindStep_spec (arr : List ℕ) (n i j m : ℕ) (σ0 : Env)
    (hi : i < m) (hj : j < n) (hlen : 3 + 2 * (m * n) ≤ arr.length)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 < B)
    (hB : 3 + 2 * (m * n) + 8 < B) (hnB : n + 8 < B) (hcell : ∀ jj < n, i * n + jj < m * n) :
    Spec B (fun σ => (FInv arr n i j (σ.vars "jj") σ0 σ ∧ σ.vars "jj" ≤ n) ∧ σ.vars "jj" < n)
      (.seq repFindBody (.assign "jj" (.bin .add (.var "jj") (.lit 1))))
      (fun σ σ' => (FInv arr n i j (σ'.vars "jj") σ0 σ' ∧ σ'.vars "jj" ≤ n) ∧
        σ'.vars "jj" = σ.vars "jj" + 1) 34 := by
  rintro σ ⟨⟨hI, hle⟩, hlt⟩
  obtain ⟨σ1, r1, hI1, hjj1⟩ := repFindBody_spec (B := B) arr n i j m (σ.vars "jj") σ0 hi hj hlt hlen
    hE hB hnB hcell σ ⟨hI, rfl⟩
  have r2 : Run B (.assign "jj" (.bin .add (.var "jj") (.lit 1))) σ1
      (σ1.setVar "jj" (σ1.vars "jj" + 1)) (1 + (Expr.bin .add (.var "jj") (.lit 1)).size) :=
    Run.assign (evalB_bin (evalB_var (by rw [hjj1]; omega)) (evalB_lit (by omega))
      (by simp [hjj1]; omega))
  refine ⟨_, (r1.seq r2).mono (by simp [Expr.size]), ⟨?_, ?_⟩, ?_⟩
  · simpa [Env.setVar, hjj1] using hI1.setJJ (σ.vars "jj" + 1)
  · simp [Env.setVar, hjj1]; omega
  · simp [Env.setVar, hjj1]

/-- **The scan finds the first client of the day with the due date of client `j`.** -/
theorem repFind_run (arr : List ℕ) (n i j m : ℕ) (σ : Env)
    (hi : i < m) (hj : j < n) (hlen : 3 + 2 * (m * n) ≤ arr.length)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 < B)
    (hB : 3 + 2 * (m * n) + 8 < B) (hnB : n + 8 < B) (hcell : ∀ jj < n, i * n + jj < m * n)
    (h0 : FInv arr n i j 0 σ σ) :
    ∃ σ', Run B repFind σ σ' ((34 + 4) * n + 6) ∧ FInv arr n i j n σ σ' := by
  obtain ⟨σ', r, hI, hjj⟩ := (Spec.forRangeZero (B := B) (c := .seq repFindBody
      (.assign "jj" (.bin .add (.var "jj") (.lit 1)))) "jj" "n"
    (fun σ' => FInv arr n i j (σ'.vars "jj") σ σ' ∧ σ'.vars "jj" ≤ n) n 34 (by omega)
    (fun _ h => h.2) (fun _ h => h.1.vn)
    (repFindStep_spec arr n i j m σ hi hj hlen hE hB hnB hcell)) σ
    ⟨by simpa [Env.setVar] using h0.setJJ 0, by simp [Env.setVar]⟩
  exact ⟨σ', r, by rw [hjj] at hI; exact hI.1⟩

/-! ### The row -/

/-- Locate the job of the row and start the scan. -/
def locCom : Com :=
  .seq (.assign "i" (.bin .div (.var "r") (.var "n")))
  (.seq (.assign "j" (.bin .sub (.var "r") (.bin .mul (.var "i") (.var "n"))))
  (.seq (.assign "dj" (.get "TK" (idxD (cellE "j"))))
  (.seq (.assign "rep" (.var "j")) (.assign "fnd" (.lit 0)))))

/-- The lengths of the six runs. -/
def setCom : Com :=
  .seq (.assign "a1" (.bin .add (.bin .mul (.var "i") (.var "n")) (.var "rep")))
  (.seq (.assign "a2" (.bin .sub (.bin .sub (.var "N") (.lit 1)) (.var "a1")))
  (.seq (.assign "a3" (.bin .mul (.var "j") (.var "q")))
  (.seq (.assign "a4" (.var "q"))
    (.assign "a5" (.bin .mul (.bin .sub (.bin .sub (.var "n") (.lit 1)) (.var "j")) (.var "q"))))))

/-- The whole row: locate the job, find its representative, write the six runs. -/
def rowBody : Com := .seq locCom (.seq repFind (.seq setCom emit6))

/-- What a row starts in. -/
structure RCtx (arr : List ℕ) (n m kp r : ℕ) (σ : Env) : Prop where
  tk : σ.arrs "TK" = arr
  vn : σ.vars "n" = n
  vm : σ.vars "m" = m
  vN : σ.vars "N" = m * n
  vq : σ.vars "q" = m - kp
  vC : σ.vars "C" = m * n + n * (m - kp)
  vr : σ.vars "r" = r

theorem repFind_spec (arr : List ℕ) (n i j m : ℕ)
    (hi : i < m) (hj : j < n) (hlen : 3 + 2 * (m * n) ≤ arr.length)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 < B)
    (hB : 3 + 2 * (m * n) + 8 < B) (hnB : n + 8 < B) (hcell : ∀ jj < n, i * n + jj < m * n) :
    Spec B (fun σ => FInv arr n i j 0 σ σ) repFind (fun σ σ' => FInv arr n i j n σ σ')
      ((34 + 4) * n + 6) :=
  fun σ h => repFind_run arr n i j m σ hi hj hlen hE hB hnB hcell h

theorem locCom_spec (arr : List ℕ) (n m kp r : ℕ) (hr : r < m * n)
    (hlen : 3 + 2 * (m * n) ≤ arr.length)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 < B)
    (hB : 3 + 2 * (m * n) + 8 < B) (hnB : n + 8 < B) (hmB : m + 8 < B) :
    Spec B (fun σ => RCtx arr n m kp r σ) locCom
      (fun σ σ' => FInv arr n (r / n) (r % n) 0 σ' σ' ∧ RCtx arr n m kp r σ' ∧
        σ'.vars "j" = r % n ∧ σ'.out = σ.out ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp) 40 := by
  rintro σ ⟨tk, vn, vm, vN, vq, vC, vr⟩
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hr; simp at hr
    · exact h
  have hi : r / n < m := (Nat.div_lt_iff_lt_mul hn1).mpr hr
  have hdm : r / n * n + r % n = r := by
    have := Nat.div_add_mod r n
    rw [Nat.mul_comm] at this; omega
  have hin : r / n ≤ r / n * n := Nat.le_mul_of_pos_right _ hn1
  have hrB : r < B := by omega
  have hdjB : (σ.arrs "TK").getD (3 + 2 * r) 0 < B := by rw [tk]; exact hE _ (by omega)
  have hTKl : (σ.arrs "TK").length = arr.length := by rw [tk]
  have hdjB' : (σ.arrs "TK")[3 + 2 * r]?.getD 0 < B := by simpa using hdjB
  have hidx : r / n * n + (r - r / n * n) = r := by omega
  unfold locCom idxD cellE
  run_vcg
  all_goals (simp [vr, vn, hidx])
  all_goals (try omega)
  all_goals (try exact hdjB')
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [Env.setVar, tk]
  · simp [Env.setVar, vn]
  · simp [Env.setVar]
  · simp [Env.setVar, dA, hdm, tk, List.getD_eq_getElem?_getD]
  · simp [Env.setVar]; omega
  · simp [Env.setVar]
  · simp [Env.setVar, tk]
  · simp [Env.setVar, vn]
  · simp [Env.setVar, vm]
  · simp [Env.setVar, vN]
  · simp [Env.setVar, vq]
  · simp [Env.setVar, vC]
  · simp [Env.setVar, vr]
  · first | omega | (simp [Env.setVar]; omega) | simp [Env.setVar]

theorem setCom_spec (arr : List ℕ) (n m kp r I J T0 : ℕ) (hk : kp ≤ m) (hI : I < m) (hJ : J < n)
    (hT : T0 < n) (hB : 3 + 2 * (m * n) + 8 < B) (hnB : n + 8 < B) (hmB : m + 8 < B) :
    Spec B (fun σ => RCtx arr n m kp r σ ∧ σ.vars "i" = I ∧ σ.vars "j" = J ∧ σ.vars "rep" = T0)
      setCom
      (fun σ σ' => RCtx arr n m kp r σ' ∧ σ'.vars "a1" = I * n + T0 ∧
        σ'.vars "a2" = m * n - 1 - (I * n + T0) ∧ σ'.vars "a3" = J * (m - kp) ∧
        σ'.vars "a4" = m - kp ∧ σ'.vars "a5" = (n - 1 - J) * (m - kp) ∧
        σ'.out = σ.out ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp) 60 := by
  rintro σ ⟨⟨tk, vn, vm, vN, vq, vC, vr⟩, vi, vj, vrep⟩
  have hcell : I * n + T0 < m * n := InstSem.cell_lt hI hT
  have hC : n * (m - kp) ≤ m * n := by
    have := Nat.mul_le_mul_left n (Nat.sub_le m kp)
    rw [Nat.mul_comm n m] at this; exact this
  have hJq : J * (m - kp) ≤ n * (m - kp) := Nat.mul_le_mul_right _ hJ.le
  have h5q : (n - 1 - J) * (m - kp) ≤ n * (m - kp) := Nat.mul_le_mul_right _ (by omega)
  have hbi : σ.vars "i" < B := by omega
  have hbn : σ.vars "n" < B := by omega
  unfold setCom
  run_vcg
  all_goals (simp [vi, vj, vrep, vn, vN, vq, hI, hJ])
  all_goals (try omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Env.setVar, tk]
  · simp [Env.setVar, vn]
  · simp [Env.setVar, vm]
  · simp [Env.setVar, vN]
  · simp [Env.setVar, vq]
  · simp [Env.setVar, vC]
  · simp [Env.setVar, vr]

theorem RCtx.of_fr {arr : List ℕ} {n m kp r : ℕ} {σ0 σ : Env} (h : RCtx arr n m kp r σ0)
    (hk : σ.arrs "TK" = arr)
    (fr : ∀ y, y ∈ ["n", "m", "N", "q", "C", "r"] → σ.vars y = σ0.vars y) :
    RCtx arr n m kp r σ where
  tk := hk
  vn := by rw [fr "n" (by simp)]; exact h.vn
  vm := by rw [fr "m" (by simp)]; exact h.vm
  vN := by rw [fr "N" (by simp)]; exact h.vN
  vq := by rw [fr "q" (by simp)]; exact h.vq
  vC := by rw [fr "C" (by simp)]; exact h.vC
  vr := by rw [fr "r" (by simp)]; exact h.vr

theorem ctx_names : ∀ y, y ∈ ["n", "m", "N", "q", "C", "r"] →
    y ≠ "jj" ∧ y ≠ "rep" ∧ y ≠ "fnd" ∧ y ≠ "cc" ∧ y ≠ "cn" := by
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with h | h | h | h | h | h <;> subst h <;> decide

theorem rowBody_spec (arr : List ℕ) (n m kp r : ℕ) (hk : kp ≤ m) (hr : r < m * n)
    (hlen : 3 + 2 * (m * n) ≤ arr.length)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 < B)
    (hB : 3 + 2 * (m * n) + 8 < B) (hnB : n + 8 < B) (hmB : m + 8 < B) :
    Spec B (fun σ => RCtx arr n m kp r σ) rowBody
      (fun σ σ' => σ'.out = σ.out ++ rowR n m kp (dA arr) r ∧ RCtx arr n m kp r σ' ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp) (400 + 40 * n + 50 * (m * n + n * (m - kp))) := by
  intro σ hσ
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hr; simp at hr
    · exact h
  have hi : r / n < m := (Nat.div_lt_iff_lt_mul hn1).mpr hr
  have hj : r % n < n := Nat.mod_lt _ hn1
  have hcell : ∀ jj < n, r / n * n + jj < m * n := fun jj h => InstSem.cell_lt hi h
  obtain ⟨σ1, r1, hF1, hR1, hj1, ho1, ha1, hi1⟩ :=
    locCom_spec arr n m kp r hr hlen hE hB hnB hmB σ hσ
  obtain ⟨σ2, r2, hF2⟩ := repFind_spec arr n (r / n) (r % n) m hi hj hlen hE hB hnB hcell σ1 hF1
  have hR2 : RCtx arr n m kp r σ2 :=
    hR1.of_fr hF2.tk (fun y hy => by
      have h := ctx_names y hy
      exact hF2.fr y h.1 h.2.1 h.2.2.1)
  have hj2 : σ2.vars "j" = r % n := by
    rw [hF2.fr "j" (by decide) (by decide) (by decide)]; exact hj1
  have hrep := repN_spec (n := n) (d := dA arr) (i := r / n) hj
  have hrep2 : σ2.vars "rep" = repN n (dA arr) (r / n) (r % n) := hF2.rep
  obtain ⟨σ3, r3, hR3, ha1', ha2', ha3', ha4', ha5', ho3, hA3, hI3⟩ :=
    setCom_spec (B := B) arr n m kp r (r / n) (r % n) (repN n (dA arr) (r / n) (r % n)) hk hi hj
      hrep.1 hB hnB hmB σ2 ⟨hR2, hF2.vi, hj2, hrep2⟩
  have hcell2 : r / n * n + repN n (dA arr) (r / n) (r % n) < m * n := InstSem.cell_lt hi hrep.1
  have hC : n * (m - kp) ≤ m * n := by
    have := Nat.mul_le_mul_left n (Nat.sub_le m kp)
    rw [Nat.mul_comm n m] at this; exact this
  have hJq : r % n * (m - kp) ≤ n * (m - kp) := Nat.mul_le_mul_right _ hj.le
  have h5q : (n - 1 - r % n) * (m - kp) ≤ n * (m - kp) := Nat.mul_le_mul_right _ (by omega)
  have hqm : m - kp ≤ m * n := le_trans (Nat.sub_le m kp) (Nat.le_mul_of_pos_right _ hn1)
  obtain ⟨σ4, r4, ho4, hFrm⟩ := emit6_run (B := B) _ _ _ _ _ (m * n + n * (m - kp)) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) σ3 ha1' ha2' ha3' ha4' ha5'
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by omega), ?_, ?_, ?_, ?_⟩
  · rw [ho4, ho3, hF2.out, ho1]; unfold rowR; simp only [List.append_assoc]
  · exact hR3.of_fr (by rw [hFrm.1]; exact hR3.tk) (fun y hy => by
      have h := ctx_names y hy
      exact hFrm.2.2 y h.2.2.2.1 h.2.2.2.2)
  · rw [hFrm.1, hA3, hF2.arrs, ha1]
  · rw [hFrm.2.1, hI3, hF2.inp, hi1]

end Lax117284Proofs.Machine.URow

end

/-! ### `Lax117284Proofs.Machine.UAcc` -/

section
/-!
The accepting phase of the reduction of the unit processing times to matching: the check of the
table, the header of the graph, and the rows.
-/

namespace Lax117284Proofs.Machine.UAcc

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.UEmit Lax117284Proofs.Machine.URow Lax117284Proofs.Machine.USem
open Lax117284Proofs.UnitPGraph Lax117284Proofs.Machine.ILoop Lax117284Proofs.Machine.FoldLoop
open Lax117284Proofs.Machine.Flag

variable {B : ℕ}

/-- What every row shares. -/
structure Ctx0 (arr : List ℕ) (n m kp : ℕ) (σ : Env) : Prop where
  tk : σ.arrs "TK" = arr
  vn : σ.vars "n" = n
  vm : σ.vars "m" = m
  vN : σ.vars "N" = m * n
  vq : σ.vars "q" = m - kp
  vC : σ.vars "C" = m * n + n * (m - kp)

theorem rctx_toC {arr : List ℕ} {n m kp r : ℕ} {σ : Env} (h : RCtx arr n m kp r σ) :
    Ctx0 arr n m kp σ := ⟨h.tk, h.vn, h.vm, h.vN, h.vq, h.vC⟩

theorem Ctx0.toR {arr : List ℕ} {n m kp : ℕ} {σ : Env} (h : Ctx0 arr n m kp σ) {r : ℕ}
    (hr : σ.vars "r" = r) : RCtx arr n m kp r σ := ⟨h.tk, h.vn, h.vm, h.vN, h.vq, h.vC, hr⟩

theorem Ctx0.setR {arr : List ℕ} {n m kp : ℕ} {σ : Env} (h : Ctx0 arr n m kp σ) (v : ℕ) :
    Ctx0 arr n m kp (σ.setVar "r" v) :=
  ⟨by simpa [Env.setVar] using h.tk, by simpa [Env.setVar] using h.vn,
    by simpa [Env.setVar] using h.vm, by simpa [Env.setVar] using h.vN,
    by simpa [Env.setVar] using h.vq, by simpa [Env.setVar] using h.vC⟩

/-- All the rows of the table. -/
def rowsLoop : Com := fLoop "r" "N" rowBody

theorem flatMap_range_succ (f : ℕ → List ℕ) (j : ℕ) :
    (List.range (j + 1)).flatMap f = (List.range j).flatMap f ++ f j := by
  simp [List.range_succ, List.flatMap_append]

/-- **The rows are written.** -/
theorem rowsLoop_run (arr : List ℕ) (n m kp : ℕ) (hk : kp ≤ m) (σ : Env)
    (hlen : 3 + 2 * (m * n) ≤ arr.length)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 < B)
    (hB : 3 + 2 * (m * n) + 8 < B) (hnB : n + 8 < B) (hmB : m + 8 < B)
    (hC : Ctx0 arr n m kp σ) :
    ∃ σ', Run B rowsLoop σ σ' ((400 + 40 * n + 50 * (m * n + n * (m - kp)) + 10 + 4) * (m * n) + 6) ∧
      σ'.out = σ.out ++ (List.range (m * n)).flatMap (rowR n m kp (dA arr)) ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp := by
  obtain ⟨σ', r, hQ⟩ := iLoop_spec (B := B) "r" "N" rowBody
    (fun j σ' => Ctx0 arr n m kp σ' ∧
      σ'.out = σ.out ++ (List.range j).flatMap (rowR n m kp (dA arr)) ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp)
    (400 + 40 * n + 50 * (m * n + n * (m - kp))) (m * n) σ hC.vN
    (fun j σ' h => h.1.vN) (by decide) (by omega)
    ⟨hC.setR 0, by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar]⟩
    (fun j σ' v h => ⟨h.1.setR v, by simpa [Env.setVar] using h.2.1,
      by simpa [Env.setVar] using h.2.2.1, by simpa [Env.setVar] using h.2.2.2⟩)
    (fun j σ' h hj hlt => by
      obtain ⟨σ'', r', ho, hR, ha, hi⟩ := rowBody_spec (B := B) arr n m kp j hk hlt hlen hE hB
        hnB hmB σ' (h.1.toR hj)
      refine ⟨σ'', r', ⟨rctx_toC hR, ?_, ?_, ?_⟩, hR.vr⟩
      · rw [ho, h.2.1, flatMap_range_succ, List.append_assoc]
      · rw [ha, h.2.2.1]
      · rw [hi, h.2.2.2])
  exact ⟨σ', r, hQ.2.1, hQ.2.2.1, hQ.2.2.2⟩

/-! ### The check of the table -/

/-- The job of the cell `t` has processing time one and a positive due date. -/
def PassU (arr : List ℕ) (t : ℕ) : Prop :=
  arr.getD (2 + 2 * t) 0 = 1 ∧ 0 < arr.getD (3 + 2 * t) 0

open Classical in
noncomputable instance (arr : List ℕ) : DecidablePred (PassU arr) := fun _ => Classical.propDecidable _

/-- The test of the cell `i`. -/
def okChkU : Com :=
  .seq (.assign "p" (.get "TK" (.bin .add (.lit 2) (.bin .mul (.lit 2) (.var "i")))))
    (.seq (.assign "d" (.get "TK" (.bin .add (.lit 3) (.bin .mul (.lit 2) (.var "i")))))
      (.ite (.eq (.var "p") (.lit 1))
        (.ite (.lt (.lit 0) (.var "d")) .skip (.assign "ok" (.lit 0)))
        (.assign "ok" (.lit 0))))

def okBodyU : Com := .seq okChkU (.assign "i" (.bin .add (.var "i") (.lit 1)))

def okLoopU : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") (.var "N")) okBodyU)

/-- The invariant of the pass over the table. -/
structure OkInvU (arr : List ℕ) (N ok0 : ℕ) (σ0 σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  inp : σ.inp = σ0.inp
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vN : σ.vars "N" = N
  hi : σ.vars "i" ≤ N
  hok : σ.vars "ok" = flagTo (PassU arr) ok0 (σ.vars "i")
  fr : ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → y ≠ "d" → σ.vars y = σ0.vars y

lemma flag_failU (arr : List ℕ) (ok0 i : ℕ) (h : ¬ PassU arr i) :
    flagTo (PassU arr) ok0 (i + 1) = 0 := by
  rw [flagTo_succ]; simp [h]

lemma flag_passU (arr : List ℕ) (ok0 i : ℕ) (h : PassU arr i) (hok : ok0 ≤ 1) :
    flagTo (PassU arr) ok0 (i + 1) = flagTo (PassU arr) ok0 i := by
  rw [flagTo_succ]
  have := flagTo_le (PassU arr) ok0 i
  by_cases h1 : flagTo (PassU arr) ok0 i = 1
  · simp [h1, h]
  · have : flagTo (PassU arr) ok0 i = 0 := by omega
    simp [this]

theorem okBodyU_spec (arr : List ℕ) (N ok0 : ℕ) (σ0 : Env)
    (hE : ∀ k < 3 + 2 * N, arr.getD k 0 + 8 < B) (hL : 3 + 2 * N + 8 < B)
    (hN : 3 + 2 * N ≤ arr.length) (hNB : N + 8 < B) (hok0 : ok0 ≤ 1) :
    Spec B (fun σ => OkInvU arr N ok0 σ0 σ ∧ σ.vars "i" < N) okBodyU
      (fun σ σ' => OkInvU arr N ok0 σ0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  unfold okBodyU okChkU
  run_vcg
  all_goals (
    have hI := ‹OkInvU arr N ok0 σ0 σ›
    have hlt := ‹σ.vars "i" < N›
    have hsa := hI.arrs
    have hsi := hI.inp
    have hso := hI.out
    have hA0 := hI.hA
    have hNv := hI.vN
    have hi := hI.hi
    have hok := hI.hok
    have hfr := hI.fr
    clear hI
    have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
    have h1 := hE (2 + 2 * σ.vars "i") (by omega)
    have h2 := hE (3 + 2 * σ.vars "i") (by omega)
    subst hA
    try simp only [Env.setVar] at *
    try simp at *)
  all_goals try omega
  all_goals (refine ⟨hsa, hsi, hso, hA0, ?_, ?_, ?_, fun y a b c d => ?_⟩)
  · simp [hNv]
  · simp; omega
  · simp
    rw [flag_passU _ ok0 _ (by simp [PassU, List.getD_eq_getElem?_getD]; omega) hok0, hok]
  · simp [a, b, c, d]; exact hfr y a b c d
  · simp [hNv]
  · simp; omega
  · simp
    exact (flag_failU _ ok0 _ (by simp [PassU, List.getD_eq_getElem?_getD]; omega)).symm
  · simp [a, b, c, d]; exact hfr y a b c d
  · simp [hNv]
  · simp; omega
  · simp
    exact (flag_failU _ ok0 _ (by simp [PassU, List.getD_eq_getElem?_getD]; omega)).symm
  · simp [a, b, c, d]; exact hfr y a b c d

theorem okLoopU_run (arr : List ℕ) (N ok0 : ℕ) (σ : Env)
    (hE : ∀ k < 3 + 2 * N, arr.getD k 0 + 8 < B) (hL : 3 + 2 * N + 8 < B)
    (hN : 3 + 2 * N ≤ arr.length) (hNB : N + 8 < B) (hok0 : ok0 ≤ 1)
    (hA : σ.arrs "TK" = arr) (hNv : σ.vars "N" = N) (hok : σ.vars "ok" = ok0) :
    ∃ σ', Run B okLoopU σ σ' ((40 + 4) * N + 6) ∧ σ'.vars "ok" = flagTo (PassU arr) ok0 N ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
      ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → y ≠ "d" → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := okBodyU) "i" "N"
    (OkInvU arr N ok0 σ) N 40 (by omega) (fun _ h => h.hi) (fun _ h => h.vN)
    (okBodyU_spec arr N ok0 σ hE hL hN hNB hok0)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar], hA, hNv,
      by simp [Env.setVar], by
        simp only [Env.setVar]
        simp [flagTo_zero (PassU arr) ok0 hok0, hok], fun y a b c d => by
      simp [Env.setVar, b]⟩
  refine ⟨σ', r, ?_, hI.arrs, hI.out, hI.inp, ?_⟩
  · rw [hI.hok, hi]
  · intro y a b c d
    rw [hI.fr y a b c d]

/-! ### The header -/

/-- Read the counts, the size of the table and the parameter. -/
def prepU : Com :=
  .seq (.assign "n" (.get "TK" (.lit 0)))
  (.seq (.assign "m" (.get "TK" (.lit 1)))
  (.seq (.assign "N" (.bin .mul (.var "m") (.var "n")))
  (.seq (.assign "kp" (.get "TK" (.bin .add (.lit 2) (.bin .mul (.lit 2) (.var "N")))))
    (.assign "ok" (.lit 1)))))

theorem prepU_spec (arr : List ℕ) (hlen : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) ≤ arr.length)
    (hE : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), arr.getD k 0 + 8 < B)
    (hB : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B) :
    Spec B (fun σ => σ.arrs "TK" = arr) prepU
      (fun σ σ' => σ'.vars "n" = arr.getD 0 0 ∧ σ'.vars "m" = arr.getD 1 0 ∧
        σ'.vars "N" = arr.getD 1 0 * arr.getD 0 0 ∧
        σ'.vars "kp" = arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 ∧ σ'.vars "ok" = 1 ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
        ∀ y, y ≠ "n" → y ≠ "m" → y ≠ "N" → y ≠ "kp" → y ≠ "ok" → σ'.vars y = σ.vars y) 60 := by
  intro σ hA
  have h0 := hE 0 (by omega)
  have h1 := hE 1 (by omega)
  have h2 := hE (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) (by omega)
  have hTKl : (σ.arrs "TK").length = arr.length := by rw [hA]
  simp only [List.getD_eq_getElem?_getD] at h0 h1 h2 hlen hB
  unfold prepU
  run_vcg
  all_goals (try simp [hA])
  all_goals (try omega)
  intro y a b c d e
  simp [a, b, c, d, e]

/-! ### The graph -/

/-- The header of the graph and the rows. -/
def mainU : Com :=
  .seq (.write (.var "N"))
  (.seq (.assign "q" (.bin .sub (.var "m") (.var "kp")))
  (.seq (.assign "C" (.bin .add (.var "N") (.bin .mul (.var "n") (.var "q"))))
  (.seq (.write (.var "C")) rowsLoop)))

/-- The cost of the rows. -/
def Kmain (n m kp : ℕ) : ℕ :=
  (400 + 40 * n + 50 * (m * n + n * (m - kp)) + 10 + 4) * (m * n) + 6

theorem rowsLoop_spec (arr : List ℕ) (n m kp : ℕ) (hk : kp ≤ m)
    (hlen : 3 + 2 * (m * n) ≤ arr.length)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 < B)
    (hB : 3 + 2 * (m * n) + 8 < B) (hnB : n + 8 < B) (hmB : m + 8 < B) :
    Spec B (fun σ => Ctx0 arr n m kp σ) rowsLoop
      (fun σ σ' => σ'.out = σ.out ++ (List.range (m * n)).flatMap (rowR n m kp (dA arr)) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp) (Kmain n m kp) := by
  intro σ hC
  obtain ⟨σ', r, h⟩ := rowsLoop_run arr n m kp hk σ hlen hE hB hnB hmB hC
  exact ⟨σ', r, h⟩

theorem mainU_spec (arr : List ℕ) (n m kp : ℕ) (hk : kp ≤ m)
    (hlen : 3 + 2 * (m * n) ≤ arr.length)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 < B)
    (hB : 3 + 2 * (m * n) + 8 < B) (hnB : n + 8 < B) (hmB : m + 8 < B) :
    Spec B (fun σ => σ.arrs "TK" = arr ∧ σ.vars "n" = n ∧ σ.vars "m" = m ∧ σ.vars "N" = m * n ∧
        σ.vars "kp" = kp) mainU
      (fun σ σ' => σ'.out = σ.out ++ ([m * n, cols n m kp] ++
        (List.range (m * n)).flatMap (rowR n m kp (dA arr))) ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp) (14 + Kmain n m kp) := by
  rintro σ ⟨tk, vn, vm, vN, vkp⟩
  have hC : n * (m - kp) ≤ m * n := by
    have := Nat.mul_le_mul_left n (Nat.sub_le m kp)
    rw [Nat.mul_comm n m] at this; exact this
  unfold mainU
  run_vcg [rowsLoop_spec (B := B) arr n m kp hk hlen hE hB hnB hmB]
  all_goals first
    | (simp [Env.setVar, vn, vm, vN, vkp]; omega)
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Env.setVar, tk, vn, vm, vN, vkp]; done)
    | (obtain ⟨ho, ha, hi⟩ := ‹_ ∧ _ ∧ _›
       refine ⟨?_, ?_, ?_⟩
       · rw [ho]; simp [Env.setVar, vN, vn, vm, vkp, cols]
       · rw [ha]; simp [Env.setVar]
       · rw [hi]; simp [Env.setVar])

/-! ### The whole phase -/

/-- Write the graph without a full matching. -/
def rejCom : Com := .seq (.write (.lit 1)) (.write (.lit 0))

/-- The parameter is above the number of days: the empty graph if there is no client, the graph
of one left vertex and no right vertex if there is one. -/
def kBigCom : Com :=
  .ite (.eq (.var "n") (.lit 0)) (.seq (.write (.lit 0)) (.write (.lit 0))) rejCom

/-- **The accepting phase**: check the table, then write the graph. -/
def accU : Com :=
  .seq prepU (.seq okLoopU (.ite (.eq (.var "ok") (.lit 1))
    (.ite (.lt (.var "m") (.var "kp")) kBigCom mainU) rejCom))

theorem write_lit_run {σ : Env} (v : ℕ) (hv : v < B) :
    Run B (.write (.lit v)) σ { σ with out := σ.out ++ [v] } 2 :=
  (Run.write (evalB_lit hv)).mono (by simp [Expr.size])

theorem rejCom_run (σ : Env) (hB : 2 < B) :
    ∃ σ', Run B rejCom σ σ' 4 ∧ σ'.out = σ.out ++ rejU := by
  refine ⟨_, (write_lit_run (σ := σ) 1 (by omega)).seq (write_lit_run 0 (by omega)), ?_⟩
  simp [rejU]

theorem kBigCom_run (σ : Env) (hB : 2 < B) (hn : σ.vars "n" < B) :
    ∃ σ', Run B kBigCom σ σ' 8 ∧
      σ'.out = σ.out ++ (if σ.vars "n" = 0 then [0, 0] else [1, 0]) := by
  by_cases h : σ.vars "n" = 0
  · have hc : (Cond.eq (.var "n") (.lit 0)).evalB B σ = some true :=
      Lax117284Proofs.Machine.MisBlk.condEq_true _ _ σ (by simpa using hn) (by simp; omega)
        (by simp [h])
    refine ⟨_, ((Run.ite_true hc ((write_lit_run (σ := σ) 0 (by omega)).seq
      (write_lit_run 0 (by omega)))).mono (by simp [Cond.size, Expr.size])), ?_⟩
    simp [h]
  · have hc : (Cond.eq (.var "n") (.lit 0)).evalB B σ = some false :=
      Lax117284Proofs.Machine.MisBlk.condEq_false _ _ σ (by simpa using hn) (by simp; omega)
        (by simp [h])
    obtain ⟨σ', r, ho⟩ := rejCom_run σ hB
    refine ⟨σ', (Run.ite_false hc r).mono (by simp [Cond.size, Expr.size]), ?_⟩
    simp [h, ho, rejU]

theorem Kmain_le (n m kp : ℕ) :
    Kmain n m kp ≤ 414 * (m * n) + 140 * (m * n) * (m * n) + 6 := by
  unfold Kmain
  rcases Nat.eq_zero_or_pos (m * n) with h | h
  · rw [h]; simp
  · have hn : n ≤ m * n := by
      have : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0] at h; simp at h
        · exact h0
      exact Nat.le_mul_of_pos_left n this
    have hC : n * (m - kp) ≤ m * n := by
      have := Nat.mul_le_mul_left n (Nat.sub_le m kp)
      rw [Nat.mul_comm n m] at this; exact this
    have : (400 + 40 * n + 50 * (m * n + n * (m - kp)) + 10 + 4) * (m * n) ≤
        (414 + 40 * (m * n) + 100 * (m * n)) * (m * n) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith

theorem accU_run (arr : List ℕ) (n m kp : ℕ) (hn : arr.getD 0 0 = n) (hm : arr.getD 1 0 = m)
    (hkp : arr.getD (2 + 2 * (m * n)) 0 = kp) (σ : Env) (hA : σ.arrs "TK" = arr)
    (hlen : 3 + 2 * (m * n) ≤ arr.length)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 + 8 < B) (hB : 3 + 2 * (m * n) + 8 < B) :
    ∃ σ', Run B accU σ σ' (200 + 460 * (m * n) + 140 * (m * n) * (m * n)) ∧
      σ'.out = σ.out ++
        (if (∀ t < m * n, PassU arr t) then graphNums n m kp (dA arr) else rejU) := by
  subst hn; subst hm
  have hnB : arr.getD 0 0 + 8 < B := hE 0 (by omega)
  have hmB : arr.getD 1 0 + 8 < B := hE 1 (by omega)
  have hKm := Kmain_le (arr.getD 0 0) (arr.getD 1 0) kp
  obtain ⟨σ1, r1, e1n, e1m, e1N, e1kp, e1ok, e1a, e1o, e1i, e1f⟩ :=
    (prepU_spec (B := B) arr hlen hE hB) σ hA
  obtain ⟨σ2, r2, e2ok, e2a, e2o, e2i, e2f⟩ := okLoopU_run (B := B) arr
    (arr.getD 1 0 * arr.getD 0 0) 1 σ1 hE (by omega) hlen (by omega) le_rfl
    (by rw [e1a]; exact hA) e1N e1ok
  have hA2 : σ2.arrs "TK" = arr := by rw [e2a, e1a]; exact hA
  have hn2 : σ2.vars "n" = arr.getD 0 0 := by
    rw [e2f "n" (by decide) (by decide) (by decide) (by decide)]; exact e1n
  have hm2 : σ2.vars "m" = arr.getD 1 0 := by
    rw [e2f "m" (by decide) (by decide) (by decide) (by decide)]; exact e1m
  have hN2 : σ2.vars "N" = arr.getD 1 0 * arr.getD 0 0 := by
    rw [e2f "N" (by decide) (by decide) (by decide) (by decide)]; exact e1N
  have hkp2 : σ2.vars "kp" = kp := by
    rw [e2f "kp" (by decide) (by decide) (by decide) (by decide), e1kp]; exact hkp
  have hflag := flagTo_eq_one (P := PassU arr) (okin := 1) (k := arr.getD 1 0 * arr.getD 0 0)
  have hokB : σ2.vars "ok" < B := by
    rw [e2ok]; have := flagTo_le (PassU arr) 1 (arr.getD 1 0 * arr.getD 0 0); omega
  have hkpB : kp < B := by
    rw [← hkp]; have := hE (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) (by omega); omega
  by_cases hpass : ∀ t < arr.getD 1 0 * arr.getD 0 0, PassU arr t
  · have hok1 : σ2.vars "ok" = 1 := by rw [e2ok]; exact hflag.2 ⟨rfl, hpass⟩
    have hcT : (Cond.eq (.var "ok") (.lit 1)).evalB B σ2 = some true :=
      Lax117284Proofs.Machine.MisBlk.condEq_true _ _ σ2 (by simpa using hokB) (by simp; omega)
        (by simp [hok1])
    by_cases hbig : arr.getD 1 0 < kp
    · have hcb : (Cond.lt (.var "m") (.var "kp")).evalB B σ2 = some true :=
        Lax117284Proofs.Machine.MisBlk.condLt_true _ _ σ2 (by simp; omega) (by simp; omega)
          (by simp only [Lax117284Proofs.Machine.MisBlk.den_var, hm2, hkp2]; exact hbig)
      obtain ⟨σ3, r3, o3⟩ := kBigCom_run (B := B) σ2 (by omega) (by omega)
      have hr : Run B accU σ σ3 (60 + ((40 + 4) * (arr.getD 1 0 * arr.getD 0 0) + 6 +
          (1 + (Cond.eq (.var "ok") (.lit 1)).size +
            (1 + (Cond.lt (.var "m") (.var "kp")).size + 8)))) :=
        r1.seq (r2.seq (Run.ite_true hcT (Run.ite_true hcb r3)))
      refine ⟨σ3, hr.mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      rw [o3, e2o, e1o, if_pos hpass, hn2]
      unfold graphNums
      rw [if_neg (show ¬ kp ≤ arr.getD 1 0 by omega)]
    · have hcb : (Cond.lt (.var "m") (.var "kp")).evalB B σ2 = some false :=
        Lax117284Proofs.Machine.MisBlk.condLt_false _ _ σ2 (by simp; omega) (by simp; omega)
          (by simp only [Lax117284Proofs.Machine.MisBlk.den_var, hm2, hkp2]; omega)
      obtain ⟨σ3, r3, o3, -, -⟩ := mainU_spec (B := B) arr (arr.getD 0 0) (arr.getD 1 0) kp
        (by omega) hlen (fun k hk => by have := hE k hk; omega) hB hnB hmB σ2
        ⟨hA2, hn2, hm2, hN2, hkp2⟩
      have hr : Run B accU σ σ3 (60 + ((40 + 4) * (arr.getD 1 0 * arr.getD 0 0) + 6 +
          (1 + (Cond.eq (.var "ok") (.lit 1)).size +
            (1 + (Cond.lt (.var "m") (.var "kp")).size + (14 + Kmain (arr.getD 0 0)
              (arr.getD 1 0) kp))))) :=
        r1.seq (r2.seq (Run.ite_true hcT (Run.ite_false hcb r3)))
      refine ⟨σ3, hr.mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      rw [o3, e2o, e1o, if_pos hpass, graphNums_rows (show kp ≤ arr.getD 1 0 by omega)]
  · have hok0 : σ2.vars "ok" = 0 := by
      have h1 := flagTo_le (PassU arr) 1 (arr.getD 1 0 * arr.getD 0 0)
      have h2 : ¬ flagTo (PassU arr) 1 (arr.getD 1 0 * arr.getD 0 0) = 1 := fun h =>
        hpass (hflag.1 h).2
      rw [e2ok]; omega
    have hcF : (Cond.eq (.var "ok") (.lit 1)).evalB B σ2 = some false :=
      Lax117284Proofs.Machine.MisBlk.condEq_false _ _ σ2 (by simpa using hokB) (by simp; omega)
        (by simp [hok0])
    obtain ⟨σ3, r3, o3⟩ := rejCom_run (B := B) σ2 (by omega)
    have hr : Run B accU σ σ3 (60 + ((40 + 4) * (arr.getD 1 0 * arr.getD 0 0) + 6 +
        (1 + (Cond.eq (.var "ok") (.lit 1)).size + 4))) :=
      r1.seq (r2.seq (Run.ite_false hcF r3))
    refine ⟨σ3, hr.mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
    rw [o3, e2o, e1o, if_neg hpass]

end Lax117284Proofs.Machine.UAcc

end

/-! ### `Lax117284Proofs.Machine.UCongr` -/

section
/-!
The graph depends on the due dates of the jobs of the table only.
-/

namespace Lax117284Proofs.Machine.UCongr

open Lax117284Proofs.UnitPGraph

theorem find_congr (p q : ℕ → Bool) (l : List ℕ) (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      have ha := h a (by simp)
      have ht : t.find? p = t.find? q := ih (fun x hx => h x (by simp [hx]))
      simp [List.find?_cons, ha, ht]

theorem repN_congr {n : ℕ} {d d' : ℕ → ℕ} {i j : ℕ}
    (h : ∀ jj < n, d (i * n + jj) = d' (i * n + jj)) (hj : j < n) :
    repN n d i j = repN n d' i j := by
  unfold repN
  rw [find_congr _ (fun j' => decide (d' (i * n + j') = d' (i * n + j))) _ (fun x hx => by
    have hx' := List.mem_range.mp hx
    simp [h x hx', h j hj])]

theorem entry_congr {n m k : ℕ} {d d' : ℕ → ℕ} (h : ∀ t < m * n, d t = d' t) {r : ℕ}
    (hr : r < m * n) (c : ℕ) : entry n m k d r c = entry n m k d' r c := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at hr; simp at hr
    · exact h0
  have hi : r / n < m := (Nat.div_lt_iff_lt_mul hn).mpr hr
  have hj : r % n < n := Nat.mod_lt _ hn
  have hrep : repN n d (r / n) (r % n) = repN n d' (r / n) (r % n) :=
    repN_congr (fun jj hjj => h _ (InstSem.cell_lt hi hjj)) hj
  unfold entry
  rw [hrep]

theorem graphNums_congr {n m k : ℕ} {d d' : ℕ → ℕ} (h : ∀ t < m * n, d t = d' t) :
    graphNums n m k d = graphNums n m k d' := by
  unfold graphNums
  split_ifs with hk
  · congr 1
    refine List.flatMap_congr fun r hr => ?_
    exact List.map_congr_left fun c _ => entry_congr h (List.mem_range.mp hr) c
  · rfl
  · rfl

end Lax117284Proofs.Machine.UCongr

end

/-! ### `Lax117284Proofs.Machine.WrapN` -/

section
/-!
A reduction from the numbers of its input to a list of numbers, once and for all: the program reads the word, tokenizes it
against a format of numbers, and then either runs the phase that writes the image or writes the
rejected list. What differs from one reduction to the next is the format, the phase and the
semantics of the image, and they are the fields of the structure.
-/

namespace Lax117284Proofs.Machine.WrapNum

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime Lax117284Proofs.Codes
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan Lax117284Proofs.Machine.TokProg
open Lax117284Proofs.Machine.TokLoop Lax117284Proofs.Machine.TokBound Lax117284Proofs.Machine.TokRun
open Lax117284Proofs.Machine.FreeAccept

open scoped Classical

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- **A reduction that reads numbers and writes numbers.** -/
structure WrapN where
  /-- The format of the numbers the word is a stream of. -/
  E : Format
  /-- The streams of the format. -/
  Sh : List ℕ → Prop
  /-- What the format expects next, as a command. -/
  nk : Com
  Knk : ℕ
  hnk : ∀ (B Bt cap : ℕ), 2 * (Bt * Bt) + 2 * Bt + cap + 16 < B → NkSpec B Bt E cap nk Knk
  hconf : ∀ ns, Sh ns → Conforms E (ns.map Tok.num)
  hshape : ∀ ts, Conforms E ts → ∃ ns, ts = ns.map Tok.num ∧ Sh ns
  /-- The reduction, as a map from words to lists of numbers. -/
  red : Word → List ℕ
  /-- The streams that are mapped to an image. -/
  cond : List ℕ → Prop
  /-- The image, as a list of numbers. -/
  outN : List ℕ → List ℕ
  sem_acc : ∀ ns, Sh ns → cond ns → red (numCode ns) = outN ns
  /-- The list every other word is sent to. -/
  rejN : List ℕ
  sem_rej : ∀ w, ¬ (∃ ns, w = numCode ns ∧ Sh ns ∧ cond ns) → red w = rejN
  /-- The command that writes it. -/
  rej : Com
  Krej : ℕ → ℕ
  rejRun : ∀ (B Sz : ℕ) (σ : Env), (∀ v, v + 4 < B → v.size ≤ Sz) → 6 < B →
    ∃ σ', Run B rej σ σ' (Krej Sz) ∧ σ'.out = σ.out ++ rejN
  /-- The phase that runs once the tokenizer has accepted. -/
  acc : Com
  Kacc : ℕ → ℕ → ℕ
  Kmono : ∀ Sz a b, a ≤ b → Kacc Sz a ≤ Kacc Sz b
  accRun : ∀ (B Sz L : ℕ) (ns arr : List ℕ) (σ : Env), Sh ns → arr.take ns.length = ns →
    σ.arrs "TK" = arr → ns.length ≤ L → (∀ v ∈ ns, v < 2 ^ (L + 1)) →
    2 ^ (2 * L + 4) + 8 * L + 64 ≤ B → (∀ v, v + 4 < B → v.size ≤ Sz) →
    ∃ σ', Run B acc σ σ' (Kacc Sz ns.length) ∧
      σ'.out = σ.out ++ (if cond ns then outN ns else rejN)

variable (W : WrapN)

/-- The reduction: read the word, tokenize it against the format, and then either write the
output or the rejected word. -/
def WrapN.mainW : Com :=
  .seq ReadAll.readAll (.seq (tokRun "a" "L" W.nk)
    (.ite (.eq (.var "ph") (.lit 0))
      (.ite (.eq (.var "L") (.lit 0))
        (.ite (.eq (.var "kind") (.lit 2)) W.acc W.rej) W.rej) W.rej))

/-- The cost of the whole program on an input of length `l` at word size `Sz`. -/
def WrapN.Kmain (l Sz : ℕ) : ℕ :=
  (12 * l + 10) + (20 + W.Knk + ((100 + W.Knk + 4) * l + 6)) + 20 + W.Kacc Sz l + W.Krej Sz

/-- What the reduction computes, on the zeros and ones of its input. -/
noncomputable def WrapN.redBits (y : List ℕ) : List ℕ := W.red (bitsOf y)

lemma code_map_num' (ns : List ℕ) : code (ns.map Tok.num) = numCode ns :=
  Lax117284Proofs.Machine.FreeMain.code_map_num ns

/-- **A word the tokenizer accepts is the numbers of a stream of the format.** -/
theorem WrapN.accepted_stream (y : List ℕ) (hacc : Accepts W.E (run W.E init (bitsOf y))) :
    ∃ ns : List ℕ, bitsOf y = numCode ns ∧ W.Sh ns ∧
      (run W.E init (bitsOf y)).toks = ns.map Tok.num := by
  obtain ⟨hcode, hconf⟩ := accept_sound W.E hacc
  obtain ⟨ns, hns, hsh⟩ := W.hshape _ hconf
  refine ⟨ns, ?_, hsh, hns⟩
  rw [← hcode, hns, code_map_num']

theorem WrapN.bits_accept (y : List ℕ) (ns : List ℕ) (hw : bitsOf y = numCode ns) (hsh : W.Sh ns) :
    W.redBits y = if W.cond ns then W.outN ns else W.rejN := by
  unfold WrapN.redBits
  rw [hw]
  by_cases hc : W.cond ns
  · rw [if_pos hc, W.sem_acc ns hsh hc]
  · rw [if_neg hc, W.sem_rej]
    rintro ⟨ns', hw', hs', hc'⟩
    have hnn : ns' = ns := (numCode_inj hw').symm
    subst hnn
    exact hc hc'

theorem WrapN.bits_reject (y : List ℕ) (hn : ¬ Accepts W.E (run W.E init (bitsOf y))) :
    W.redBits y = W.rejN := by
  unfold WrapN.redBits
  rw [W.sem_rej]
  rintro ⟨ns', hw', hs', -⟩
  apply hn
  have := (accept_complete W.E (ns'.map Tok.num) (W.hconf ns' hs')).1
  rwa [code_map_num', ← hw'] at this

lemma warrs_readAll : ReadAll.readAll.warrs = ["a"] := by
  simp [ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, Com.warrs]

variable {W} {B : ℕ} (y : List ℕ)

theorem mainW_spec (hyB : ∀ v ∈ y, v < B)
    (hB : 2 ^ (2 * y.length + 4) + 8 * y.length + 64 ≤ B) :
    ∃ σ', Run B W.mainW (initEnv (fun _ => y.length) (y.length :: y)) σ'
        (W.Kmain y.length B.size) ∧ σ'.out = W.redBits y := by
  have hpow : y.length < 2 ^ y.length := Nat.lt_two_pow_self
  have hpow1 : (2 : ℕ) ^ (y.length + 1) = 2 * 2 ^ y.length := by ring
  have hpow2 : (2 : ℕ) ^ (2 * y.length + 4) = 16 * (2 ^ y.length * 2 ^ y.length) := by ring
  have hPP : 2 ^ y.length ≤ 2 ^ y.length * 2 ^ y.length :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have hs : ∀ v, v + 4 < B → v.size ≤ B.size := fun v hv => Nat.size_le_size (by omega)
  set σ0 := initEnv (fun _ => y.length) (y.length :: y) with hσ0
  -- read the word
  obtain ⟨σ1, r1, ⟨hL1, ha1, ho1, -⟩, fv1, fa1, -, -⟩ :=
    (ReadAll.readAll_spec (B := B) (y := y) hyB (by omega)).frame σ0
      ⟨rfl, rfl, by simp [hσ0, initEnv]⟩
  have tk1 : σ1.arrs "TK" = List.replicate y.length 0 := by
    rw [fa1 "TK" (by simp [warrs_readAll])]; rfl
  -- tokenize
  have hnk : NkSpec B (2 ^ y.length) W.E y.length W.nk W.Knk :=
    W.hnk B _ _ (by nlinarith)
  obtain ⟨σ2, r2, hR, ho2, hlen2⟩ := (tokRun_spec (B := B) "a" "L" W.nk (by decide) y y.length
    (le_refl _) hnk (by omega) hyB) σ1 ⟨by rw [ha1, List.take_length], hL1, by rw [tk1]; simp, ho1⟩
  set st := run W.E init (bitsOf y) with hst
  have hbd : Bd st y.length := by
    have h := bd_stAt W.E y y.length (le_refl _)
    have e : stAt W.E y y.length = st := by unfold stAt; rw [List.take_length]
    rwa [e] at h
  have hkB : σ2.vars "kind" < B := by
    rw [hR.kind]; cases W.E st.toks <;> simp [kcode] <;> omega
  have hphB : σ2.vars "ph" < B := by rw [hR.ph]; have := hbd.ph; omega
  have hLB : σ2.vars "L" < B := by rw [hR.L]; have := hbd.L; omega
  by_cases hacc : Accepts W.E st
  · obtain ⟨h0, hL0, hk⟩ := hacc
    have hph : σ2.vars "ph" = 0 := by rw [hR.ph]; exact h0
    have hLv : σ2.vars "L" = 0 := by rw [hR.L]; exact hL0
    have hkind : σ2.vars "kind" = 2 := by rw [hR.kind, hk]; rfl
    obtain ⟨ns, hw, hsh, hns⟩ := W.accepted_stream y ⟨h0, hL0, hk⟩
    rw [← hst] at hns
    have hlenT : ns.length ≤ y.length := by
      have := hbd.T; rw [hns] at this; simpa using this
    have hval : ∀ v ∈ ns, v < 2 ^ (y.length + 1) := fun v hv => by
      have := hbd.tok (.num v) (by rw [hns]; exact List.mem_map_of_mem hv)
      simpa [Tok.val] using this
    obtain ⟨hTv, hTK⟩ := hR.tok
    have harr : (σ2.arrs "TK").take ns.length = ns := by
      rw [hns] at hTK
      simpa [List.map_map, Function.comp_def, Tok.val] using hTK
    obtain ⟨σa, ra, oa⟩ := W.accRun B B.size y.length ns (σ2.arrs "TK") σ2 hsh harr rfl hlenT hval hB hs
    have rite := Run.ite_true (d := W.rej)
      (cond_lit_true (B := B) hph (by omega))
      (Run.ite_true (d := W.rej) (cond_lit_true (B := B) hLv (by omega))
        (Run.ite_true (d := W.rej) (cond_lit_true (B := B) hkind (by omega)) ra))
    refine ⟨σa, (r1.seq (r2.seq rite)).mono ?_, ?_⟩
    · unfold WrapN.Kmain
      simp only [Cond.size, Expr.size]
      have := W.Kmono B.size ns.length y.length hlenT
      omega
    · rw [oa, ho2, W.bits_accept y ns hw hsh]
      simp only [List.nil_append]
  · have hrej := W.bits_reject y hacc
    obtain ⟨σr, rr, orr⟩ := W.rejRun B B.size σ2 hs (by omega)
    have houtr : σr.out = W.redBits y := by
      rw [orr, ho2, hrej]; simp
    have hKrej : W.Krej B.size ≤ W.Kmain y.length B.size := by
      unfold WrapN.Kmain; omega
    by_cases h0 : st.ph = 0
    · by_cases hL0 : st.L = 0
      · have hk : W.E st.toks ≠ .done := fun hk => hacc ⟨h0, hL0, hk⟩
        have rite := Run.ite_true (d := W.rej)
          (cond_lit_true (B := B) (hR.ph.trans h0) (by omega))
          (Run.ite_true (d := W.rej) (cond_lit_true (B := B) (hR.L.trans hL0) (by omega))
            (Run.ite_false (c := W.acc) (cond_lit_false (B := B)
              (by rw [hR.kind]; exact fun h => hk (kcode_done.mp h)) hkB (by omega)) rr))
        exact ⟨σr, (r1.seq (r2.seq rite)).mono (by
          unfold WrapN.Kmain; simp only [Cond.size, Expr.size]; omega), houtr⟩
      · have rite := Run.ite_true (d := W.rej)
          (cond_lit_true (B := B) (hR.ph.trans h0) (by omega))
          (Run.ite_false (c := Com.ite (.eq (.var "kind") (.lit 2)) W.acc W.rej)
            (cond_lit_false (B := B) (by rw [hR.L]; exact hL0) hLB (by omega)) rr)
        exact ⟨σr, (r1.seq (r2.seq rite)).mono (by
          unfold WrapN.Kmain; simp only [Cond.size, Expr.size]; omega), houtr⟩
    · have rite := Run.ite_false
        (c := Com.ite (.eq (.var "L") (.lit 0))
          (.ite (.eq (.var "kind") (.lit 2)) W.acc W.rej) W.rej)
        (cond_lit_false (B := B) (by rw [hR.ph]; exact h0) hphB (by omega)) rr
      exact ⟨σr, (r1.seq (r2.seq rite)).mono (by
        unfold WrapN.Kmain; simp only [Cond.size, Expr.size]; omega), houtr⟩

end Lax117284Proofs.Machine.WrapNum

end

/-! ### `Lax117284Proofs.Machine.WrapNFinal` -/

section
/-!
A reduction of the shape of `WrapN` is polynomial-time computable: on the word RAM, and hence on a
Turing machine, once its program is laid out in memory and its accepting phase is linear in the
size of its input times the word size.
-/

namespace Lax117284Proofs.Machine.WrapNFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.WrapNum Lax117284Proofs.Machine.FreeFinal
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax759944Proofs.Encoding

variable (W : WrapN) (layout : Layout)

theorem solves (hok : Com.Ok layout W.mainW) :
    Solves layout W.mainW FreeFinal.Shape (fun x => W.redBits x.tail) (fun x => Bd x.tail)
      (fun x => W.Kmain x.tail.length (Bd x.tail).size) where
  ok := hok
  inp := by
    intro x hx v hv
    rw [shape_eq hx] at hv
    have hpow : x.tail.length < 2 ^ (2 * x.tail.length + 4) := by
      have := Nat.lt_two_pow_self (n := x.tail.length)
      have h2 : 2 ^ x.tail.length ≤ 2 ^ (2 * x.tail.length + 4) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    rcases List.mem_cons.mp hv with rfl | hv'
    · unfold Bd; omega
    · have := le_Mx hv'; unfold Bd; omega
  run := by
    intro x hx
    obtain ⟨σ', hrun, hout⟩ := mainW_spec (W := W) (B := Bd x.tail) x.tail
      (fun v hv => by
        have := le_Mx hv
        have h2 : 2 ^ (2 * x.tail.length + 4) ≥ 1 := Nat.one_le_two_pow
        unfold Bd; omega)
      (by unfold Bd; omega)
    rw [← shape_eq hx] at hrun
    exact ⟨_, σ', hrun, hout⟩

theorem prog_runs (hok : Com.Ok layout W.mainW) (harr : layout.arrays.length = 2)
    (hsc : layout.temps + layout.scalars.length ≤ 200) (w : ℕ) (x : List ℕ)
    (hfit : 202 + 2 * Bd x ≤ 2 ^ w) :
    ∃ t ≤ 10 * W.Kmain x.length (Bd x).size + 1,
      RunsTo w (compileProgram layout W.mainW) (x.length :: x) (W.redBits x) t := by
  have hs : Solves layout W.mainW {z | z = x.length :: x} (fun z => W.redBits z.tail)
      (fun z => Bd z.tail) (fun z => W.Kmain z.tail.length (Bd z.tail).size) :=
    ⟨(solves W layout hok).ok, fun z hz => (solves W layout hok).inp z
      (by rw [hz]; exact ⟨by simp, by simp⟩),
      fun z hz => (solves W layout hok).run z (by rw [hz]; exact ⟨by simp, by simp⟩)⟩
  have h := computesInTime_of_solves (w := w)
    (T := fun z => 10 * W.Kmain z.tail.length (Bd z.tail).size + 1) hs
    (fun z hz => by
      rw [hz]; simp only [List.tail_cons]
      have hB : 64 ≤ Bd x := by
        have := Nat.zero_le (2 ^ (2 * x.length + 4))
        unfold Bd; omega
      refine fitsWords_of_max_le (by omega) ?_
      simp only [Layout.span, harr, max_le_iff]
      omega)
    (fun z hz => by simp [Layout.const])
  obtain ⟨t, ht, hrun⟩ := h (x.length :: x) rfl
  exact ⟨t, by simpa using ht, by simpa using hrun⟩

/-- **The reduction is a polynomial-time word RAM computation on the zeros and ones of its
input**, when its accepting phase costs at most `C · (Sz + 1) · (l + 1) ^ e`. -/
theorem ramPolytimeE (hok : Com.Ok layout W.mainW) (harr : layout.arrays.length = 2)
    (hsc : layout.temps + layout.scalars.length ≤ 200) (C e : ℕ) (he : 1 ≤ e)
    (hK : ∀ Sz l, W.Kacc Sz l ≤ C * (Sz + 1) * (l + 1) ^ e)
    (hKr : ∀ Sz, W.Krej Sz ≤ C * (Sz + 1))
    (hout : ∀ x, ∀ v ∈ W.redBits x, v < 2 ^ (2 * bitSize x + 10)) :
    RamPolytime W.redBits := by
  refine Lax117284Proofs.Machine.RamBridge2.ramPolytime_of_wordlen (d := 2) (K := 10)
    (prog := compileProgram layout W.mainW)
    (Polynomial.C (100 * (2 * C + W.Knk + 1000)) * (Polynomial.X + Polynomial.C 1) ^ (e + 1))
    (by omega) ?_ ?_
  · exact hout
  · intro w x hw
    have hB := Bd_lt x
    have hlen := length_le_bitSize x
    have hfit : 202 + 2 * Bd x ≤ 2 ^ w := by
      have h1 : (2 : ℕ) ^ (2 * bitSize x + 11) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
      have e : (2 : ℕ) ^ (2 * bitSize x + 11) = 16 * 2 ^ (2 * bitSize x + 7) := by ring
      have h5 : 128 ≤ 2 ^ (2 * bitSize x + 7) := by
        calc (128 : ℕ) = 2 ^ 7 := by norm_num
          _ ≤ 2 ^ (2 * bitSize x + 7) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    obtain ⟨t, ht, hrun⟩ := prog_runs W layout hok harr hsc w x hfit
    refine ⟨t, ?_, hrun⟩
    have hsz : (Bd x).size ≤ 2 * bitSize x + 7 := Nat.size_le.mpr hB
    unfold WrapN.Kmain at ht
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
    obtain ⟨u, hu⟩ : ∃ u, u = bitSize x + 1 := ⟨_, rfl⟩
    rw [← hu]
    have hu1 : 1 ≤ u := by omega
    have hT1 : u ≤ u ^ (e + 1) := Nat.le_self_pow (by omega) u
    have hT0 : 1 ≤ u ^ (e + 1) := le_trans hu1 hT1
    have hpe : (x.length + 1) ^ e ≤ u ^ e := Nat.pow_le_pow_left (by omega) e
    have h8 : (Bd x).size + 1 ≤ 8 * u := by omega
    have hTe : u * u ^ e = u ^ (e + 1) := by rw [pow_succ']
    have hKa : W.Kacc (Bd x).size x.length ≤ 8 * C * u ^ (e + 1) := by
      calc W.Kacc (Bd x).size x.length ≤ C * ((Bd x).size + 1) * (x.length + 1) ^ e := hK _ _
        _ ≤ C * (8 * u) * u ^ e := Nat.mul_le_mul (Nat.mul_le_mul_left _ h8) hpe
        _ = 8 * C * (u * u ^ e) := by ring
        _ = 8 * C * u ^ (e + 1) := by rw [hTe]
    have hKb : W.Krej (Bd x).size ≤ 8 * C * u ^ (e + 1) := by
      calc W.Krej (Bd x).size ≤ C * ((Bd x).size + 1) := hKr _
        _ ≤ C * (8 * u) := Nat.mul_le_mul_left _ h8
        _ = 8 * C * u := by ring
        _ ≤ 8 * C * u ^ (e + 1) := Nat.mul_le_mul_left _ hT1
    have hL1 : (W.Knk + 116) * x.length ≤ (W.Knk + 116) * u ^ (e + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hL2 : W.Knk + 56 ≤ (W.Knk + 56) * u ^ (e + 1) := Nat.le_mul_of_pos_right _ hT0
    have hmain : 12 * x.length + 10 + (20 + W.Knk + ((100 + W.Knk + 4) * x.length + 6)) + 20 +
        W.Kacc (Bd x).size x.length + W.Krej (Bd x).size ≤
        (2 * W.Knk + 172 + 16 * C) * u ^ (e + 1) := by nlinarith
    nlinarith [hmain, hT0, Nat.zero_le C, Nat.zero_le W.Knk]

end Lax117284Proofs.Machine.WrapNFinal

end

/-! ### `Lax117284Proofs.Machine.UFinal` -/

section
/-!
The reduction of the unit processing times to matching, as a reduction on numbers of the shape
`WrapN`, and its running time on the word RAM.
-/

namespace Lax117284Proofs.Machine.UFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.USem Lax117284Proofs.Machine.UAcc Lax117284Proofs.Machine.UCongr
open Lax117284Proofs.Machine.WrapNum Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.URow
open Lax117284Proofs.Machine Lax117284Proofs.Machine.UEmit
open Lax117284Proofs.UnitPGraph
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax759944Proofs.Encoding

open scoped Classical

theorem getD_take_eq {arr ns : List ℕ} (h : arr.take ns.length = ns) {k : ℕ} (hk : k < ns.length) :
    arr.getD k 0 = ns.getD k 0 := by
  conv_rhs => rw [← h]
  simp [List.getD_eq_getElem?_getD, hk]

/-- The cost of the accepting phase, on an input of `l` numbers. -/
def KaccU (_Sz l : ℕ) : ℕ := 200 + 460 * l + 140 * l * l

theorem KaccU_mono (Sz a b : ℕ) (h : a ≤ b) : KaccU Sz a ≤ KaccU Sz b := by
  unfold KaccU
  have := Nat.mul_le_mul h h
  nlinarith

/-- **The accepting phase, on a stream of the format.** -/
theorem accU_stream (B L : ℕ) (ns arr : List ℕ) (σ : Env) (hsh : Shape eU ns)
    (harr : arr.take ns.length = ns) (hA : σ.arrs "TK" = arr) (hlenL : ns.length ≤ L)
    (hvals : ∀ v ∈ ns, v < 2 ^ (L + 1)) (hB : 2 ^ (2 * L + 4) + 8 * L + 64 ≤ B) :
    ∃ σ', Run B accU σ σ' (KaccU 0 ns.length) ∧
      σ'.out = σ.out ++ (if condU ns then outU ns else rejU) := by
  obtain ⟨h2, hl⟩ := hsh
  simp only [eU] at hl
  have hl' : ns.length = 3 + 2 * (ns.getD 1 0 * ns.getD 0 0) := by omega
  have hg : ∀ k < ns.length, arr.getD k 0 = ns.getD k 0 := fun k hk => getD_take_eq harr hk
  have hlenA : ns.length ≤ arr.length := by
    have := congrArg List.length harr
    rw [List.length_take] at this; omega
  have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
  have hpow2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (2 ^ L * 2 ^ L) := by ring
  have hLt : L < 2 ^ L := Nat.lt_two_pow_self
  have hPP : 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.le_mul_of_pos_right _ (by positivity)
  have hval : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1) := fun k hk => by
    rw [List.getD_eq_getElem _ _ hk]; exact hvals _ (List.getElem_mem hk)
  have hN : ns.getD 1 0 * ns.getD 0 0 + 3 + ns.getD 1 0 * ns.getD 0 0 ≤ L := by omega
  have hE : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 + 8 < B := fun k hk => by
    rw [hg k (by omega)]
    have := hval k (by omega)
    omega
  have hBB : 3 + 2 * (ns.getD 1 0 * ns.getD 0 0) + 8 < B := by omega
  obtain ⟨σ', r, o⟩ := accU_run (B := B) arr (ns.getD 0 0) (ns.getD 1 0) (paramOf ns)
    (by rw [hg 0 (by omega)]) (by rw [hg 1 (by omega)]) (by
      have : 2 + 2 * (ns.getD 1 0 * ns.getD 0 0) < ns.length := by omega
      rw [hg _ this]; rfl)
    σ hA (by omega) hE hBB
  refine ⟨σ', r.mono ?_, ?_⟩
  · unfold KaccU
    have hle : ns.getD 1 0 * ns.getD 0 0 ≤ ns.length := by omega
    have := Nat.mul_le_mul hle hle
    nlinarith
  · rw [o]
    congr 1
    have hcond : (∀ t < ns.getD 1 0 * ns.getD 0 0, PassU arr t) ↔ condU ns := by
      unfold condU PassU
      refine forall_congr' fun t => imp_congr_right fun ht => ?_
      rw [hg _ (by omega), hg _ (by omega)]
    by_cases hc : condU ns
    · rw [if_pos (hcond.mpr hc), if_pos hc]
      unfold outU
      exact graphNums_congr (fun t ht => by
        unfold dA dU; rw [hg _ (by omega)])
    · rw [if_neg (fun h => hc (hcond.mp h)), if_neg hc]

/-! ### The reduction as a `WrapN` -/

/-- The memory layout: the scalars of the tokenizer and of the accepting phase, the arrays of
the tokenizer. -/
def layoutU : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "n",
    "m", "N", "N2", "m1", "g", "kp", "ok", "d", "b3", "v", "s", "u", "i2", "ix", "aa", "M",
    "k1", "nn", "mm", "V1", "C1", "C2", "CC", "tq", "ci", "cr", "j1", "j2", "tt", "x1", "x2",
    "pa", "da", "pb", "db", "cj", "r2", "i1", "CU", "q", "C", "r", "dj", "rep", "fnd", "jj", "cn",
    "cc", "a1", "a2", "a3", "a4", "a5"], ["a", "TK"], 12⟩

/-- **The reduction as a reduction on numbers.** -/
noncomputable def W : WrapN where
  E := EI eU
  Sh := Shape eU
  nk := UNk.nkU
  Knk := 60
  hnk := fun B Bt cap hB => UNk.nkU_spec (B := B) Bt cap hB
  hconf := fun ns hs => conforms_of_shape eU hs
  hshape := fun ts h => shape_of_conforms eU h
  red := redU
  cond := condU
  outN := outU
  sem_acc := fun ns hs hc => redU_acc ns hs hc
  rejN := rejU
  sem_rej := fun w h => redU_rej w h
  rej := rejCom
  Krej := fun _ => 4
  rejRun := fun B _ σ _ hB => rejCom_run σ (by omega)
  acc := accU
  Kacc := KaccU
  Kmono := KaccU_mono
  accRun := fun B _ L ns arr σ hsh harr hA hlenL hvals hB _ =>
    accU_stream B L ns arr σ hsh harr hA hlenL hvals hB

theorem com_ok : Com.Ok layoutU W.mainW := by
  simp [WrapN.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, UNk.nkU,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    accU, prepU, okLoopU, okBodyU, okChkU, rejCom, kBigCom, mainU, rowsLoop,
    FoldLoop.fLoop, rowBody, locCom, setCom, repFind, repFindBody, idxD, cellE, emit6,
    emitRep, repLoop, repBody, layoutU, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 800 * (Sz + 1) * (l + 1) ^ 2 := by
  intro Sz l
  show KaccU Sz l ≤ _
  unfold KaccU
  nlinarith [Nat.zero_le Sz, Nat.zero_le l, Nat.zero_le (Sz * l), Nat.zero_le (Sz * l * l),
    Nat.zero_le (l * l)]

theorem redBits_lt (y : List ℕ) : ∀ v ∈ W.redBits y, v < 2 ^ (2 * bitSize y + 10) := by
  intro v hv
  have h1 := redU_lt (bitsOf y) v hv
  have h2 : (bitsOf y).length = y.length := by simp [bitsOf]
  have h3 := length_le_bitSize y
  have h4 : bitSize y < 2 ^ bitSize y := Nat.lt_two_pow_self
  have h5 : (2 : ℕ) ^ bitSize y < 2 ^ (2 * bitSize y + 10) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-- **The reduction of the unit processing times to matching is a polynomial-time word RAM
computation on the zeros and ones of its input.** -/
theorem redU_ramPolytime : RamPolytime W.redBits :=
  WrapNFinal.ramPolytimeE W layoutU com_ok rfl (by simp [layoutU]) 800 2 (by omega) Kpoly
    (fun Sz => by show 4 ≤ 800 * (Sz + 1); omega) redBits_lt

end Lax117284Proofs.Machine.UFinal

end
