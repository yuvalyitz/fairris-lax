import Lax117284Proofs.Machine.FreeSem

/-!
The reduction that adds a blocking client and a blocking day, on the numbers of a stream: what it
writes. The output is read off the table cell by cell, with the closed form of every cell of the
new table: a cell of the old table is copied, the new day repeats the first day's processing
times with the blocking due date, and the new client's job is the blocking job.
-/

namespace Lax117284Proofs.Machine.BlockSem

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.FreeSem

/-- The largest due date of the table, as a running maximum. -/
def dmaxOf (ns : List ℕ) : ℕ :=
  (List.range (ns.getD 1 0 * ns.getD 0 0)).foldl (fun g t => max g (ns.getD (2 + 2 * t + 1) 0)) 0

/-- A time later than every due date of the table. -/
def bdOf (ns : List ℕ) : ℕ := dmaxOf ns + 1

/-- The two numbers of cell `t` of the new table, whose rows have `n + 1` cells. -/
def cellB (ns : List ℕ) (t : ℕ) : List ℕ :=
  if t % (ns.getD 0 0 + 1) < ns.getD 0 0 then
    (if t / (ns.getD 0 0 + 1) < ns.getD 1 0 then
      [ns.getD (2 + 2 * (t / (ns.getD 0 0 + 1) * ns.getD 0 0 + t % (ns.getD 0 0 + 1))) 0,
       ns.getD (2 + 2 * (t / (ns.getD 0 0 + 1) * ns.getD 0 0 + t % (ns.getD 0 0 + 1)) + 1) 0]
    else [ns.getD (2 + 2 * (t % (ns.getD 0 0 + 1))) 0, bdOf ns])
  else [bdOf ns, bdOf ns]

/-- The numbers of the output: the counts with one more of each, the new table, and the
parameter `1`. -/
def outBlock (ns : List ℕ) : List ℕ :=
  [ns.getD 0 0 + 1, ns.getD 1 0 + 1] ++
    (List.range ((ns.getD 1 0 + 1) * (ns.getD 0 0 + 1))).flatMap (cellB ns) ++ [1]

/-- The numbers of the output for every accepted stream: with no clients the day count grows and
nothing else. -/
def outBlockAll (ns : List ℕ) : List ℕ :=
  if ns.getD 0 0 = 0 then [0, ns.getD 1 0 + 1, 1] else outBlock ns

section Bound

variable (ns : List ℕ) (hv : Valid ns)

lemma inst_d (a b : ℕ) (ha : a < ns.getD 1 0) (hb : b < ns.getD 0 0) :
    (instOf ns hv).dAt a b = ns.getD (2 + 2 * (a * ns.getD 0 0 + b) + 1) 0 := by
  have := Instance.dAt_coe (instOf ns hv) ⟨a, ha⟩ ⟨b, hb⟩
  simp only [Fin.val_mk] at this
  rw [this]; rfl

lemma inst_p (a b : ℕ) (ha : a < ns.getD 1 0) (hb : b < ns.getD 0 0) :
    (instOf ns hv).pAt a b = ns.getD (2 + 2 * (a * ns.getD 0 0 + b)) 0 := by
  have := Instance.pAt_coe (instOf ns hv) ⟨a, ha⟩ ⟨b, hb⟩
  simp only [Fin.val_mk] at this
  rw [this]; rfl

/-- The bound of the instance is the running maximum plus one. -/
theorem bound_instOf : Lax117284.Corollary8.bound (instOf ns hv) = bdOf ns := by
  unfold Lax117284.Corollary8.bound bdOf dmaxOf
  congr 1
  apply le_antisymm
  · refine Finset.sup_le fun i _ => Finset.sup_le fun j _ => ?_
    have h := inst_d ns hv i j i.isLt j.isLt
    have hd := Instance.dAt_coe (instOf ns hv) i j
    have ht : (i : ℕ) * ns.getD 0 0 + j < ns.getD 1 0 * ns.getD 0 0 := cell_lt i.isLt j.isLt
    have := le_foldl_max_of_lt (fun t => ns.getD (2 + 2 * t + 1) 0) (ns.getD 1 0 * ns.getD 0 0) 0
      ((i : ℕ) * ns.getD 0 0 + j) ht
    rw [← hd, h]
    exact this
  · refine foldl_max_le _ _ _ _ (Nat.zero_le _) fun t ht => ?_
    have hn : 0 < ns.getD 0 0 := by
      rcases Nat.eq_zero_or_pos (ns.getD 0 0) with h | h
      · rw [h] at ht; simp at ht
      · exact h
    have h1 : t / ns.getD 0 0 < ns.getD 1 0 := by
      rw [Nat.div_lt_iff_lt_mul hn]; exact ht
    have h2 : t % ns.getD 0 0 < ns.getD 0 0 := Nat.mod_lt _ hn
    have e : t / ns.getD 0 0 * ns.getD 0 0 + t % ns.getD 0 0 = t := by
      have := Nat.div_add_mod t (ns.getD 0 0)
      rw [Nat.mul_comm] at this
      omega
    have h := inst_d ns hv _ _ h1 h2
    rw [e] at h
    have hd := Instance.dAt_coe (instOf ns hv) ⟨t / ns.getD 0 0, h1⟩ ⟨t % ns.getD 0 0, h2⟩
    simp only [Fin.val_mk] at hd
    rw [← h, hd]
    exact Finset.le_sup (f := fun j => (instOf ns hv).d ⟨t / ns.getD 0 0, h1⟩ j)
        (Finset.mem_univ _) |>.trans
      (Finset.le_sup (f := fun i => Finset.univ.sup fun j => (instOf ns hv).d i j)
        (Finset.mem_univ _))

end Bound

section Cells

variable (I : Instance)

lemma pAt_blk {i j : ℕ} (hi : i < I.days + 1) (hj : j < I.clients + 1) :
    (Lax117284.Corollary8.addBlockingDay I).pAt i j =
      if j < I.clients then (if i < I.days then I.pAt i j else I.pAt 0 j)
      else Lax117284.Corollary8.bound I := by
  simp only [Instance.pAt, Lax117284.Corollary8.addBlockingDay]
  rw [dif_pos hi, dif_pos hj]

lemma dAt_blk {i j : ℕ} (hi : i < I.days + 1) (hj : j < I.clients + 1) :
    (Lax117284.Corollary8.addBlockingDay I).dAt i j =
      if j < I.clients ∧ i < I.days then I.dAt i j else Lax117284.Corollary8.bound I := by
  simp only [Instance.dAt, Lax117284.Corollary8.addBlockingDay]
  rw [dif_pos hi, dif_pos hj]

end Cells

/-- **The numbers of the instance with a blocking client and day added.** -/
theorem instToks_addBlock (ns : List ℕ) (hv : Valid ns) (hpos : 0 < ns.getD 1 0) :
    instToks (Lax117284.Corollary8.addBlockingDay (instOf ns hv)) =
      [ns.getD 0 0 + 1, ns.getD 1 0 + 1] ++
        (List.range ((ns.getD 1 0 + 1) * (ns.getD 0 0 + 1))).flatMap (cellB ns) := by
  set I := instOf ns hv with hI
  have hn : ns.getD 0 0 = I.clients := rfl
  have hm : ns.getD 1 0 = I.days := rfl
  have hb := bound_instOf ns hv
  unfold instToks
  show [I.clients + 1, I.days + 1] ++ _ = _
  rw [← hn, ← hm]
  congr 1
  refine List.flatMap_congr fun t ht => ?_
  have ht' : t < (ns.getD 1 0 + 1) * (ns.getD 0 0 + 1) := List.mem_range.mp ht
  have hn1 : 0 < ns.getD 0 0 + 1 := by omega
  have h1 : t / (ns.getD 0 0 + 1) < ns.getD 1 0 + 1 := by
    rw [Nat.div_lt_iff_lt_mul hn1]; exact ht'
  have h2 : t % (ns.getD 0 0 + 1) < ns.getD 0 0 + 1 := Nat.mod_lt _ hn1
  show [(Lax117284.Corollary8.addBlockingDay I).pAt (t / (ns.getD 0 0 + 1))
      (t % (ns.getD 0 0 + 1)), (Lax117284.Corollary8.addBlockingDay I).dAt
      (t / (ns.getD 0 0 + 1)) (t % (ns.getD 0 0 + 1))] = _
  rw [pAt_blk I (by rw [← hm]; exact h1) (by rw [← hn]; exact h2),
    dAt_blk I (by rw [← hm]; exact h1) (by rw [← hn]; exact h2), hb]
  unfold cellB
  by_cases hbn : t % (ns.getD 0 0 + 1) < ns.getD 0 0
  · by_cases han : t / (ns.getD 0 0 + 1) < ns.getD 1 0
    · rw [if_pos hbn, if_pos han, if_pos (by rw [← hn]; exact hbn), if_pos (by rw [← hm]; exact han),
        if_pos ⟨by rw [← hn]; exact hbn, by rw [← hm]; exact han⟩,
        inst_p ns hv _ _ han hbn, inst_d ns hv _ _ han hbn]
    · rw [if_pos hbn, if_neg han, if_pos (by rw [← hn]; exact hbn), if_neg (by rw [← hm]; exact han),
        if_neg (fun h => han (by rw [hm]; exact h.2)),
        inst_p ns hv 0 _ hpos hbn]
      simp
  · rw [if_neg hbn, if_neg (by rw [← hn]; exact hbn),
      if_neg (fun h => hbn (by rw [hn]; exact h.1))]

/-- **The reduction writes the numbers of the instance with a blocking client and day.** -/
theorem block_eq (ns : List ℕ) (hv : Valid ns) (hs : Shape eU ns) (hpos : 0 < ns.getD 1 0)
    (hk : paramOf ns = 1) :
    Lax117284.Corollary8.reduceBlockingDay (numCode ns) = numCode (outBlockAll ns) := by
  classical
  have hI : encodeUniform (instOf ns hv) (paramOf ns) = numCode ns := by
    rw [encodeUniform, encodeInstance_eq]
    conv_rhs => rw [← instToks_instOf ns hv hs]
    rw [numCode_append]
    simp [numCode]
  have hg : ∃ (I : Instance) (k : ℕ), encodeUniform I k = numCode ns ∧ 0 < I.days ∧ k = 1 :=
    ⟨instOf ns hv, paramOf ns, hI, hpos, hk⟩
  unfold Lax117284.Corollary8.reduceBlockingDay
  rw [dif_pos hg]
  have key : ∀ (I' : Instance) (k' : ℕ), encodeUniform I' k' = numCode ns →
      (if I'.clients = 0 then encodeUniform (Lax117284.Corollary8.noClients (I'.days + 1)) 1
        else encodeUniform (Lax117284.Corollary8.addBlockingDay I') 1) =
        numCode (outBlockAll ns) := by
    intro I' k' h'
    obtain ⟨rfl, rfl⟩ := Injectivity.encodeUniform_inj (h'.trans hI.symm)
    have hcl : (instOf ns hv).clients = ns.getD 0 0 := rfl
    have hdy : (instOf ns hv).days = ns.getD 1 0 := rfl
    unfold outBlockAll
    by_cases hn0 : ns.getD 0 0 = 0
    · rw [if_pos (by rw [hcl]; exact hn0), if_pos hn0, hdy, encodeUniform, encodeInstance_eq]
      have : instToks (Lax117284.Corollary8.noClients (ns.getD 1 0 + 1)) = [0, ns.getD 1 0 + 1] := by
        simp [instToks, Lax117284.Corollary8.noClients]
      rw [this]
      simp [numCode]
    · rw [if_neg (by rw [hcl]; exact hn0), if_neg hn0, encodeUniform, encodeInstance_eq,
        instToks_addBlock ns hv hpos]
      unfold outBlock
      simp only [numCode_append, List.append_assoc, numCode_cons, numCode_nil, List.append_nil]
  exact key _ _ hg.choose_spec.choose_spec.1

/-- **The gate of the reduction, on streams.** -/
theorem block_gate (w : Word) :
    (∃ (I : Instance) (k : ℕ), encodeUniform I k = w ∧ 0 < I.days ∧ k = 1) ↔
      ∃ ns : List ℕ, w = numCode ns ∧ Shape eU ns ∧ Valid ns ∧ 0 < ns.getD 1 0 ∧ paramOf ns = 1 := by
  constructor
  · rintro ⟨I, k, hw, hd, rfl⟩
    obtain ⟨ns, hw', hs, hv, hpos⟩ := (uniform_iff w).1 ⟨I, 1, hw, hd⟩
    refine ⟨ns, hw', hs, hv, hpos, ?_⟩
    have hI : encodeUniform (instOf ns hv) (paramOf ns) = numCode ns := by
      rw [encodeUniform, encodeInstance_eq]
      conv_rhs => rw [← instToks_instOf ns hv hs]
      rw [numCode_append]
      simp [numCode]
    have := Injectivity.encodeUniform_inj (I := instOf ns hv) (I' := I) (k := paramOf ns)
      (k' := 1) (hI.trans (hw'.symm.trans hw.symm))
    exact this.2
  · rintro ⟨ns, hw, hs, hv, hpos, hk⟩
    refine ⟨instOf ns hv, paramOf ns, ?_, hpos, hk⟩
    rw [hw, encodeUniform, encodeInstance_eq]
    conv_rhs => rw [← instToks_instOf ns hv hs]
    rw [numCode_append]
    simp [numCode]

/-- **A word that is not the code of an accepted stream is rejected.** -/
theorem block_rej (w : Word)
    (h : ¬ ∃ ns : List ℕ, w = numCode ns ∧ Shape eU ns ∧ Valid ns ∧ 0 < ns.getD 1 0 ∧
      paramOf ns = 1) :
    Lax117284.Corollary8.reduceBlockingDay w = rejected := by
  classical
  unfold Lax117284.Corollary8.reduceBlockingDay
  rw [dif_neg (fun hg => h ((block_gate w).1 hg))]

end Lax117284Proofs.Machine.BlockSem
