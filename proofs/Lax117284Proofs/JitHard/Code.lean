import Lax470956.BinaryEncoding
import Lax117284.JustInTime
import Lax117284Proofs.JitHard.Reduction
import Lax117284Proofs.Machine.JitHardFormat
import Lax117284Proofs.Machine.JitHardSem
import Lax117284Proofs.Machine.Lists

/-!
The binary code of an instance of interval scheduling with eligible machine sets is the code of
a stream of the format the word RAM program reads, and the image the program writes is the code
of the image of the instance.
-/

namespace Lax117284Proofs.JitHard.Code

open Lax434930.PolynomialTime Lax470956.Scheduling
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.JitHardFormat
open Lax117284Proofs.Machine.Lists

/-! ### The numbers of an instance -/

/-- The processing time of job `j`, and `0` beyond the last. -/
def numP (I : SchedI) (j : ℕ) : ℕ := if h : j < I.jobs then I.p ⟨j, h⟩ else 0

/-- The deadline of job `j`. -/
def numD (I : SchedI) (j : ℕ) : ℕ := if h : j < I.jobs then I.d ⟨j, h⟩ else 0

/-- The weight of job `j`. -/
def numW (I : SchedI) (j : ℕ) : ℕ := if h : j < I.jobs then I.w ⟨j, h⟩ else 0

/-- The bit of the eligibility matrix at job `j` and machine `i`. -/
def numBit (I : SchedI) (j i : ℕ) : ℕ :=
  if h : j < I.jobs then
    (if h' : i < I.machines then
      (if (⟨i, h'⟩ : Fin I.machines) ∈ I.eligible ⟨j, h⟩ then 1 else 0) else 0)
  else 0

/-- The counts and the three tables. -/
def front (I : SchedI) : List ℕ :=
  [I.jobs, I.machines] ++ (List.range I.jobs).map (numP I) ++ (List.range I.jobs).map (numD I) ++
    (List.range I.jobs).map (numW I)

/-- The eligibility matrix. -/
def tail (I : SchedI) : List ℕ :=
  (List.range I.jobs).flatMap fun j => (List.range I.machines).map (numBit I j)

/-- The numbers of an instance, in the order of its code. -/
def nsOf (I : SchedI) : List ℕ := front I ++ tail I

theorem front_length (I : SchedI) : (front I).length = 2 + 3 * I.jobs := by
  simp [front]
  omega

theorem tail_length (I : SchedI) : (tail I).length = I.jobs * I.machines := by
  simp [tail, List.length_flatMap]

theorem tail_le_one (I : SchedI) : ∀ v ∈ tail I, v ≤ 1 := by
  intro v hv
  simp only [tail, List.mem_flatMap, List.mem_map] at hv
  obtain ⟨j, -, i, -, rfl⟩ := hv
  unfold numBit
  split_ifs <;> omega

theorem getD_zero (I : SchedI) : (nsOf I).getD 0 0 = I.jobs := by
  simp [nsOf, front]

theorem getD_one (I : SchedI) : (nsOf I).getD 1 0 = I.machines := by
  simp [nsOf, front]

theorem length_nsOf (I : SchedI) : (nsOf I).length = 2 + 3 * I.jobs + I.jobs * I.machines := by
  simp only [nsOf, List.length_append, front_length, tail_length]

theorem shape (I : SchedI) : ShapeH (nsOf I) := by
  refine ⟨by rw [length_nsOf]; omega, ?_, ?_⟩
  · rw [getD_zero, getD_one, length_nsOf]
  · intro k hk hk'
    rw [getD_zero] at hk
    have hk2 : k - (front I).length < (tail I).length := by
      rw [front_length, tail_length]
      rw [length_nsOf] at hk'
      omega
    have h1 : (nsOf I).getD k 0 = (tail I).getD (k - (front I).length) 0 :=
      List.getD_append_right _ _ _ _ (by rw [front_length]; omega)
    rw [h1, List.getD_eq_getElem _ _ hk2]
    exact tail_le_one I _ (List.getElem_mem hk2)

/-! ### The tokens of a stream -/

lemma code_map_num (ns : List ℕ) : code (ns.map Tok.num) = numCode ns := by
  induction ns with
  | nil => rfl
  | cons a t ih => simp [code, Tok.code, numCode] at ih ⊢; rw [ih]

lemma code_map_bit (ns : List ℕ) :
    code (ns.map fun v => Tok.bit (decide (v ≠ 0))) = ns.map fun v => decide (v ≠ 0) := by
  induction ns with
  | nil => rfl
  | cons a t ih => simp [code, Tok.code] at ih ⊢; rw [ih]

theorem toksH_split (ns : List ℕ) (h : ShapeH ns) :
    toksH ns = (ns.take (2 + 3 * ns.getD 0 0)).map Tok.num ++
      (ns.drop (2 + 3 * ns.getD 0 0)).map (fun v => Tok.bit (decide (v ≠ 0))) := by
  obtain ⟨h2, hl, hs⟩ := h
  have hle : 2 + 3 * ns.getD 0 0 ≤ ns.length := by omega
  have hmin : min (2 + 3 * ns.getD 0 0) ns.length = 2 + 3 * ns.getD 0 0 := Nat.min_eq_left hle
  have hlenL : (List.map Tok.num (List.take (2 + 3 * ns.getD 0 0) ns) ++
        List.map (fun v => Tok.bit (decide (v ≠ 0))) (List.drop (2 + 3 * ns.getD 0 0) ns)).length
      = ns.length := by
    simp only [List.length_append, List.length_map, List.length_take, List.length_drop, hmin]
    omega
  apply List.ext_getElem
  · rw [hlenL]; simp [toksH]
  · intro k h1 h2'
    have hk : k < ns.length := by simpa [toksH] using h1
    have hL : (toksH ns)[k] = tokAtH ns k := by simp [toksH]
    rw [hL]
    by_cases hka : k < 2 + 3 * ns.getD 0 0
    · have hlt : k < (List.map Tok.num (List.take (2 + 3 * ns.getD 0 0) ns)).length := by
        simp only [List.length_map, List.length_take, hmin]; exact hka
      rw [List.getElem_append_left hlt]
      simp only [tokAtH, if_pos hka, List.getElem_map, List.getElem_take]
      simp [List.getElem?_eq_getElem hk]
    · have hlt : ¬ k < (List.map Tok.num (List.take (2 + 3 * ns.getD 0 0) ns)).length := by
        simp only [List.length_map, List.length_take, hmin]; exact hka
      rw [List.getElem_append_right (by omega)]
      simp only [tokAtH, if_neg hka, List.getElem_map, List.getElem_drop]
      have hlen' : (List.map Tok.num (List.take (2 + 3 * ns.getD 0 0) ns)).length =
          2 + 3 * ns.getD 0 0 := by
        simp only [List.length_map, List.length_take]; exact hmin
      have e : 2 + 3 * ns.getD 0 0 + (k - (2 + 3 * ns.getD 0 0)) = k := by omega
      simp only [hlen', e]
      simp [List.getElem?_eq_getElem hk]

theorem code_toksH (ns : List ℕ) (h : ShapeH ns) :
    code (toksH ns) = numCode (ns.take (2 + 3 * ns.getD 0 0)) ++
      (ns.drop (2 + 3 * ns.getD 0 0)).map (fun v => decide (v ≠ 0)) := by
  rw [toksH_split ns h, code_append, code_map_num, code_map_bit]

/-! ### The code of an instance -/

lemma map_finRange_eq {α : Type} (m : ℕ) (g : Fin m → α) (h : ℕ → α)
    (hh : ∀ i (hi : i < m), h i = g ⟨i, hi⟩) :
    (List.finRange m).map g = (List.range m).map h := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
    have hk : k < m := by simpa using h1
    rw [hh k hk]
    rfl

lemma flatMap_finRange_eq {α : Type} (m : ℕ) (g : Fin m → List α) (h : ℕ → List α)
    (hh : ∀ i (hi : i < m), h i = g ⟨i, hi⟩) :
    (List.finRange m).flatMap g = (List.range m).flatMap h := by
  rw [flatMap_finRange]
  refine List.flatMap_congr fun i hi => ?_
  have hi' := List.mem_range.mp hi
  rw [dif_pos hi', hh i hi']

lemma numCode_map (l : List ℕ) (f : ℕ → ℕ) :
    numCode (l.map f) = l.flatMap (fun x => Lax117284.Problems.encodeNat (f x)) := by
  simp [numCode, List.flatMap_map]

/-- **The code of an instance is the code of the stream of its numbers.** -/
theorem encode_eq (I : SchedI) :
    Lax470956.BinaryEncoding.encodeInstance I = code (toksH (nsOf I)) := by
  rw [code_toksH _ (shape I), getD_zero, show 2 + 3 * I.jobs = (front I).length from
    (front_length I).symm]
  unfold nsOf
  rw [List.take_left, List.drop_left]
  unfold Lax470956.BinaryEncoding.encodeInstance front tail
  simp only [numCode_append, numCode_cons, numCode_nil, List.append_nil, numCode_map]
  have e1 := flatMap_finRange_eq I.jobs
    (fun j => Lax470956.BinaryEncoding.encodeNat (I.p j))
    (fun j => Lax117284.Problems.encodeNat (numP I j)) (fun i hi => by simp [numP, hi]; rfl)
  have e2 := flatMap_finRange_eq I.jobs
    (fun j => Lax470956.BinaryEncoding.encodeNat (I.d j))
    (fun j => Lax117284.Problems.encodeNat (numD I j)) (fun i hi => by simp [numD, hi]; rfl)
  have e3 := flatMap_finRange_eq I.jobs
    (fun j => Lax470956.BinaryEncoding.encodeNat (I.w j))
    (fun j => Lax117284.Problems.encodeNat (numW I j)) (fun i hi => by simp [numW, hi]; rfl)
  have e4 := flatMap_finRange_eq I.jobs
    (fun j => (List.finRange I.machines).map fun i => decide (i ∈ I.eligible j))
    (fun j => (List.range I.machines).map fun i => decide (numBit I j i ≠ 0)) (fun j hj => by
      rw [map_finRange_eq I.machines _ (fun i => decide (numBit I j i ≠ 0))]
      intro i hi
      simp only [numBit, hj, hi, dif_pos]
      split_ifs <;> simp_all)
  rw [e1, e2, e3, e4]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  rfl

/-! ### Reading the numbers back -/

lemma getD_map_range (n j : ℕ) (f : ℕ → ℕ) (hj : j < n) :
    ((List.range n).map f).getD j 0 = f j := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

lemma getD_flatMap_blocks (g : ℕ → ℕ → ℕ) (m : ℕ) :
    ∀ n j i, j < n → i < m →
      ((List.range n).flatMap (fun j => (List.range m).map (g j))).getD (j * m + i) 0 = g j i := by
  intro n
  induction n with
  | zero => intro j i hj; omega
  | succ n ih =>
    intro j i hj hi
    rw [List.range_succ, List.flatMap_append]
    have hlen : ((List.range n).flatMap (fun j => (List.range m).map (g j))).length = n * m := by
      simp [List.length_flatMap]
    by_cases hjn : j < n
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith)]
      exact ih j i hjn hi
    · have hjn' : j = n := by omega
      subst hjn'
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have : j * m + i - j * m = i := by omega
      rw [this, getD_map_range _ _ _ hi]

lemma front_getD_left (I : SchedI) (k : ℕ) (hk : k < (front I).length) :
    (nsOf I).getD k 0 = (front I).getD k 0 := by
  unfold nsOf; exact List.getD_append _ _ _ _ hk

theorem rd_p (I : SchedI) (j : ℕ) (hj : j < I.jobs) : (nsOf I).getD (2 + j) 0 = numP I j := by
  rw [front_getD_left I _ (by rw [front_length]; omega)]
  unfold front
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    show 2 + j - 2 = j by omega]
  exact getD_map_range _ _ _ hj

theorem rd_d (I : SchedI) (j : ℕ) (hj : j < I.jobs) :
    (nsOf I).getD (2 + I.jobs + j) 0 = numD I j := by
  rw [front_getD_left I _ (by rw [front_length]; omega)]
  unfold front
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_range, Nat.zero_add, Nat.reduceAdd, show 2 + I.jobs + j - (2 + I.jobs) = j by omega]
  exact getD_map_range _ _ _ hj

theorem rd_bit (I : SchedI) (j i : ℕ) (hj : j < I.jobs) (hi : i < I.machines) :
    (nsOf I).getD (2 + 3 * I.jobs + j * I.machines + i) 0 = numBit I j i := by
  have h1 : (nsOf I).getD (2 + 3 * I.jobs + j * I.machines + i) 0 =
      (tail I).getD (j * I.machines + i) 0 := by
    unfold nsOf
    rw [List.getD_append_right _ _ _ _ (by rw [front_length]; omega), front_length]
    congr 1
    omega
  rw [h1]
  exact getD_flatMap_blocks (numBit I) I.machines I.jobs j i hj hi


/-! ### The image -/

theorem walls_eq (I : SchedI) : walls I = Lax117284Proofs.Machine.JitHardSem.wallsN I.jobs I.machines := by
  rcases Nat.eq_zero_or_pos I.jobs with h | h
  · rw [walls_eq_zero I h, h, Lax117284Proofs.Machine.JitHardSem.wallsN_zero]
  · rw [walls_eq_of_pos I h, Lax117284Proofs.Machine.JitHardSem.wallsN_pos _ _ h]

theorem dOf_val (I : SchedI) (k : Fin (I.jobs + walls I)) :
    dOf I k = if h : k.val < I.jobs then I.d ⟨k.val, h⟩ + 1 else 1 := by
  refine Fin.addCases (fun j => ?_) (fun w => ?_) k
  · simp [dOf, j.2]
  · have : ¬ (Fin.natAdd I.jobs w).val < I.jobs := by simp
    simp [dOf, this]

theorem pOf_val (I : SchedI) (i : Fin I.machines) (k : Fin (I.jobs + walls I)) :
    pOf I i k = if h : k.val < I.jobs then
      (if i ∈ I.eligible ⟨k.val, h⟩ then I.p ⟨k.val, h⟩ else I.d ⟨k.val, h⟩ + 1) else 1 := by
  refine Fin.addCases (fun j => ?_) (fun w => ?_) k
  · simp [pOf, j.2]
  · have : ¬ (Fin.natAdd I.jobs w).val < I.jobs := by simp
    simp [pOf, this]

lemma enc_eq (n : ℕ) : Lax470956.BinaryEncoding.encodeNat n = Lax117284.Problems.encodeNat n := rfl

lemma numCode_replicate (k a : ℕ) :
    numCode (List.replicate k a) = (List.range k).flatMap (fun _ => Lax117284.Problems.encodeNat a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ', List.range_succ, List.flatMap_append, ← ih, numCode_append]
    simp

lemma numCode_flatMap (l : List ℕ) (g : ℕ → List ℕ) :
    numCode (l.flatMap g) = l.flatMap (fun x => numCode (g x)) := by
  simp [numCode, List.flatMap_assoc]

/-- The due dates of the image: the jobs, and then the walls. -/
theorem dPart (I : SchedI) :
    (List.finRange (I.jobs + walls I)).flatMap (fun k => Lax117284.Problems.encodeNat (dOf I k)) =
      (List.range I.jobs).flatMap (fun j => Lax117284.Problems.encodeNat (numD I j + 1)) ++
        (List.range (walls I)).flatMap (fun _ => Lax117284.Problems.encodeNat 1) := by
  rw [flatMap_finRange_eq (I.jobs + walls I) _
    (fun k => if k < I.jobs then Lax117284.Problems.encodeNat (numD I k + 1)
      else Lax117284.Problems.encodeNat 1) (fun k hk => by
      rw [dOf_val]
      by_cases h : k < I.jobs
      · simp [h, numD]
      · simp [h]), List.range_add, List.flatMap_append, List.flatMap_map]
  congr 1
  · exact List.flatMap_congr fun k hk => by rw [if_pos (List.mem_range.mp hk)]
  · exact List.flatMap_congr fun k hk => by simp

/-- The processing times of the image on a machine: the jobs, and then the walls. -/
theorem rowPart (I : SchedI) (i : Fin I.machines) :
    (List.finRange (I.jobs + walls I)).flatMap
        (fun k => Lax117284.Problems.encodeNat (pOf I i k)) =
      (List.range I.jobs).flatMap (fun j => Lax117284.Problems.encodeNat
          (Lax117284Proofs.Machine.JitHardSem.cellV (numBit I j i.val) (numP I j) (numD I j))) ++
        (List.range (walls I)).flatMap (fun _ => Lax117284.Problems.encodeNat 1) := by
  rw [flatMap_finRange_eq (I.jobs + walls I) _
    (fun k => if k < I.jobs then Lax117284.Problems.encodeNat
        (Lax117284Proofs.Machine.JitHardSem.cellV (numBit I k i.val) (numP I k) (numD I k))
      else Lax117284.Problems.encodeNat 1) (fun k hk => by
      rw [pOf_val]
      by_cases h : k < I.jobs
      · simp only [h, dif_pos, if_true]
        unfold numBit numP numD Lax117284Proofs.Machine.JitHardSem.cellV
        simp only [h, i.2, dif_pos]
        split_ifs <;> simp_all
      · simp [h]), List.range_add, List.flatMap_append, List.flatMap_map]
  congr 1
  · exact List.flatMap_congr fun k hk => by rw [if_pos (List.mem_range.mp hk)]
  · exact List.flatMap_congr fun k hk => by simp

/-- **The image the program writes is the code of the image of the instance.** -/
theorem outH_code (I : SchedI) :
    numCode (Lax117284Proofs.Machine.JitHardSem.outH (nsOf I)) =
      Lax117284.JustInTime.encodeInstance (toJIT I) := by
  open Lax117284Proofs.Machine.JitHardSem in
  have hn := getD_zero I
  have hm := getD_one I
  have hw := walls_eq I
  unfold Lax117284Proofs.Machine.JitHardSem.outH
  rw [hn, hm, ← hw]
  unfold Lax117284.JustInTime.encodeInstance
  show numCode ([I.jobs + walls I, I.machines] ++
      (List.range I.jobs).map (Lax117284Proofs.Machine.JitHardSem.dueN (nsOf I)) ++
      List.replicate (walls I) 1 ++
      (List.range (walls I)).flatMap fun i =>
        (List.range I.jobs).map (Lax117284Proofs.Machine.JitHardSem.cellN (nsOf I) i) ++
          List.replicate (walls I) 1) =
    Lax117284.Problems.encodeNat (I.jobs + walls I) ++ Lax117284.Problems.encodeNat I.machines ++
      (List.finRange (I.jobs + walls I)).flatMap
        (fun k => Lax117284.Problems.encodeNat (dOf I k)) ++
      (List.finRange I.machines).flatMap fun i => (List.finRange (I.jobs + walls I)).flatMap
        (fun k => Lax117284.Problems.encodeNat (pOf I i k))
  rw [dPart, flatMap_finRange_eq I.machines _ (fun i =>
    (List.range I.jobs).flatMap (fun j => Lax117284.Problems.encodeNat
        (Lax117284Proofs.Machine.JitHardSem.cellV (numBit I j i) (numP I j) (numD I j))) ++
      (List.range (walls I)).flatMap (fun _ => Lax117284.Problems.encodeNat 1))
    (fun i hi => (rowPart I ⟨i, hi⟩).symm)]
  have hdue : (List.range I.jobs).flatMap (fun j => Lax117284.Problems.encodeNat
        (Lax117284Proofs.Machine.JitHardSem.dueN (nsOf I) j)) =
      (List.range I.jobs).flatMap (fun j => Lax117284.Problems.encodeNat (numD I j + 1)) :=
    List.flatMap_congr fun j hj => by
      unfold Lax117284Proofs.Machine.JitHardSem.dueN
      rw [hn, rd_d I j (List.mem_range.mp hj)]
  have hrows : (List.range (walls I)).flatMap (fun i =>
        (List.range I.jobs).flatMap (fun j => Lax117284.Problems.encodeNat
            (Lax117284Proofs.Machine.JitHardSem.cellN (nsOf I) i j)) ++
          (List.range (walls I)).flatMap (fun _ => Lax117284.Problems.encodeNat 1)) =
      (List.range I.machines).flatMap (fun i =>
        (List.range I.jobs).flatMap (fun j => Lax117284.Problems.encodeNat
            (Lax117284Proofs.Machine.JitHardSem.cellV (numBit I j i) (numP I j) (numD I j))) ++
          (List.range (walls I)).flatMap (fun _ => Lax117284.Problems.encodeNat 1)) := by
    rcases Nat.eq_zero_or_pos I.jobs with h | h
    · have hW : walls I = 0 := walls_eq_zero I h
      rw [hW]
      simp [h]
    · have hW : walls I = I.machines := walls_eq_of_pos I h
      rw [hW]
      refine List.flatMap_congr fun i hi => ?_
      have hi' := List.mem_range.mp hi
      have hA : (List.range I.jobs).flatMap (fun j => Lax117284.Problems.encodeNat
            (Lax117284Proofs.Machine.JitHardSem.cellN (nsOf I) i j)) =
          (List.range I.jobs).flatMap (fun j => Lax117284.Problems.encodeNat
            (Lax117284Proofs.Machine.JitHardSem.cellV (numBit I j i) (numP I j) (numD I j))) :=
        List.flatMap_congr fun j hj => by
          have hj' := List.mem_range.mp hj
          unfold Lax117284Proofs.Machine.JitHardSem.cellN
          rw [hn, hm, rd_bit I j i hj' hi', rd_p I j hj', rd_d I j hj']
      rw [hA]
  simp only [numCode_append, numCode_cons, numCode_nil, List.append_nil, numCode_map,
    numCode_replicate, numCode_flatMap]
  rw [hdue, hrows]
  simp only [List.append_assoc]


end Lax117284Proofs.JitHard.Code
