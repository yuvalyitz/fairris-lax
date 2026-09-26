import Lax117284Proofs.Machine.InstSem
import Lax117284Proofs.SourceInjectivity
import Lax117284.Theorem11

/-!
The just-in-time format and the reduction of Theorem 11 on the numbers of a stream. An instance of
`R || ∑ Z` is the number of jobs, the number of machines, the due dates of the jobs and then the
processing times machine by machine.
-/

namespace Lax117284Proofs.Machine.JitSem

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.TokModel
open Lax117284Proofs.Machine.InstSem (numsOf)

/-! ### The format -/

/-- What is expected after the two counts and `j` further numbers, `ex n m` being the number of
entries that follow the table. -/
def kindJ (n m j : ℕ) : Kind := if j < n + m * n then .num else .done

/-- The format: the two counts, then the table and `ex n m` more numbers. -/
def EJ : Format := fun ts =>
  match ts with
  | .num n :: .num m :: rest => kindJ n m rest.length
  | [] => .num
  | [_] => .num
  | _ => .done

lemma EJ_cons (n m : ℕ) (rest : List Tok) :
    EJ (.num n :: .num m :: rest) = kindJ n m rest.length := rfl

/-- A stream of numbers of the right length for its counts. -/
def ShapeJ (ns : List ℕ) : Prop :=
  2 ≤ ns.length ∧ ns.length = 2 + (ns.getD 0 0 + ns.getD 1 0 * ns.getD 0 0)

/-- The numbers of a stream of number tokens. -/
def numsOfJ (ts : List Tok) : List ℕ := ts.map fun t => match t with | .num v => v | .bit _ => 0

lemma map_numsOfJ : ∀ ts : List Tok, (∀ t ∈ ts, t.kind = .num) → ts = (numsOfJ ts).map Tok.num
  | [], _ => rfl
  | t :: r, h => by
      have ht := h t (by simp)
      obtain ⟨v, rfl⟩ : ∃ v, t = .num v := by cases t <;> simp_all [Tok.kind]
      have := map_numsOfJ r (fun u hu => h u (by simp [hu]))
      simp only [numsOfJ, List.map_cons, List.map_map] at this ⊢
      rw [← this]

theorem conformsJ_of_shape {ns : List ℕ} (h : ShapeJ ns) :
    Conforms (EJ) (ns.map Tok.num) := by
  obtain ⟨h2, hl⟩ := h
  obtain ⟨n, m, rest, rfl⟩ : ∃ n m rest, ns = n :: m :: rest := by
    rcases ns with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp at h2
    exact ⟨a, b, rest, rfl⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ, List.length_cons] at hl
  refine ⟨fun k hk => ?_, ?_⟩
  · simp only [List.length_map, List.length_cons] at hk
    rcases k with _ | _ | k
    · simp [EJ, Tok.kind]
    · simp [EJ, Tok.kind]
    · simp only [List.map_cons, List.getD_cons_succ, List.take_succ_cons]
      rw [EJ_cons]
      simp only [List.length_take, List.length_map]
      have hk' : k < rest.length := by omega
      have : k < n + m * n := by omega
      simp [kindJ, this, Tok.kind, List.getD_eq_getElem?_getD, List.getElem?_map, hk']
  · simp only [List.map_cons]
    rw [EJ_cons]
    simp only [List.length_map]
    have : ¬ rest.length < n + m * n := by omega
    simp [kindJ, this]

theorem shapeJ_of_conforms {ts : List Tok} (h : Conforms (EJ) ts) :
    ∃ ns : List ℕ, ts = ns.map Tok.num ∧ ShapeJ ns := by
  obtain ⟨hf, hd⟩ := h
  have hlen2 : 2 ≤ ts.length := by
    by_contra hlt
    rcases ts with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp [EJ] at hd
    · simp [EJ] at hd
    · simp at hlt
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, ts = a :: b :: rest := by
    rcases ts with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hlen2
    · simp at hlen2
    · exact ⟨a, b, rest, rfl⟩
  have ha : a.kind = .num := by simpa [EJ] using hf 0 (by simp)
  have hb : b.kind = .num := by simpa [EJ] using hf 1 (by simp)
  obtain ⟨n, rfl⟩ : ∃ n, a = .num n := by cases a <;> simp_all [Tok.kind]
  obtain ⟨m, rfl⟩ : ∃ m, b = .num m := by cases b <;> simp_all [Tok.kind]
  rw [EJ_cons] at hd
  have hge : ¬ rest.length < n + m * n := by
    intro hlt; simp [kindJ, hlt] at hd
  have hall : ∀ k < rest.length, k < n + m * n ∧ (rest.getD k (.bit false)).kind = .num := by
    intro k hk
    have h := hf (k + 2) (by simp only [List.length_cons]; omega)
    simp only [List.getD_cons_succ, List.take_succ_cons] at h
    have hE : EJ (.num n :: .num m :: List.take k rest) = kindJ n m k := by
      rw [EJ_cons, List.length_take, Nat.min_eq_left (by omega)]
    rw [hE] at h
    unfold kindJ at h
    by_cases hk2 : k < n + m * n
    · rw [if_pos hk2] at h; exact ⟨hk2, h⟩
    · rw [if_neg hk2] at h
      cases hh : (rest.getD k (.bit false)) <;> simp_all [Tok.kind]
  have hlen : rest.length = n + m * n := by
    have h1 : rest.length ≤ n + m * n := by
      by_contra hgt
      have := (hall (n + m * n) (by omega)).1
      omega
    omega
  have hnum : ∀ t ∈ rest, t.kind = .num := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
    have := (hall k hk).2
    rwa [List.getD_eq_getElem _ _ hk] at this
  refine ⟨n :: m :: numsOfJ rest, ?_, ?_⟩
  · simp only [List.map_cons]
    rw [← map_numsOfJ rest hnum]
  · refine ⟨by simp, ?_⟩
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.length_cons, numsOfJ,
      List.length_map]
    omega


/-! ### The numbers of an instance -/

lemma finRange_map_val {α : Type} (n : ℕ) (G : ℕ → α) :
    (List.finRange n).map (fun j : Fin n => G j) = (List.range n).map G := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

lemma numCode_flatMap' {α : Type} (L : List α) (f : α → List ℕ) :
    numCode (L.flatMap f) = L.flatMap fun a => numCode (f a) := by
  simp [numCode, List.flatMap_assoc]

lemma flatMap_single {α β : Type} (l : List α) (f : α → β) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

open Lax117284.JustInTime in
/-- The numbers of an instance: the counts, the due dates, and the processing times machine by
machine. -/
def jitToks (R : Lax117284.JustInTime.Instance) : List ℕ :=
  [R.jobs, R.machines] ++ (List.finRange R.jobs).map (fun j => R.d j) ++
    (List.finRange R.machines).flatMap fun i => (List.finRange R.jobs).map fun j => R.p i j

theorem encodeInstance_eq (R : Lax117284.JustInTime.Instance) :
    Lax117284.JustInTime.encodeInstance R = numCode (jitToks R) := by
  unfold Lax117284.JustInTime.encodeInstance jitToks
  have hd : numCode ((List.finRange R.jobs).map fun j => R.d j) =
      (List.finRange R.jobs).flatMap fun j => encodeNat (R.d j) := by
    simp [numCode, List.flatMap_map]
  have hp : numCode ((List.finRange R.machines).flatMap fun i =>
      (List.finRange R.jobs).map fun j => R.p i j) =
      (List.finRange R.machines).flatMap fun i =>
        (List.finRange R.jobs).flatMap fun j => encodeNat (R.p i j) := by
    rw [numCode_flatMap']
    exact List.flatMap_congr fun i _ => by simp [numCode, List.flatMap_map]
  rw [numCode_append, numCode_append, hd, hp]
  simp [numCode]

theorem jitToks_length (R : Lax117284.JustInTime.Instance) :
    (jitToks R).length = 2 + (R.jobs + R.machines * R.jobs) := by
  unfold jitToks
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_finRange, List.length_flatMap]
  have : ∀ i : Fin R.machines, ((List.finRange R.jobs).map fun j => R.p i j).length = R.jobs :=
    fun i => by simp
  simp only [this, List.map_const', List.sum_replicate, smul_eq_mul, List.length_finRange]
  omega

/-- Every job takes some time and is not due before it starts. -/
def ValidJ (ns : List ℕ) : Prop :=
  ∀ t < ns.getD 1 0 * ns.getD 0 0,
    0 < ns.getD (2 + ns.getD 0 0 + t) 0 ∧
      ns.getD (2 + ns.getD 0 0 + t) 0 ≤ ns.getD (2 + t % ns.getD 0 0) 0

lemma range_map_getD (ns : List ℕ) (a k : ℕ) (h : a + k ≤ ns.length) :
    (List.range k).map (fun j => ns.getD (a + j) 0) = (ns.drop a).take k := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    simp only [List.length_map, List.length_range] at h1
    rw [List.getD_eq_getElem _ _ (by omega)]

/-- The instance a valid stream describes. -/
def instJ (ns : List ℕ) (hv : ValidJ ns) : Lax117284.JustInTime.Instance where
  jobs := ns.getD 0 0
  machines := ns.getD 1 0
  p i j := ns.getD (2 + ns.getD 0 0 + (i * ns.getD 0 0 + j)) 0
  d j := ns.getD (2 + j) 0
  p_pos i j := by
    have hn : 0 < ns.getD 0 0 := Nat.pos_of_ne_zero (fun h => by have := j.isLt; omega)
    have ht : (i : ℕ) * ns.getD 0 0 + j < ns.getD 1 0 * ns.getD 0 0 := InstSem.cell_lt i.isLt j.isLt
    have := (hv _ ht).1
    exact this
  p_le_d i j := by
    have hn : 0 < ns.getD 0 0 := Nat.pos_of_ne_zero (fun h => by have := j.isLt; omega)
    have ht : (i : ℕ) * ns.getD 0 0 + j < ns.getD 1 0 * ns.getD 0 0 := InstSem.cell_lt i.isLt j.isLt
    have h := (hv _ ht).2
    have e : ((i : ℕ) * ns.getD 0 0 + j) % ns.getD 0 0 = j := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
    rw [e] at h
    exact h

theorem jitToks_instJ (ns : List ℕ) (hv : ValidJ ns) (h2 : 2 ≤ ns.length)
    (hl : ns.length = 2 + (ns.getD 0 0 + ns.getD 1 0 * ns.getD 0 0)) :
    jitToks (instJ ns hv) = ns := by
  unfold jitToks
  have hj : (instJ ns hv).jobs = ns.getD 0 0 := rfl
  have hm : (instJ ns hv).machines = ns.getD 1 0 := rfl
  show [ns.getD 0 0, ns.getD 1 0] ++
    (List.finRange (ns.getD 0 0)).map (fun j : Fin (ns.getD 0 0) => ns.getD (2 + j) 0) ++
    (List.finRange (ns.getD 1 0)).flatMap (fun i : Fin (ns.getD 1 0) =>
      (List.finRange (ns.getD 0 0)).map fun j : Fin (ns.getD 0 0) =>
        ns.getD (2 + ns.getD 0 0 + (i * ns.getD 0 0 + j)) 0) = ns
  have e1 : (List.finRange (ns.getD 0 0)).map (fun j : Fin (ns.getD 0 0) => ns.getD (2 + j) 0)
      = (List.range (ns.getD 0 0)).map (fun j => ns.getD (2 + j) 0) :=
    finRange_map_val _ (fun j => ns.getD (2 + j) 0)
  have e2 : (List.finRange (ns.getD 1 0)).flatMap (fun i : Fin (ns.getD 1 0) =>
      (List.finRange (ns.getD 0 0)).map fun j : Fin (ns.getD 0 0) =>
        ns.getD (2 + ns.getD 0 0 + (i * ns.getD 0 0 + j)) 0)
      = (List.range (ns.getD 1 0 * ns.getD 0 0)).map
          (fun t => ns.getD (2 + ns.getD 0 0 + t) 0) := by
    rw [flatMap_finRange]
    have : ∀ a ∈ List.range (ns.getD 1 0), (if h : a < ns.getD 1 0 then
        (List.finRange (ns.getD 0 0)).map fun j : Fin (ns.getD 0 0) =>
          ns.getD (2 + ns.getD 0 0 + (a * ns.getD 0 0 + j)) 0 else []) =
        (List.range (ns.getD 0 0)).flatMap (fun b =>
          [ns.getD (2 + ns.getD 0 0 + (a * ns.getD 0 0 + b)) 0]) := by
      intro a ha
      rw [dif_pos (List.mem_range.mp ha), finRange_map_val (ns.getD 0 0)
        (fun j => ns.getD (2 + ns.getD 0 0 + (a * ns.getD 0 0 + j)) 0), flatMap_single]
    rw [List.flatMap_congr this,
      flatMap_rows (fun t => [ns.getD (2 + ns.getD 0 0 + t) 0]) (ns.getD 0 0) (ns.getD 1 0),
      flatMap_single]
  rw [e1, e2, range_map_getD ns 2 _ (by omega),
    range_map_getD ns (2 + ns.getD 0 0) _ (by omega)]
  obtain ⟨n, m, rest, rfl⟩ : ∃ n m rest, ns = n :: m :: rest := by
    rcases ns with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp at h2
    exact ⟨a, b, rest, rfl⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ, List.length_cons] at hl ⊢
  simp only [List.drop_succ_cons, List.drop_zero]
  rw [show 2 + n = (n + 1) + 1 by ring, List.drop_succ_cons, List.drop_succ_cons]
  simp only [List.cons_append, List.nil_append]
  have h1 : (rest.drop n).take (m * n) = rest.drop n :=
    List.take_of_length_le (by simp only [List.length_drop]; omega)
  rw [List.cons_inj_right, List.cons_inj_right, h1, List.take_append_drop]

/-! ### The gate -/

/-- The due date of job `j`, and `1` outside the instance. -/
def dA (R : Lax117284.JustInTime.Instance) (j : ℕ) : ℕ :=
  if h : j < R.jobs then R.d ⟨j, h⟩ else 1

/-- The processing time of job `j` on machine `i`, and `1` outside the instance. -/
def pA (R : Lax117284.JustInTime.Instance) (i j : ℕ) : ℕ :=
  if h : i < R.machines then if h' : j < R.jobs then R.p ⟨i, h⟩ ⟨j, h'⟩ else 1 else 1

lemma jitToks_eq (R : Lax117284.JustInTime.Instance) :
    jitToks R = [R.jobs, R.machines] ++ (List.range R.jobs).map (dA R) ++
      (List.range (R.machines * R.jobs)).map (fun t => pA R (t / R.jobs) (t % R.jobs)) := by
  unfold jitToks
  congr 1
  · congr 1
    have := finRange_map_val R.jobs (dA R)
    rw [← this]
    refine List.map_congr_left fun j _ => ?_
    simp [dA, j.isLt]
  · rw [flatMap_finRange]
    rcases Nat.eq_zero_or_pos R.jobs with hn | hn
    · have h0 : R.machines * R.jobs = 0 := by rw [hn]; simp
      rw [h0]
      simp only [List.range_zero, List.map_nil]
      apply List.eq_nil_iff_forall_not_mem.2
      intro x hx
      rw [List.mem_flatMap] at hx
      obtain ⟨a, -, hx⟩ := hx
      split at hx
      · rw [List.mem_map] at hx
        obtain ⟨j, -, -⟩ := hx
        exact absurd j.isLt (by omega)
      · simp at hx
    · have hstep : ∀ a ∈ List.range R.machines, (if h : a < R.machines then
          (List.finRange R.jobs).map fun j : Fin R.jobs => R.p ⟨a, h⟩ j else []) =
          (List.range R.jobs).flatMap (fun b =>
            [pA R ((a * R.jobs + b) / R.jobs) ((a * R.jobs + b) % R.jobs)]) := by
        intro a ha
        have ha' := List.mem_range.mp ha
        have hm := finRange_map_val R.jobs (fun j => pA R a j)
        have e : (List.finRange R.jobs).map (fun j : Fin R.jobs => R.p ⟨a, ha'⟩ j) =
            (List.finRange R.jobs).map (fun j : Fin R.jobs => pA R a j) :=
          List.map_congr_left fun j _ => by simp [pA, ha', j.isLt]
        rw [dif_pos ha', e, hm, ← flatMap_single]
        refine List.flatMap_congr fun b hb => ?_
        have hb' := List.mem_range.mp hb
        have e1 : (a * R.jobs + b) / R.jobs = a := by
          rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hb', Nat.add_zero]
        have e2 : (a * R.jobs + b) % R.jobs = b := by
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb']
        rw [e1, e2]
      rw [List.flatMap_congr hstep,
        flatMap_rows (fun t => [pA R (t / R.jobs) (t % R.jobs)]) R.jobs R.machines,
        flatMap_single]

theorem jit_iff (w : Word) :
    (∃ R : Lax117284.JustInTime.Instance, Lax117284.JustInTime.encodeInstance R = w) ↔
      ∃ ns : List ℕ, w = numCode ns ∧ ShapeJ ns ∧ ValidJ ns := by
  constructor
  · rintro ⟨R, hw⟩
    have hl := jitToks_length R
    have he := jitToks_eq R
    have h0 : (jitToks R).getD 0 0 = R.jobs := by rw [he]; simp
    have h1 : (jitToks R).getD 1 0 = R.machines := by rw [he]; simp
    refine ⟨jitToks R, by rw [← hw, encodeInstance_eq], ⟨by omega, ?_⟩, ?_⟩
    · rw [h0, h1, hl]
    · intro t ht
      rw [h0, h1] at ht
      rw [h0]
      have hn : 0 < R.jobs := Nat.pos_of_ne_zero (fun h => by rw [h] at ht; simp at ht)
      have hi : t / R.jobs < R.machines := by
        rw [Nat.div_lt_iff_lt_mul hn]
        have := Nat.mul_comm R.machines R.jobs
        omega
      have hj : t % R.jobs < R.jobs := Nat.mod_lt _ hn
      have hp : (jitToks R).getD (2 + R.jobs + t) 0 = pA R (t / R.jobs) (t % R.jobs) := by
        rw [he, List.getD_append_right _ _ _ _ (by simp; omega)]
        simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
          List.length_range]
        rw [show 2 + R.jobs + t - (0 + 1 + 1 + R.jobs) = t by omega,
          List.getD_eq_getElem _ _ (by simp; exact ht)]
        simp
      have hd : (jitToks R).getD (2 + t % R.jobs) 0 = dA R (t % R.jobs) := by
        rw [he, List.getD_append _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp)]
        simp only [List.length_cons, List.length_nil]
        rw [show 2 + t % R.jobs - (0 + 1 + 1) = t % R.jobs by omega,
          List.getD_eq_getElem _ _ (by simp; omega)]
        simp
      rw [hp, hd]
      have h1 := R.p_pos ⟨t / R.jobs, hi⟩ ⟨t % R.jobs, hj⟩
      have h2 := R.p_le_d ⟨t / R.jobs, hi⟩ ⟨t % R.jobs, hj⟩
      simp only [pA, dA, dif_pos hi, dif_pos hj]
      exact ⟨h1, h2⟩
  · rintro ⟨ns, hw, ⟨h2, hl⟩, hv⟩
    refine ⟨instJ ns hv, ?_⟩
    rw [hw, encodeInstance_eq, jitToks_instJ ns hv h2 hl]

/-! ### The image -/

/-- The numbers of the image: the counts, the table of `(p, d)` read off the stream, and the
parameter `1`. -/
def outJ (ns : List ℕ) : List ℕ :=
  [ns.getD 0 0, ns.getD 1 0] ++
    (List.range (ns.getD 1 0 * ns.getD 0 0)).flatMap
      (fun t => [ns.getD (2 + ns.getD 0 0 + t) 0, ns.getD (2 + t % ns.getD 0 0) 0]) ++ [1]

/-- **The numbers of the constructed instance.** -/
theorem instToks_instJ (ns : List ℕ) (hv : ValidJ ns) :
    InstSem.instToks (Lax117284.Theorem11.inst (instJ ns hv)) =
      [ns.getD 0 0, ns.getD 1 0] ++
        (List.range (ns.getD 1 0 * ns.getD 0 0)).flatMap
          (fun t => [ns.getD (2 + ns.getD 0 0 + t) 0, ns.getD (2 + t % ns.getD 0 0) 0]) := by
  unfold InstSem.instToks
  show [ns.getD 0 0, ns.getD 1 0] ++ (List.range (ns.getD 1 0 * ns.getD 0 0)).flatMap (fun t =>
    [(Lax117284.Theorem11.inst (instJ ns hv)).pAt (t / ns.getD 0 0) (t % ns.getD 0 0),
     (Lax117284.Theorem11.inst (instJ ns hv)).dAt (t / ns.getD 0 0) (t % ns.getD 0 0)]) = _
  congr 1
  refine List.flatMap_congr fun t ht => ?_
  have ht' : t < ns.getD 1 0 * ns.getD 0 0 := List.mem_range.mp ht
  have hn : 0 < ns.getD 0 0 := Nat.pos_of_ne_zero (fun h => by rw [h] at ht'; simp at ht')
  have h1 : t / ns.getD 0 0 < ns.getD 1 0 := by rw [Nat.div_lt_iff_lt_mul hn]; exact ht'
  have h2 : t % ns.getD 0 0 < ns.getD 0 0 := Nat.mod_lt _ hn
  have e : t / ns.getD 0 0 * ns.getD 0 0 + t % ns.getD 0 0 = t := by
    have := Nat.div_add_mod t (ns.getD 0 0)
    rw [Nat.mul_comm] at this
    omega
  simp only [Instance.pAt, Instance.dAt]
  have h1' : t / ns.getD 0 0 < (Lax117284.Theorem11.inst (instJ ns hv)).days := h1
  have h2' : t % ns.getD 0 0 < (Lax117284.Theorem11.inst (instJ ns hv)).clients := h2
  rw [dif_pos h1', dif_pos h2', dif_pos h1', dif_pos h2']
  show [ns.getD (2 + ns.getD 0 0 + (t / ns.getD 0 0 * ns.getD 0 0 + t % ns.getD 0 0)) 0,
    ns.getD (2 + t % ns.getD 0 0) 0] = _
  rw [e]

/-- **The reduction writes the numbers of the constructed instance.** -/
theorem t11_eq (ns : List ℕ) (hv : ValidJ ns) (hs : ShapeJ ns) :
    Lax117284.Theorem11.reduce (numCode ns) = numCode (outJ ns) := by
  classical
  obtain ⟨h2, hl⟩ := hs
  have hI : Lax117284.JustInTime.encodeInstance (instJ ns hv) = numCode ns := by
    rw [encodeInstance_eq, jitToks_instJ ns hv h2 hl]
  have hg : ∃ R : Lax117284.JustInTime.Instance,
      Lax117284.JustInTime.encodeInstance R = numCode ns := ⟨instJ ns hv, hI⟩
  unfold Lax117284.Theorem11.reduce
  rw [dif_pos hg]
  have key : ∀ R' : Lax117284.JustInTime.Instance,
      Lax117284.JustInTime.encodeInstance R' = numCode ns →
      encodeUniform (Lax117284.Theorem11.inst R') 1 = numCode (outJ ns) := by
    intro R' h'
    have := SourceInjectivity.jit_encode_inj (h'.trans hI.symm)
    subst this
    rw [encodeUniform, InstSem.encodeInstance_eq, instToks_instJ ns hv]
    unfold outJ
    simp only [numCode_append, List.append_assoc, numCode_cons, numCode_nil, List.append_nil]
  exact key _ hg.choose_spec

/-- **A word that is not the code of an admissible stream is rejected.** -/
theorem t11_rej (w : Word)
    (h : ¬ ∃ ns : List ℕ, w = numCode ns ∧ ShapeJ ns ∧ ValidJ ns) :
    Lax117284.Theorem11.reduce w = rejected := by
  classical
  unfold Lax117284.Theorem11.reduce
  rw [dif_neg (fun hg => h ((jit_iff w).1 hg))]

end Lax117284Proofs.Machine.JitSem
