import Lax117284Proofs.Machine.Lists
import Lax117284Proofs.Machine.TokModel
import Lax117284Proofs.Injectivity

/-!
An instance as a stream of numbers: the two counts, then a pair for every cell of the table of
jobs, and the format that accepts exactly those streams, with a number of further entries that
depends on the two counts.
-/

namespace Lax117284Proofs.Machine.InstSem

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.TokModel

/-! ### The numbers of an instance -/

/-- The numbers of an instance: the counts, then the processing time and the due date of every
cell of the table, row by row. -/
def instToks (I : Instance) : List ℕ :=
  [I.clients, I.days] ++ (List.range (I.days * I.clients)).flatMap fun t =>
    [I.pAt (t / I.clients) (t % I.clients), I.dAt (t / I.clients) (t % I.clients)]

lemma numCode_flatMap (l : List ℕ) (f : ℕ → List ℕ) :
    numCode (l.flatMap f) = l.flatMap fun a => numCode (f a) := by
  simp [numCode, List.flatMap_assoc]

theorem encodeInstance_eq (I : Instance) : encodeInstance I = numCode (instToks I) := by
  unfold encodeInstance instToks
  rw [numCode_append, numCode_flatMap, flatMap_finRange]
  simp only [numCode_cons, numCode_nil, List.append_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  congr 1
  rw [← flatMap_rows (fun t => encodeNat (I.pAt (t / I.clients) (t % I.clients)) ++
      encodeNat (I.dAt (t / I.clients) (t % I.clients))) I.clients I.days]
  congr 1
  refine List.flatMap_congr fun a ha => ?_
  have ha' : a < I.days := List.mem_range.mp ha
  rw [dif_pos ha', flatMap_finRange]
  refine List.flatMap_congr fun b hb => ?_
  have hb' : b < I.clients := List.mem_range.mp hb
  rw [dif_pos hb']
  have hn : 0 < I.clients := by omega
  have e1 : (a * I.clients + b) / I.clients = a := by
    rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hb', Nat.add_zero]
  have e2 : (a * I.clients + b) % I.clients = b := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb']
  rw [e1, e2]
  have := Instance.pAt_coe I ⟨a, ha'⟩ ⟨b, hb'⟩
  have h2 := Instance.dAt_coe I ⟨a, ha'⟩ ⟨b, hb'⟩
  simp only [Fin.val_mk] at this h2
  rw [this, h2]

theorem instToks_length (I : Instance) : (instToks I).length = 2 + 2 * (I.days * I.clients) := by
  unfold instToks
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [RecList.length_flatMap_const (fun t => [I.pAt (t / I.clients) (t % I.clients),
    I.dAt (t / I.clients) (t % I.clients)]) 2 (fun _ => rfl)]

/-! ### The format -/

/-- What is expected after the two counts and `j` further numbers, `ex n m` being the number of
entries that follow the table. -/
def kindI (ex : ℕ → ℕ → ℕ) (n m j : ℕ) : Kind := if j < 2 * (m * n) + ex n m then .num else .done

/-- The format: the two counts, then the table and `ex n m` more numbers. -/
def EI (ex : ℕ → ℕ → ℕ) : Format := fun ts =>
  match ts with
  | .num n :: .num m :: rest => kindI ex n m rest.length
  | [] => .num
  | [_] => .num
  | _ => .done

lemma EI_cons (ex : ℕ → ℕ → ℕ) (n m : ℕ) (rest : List Tok) :
    EI ex (.num n :: .num m :: rest) = kindI ex n m rest.length := rfl

/-- A stream of numbers of the right length for its counts. -/
def Shape (ex : ℕ → ℕ → ℕ) (ns : List ℕ) : Prop :=
  2 ≤ ns.length ∧ ns.length = 2 + 2 * (ns.getD 1 0 * ns.getD 0 0) + ex (ns.getD 0 0) (ns.getD 1 0)

/-- The numbers of a stream of number tokens. -/
def numsOf (ts : List Tok) : List ℕ := ts.map fun t => match t with | .num v => v | .bit _ => 0

lemma map_numsOf : ∀ ts : List Tok, (∀ t ∈ ts, t.kind = .num) → ts = (numsOf ts).map Tok.num
  | [], _ => rfl
  | t :: r, h => by
      have ht := h t (by simp)
      obtain ⟨v, rfl⟩ : ∃ v, t = .num v := by cases t <;> simp_all [Tok.kind]
      have := map_numsOf r (fun u hu => h u (by simp [hu]))
      simp only [numsOf, List.map_cons, List.map_map] at this ⊢
      rw [← this]

theorem conforms_of_shape (ex : ℕ → ℕ → ℕ) {ns : List ℕ} (h : Shape ex ns) :
    Conforms (EI ex) (ns.map Tok.num) := by
  obtain ⟨h2, hl⟩ := h
  obtain ⟨n, m, rest, rfl⟩ : ∃ n m rest, ns = n :: m :: rest := by
    rcases ns with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp at h2
    exact ⟨a, b, rest, rfl⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ, List.length_cons] at hl
  refine ⟨fun k hk => ?_, ?_⟩
  · simp only [List.length_map, List.length_cons] at hk
    rcases k with _ | _ | k
    · simp [EI, Tok.kind]
    · simp [EI, Tok.kind]
    · simp only [List.map_cons, List.getD_cons_succ, List.take_succ_cons]
      rw [EI_cons]
      simp only [List.length_take, List.length_map]
      have hk' : k < rest.length := by omega
      have : k < 2 * (m * n) + ex n m := by omega
      simp [kindI, this, Tok.kind, List.getD_eq_getElem?_getD, List.getElem?_map, hk']
  · simp only [List.map_cons]
    rw [EI_cons]
    simp only [List.length_map]
    have : ¬ rest.length < 2 * (m * n) + ex n m := by omega
    simp [kindI, this]

theorem shape_of_conforms (ex : ℕ → ℕ → ℕ) {ts : List Tok} (h : Conforms (EI ex) ts) :
    ∃ ns : List ℕ, ts = ns.map Tok.num ∧ Shape ex ns := by
  obtain ⟨hf, hd⟩ := h
  have hlen2 : 2 ≤ ts.length := by
    by_contra hlt
    rcases ts with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp [EI] at hd
    · simp [EI] at hd
    · simp at hlt
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, ts = a :: b :: rest := by
    rcases ts with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hlen2
    · simp at hlen2
    · exact ⟨a, b, rest, rfl⟩
  have ha : a.kind = .num := by simpa [EI] using hf 0 (by simp)
  have hb : b.kind = .num := by simpa [EI] using hf 1 (by simp)
  obtain ⟨n, rfl⟩ : ∃ n, a = .num n := by cases a <;> simp_all [Tok.kind]
  obtain ⟨m, rfl⟩ : ∃ m, b = .num m := by cases b <;> simp_all [Tok.kind]
  rw [EI_cons] at hd
  have hge : ¬ rest.length < 2 * (m * n) + ex n m := by
    intro hlt; simp [kindI, hlt] at hd
  have hall : ∀ k < rest.length, k < 2 * (m * n) + ex n m ∧ (rest.getD k (.bit false)).kind = .num := by
    intro k hk
    have h := hf (k + 2) (by simp only [List.length_cons]; omega)
    simp only [List.getD_cons_succ, List.take_succ_cons] at h
    have hE : EI ex (.num n :: .num m :: List.take k rest) = kindI ex n m k := by
      rw [EI_cons, List.length_take, Nat.min_eq_left (by omega)]
    rw [hE] at h
    unfold kindI at h
    by_cases hk2 : k < 2 * (m * n) + ex n m
    · rw [if_pos hk2] at h; exact ⟨hk2, h⟩
    · rw [if_neg hk2] at h
      cases hh : (rest.getD k (.bit false)) <;> simp_all [Tok.kind]
  have hlen : rest.length = 2 * (m * n) + ex n m := by
    have h1 : rest.length ≤ 2 * (m * n) + ex n m := by
      by_contra hgt
      have := (hall (2 * (m * n) + ex n m) (by omega)).1
      omega
    omega
  have hnum : ∀ t ∈ rest, t.kind = .num := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
    have := (hall k hk).2
    rwa [List.getD_eq_getElem _ _ hk] at this
  refine ⟨n :: m :: numsOf rest, ?_, ?_⟩
  · simp only [List.map_cons]
    rw [← map_numsOf rest hnum]
  · refine ⟨by simp, ?_⟩
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.length_cons, numsOf,
      List.length_map]
    omega

/-! ### Valid streams are the numbers of instances -/

/-- Every job of the table takes some time and is not due before it starts. -/
def Valid (ns : List ℕ) : Prop :=
  ∀ t < ns.getD 1 0 * ns.getD 0 0,
    0 < ns.getD (2 + 2 * t) 0 ∧ ns.getD (2 + 2 * t) 0 ≤ ns.getD (2 + 2 * t + 1) 0

lemma cell_lt {m n i j : ℕ} (hi : i < m) (hj : j < n) : i * n + j < m * n := by
  have h1 : (i + 1) * n ≤ m * n := Nat.mul_le_mul_right _ hi
  have h2 : (i + 1) * n = i * n + n := by ring
  omega

/-- The instance a valid stream of numbers describes. -/
def instOf (ns : List ℕ) (hv : Valid ns) : Instance where
  clients := ns.getD 0 0
  days := ns.getD 1 0
  p i j := ns.getD (2 + 2 * (i * ns.getD 0 0 + j)) 0
  d i j := ns.getD (2 + 2 * (i * ns.getD 0 0 + j) + 1) 0
  p_pos i j := (hv _ (cell_lt i.isLt j.isLt)).1
  p_le_d i j := (hv _ (cell_lt i.isLt j.isLt)).2

lemma instOf_pAt (ns : List ℕ) (hv : Valid ns) {t : ℕ} (ht : t < ns.getD 1 0 * ns.getD 0 0) :
    (instOf ns hv).pAt (t / ns.getD 0 0) (t % ns.getD 0 0) = ns.getD (2 + 2 * t) 0 ∧
    (instOf ns hv).dAt (t / ns.getD 0 0) (t % ns.getD 0 0) = ns.getD (2 + 2 * t + 1) 0 := by
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
  have hp := Instance.pAt_coe (instOf ns hv) ⟨t / ns.getD 0 0, h1⟩ ⟨t % ns.getD 0 0, h2⟩
  have hd := Instance.dAt_coe (instOf ns hv) ⟨t / ns.getD 0 0, h1⟩ ⟨t % ns.getD 0 0, h2⟩
  simp only [Fin.val_mk] at hp hd
  rw [hp, hd]
  refine ⟨?_, ?_⟩
  · show ns.getD (2 + 2 * (t / ns.getD 0 0 * ns.getD 0 0 + t % ns.getD 0 0)) 0
      = ns.getD (2 + 2 * t) 0
    rw [e]
  · show ns.getD (2 + 2 * (t / ns.getD 0 0 * ns.getD 0 0 + t % ns.getD 0 0) + 1) 0
      = ns.getD (2 + 2 * t + 1) 0
    rw [e]

/-- The number that follows the table of a uniform stream: the fairness parameter. -/
def paramOf (ns : List ℕ) : ℕ := ns.getD (2 + 2 * (ns.getD 1 0 * ns.getD 0 0)) 0

/-- The uniform format: the counts, the table, and one number more. -/
abbrev eU : ℕ → ℕ → ℕ := fun _ _ => 1

theorem instToks_instOf (ns : List ℕ) (hv : Valid ns) (hs : Shape eU ns) :
    instToks (instOf ns hv) ++ [paramOf ns] = ns := by
  obtain ⟨h2, hl⟩ := hs
  have hcount : ns.length = 3 + 2 * (ns.getD 1 0 * ns.getD 0 0) := by simp only [eU] at hl; omega
  have hcl : (instOf ns hv).clients = ns.getD 0 0 := rfl
  have hdy : (instOf ns hv).days = ns.getD 1 0 := rfl
  unfold instToks
  rw [hcl, hdy]
  have hmap : (List.range (ns.getD 1 0 * ns.getD 0 0)).flatMap (fun t =>
      [(instOf ns hv).pAt (t / ns.getD 0 0) (t % ns.getD 0 0),
       (instOf ns hv).dAt (t / ns.getD 0 0) (t % ns.getD 0 0)])
      = (List.range (ns.getD 1 0 * ns.getD 0 0)).flatMap (fun t =>
      [ns.getD (2 + 2 * t) 0, ns.getD (2 + 2 * t + 1) 0]) :=
    List.flatMap_congr fun t ht => by
      have := instOf_pAt ns hv (List.mem_range.mp ht)
      rw [this.1, this.2]
  rw [hmap, flatMap_pairs ns 2 _ (by omega)]
  obtain ⟨n, m, rest, rfl⟩ : ∃ n m rest, ns = n :: m :: rest := by
    rcases ns with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp at h2
    exact ⟨a, b, rest, rfl⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ, List.length_cons, List.drop_succ_cons,
    List.drop_zero, paramOf, Nat.add_assoc] at hcount ⊢
  have hr : rest.length = 2 * (m * n) + 1 := by omega
  have hg : rest.getD (2 * (m * n)) 0 = rest[2 * (m * n)] := List.getD_eq_getElem _ _ (by omega)
  have hlast : rest.take (2 * (m * n)) ++ [rest[2 * (m * n)]'(by omega)] = rest := by
    have h1 := List.take_append_drop (2 * (m * n)) rest
    have h2 : rest.drop (2 * (m * n)) = [rest[2 * (m * n)]'(by omega)] := by
      rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
    rw [h2] at h1
    exact h1
  rw [show 2 + 2 * (m * n) = (2 * (m * n)) + 2 by ring]
  simp only [List.getD_cons_succ]
  rw [hg]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  rw [List.cons_inj_right, List.cons_inj_right]
  exact hlast

lemma instToks_getD_cell (I : Instance) {t : ℕ} (ht : t < I.days * I.clients) :
    (instToks I).getD (2 + 2 * t) 0 = I.pAt (t / I.clients) (t % I.clients) ∧
    (instToks I).getD (2 + 2 * t + 1) 0 = I.dAt (t / I.clients) (t % I.clients) := by
  unfold instToks
  have hf : ∀ k, ([I.pAt (k / I.clients) (k % I.clients), I.dAt (k / I.clients) (k % I.clients)]
      : List ℕ).length = 2 := fun _ => rfl
  have key := fun r (hr : r < 2) => RecList.getD_flatMap_const
    (fun k => [I.pAt (k / I.clients) (k % I.clients), I.dAt (k / I.clients) (k % I.clients)])
    2 hf (I.days * I.clients) t r ht hr 0
  refine ⟨?_, ?_⟩
  · rw [show 2 + 2 * t = 2 + 2 * t + 0 by rfl]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_cons, List.length_nil]; omega)]
    simp only [List.length_cons, List.length_nil]
    rw [show 2 + 2 * t + 0 - 2 = 2 * t + 0 by omega]
    exact key 0 (by omega)
  · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_cons, List.length_nil]; omega)]
    simp only [List.length_cons, List.length_nil]
    rw [show 2 + 2 * t + 1 - 2 = 2 * t + 1 by omega]
    exact key 1 (by omega)

lemma instToks_getD_head (I : Instance) :
    (instToks I).getD 0 0 = I.clients ∧ (instToks I).getD 1 0 = I.days := by
  unfold instToks
  exact ⟨by simp, by simp⟩

/-- **The numbers of the instances of a given number of days and clients are the valid
streams.** -/
theorem uniform_iff (w : Word) :
    (∃ (I : Instance) (k : ℕ), encodeUniform I k = w ∧ 0 < I.days) ↔
      ∃ ns : List ℕ, w = numCode ns ∧ Shape eU ns ∧ Valid ns ∧ 0 < ns.getD 1 0 := by
  constructor
  · rintro ⟨I, k, hw, hd⟩
    refine ⟨instToks I ++ [k], ?_, ?_, ?_, ?_⟩
    · rw [← hw, encodeUniform, encodeInstance_eq, numCode_append]
      simp
    · have hl := instToks_length I
      have h0 : (instToks I ++ [k]).getD 0 0 = I.clients := by
        rw [List.getD_append _ _ _ _ (by omega)]; exact (instToks_getD_head I).1
      have h1 : (instToks I ++ [k]).getD 1 0 = I.days := by
        rw [List.getD_append _ _ _ _ (by omega)]; exact (instToks_getD_head I).2
      refine ⟨by simp; omega, ?_⟩
      rw [h0, h1]
      simp only [List.length_append, List.length_singleton, eU, hl]
    · intro t ht
      have h0 : (instToks I ++ [k]).getD 0 0 = I.clients := by
        rw [List.getD_append _ _ _ _ (by have := instToks_length I; omega)]
        exact (instToks_getD_head I).1
      have h1 : (instToks I ++ [k]).getD 1 0 = I.days := by
        rw [List.getD_append _ _ _ _ (by have := instToks_length I; omega)]
        exact (instToks_getD_head I).2
      rw [h0, h1] at ht
      have ht' : t < I.days * I.clients := ht
      have hl := instToks_length I
      have hp := instToks_getD_cell I ht'
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), hp.1, hp.2]
      exact ⟨I.pAt_pos _ _, I.pAt_le_dAt _ _⟩
    · have hl := instToks_length I
      rw [List.getD_append _ _ _ _ (by omega), (instToks_getD_head I).2]
      exact hd
  · rintro ⟨ns, hw, hs, hv, hd⟩
    refine ⟨instOf ns hv, paramOf ns, ?_, hd⟩
    rw [hw, encodeUniform, encodeInstance_eq]
    conv_rhs => rw [← instToks_instOf ns hv hs]
    rw [numCode_append]
    simp [numCode]

end Lax117284Proofs.Machine.InstSem
