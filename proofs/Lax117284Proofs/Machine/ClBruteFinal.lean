import Mathlib.Tactic
import Lax117284Proofs.ClientsWord
import Lax808846Proofs.Tactic

/-! ### `Lax117284Proofs.Machine.ClBruteDefs` -/

section
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

end

/-! ### `Lax117284Proofs.Machine.ClBruteCom` -/

section
/-!
The brute force as an IMP+ command.

The array `bfsc` is the schedule, one bit per cell (`i * n + j` is client `j` on day `i`), read as
a binary counter. One pass over the counter checks the bits (`evalCom`: no two conflicting
clients on one day, every client served on at least `k` days), records a success, and adds one
(`odoCom`), the carry out of the last cell ending the loop.

Every test is arithmetic on the values `0` and `1` (`ltF e f` is `1` exactly when `e < f`), so
that a pass costs the same whatever it finds.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

abbrev V (s : String) : Expr := .var s
abbrev lit (n : ℕ) : Expr := .lit n
abbrev asg (x : String) (e : Expr) : Com := .assign x e

/-- Right-nested sequence. -/
def seqs : List Com → Com
  | [] => .skip
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- `x := 0; while x < m do c`. -/
abbrev forZ (x m : String) (c : Com) : Com :=
  .seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) c)

/-- `1` when `e < f`, `0` otherwise. -/
abbrev ltF (e f : Expr) : Expr := .sub (lit 1) (.sub (lit 1) (.sub f e))

/-! ### One pair of clients `a < b` of a day -/

/-- The pair `(a, b)` on day `i`: does it clash? Remove it from the flag. -/
def bStep : Com := seqs [
  asg "bfqb" (.add (V "bfro") (V "bfb")),
  asg "bfbb" (.get "bfsc" (V "bfqb")),
  asg "bfpb" (.get "X" (.add (lit 2) (V "bfqb"))),
  asg "bfdb" (.get "X" (.add (.add (lit 2) (V "bfmn")) (V "bfqb"))),
  asg "bfsb" (.sub (V "bfdb") (V "bfpb")),
  asg "bfx" (.mul (V "bfba") (V "bfbb")),
  asg "bfx" (.mul (V "bfx") (ltF (V "bfa") (V "bfb"))),
  asg "bfx" (.mul (V "bfx") (ltF (V "bfsa") (V "bfdb"))),
  asg "bfx" (.mul (V "bfx") (ltF (V "bfsb") (V "bfda"))),
  asg "bfok" (.sub (V "bfok") (V "bfx")),
  asg "bfb" (.add (V "bfb") (lit 1))]

/-- The pair loop of one client `a`. -/
abbrev bLoop : Com := forZ "bfb" "n" bStep

/-- Read client `a` of day `i`: its bit, its due date, its start. -/
def aSetup : Com := seqs [
  asg "bfqa" (.add (V "bfro") (V "bfa")),
  asg "bfba" (.get "bfsc" (V "bfqa")),
  asg "bfpa" (.get "X" (.add (lit 2) (V "bfqa"))),
  asg "bfda" (.get "X" (.add (.add (lit 2) (V "bfmn")) (V "bfqa"))),
  asg "bfsa" (.sub (V "bfda") (V "bfpa"))]

/-- One client `a` of day `i` against every client. -/
def aStep : Com := .seq aSetup (.seq bLoop (asg "bfa" (.add (V "bfa") (lit 1))))

/-- One day. -/
def iStep : Com := seqs [
  asg "bfro" (.mul (V "bfi") (V "n")),
  forZ "bfa" "n" aStep,
  asg "bfi" (.add (V "bfi") (lit 1))]

/-- Feasibility: no day serves two conflicting clients. -/
abbrev feasCom : Com := forZ "bfi" "m" iStep

/-! ### Fairness: every client is served on `k` days -/

/-- Add the cell of day `i`, client `j`. -/
def cStep : Com := seqs [
  asg "bfc" (.add (V "bfc") (.get "bfsc" (.add (.mul (V "bfi") (V "n")) (V "bfj")))),
  asg "bfi" (.add (V "bfi") (lit 1))]

/-- Compare the count with `k`; move to the next client. -/
def jTail : Com := seqs [
  asg "bfx" (ltF (V "bfc") (V "k")),
  asg "bfok" (.sub (V "bfok") (V "bfx")),
  asg "bfj" (.add (V "bfj") (lit 1))]

/-- One client: count its days, compare with `k`. -/
def jStep : Com := .seq (asg "bfc" (lit 0)) (.seq (forZ "bfi" "m" cStep) jTail)

abbrev fairCom : Com := forZ "bfj" "n" jStep

/-- The feasibility scan, unless there is no client (then the scan over the days would cost
a number of steps that the word does not bound). -/
def feasG : Com := .ite (.lt (lit 0) (V "n")) feasCom .skip

/-- Test the vector in `bfsc`: `bfok` ends `1` exactly when it is feasible and fair. -/
def evalCom : Com := seqs [asg "bfok" (lit 1), feasG, fairCom]

/-! ### The odometer -/

/-- One cell of the increment: add the carry; the cell keeps the parity, the carry the rest. -/
def oStep : Com := seqs [
  asg "bft" (.add (.get "bfsc" (V "bfq")) (V "bfcy")),
  asg "bfcy" (.div (V "bft") (lit 2)),
  .store "bfsc" (V "bfq") (.sub (V "bft") (.mul (V "bfcy") (lit 2))),
  asg "bfq" (.add (V "bfq") (lit 1))]

/-- Add one to the vector; the carry out of the last cell is `1` exactly when it was the last
vector, and the vector is then all zeros again. -/
def odoCom : Com := .seq (asg "bfcy" (lit 1)) (forZ "bfq" "bfmn" oStep)

/-! ### The search -/

/-- Record a success. -/
def recCom : Com := .ite (.eq (V "bfok") (lit 1)) (asg "bfans" (lit 1)) .skip

/-- Test a vector, record a success, move on. -/
def bodyCom : Com := seqs [evalCom, recCom, odoCom, asg "bfdn" (V "bfcy")]

/-- **The brute force**: `bfans` ends `1` exactly when some vector of `m * n` bits reads a
feasible schedule serving every client on `k` days. -/
def bruteCom : Com := seqs [
  asg "bfmn" (.mul (V "n") (V "m")),
  asg "bfans" (lit 0),
  asg "bfdn" (lit 0),
  .while (.eq (V "bfdn") (lit 0)) bodyCom]

end Lax117284Proofs.Machine.ClBrute

end

/-! ### `Lax117284Proofs.Machine.ClBruteCtx` -/

section
/-!
The context every pass of the brute force runs in: what the word and the value bound say
(`Bd`), and the scalars and arrays no pass but the odometer changes (`Ctx`).
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

/-! ### The value bound -/

/-- The word encodes the instance, and the bound `B` is big enough for it. -/
structure Bd (B : ℕ) (x : List ℕ) (I : Instance) (k : ℕ) : Prop where
  dec : EncodesUniform x I k
  big : 4 * x.length + 64 < B
  xB : ∀ v ∈ x, v < B

variable {B k : ℕ} {x : List ℕ} {I : Instance}

namespace Bd

lemma len (h : Bd B x I k) : x.length = 3 + 2 * (I.days * I.clients) :=
  Lax117284Proofs.ClientsWord.len_eq h.dec

lemma xg (h : Bd B x I k) (j : ℕ) : x.getD j 0 < B := by
  by_cases hj : j < x.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact h.xB _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    have := h.big; omega

lemma mnB (h : Bd B x I k) : I.days * I.clients + 8 < B := by
  have := h.big; have := h.len; omega

lemma nB (h : Bd B x I k) : I.clients < B := by
  have := h.xg 0; rwa [Lax117284Proofs.ClientsWord.x0 h.dec] at this

lemma mB (h : Bd B x I k) : I.days < B := by
  have := h.xg 1; rwa [Lax117284Proofs.ClientsWord.x1 h.dec] at this

lemma kB (h : Bd B x I k) : k < B := by
  have := h.xg (2 + 2 * (I.days * I.clients))
  rwa [Lax117284Proofs.ClientsWord.xk h.dec] at this

end Bd

/-! ### The context -/

/-- What no pass but the odometer changes: the word, the three parameters, the size of the
vector, and the vector itself, `m * n` bits. -/
structure Ctx (x : List ℕ) (I : Instance) (k : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop where
  hx : σ.arrs "X" = x
  hn : σ.vars "n" = I.clients
  hm : σ.vars "m" = I.days
  hk : σ.vars "k" = k
  hmn : σ.vars "bfmn" = I.days * I.clients
  hsc : σ.arrs "bfsc" = arrOf (I.days * I.clients) f
  hf : ∀ r, r < I.days * I.clients → f r ≤ 1

namespace Ctx

variable {f : ℕ → ℕ} {σ : Env}

lemma scLen (h : Ctx x I k f σ) : (σ.arrs "bfsc").length = I.days * I.clients := by
  rw [h.hsc]; simp

lemma scGet (h : Ctx x I k f σ) {r : ℕ} (hr : r < I.days * I.clients) :
    (σ.arrs "bfsc").getD r 0 = f r := by
  rw [h.hsc, getD_arrOf f hr]

lemma xLen (hb : Bd B x I k) (h : Ctx x I k f σ) :
    (σ.arrs "X").length = 3 + 2 * (I.days * I.clients) := by
  rw [h.hx]; exact hb.len

lemma xGet (h : Ctx x I k f σ) (j : ℕ) : (σ.arrs "X").getD j 0 = x.getD j 0 := by
  rw [h.hx]

end Ctx

/-! ### The flags -/

/-- The value of `ltF e f`. -/
lemma ltf_eq (e f : ℕ) : 1 - (1 - (f - e)) = if e < f then 1 else 0 := by
  split_ifs <;> omega

/-- The clash of the pair, as the program computes it. -/
def cl (ba bb a b sa db sb da : ℕ) : ℕ :=
  ba * bb * (1 - (1 - (b - a))) * (1 - (1 - (db - sa))) * (1 - (1 - (da - sb)))

lemma cl_eq {ba bb : ℕ} (hba : ba ≤ 1) (hbb : bb ≤ 1) (a b sa db sb da : ℕ) :
    cl ba bb a b sa db sb da =
      if ba = 1 ∧ bb = 1 ∧ a < b ∧ sa < db ∧ sb < da then 1 else 0 := by
  rw [cl, ltf_eq, ltf_eq, ltf_eq]
  have h1 : ba = 0 ∨ ba = 1 := by omega
  have h2 : bb = 0 ∨ bb = 1 := by omega
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> split_ifs <;> simp_all

end Lax117284Proofs.Machine.ClBrute

end

/-! ### `Lax117284Proofs.Machine.ClBruteFeas1` -/

section
/-!
The pair loop: one client `a` of day `i` against every client `b`.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

/-- The state of the pair loop of client `a` on day `i`. -/
structure BInv (x : List ℕ) (I : Instance) (k : ℕ) (f : ℕ → ℕ) (i a ok0 : ℕ) (σ : Env) : Prop where
  ctx : Ctx x I k f σ
  hi : σ.vars "bfi" = i
  hro : σ.vars "bfro" = i * I.clients
  ha : σ.vars "bfa" = a
  hba : σ.vars "bfba" = f (i * I.clients + a)
  hda : σ.vars "bfda" = I.dAt i a
  hsa : σ.vars "bfsa" = I.dAt i a - I.pAt i a
  hb : σ.vars "bfb" ≤ I.clients
  hok : σ.vars "bfok" ≤ 1
  hiff : σ.vars "bfok" = 1 ↔ ok0 = 1 ∧ ∀ b, b < σ.vars "bfb" → ¬ Bad I f i a b

lemma mul_le1 {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
  calc a * b ≤ 1 * 1 := Nat.mul_le_mul ha hb
    _ = 1 := rfl

set_option maxHeartbeats 1600000 in
theorem bStep_vals (hb : Bd B x I k) (f : ℕ → ℕ) (i a ok0 : ℕ) (hi : i < I.days)
    (ha : a < I.clients) :
    Spec B (fun σ => BInv x I k f i a ok0 σ ∧ σ.vars "bfb" < I.clients) bStep
      (fun σ σ' => σ'.vars "bfok" = σ.vars "bfok" -
          cl (σ.vars "bfba") ((σ.arrs "bfsc").getD (σ.vars "bfro" + σ.vars "bfb") 0)
            (σ.vars "bfa") (σ.vars "bfb") (σ.vars "bfsa")
            ((σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfb")) 0)
            ((σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfb")) 0 -
              (σ.arrs "X").getD (2 + (σ.vars "bfro" + σ.vars "bfb")) 0)
            (σ.vars "bfda") ∧
        σ'.vars "bfb" = σ.vars "bfb" + 1) 65 := by
  run_vcg
  all_goals obtain ⟨hctx, hi', hro, ha', hba, hda, hsa, hb', hok, hiff⟩ := ‹BInv x I k f i a ok0 σ›
  all_goals have hbl : σ.vars "bfb" < I.clients := ‹σ.vars "bfb" < I.clients›
  all_goals have hmn := hb.mnB
  all_goals have hnB := hb.nB
  all_goals have hmB := hb.mB
  all_goals have hkB := hb.kB
  all_goals have hbig := hb.big
  all_goals have hlen := hb.len
  all_goals have hq : σ.vars "bfro" + σ.vars "bfb" < I.days * I.clients := (by
    rw [hro]; exact idx_lt I hi hbl)
  all_goals have hmn' := hctx.hmn
  all_goals have hscb : (σ.arrs "bfsc").getD (σ.vars "bfro" + σ.vars "bfb") 0 ≤ 1 := (by
    rw [hctx.scGet hq]; exact hctx.hf _ hq)
  all_goals have hscl := hctx.scLen
  all_goals have hxl := hctx.xLen hb
  all_goals have hx1 : (σ.arrs "X").getD (2 + (σ.vars "bfro" + σ.vars "bfb")) 0 < B := (by
    rw [hctx.xGet]; exact hb.xg _)
  all_goals have hx2 : (σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfb")) 0 < B := (by
    rw [hctx.xGet]; exact hb.xg _)
  all_goals have hba1 : σ.vars "bfba" ≤ 1 := (by rw [hba]; exact hctx.hf _ (idx_lt I hi ha))
  all_goals have han := hctx.hn
  all_goals have hkk := hctx.hk
  all_goals have hdaB : σ.vars "bfda" < B := (by
    rw [hda, ← Lax117284Proofs.ClientsWord.due_eq hb.dec hi ha]; exact hb.xg _)
  all_goals have hsaB : σ.vars "bfsa" ≤ σ.vars "bfda" := (by rw [hsa, hda]; omega)
  all_goals have p1 := mul_le1 hba1 hscb
  all_goals have p2 := mul_le1 p1 (show 1 - (1 - (σ.vars "bfb" - σ.vars "bfa")) ≤ 1 by omega)
  all_goals have p3 := mul_le1 p2 (show 1 - (1 - ((σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfb")) 0 - σ.vars "bfsa")) ≤ 1 by omega)
  all_goals have p4 := mul_le1 p3 (show 1 - (1 - (σ.vars "bfda" - ((σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfb")) 0 - (σ.arrs "X").getD (2 + (σ.vars "bfro" + σ.vars "bfb")) 0))) ≤ 1 by omega)
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte]
  all_goals try omega
  exact ⟨by unfold cl; rfl, trivial⟩


/-! ### From the values to the invariant -/

lemma lt_succ_forall {Q : ℕ → Prop} {c : ℕ} :
    (∀ b, b < c + 1 → Q b) ↔ (∀ b, b < c → Q b) ∧ Q c := by
  constructor
  · intro h; exact ⟨fun b hb => h b (by omega), h c (by omega)⟩
  · rintro ⟨h1, h2⟩ b hb
    rcases Nat.lt_succ_iff_lt_or_eq.mp hb with h | rfl
    · exact h1 b h
    · exact h2

open Classical in
/-- Removing a clash from the flag. -/
lemma iff_step {ok ok0 b c : ℕ} {Q : ℕ → Prop} (hok : ok ≤ 1)
    (h : ok = 1 ↔ ok0 = 1 ∧ ∀ b', b' < b → ¬ Q b') (hc : c = if Q b then 1 else 0) :
    ok - c = 1 ↔ ok0 = 1 ∧ ∀ b', b' < b + 1 → ¬ Q b' := by
  rw [lt_succ_forall]
  by_cases hq : Q b
  · rw [if_pos hq] at hc; subst hc
    constructor
    · intro h1; omega
    · rintro ⟨-, -, h2⟩; exact absurd hq h2
  · rw [if_neg hq] at hc; subst hc
    rw [Nat.sub_zero, h]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, hq⟩
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩

lemma Ctx.frame {c : Com} {f : ℕ → ℕ} {σ σ' : Env} (h : Ctx x I k f σ)
    (hv : ∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y)
    (ha : ∀ a, a ∉ c.warrs → σ'.arrs a = σ.arrs a)
    (h1 : ∀ y ∈ ["n", "m", "k", "bfmn"], y ∉ c.wvars) (h2 : "X" ∉ c.warrs)
    (h3 : "bfsc" ∉ c.warrs) : Ctx x I k f σ' :=
  ⟨by rw [ha _ h2]; exact h.hx, by rw [hv _ (h1 _ (by simp))]; exact h.hn,
    by rw [hv _ (h1 _ (by simp))]; exact h.hm, by rw [hv _ (h1 _ (by simp))]; exact h.hk,
    by rw [hv _ (h1 _ (by simp))]; exact h.hmn, by rw [ha _ h3]; exact h.hsc, h.hf⟩

lemma Ctx.setVar {f : ℕ → ℕ} {σ : Env} (h : Ctx x I k f σ) {y : String} (v : ℕ)
    (hy : y ≠ "n" ∧ y ≠ "m" ∧ y ≠ "k" ∧ y ≠ "bfmn") : Ctx x I k f (σ.setVar y v) :=
  ⟨h.hx, by rw [vars_setVar, if_neg hy.1.symm]; exact h.hn,
    by rw [vars_setVar, if_neg hy.2.1.symm]; exact h.hm,
    by rw [vars_setVar, if_neg hy.2.2.1.symm]; exact h.hk,
    by rw [vars_setVar, if_neg hy.2.2.2.symm]; exact h.hmn, h.hsc, h.hf⟩

open Classical in
/-- The value the clash expression takes is the truth of `Bad`. -/
lemma cl_bad (hb : Bd B x I k) {f : ℕ → ℕ} {σ : Env} {i a : ℕ} (hi : i < I.days)
    (ha : a < I.clients) (hctx : Ctx x I k f σ) (hro : σ.vars "bfro" = i * I.clients)
    (ha' : σ.vars "bfa" = a) (hba : σ.vars "bfba" = f (i * I.clients + a))
    (hda : σ.vars "bfda" = I.dAt i a) (hsa : σ.vars "bfsa" = I.dAt i a - I.pAt i a)
    (hlt : σ.vars "bfb" < I.clients) :
    cl (σ.vars "bfba") ((σ.arrs "bfsc").getD (σ.vars "bfro" + σ.vars "bfb") 0)
        (σ.vars "bfa") (σ.vars "bfb") (σ.vars "bfsa")
        ((σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfb")) 0)
        ((σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfb")) 0 -
          (σ.arrs "X").getD (2 + (σ.vars "bfro" + σ.vars "bfb")) 0)
        (σ.vars "bfda") = if Bad I f i a (σ.vars "bfb") then 1 else 0 := by
  have hq : i * I.clients + σ.vars "bfb" < I.days * I.clients := idx_lt I hi hlt
  have hbb : (σ.arrs "bfsc").getD (σ.vars "bfro" + σ.vars "bfb") 0 = f (i * I.clients + σ.vars "bfb") := by
    rw [hro, hctx.scGet hq]
  have hp : (σ.arrs "X").getD (2 + (σ.vars "bfro" + σ.vars "bfb")) 0 = I.pAt i (σ.vars "bfb") := by
    rw [hctx.xGet, hro, ← Nat.add_assoc]
    exact Lax117284Proofs.ClientsWord.proc_eq hb.dec hi hlt
  have hd : (σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfb")) 0 =
      I.dAt i (σ.vars "bfb") := by
    rw [hctx.xGet, hro, hctx.hmn, ← Nat.add_assoc]
    exact Lax117284Proofs.ClientsWord.due_eq hb.dec hi hlt
  have hba1 : σ.vars "bfba" ≤ 1 := by rw [hba]; exact hctx.hf _ (idx_lt I hi ha)
  have hbb1 : f (i * I.clients + σ.vars "bfb") ≤ 1 := hctx.hf _ hq
  rw [hbb, hd, hp, hda, hsa, ha', hba, cl_eq (by rw [← hba]; exact hba1) hbb1]
  refine if_congr ?_ rfl rfl
  simp only [Bad, Instance.ConflictAt]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h3, hlt, h1, h2, h4, h5⟩
  · rintro ⟨h3, -, h1, h2, h4, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩

theorem bStep_spec (hb : Bd B x I k) (f : ℕ → ℕ) (i a ok0 : ℕ) (hi : i < I.days)
    (ha : a < I.clients) :
    Spec B (fun σ => BInv x I k f i a ok0 σ ∧ σ.vars "bfb" < I.clients) bStep
      (fun σ σ' => BInv x I k f i a ok0 σ' ∧ σ'.vars "bfb" = σ.vars "bfb" + 1) 65 := by
  refine ((bStep_vals hb f i a ok0 hi ha).frame).post ?_
  rintro σ σ' ⟨hB, hlt⟩ ⟨⟨hok', hb'⟩, hfv, hfa, -, -⟩
  have hclb := cl_bad hb hi ha hB.ctx hB.hro hB.ha hB.hba hB.hda hB.hsa hlt
  obtain ⟨hctx, hi', hro, ha', hba, hda, hsa, hb1, hok, hiff⟩ := hB
  refine ⟨⟨hctx.frame hfv hfa (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, hb'⟩
  · rw [hfv "bfi" (by decide)]; exact hi'
  · rw [hfv "bfro" (by decide)]; exact hro
  · rw [hfv "bfa" (by decide)]; exact ha'
  · rw [hfv "bfba" (by decide)]; exact hba
  · rw [hfv "bfda" (by decide)]; exact hda
  · rw [hfv "bfsa" (by decide)]; exact hsa
  · omega
  · rw [hok']; exact le_trans (Nat.sub_le _ _) hok
  · rw [hb', hok']
    exact iff_step hok hiff hclb

/-- The pair loop of client `a` of day `i`: the flag loses the clashes of `a` with the later
clients. -/
theorem bLoop_spec (hb : Bd B x I k) (f : ℕ → ℕ) (i a : ℕ) (hi : i < I.days)
    (ha : a < I.clients) :
    Spec B (fun σ => Ctx x I k f σ ∧ σ.vars "bfi" = i ∧ σ.vars "bfro" = i * I.clients ∧
        σ.vars "bfa" = a ∧ σ.vars "bfba" = f (i * I.clients + a) ∧ σ.vars "bfda" = I.dAt i a ∧
        σ.vars "bfsa" = I.dAt i a - I.pAt i a ∧ σ.vars "bfok" ≤ 1) bLoop
      (fun σ σ' => BInv x I k f i a (σ.vars "bfok") σ' ∧ σ'.vars "bfb" = I.clients)
      ((65 + 4) * I.clients + 6) := by
  intro σ ⟨hctx, h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨σ', hrun, hI, hbn⟩ := (Spec.forRangeZero (B := B) "bfb" "n"
    (BInv x I k f i a (σ.vars "bfok")) I.clients 65 hb.nB (fun _ h => h.hb)
    (fun _ h => h.ctx.hn) (bStep_spec hb f i a (σ.vars "bfok") hi ha)) σ
    ⟨hctx.setVar 0 (by decide), by simpa using h1, by simpa using h2, by simpa using h3,
      by simpa using h4, by simpa using h5, by simpa using h6, by simp, by simpa using h7,
      by simp⟩
  exact ⟨σ', hrun, hI, hbn⟩

end Lax117284Proofs.Machine.ClBrute

end

/-! ### `Lax117284Proofs.Machine.ClBruteFeas2` -/

section
/-!
The feasibility scan: every client `a` of a day against every client, every day.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

/-- Adding one to a scalar. -/
theorem bump_spec (v : String) :
    Spec B (fun σ => σ.vars v + 1 < B ∧ 1 < B) (asg v (.add (V v) (lit 1)))
      (fun σ σ' => σ' = σ.setVar v (σ.vars v + 1)) 4 :=
  Spec.assign (f := fun σ => σ.vars v + 1) fun σ h =>
    evalB_bin (evalB_var (by omega)) (evalB_lit h.2) h.1

/-- The state of the loop over the clients `a` of day `i`. -/
structure AInv (x : List ℕ) (I : Instance) (k : ℕ) (f : ℕ → ℕ) (i ok0 : ℕ) (σ : Env) : Prop where
  ctx : Ctx x I k f σ
  hi : σ.vars "bfi" = i
  hro : σ.vars "bfro" = i * I.clients
  ha : σ.vars "bfa" ≤ I.clients
  hok : σ.vars "bfok" ≤ 1
  hiff : σ.vars "bfok" = 1 ↔ ok0 = 1 ∧ ∀ a', a' < σ.vars "bfa" → ∀ b, ¬ Bad I f i a' b

set_option maxHeartbeats 1600000 in
theorem aSetup_vals (hb : Bd B x I k) (f : ℕ → ℕ) (i ok0 : ℕ) (hi : i < I.days) :
    Spec B (fun σ => AInv x I k f i ok0 σ ∧ σ.vars "bfa" < I.clients) aSetup
      (fun σ σ' => σ'.vars "bfba" = (σ.arrs "bfsc").getD (σ.vars "bfro" + σ.vars "bfa") 0 ∧
        σ'.vars "bfda" = (σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfa")) 0 ∧
        σ'.vars "bfsa" = (σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfa")) 0 -
          (σ.arrs "X").getD (2 + (σ.vars "bfro" + σ.vars "bfa")) 0) 23 := by
  run_vcg
  all_goals have hro := (‹AInv x I k f i ok0 σ›).hro
  all_goals obtain ⟨hctx, hi', -, ha', hok, hiff⟩ := ‹AInv x I k f i ok0 σ›
  all_goals have hal : σ.vars "bfa" < I.clients := ‹σ.vars "bfa" < I.clients›
  all_goals have hmn := hb.mnB
  all_goals have hlen := hb.len
  all_goals have hbig := hb.big
  all_goals have hq : σ.vars "bfro" + σ.vars "bfa" < I.days * I.clients := (by
    rw [hro]; exact idx_lt I hi hal)
  all_goals have hmn' := hctx.hmn
  all_goals have hscb : (σ.arrs "bfsc").getD (σ.vars "bfro" + σ.vars "bfa") 0 ≤ 1 := (by
    rw [hctx.scGet hq]; exact hctx.hf _ hq)
  all_goals have hscl := hctx.scLen
  all_goals have hxl := hctx.xLen hb
  all_goals have hx1 : (σ.arrs "X").getD (2 + (σ.vars "bfro" + σ.vars "bfa")) 0 < B := (by
    rw [hctx.xGet]; exact hb.xg _)
  all_goals have hx2 : (σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfa")) 0 < B := (by
    rw [hctx.xGet]; exact hb.xg _)
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte]
  all_goals try omega
  trivial

theorem aSetup_spec (hb : Bd B x I k) (f : ℕ → ℕ) (i ok0 : ℕ) (hi : i < I.days) :
    Spec B (fun σ => AInv x I k f i ok0 σ ∧ σ.vars "bfa" < I.clients) aSetup
      (fun σ σ' => Ctx x I k f σ' ∧ σ'.vars "bfi" = i ∧ σ'.vars "bfro" = i * I.clients ∧
        σ'.vars "bfa" = σ.vars "bfa" ∧ σ'.vars "bfok" = σ.vars "bfok" ∧
        σ'.vars "bfba" = f (i * I.clients + σ.vars "bfa") ∧
        σ'.vars "bfda" = I.dAt i (σ.vars "bfa") ∧
        σ'.vars "bfsa" = I.dAt i (σ.vars "bfa") - I.pAt i (σ.vars "bfa")) 23 := by
  refine ((aSetup_vals hb f i ok0 hi).frame).post ?_
  rintro σ σ' ⟨hA, hlt⟩ ⟨⟨hba, hda, hsa⟩, hfv, hfa, -, -⟩
  have hro := hA.hro
  obtain ⟨hctx, hi', -, ha', hok, hiff⟩ := hA
  have hq : i * I.clients + σ.vars "bfa" < I.days * I.clients := idx_lt I hi hlt
  have hp : (σ.arrs "X").getD (2 + (σ.vars "bfro" + σ.vars "bfa")) 0 = I.pAt i (σ.vars "bfa") := by
    rw [hctx.xGet, hro, ← Nat.add_assoc]
    exact Lax117284Proofs.ClientsWord.proc_eq hb.dec hi hlt
  have hd : (σ.arrs "X").getD (2 + σ.vars "bfmn" + (σ.vars "bfro" + σ.vars "bfa")) 0 =
      I.dAt i (σ.vars "bfa") := by
    rw [hctx.xGet, hro, hctx.hmn, ← Nat.add_assoc]
    exact Lax117284Proofs.ClientsWord.due_eq hb.dec hi hlt
  refine ⟨hctx.frame hfv hfa (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfv "bfi" (by decide)]; exact hi'
  · rw [hfv "bfro" (by decide)]; exact hro
  · rw [hfv "bfa" (by decide)]
  · rw [hfv "bfok" (by decide)]
  · rw [hba, hro, hctx.scGet hq]
  · rw [hda, hd]
  · rw [hsa, hd, hp]

lemma col_iff (f : ℕ → ℕ) (i a : ℕ) :
    (∀ b, b < I.clients → ¬ Bad I f i a b) ↔ ∀ b, ¬ Bad I f i a b :=
  ⟨fun h b hbad => h b hbad.2.1 hbad, fun h b _ => h b⟩

lemma row_iff (f : ℕ → ℕ) (i : ℕ) :
    (∀ a, a < I.clients → ∀ b, ¬ Bad I f i a b) ↔ ∀ a b, ¬ Bad I f i a b :=
  ⟨fun h a b hbad => h a (lt_trans hbad.1 hbad.2.1) b hbad, fun h a _ b => h a b⟩

theorem aStep_spec (hb : Bd B x I k) (f : ℕ → ℕ) (i ok0 : ℕ) (hi : i < I.days) :
    Spec B (fun σ => AInv x I k f i ok0 σ ∧ σ.vars "bfa" < I.clients) aStep
      (fun σ σ' => AInv x I k f i ok0 σ' ∧ σ'.vars "bfa" = σ.vars "bfa" + 1)
      (23 + ((65 + 4) * I.clients + 6 + 4)) := by
  intro σ ⟨hA, hlt⟩
  obtain ⟨σ1, hr1, hC1, hi1, hro1, ha1, hok1, hba1, hda1, hsa1⟩ :=
    aSetup_spec hb f i ok0 hi σ ⟨hA, hlt⟩
  obtain ⟨σ2, hr2, hBI, hbn⟩ := bLoop_spec hb f i (σ.vars "bfa") hi hlt σ1
    ⟨hC1, hi1, hro1, ha1, hba1, hda1, hsa1, by rw [hok1]; exact hA.hok⟩
  have hbig := hb.big
  have hnB := hb.nB
  have ha2 : σ2.vars "bfa" = σ.vars "bfa" := hBI.ha
  obtain ⟨σ3, hr3, rfl⟩ := (bump_spec (B := B) "bfa") σ2 ⟨by omega, by omega⟩
  refine ⟨_, hr1.seq (hr2.seq hr3), ⟨hBI.ctx.setVar _ (by decide), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa using hBI.hi
  · simpa using hBI.hro
  · simp only [vars_setVar, if_true]; omega
  · simpa using hBI.hok
  · have h1 := hBI.hiff
    rw [hbn, hok1, hA.hiff, col_iff] at h1
    simp only [vars_setVar, if_true, ha2, String.reduceEq, not_false_eq_true, if_neg]
    rw [h1, lt_succ_forall]
    tauto
  · simp only [vars_setVar, if_true, ha2]

theorem aLoop_spec (hb : Bd B x I k) (f : ℕ → ℕ) (i : ℕ) (hi : i < I.days) :
    Spec B (fun σ => Ctx x I k f σ ∧ σ.vars "bfi" = i ∧ σ.vars "bfro" = i * I.clients ∧
        σ.vars "bfok" ≤ 1) (forZ "bfa" "n" aStep)
      (fun σ σ' => AInv x I k f i (σ.vars "bfok") σ' ∧ σ'.vars "bfa" = I.clients)
      ((23 + ((65 + 4) * I.clients + 6 + 4) + 4) * I.clients + 6) := by
  intro σ ⟨hctx, h1, h2, h3⟩
  obtain ⟨σ', hrun, hI, hbn⟩ := (Spec.forRangeZero (B := B) "bfa" "n"
    (AInv x I k f i (σ.vars "bfok")) I.clients (23 + ((65 + 4) * I.clients + 6 + 4)) hb.nB
    (fun _ h => h.ha) (fun _ h => h.ctx.hn) (aStep_spec hb f i (σ.vars "bfok") hi)) σ
    ⟨hctx.setVar 0 (by decide), by simpa using h1, by simpa using h2, by simp,
      by simpa using h3, by simp⟩
  exact ⟨σ', hrun, hI, hbn⟩

end Lax117284Proofs.Machine.ClBrute

end

/-! ### `Lax117284Proofs.Machine.ClBruteFeas3` -/

section
/-!
The feasibility scan, over the days.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

/-- The state of the loop over the days. -/
structure IInv (x : List ℕ) (I : Instance) (k : ℕ) (f : ℕ → ℕ) (ok0 : ℕ) (σ : Env) : Prop where
  ctx : Ctx x I k f σ
  hi : σ.vars "bfi" ≤ I.days
  hok : σ.vars "bfok" ≤ 1
  hiff : σ.vars "bfok" = 1 ↔ ok0 = 1 ∧ ∀ i', i' < σ.vars "bfi" → ∀ a b, ¬ Bad I f i' a b

theorem ro_spec (hb : Bd B x I k) (f : ℕ → ℕ) (ok0 : ℕ) :
    Spec B (fun σ => IInv x I k f ok0 σ ∧ σ.vars "bfi" < I.days)
      (asg "bfro" (.mul (V "bfi") (V "n")))
      (fun σ σ' => σ' = σ.setVar "bfro" (σ.vars "bfi" * σ.vars "n")) 4 := by
  refine Spec.assign (f := fun σ => σ.vars "bfi" * σ.vars "n") fun σ h => ?_
  have hnn : σ.vars "n" = I.clients := h.1.ctx.hn
  have hlt := h.2
  have hbig := hb.big
  have hmB := hb.mB
  have hmn := hb.mnB
  have hlen := hb.len
  have hnB := hb.nB
  have : σ.vars "bfi" * I.clients ≤ I.days * I.clients := Nat.mul_le_mul_right _ hlt.le
  exact evalB_bin (evalB_var (by omega)) (evalB_var (by omega)) (by rw [Bop.apply_mul, hnn]; omega)

theorem iStep_spec (hb : Bd B x I k) (f : ℕ → ℕ) (ok0 : ℕ) :
    Spec B (fun σ => IInv x I k f ok0 σ ∧ σ.vars "bfi" < I.days) iStep
      (fun σ σ' => IInv x I k f ok0 σ' ∧ σ'.vars "bfi" = σ.vars "bfi" + 1)
      (4 + (((23 + ((65 + 4) * I.clients + 6 + 4) + 4) * I.clients + 6) + 4)) := by
  intro σ ⟨hI, hlt⟩
  have hbig := hb.big
  have hmB := hb.mB
  have hnn : σ.vars "n" = I.clients := hI.ctx.hn
  obtain ⟨σ1, hr1, h1⟩ := ro_spec hb f ok0 σ ⟨hI, hlt⟩
  have hc1 : Ctx x I k f σ1 := by rw [h1]; exact hI.ctx.setVar _ (by decide)
  have hv1 : ∀ y, y ≠ "bfro" → σ1.vars y = σ.vars y := by
    intro y hy; rw [h1]; simp [hy]
  have hro1 : σ1.vars "bfro" = σ.vars "bfi" * I.clients := by rw [h1]; simp [hnn]
  obtain ⟨σ2, hr2, hAI, han⟩ := aLoop_spec hb f (σ.vars "bfi") hlt σ1
    ⟨hc1, by rw [hv1 _ (by decide)], hro1, by rw [hv1 _ (by decide)]; exact hI.hok⟩
  have hbi : σ2.vars "bfi" = σ.vars "bfi" := hAI.hi
  obtain ⟨σ3, hr3, rfl⟩ := (bump_spec (B := B) "bfi") σ2 ⟨by omega, by omega⟩
  refine ⟨_, hr1.seq (hr2.seq hr3), ⟨hAI.ctx.setVar _ (by decide), ?_, ?_, ?_⟩, ?_⟩
  · simp only [vars_setVar, if_true, hbi]; omega
  · simpa using hAI.hok
  · have h1' := hAI.hiff
    rw [han, row_iff] at h1'
    simp only [vars_setVar, if_true, hbi, String.reduceEq, not_false_eq_true, if_neg]
    have h2 : (σ1.vars "bfok") = σ.vars "bfok" := hv1 _ (by decide)
    rw [h1', h2, hI.hiff, lt_succ_forall]
    tauto
  · simp only [vars_setVar, if_true, hbi]

theorem feasCom_spec (hb : Bd B x I k) (f : ℕ → ℕ) :
    Spec B (fun σ => Ctx x I k f σ ∧ σ.vars "bfok" ≤ 1) feasCom
      (fun σ σ' => IInv x I k f (σ.vars "bfok") σ' ∧ σ'.vars "bfi" = I.days)
      ((4 + (((23 + ((65 + 4) * I.clients + 6 + 4) + 4) * I.clients + 6) + 4) + 4) * I.days + 6) := by
  intro σ ⟨hctx, h1⟩
  obtain ⟨σ', hrun, hI, hbn⟩ := (Spec.forRangeZero (B := B) "bfi" "m"
    (IInv x I k f (σ.vars "bfok")) I.days
    (4 + (((23 + ((65 + 4) * I.clients + 6 + 4) + 4) * I.clients + 6) + 4)) hb.mB
    (fun _ h => h.hi) (fun _ h => h.ctx.hm) (iStep_spec hb f (σ.vars "bfok"))) σ
    ⟨hctx.setVar 0 (by decide), by simp, by simpa using h1, by simp⟩
  exact ⟨σ', hrun, hI, hbn⟩

end Lax117284Proofs.Machine.ClBrute

end

/-! ### `Lax117284Proofs.Machine.ClBruteFair` -/

section
/-!
The fairness scan: the number of days each client is served, against `k`.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

/-- The state of the count of client `j` over the days. -/
structure CInv (x : List ℕ) (I : Instance) (k : ℕ) (f : ℕ → ℕ) (j : ℕ) (σ : Env) : Prop where
  ctx : Ctx x I k f σ
  hj : σ.vars "bfj" = j
  hi : σ.vars "bfi" ≤ I.days
  hc : σ.vars "bfc" = ∑ i ∈ Finset.range (σ.vars "bfi"), f (i * I.clients + j)
  hcle : σ.vars "bfc" ≤ σ.vars "bfi"

set_option maxHeartbeats 1600000 in
theorem cStep_vals (hb : Bd B x I k) (f : ℕ → ℕ) (j : ℕ) (hj : j < I.clients) :
    Spec B (fun σ => CInv x I k f j σ ∧ σ.vars "bfi" < I.days) cStep
      (fun σ σ' => σ'.vars "bfc" = σ.vars "bfc" +
          (σ.arrs "bfsc").getD (σ.vars "bfi" * σ.vars "n" + σ.vars "bfj") 0 ∧
        σ'.vars "bfi" = σ.vars "bfi" + 1) 13 := by
  run_vcg
  all_goals obtain ⟨hctx, hj', hi', hc, hcle⟩ := ‹CInv x I k f j σ›
  all_goals have hil : σ.vars "bfi" < I.days := ‹σ.vars "bfi" < I.days›
  all_goals have hmn := hb.mnB
  all_goals have hlen := hb.len
  all_goals have hbig := hb.big
  all_goals have hnB := hb.nB
  all_goals have hmB := hb.mB
  all_goals have hq : σ.vars "bfi" * σ.vars "n" + σ.vars "bfj" < I.days * I.clients := (by
    rw [hctx.hn, hj']; exact idx_lt I hil hj)
  all_goals have hscb : (σ.arrs "bfsc").getD (σ.vars "bfi" * σ.vars "n" + σ.vars "bfj") 0 ≤ 1 := (by
    rw [hctx.scGet hq]; exact hctx.hf _ hq)
  all_goals have hscl := hctx.scLen
  all_goals have hn' := hctx.hn
  all_goals have hprod : σ.vars "bfi" * σ.vars "n" ≤ I.days * I.clients := (by
    rw [hn']; exact Nat.mul_le_mul_right _ hil.le)
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte]
  all_goals try omega
  exact ⟨trivial, trivial⟩

theorem cStep_spec (hb : Bd B x I k) (f : ℕ → ℕ) (j : ℕ) (hj : j < I.clients) :
    Spec B (fun σ => CInv x I k f j σ ∧ σ.vars "bfi" < I.days) cStep
      (fun σ σ' => CInv x I k f j σ' ∧ σ'.vars "bfi" = σ.vars "bfi" + 1) 13 := by
  refine ((cStep_vals hb f j hj).frame).post ?_
  rintro σ σ' ⟨hC, hlt⟩ ⟨⟨hc', hi'⟩, hfv, hfa, -, -⟩
  have hq' : σ.vars "bfi" * I.clients + j < I.days * I.clients := idx_lt I hlt hj
  have hbit : (σ.arrs "bfsc").getD (σ.vars "bfi" * σ.vars "n" + σ.vars "bfj") 0 =
      f (σ.vars "bfi" * I.clients + j) := by
    rw [hC.ctx.hn, hC.hj]; exact hC.ctx.scGet hq'
  have hf1 : f (σ.vars "bfi" * I.clients + j) ≤ 1 := hC.ctx.hf _ hq'
  have hcle := hC.hcle
  refine ⟨⟨hC.ctx.frame hfv hfa (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_⟩, hi'⟩
  · rw [hfv "bfj" (by decide)]; exact hC.hj
  · omega
  · rw [hc', hi', Finset.sum_range_succ, hC.hc, hbit]
  · rw [hc', hi', hbit]; omega

theorem cLoop_spec (hb : Bd B x I k) (f : ℕ → ℕ) (j : ℕ) (hj : j < I.clients) :
    Spec B (fun σ => Ctx x I k f σ ∧ σ.vars "bfj" = j ∧ σ.vars "bfc" = 0) (forZ "bfi" "m" cStep)
      (fun _ σ' => CInv x I k f j σ' ∧ σ'.vars "bfi" = I.days) ((13 + 4) * I.days + 6) := by
  intro σ ⟨hctx, h1, h2⟩
  obtain ⟨σ', hrun, hI, hbn⟩ := (Spec.forRangeZero (B := B) "bfi" "m"
    (CInv x I k f j) I.days 13 hb.mB (fun _ h => h.hi) (fun _ h => h.ctx.hm)
    (cStep_spec hb f j hj)) σ
    ⟨hctx.setVar 0 (by decide), by simpa using h1, by simp, by simpa using h2, by simp [h2]⟩
  exact ⟨σ', hrun, hI, hbn⟩

set_option maxHeartbeats 1600000 in
theorem jTail_vals (hb : Bd B x I k) (f : ℕ → ℕ) :
    Spec B (fun σ => Ctx x I k f σ ∧ σ.vars "bfc" ≤ I.days ∧ σ.vars "bfok" ≤ 1 ∧
        σ.vars "bfj" < I.clients) jTail
      (fun σ σ' => σ'.vars "bfok" = σ.vars "bfok" - (1 - (1 - (σ.vars "k" - σ.vars "bfc"))) ∧
        σ'.vars "bfj" = σ.vars "bfj" + 1) 20 := by
  run_vcg
  all_goals have hctx : Ctx x I k f σ := ‹Ctx x I k f σ›
  all_goals have hc : σ.vars "bfc" ≤ I.days := ‹σ.vars "bfc" ≤ I.days›
  all_goals have hok : σ.vars "bfok" ≤ 1 := ‹σ.vars "bfok" ≤ 1›
  all_goals have hjl : σ.vars "bfj" < I.clients := ‹σ.vars "bfj" < I.clients›
  all_goals have hmB := hb.mB
  all_goals have hnB := hb.nB
  all_goals have hkB := hb.kB
  all_goals have hbig := hb.big
  all_goals have hkk := hctx.hk
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte]
  all_goals try omega
  exact ⟨trivial, trivial⟩

/-- The state of the loop over the clients. -/
structure JInv (x : List ℕ) (I : Instance) (k : ℕ) (f : ℕ → ℕ) (ok0 : ℕ) (σ : Env) : Prop where
  ctx : Ctx x I k f σ
  hj : σ.vars "bfj" ≤ I.clients
  hok : σ.vars "bfok" ≤ 1
  hiff : σ.vars "bfok" = 1 ↔ ok0 = 1 ∧ ∀ j', j' < σ.vars "bfj" →
    k ≤ ∑ i ∈ Finset.range I.days, f (i * I.clients + j')

open Classical in
lemma iff_step2 {ok ok0 b c : ℕ} {P : ℕ → Prop} (hok : ok ≤ 1)
    (h : ok = 1 ↔ ok0 = 1 ∧ ∀ b', b' < b → P b') (hc : c = if P b then 0 else 1) :
    ok - c = 1 ↔ ok0 = 1 ∧ ∀ b', b' < b + 1 → P b' := by
  rw [lt_succ_forall]
  by_cases hp : P b
  · rw [if_pos hp] at hc; subst hc
    rw [Nat.sub_zero, h]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, hp⟩
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rw [if_neg hp] at hc; subst hc
    constructor
    · intro h1; omega
    · rintro ⟨-, -, h2⟩; exact absurd h2 hp

theorem jStep_spec (hb : Bd B x I k) (f : ℕ → ℕ) (ok0 : ℕ) :
    Spec B (fun σ => JInv x I k f ok0 σ ∧ σ.vars "bfj" < I.clients) jStep
      (fun σ σ' => JInv x I k f ok0 σ' ∧ σ'.vars "bfj" = σ.vars "bfj" + 1)
      (2 + (((13 + 4) * I.days + 6) + 20)) := by
  intro σ ⟨hJ, hlt⟩
  have hbig := hb.big
  have hmB := hb.mB
  obtain ⟨σ1, hr1, h1⟩ := (Spec.assign (B := B) (x := "bfc") (e := lit 0) (f := fun _ => 0)
    (P := fun σ => JInv x I k f ok0 σ ∧ σ.vars "bfj" < I.clients)
    (fun σ h => evalB_lit (by have := hb.big; omega))) σ ⟨hJ, hlt⟩
  have hc1 : Ctx x I k f σ1 := by rw [h1]; exact hJ.ctx.setVar _ (by decide)
  have hv1 : ∀ y, y ≠ "bfc" → σ1.vars y = σ.vars y := by
    intro y hy; rw [h1]; simp [hy]
  obtain ⟨σ2, hr2, ⟨hCI, hbn⟩, hfv, -, -, -⟩ := (cLoop_spec hb f (σ.vars "bfj") hlt).frame σ1
    ⟨hc1, hv1 _ (by decide), by rw [h1]; simp⟩
  have hok2 : σ2.vars "bfok" = σ.vars "bfok" := by
    rw [hfv "bfok" (by decide), hv1 _ (by decide)]
  have hbj2 : σ2.vars "bfj" = σ.vars "bfj" := by
    rw [hCI.hj]
  have hcle : σ2.vars "bfc" ≤ I.days := by have := hCI.hcle; omega
  obtain ⟨σ3, hr3, ⟨hok3, hj3⟩, hfv3, hfa3, -, -⟩ := (jTail_vals hb f).frame σ2
    ⟨hCI.ctx, hcle, by rw [hok2]; exact hJ.hok, by rw [hbj2]; exact hlt⟩
  have hs : (lit 0).size = 1 := rfl
  have hS : σ2.vars "bfc" = ∑ i ∈ Finset.range I.days, f (i * I.clients + σ.vars "bfj") := by
    rw [hCI.hc, hbn]
  have hkk : σ2.vars "k" = k := hCI.ctx.hk
  refine ⟨σ3, hr1.seq (hr2.seq hr3) |>.mono (by omega),
    ⟨hCI.ctx.frame hfv3 hfa3 (by decide) (by decide) (by decide), ?_, ?_, ?_⟩, ?_⟩
  · rw [hj3, hbj2]; omega
  · rw [hok3]; exact le_trans (Nat.sub_le _ _) (by rw [hok2]; exact hJ.hok)
  · rw [hok3, hj3, hbj2, hok2]
    exact iff_step2 hJ.hok hJ.hiff (by rw [hS, hkk, ltf_eq]; split_ifs <;> omega)
  · rw [hj3, hbj2]

theorem fairCom_spec (hb : Bd B x I k) (f : ℕ → ℕ) :
    Spec B (fun σ => Ctx x I k f σ ∧ σ.vars "bfok" ≤ 1) fairCom
      (fun σ σ' => JInv x I k f (σ.vars "bfok") σ' ∧ σ'.vars "bfj" = I.clients)
      ((2 + (((13 + 4) * I.days + 6) + 20) + 4) * I.clients + 6) := by
  intro σ ⟨hctx, h1⟩
  obtain ⟨σ', hrun, hI, hbn⟩ := (Spec.forRangeZero (B := B) "bfj" "n"
    (JInv x I k f (σ.vars "bfok")) I.clients (2 + (((13 + 4) * I.days + 6) + 20)) hb.nB
    (fun _ h => h.hj) (fun _ h => h.ctx.hn) (jStep_spec hb f (σ.vars "bfok"))) σ
    ⟨hctx.setVar 0 (by decide), by simp, by simpa using h1, by simp⟩
  exact ⟨σ', hrun, hI, hbn⟩

end Lax117284Proofs.Machine.ClBrute

end

/-! ### `Lax117284Proofs.Machine.ClBruteOdo` -/

section
/-!
The odometer: add one to the vector, the carry running from cell to cell.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

set_option maxHeartbeats 1600000 in
theorem oStep_vals (hb : Bd B x I k) (g : ℕ → ℕ) :
    Spec B (fun σ => Ctx x I k g σ ∧ σ.vars "bfq" < I.days * I.clients ∧ σ.vars "bfcy" ≤ 1) oStep
      (fun σ σ' => σ'.vars "bfcy" = ((σ.arrs "bfsc").getD (σ.vars "bfq") 0 + σ.vars "bfcy") / 2 ∧
        σ'.arrs "bfsc" = (σ.arrs "bfsc").set (σ.vars "bfq")
          (((σ.arrs "bfsc").getD (σ.vars "bfq") 0 + σ.vars "bfcy") -
            ((σ.arrs "bfsc").getD (σ.vars "bfq") 0 + σ.vars "bfcy") / 2 * 2) ∧
        σ'.vars "bfq" = σ.vars "bfq" + 1) 20 := by
  run_vcg
  all_goals have hctx : Ctx x I k g σ := ‹Ctx x I k g σ›
  all_goals have hq : σ.vars "bfq" < I.days * I.clients := ‹σ.vars "bfq" < I.days * I.clients›
  all_goals have hcy : σ.vars "bfcy" ≤ 1 := ‹σ.vars "bfcy" ≤ 1›
  all_goals have hmn := hb.mnB
  all_goals have hbig := hb.big
  all_goals have hlen := hb.len
  all_goals have hscb : (σ.arrs "bfsc").getD (σ.vars "bfq") 0 ≤ 1 := (by
    rw [hctx.scGet hq]; exact hctx.hf _ hq)
  all_goals have hscl := hctx.scLen
  all_goals try simp only [Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte]
  all_goals try omega
  exact ⟨trivial, trivial, trivial⟩

/-- The state of the increment after `bfq` cells: the cells before `bfq` hold the new bits
`g`, the others are still `f`, and `g` with the carry adds one to `f` there. -/
def OInv (x : List ℕ) (I : Instance) (k : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  ∃ g : ℕ → ℕ, Ctx x I k g σ ∧ σ.vars "bfq" ≤ I.days * I.clients ∧ σ.vars "bfcy" ≤ 1 ∧
    (∀ r, σ.vars "bfq" ≤ r → g r = f r) ∧
    enc g (σ.vars "bfq") + σ.vars "bfcy" * 2 ^ σ.vars "bfq" = enc f (σ.vars "bfq") + 1

lemma Ctx.frame_sc {c : Com} {f g : ℕ → ℕ} {σ σ' : Env} (h : Ctx x I k f σ)
    (hv : ∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y)
    (ha : ∀ a, a ∉ c.warrs → σ'.arrs a = σ.arrs a)
    (h1 : ∀ y ∈ ["n", "m", "k", "bfmn"], y ∉ c.wvars) (h2 : "X" ∉ c.warrs)
    (hsc : σ'.arrs "bfsc" = arrOf (I.days * I.clients) g)
    (hg : ∀ r, r < I.days * I.clients → g r ≤ 1) : Ctx x I k g σ' :=
  ⟨by rw [ha _ h2]; exact h.hx, by rw [hv _ (h1 _ (by simp))]; exact h.hn,
    by rw [hv _ (h1 _ (by simp))]; exact h.hm, by rw [hv _ (h1 _ (by simp))]; exact h.hk,
    by rw [hv _ (h1 _ (by simp))]; exact h.hmn, hsc, hg⟩

lemma odo_arith (E1 E2 P a cy c d : ℕ) (hd : d + c * 2 = a + cy) (hE : E1 + cy * P = E2 + 1) :
    E1 + d * P + c * (P * 2) = E2 + a * P + 1 := by
  have hm : (d + c * 2) * P = (a + cy) * P := by rw [hd]
  nlinarith [hm, hE]

theorem oStep_spec (hb : Bd B x I k) (f : ℕ → ℕ) :
    Spec B (fun σ => OInv x I k f σ ∧ σ.vars "bfq" < I.days * I.clients) oStep
      (fun σ σ' => OInv x I k f σ' ∧ σ'.vars "bfq" = σ.vars "bfq" + 1) 20 := by
  intro σ ⟨⟨g, hctx, hq, hcy, hrest, henc⟩, hlt⟩
  obtain ⟨σ', hr, ⟨hcy', hsc', hq'⟩, hfv, hfa, -, -⟩ := (oStep_vals hb g).frame σ ⟨hctx, hlt, hcy⟩
  have hgq : (σ.arrs "bfsc").getD (σ.vars "bfq") 0 = g (σ.vars "bfq") := hctx.scGet hlt
  rw [hgq] at hcy' hsc'
  have hg1 : g (σ.vars "bfq") ≤ 1 := hctx.hf _ hlt
  refine ⟨σ', hr, ⟨fun r => if r = σ.vars "bfq" then
      (g r + σ.vars "bfcy") - (g r + σ.vars "bfcy") / 2 * 2 else g r, ?_, ?_, ?_, ?_, ?_⟩, hq'⟩
  · refine hctx.frame_sc hfv hfa (by decide) (by decide) ?_ ?_
    · rw [hsc', hctx.hsc, set_arrOf]
      refine arrOf_congr fun r _ => ?_
      by_cases h : r = σ.vars "bfq"
      · subst h; simp
      · simp [h]
    · intro r hr
      by_cases h : r = σ.vars "bfq"
      · subst h; simp only [if_true]; omega
      · simp only [h, if_false]; exact hctx.hf r hr
  · rw [hq']; omega
  · rw [hcy']; omega
  · intro r hr
    rw [hq'] at hr
    have h : r ≠ σ.vars "bfq" := by omega
    simp only [h, if_false]
    exact hrest r (by omega)
  · rw [hq', hcy', enc_succ, enc_succ, pow_succ]
    have hc : enc (fun r => if r = σ.vars "bfq" then
        (g r + σ.vars "bfcy") - (g r + σ.vars "bfcy") / 2 * 2 else g r) (σ.vars "bfq") =
        enc g (σ.vars "bfq") :=
      enc_congr fun r hr => by simp only [show r ≠ σ.vars "bfq" by omega, if_false]
    rw [hc, if_pos rfl, hrest _ le_rfl]
    have := odo_arith (enc g (σ.vars "bfq")) (enc f (σ.vars "bfq")) (2 ^ σ.vars "bfq")
      (g (σ.vars "bfq")) (σ.vars "bfcy") ((g (σ.vars "bfq") + σ.vars "bfcy") / 2)
      ((g (σ.vars "bfq") + σ.vars "bfcy") - (g (σ.vars "bfq") + σ.vars "bfcy") / 2 * 2)
      (by omega) henc
    rw [hrest _ le_rfl] at this
    linarith

/-- **The increment**: the vector `f` becomes a vector `g` with `g + carry * 2 ^ (m * n) = f + 1`
(as numbers), the carry being `0` or `1`. -/
theorem odoCom_spec (hb : Bd B x I k) (f : ℕ → ℕ) :
    Spec B (fun σ => Ctx x I k f σ) odoCom
      (fun _ σ' => ∃ g, Ctx x I k g σ' ∧ σ'.vars "bfcy" ≤ 1 ∧
        enc g (I.days * I.clients) + σ'.vars "bfcy" * 2 ^ (I.days * I.clients) =
          enc f (I.days * I.clients) + 1 ∧ σ'.vars "bfq" = I.days * I.clients)
      (2 + ((20 + 4) * (I.days * I.clients) + 6)) := by
  intro σ hctx
  have hbig := hb.big
  obtain ⟨σ1, hr1, h1⟩ := (Spec.assign (B := B) (x := "bfcy") (e := lit 1) (f := fun _ => 1)
    (P := fun σ => Ctx x I k f σ)
    (fun _ _ => evalB_lit (by have := hb.big; omega))) σ hctx
  have hs : (lit 1).size = 1 := rfl
  have hc1 : Ctx x I k f σ1 := by rw [h1]; exact hctx.setVar _ (by decide)
  obtain ⟨σ2, hr2, ⟨g, hg, hq, hcy, -, henc⟩, hq2⟩ := (Spec.forRangeZero (B := B) "bfq" "bfmn"
    (OInv x I k f) (I.days * I.clients) 20 (by have := hb.mnB; omega)
    (fun _ h => by obtain ⟨g, -, h, -⟩ := h; exact h)
    (fun _ h => by obtain ⟨g, hg, -⟩ := h; exact hg.hmn) (oStep_spec hb f)) σ1
    ⟨f, hc1.setVar _ (by decide), by simp, by simp [h1], fun _ _ => rfl, by simp [h1, enc_zero]⟩
  refine ⟨σ2, (hr1.seq hr2).mono (by omega), g, hg, hcy, ?_, hq2⟩
  rw [hq2] at henc
  exact henc

end Lax117284Proofs.Machine.ClBrute

end

/-! ### `Lax117284Proofs.Machine.ClBruteEval` -/

section
/-!
One vector, tested: `evalCom` leaves in `bfok` the truth of "feasible and fair".
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

/-! ### The costs -/

/-- The cost of the feasibility scan. -/
def costFeas (m n : ℕ) : ℕ := (4 + (((23 + ((65 + 4) * n + 6 + 4) + 4) * n + 6) + 4) + 4) * m + 6

/-- The cost of the fairness scan. -/
def costFair (m n : ℕ) : ℕ := (2 + (((13 + 4) * m + 6) + 20) + 4) * n + 6

/-- The cost of the guarded feasibility scan: with no client it is one test. -/
def costFeasG (m n : ℕ) : ℕ := 1 + 3 + (if n = 0 then 1 else costFeas m n)

/-- The cost of testing one vector. -/
def costEval (m n : ℕ) : ℕ := 2 + (costFeasG m n + costFair m n)

/-! ### The guard -/

lemma lt_of_lit_lt_true {σ : Env} {y : String}
    (h : (Cond.lt (lit 0) (V y)).evalB B σ = some true) : 0 < σ.vars y := by
  simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  simpa using hr.symm

lemma le_of_lit_lt_false {σ : Env} {y : String}
    (h : (Cond.lt (lit 0) (V y)).evalB B σ = some false) : σ.vars y ≤ 0 := by
  simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  have := hr.symm
  simpa using this

lemma feasF_of_no_clients (f : ℕ → ℕ) (h : I.clients = 0) : FeasF I f :=
  fun _ _ _ _ hbad => by have := hbad.2.1; omega

theorem feasG_spec (hb : Bd B x I k) (f : ℕ → ℕ) :
    Spec B (fun σ => Ctx x I k f σ ∧ σ.vars "bfok" ≤ 1) feasG
      (fun σ σ' => Ctx x I k f σ' ∧ σ'.vars "bfok" ≤ 1 ∧
        (σ'.vars "bfok" = 1 ↔ σ.vars "bfok" = 1 ∧ FeasF I f))
      (1 + 3 + (if I.clients = 0 then 1 else costFeas I.days I.clients)) := by
  refine Spec.ite (b := .lt (lit 0) (V "n")) ?_ ?_ ?_
  · intro σ ⟨hctx, hok⟩
    have := hb.nB
    exact ⟨_, evalB_condLt (evalB_lit (by have := hb.big; omega))
      (evalB_var (by rw [hctx.hn]; exact hb.nB))⟩
  · intro σ ⟨⟨hctx, hok⟩, hc⟩
    have hpos : 0 < I.clients := by rw [← hctx.hn]; exact lt_of_lit_lt_true hc
    obtain ⟨σ', hr, hIn, hbn⟩ := feasCom_spec hb f σ ⟨hctx, hok⟩
    refine ⟨σ', hr.mono (by rw [if_neg (by omega)]; exact le_rfl), hIn.ctx, hIn.hok, ?_⟩
    rw [hIn.hiff]
    simp only [hbn]
    constructor
    · intro h; exact ⟨h.1, fun i hi a b => h.2 i hi a b⟩
    · intro h; exact ⟨h.1, fun i hi a b => h.2 i hi a b⟩
  · intro σ ⟨⟨hctx, hok⟩, hc⟩
    have h0 : I.clients = 0 := by rw [← hctx.hn]; exact Nat.le_zero.mp (le_of_lit_lt_false hc)
    refine ⟨σ, Run.skip.mono (by rw [if_pos h0]), hctx, hok, ?_⟩
    exact ⟨fun h => ⟨h, feasF_of_no_clients f h0⟩, fun h => h.1⟩

theorem evalCom_spec (hb : Bd B x I k) (f : ℕ → ℕ) :
    Spec B (fun σ => Ctx x I k f σ) evalCom
      (fun σ σ' => Ctx x I k f σ' ∧ σ'.vars "bfok" ≤ 1 ∧
        (σ'.vars "bfok" = 1 ↔ FeasF I f ∧ FairF I k f) ∧
        σ'.vars "bfans" = σ.vars "bfans" ∧ σ'.vars "bfdn" = σ.vars "bfdn")
      (costEval I.days I.clients) := by
  intro σ hctx
  have hbig := hb.big
  obtain ⟨σ1, hr1, h1⟩ := (Spec.assign (B := B) (x := "bfok") (e := lit 1) (f := fun _ => 1)
    (P := fun σ => Ctx x I k f σ)
    (fun _ _ => evalB_lit (by omega))) σ hctx
  have hs : (lit 1).size = 1 := rfl
  have hc1 : Ctx x I k f σ1 := by rw [h1]; exact hctx.setVar _ (by decide)
  have hv1 : ∀ y, y ≠ "bfok" → σ1.vars y = σ.vars y := by
    intro y hy; rw [h1]; simp [hy]
  have hok1 : σ1.vars "bfok" = 1 := by rw [h1]; simp
  obtain ⟨σ2, hr2, ⟨hc2, hok2, hiff2⟩, hfv2, -, -, -⟩ := (feasG_spec hb f).frame σ1
    ⟨hc1, by omega⟩
  obtain ⟨σ3, hr3, ⟨hJ, hbn⟩, hfv3, -, -, -⟩ := (fairCom_spec hb f).frame σ2 ⟨hc2, hok2⟩
  refine ⟨σ3, (hr1.seq (hr2.seq hr3)).mono (le_of_eq (by simp only [hs]; rfl)), hJ.ctx, hJ.hok,
    ?_, ?_, ?_⟩
  · rw [hJ.hiff, hiff2, hok1]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h2, fun j hj => h3 j (by omega)⟩
    · rintro ⟨h2, h3⟩; exact ⟨⟨rfl, h2⟩, fun j hj => h3 j (by omega)⟩
  · rw [hfv3 "bfans" (by decide), hfv2 "bfans" (by decide), hv1 _ (by decide)]
  · rw [hfv3 "bfdn" (by decide), hfv2 "bfdn" (by decide), hv1 _ (by decide)]

set_option maxHeartbeats 1600000 in
theorem rec_spec :
    Spec B (fun σ => σ.vars "bfok" ≤ 1 ∧ 1 < B) recCom
      (fun σ σ' => σ'.vars "bfans" = if σ.vars "bfok" = 1 then 1 else σ.vars "bfans") 7 := by
  run_vcg
  all_goals simp_all

end Lax117284Proofs.Machine.ClBrute

end

/-! ### `Lax117284Proofs.Machine.ClBruteBody` -/

section
/-!
One round of the search: test the vector, record a success, add one.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

/-- The cost of the increment. -/
def costOdo (m n : ℕ) : ℕ := 2 + ((20 + 4) * (m * n) + 6)

/-- The cost of one round. -/
def costBody (m n : ℕ) : ℕ := costEval m n + (7 + (costOdo m n + 2))

/-- The state of the search: the vector `f` in `bfsc`; while `bfdn = 0`, `bfans` says whether a
vector below `f` passed; once `bfdn = 1`, whether any vector passed. -/
def J (x : List ℕ) (I : Instance) (k : ℕ) (σ : Env) : Prop :=
  ∃ f : ℕ → ℕ, Ctx x I k f σ ∧ σ.vars "bfans" ≤ 1 ∧ σ.vars "bfdn" ≤ 1 ∧
    (σ.vars "bfdn" = 0 → (σ.vars "bfans" = 1 ↔
      ∃ s, s < enc f (I.days * I.clients) ∧ Chk I k s)) ∧
    (σ.vars "bfdn" = 1 → (σ.vars "bfans" = 1 ↔ ∃ s, s < 2 ^ (I.days * I.clients) ∧ Chk I k s))

/-- The number of the vector in `bfsc`. -/
def encA (I : Instance) (σ : Env) : ℕ :=
  enc (fun r => (σ.arrs "bfsc").getD r 0) (I.days * I.clients)

/-- What is left to search. -/
def Vm (I : Instance) (σ : Env) : ℕ :=
  if σ.vars "bfdn" = 0 then 2 ^ (I.days * I.clients) - encA I σ else 0

lemma encA_eq {f : ℕ → ℕ} {σ : Env} (h : Ctx x I k f σ) : encA I σ = enc f (I.days * I.clients) :=
  enc_congr fun _ hr => h.scGet hr

lemma chk_iff {f : ℕ → ℕ} (hf : ∀ r, r < I.days * I.clients → f r ≤ 1) :
    Chk I k (enc f (I.days * I.clients)) ↔ FeasF I f ∧ FairF I k f := by
  have hd : ∀ r, r < I.days * I.clients → dig (enc f (I.days * I.clients)) r = f r :=
    fun r hr => dig_enc hf r hr
  unfold Chk
  rw [feasF_congr I hd, fairF_congr I hd]

lemma succ_exists (P : ℕ → Prop) (S : ℕ) :
    (∃ s, s < S + 1 ∧ P s) ↔ (∃ s, s < S ∧ P s) ∨ P S := by
  constructor
  · rintro ⟨s, hs, hp⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | rfl
    · exact Or.inl ⟨s, h, hp⟩
    · exact Or.inr hp
  · rintro (⟨s, hs, hp⟩ | hp)
    · exact ⟨s, by omega, hp⟩
    · exact ⟨S, by omega, hp⟩

open Classical in
lemma record_iff {ans0 ok S T : ℕ} {P : ℕ → Prop} (hT : T = S + 1)
    (h0 : ans0 = 1 ↔ ∃ s, s < S ∧ P s) (hok : ok = 1 ↔ P S) :
    (if ok = 1 then 1 else ans0) = 1 ↔ ∃ s, s < T ∧ P s := by
  rw [hT, succ_exists]
  by_cases h : ok = 1
  · rw [if_pos h]; exact ⟨fun _ => Or.inr (hok.mp h), fun _ => rfl⟩
  · rw [if_neg h, h0]
    constructor
    · exact Or.inl
    · rintro (h1 | h1)
      · exact h1
      · exact absurd (hok.mpr h1) h

theorem body_spec (hb : Bd B x I k) :
    Spec B (fun σ => J x I k σ ∧ σ.vars "bfdn" = 0) bodyCom
      (fun σ σ' => J x I k σ' ∧ Vm I σ' < Vm I σ) (costBody I.days I.clients) := by
  intro σ ⟨⟨f, hctx, hans, hdn, h0, h1⟩, hd0⟩
  have hbig := hb.big
  obtain ⟨σ1, hr1, hc1, hok1, hiff1, hans1, hdn1⟩ := evalCom_spec hb f σ hctx
  obtain ⟨σ2, hr2, hans2, hfv2, hfa2, -, -⟩ := (rec_spec (B := B)).frame σ1
    ⟨hok1, by omega⟩
  have hc2 : Ctx x I k f σ2 := hc1.frame hfv2 hfa2 (by decide) (by decide) (by decide)
  obtain ⟨σ3, hr3, ⟨g, hc3, hcy3, henc3, -⟩, hfv3, hfa3, -, -⟩ := (odoCom_spec hb f).frame σ2 hc2
  obtain ⟨σ4, hr4, h4⟩ := (Spec.assign (B := B) (x := "bfdn") (e := V "bfcy")
    (f := fun σ => σ.vars "bfcy")
    (P := fun σ => σ.vars "bfcy" ≤ 1)
    (fun σ h => evalB_var (by omega))) σ3 hcy3
  have hsv : (V "bfcy").size = 1 := rfl
  have hc4 : Ctx x I k g σ4 := by rw [h4]; exact hc3.setVar _ (by decide)
  have hans3 : σ3.vars "bfans" = σ2.vars "bfans" := hfv3 _ (by decide)
  have hans4 : σ4.vars "bfans" = σ3.vars "bfans" := by rw [h4]; simp
  have hdn4 : σ4.vars "bfdn" = σ3.vars "bfcy" := by rw [h4]; simp
  have hS : enc f (I.days * I.clients) < 2 ^ (I.days * I.clients) := enc_lt hctx.hf
  have hset : σ2.vars "bfans" =
      if σ1.vars "bfok" = 1 then 1 else σ1.vars "bfans" := hans2
  have hv : σ1.vars "bfans" = σ.vars "bfans" := hans1
  have hdn' : σ1.vars "bfdn" = σ.vars "bfdn" := hdn1
  have hchk : σ1.vars "bfok" = 1 ↔ Chk I k (enc f (I.days * I.clients)) := by
    rw [chk_iff hctx.hf]; exact hiff1
  have h0' := h0 hd0
  have hV : Vm I σ = 2 ^ (I.days * I.clients) - enc f (I.days * I.clients) := by
    rw [Vm, if_pos hd0, encA_eq hctx]
  have hE4 : encA I σ4 = enc g (I.days * I.clients) := encA_eq hc4
  refine ⟨σ4, hr1.seq (hr2.seq (hr3.seq hr4)) |>.mono (le_of_eq (by simp only [hsv]; rfl)),
    ⟨g, hc4, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hans4, hans3, hset, hv]; split_ifs <;> omega
  · rw [hdn4]; exact hcy3
  · intro hd
    rw [hdn4] at hd
    rw [hd] at henc3
    rw [hans4, hans3, hset, hv]
    refine record_iff (by omega) h0' hchk
  · intro hd
    rw [hdn4] at hd
    rw [hd] at henc3
    rw [hans4, hans3, hset, hv]
    refine record_iff (by omega) h0' hchk
  · rw [hV, Vm, hdn4]
    by_cases hc : σ3.vars "bfcy" = 0
    · rw [if_pos hc, hE4]; rw [hc] at henc3; omega
    · rw [if_neg hc]; omega

end Lax117284Proofs.Machine.ClBrute

end

/-! ### `Lax117284Proofs.Machine.ClBruteMain` -/

section
/-!
The whole search, and its correctness: `bfans` ends `1` exactly when a fair schedule exists.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

/-- The cost of the loop over all vectors. -/
def costLoop (m n : ℕ) : ℕ := (1 + 3 + costBody m n) * 2 ^ (m * n) + 1 + 3

/-- **The cost of the brute force**: three initialisations and the loop. -/
def bruteCost (m n : ℕ) : ℕ := 4 + (2 + (2 + costLoop m n))

lemma dn_zero_of_true {σ : Env}
    (h : (Cond.eq (V "bfdn") (lit 0)).evalB B σ = some true) : σ.vars "bfdn" = 0 := by
  simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  simpa using hr.symm

lemma dn_ne_of_false {σ : Env}
    (h : (Cond.eq (V "bfdn") (lit 0)).evalB B σ = some false) : σ.vars "bfdn" ≠ 0 := by
  simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  simpa using hr.symm

theorem loop_spec (hb : Bd B x I k) :
    Spec B (fun σ => J x I k σ) (.while (.eq (V "bfdn") (lit 0)) bodyCom)
      (fun _ σ' => J x I k σ' ∧ (Cond.eq (V "bfdn") (lit 0)).evalB B σ' = some false)
      (costLoop I.days I.clients) := by
  have hsz : (Cond.eq (V "bfdn") (lit 0)).size = 3 := rfl
  refine Spec.while_count (J x I k) (Vm I) (costBody I.days I.clients) ?_
    ((body_spec hb).pre (fun σ h => ⟨h.1, dn_zero_of_true h.2⟩)) (fun σ h => h) ?_
  · rintro σ ⟨f, hctx, hans, hdn, -, -⟩
    exact ⟨_, evalB_condEq (evalB_var (by have := hb.big; omega))
      (evalB_lit (by have := hb.big; omega))⟩
  · rintro σ ⟨f, hctx, -⟩
    rw [hsz, costLoop]
    have hV : Vm I σ ≤ 2 ^ (I.days * I.clients) := by
      unfold Vm; split_ifs
      · exact Nat.sub_le _ _
      · exact Nat.zero_le _
    have := Nat.mul_le_mul_left (1 + 3 + costBody I.days I.clients) hV
    omega

end Lax117284Proofs.Machine.ClBrute

end

/-! ### `Lax117284Proofs.Machine.ClBruteFinal` -/

section
/-!
The brute force decides whether a fair schedule exists, in time `2 ^ (m * n)` times a
polynomial.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

/-! ### The cost -/

lemma costBody_le (m n : ℕ) : costBody m n ≤ 1000 * (m * n + n + 2) ^ 2 := by
  have hfe : costFeas m n = 69 * (m * n) * n + 37 * (m * n) + 18 * m + 6 := by
    unfold costFeas; ring
  have hfa : costFair m n = 17 * (m * n) + 32 * n + 6 := by
    unfold costFair; ring
  have ho : costOdo m n = 24 * (m * n) + 8 := by unfold costOdo; ring
  unfold costBody costEval costFeasG
  rw [hfe, hfa, ho]
  have hm : 0 < n → m ≤ m * n := fun h => Nat.le_mul_of_pos_right m h
  generalize m * n = p at *
  by_cases hn : n = 0
  · subst hn; simp only [if_true]; nlinarith
  · have hm := hm (Nat.pos_of_ne_zero hn)
    rw [if_neg hn]
    nlinarith

theorem bruteCost_le (m n : ℕ) :
    bruteCost m n ≤ 5000 * 2 ^ (m * n) * (m * n + n + 2) ^ 2 := by
  have hb := costBody_le m n
  have hY : 1 ≤ 2 ^ (m * n) := Nat.one_le_two_pow
  unfold bruteCost costLoop
  generalize 2 ^ (m * n) = Y at *
  generalize m * n = p at *
  have hN : 4 ≤ (p + n + 2) ^ 2 := by
    have := Nat.pow_le_pow_left (show 2 ≤ p + n + 2 by omega) 2
    simpa using this
  generalize (p + n + 2) ^ 2 = N at *
  generalize costBody m n = c at *
  nlinarith

/-! ### The correctness -/

open Classical in
theorem brute_core (hb : Bd B x I k) :
    Spec B (fun σ => σ.arrs "X" = x ∧ σ.vars "n" = I.clients ∧ σ.vars "m" = I.days ∧
        σ.vars "k" = k ∧ σ.arrs "bfsc" = List.replicate (I.days * I.clients) 0) bruteCom
      (fun _ σ' => σ'.vars "bfans" = (if I.HasKFairSchedule k then 1 else 0) ∧
        σ'.arrs "X" = x ∧ σ'.vars "n" = I.clients ∧ σ'.vars "m" = I.days ∧ σ'.vars "k" = k)
      (bruteCost I.days I.clients) := by
  intro σ ⟨hX, hn, hm, hk, hsc⟩
  have hbig := hb.big
  have hmn := hb.mnB
  have hs1 : ((V "n").mul (V "m")).size = 3 := rfl
  have hs2 : (lit 0).size = 1 := rfl
  obtain ⟨σ1, hr1, rfl⟩ := (Spec.assign (B := B) (x := "bfmn") (e := .mul (V "n") (V "m"))
    (f := fun σ => σ.vars "n" * σ.vars "m")
    (P := fun σ => σ.vars "n" = I.clients ∧ σ.vars "m" = I.days)
    (fun σ h => evalB_bin (evalB_var (by rw [h.1]; exact hb.nB)) (evalB_var (by rw [h.2]; exact hb.mB))
      (by rw [Bop.apply_mul, h.1, h.2, Nat.mul_comm]; omega))) σ ⟨hn, hm⟩
  obtain ⟨σ2, hr2, rfl⟩ := (Spec.assign (B := B) (x := "bfans") (e := lit 0) (f := fun _ => 0)
    (P := fun _ => True) (fun _ _ => evalB_lit (by omega))) (σ.setVar "bfmn" (σ.vars "n" * σ.vars "m")) trivial
  obtain ⟨σ3, hr3, rfl⟩ := (Spec.assign (B := B) (x := "bfdn") (e := lit 0) (f := fun _ => 0)
    (P := fun _ => True) (fun _ _ => evalB_lit (by omega)))
    ((σ.setVar "bfmn" (σ.vars "n" * σ.vars "m")).setVar "bfans" 0) trivial
  obtain ⟨σ', hrun, ⟨f', hc', hans', hdn', h0', h1'⟩, hfalse⟩ := loop_spec hb
    (((σ.setVar "bfmn" (σ.vars "n" * σ.vars "m")).setVar "bfans" 0).setVar "bfdn" 0)
    ⟨fun _ => 0, ⟨by simpa [Env.setVar] using hX, by simp [Env.setVar, hn], by simp [Env.setVar, hm],
      by simp [Env.setVar, hk], by simp [Env.setVar, hn, hm, Nat.mul_comm],
      by simp [Env.setVar, hsc, replicate_eq_arrOf], fun _ _ => Nat.zero_le _⟩,
      by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar, enc], by simp [Env.setVar]⟩
  have hdn1 : σ'.vars "bfdn" = 1 := by have := dn_ne_of_false hfalse; omega
  have hiff : σ'.vars "bfans" = 1 ↔ I.HasKFairSchedule k := by
    rw [h1' hdn1, ← hasK_iff]
  refine ⟨σ', (hr1.seq (hr2.seq (hr3.seq hrun))).mono (le_of_eq (by simp only [hs1, hs2]; rfl)),
    ?_, hc'.hx, hc'.hn, hc'.hm, hc'.hk⟩
  split_ifs with hK
  · exact hiff.mpr hK
  · have : σ'.vars "bfans" ≠ 1 := fun h => hK (hiff.mp h)
    omega

open Classical in
/-- **The brute force decides the existence of a fair schedule.** Started on the word `x`, which
encodes the instance `I` and the fairness parameter `k`, with `bfsc` all zeros, `bruteCom` leaves
`1` in `bfans` if the instance has a `k`-fair schedule and `0` otherwise, at a cost of
`bruteCost m n`, which is at most `5000 * 2 ^ (m * n) * (m * n + n + 2) ^ 2` (`bruteCost_le`). -/
theorem brute_spec (I : Instance) (x : List ℕ) (k B : ℕ) (hdec : EncodesUniform x I k)
    (hB : 4 * x.length + 64 < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (fun σ => σ.arrs "X" = x ∧ σ.vars "n" = I.clients ∧ σ.vars "m" = I.days ∧
        σ.vars "k" = k ∧ σ.arrs "bfsc" = List.replicate (I.days * I.clients) 0)
      bruteCom
      (fun σ σ' => σ'.vars "bfans" = (if I.HasKFairSchedule k then 1 else 0) ∧ σ'.arrs "X" = x ∧
        σ'.vars "n" = σ.vars "n" ∧ σ'.vars "m" = σ.vars "m" ∧ σ'.vars "k" = σ.vars "k" ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out)
      (bruteCost I.days I.clients) := by
  refine ((brute_core (B := B) (x := x) (I := I) (k := k) ⟨hdec, hB, hX⟩).frame).post ?_
  rintro σ σ' ⟨-, hn, hm, hk, -⟩ ⟨⟨hans, hx, hn', hm', hk'⟩, -, -, hrd, hwr⟩
  exact ⟨hans, hx, by rw [hn', hn], by rw [hm', hm], by rw [hk', hk], hrd (by decide),
    hwr (by decide)⟩

end Lax117284Proofs.Machine.ClBrute

end
