import Lax117284Proofs.Machine.UEmit
import Lax117284Proofs.Machine.USem

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
