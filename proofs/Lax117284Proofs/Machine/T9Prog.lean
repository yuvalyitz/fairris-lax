import Lax117284Proofs.Machine.T9Comp1
import Lax117284Proofs.Machine.T9Comp2

/-!
The program that writes the clauses of Theorem 9: one loop over the conflict clauses and one over
the validation clauses, each clause computed from its index.
-/

namespace Lax117284Proofs.Machine.T9Prog

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.T9Sem
open Lax117284Proofs.Machine.InstSem Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Machine.T9Comp1 Lax117284Proofs.Machine.T9Comp2

variable {B : ℕ}

lemma clB_conf (arr : List ℕ) (n m c : ℕ) (hc : c < m * n * n)
    (h : c % (n * n) / n ≠ c % (n * n) % n ∧
      confG arr n (c / (n * n)) (c % (n * n) / n) (c % (n * n) % n)) :
    clB arr n m c = bitsNat (c / (n * n) * n + c % (n * n) / n) ++ [0] ++
      bitsNat (c / (n * n) * n + c % (n * n) % n) ++ [0] := by
  unfold clB clauseG
  rw [if_pos hc, if_pos h]
  simp [sb]

lemma clB_non (arr : List ℕ) (n m c : ℕ) (hc : c < m * n * n)
    (h : ¬ (c % (n * n) / n ≠ c % (n * n) % n ∧
      confG arr n (c / (n * n)) (c % (n * n) / n) (c % (n * n) % n))) :
    clB arr n m c = bitsNat (c / (n * n) * n + c % (n * n) / n) ++ [1] ++
      bitsNat (c / (n * n) * n + c % (n * n) / n) ++ [0] := by
  unfold clB clauseG
  rw [if_pos hc, if_neg h]
  simp [sb]

/-- The branching of a conflict clause. -/
def br1 : Com :=
  .ite (.eq (V "j1") (V "j2")) (emitClause "x1" "x1" 1 0)
    (.ite (.lt (sub (V "da") (V "pa")) (V "db"))
      (.ite (.lt (sub (V "db") (V "pb")) (V "da")) (emitClause "x1" "x2" 0 0)
        (emitClause "x1" "x1" 1 0))
      (emitClause "x1" "x1" 1 0))

/-- Write a conflict clause. -/
def body1 : Com := .seq comp1 br1

/-- The cost of a conflict clause. -/
def K1 (Sz : ℕ) : ℕ := 320 + 2 * (48 * Sz + 50)

/-- **A conflict clause.** -/
theorem body1_run (Sz : ℕ) (arr : List ℕ) (n m c : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ.arrs "TK" = arr) (hi : σ.vars "i" = c) (hn : σ.vars "n" = n)
    (hnn : σ.vars "nn" = n * n) (hc : c < m * n * n) (hcB : c + 8 < B) (hnB : n + 8 < B)
    (hnnB : n * n + 8 < B) (hmnB : m * n + 8 < B)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 + 8 < B) (hL : 3 + 2 * (m * n) + 8 < B)
    (hlen : 3 + 2 * (m * n) ≤ arr.length) :
    ∃ σ', Run B body1 σ σ' (K1 Sz) ∧ σ'.out = σ.out ++ clB arr n m c ∧
      (∀ y ∉ S9, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨σ1, r1, a1, o1, hj1, hj2, hx1, hx2, hpa, hda, hpb, hdb, hfr⟩ :=
    comp1_run (B := B) arr n m c σ hA hi hn hnn hc hcB hnB hnnB hmnB hE hL hlen
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hc; simp at hc
    · exact h
  have hnn0 : 0 < n * n := Nat.mul_pos hn0 hn0
  have hai : c / (n * n) < m := by
    rw [Nat.div_lt_iff_lt_mul hnn0, ← Nat.mul_assoc]; exact hc
  have hrl : c % (n * n) < n * n := Nat.mod_lt _ hnn0
  have hj1l : c % (n * n) / n < n := by rw [Nat.div_lt_iff_lt_mul hn0]; exact hrl
  have hj2l : c % (n * n) % n < n := Nat.mod_lt _ hn0
  have hx1l := cell_lt hai hj1l
  have hx2l := cell_lt hai hj2l
  have hbase : ∀ σ'' : Env, (∀ y ∉ ["v", "s", "u", "i2"], σ''.vars y = σ1.vars y) →
      σ''.arrs = σ1.arrs → (∀ y ∉ S9, σ''.vars y = σ.vars y) ∧ σ''.arrs = σ.arrs := by
    intro σ'' hv ha
    refine ⟨fun y hy => ?_, by rw [ha, a1]⟩
    have hyA : y ∉ A1 := fun h => hy (by
      simp only [A1, S9, List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at h ⊢
      tauto)
    rw [hv y (nscr_of_s9 hy), hfr y hyA]
  have hx1B : σ1.vars "x1" + 4 < B := by rw [hx1]; omega
  have hx2B : σ1.vars "x2" + 4 < B := by rw [hx2]; omega
  have hcondj : (Cond.eq (V "j1") (V "j2")).evalB B σ1 = some (c % (n * n) / n ==
      c % (n * n) % n) := by
    have h := evalB_condEq (B := B) (σ := σ1)
      (evalB_var (B := B) (x := "j1") (σ := σ1) (by rw [hj1]; omega))
      (evalB_var (B := B) (x := "j2") (σ := σ1) (by rw [hj2]; omega))
    rw [hj1, hj2] at h
    exact h
  by_cases hj : c % (n * n) / n = c % (n * n) % n
  · have hT : (Cond.eq (V "j1") (V "j2")).evalB B σ1 = some true := by rw [hcondj, beq_iff_eq.2 hj]
    obtain ⟨σ2, r2, o2, v2, a2⟩ := emitClause_run (B := B) Sz "x1" "x1" 1 0 σ1 hs (by decide)
      (by decide) hx1B hx1B (by omega) (by omega)
    obtain ⟨hv, ha⟩ := hbase σ2 v2 a2
    refine ⟨σ2, (r1.seq (Run.ite_true hT r2)).mono ?_, ?_, hv, ha⟩
    · simp [Cond.size, Expr.size, K1] <;> omega
    · rw [o2, o1, hx1, clB_non arr n m c hc (fun h => h.1 hj)]
  · have hF : (Cond.eq (V "j1") (V "j2")).evalB B σ1 = some false := by rw [hcondj, beq_eq_false_iff_ne.2 hj]
    have kA : 2 + 2 * (c / (n * n) * n + c % (n * n) / n) + 1 < 3 + 2 * (m * n) := by omega
    have kB : 2 + 2 * (c / (n * n) * n + c % (n * n) / n) < 3 + 2 * (m * n) := by omega
    have kC : 2 + 2 * (c / (n * n) * n + c % (n * n) % n) + 1 < 3 + 2 * (m * n) := by omega
    have kD : 2 + 2 * (c / (n * n) * n + c % (n * n) % n) < 3 + 2 * (m * n) := by omega
    have hda' : σ1.vars "da" < B := by
      rw [hda]; have := hE _ kA; omega
    have hpa' : σ1.vars "pa" < B := by
      rw [hpa]; have := hE _ kB; omega
    have hdb' : σ1.vars "db" < B := by
      rw [hdb]; have := hE _ kC; omega
    have hpb' : σ1.vars "pb" < B := by
      rw [hpb]; have := hE _ kD; omega
    have hc2 : (Cond.lt (sub (V "da") (V "pa")) (V "db")).evalB B σ1 = some (decide
        (σ1.vars "da" - σ1.vars "pa" < σ1.vars "db")) := by
      have h := evalB_condLt (B := B) (σ := σ1)
        (evalB_bin (B := B) (op := .sub) (evalB_var (B := B) (x := "da") (σ := σ1) hda')
          (evalB_var (B := B) (x := "pa") (σ := σ1) hpa') (by simp; omega))
        (evalB_var (B := B) (x := "db") (σ := σ1) hdb')
      simp only [Bop.apply_sub] at h
      exact h
    have hc3 : (Cond.lt (sub (V "db") (V "pb")) (V "da")).evalB B σ1 = some (decide
        (σ1.vars "db" - σ1.vars "pb" < σ1.vars "da")) := by
      have h := evalB_condLt (B := B) (σ := σ1)
        (evalB_bin (B := B) (op := .sub) (evalB_var (B := B) (x := "db") (σ := σ1) hdb')
          (evalB_var (B := B) (x := "pb") (σ := σ1) hpb') (by simp; omega))
        (evalB_var (B := B) (x := "da") (σ := σ1) hda')
      simp only [Bop.apply_sub] at h
      exact h
    have hconf : confG arr n (c / (n * n)) (c % (n * n) / n) (c % (n * n) % n) ↔
        (σ1.vars "da" - σ1.vars "pa" < σ1.vars "db" ∧ σ1.vars "db" - σ1.vars "pb" < σ1.vars "da") := by
      rw [hda, hpa, hdb, hpb]
      unfold confG
      simp
    by_cases h2 : σ1.vars "da" - σ1.vars "pa" < σ1.vars "db"
    · have hT2 : (Cond.lt (sub (V "da") (V "pa")) (V "db")).evalB B σ1 = some true := by
        rw [hc2]; simp [h2]
      by_cases h3 : σ1.vars "db" - σ1.vars "pb" < σ1.vars "da"
      · have hT3 : (Cond.lt (sub (V "db") (V "pb")) (V "da")).evalB B σ1 = some true := by
          rw [hc3]; simp [h3]
        obtain ⟨σ2, r2, o2, v2, a2⟩ := emitClause_run (B := B) Sz "x1" "x2" 0 0 σ1 hs (by decide)
          (by decide) hx1B hx2B (by omega) (by omega)
        obtain ⟨hv, ha⟩ := hbase σ2 v2 a2
        refine ⟨σ2, (r1.seq (Run.ite_false hF (Run.ite_true hT2 (Run.ite_true hT3 r2)))).mono ?_,
          ?_, hv, ha⟩
        · simp [Cond.size, Expr.size, K1] <;> omega
        · rw [o2, o1, hx1, hx2, clB_conf arr n m c hc ⟨hj, hconf.2 ⟨h2, h3⟩⟩]
      · have hF3 : (Cond.lt (sub (V "db") (V "pb")) (V "da")).evalB B σ1 = some false := by
          rw [hc3]; simp [h3]
        obtain ⟨σ2, r2, o2, v2, a2⟩ := emitClause_run (B := B) Sz "x1" "x1" 1 0 σ1 hs (by decide)
          (by decide) hx1B hx1B (by omega) (by omega)
        obtain ⟨hv, ha⟩ := hbase σ2 v2 a2
        refine ⟨σ2, (r1.seq (Run.ite_false hF (Run.ite_true hT2 (Run.ite_false hF3 r2)))).mono ?_,
          ?_, hv, ha⟩
        · simp [Cond.size, Expr.size, K1] <;> omega
        · rw [o2, o1, hx1, clB_non arr n m c hc (fun h => h3 (hconf.1 h.2).2)]
    · have hF2 : (Cond.lt (sub (V "da") (V "pa")) (V "db")).evalB B σ1 = some false := by
        rw [hc2]; simp [h2]
      obtain ⟨σ2, r2, o2, v2, a2⟩ := emitClause_run (B := B) Sz "x1" "x1" 1 0 σ1 hs (by decide)
        (by decide) hx1B hx1B (by omega) (by omega)
      obtain ⟨hv, ha⟩ := hbase σ2 v2 a2
      refine ⟨σ2, (r1.seq (Run.ite_false hF (Run.ite_false hF2 r2))).mono ?_, ?_, hv, ha⟩
      · simp [Cond.size, Expr.size, K1] <;> omega
      · rw [o2, o1, hx1, clB_non arr n m c hc (fun h => h2 (hconf.1 h.2).1)]


lemma clB_v_ne (arr : List ℕ) (n m c : ℕ)
    (h : c % (m * m) / m ≠ c % (m * m) % m) :
    clB arr n m (m * n * n + c) = bitsNat (c % (m * m) / m * n + c / (m * m)) ++ [1] ++
      bitsNat (c % (m * m) % m * n + c / (m * m)) ++ [1] := by
  unfold clB clauseG
  rw [if_neg (by omega), Nat.add_sub_cancel_left, if_pos h]
  simp [sb]

lemma clB_v_eq (arr : List ℕ) (n m c : ℕ)
    (h : ¬ c % (m * m) / m ≠ c % (m * m) % m) :
    clB arr n m (m * n * n + c) = bitsNat (c % (m * m) / m * n + c / (m * m)) ++ [1] ++
      bitsNat (c % (m * m) / m * n + c / (m * m)) ++ [0] := by
  unfold clB clauseG
  rw [if_neg (by omega), Nat.add_sub_cancel_left, if_neg h]
  simp [sb]

/-- The branching of a validation clause. -/
def br2 : Com :=
  .ite (.eq (V "i1") (V "i2")) (emitClause "x1" "x1" 1 0) (emitClause "x1" "x2" 1 1)

/-- Write a validation clause. -/
def body2 : Com := .seq comp2 br2

/-- **A validation clause.** -/
theorem body2_run (Sz : ℕ) (arr : List ℕ) (n m c : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hi : σ.vars "i" = c) (hn : σ.vars "n" = n) (hm : σ.vars "m" = m)
    (hmm : σ.vars "mm" = m * m) (hc : c < n * m * m) (hcB : c + 8 < B) (hmB : m + 8 < B)
    (hmmB : m * m + 8 < B) (hmnB : m * n + 8 < B) :
    ∃ σ', Run B body2 σ σ' (K1 Sz) ∧ σ'.out = σ.out ++ clB arr n m (m * n * n + c) ∧
      (∀ y ∉ S9, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨σ1, r1, a1, o1, hi1, hi2, hx1, hx2, hfr⟩ :=
    comp2_run (B := B) n m c σ hi hn hm hmm hc hcB hmB hmmB hmnB
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hc; simp at hc
    · exact h
  have hmm0 : 0 < m * m := Nat.mul_pos hm0 hm0
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hc; simp at hc
    · exact h
  have hj : c / (m * m) < n := by
    rw [Nat.div_lt_iff_lt_mul hmm0]
    have : n * m * m = n * (m * m) := Nat.mul_assoc _ _ _
    omega
  have hrl : c % (m * m) < m * m := Nat.mod_lt _ hmm0
  have hi1l : c % (m * m) / m < m := by rw [Nat.div_lt_iff_lt_mul hm0]; exact hrl
  have hi2l : c % (m * m) % m < m := Nat.mod_lt _ hm0
  have hx1l := cell_lt hi1l hj
  have hx2l := cell_lt hi2l hj
  have hbase : ∀ σ'' : Env, (∀ y ∉ ["v", "s", "u", "i2"], σ''.vars y = σ1.vars y) →
      σ''.arrs = σ1.arrs → (∀ y ∉ S9, σ''.vars y = σ.vars y) ∧ σ''.arrs = σ.arrs := by
    intro σ'' hv ha
    refine ⟨fun y hy => ?_, by rw [ha, a1]⟩
    have hyA : y ∉ A2 := fun h => hy (by
      simp only [A2, S9, List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at h ⊢
      tauto)
    rw [hv y (nscr_of_s9 hy), hfr y hyA]
  have hx1B : σ1.vars "x1" + 4 < B := by rw [hx1]; omega
  have hx2B : σ1.vars "x2" + 4 < B := by rw [hx2]; omega
  have hcondj : (Cond.eq (V "i1") (V "i2")).evalB B σ1 = some (c % (m * m) / m ==
      c % (m * m) % m) := by
    have h := evalB_condEq (B := B) (σ := σ1)
      (evalB_var (B := B) (x := "i1") (σ := σ1) (by rw [hi1]; omega))
      (evalB_var (B := B) (x := "i2") (σ := σ1) (by rw [hi2]; omega))
    rw [hi1, hi2] at h
    exact h
  by_cases hj' : c % (m * m) / m = c % (m * m) % m
  · have hT : (Cond.eq (V "i1") (V "i2")).evalB B σ1 = some true := by
      rw [hcondj, beq_iff_eq.2 hj']
    obtain ⟨σ2, r2, o2, v2, a2⟩ := emitClause_run (B := B) Sz "x1" "x1" 1 0 σ1 hs (by decide)
      (by decide) hx1B hx1B (by omega) (by omega)
    obtain ⟨hv, ha⟩ := hbase σ2 v2 a2
    refine ⟨σ2, (r1.seq (Run.ite_true hT r2)).mono ?_, ?_, hv, ha⟩
    · simp [Cond.size, Expr.size, K1] <;> omega
    · rw [o2, o1, hx1, clB_v_eq arr n m c (fun h => h hj')]
  · have hF : (Cond.eq (V "i1") (V "i2")).evalB B σ1 = some false := by
      rw [hcondj, beq_eq_false_iff_ne.2 hj']
    obtain ⟨σ2, r2, o2, v2, a2⟩ := emitClause_run (B := B) Sz "x1" "x2" 1 1 σ1 hs (by decide)
      (by decide) hx1B hx2B (by omega) (by omega)
    obtain ⟨hv, ha⟩ := hbase σ2 v2 a2
    refine ⟨σ2, (r1.seq (Run.ite_false hF r2)).mono ?_, ?_, hv, ha⟩
    · simp [Cond.size, Expr.size, K1] <;> omega
    · rw [o2, o1, hx1, hx2, clB_v_ne arr n m c hj']

end Lax117284Proofs.Machine.T9Prog
