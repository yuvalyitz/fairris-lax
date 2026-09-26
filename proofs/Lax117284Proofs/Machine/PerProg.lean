import Lax117284Proofs.Machine.Emit
import Lax117284Proofs.Machine.BlockProg
import Lax117284Proofs.Machine.PerCheck

/-!
The program that writes the image of Lemma 15 once the numbers of its input are in an array: the
counts with two more clients and twice the days, the table cell by cell from its closed form, and
the parameter `m`.
-/

namespace Lax117284Proofs.Machine.PerProg

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.PerSem Lax117284Proofs.Machine.BlockProg
open Lax117284Proofs.Machine.InstSem

variable {B : ℕ}

/-- Write a cell of the additional days that belongs to an original client. -/
def newCell : Com :=
  .seq (emitLit 1)
    (.seq (.assign "kj" (.get "TK" (add (add (.lit 2) (V "N2")) (V "cb"))))
      (.seq (.assign "cr" (sub (V "ca") (V "m")))
        (.ite (.lt (V "cr") (V "kj"))
          (emitVal (add (V "g") (add (V "cb") (.lit 1))))
          (emitVal (add (add (V "g") (V "n1")) (add (V "cb") (.lit 1)))))))

/-- Scratch scalars of a cell. -/
def SCP : List String := SCB ++ ["kj", "cr"]

lemma scb_of_scp {y : String} (h : y ∉ SCP) : y ∉ SCB := fun h' =>
  h (List.mem_append_left _ h')

/-- **A cell of the additional days.** -/
theorem newCell_run (Sz : ℕ) (arr : List ℕ) (n m dm : ℕ) (σ : Env) (a b : ℕ)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ.arrs "TK" = arr) (hca : σ.vars "ca" = a) (hcb : σ.vars "cb" = b)
    (hm : σ.vars "m" = m) (hn1 : σ.vars "n1" = n + 1) (hg : σ.vars "g" = dm)
    (hN2 : σ.vars "N2" = 2 * (m * n))
    (hbn : b < n) (ham : m ≤ a) (haB : a + 8 < B) (hmB : m + 8 < B)
    (hsum : dm + 2 * n + 16 < B)
    (hE : ∀ k < 2 + 2 * (m * n) + n, arr.getD k 0 + 8 < B)
    (hL : 2 + 2 * (m * n) + n + 8 < B) (hlen : 2 + 2 * (m * n) + n ≤ arr.length) :
    ∃ σ', Run B newCell σ σ' (10 + (48 * Sz + 50) + (20 + 20 + (48 * Sz + 60))) ∧
      σ'.out = σ.out ++ (bitsNat 1 ++ bitsNat (if a - m < arr.getD (2 + 2 * (m * n) + b) 0
        then dm + (b + 1) else dm + (n + 1) + (b + 1))) ∧
      (∀ y ∉ SCP, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitLit_spec (B := B) 1 Sz (by omega) (hs _ (by omega)) σ trivial
  have s1 : Same σ σ1 := same_of_frame v1 a1
  have A1 : σ1.arrs "TK" = arr := by rw [a1]; exact hA
  have h1 : ∀ x : String, x ∉ SCR → σ1.vars x = σ.vars x := fun x hx => s1.1 x hx
  have hidx : 2 + 2 * (m * n) + b < 2 + 2 * (m * n) + n := by omega
  have hkjB := hE _ hidx
  -- the bound
  have hkv : σ1.vars "N2" = 2 * (m * n) := by rw [h1 "N2" (by decide)]; exact hN2
  have hcb1 : σ1.vars "cb" = b := by rw [h1 "cb" (by decide)]; exact hcb
  have ev1i : (add (add (.lit 2) (V "N2")) (V "cb")).evalB B σ1 = some (2 + 2 * (m * n) + b) := by
    have h := evalB_bin (B := B) (op := .add)
      (evalB_bin (B := B) (op := .add) (evalB_lit (B := B) (σ := σ1) (n := 2) (by omega))
        (evalB_var (B := B) (x := "N2") (σ := σ1) (by omega)) (by simp [hkv]; omega))
      (evalB_var (B := B) (x := "cb") (σ := σ1) (by omega)) (by simp [hkv, hcb1]; omega)
    simpa [hkv, hcb1] using h
  have ev1 : (Expr.get "TK" (add (add (.lit 2) (V "N2")) (V "cb"))).evalB B σ1
      = some (arr.getD (2 + 2 * (m * n) + b) 0) := by
    have := RunStep.eval_get B σ1 "TK" _ (2 + 2 * (m * n) + b) ev1i (by rw [A1]; omega)
      (by rw [A1]; omega)
    rwa [A1] at this
  have r2 := Run.assign (x := "kj") ev1
  set σ2 := σ1.setVar "kj" (arr.getD (2 + 2 * (m * n) + b) 0) with hσ2
  have hca2 : σ2.vars "ca" = a := by simp [hσ2, Env.setVar, h1 "ca" (by decide), hca]
  have hm2 : σ2.vars "m" = m := by simp [hσ2, Env.setVar, h1 "m" (by decide), hm]
  have ev3 : (sub (V "ca") (V "m")).evalB B σ2 = some (a - m) := by
    have h := evalB_bin (B := B) (op := .sub)
      (evalB_var (B := B) (x := "ca") (σ := σ2) (by omega))
      (evalB_var (B := B) (x := "m") (σ := σ2) (by omega)) (by simp [hca2, hm2]; omega)
    simpa [hca2, hm2] using h
  have r3 := Run.assign (x := "cr") ev3
  set σ3 := σ2.setVar "cr" (a - m) with hσ3
  have hcr3 : σ3.vars "cr" = a - m := by simp [hσ3, Env.setVar]
  have hkj3 : σ3.vars "kj" = arr.getD (2 + 2 * (m * n) + b) 0 := by simp [hσ3, hσ2, Env.setVar]
  have hc : (Cond.lt (V "cr") (V "kj")).evalB B σ3
      = some (decide (a - m < arr.getD (2 + 2 * (m * n) + b) 0)) := by
    have h := evalB_condLt (B := B) (σ := σ3)
      (evalB_var (B := B) (x := "cr") (σ := σ3) (by omega))
      (evalB_var (B := B) (x := "kj") (σ := σ3) (by omega))
    simpa [hcr3, hkj3] using h
  have hcb3 : σ3.vars "cb" = b := by simp [hσ3, hσ2, Env.setVar, hcb1]
  have hg3 : σ3.vars "g" = dm := by simp [hσ3, hσ2, Env.setVar, h1 "g" (by decide), hg]
  have hn13 : σ3.vars "n1" = n + 1 := by
    simp [hσ3, hσ2, Env.setVar, h1 "n1" (by decide), hn1]
  have hbase : ∀ σ' : Env, (∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ3.vars y) →
      σ'.arrs = σ3.arrs → (∀ y ∉ SCP, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
    intro σ' hv ha
    refine ⟨fun y hy => ?_, ?_⟩
    · have hy1 : y ∉ SCR := by
        intro h; exact hy (by simp only [SCP, SCB, List.mem_append]; tauto)
      have hyk : y ≠ "kj" := fun h => hy (by simp [SCP, h])
      have hyr : y ≠ "cr" := fun h => hy (by simp [SCP, h])
      have hy2 : y ∉ ["v", "s", "u", "i2"] := fun h => hy1 (by
        simp only [SCR, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
      rw [hv y hy2]
      simp [hσ3, hσ2, Env.setVar, hyk, hyr, h1 y hy1]
    · rw [ha]; simp [hσ3, hσ2, Env.setVar, a1]
  by_cases hk : a - m < arr.getD (2 + 2 * (m * n) + b) 0
  · have hcT : (Cond.lt (V "cr") (V "kj")).evalB B σ3 = some true := by rw [hc]; exact congrArg some (decide_eq_true hk)
    have ev4 : (add (V "g") (add (V "cb") (.lit 1))).evalB B σ3 = some (dm + (b + 1)) := by
      have h := evalB_bin (B := B) (op := .add) (evalB_var (B := B) (x := "g") (σ := σ3) (by omega))
        (evalB_bin (B := B) (op := .add) (evalB_var (B := B) (x := "cb") (σ := σ3) (by omega))
          (evalB_lit (B := B) (σ := σ3) (n := 1) (by omega)) (by simp [hcb3]; omega))
        (by simp [hg3, hcb3]; omega)
      simpa [hg3, hcb3] using h
    obtain ⟨σ4, r4, o4, v4, a4⟩ := emitVal_spec (B := B)
      (add (V "g") (add (V "cb") (.lit 1))) (fun _ => dm + (b + 1)) Sz σ3
      ⟨ev4, by omega, hs _ (by omega)⟩
    obtain ⟨hv4, ha4⟩ := hbase σ4 v4 a4
    refine ⟨σ4, ((r1.seq (r2.seq (r3.seq (Run.ite_true hcT r4))))).mono ?_, ?_, hv4, ha4⟩
    · simp [Expr.size, Cond.size]; omega
    · rw [o4, if_pos hk]
      simp [hσ3, hσ2, Env.setVar, o1]
  · have hcF : (Cond.lt (V "cr") (V "kj")).evalB B σ3 = some false := by rw [hc]; exact congrArg some (decide_eq_false hk)
    have ev4 : (add (add (V "g") (V "n1")) (add (V "cb") (.lit 1))).evalB B σ3
        = some (dm + (n + 1) + (b + 1)) := by
      have h := evalB_bin (B := B) (op := .add)
        (evalB_bin (B := B) (op := .add) (evalB_var (B := B) (x := "g") (σ := σ3) (by omega))
          (evalB_var (B := B) (x := "n1") (σ := σ3) (by omega)) (by simp [hg3, hn13]; omega))
        (evalB_bin (B := B) (op := .add) (evalB_var (B := B) (x := "cb") (σ := σ3) (by omega))
          (evalB_lit (B := B) (σ := σ3) (n := 1) (by omega)) (by simp [hcb3]; omega))
        (by simp [hg3, hn13, hcb3]; omega)
      simpa [hg3, hn13, hcb3] using h
    obtain ⟨σ4, r4, o4, v4, a4⟩ := emitVal_spec (B := B)
      (add (add (V "g") (V "n1")) (add (V "cb") (.lit 1))) (fun _ => dm + (n + 1) + (b + 1)) Sz σ3
      ⟨ev4, by omega, hs _ (by omega)⟩
    obtain ⟨hv4, ha4⟩ := hbase σ4 v4 a4
    refine ⟨σ4, ((r1.seq (r2.seq (r3.seq (Run.ite_false hcF r4))))).mono ?_, ?_, hv4, ha4⟩
    · simp [Expr.size, Cond.size]; omega
    · rw [o4, if_neg hk]
      simp [hσ3, hσ2, Env.setVar, o1]


/-- **A cell of a new client.** -/
theorem clCell_run (Sz : ℕ) (n dm : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hn1 : σ.vars "n1" = n + 1) (hg : σ.vars "g" = dm) (hsum : dm + 2 * n + 16 < B) :
    ∃ σ', Run B (.seq (emitVar "n1") (emitVal (add (V "g") (V "n1")))) σ σ'
        ((48 * Sz + 50) + (1 + 3 + (48 * Sz + 40))) ∧
      σ'.out = σ.out ++ (bitsNat (n + 1) ++ bitsNat (dm + (n + 1))) ∧
      (∀ y ∉ SCP, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "n1" Sz σ
    ⟨by rw [hn1]; omega, by rw [hn1]; exact hs _ (by omega)⟩
  have h1 : ∀ y ∉ ["v", "s", "u", "i2"], σ1.vars y = σ.vars y := v1
  have hn11 : σ1.vars "n1" = n + 1 := by rw [h1 "n1" (by decide)]; exact hn1
  have hg1 : σ1.vars "g" = dm := by rw [h1 "g" (by decide)]; exact hg
  have ev : (add (V "g") (V "n1")).evalB B σ1 = some (dm + (n + 1)) := by
    have h := evalB_bin (B := B) (op := .add) (evalB_var (B := B) (x := "g") (σ := σ1) (by omega))
      (evalB_var (B := B) (x := "n1") (σ := σ1) (by omega)) (by simp [hg1, hn11]; omega)
    simpa [hg1, hn11] using h
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitVal_spec (B := B) (add (V "g") (V "n1"))
    (fun _ => dm + (n + 1)) Sz σ1 ⟨ev, by omega, hs _ (by omega)⟩
  refine ⟨σ2, (r1.seq r2).mono (by simp [Expr.size]), ?_, fun y hy => ?_, ?_⟩
  · rw [o2, o1, hn1]; simp
  · have hy' : y ∉ ["v", "s", "u", "i2"] := fun h => hy (by
      simp only [SCP, SCB, SCR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      tauto)
    rw [v2 y hy', h1 y hy']
  · rw [a2, a1]

/-- Write a cell of the image. -/
def cellBodyL : Com :=
  .seq (.assign "ca" (.bin .div (V "i") (V "n2")))
  (.seq (.assign "cb" (sub (V "i") (mul (V "ca") (V "n2"))))
   (.ite (.lt (V "cb") (V "n"))
     (.ite (.lt (V "ca") (V "m"))
        (.seq (.assign "cs" (add (mul (V "ca") (V "n")) (V "cb")))
          (.seq (emitCell "cs" 0) (emitCell "cs" 1)))
        newCell)
     (.seq (emitVar "n1") (emitVal (add (V "g") (V "n1"))))))

/-- The cost of a cell. -/
def KcellP (Sz : ℕ) : ℕ := 300 + 4 * (48 * Sz + 60)

/-- **A cell of the image.** -/
theorem cellBodyL_run (Sz : ℕ) (arr : List ℕ) (n m dm : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hm : σ.vars "m" = m)
    (hn2 : σ.vars "n2" = n + 2) (hn1 : σ.vars "n1" = n + 1) (hg : σ.vars "g" = dm)
    (hN2 : σ.vars "N2" = 2 * (m * n))
    (ht : σ.vars "i" < 2 * m * (n + 2)) (hM2 : 2 * m * (n + 2) + 8 < B)
    (hnB : n + 8 < B) (hmB : m + 8 < B) (hsum : dm + 2 * n + 16 < B)
    (hE : ∀ k < 2 + 2 * (m * n) + n, arr.getD k 0 + 8 < B)
    (hL : 2 + 2 * (m * n) + n + 8 < B) (hlen : 2 + 2 * (m * n) + n ≤ arr.length) :
    ∃ σ', Run B cellBodyL σ σ' (KcellP Sz) ∧
      σ'.out = σ.out ++ numBits (cellLG arr n m dm (σ.vars "i")) ∧
      (∀ y ∉ SCP, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨t, ht'⟩ : ∃ t, σ.vars "i" = t := ⟨_, rfl⟩
  rw [ht'] at ht ⊢
  have hn1p : 0 < n + 2 := by omega
  obtain ⟨a, ha⟩ : ∃ a, a = t / (n + 2) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = t % (n + 2) := ⟨_, rfl⟩
  have hdm : (n + 2) * a + b = t := by rw [ha, hb]; exact Nat.div_add_mod t (n + 2)
  have hale : a ≤ t := by rw [ha]; exact Nat.div_le_self _ _
  have hb_lt : b < n + 2 := by rw [hb]; exact Nat.mod_lt _ hn1p
  have ha_lt : a < 2 * m := by rw [ha, Nat.div_lt_iff_lt_mul hn1p]; exact ht
  have hmc : a * (n + 2) = (n + 2) * a := Nat.mul_comm _ _
  have hiB : t < B := by omega
  have ev1 : (Expr.bin .div (V "i") (V "n2")).evalB B σ = some a := by
    have h := evalB_bin (B := B) (op := .div) (evalB_var (B := B) (x := "i") (σ := σ) (by omega))
      (evalB_var (B := B) (x := "n2") (σ := σ) (by omega)) (by simp [hn2, ht']; omega)
    simpa [hn2, ht', ha] using h
  have r1 := Run.assign (x := "ca") ev1
  set σ1 := σ.setVar "ca" a with hσ1
  have h1i : σ1.vars "i" = t := by simp [hσ1, Env.setVar, ht']
  have h1n2 : σ1.vars "n2" = n + 2 := by simp [hσ1, Env.setVar, hn2]
  have h1ca : σ1.vars "ca" = a := by simp [hσ1, Env.setVar]
  have ev2a : (mul (V "ca") (V "n2")).evalB B σ1 = some (a * (n + 2)) := by
    have h := evalB_bin (B := B) (op := .mul) (evalB_var (B := B) (x := "ca") (σ := σ1) (by omega))
      (evalB_var (B := B) (x := "n2") (σ := σ1) (by omega)) (by simp [h1ca, h1n2]; omega)
    simpa [h1ca, h1n2] using h
  have ev2 : (sub (V "i") (mul (V "ca") (V "n2"))).evalB B σ1 = some b := by
    have h := evalB_bin (B := B) (op := .sub) (evalB_var (B := B) (x := "i") (σ := σ1) (by omega))
      ev2a (by simp [h1i]; omega)
    have e : t - a * (n + 2) = b := by omega
    simpa [h1i, e] using h
  have r2 := Run.assign (x := "cb") ev2
  set σ2 := σ1.setVar "cb" b with hσ2
  have h2ca : σ2.vars "ca" = a := by simp [hσ2, Env.setVar, h1ca]
  have h2cb : σ2.vars "cb" = b := by simp [hσ2, Env.setVar]
  have h2n : σ2.vars "n" = n := by simp [hσ2, hσ1, Env.setVar, hn]
  have h2m : σ2.vars "m" = m := by simp [hσ2, hσ1, Env.setVar, hm]
  have h2n1 : σ2.vars "n1" = n + 1 := by simp [hσ2, hσ1, Env.setVar, hn1]
  have h2g : σ2.vars "g" = dm := by simp [hσ2, hσ1, Env.setVar, hg]
  have h2N2 : σ2.vars "N2" = 2 * (m * n) := by simp [hσ2, hσ1, Env.setVar, hN2]
  have h2A : σ2.arrs "TK" = arr := by simp [hσ2, hσ1, Env.setVar, hA]
  have hc1 : (Cond.lt (V "cb") (V "n")).evalB B σ2 = some (decide (b < n)) := by
    have h := evalB_condLt (B := B) (σ := σ2) (evalB_var (B := B) (x := "cb") (σ := σ2) (by omega))
      (evalB_var (B := B) (x := "n") (σ := σ2) (by omega))
    simpa [h2cb, h2n] using h
  have hc2 : (Cond.lt (V "ca") (V "m")).evalB B σ2 = some (decide (a < m)) := by
    have h := evalB_condLt (B := B) (σ := σ2) (evalB_var (B := B) (x := "ca") (σ := σ2) (by omega))
      (evalB_var (B := B) (x := "m") (σ := σ2) (by omega))
    simpa [h2ca, h2m] using h
  have hbase : ∀ σ' : Env, (∀ y ∉ SCP, σ'.vars y = σ2.vars y) → σ'.arrs = σ2.arrs →
      (∀ y ∉ SCP, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
    intro σ' hv ha'
    refine ⟨fun y hy => ?_, ?_⟩
    · have hyc : y ≠ "ca" := fun h => hy (by simp [SCP, SCB, h])
      have hyb : y ≠ "cb" := fun h => hy (by simp [SCP, SCB, h])
      rw [hv y hy]
      simp [hσ2, hσ1, Env.setVar, hyc, hyb]
    · rw [ha']; simp [hσ2, hσ1, Env.setVar]
  by_cases hbn : b < n
  · by_cases ham : a < m
    · have hab : a * n + b < m * n := cell_lt ham hbn
      have hnpos : 1 ≤ n := by omega
      obtain ⟨σ3, r3, o3, v3, a3⟩ := branchOld (B := B) Sz arr n m σ2 a b hs h2A h2ca h2cb h2n ham hbn
        hnB hab (by omega) (fun k hk => hE k (by omega)) (by omega) (by omega)
      have hcell : cellLG arr n m dm t = [arr.getD (2 + 2 * (a * n + b)) 0,
          arr.getD (2 + 2 * (a * n + b) + 1) 0] := by
        unfold cellLG; rw [← ha, ← hb, if_pos hbn, if_pos ham]
      have hv3 : ∀ y ∉ SCP, σ3.vars y = σ2.vars y := fun y hy => v3 y (scb_of_scp hy)
      obtain ⟨hv, ha3⟩ := hbase σ3 hv3 a3
      refine ⟨σ3, (r1.seq (r2.seq (Run.ite_true (by simpa [hbn] using hc1)
        (Run.ite_true (by simpa [ham] using hc2) r3)))).mono ?_, ?_, hv, ha3⟩
      · simp [Cond.size, Expr.size, KcellP]; omega
      · rw [o3, hcell, numBits_pair]
        simp [hσ2, hσ1, Env.setVar]
    · have ham' : m ≤ a := by omega
      obtain ⟨σ3, r3, o3, v3, a3⟩ := newCell_run (B := B) Sz arr n m dm σ2 a b hs h2A h2ca h2cb h2m
        h2n1 h2g h2N2 hbn ham' (by omega) hmB hsum hE hL hlen
      have hcell : cellLG arr n m dm t = [1, if a - m < arr.getD (2 + 2 * (m * n) + b) 0
          then dm + (b + 1) else dm + (n + 1) + (b + 1)] := by
        unfold cellLG; rw [← ha, ← hb, if_pos hbn, if_neg ham]
      obtain ⟨hv, ha3⟩ := hbase σ3 v3 a3
      refine ⟨σ3, (r1.seq (r2.seq (Run.ite_true (by simpa [hbn] using hc1)
        (Run.ite_false (by simpa [ham] using hc2) r3)))).mono ?_, ?_, hv, ha3⟩
      · simp [Cond.size, Expr.size, KcellP]; omega
      · rw [o3, hcell, numBits_pair]
        simp [hσ2, hσ1, Env.setVar]
  · obtain ⟨σ3, r3, o3, v3, a3⟩ := clCell_run (B := B) Sz n dm σ2 hs h2n1 h2g hsum
    have hcell : cellLG arr n m dm t = [n + 1, dm + (n + 1)] := by
      unfold cellLG; rw [← hb, if_neg hbn]
    obtain ⟨hv, ha3⟩ := hbase σ3 v3 a3
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_false (by simpa [hbn] using hc1) r3))).mono ?_, ?_, hv,
      ha3⟩
    · simp [Cond.size, Expr.size, KcellP]; omega
    · rw [o3, hcell, numBits_pair]
      simp [hσ2, hσ1, Env.setVar]


/-- **The loop over the cells.** -/
theorem cellLoopL_run (Sz : ℕ) (arr : List ℕ) (n m dm : ℕ) (σ0 : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ0.arrs "TK" = arr) (hn : σ0.vars "n" = n) (hm : σ0.vars "m" = m)
    (hn2 : σ0.vars "n2" = n + 2) (hn1 : σ0.vars "n1" = n + 1) (hg : σ0.vars "g" = dm)
    (hN2 : σ0.vars "N2" = 2 * (m * n))
    (hM : σ0.vars "M2" = 2 * m * (n + 2)) (hM2 : 2 * m * (n + 2) + 8 < B)
    (hnB : n + 8 < B) (hmB : m + 8 < B) (hsum : dm + 2 * n + 16 < B)
    (hE : ∀ k < 2 + 2 * (m * n) + n, arr.getD k 0 + 8 < B)
    (hL : 2 + 2 * (m * n) + n + 8 < B) (hlen : 2 + 2 * (m * n) + n ≤ arr.length) :
    ∃ σ', Run B (outLoop "M2" cellBodyL) σ0 σ' ((KcellP Sz + 10 + 4) * (2 * m * (n + 2)) + 6) ∧
      σ'.out = σ0.out ++ numBits ((List.range (2 * m * (n + 2))).flatMap (cellLG arr n m dm)) ∧
      (∀ y ∉ "i" :: SCP, σ'.vars y = σ0.vars y) ∧ σ'.arrs = σ0.arrs := by
  obtain ⟨σ', r, o, hAg⟩ := eLoop (B := B) "M2" cellBodyL ("i" :: SCP)
    (fun t => numBits (cellLG arr n m dm t)) (KcellP Sz) (2 * m * (n + 2)) σ0
    (by simp) (by decide) hM (by omega) (by
      intro σ hAg hlt
      have hA' : σ.arrs "TK" = arr := by rw [hAg.1]; exact hA
      have hn' : σ.vars "n" = n := by rw [hAg.2 "n" (by decide)]; exact hn
      have hm' : σ.vars "m" = m := by rw [hAg.2 "m" (by decide)]; exact hm
      have hn2' : σ.vars "n2" = n + 2 := by rw [hAg.2 "n2" (by decide)]; exact hn2
      have hn1' : σ.vars "n1" = n + 1 := by rw [hAg.2 "n1" (by decide)]; exact hn1
      have hg' : σ.vars "g" = dm := by rw [hAg.2 "g" (by decide)]; exact hg
      have hN2' : σ.vars "N2" = 2 * (m * n) := by rw [hAg.2 "N2" (by decide)]; exact hN2
      obtain ⟨σ1, r1, o1, v1, a1⟩ := cellBodyL_run (B := B) Sz arr n m dm σ hs hA' hn' hm' hn2' hn1'
        hg' hN2' hlt hM2 hnB hmB hsum hE hL hlen
      refine ⟨σ1, r1, o1, ⟨a1.trans hAg.1, fun y hy => ?_⟩, ?_⟩
      · have hy' : y ∉ SCP := fun h => hy (List.mem_cons_of_mem _ h)
        rw [v1 y hy', hAg.2 y hy]
      · exact v1 "i" (by decide))
  refine ⟨σ', r, ?_, hAg.2, hAg.1⟩
  rw [o, numBits_flatMap]

/-- Write the whole image. -/
def printL : Com :=
  .seq (emitVar "n2") (.seq (emitVar "m2") (.seq (outLoop "M2" cellBodyL) (emitVar "m")))

/-- The cost of writing the image. -/
def KprintL (Sz M2 : ℕ) : ℕ := 3 * (48 * Sz + 50) + (KcellP Sz + 10 + 4) * M2 + 6

/-- **Writing the image.** -/
theorem printL_run (Sz : ℕ) (arr : List ℕ) (n m dm : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hm : σ.vars "m" = m)
    (hn2 : σ.vars "n2" = n + 2) (hm2 : σ.vars "m2" = 2 * m) (hn1 : σ.vars "n1" = n + 1)
    (hg : σ.vars "g" = dm) (hN2 : σ.vars "N2" = 2 * (m * n))
    (hM : σ.vars "M2" = 2 * m * (n + 2)) (hM2 : 2 * m * (n + 2) + 8 < B)
    (hnB : n + 8 < B) (hmB : m + 8 < B) (hsum : dm + 2 * n + 16 < B)
    (hE : ∀ k < 2 + 2 * (m * n) + n, arr.getD k 0 + 8 < B)
    (hL : 2 + 2 * (m * n) + n + 8 < B) (hlen : 2 + 2 * (m * n) + n ≤ arr.length) :
    ∃ σ', Run B printL σ σ' (KprintL Sz (2 * m * (n + 2))) ∧
      σ'.out = σ.out ++ numBits (outLG arr n m dm) := by
  have h2m : 2 * m ≤ 2 * m * (n + 2) := Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "n2" Sz σ
    ⟨by rw [hn2]; omega, by rw [hn2]; exact hs _ (by omega)⟩
  have z1 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ1.vars y = σ.vars y := v1
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitVar_spec (B := B) "m2" Sz σ1
    ⟨by rw [v1 "m2" (by decide), hm2]; omega,
      by rw [v1 "m2" (by decide), hm2]; exact hs _ (by omega)⟩
  have z2 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ2.vars y = σ.vars y := fun y hy => by
    rw [v2 y hy, v1 y hy]
  have A2 : σ2.arrs "TK" = arr := by rw [a2, a1]; exact hA
  obtain ⟨σ3, r3, o3, v3, a3⟩ := cellLoopL_run (B := B) Sz arr n m dm σ2 hs A2
    (by rw [z2 "n" (by decide)]; exact hn) (by rw [z2 "m" (by decide)]; exact hm)
    (by rw [z2 "n2" (by decide)]; exact hn2) (by rw [z2 "n1" (by decide)]; exact hn1)
    (by rw [z2 "g" (by decide)]; exact hg) (by rw [z2 "N2" (by decide)]; exact hN2)
    (by rw [z2 "M2" (by decide)]; exact hM) hM2 hnB hmB hsum hE hL hlen
  -- the parameter: `m` is not touched by the loop
  have hm3 : σ3.vars "m" = m := by
    rw [v3 "m" (by decide), z2 "m" (by decide)]; exact hm
  obtain ⟨σ4, r4, o4, v4, a4⟩ := emitVar_spec (B := B) "m" Sz σ3
    ⟨by rw [hm3]; omega, by rw [hm3]; exact hs _ (by omega)⟩
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by unfold KprintL; omega), ?_⟩
  rw [o4, o3, o2, o1, hm3, hn2, z1 "m2" (by decide), hm2]
  unfold outLG
  simp only [numBits_append, numBits_cons, numBits_nil, List.append_nil, List.append_assoc]

/-- Write the image of an instance without clients. -/
def print0L : Com := .seq (emitLit 0) (.seq (emitLit 0) (emitLit 0))

theorem print0L_run (Sz : ℕ) (σ : Env) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hB : 6 < B) :
    ∃ σ', Run B print0L σ σ' (3 * (48 * Sz + 50)) ∧ σ'.out = σ.out ++ numBits [0, 0, 0] := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := (emitLit_spec (B := B) 0 Sz (by omega) (hs _ (by omega))) σ trivial
  obtain ⟨σ2, r2, o2, v2, a2⟩ := (emitLit_spec (B := B) 0 Sz (by omega) (hs _ (by omega))) σ1 trivial
  obtain ⟨σ3, r3, o3, v3, a3⟩ := (emitLit_spec (B := B) 0 Sz (by omega) (hs _ (by omega))) σ2 trivial
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), ?_⟩
  rw [o3, o2, o1]
  simp [numBits]

end Lax117284Proofs.Machine.PerProg
