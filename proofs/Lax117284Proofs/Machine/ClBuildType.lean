import Lax117284Proofs.Machine.ClBuildDefs

/-!
The type number of one day, and the table of how many days have each type.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The index of the processing time of client `a` on day `ci`. -/
abbrev procIdx (a : String) : Expr := add (add (lit 2) (mul (V "ci") (V "n"))) (V a)
/-- The index of the due date of client `a` on day `ci`. -/
abbrev dueIdx (a : String) : Expr :=
  add (add (add (lit 2) (mul (V "m") (V "n"))) (mul (V "ci") (V "n"))) (V a)

/-- The client indices of position `q`. -/
def phaseA : Com := seqs [asg "qa" (dv (V "q") (V "n")), asg "qb" (sub (V "q") (mul (V "qa") (V "n")))]

/-- The processing times and due dates of the two clients. -/
def phaseB : Com := seqs [
  asg "da" (.get "X" (dueIdx "qa")), asg "pa" (.get "X" (procIdx "qa")),
  asg "db" (.get "X" (dueIdx "qb")), asg "pb" (.get "X" (procIdx "qb"))]

/-- Whether they conflict, and the bit added. -/
def phaseC : Com := seqs [
  asg "fl" (mul (ltFl (sub (V "da") (V "pa")) (V "db")) (ltFl (sub (V "db") (V "pb")) (V "da"))),
  asg "tt" (add (V "tt") (mul (V "fl") (pow2 (V "q")))),
  asg "q" (add (V "q") (lit 1))]

/-- One position `q = a * n + b` of the type of day `ci`: add its bit. -/
def typeBody : Com := .seq phaseA (.seq phaseB phaseC)

/-- The number of the type of day `ci`, in `tt`. -/
def typeLoop : Com := seqs [asg "tt" (lit 0), asg "q" (lit 0), .while (.lt (V "q") (V "nn")) typeBody]

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The bit function of day `i`'s type. -/
def fconf (I : Instance) (i : ℕ) : ℕ → Bool :=
  fun q => confB I i (q / I.clients) (q % I.clients)

/-- The invariant of the type loop. -/
def TInv (I : Instance) (x : List ℕ) (k i : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ci" = i ∧ σ.vars "q" ≤ I.clients * I.clients ∧
    σ.vars "tt" = bitsNum (fconf I i) (σ.vars "q")

theorem flag_lt (e f : ℕ) : min (f - e) 1 = if e < f then 1 else 0 := by
  split_ifs with h <;> omega

open Lax117284Proofs.Machine.ClSim (AgreeOff)

theorem Ctx0.agree {L : List String} {σ σ' : Env} (h : Ctx0 I x k σ) (hA : AgreeOff L σ σ')
    (h1 : "n" ∉ L) (h2 : "m" ∉ L) (h3 : "k" ∉ L) : Ctx0 I x k σ' :=
  ⟨by rw [hA.1]; exact h.X, by rw [hA.2.2.2 _ h1]; exact h.n, by rw [hA.2.2.2 _ h2]; exact h.m,
    by rw [hA.2.2.2 _ h3]; exact h.k⟩

theorem Sizes.agree {L : List String} {σ σ' : Env} (h : Sizes I σ) (hA : AgreeOff L σ σ')
    (h1 : "nn" ∉ L) (h2 : "T" ∉ L) (h3 : "Z" ∉ L) (h4 : "Vv" ∉ L) (h5 : "N" ∉ L) (h6 : "M" ∉ L)
    (h7 : "zl" ∉ L) : Sizes I σ' :=
  ⟨by rw [hA.2.2.2 _ h1]; exact h.nn, by rw [hA.2.2.2 _ h2]; exact h.T,
    by rw [hA.2.2.2 _ h3]; exact h.Z, by rw [hA.2.2.2 _ h4]; exact h.Vv,
    by rw [hA.2.2.2 _ h5]; exact h.N, by rw [hA.2.2.2 _ h6]; exact h.M,
    by rw [hA.2.2.2 _ h7]; exact h.zl⟩

theorem phaseA_spec (h : Bh I x k B) (hn : 0 < I.clients) :
    Spec B (fun σ => Ctx0 I x k σ ∧ σ.vars "q" < I.clients * I.clients ∧ σ.vars "q" < B) phaseA
      (fun σ σ' => AgreeOff ["qa", "qb"] σ σ' ∧ σ'.vars "qa" = σ.vars "q" / I.clients ∧
        σ'.vars "qb" = σ.vars "q" % I.clients) 50 := by
  have hL := h.hL
  have hnB : I.clients < B := by
    have := h.hzB; have := n_le_nZ I.clients; have := (sizes_le_zLen I.clients).2.2.2.2.2.2.1
    have := zLen_le I.clients; have := (sizes_le_zLen I.clients).2.1
    omega
  run_vcg
  all_goals
    obtain ⟨hX, hnv, hm, hk⟩ := ‹Ctx0 I x k _›
  all_goals try
    refine ⟨⟨rfl, rfl, rfl, fun y hy => ?_⟩, ?_, ?_⟩
  all_goals try
    (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
     simp [Env.setVar, hy.1, hy.2])
  all_goals try simp [Env.setVar, hnv]
  all_goals try (rw [Nat.mod_def]; simp [Nat.mul_comm])
  all_goals try omega
  all_goals first
    | (exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
    | (exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) (by omega))

/-- The times of the two clients. -/
theorem phaseB_spec (h : Bh I x k B) (i : ℕ) (hi : i < I.days) :
    Spec B (fun σ => Ctx0 I x k σ ∧ σ.vars "ci" = i ∧ σ.vars "qa" < I.clients ∧
        σ.vars "qb" < I.clients) phaseB
      (fun σ σ' => AgreeOff ["da", "pa", "db", "pb"] σ σ' ∧ σ'.vars "da" = I.dAt i (σ.vars "qa") ∧
        σ'.vars "pa" = I.pAt i (σ.vars "qa") ∧ σ'.vars "db" = I.dAt i (σ.vars "qb") ∧
        σ'.vars "pb" = I.pAt i (σ.vars "qb")) 100 := by
  have hlen := ClientsWord.len_eq h.enc
  have hin : i * I.clients + I.clients ≤ I.days * I.clients := by
    have := Nat.mul_le_mul_right I.clients (Nat.succ_le_of_lt hi); nlinarith
  have hproc : ∀ a, a < I.clients → x.getD (2 + i * I.clients + a) 0 = I.pAt i a :=
    fun a ha => ClientsWord.proc_eq h.enc hi ha
  have hdue : ∀ a, a < I.clients → x.getD (2 + I.days * I.clients + i * I.clients + a) 0 = I.dAt i a :=
    fun a ha => ClientsWord.due_eq h.enc hi ha
  have hgB : ∀ j, x.getD j 0 < B := by
    intro j
    by_cases hj : j < x.length
    · rw [List.getD_eq_getElem _ _ hj]; exact h.hX _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (by omega)]; have := h.hL; omega
  have hL := h.hL
  have hmB := h.m_lt
  have hnB := h.n_lt
  have hlen' := h.mn_le
  have hproc' : ∀ a, a < I.clients → x[2 + i * I.clients + a]?.getD 0 = I.pAt i a := fun a ha => by
    simpa [List.getD_eq_getElem?_getD] using hproc a ha
  have hdue' : ∀ a, a < I.clients → x[2 + I.days * I.clients + i * I.clients + a]?.getD 0 =
      I.dAt i a := fun a ha => by simpa [List.getD_eq_getElem?_getD] using hdue a ha
  have hgB' : ∀ j, (x[j]?.getD 0) < B := fun j => by
    simpa [List.getD_eq_getElem?_getD] using hgB j
  have hdB : ∀ a, a < I.clients → I.dAt i a < B := fun a ha => by
    rw [← hdue' a ha]; exact hgB' _
  have hpB : ∀ a, a < I.clients → I.pAt i a < B := fun a ha => by
    rw [← hproc' a ha]; exact hgB' _
  run_vcg
  all_goals
    obtain ⟨hX, hnv, hm, hk⟩ := ‹Ctx0 I x k _›
    have hci : σ.vars "ci" = i := ‹_›
    have hqa : σ.vars "qa" < I.clients := ‹_›
    have hqb : σ.vars "qb" < I.clients := ‹_›
  all_goals try
    refine ⟨⟨rfl, rfl, rfl, fun y hy => ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals try
    (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
     simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2])
  all_goals try simp [Env.setVar, hX, hnv, hm, hci, hproc', hdue', hgB', hgB, hqa, hqb, hdB, hpB]
  all_goals try omega

theorem cap_one (a : ℕ) : a - (a - 1) = min a 1 := by omega

theorem conf_flag (da pa db pb : ℕ) :
    min (db - (da - pa)) 1 * min (da - (db - pb)) 1 =
      if da - pa < db ∧ db - pb < da then 1 else 0 := by
  rw [flag_lt, flag_lt]
  split_ifs <;> simp_all

theorem bitsNum_succ_conf (I : Instance) (i q : ℕ) :
    bitsNum (fconf I i) (q + 1) =
      bitsNum (fconf I i) q + if I.ConflictAt i (q / I.clients) (q % I.clients) then 2 ^ q else 0 := by
  simp only [bitsNum, fconf, confB, decide_eq_true_eq]

theorem pow_lt_nT {q n : ℕ} (hq : q < n * n) : 2 ^ q < nT n := by
  rw [nT]; exact Nat.pow_lt_pow_right (by norm_num) hq

theorem bitsNum_step_lt (f : ℕ → Bool) {q n : ℕ} (hq : q < n * n) (b : ℕ) (hb : b ≤ 1) :
    bitsNum f q + b * 2 ^ q < nT n := by
  have h1 := bitsNum_lt f q
  have h2 : 2 ^ (q + 1) ≤ nT n := by
    rw [nT]; exact Nat.pow_le_pow_right (by norm_num) hq
  rw [pow_succ] at h2
  have : b * 2 ^ q ≤ 2 ^ q := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> simp
  omega

/-- The precondition of the last phase. -/
def PC (I : Instance) (x : List ℕ) (k i B : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "q" < I.clients * I.clients ∧
    σ.vars "tt" = bitsNum (fconf I i) (σ.vars "q") ∧
    σ.vars "da" = I.dAt i (σ.vars "q" / I.clients) ∧
    σ.vars "pa" = I.pAt i (σ.vars "q" / I.clients) ∧
    σ.vars "db" = I.dAt i (σ.vars "q" % I.clients) ∧
    σ.vars "pb" = I.pAt i (σ.vars "q" % I.clients) ∧
    σ.vars "da" < B ∧ σ.vars "pa" < B ∧ σ.vars "db" < B ∧ σ.vars "pb" < B

set_option maxHeartbeats 1600000 in
theorem phaseC_spec (h : Bh I x k B) (i : ℕ) :
    Spec B (PC I x k i B) phaseC
      (fun σ σ' => AgreeOff ["fl", "tt", "q"] σ σ' ∧ σ'.vars "q" = σ.vars "q" + 1 ∧
        σ'.vars "tt" = bitsNum (fconf I i) (σ.vars "q" + 1)) 50 := by
  have hL := h.hL
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hgB := h.getD_lt
  unfold PC
  run_vcg
  all_goals
    obtain ⟨hX, hnv, hm, hk⟩ := ‹Ctx0 I x k _›
    obtain ⟨hnn, hT, hZ, hVv, hN, hM, hzl⟩ := ‹Sizes I _›
  all_goals
    have hq : σ.vars "q" < I.clients * I.clients := ‹_›
    have htt : σ.vars "tt" = bitsNum (fconf I i) (σ.vars "q") := ‹_›
    have hda : σ.vars "da" = I.dAt i (σ.vars "q" / I.clients) := ‹_›
    have hpa : σ.vars "pa" = I.pAt i (σ.vars "q" / I.clients) := ‹_›
    have hdb : σ.vars "db" = I.dAt i (σ.vars "q" % I.clients) := ‹_›
    have hpb : σ.vars "pb" = I.pAt i (σ.vars "q" % I.clients) := ‹_›
    have hdaB : σ.vars "da" < B := ‹_›
    have hpaB : σ.vars "pa" < B := ‹_›
    have hdbB : σ.vars "db" < B := ‹_›
    have hpbB : σ.vars "pb" < B := ‹_›
    have hbn : bitsNum (fconf I i) (σ.vars "q") < 2 ^ σ.vars "q" := bitsNum_lt _ _
    have hTq := pow_lt_nT hq
    have hstep := bitsNum_step_lt (fconf I i) hq
    have hs1 := hstep 1 (le_refl 1)
    have hs0 := hstep 0 (Nat.zero_le _)
    have hnT : nT I.clients < B := lt_of_le_of_lt h1 hz
  all_goals try
    refine ⟨⟨rfl, rfl, rfl, fun y hy => ?_⟩, ?_, ?_⟩
  all_goals try
    (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
     simp [Env.setVar, hy.1, hy.2.1, hy.2.2])
  all_goals try simp [Env.setVar, hnv, htt, hda, hpa, hdb, hpb, cap_one, conf_flag, bitsNum_succ_conf,
    Instance.ConflictAt]
  all_goals try (split_ifs <;> first | omega | simp_all)
  all_goals try omega
  all_goals try (exact lt_of_le_of_lt (Nat.sub_le _ _) (by omega))

end Lax117284Proofs.Machine.ClBuild
