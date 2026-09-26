import Lax117284Proofs.Machine.ClBruteOdo

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
