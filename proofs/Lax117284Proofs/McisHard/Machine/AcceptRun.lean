import Lax117284Proofs.McisHard.Machine.PrintMain
import Lax117284Proofs.McisHard.Machine.AcceptPrefix
import Lax117284Proofs.Machine.SatAccept
import Lax117284Proofs.Machine.SatCong

/-!
# The accepting phase of the reduction to `H` (WP8)

`accMcis`: read the counts, check the positions, and write the image `H` if the check passes (and nothing
otherwise).  The output is `natBits (encodeInstance (Hfin ns))` when `CondN ns` and empty otherwise.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Acc

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.SatOps Lax117284Proofs.Machine.SatSem
open Lax117284Proofs.Machine.SatRank Lax117284Proofs.Machine.SatCheck Lax117284Proofs.Machine.SatAccept
open Lax117284Proofs.Machine.SatCong Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.SatFormat (SlotsN ShapeF)
open Lax117284Proofs.McisHard Lax117284Proofs.McisHard.Print Lax117284Proofs.McisHard.Bit

variable {B : ℕ}

/-- The size of `H` is at most `400 (N + 1)²`. -/
theorem V_le (ns : List ℕ) : kOf ns * nOf ns ≤ 400 * (SlotsN ns + 1) ^ 2 := by
  unfold kOf nOf
  by_cases h : SlotsN ns = 0
  · rw [if_pos h, if_pos h, h]; norm_num
  · rw [if_neg h, if_neg h]
    have h1 : ns.getD 1 0 + ns.getD 2 0 ≤ SlotsN ns := by unfold SlotsN; omega
    have h2 : (ns.getD 1 0 + ns.getD 2 0 + 10 * SlotsN ns) * (SlotsN ns * 36) ≤
        (11 * SlotsN ns) * (SlotsN ns * 36) := Nat.mul_le_mul (by omega) le_rfl
    nlinarith [Nat.zero_le (SlotsN ns)]

/-- The phase after the tokenizer. -/
def accMcis : Com :=
  .seq prepSat (.seq chkLoop (.ite (.eq (V "ok") (.lit 1)) printCom .skip))

/-- The cost of the phase, on an input of `l` tokens. -/
def KaccM (Sz l : ℕ) : ℕ :=
  200 + ((120 + 64 * l + 4) * l + 6) + KprintM Sz l (400 * (l + 1) ^ 2)

lemma KprintM_mono (Sz N N' V V' : ℕ) (hN : N ≤ N') (hV : V ≤ V') :
    KprintM Sz N V ≤ KprintM Sz N' V' := by
  unfold KprintM Kbit
  have h1 : (128 * N + 1500 + 2 + 10 + 4) * V ≤ (128 * N' + 1500 + 2 + 10 + 4) * V' :=
    Nat.mul_le_mul (by omega) hV
  have h2 : ((128 * N + 1500 + 2 + 10 + 4) * V + 6 + 10 + 4) * V ≤
      ((128 * N' + 1500 + 2 + 10 + 4) * V' + 6 + 10 + 4) * V' :=
    Nat.mul_le_mul (by omega) hV
  omega

lemma KaccM_mono (Sz a b : ℕ) (h : a ≤ b) : KaccM Sz a ≤ KaccM Sz b := by
  unfold KaccM
  have h1 : (120 + 64 * a + 4) * a ≤ (120 + 64 * b + 4) * b := Nat.mul_le_mul (by omega) h
  have h2 := KprintM_mono Sz a b (400 * (a + 1) ^ 2) (400 * (b + 1) ^ 2) h
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  omega

theorem printCom_warrs : printCom.warrs = [] := by
  simp [printCom, hdrCom, matCom, rowCom, rowBody, Print.bitCom_warrs, Lax117284Proofs.Machine.Out.emitVar,
    Lax117284Proofs.Machine.FoldLoop.fLoop, Com.warrs, Lax117284Proofs.Machine.EmitNat.emitNat,
    Lax117284Proofs.Machine.EmitNat.sizeLoop, Lax117284Proofs.Machine.EmitNat.sizeBody,
    Lax117284Proofs.Machine.EmitNat.onesLoop, Lax117284Proofs.Machine.EmitNat.onesBody,
    Lax117284Proofs.Machine.EmitNat.digLoop, Lax117284Proofs.Machine.EmitNat.digBody]

lemma getD_of_take {arr ns : List ℕ} (h : arr.take ns.length = ns) :
    ∀ k < ns.length, arr.getD k 0 = ns.getD k 0 := fun k hk => by
  conv_rhs => rw [← h]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]

open Classical in
set_option maxHeartbeats 3200000 in
/-- **The accepting phase.** `ns` is the stream of the formula, a prefix of the token array `arr`. -/
theorem accMcis_run (Sz l : ℕ) (arr ns : List ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hA : σ.arrs "TK" = arr) (hsh : ShapeF ns)
    (hpre : arr.take ns.length = ns)
    (hE : ∀ k < 3 + 2 * SlotsN ns, ns.getD k 0 + 8 < B) (hl : SlotsN ns ≤ l)
    (hB : 60 * (SlotsN ns + 4) < B)
    (hb : 4 * ns.getD 0 0 + 8 * (ns.getD 1 0 + ns.getD 2 0) + 64 < B)
    (hVl : 400 * (SlotsN ns + 1) ^ 2 + 8 < B) :
    ∃ σ', Run B accMcis σ σ' (KaccM Sz l) ∧
      σ'.out = σ.out ++ (if CondN ns then
        natBits (Lax117284.MulticolouredIndepSet.encodeInstance (Hfin ns)) else []) := by
  obtain ⟨S, hSdef⟩ : ∃ S, SlotsN ns = S := ⟨_, rfl⟩
  have hlenns : ns.length = 3 + 2 * S := by rw [hsh.2.1, hSdef]
  have hAg : Agree arr ns S := fun k hk => getD_of_take hpre k (by omega)
  have hSa : SlotsN arr = S := hAg.slots.trans hSdef
  have hlenA : 3 + 2 * S ≤ arr.length := by
    have := congrArg List.length hpre
    rw [List.length_take] at this
    omega
  rw [hSdef] at hE hl hB hVl
  have hB2 : 6 < B := by omega
  have hEa : ∀ k < 3 + 2 * S, arr.getD k 0 + 8 < B := fun k hk => by rw [hAg k hk]; exact hE k hk
  have hba : 4 * arr.getD 0 0 + 8 * (arr.getD 1 0 + arr.getD 2 0) + 64 < B := by
    rw [hAg.n, hAg.na, hAg.nb]; exact hb
  obtain ⟨σ1, r1, e1n, e1N, e1V3, e1A2, e1K7, e1K9, e1C, e1ok, e1a, e1o, e1f⟩ :=
    prepSat_run (B := B) arr σ hA (by omega) (fun k hk => hEa k (by omega)) hba
  rw [hSa] at e1N e1C e1ok
  have A1 : σ1.arrs "TK" = arr := by rw [e1a]; exact hA
  have hok0 : (if S < arr.getD 0 0 then 0 else 1) ≤ 1 := by split <;> omega
  have hEv : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B := fun k hk => hEa _ (by omega)
  have hEs : ∀ k < S, arr.getD (4 + 2 * k) 0 + 8 < B := fun k hk => hEa _ (by omega)
  obtain ⟨σ2, r2, e2ok, e2a, e2o, e2f⟩ := chkLoop_spec (B := B) arr S (arr.getD 0 0)
    (if S < arr.getD 0 0 then 0 else 1) σ1 rfl hEv hEs hlenA (by omega)
    (hEa 0 (by omega)) hok0 A1 e1N e1n e1ok
  have A2 : σ2.arrs "TK" = arr := by rw [e2a]; exact A1
  have hcondA : σ2.vars "ok" = 1 ↔ CondN arr := by
    rw [e2ok, flagTo_eq_one]
    unfold CondN
    rw [hSa]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra h
      have : S < arr.getD 0 0 := by omega
      rw [if_pos this] at h1
      exact absurd h1 (by decide)
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [if_neg (by omega)], h2⟩
  have hcond : σ2.vars "ok" = 1 ↔ CondN ns := hcondA.trans (hAg.cond hSdef)
  have hokB : σ2.vars "ok" < B := by
    rw [e2ok]; have := flagTo_le (PassS arr) (if S < arr.getD 0 0 then 0 else 1) S; omega
  by_cases hok : σ2.vars "ok" = 1
  · have hc := hcond.1 hok
    have hcondT : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some true := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    have hcc : CondN ns := hc
    -- the state on which `printCom` runs: the token array is exactly the stream
    let σn : Env := { σ2 with arrs := fun a => if a = "TK" then ns else σ2.arrs a }
    have hctx : Ctx[ns, σn] := by
      refine ⟨by simp [σn], ?_, ?_⟩
      · show σ2.vars "N" = SlotsN ns
        rw [e2f "N" (by decide), e1N, hSdef]
      · show σ2.vars "A2" = 2 * ns.getD 1 0
        rw [e2f "A2" (by decide), e1A2, hAg.na]
    have hV : kOf ns * nOf ns + 8 < B := by
      have := V_le ns
      rw [hSdef] at this
      omega
    obtain ⟨σ3, r3, o3⟩ := printCom_run (B := B) Sz ns hsh hc (by rw [hSdef]; exact hB)
      (by rw [hSdef]; exact hE) hV hs σn hctx
    obtain ⟨σ4, r4, v4, o4, i4, a4⟩ := Prefix.run_prefix printCom_warrs r3 σ2 rfl rfl rfl (fun a => by
      by_cases h : a = "TK"
      · subst h; simp only [σn, if_true]; rw [A2]; exact hpre ▸ List.take_prefix _ _
      · simp [σn, h])
    have hK := KprintM_mono Sz (SlotsN ns) l (kOf ns * nOf ns) (400 * (l + 1) ^ 2)
      (by rw [hSdef]; exact hl) (le_trans (V_le ns) (by
        rw [hSdef]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)))
    refine ⟨σ4, (r1.seq (r2.seq (Run.ite_true hcondT r4))).mono ?_, ?_⟩
    · unfold KaccM
      have h1 : (120 + 64 * S + 4) * S ≤ (120 + 64 * l + 4) * l := Nat.mul_le_mul (by omega) hl
      simp only [Cond.size, Expr.size]
      omega
    · rw [o4, o3, show σn.out = σ2.out from rfl, e2o, e1o, if_pos hcc]
  · have hno : ¬ CondN ns := fun h => hok (hcond.2 h)
    have hcondF : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some false := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    refine ⟨σ2, (r1.seq (r2.seq (Run.ite_false hcondF Run.skip))).mono ?_, ?_⟩
    · unfold KaccM
      have h1 : (120 + 64 * S + 4) * S ≤ (120 + 64 * l + 4) * l := Nat.mul_le_mul (by omega) hl
      simp only [Cond.size, Expr.size]
      omega
    · rw [e2o, e1o, if_neg hno]; simp

end Lax117284Proofs.McisHard.Acc
