import Lax117284Proofs.Machine.IlpNum
import Lax117284Proofs.Machine.IlpScan
import Lax117284Proofs.Machine.IlpKind
import Lax117284Proofs.Machine.IlpTac

/-!
The classification pass: the kind of every column, and the flags of the types.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients

/-- What one turn of the classification stores in `kd`. -/
def kdVal (σ : Env) : ℕ :=
  if σ.vars "i" < σ.vars "V" then
    (if (σ.arrs "z").getD (2 + σ.vars "i" / σ.vars "Z" * σ.vars "N" + σ.vars "i") 0 = 1 then
      (if (σ.arrs "dg").getD (σ.vars "i") 0 < σ.vars "K" then 3
       else if (σ.arrs "hl").getD (σ.vars "i" / σ.vars "Z") 0 = 0 then 1 else 2)
     else 0)
  else (if (σ.arrs "dg").getD (σ.vars "i") 0 < σ.vars "K" then 3 else 2)

/-- What one turn of the classification does to `hl`. -/
def hlNew (σ : Env) : List ℕ :=
  if σ.vars "i" < σ.vars "V" ∧
      (σ.arrs "z").getD (2 + σ.vars "i" / σ.vars "Z" * σ.vars "N" + σ.vars "i") 0 = 1 ∧
      ¬ (σ.arrs "dg").getD (σ.vars "i") 0 < σ.vars "K" ∧
      (σ.arrs "hl").getD (σ.vars "i" / σ.vars "Z") 0 = 0
  then (σ.arrs "hl").set (σ.vars "i" / σ.vars "Z") 1 else σ.arrs "hl"

theorem Dn_ge_nN (n : ℕ) : nN n ≤ Dn n := by unfold Dn; omega

/-- The numeric facts about a state of the classification pass. -/
theorem kdFacts {n : ℕ} {cnt : ℕ → ℕ} {bb v B : ℕ} (hb : Hyp n cnt bb v B) (d : ℕ → ℕ)
    (hd : ∀ q < Dn n, d q ≤ Kn n) {σ : Env} (hctx : Ctx n cnt bb σ)
    (hdg : σ.arrs "dg" = arrOf (Dn n) d) (hi : σ.vars "i" < nN n) :
    σ.vars "N" = nN n ∧ σ.vars "V" = nV n ∧ σ.vars "Z" = nZ n ∧ σ.vars "K" = Kn n ∧
    (σ.arrs "dg").getD (σ.vars "i") 0 ≤ Kn n ∧
    (σ.arrs "hl").length = nT n ∧ (σ.arrs "kd").length = nN n ∧ (σ.arrs "z").length = zLen n ∧
    (σ.arrs "dg").length = Dn n ∧
    (σ.vars "i" < nV n → σ.vars "i" / σ.vars "Z" < nT n) ∧
    (σ.vars "i" < nV n → 2 + σ.vars "i" / σ.vars "Z" * σ.vars "N" + σ.vars "i" < zLen n) ∧
    (σ.vars "i" < nV n →
      (σ.arrs "z").getD (2 + σ.vars "i" / σ.vars "Z" * σ.vars "N" + σ.vars "i") 0 ≤ 1) := by
  have hNv : σ.vars "N" = nN n := hctx.hN
  have hZv : σ.vars "Z" = nZ n := hctx.hZ
  have hq : σ.vars "i" < nV n → σ.vars "i" / σ.vars "Z" < nT n := by
    intro h
    rw [hZv]
    apply Nat.div_lt_of_lt_mul
    rw [mul_comm]; exact h
  refine ⟨hNv, hctx.hV, hZv, hctx.hK, ?_, hctx.lhl, hctx.lkd, ?_, hctx.ldg, hq, ?_, ?_⟩
  · rw [hdg, getD_arrOf _ (by have := Dn_ge_nN n; omega)]
    exact hd _ (by have := Dn_ge_nN n; omega)
  · rw [hctx.hz]; simp [ilpWord, zLen]
  · intro h
    have h1 := hq h
    rw [hNv]
    have h2 : 2 + σ.vars "i" / σ.vars "Z" * nN n + σ.vars "i" < 2 + nM n * nN n :=
      idx_lt_zLen (by have := h1; unfold nM; omega) hi
    have := rb_le_zLen n
    omega
  · intro h
    have h1 := hq h
    rw [hctx.hz, hNv, hZv] at *
    have h1' : σ.vars "i" / nZ n < nM n := by have := h1; unfold nM; omega
    rw [ilpWord_coef n cnt bb h1' hi]
    exact coef_le_one n _ _

theorem kdBody_vals {n : ℕ} {cnt : ℕ → ℕ} {bb v B : ℕ} (hb : Hyp n cnt bb v B) (d : ℕ → ℕ)
    (hd : ∀ q < Dn n, d q ≤ Kn n) :
    Spec B (fun σ => Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) d ∧ σ.vars "i" < nN n ∧
        ∀ t, (σ.arrs "hl").getD t 0 ≤ 1)
      kdBody
      (fun σ σ' => σ'.vars "i" = σ.vars "i" + 1 ∧
        σ'.arrs "kd" = (σ.arrs "kd").set (σ.vars "i") (kdVal σ) ∧ σ'.arrs "hl" = hlNew σ) 100 := by
  run_vcg
  all_goals
    obtain ⟨hNv, hVv, hZv, hKv, hdgv, hlhl, hlkd, hlz, hldg, hq, hzi, hzv⟩ :=
      kdFacts hb d hd ‹Ctx n cnt bb σ› ‹σ.arrs "dg" = arrOf (Dn n) d› ‹σ.vars "i" < nN n›
    have hlb : ∀ t, (σ.arrs "hl").getD t 0 ≤ 1 := ‹∀ t, (σ.arrs "hl").getD t 0 ≤ 1›
    have hBN := hb.nN_lt
    have hBV := hb.nV_lt
    have hBK := hb.Kn_lt
    have hBz := hb.zLen_lt
    have hBT := hb.nT_lt
    have hBZ := hb.nZ_lt
    have hB5 := hb.five_lt_B
    have hDN := Dn_ge_nN n
    have hlb' := hlb (σ.vars "i" / σ.vars "Z")
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | (unfold kdVal hlNew; split_ifs <;> first | omega | simp) | omega)

end Lax117284Proofs.Machine.Ilp
