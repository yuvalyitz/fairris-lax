import Lax117284Proofs.Machine.TwJoin1

/-!
The program of a join node: the size, the table, and the whole program.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- Store the size, and set the parameters of the fill of the table. -/
def joinMid : Com := seqs
  [ .store "SZ" (V "i") (V "s1"),
    .assign "cbase" (mul (V "c") (V "Tm")),
    .assign "ob" (mul (V "ot") (V "Tm")),
    .assign "bs" (mul (V "i") (V "Tm")),
    .assign "fn" (.bin .shiftl (L 1) (mul (V "m") (V "s1"))) ]

/-- The state after `joinMid`. -/
def midStateJ (P : Params) (i0 : ℕ) (σ : Env) : Env :=
  (((σ.setArr "SZ" (i0 + 1) (bagL P.D i0).length).setVar "cbase" (i0 * P.tabs)).setVar "ob"
    (other P.D (i0 + 1) * P.tabs)).setVar "bs" ((i0 + 1) * P.tabs) |>.setVar "fn"
    (2 ^ (P.m * (bagL P.D i0).length))

theorem joinMid_run {i0 : ℕ} (h : HQj P B i0 σ) :
    ∃ σ', Run B joinMid σ σ' 100 ∧ σ' = midStateJ P i0 σ := by
  have hC := h.C
  have hiN := h.iN
  have hjf := join_facts P h.iN h.k_
  have hle0 := bagL_len_le P (j := i0) (by omega)
  have hb1 := hC.b1
  have hb9 := hC.b9
  have hb3 := hC.b3
  have hb2 := hC.b2
  have hlenSZ := hC.lenSZ
  have hNt : (i0 + 2) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ h.iN
  have hi2 : (i0 + 2) * P.tabs = i0 * P.tabs + P.tabs + P.tabs := by ring
  have hi1 : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
  have hp2 : 2 ^ (P.m * (bagL P.D i0).length) ≤ P.tabs := pow_le_tabs P hle0
  have hms1 : P.m * (bagL P.D i0).length ≤ P.m * P.wid := Nat.mul_le_mul_left _ hle0
  have hmw : P.m * (P.wid + 1) = P.m * P.wid + P.m := by ring
  have hct : i0 * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ (by omega)
  have hot : other P.D (i0 + 1) * P.tabs ≤ i0 * P.tabs := Nat.mul_le_mul_right _ (by omega)
  unfold joinMid seqs
  run_vcg
  all_goals (try nrmA)
  all_goals try (first | omega | (simp only [h.i_, h.s1_, hC.m_, hC.Tm_, h.c_, h.ot_, one_mul]; omega))
  all_goals (try simp only [midStateJ, h.i_, h.s1_, hC.m_, hC.Tm_, h.c_, h.ot_, one_mul])

/-- The cell of the table of a join node: the product of the entries of the two children. -/
def joinCell : Com :=
  .assign "val" (mul (G "TB" (add (V "cbase") (V "fc"))) (G "TB" (add (V "ob") (V "fc"))))

/-- **The context of a cell of the table of a join node.** -/
structure TCj (P : Params) (B : ℕ) (i0 : ℕ) (σ : Env) : Prop where
  C : NC P B σ
  iN : i0 + 1 < P.N
  k_ : kind P.D (i0 + 1) = 3
  tb : ∀ e < (2 ^ P.m) ^ (bagL P.D i0).length,
    (σ.arrs "TB").getD (i0 * P.tabs + e) 0 = tbv P.I P.kk P.D i0 e
  tbo : ∀ e < (2 ^ P.m) ^ (bagL P.D i0).length,
    (σ.arrs "TB").getD (other P.D (i0 + 1) * P.tabs + e) 0 =
      tbv P.I P.kk P.D (other P.D (i0 + 1)) e
  cbase_ : σ.vars "cbase" = i0 * P.tabs
  ob_ : σ.vars "ob" = other P.D (i0 + 1) * P.tabs

theorem joinCell_run {i0 : ℕ} (hT : TCj P B i0 σ)
    (hfc : σ.vars "fc" < 2 ^ (P.m * (bagL P.D i0).length)) :
    ∃ σ', Run B joinCell σ σ' 30 ∧
      σ'.vars "val" = tbv P.I P.kk P.D (i0 + 1) (σ.vars "fc") ∧ σ'.arrs = σ.arrs ∧
      (∀ y, y ≠ "val" → σ'.vars y = σ.vars y) ∧ σ'.out = σ.out := by
  have hC := hT.C
  have hiN := hT.iN
  have hjf := join_facts P hiN hT.k_
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  have hb1 := hC.b1
  have hlenTB := hC.lenTB
  have hfc' : σ.vars "fc" < (2 ^ P.m) ^ (bagL P.D i0).length := by rw [bpow']; exact hfc
  have hpt : 2 ^ (P.m * (bagL P.D i0).length) ≤ P.tabs := pow_le_tabs P hlen0
  have hNt : (i0 + 1) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ (by omega)
  have hi1 : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
  have hoi : (other P.D (i0 + 1) + 1) * P.tabs ≤ i0 * P.tabs := Nat.mul_le_mul_right _ (by omega)
  have hoi1 : (other P.D (i0 + 1) + 1) * P.tabs = other P.D (i0 + 1) * P.tabs + P.tabs := by ring
  have hv1 := hT.tb _ hfc'
  have hv2 := hT.tbo _ hfc'
  have hle1 := tbv_le_one (I := P.I) (kk := P.kk) (D := P.D) (j := i0) (e := σ.vars "fc")
  have hle2 := tbv_le_one (I := P.I) (kk := P.kk) (D := P.D) (j := other P.D (i0 + 1))
    (e := σ.vars "fc")
  have hprod : tbv P.I P.kk P.D i0 (σ.vars "fc") *
      tbv P.I P.kk P.D (other P.D (i0 + 1)) (σ.vars "fc") ≤ 1 :=
    calc _ ≤ 1 * 1 := Nat.mul_le_mul hle1 hle2
      _ = 1 := rfl
  unfold joinCell
  run_vcg
  all_goals first
    | (refine ⟨?_, rfl, fun y hy => by simp [Env.setVar, hy], rfl⟩
       nrmA
       rw [hT.cbase_, hT.ob_, hv1, hv2, tbv_join hT.k_ (by omega)])
    | (simp only [hT.cbase_, hT.ob_, hv1, hv2]; omega)
    | omega

end Lax117284Proofs.Machine.TwNode
