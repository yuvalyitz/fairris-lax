import Lax117284Proofs.Machine.TwForget3

/-!
The cell of the table of a forget node, continued: the preparation and the whole cell.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- The preparation of a cell of a forget node: the low part, the high part, the accumulator. -/
def forgetPre : Com := seqs
  [ .assign "e" (V "fc"),
    .assign "lo" (.bin .and (V "e") (sub (V "Pp") (L 1))),
    .assign "hi" (mul (.bin .shiftr (V "e") (V "shp1")) (mul (V "Pp") (V "bb"))),
    .assign "ac" (L 0) ]

theorem forgetPre_run (σ : Env) (m p fc : ℕ) (hPp : σ.vars "Pp" = 2 ^ (m * p))
    (hsh : σ.vars "shp1" = m * p) (hfc : σ.vars "fc" = fc) (hbb : σ.vars "bb" = 2 ^ m)
    (hfcB : fc < B) (hPpB : 2 ^ (m * p) < B) (hshB : m * p < B)
    (hPq : 2 ^ (m * p) * 2 ^ m < B) (hhiB : fc / 2 ^ (m * p) * (2 ^ (m * p) * 2 ^ m) < B)
    (hmB : 2 ^ m < B) (h0 : 2 < B) :
    ∃ σ1, Run B forgetPre σ σ1 60 ∧ σ1 =
      (((σ.setVar "e" fc).setVar "lo" (Nat.land fc (2 ^ (m * p) - 1))).setVar "hi"
        (fc / 2 ^ (m * p) * (2 ^ (m * p) * 2 ^ m))).setVar "ac" 0 := by
  have hlo : Nat.land fc (2 ^ (m * p) - 1) < B := lt_of_le_of_lt Nat.and_le_left hfcB
  have hhi : fc / 2 ^ (m * p) < B := lt_of_le_of_lt (Nat.div_le_self _ _) hfcB
  unfold forgetPre seqs
  run_vcg
  all_goals (try nrmA)
  all_goals try (first | omega | (simp only [hPp, hsh, hfc, hbb]; first | omega | exact hlo | exact hhi | exact lt_of_le_of_lt (by omega) hPpB))
  all_goals (try simp only [hPp, hsh, hfc, hbb])

/-- The cell of the table of a forget node. -/
def forgetCell : Com := .seq forgetPre (.seq forgetOr (.assign "val" (V "ac")))

/-- The scalars a forget cell writes. -/
def SF : List String := ["e", "lo", "hi", "ac", "so", "ix", "val"]

lemma SF_sub : ∀ y ∈ "fc" :: SF, y ∈ SN := by
  intro y hy
  simp only [SF, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [SN]

/-- **The context of a cell of the table of a forget node.** -/
structure TCf (P : Params) (B : ℕ) (i0 : ℕ) (σ : Env) : Prop where
  C : NC P B σ
  iN : i0 + 1 < P.N
  k_ : kind P.D (i0 + 1) = 2
  tb : ∀ e < (2 ^ P.m) ^ (bagL P.D i0).length,
    (σ.arrs "TB").getD (i0 * P.tabs + e) 0 = tbv P.I P.kk P.D i0 e
  Pp_ : σ.vars "Pp" = 2 ^ (P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1)))
  shp1_ : σ.vars "shp1" = P.m * pos (bagL P.D i0) (vertex P.D (i0 + 1))
  cbase_ : σ.vars "cbase" = i0 * P.tabs

/-- The number the table of the child is asked at, in the shape the machine computes it. -/
lemma insAt_eq (m p j e : ℕ) :
    Nat.land e (2 ^ (m * p) - 1) + j * 2 ^ (m * p) + e / 2 ^ (m * p) * (2 ^ (m * p) * 2 ^ m) =
      insN (2 ^ m) p j e := by
  have h : 2 ^ (m * p) * 2 ^ m = 2 ^ (m * (p + 1)) := by rw [← pow_add, Nat.mul_succ]
  rw [insN_shift, h]

theorem forgetCell_run {i0 : ℕ} (hT : TCf P B i0 σ)
    (hfc : σ.vars "fc" < 2 ^ (P.m * ((bagL P.D i0).length - 1))) :
    ∃ σ', Run B forgetCell σ σ' (44 * 2 ^ P.m + 130) ∧
      σ'.vars "val" = tbv P.I P.kk P.D (i0 + 1) (σ.vars "fc") ∧ σ'.arrs = σ.arrs ∧
      (∀ y, y ∉ SF → σ'.vars y = σ.vars y) ∧ σ'.out = σ.out := by
  have hC := hT.C
  have hiN := hT.iN
  have hpl := bagL_forget_facts P hiN hT.k_
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  have hb1 := hC.b1
  have hb9 := hC.b9
  have hb10 := hC.b10
  have hlenTB := hC.lenTB
  set p := pos (bagL P.D i0) (vertex P.D (i0 + 1)) with hpdef
  set len0 := (bagL P.D i0).length with hlen0def
  have hfc' : σ.vars "fc" < (2 ^ P.m) ^ (len0 - 1) := by rw [bpow']; exact hfc
  have hptab : 2 ^ (P.m * len0) ≤ P.tabs := pow_le_tabs P hlen0
  have hpow1 : (2 ^ P.m) ^ len0 ≤ P.tabs := by rw [bpow']; exact hptab
  have hpow2 : (2 ^ P.m) ^ (len0 - 1) ≤ P.tabs := by
    rw [bpow']; exact pow_le_tabs P (by omega)
  have hct : i0 * P.tabs + P.tabs ≤ P.N * P.tabs := by
    have : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
    have := Nat.mul_le_mul_right P.tabs (show i0 + 1 ≤ P.N by omega)
    omega
  -- the numbers the child's table is asked at
  have hins : ∀ j < 2 ^ P.m, insN (2 ^ P.m) p j (σ.vars "fc") < (2 ^ P.m) ^ len0 := by
    intro j hj
    have := insN_lt (b := 2 ^ P.m) (by positivity) (s := len0 - 1) (p := p) (S := j)
      (e := σ.vars "fc") hfc' hj (by omega)
    rwa [Nat.sub_add_cancel (by omega)] at this
  have hPq : 2 ^ (P.m * p) * 2 ^ P.m ≤ P.tabs := by
    rw [← pow_add, ← Nat.mul_succ]; exact pow_le_tabs P (by omega)
  have hPp' : 2 ^ (P.m * p) ≤ P.tabs := pow_le_tabs P (by omega)
  have hmp : P.m * p ≤ P.m * P.wid := Nat.mul_le_mul_left _ (by omega)
  have hmw : P.m * (P.wid + 1) = P.m * P.wid + P.m := by ring
  have hfcB : σ.vars "fc" < B := by omega
  have hins0 := hins 0 (by positivity)
  have hins0' := insAt_eq P.m p 0 (σ.vars "fc")
  have hBpos : 0 < B := by omega
  obtain ⟨σ1, r1, e1⟩ := forgetPre_run (B := B) σ P.m p (σ.vars "fc") hT.Pp_ hT.shp1_ rfl hC.bb_
    hfcB (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hlo1 : σ1.vars "lo" = Nat.land (σ.vars "fc") (2 ^ (P.m * p) - 1) := by
    rw [e1]; simp [Env.setVar]
  have hhi1 : σ1.vars "hi" = σ.vars "fc" / 2 ^ (P.m * p) * (2 ^ (P.m * p) * 2 ^ P.m) := by
    rw [e1]; simp [Env.setVar]
  have hPp1 : σ1.vars "Pp" = 2 ^ (P.m * p) := by rw [e1]; simp [Env.setVar]; exact hT.Pp_
  have hbb1 : σ1.vars "bb" = 2 ^ P.m := by rw [e1]; simp [Env.setVar, hC.bb_]
  have hcb1 : σ1.vars "cbase" = i0 * P.tabs := by rw [e1]; simp [Env.setVar, hT.cbase_]
  have hac1 : σ1.vars "ac" = 0 := by rw [e1]; simp [Env.setVar]
  have har1 : σ1.arrs = σ.arrs := by rw [e1]; simp [Env.setVar]
  have hix : ∀ j, σ1.vars "lo" + j * σ1.vars "Pp" + σ1.vars "hi" =
      insN (2 ^ P.m) p j (σ.vars "fc") := fun j => by
    rw [hlo1, hPp1, hhi1]; exact insAt_eq _ _ _ _
  have hrowT : ∀ j < 2 ^ P.m, (σ.arrs "TB").getD (i0 * P.tabs +
      insN (2 ^ P.m) p j (σ.vars "fc")) 0 = tbv P.I P.kk P.D i0 (insN (2 ^ P.m) p j (σ.vars "fc")) :=
    fun j hj => hT.tb _ (hins j hj)
  obtain ⟨σ2, r2, hv2, A2, o2⟩ := forgetOr_run (B := B) σ1 (2 ^ P.m) (i0 * P.tabs) hbb1
    (by omega) hcb1 (by omega)
    (fun j hj => by rw [hix, har1]; have := hins j hj; omega)
    (fun j hj => by rw [hix]; have := hins j hj; omega)
    (fun j hj => by rw [hix, har1, hrowT j hj]; exact tbv_le_one) (by omega)
    (by rw [hPp1]; omega)
  have hfold := or_fold (2 ^ P.m) (fun j => (σ1.arrs "TB").getD (i0 * P.tabs +
    (σ1.vars "lo" + j * σ1.vars "Pp" + σ1.vars "hi")) 0)
    (fun j hj => by
      show (σ1.arrs "TB").getD _ 0 ≤ 1
      rw [hix, har1, hrowT j hj]; exact tbv_le_one) (2 ^ P.m) le_rfl
  have hac2 : σ2.vars "ac" ≤ 1 := by
    rw [hv2, hac1, hfold]; split_ifs <;> omega
  have r3 : Run B (.assign "val" (V "ac")) σ2 (σ2.setVar "val" (σ2.vars "ac")) 2 :=
    (Run.assign (evalB_var (by omega))).mono (by simp [Expr.size])
  refine ⟨σ2.setVar "val" (σ2.vars "ac"), (r1.seq (r2.seq r3)).mono (by omega), ?_, ?_, ?_, ?_⟩
  · simp only [vars_setVar, if_true]
    rw [hv2, hac1, hfold, tbv_forget hT.k_]
    exact if_congr (exists_congr fun j => and_congr_right fun hj => by
      show (σ1.arrs "TB").getD _ 0 = 1 ↔ _
      rw [hix, har1, hrowT j hj]; exact Iff.rfl) rfl rfl
  · simp only [arrs_setVar]; rw [A2.1, har1]
  · intro y hy
    simp only [SF, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    have hyv : y ≠ "val" := hy.2.2.2.2.2.2
    simp only [vars_setVar, hyv, if_false]
    rw [A2.2 y (by simp [SO]; tauto), e1]
    simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1]
  · simp only [out_setVar]; rw [o2, e1]; simp [Env.setVar]

end Lax117284Proofs.Machine.TwNode
