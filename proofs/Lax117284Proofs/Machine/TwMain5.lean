import Lax117284Proofs.Machine.TwMain4

/-!
The main program is correct: it answers `1` exactly for the instances that have a fair schedule,
at a cost that depends on which branch it takes.
-/

namespace Lax117284Proofs.Machine.TwMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol
open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding
open Lax117284Proofs.Machine.TwRam (opcode fa fb fc Small)
open Lax117284Proofs.Machine.TwNode (Params)

variable {B : ℕ}

/-- **The numbers the dynamic program needs, for the decomposition `D`.** -/
structure DPB (B Lx OL Kdp : ℕ) (ext : String → ℕ) (P : Params) : Prop where
  sz : P.N ≤ ext "SZ"
  bg : P.N * P.wid ≤ ext "BG"
  tb : P.N * P.tabs ≤ ext "TB"
  lenO : 3 * P.N + 5 ≤ OL
  b1 : P.N * P.tabs + P.tabs + 32 < B
  b2 : P.N * P.wid + P.wid + 32 < B
  b3 : 3 * P.N + 32 < B
  b4 : P.tabs * P.bs + 32 < B
  b5 : P.wid * (P.wid * P.m + 1) + P.wid * P.m + P.m + 32 < B
  b6 : Lx + 32 < B
  b7 : OL + 32 < B
  b8 : P.n + P.m + P.kk + 32 < B
  b9 : P.m * (P.wid + 1) + P.wid + 32 < B
  b10 : 2 ^ P.m + 32 < B
  cost : 60 + TwNode.dpCost P ≤ Kdp

/-- **The numbers the guarded branch needs.** -/
structure GB (B : ℕ) (prog : Program) (x : List ℕ) (n m OL Wp Pn w : ℕ) : Prop where
  h2m : 2 ^ m + 8 < B
  hnn : n * n + 8 < B
  hwB : w + 8 < B
  hsm : Small Wp prog
  hyP : ∀ v ∈ TwGraph.gwList x n m ++ [w], v < Pn
  hyPn : n * n + 2 < Pn
  bPP : Pn * Pn < B
  b2 : Pn + Pn < B
  bnd : prog.length + OL + (n * n + 2) + Pn + 24 < B
  hOL : 0 < OL
  hlit : ∀ ins ∈ prog, opcode ins + 3 < B ∧ fa ins + 3 < B ∧ fb ins + 3 < B ∧ fc ins + 3 < B
  hPn : Pn = 2 ^ Wp

open Classical in
/-- **The cost of the main program.** -/
noncomputable def Kmain (L lg m n t plen Kdp : ℕ) (g : Prop) (z0 : Prop) : ℕ :=
  (24 * L + 60) + (Kprep L lg + (10 + (if g then
    (Kgi m n t plen + (10 + (if z0 then ClBrute.bruteCost m n + 3 else Kdp))) else
      (4 + (if 0 < m then ClBrute.bruteCost m n + 3 else 12)))))

open Classical in
/-- **The main program answers correctly.** -/
theorem main_run {x y0 : List ℕ} {I : Instance} {k : ℕ} (hx : x = y0 ++ [k])
    (hy : EncodesInstance y0 I) (prog : Program) (cc plit : ℕ) (hcc : 1 ≤ cc)
    (ext : String → ℕ) (OL Kdp : ℕ) (z : List ℕ) (t : ℕ) (σ0 : Env)
    (hin : σ0.inp = x) (hout : σ0.out = []) (hW0 : W ext [] [] σ0)
    (hextX : ext "X" = x.length) (hextY : ext "Y" = I.clients * I.clients + 2)
    (hextOP : ext "OP" = prog.length) (hextXA : ext "XA" = prog.length)
    (hextXB : ext "XB" = prog.length) (hextXC : ext "XC" = prog.length)
    (hextM : ext "M" = 2 ^ ((2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit))
    (hextO : ext "O" = OL) (hextbf : ext "bfsc" = I.days * I.clients)
    (hL : x.length + 8 < B) (hbr : 4 * x.length + 64 < B) (hXB : ∀ v ∈ x, v < B)
    (hn : I.clients + 8 < B) (hm : I.days + 8 < B) (hmn : I.days * I.clients + 8 < B)
    (hge : TwPrep.geE cc I.days (Nat.log 2 x.length) + 8 < B) (hccB : 2 * cc + 8 < B)
    (hplB : plit + 8 < B)
    (hwp : (2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit + 8 < B)
    (hPB : 2 ^ ((2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit) + 8 < B)
    (hG : 0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days →
      GB B prog x I.clients I.days OL ((2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit)
        (2 ^ ((2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit))
        (TwPrep.wcnt cc I.days (Nat.log 2 x.length) - 1))
    (hcit : 0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days →
      RunsTo ((2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit) prog
        (TwGraph.gwList x I.clients I.days ++
          [TwPrep.wcnt cc I.days (Nat.log 2 x.length) - 1]) z t ∧ t < OL ∧
      (z = [0] ∨ ∃ D, z = 1 :: D))
    (hDP : ∀ D (hD : Lax117284.Bodlaender.NiceDecomposition I
        (TwPrep.wcnt cc I.days (Nat.log 2 x.length) - 1) D), z = 1 :: D →
      DPB B x.length OL Kdp ext ⟨I, y0, k, D, TwPrep.wcnt cc I.days (Nat.log 2 x.length) - 1, hy, hD⟩)
    (hnice : ∀ D, 0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days → z = 1 :: D →
      Lax117284.Bodlaender.NiceDecomposition I
        (TwPrep.wcnt cc I.days (Nat.log 2 x.length) - 1) D) :
    ∃ σ', Run B (mainCom prog cc plit) σ0 σ'
        (Kmain x.length (Nat.log 2 x.length) I.days I.clients t prog.length Kdp
          (0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days) (z = [0])) ∧
      σ'.out = [if I.HasKFairSchedule k then 1 else 0] := by
  have hdec : EncodesUniform x I k := ⟨y0, hx, hy⟩
  have hlen := ClientsWord.len_eq hdec
  have hL0 : 0 < x.length := by omega
  obtain ⟨σ1, r1, hC1, hL1, hin1, hout1, hW1⟩ := phaseR hdec (by omega) hXB ext hextX σ0 hin hout
    hW0
  obtain ⟨σ2, r2, hmn2, hlg2, hwc2, hok2, hw2, hwp2, hP2, hfr2, har2, ho2⟩ := phaseP (B := B) (k := 0) cc
    plit hcc σ1 hC1.n hC1.m hL1 hL0 hmn hn hm hL hge hccB hplB hwp hPB
  have hn2 : σ2.vars "n" = I.clients := by rw [hfr2 "n" (by decide)]; exact hC1.n
  have hm2 : σ2.vars "m" = I.days := by rw [hfr2 "m" (by decide)]; exact hC1.m
  have hk2 : σ2.vars "k" = k := by rw [hfr2 "k" (by decide)]; exact hC1.k
  have hX2 : σ2.arrs "X" = x := by rw [har2]; exact hC1.X
  have hW2 : W ext ["X"] (VR ++ TwPrep.SPrep) σ2 := by
    refine ⟨fun a ha => ?_, fun v hv => ?_⟩
    · rw [har2]; exact hW1.arrs a ha
    · rw [hfr2 v (fun h => hv (by simp [h]))]
      exact hW1.vars v (fun h => hv (by simp [h]))
  have ho2' : σ2.out = [] := by rw [ho2]; exact hout1
  have hbf2 : σ2.arrs "bfsc" = List.replicate (I.days * I.clients) 0 := by
    rw [hW2.arrs "bfsc" (by simp), hextbf]
  unfold mainCom seqs
  by_cases hg : 0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days
  · -- the guard holds
    have hok1 : σ2.vars "ok" = 1 := by rw [hok2, if_pos hg]
    have hcond : (Cond.lt (Expr.lit 0) (V "ok")).evalB B σ2 = some true := by
      rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (by rw [hok1]; omega))]
      simp [hok1]
    obtain hGB := hG hg
    obtain ⟨hRuns, hOLt, hzc⟩ := hcit hg
    obtain ⟨σ5, r5, hz5, hOlen5, hY5, hX5, hW5, hv5, hmask5, hbb5, ho5⟩ :=
      phaseGI (B := B) hdec prog ext _ _ OL _ t z σ2 hW2 hX2 hn2 hm2 hmn2 hw2 hwp2 hP2 hextY hextOP
        hextXA hextXB hextXC hextM hextO hGB.hPn hGB.hsm hRuns hOLt hGB.hlit hGB.h2m hn hm hGB.hnn
        hL hXB hGB.hwB hGB.hyP hGB.hyPn hGB.bPP hGB.b2 hGB.bnd hGB.hOL
    have hn5 : σ5.vars "n" = I.clients := by
      rw [hv5 "n" (by simp [VG, TwGraph.SGW, TwGraph.SG, TwViol.SD, TwSetup.SI]), hn2]
    have hm5 : σ5.vars "m" = I.days := by
      rw [hv5 "m" (by simp [VG, TwGraph.SGW, TwGraph.SG, TwViol.SD, TwSetup.SI]), hm2]
    have hk5 : σ5.vars "k" = k := by
      rw [hv5 "k" (by simp [VG, TwGraph.SGW, TwGraph.SG, TwViol.SD, TwSetup.SI]), hk2]
    have hbf5 : σ5.arrs "bfsc" = List.replicate (I.days * I.clients) 0 := by
      rw [hW5.arrs "bfsc" (by simp [AG]), hextbf]
    have ho5' : σ5.out = [] := by rw [ho5, ho2']
    have hnn : 0 < z.length := by rcases hzc with rfl | ⟨D, rfl⟩ <;> simp
    have hO0 : (σ5.arrs "O").getD 0 0 = z.getD 0 0 := getD_of_take hz5 hnn
    have hidx : 0 < (σ5.arrs "O").length := by
      have : z.length ≤ (σ5.arrs "O").length := by
        rw [hz5]; exact List.length_take_le' _ _
      omega
    have hOB0 : (σ5.arrs "O").getD 0 0 < B := by
      rw [hO0]
      rcases hzc with rfl | ⟨D, rfl⟩ <;> simp <;> omega
    have hcond2 : ∀ v : ℕ, (σ5.arrs "O").getD 0 0 = v → 1 < B →
        (Cond.eq (G "O" (Expr.lit 0)) (Expr.lit 1)).evalB B σ5 = some (v == 1) := by
      intro v hv hB1
      rw [evalB_condEq (m := (σ5.arrs "O").getD 0 0) (n := 1) ?_ (evalB_lit hB1), hv]
      exact evalB_get (k := 0) (evalB_lit (by omega)) (by
        rw [List.getElem?_eq_getElem hidx]; simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hidx]) hOB0
    unfold guarded
    rcases hzc with hz0 | ⟨D, hzD⟩
    · -- the decomposition step found no decomposition: enumerate
      have hO00 : (σ5.arrs "O").getD 0 0 = 0 := by rw [hO0, hz0]; rfl
      obtain ⟨σ6, r6, ho6⟩ := brute_run hdec hbr hXB σ5 hX5 hn5 hm5 hk5 hbf5 ho5'
      have hite := Run.ite_false (c := TwMain.dpBranch) (hcond2 0 hO00 (by omega)) r6
      have hRG := r5.seq hite
      refine ⟨σ6, (r1.seq (r2.seq (Run.ite_true hcond hRG))).mono ?_, ho6⟩
      simp only [Kmain, if_pos hg, if_pos hz0, Cond.size, Expr.size]
      omega
    · -- the decomposition step returned a decomposition: the dynamic program
      have hD := hnice D hg hzD
      have hO01 : (σ5.arrs "O").getD 0 0 = 1 := by rw [hO0, hzD]; rfl
      have hDPB := hDP D hD hzD
      have hPn1 : 1 ≤ 2 ^ ((2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit) := Nat.one_le_two_pow
      have hzB : ∀ v ∈ z, v < B := by
        intro v hv
        have h1 := TwSetup.RunsTo.out_lt hRuns v hv
        rw [← hGB.hPn] at h1
        exact lt_of_lt_of_le h1 (le_trans (Nat.le_mul_self _) hGB.bPP.le)
      obtain ⟨σ7, r7, ho7⟩ := phaseDP (B := B) ⟨I, y0, k, D, _, hy, hD⟩ ext z σ5 hzD hz5 hzB hW5
        (hX5.trans hx) hn5 hm5 hk5
        (by rw [hv5 "w" (by simp [VG, TwGraph.SGW, TwGraph.SG, TwViol.SD, TwSetup.SI]), hw2])
        (by rw [hv5 "mn" (by simp [VG, TwGraph.SGW, TwGraph.SG, TwViol.SD, TwSetup.SI]), hmn2]; rfl)
        hmask5 hbb5 (by rw [hX5]; exact hXB) hDPB.sz hDPB.bg hDPB.tb (by rw [hOlen5]; exact hDPB.lenO)
        hDPB.b1 hDPB.b2 hDPB.b3 hDPB.b4 hDPB.b5 (by rw [hX5]; exact hDPB.b6)
        (by rw [hOlen5]; exact hDPB.b7) hDPB.b8 hDPB.b9 hDPB.b10
      have hite := Run.ite_true (d := TwMain.brute) (hcond2 1 hO01 (by omega)) r7
      have hRG := r5.seq hite
      refine ⟨σ7, (r1.seq (r2.seq (Run.ite_true hcond hRG))).mono ?_, ?_⟩
      · have hc := hDPB.cost
        have hz0 : ¬ z = [0] := by rw [hzD]; simp
        simp only [Kmain, if_pos hg, if_neg hz0, Cond.size, Expr.size]
        omega
      · rw [ho7, ho5']; simp
  · -- the guard fails: enumerate
    have hok0 : σ2.vars "ok" = 0 := by rw [hok2, if_neg hg]
    have hcond : (Cond.lt (Expr.lit 0) (V "ok")).evalB B σ2 = some false := by
      rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (by rw [hok0]; omega))]
      simp [hok0]
    obtain ⟨σ6, r6, ho6⟩ := brute0_run hdec hbr hXB σ2 hX2 hn2 hm2 hk2 hbf2 hn hm
      (hXB k (by rw [hx]; simp)) ho2'
    refine ⟨σ6, (r1.seq (r2.seq (Run.ite_false hcond r6))).mono ?_, ho6⟩
    simp only [Kmain, if_neg hg, Cond.size, Expr.size]
    omega

end Lax117284Proofs.Machine.TwMain
