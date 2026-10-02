import Lax117284Proofs.Treewidth.Fun.VMSolvePhases

/-!
# WP V3 (10): `solve_run` — the whole program on one input

From the initial environment `initEnv (fun _ => Wx + 1) x` the command `solveCom` runs, within `Cimp`, with every value
below `Bimp`, to an environment whose output tape is `y`, provided the functional run `Runs Δ (Bx x) main [toVal x] (toVal y) (Kx x)`
exists and `|y| ≤ Kx x`.
-/

namespace Lax117284Proofs.Treewidth.Fun.Load

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax117284Proofs.Treewidth.Fun.VM Lax117284Proofs.Treewidth.Fun.VM.Ram ToVal

theorem getD_of_ge (x : List ℕ) {j : ℕ} (h : x.length ≤ j) : x.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem noWrite_dispatchFrom : ∀ (f k : ℕ), (dispatchFrom k f).NoWrite := by
  intro f
  induction f with
  | zero =>
    intro k
    simp only [dispatchFrom]
    unfold blkOp
    split <;> simp [bHalt, bLit, bVar, bBin, bLt, bEq, bCons, bFst, bSnd, bIsNat, bJz, bJmp, bSlide, bCall, bRet,
      incPc, incSp, decSp, Com.NoWrite]
  | succ f ih =>
    intro k
    simp only [dispatchFrom, Com.NoWrite]
    refine ⟨?_, ih (k + 1)⟩
    unfold blkOp
    split <;> simp [bHalt, bLit, bVar, bBin, bLt, bEq, bCons, bFst, bSnd, bIsNat, bJz, bJmp, bSlide, bCall, bRet,
      incPc, incSp, decSp, Com.NoWrite]

theorem noWrite_vmLoop : vmLoop.NoWrite := by
  unfold vmLoop bBody bFetch bDispatch
  simp only [Com.NoWrite]
  exact ⟨⟨trivial, trivial⟩, noWrite_dispatchFrom 16 0⟩

theorem solve_run (Δ : ℕ → Option Tm) {N : ℕ} (hN : ∀ f, N ≤ f → Δ f = none) (main : ℕ) (fmt : Fmt) (p : KP)
    (h0 : 1 ≤ p.c0) (h1 : 1 ≤ p.c1) (h2 : 1 ≤ p.c2) {x y : List ℕ} (hfmt : fmtLen fmt x = x.length)
    (hruns : Runs Δ (Bx p fmt x) main [toVal x] (toVal y) (Kx p fmt x)) (hy : y.length ≤ Kx p fmt x) :
    ∃ σ', Run (Bimp Δ N main p fmt x) (solveCom Δ N main fmt p)
      (initEnv (fun _ => Wx Δ N main p fmt x + 1) x) σ' (Cimp Δ N main p fmt x) ∧ σ'.out = y := by
  -- numeric facts, front-loaded
  have hn2 : 2 ≤ x.length := two_le_len fmt x hfmt
  have hx : x ≠ [] := by intro h; rw [h] at hn2; simp at hn2
  have hBv2 : 2 ≤ Bx p fmt x := bexp_ge_two _ _
  have hKB : Kx p fmt x < Bx p fmt x := Bx_gt_K p fmt x
  have hxBv : ∀ v ∈ x, v < Bx p fmt x := entry_lt_Bx p fmt x
  have hBiEq : Bimp Δ N main p fmt x = 2 * Bx p fmt x + 4 * (Kx p fmt x + x.length + 8) + kappa Δ N main p := rfl
  have hWEq : Wx Δ N main p fmt x = (Bx p fmt x + x.length + 1) + progLen Δ N main + Bx p fmt x + 3 * Kx p fmt x + 3 := rfl
  have hkS : progLen Δ N main + N + wordMax (opasL Δ N main) + wordMax (ftL Δ N) + p.c0 + p.c1 + p.c2 + (kE p).size + 1
      = kS Δ N main p := rfl
  have hκ : kappa Δ N main p = 1000 * kS Δ N main p := rfl
  have hκpl : progLen Δ N main < kappa Δ N main p := by omega
  have hκN : N < kappa Δ N main p := by omega
  have hκo : wordMax (opasL Δ N main) < kappa Δ N main p := by omega
  have hκf : wordMax (ftL Δ N) < kappa Δ N main p := by omega
  have hκc1 : p.c1 < kappa Δ N main p := by omega
  have hκc2 : p.c2 < kappa Δ N main p := by omega
  have hκ16 : 16 < kappa Δ N main p := by omega
  have hNp := N_le_progLen Δ N main
  have hCost := cost_total_le Δ N main p fmt x y hy
  set n := x.length with hn
  set Bv := Bx p fmt x with hBv
  set Kv := Kx p fmt x with hKv
  set κ := kappa Δ N main p with hκdef
  set Bi := Bimp Δ N main p fmt x with hBidef
  set W := Wx Δ N main p fmt x with hWdef
  set A := W + 1 with hAdef
  set σ0 : IEnv := initEnv (fun _ => A) x with hσ0
  have hAn : n ≤ A := by omega
  have hxB : ∀ v ∈ x, v < Bi := fun v hv => by have := hxBv v hv; omega
  have hL : n + 1 < Bi := by omega
  have hσ0inp : σ0.inp = x := rfl
  have hσ0arr : ∀ a, σ0.arrs a = List.replicate A 0 := fun a => rfl
  have hσ0out : σ0.out = [] := rfl
  -- phase 1: read
  obtain ⟨σ1, hr1, hread, hv1, ha1, ho1⟩ := read_phase fmt (Bi := Bi) hx hAn hxB hL hfmt (σ := σ0) hσ0inp
    (by rw [hσ0arr]; exact replicate_eq_arrOf _ _)
  have hi1 : σ1.vars "i" = n := hread.2
  have hha1 : σ1.arrs "HA" = arrOf A (fun j => x.getD j 0) := by
    rw [hread.1.1.ha, hi1]
    exact arrOf_congr (fun j _ => by
      by_cases hj : j < n
      · simp [hj]
      · rw [if_neg hj, getD_of_ge x (show x.length ≤ j by omega)])
  have hM1 : σ1.vars "M" = wordMax x := by
    have := hread.1.1.hM
    rw [hi1, hn, List.take_length] at this
    exact this
  -- phase 2: K, B
  have hidx : x.getD 0 0 * x.getD 0 0 + fmt.off < n := idx_lt fmt x hfmt
  have r2 := setKB_run (x := x) (A := A) (Bi := Bi) (off := fmt.off) p h0 h1 h2 hAn hxB hidx
    (by omega) (by omega) (show Kx p fmt x < Bi by omega) (show Bx p fmt x < Bi by omega) hi1 hha1 hM1
  set σ2 := afterKB x fmt.off p σ1 with hσ2
  have hσ2len : σ2.vars "len" = n := by simp [hσ2, afterKB]; rfl
  have hσ2B : σ2.vars "B" = Bv := by simp [hσ2, afterKB]; rfl
  have hσ2a : ∀ a, σ2.arrs a = σ1.arrs a := fun a => rfl
  have hσ2o : σ2.out = σ1.out := rfl
  have hσ2v : ∀ y, y ≠ "len" → y ≠ "kw" → y ≠ "K" → y ≠ "B" → σ2.vars y = σ1.vars y := by
    intro y a b c d; simp [hσ2, afterKB, a, b, c, d]
  -- phase 3: HB
  obtain ⟨σ3, hr3, hq3⟩ := (hbCom_spec (A := A) (Bv := Bv) (n := n) (Bi := Bi) hAn (by omega) (by omega)
    (by omega)).run (σ := σ2) ⟨hσ2len, hσ2B, by rw [hσ2a, ha1 "HB" (by decide), hσ0arr "HB"]; exact replicate_eq_arrOf _ _⟩
  have hv3 : ∀ y, y ≠ "tot" → y ≠ "i" → σ3.vars y = σ2.vars y := fun y a b =>
    hr3.frame_var y (by simp [hbCom, hbLoop, hbBody, bump, Com.wvars, a, b])
  have ha3 : ∀ a, a ≠ "HB" → σ3.arrs a = σ2.arrs a := fun a ha =>
    hr3.frame_arr a (by simp [hbCom, hbLoop, hbBody, Com.warrs, ha])
  have ho3 : σ3.out = σ2.out := hr3.out_eq (by simp [hbCom, hbLoop, hbBody, bump, Com.NoWrite])
  have hB3 : σ3.vars "B" = Bv := hq3.1.2.2.1
  have hlen3 : σ3.vars "len" = n := hq3.2.2
  have hi3 : σ3.vars "i" = n - 1 := hq3.2.1
  have hHB3 : σ3.arrs "HB" = arrOf A (fun j => if j < n - 1 then Bv + j + 1 else 0) := by
    have := hq3.1.2.2.2; rw [hi3] at this; exact this
  -- phase 4: scalars
  have hSTK3 : σ3.arrs "STK" = List.replicate A 0 := by
    rw [ha3 _ (by decide), hσ2a, ha1 _ (by decide), hσ0arr]
  have hr4 := setup_run (Bi := Bi) (n := n) (Bv := Bv) (by omega) (σ := σ3) hlen3 hB3 (by omega) (by omega)
    (by rw [hSTK3]; simp; omega)
  set σ4 := afterSetup n Bv σ3 with hσ4
  have hz : ∀ a, a ≠ "HA" → a ≠ "HB" → a ≠ "STK" → σ4.arrs a = List.replicate A 0 := by
    intro a a1 a2 a3'
    simp only [hσ4, afterSetup, arrs_setArr, arrs_setVar, a3', if_false]
    rw [ha3 a a2, hσ2a, ha1 a a1, hσ0arr]
  have hv4 : ∀ y, y ≠ "sp" → y ≠ "hp" → y ≠ "run" → σ4.vars y = σ3.vars y := by
    intro y a b c; simp [hσ4, afterSetup, a, b, c]
  -- phases 5-7: the code arrays
  have hopsB : ∀ v ∈ opsL Δ N main, v < Bi := fun v hv => by have := opsL_lt Δ N main v hv; omega
  have hopasB : ∀ v ∈ opasL Δ N main, v < Bi := fun v hv => by have := le_wordMax_of_mem hv; omega
  have hftB : ∀ v ∈ ftL Δ N, v < Bi := fun v hv => by have := le_wordMax_of_mem hv; omega
  have hlo : (opsL Δ N main).length = progLen Δ N main := opsL_length Δ N main
  have hla : (opasL Δ N main).length = progLen Δ N main := opasL_length Δ N main
  have hlf : (ftL Δ N).length = N := ftL_length Δ N
  obtain ⟨σ5, hr5, ha5, hv5, hi5, ho5, hb5⟩ := storeSeq_run0 (Bi := Bi) "OP" (opsL Δ N main) σ4 A
    (hz "OP" (by decide) (by decide) (by decide)) (by omega) hopsB (by omega)
  obtain ⟨σ6, hr6, ha6, hv6, hi6, ho6, hb6⟩ := storeSeq_run0 (Bi := Bi) "OA" (opasL Δ N main) σ5 A
    (by rw [hb5 _ (by decide)]; exact hz "OA" (by decide) (by decide) (by decide)) (by omega) hopasB (by omega)
  obtain ⟨σ7, hr7, ha7, hv7, hi7, ho7, hb7⟩ := storeSeq_run0 (Bi := Bi) "FT" (ftL Δ N) σ6 A
    (by rw [hb6 _ (by decide), hb5 _ (by decide)]; exact hz "FT" (by decide) (by decide) (by decide)) (by omega) hftB
    (by omega)
  have hv47 : σ7.vars = σ4.vars := by rw [hv7, hv6, hv5]
  have hLoaded : Loaded Δ N main x Bv A σ7 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hv47, hv4 _ (by decide) (by decide) (by decide), hv3 _ (by decide) (by decide),
        hσ2v _ (by decide) (by decide) (by decide) (by decide), hv1 _ (by decide)]; rfl
    · rw [hv47]; simp [hσ4, afterSetup]
    · rw [hv47, hv4 _ (by decide) (by decide) (by decide), hv3 _ (by decide) (by decide),
        hσ2v _ (by decide) (by decide) (by decide) (by decide), hv1 _ (by decide)]; rfl
    · rw [hv47]; simp [hσ4, afterSetup]; rfl
    · rw [hv47, hv4 _ (by decide) (by decide) (by decide), hB3]
    · rw [hv47]; simp [hσ4, afterSetup]
    · rw [hb7 _ (by decide), hb6 _ (by decide), hb5 _ (by decide)]
      simp only [hσ4, afterSetup, arrs_setArr, arrs_setVar]
      rw [if_neg (by decide), ha3 _ (by decide), hσ2a, hha1]
    · rw [hb7 _ (by decide), hb6 _ (by decide), hb5 _ (by decide)]
      simp only [hσ4, afterSetup, arrs_setArr, arrs_setVar]
      rw [if_neg (by decide), hHB3]
      exact arrOf_congr (fun j _ => by unfold hbF; split_ifs <;> first | rfl | (exfalso; omega))
    · rw [hb7 _ (by decide), hb6 _ (by decide), hb5 _ (by decide)]
      simp only [hσ4, afterSetup, arrs_setArr, arrs_setVar]
      rw [if_true, hSTK3, replicate_eq_arrOf, set_arrOf]
    · rw [hb7 _ (by decide), hb6 _ (by decide), hb5 _ (by decide), hz "RETPC" (by decide) (by decide) (by decide)]
      simp
    · rw [hb7 _ (by decide), hb6 _ (by decide), hb5 _ (by decide), hz "RETH" (by decide) (by decide) (by decide)]
      simp
    · rw [hb7 _ (by decide), hb6 _ (by decide)]; exact ha5
    · rw [hb7 _ (by decide)]; exact ha6
    · exact ha7
  -- the VM run
  have hWeq' : W = (Bv + n + 1) + (mkProgF Δ N main 1 Bv).len + Bv + 3 * Kv + 3 := hWEq
  have hAbs7 : Abs ⟨0, [Bv] ++ [], [], heapOf x Bv⟩ σ7 := abs_of_loaded hLoaded hAn (by omega) hx
  have hCst7 : Cst (mkProgF Δ N main 1 Bv) ((Bv + n + 1) + (mkProgF Δ N main 1 Bv).len + Bv + 3 * Kv + 3) Bi σ7 := by
    rw [← hWeq']
    exact cst_of_loaded hLoaded (W := W) rfl (by omega) (by omega) (by omega)
  have hrep : RepL Bv (heapOf x Bv) [Bv] [toVal x] := RepL.cons (rep_input (by omega) hxBv hx) RepL.nil
  have hbd : St.Bd (Bv + n + 1) ⟨0, [Bv] ++ [], [], heapOf x Bv⟩ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show 0 ≤ _; omega
    · simp
    · intro w hw; simp at hw; omega
    · simp
    · intro q hq; simp at hq
    · show (heapOf x Bv).length ≤ Bv + n + 1
      rw [heapOf_length]; omega
    · intro q hq
      simp only [heapOf, List.mem_map, List.mem_range] at hq
      obtain ⟨j, hj, rfl⟩ := hq
      have := getD_lt (B := Bv) (x := x) (by omega) hxBv j
      unfold hbF
      constructor
      · omega
      · split_ifs <;> omega
  obtain ⟨w, H', σ8, hr8, hA8, hC8, hrun8, hext, hrep8, hlen8⟩ := vm_ram_correctF Δ hN hBv2 (main := main)
    (xs := [toVal x]) (y := toVal y) (c := Kv) hruns hrep hbd hAbs7 hCst7 hLoaded.run
  rw [heapOf_length] at hlen8
  have hrep8' : Rep Bv H' w (listVal y) := by rw [← toVal_list]; exact hrep8
  have hstk8 : (σ8.arrs "STK")[0]? = some w := by
    have := hA8.result.2
    simpa using this
  obtain ⟨σ9, hr9, ho9⟩ := wrCom_run (Bi := Bi) (B := Bv) (w := w) (H := H') (l := y) (σ := σ8) (by omega)
    (by omega) hrep8' hstk8 hC8.tb hA8.ha hA8.hb
  refine ⟨σ9, ?_, ?_⟩
  · exact ((hr1.seq (r2.seq (hr3.seq (hr4.seq (hr5.seq (hr6.seq (hr7.seq (hr8.seq hr9)))))))).mono
      (by have := hCost; omega))
  · rw [ho9]
    have e8 : σ8.out = σ7.out := hr8.out_eq noWrite_vmLoop
    have e4 : σ4.out = σ3.out := rfl
    rw [e8, ho7, ho6, ho5, e4, ho3, hσ2o, ho1]
    simp [σ0, initEnv]

end Lax117284Proofs.Treewidth.Fun.Load
