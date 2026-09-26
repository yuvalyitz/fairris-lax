import Lax117284Proofs.Machine.IlpRead

/-!
The header: from the counts `N` and `M` of the word, the number `n` of clients and the constants.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

theorem nM_lt_nM {a b : ℕ} (h : a < b) : nM a < nM b := by
  unfold nM nT
  have : 2 ^ (a * a) < 2 ^ (b * b) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
  omega

theorem nM_eq (n : ℕ) : nM n = 2 ^ (n * n) + n := rfl

/-- The test of the loop that finds `n`, evaluated. -/
theorem nCond_eval {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (σ : Env)
    (hM : σ.vars "M" = nM n) (hk : σ.vars "n" ≤ n) :
    ∃ v, (Cond.lt (.add (.shiftl (lit 1) (.mul (V "n") (V "n"))) (V "n")) (V "M")).evalB B σ = some v ∧
      (v = true ↔ σ.vars "n" < n) := by
  have hkk : σ.vars "n" * σ.vars "n" ≤ n * n := Nat.mul_le_mul hk hk
  have hpow : 2 ^ (σ.vars "n" * σ.vars "n") ≤ 2 ^ (n * n) :=
    Nat.pow_le_pow_right (by norm_num) hkk
  have hBnn := hb.nn_lt
  have hBn := hb.n_lt
  have hBM := hb.nM_lt
  have hBT := hb.nT_lt
  have hB1 := hb.one_lt_B
  have hTn : nT n = 2 ^ (n * n) := rfl
  have hsum : 2 ^ (σ.vars "n" * σ.vars "n") + σ.vars "n" ≤ nM n := by
    rw [nM_eq]; omega
  have e1 : (Expr.mul (V "n") (V "n")).evalB B σ = some (σ.vars "n" * σ.vars "n") :=
    evalB_bin (evalB_var (by omega)) (evalB_var (by omega)) (by
      show σ.vars "n" * σ.vars "n" < B; omega)
  have e2 : (Expr.shiftl (lit 1) (.mul (V "n") (V "n"))).evalB B σ =
      some (1 * 2 ^ (σ.vars "n" * σ.vars "n")) :=
    evalB_bin (evalB_lit hB1) e1 (by
      show 1 * 2 ^ (σ.vars "n" * σ.vars "n") < B; omega)
  have e3 : (Expr.add (.shiftl (lit 1) (.mul (V "n") (V "n"))) (V "n")).evalB B σ =
      some (1 * 2 ^ (σ.vars "n" * σ.vars "n") + σ.vars "n") :=
    evalB_bin e2 (evalB_var (by omega)) (by
      show 1 * 2 ^ (σ.vars "n" * σ.vars "n") + σ.vars "n" < B; omega)
  refine ⟨_, evalB_condLt e3 (evalB_var (by omega)), ?_⟩
  simp only [decide_eq_true_eq]
  rw [hM, one_mul]
  constructor
  · intro h
    by_contra hnk
    have : σ.vars "n" = n := by omega
    rw [this] at h
    rw [nM_eq] at h
    omega
  · intro h
    have := nM_lt_nM h
    have hk2 : nM (σ.vars "n") = 2 ^ (σ.vars "n" * σ.vars "n") + σ.vars "n" := rfl
    omega

/-- **The number of clients is found.** -/
theorem nCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => σ.vars "M" = nM n) nCom (fun _ σ' => σ'.vars "n" = n) (2 + (14 * n + 10)) := by
  have hloop : Spec B (fun σ => σ.vars "M" = nM n ∧ σ.vars "n" = 0)
      (.while (.lt (.add (.shiftl (lit 1) (.mul (V "n") (V "n"))) (V "n")) (V "M")) (bump "n"))
      (fun _ σ' => σ'.vars "n" = n) (14 * n + 10) := by
    refine Spec.post (Spec.while_potential (B := B)
      (b := .lt (.add (.shiftl (lit 1) (.mul (V "n") (V "n"))) (V "n")) (V "M")) (c := bump "n")
      (fun σ => σ.vars "M" = nM n ∧ σ.vars "n" ≤ n) (fun σ => 14 * (n - σ.vars "n")) ?_ ?_
      (fun σ h => ⟨h.1, by omega⟩) ?_) ?_
    · intro σ hI
      obtain ⟨v, hv, -⟩ := nCond_eval hb σ hI.1 hI.2
      exact ⟨v, hv⟩
    · intro σ hI hcond
      obtain ⟨v, hv, hiff⟩ := nCond_eval hb σ hI.1 hI.2
      rw [hv] at hcond
      have hlt : σ.vars "n" < n := hiff.mp (Option.some.inj hcond)
      have hBn := hb.n_lt
      obtain ⟨σ', hr, e⟩ := bump_spec (B := B) "n" hb.one_lt_B σ (by omega)
      refine ⟨σ', 4, hr, ⟨by rw [e]; simpa [Env.setVar] using hI.1, by rw [e]; simp [Env.setVar]; omega⟩, ?_⟩
      rw [e]
      simp only [Env.setVar, if_true]
      have : (Cond.lt (.add (.shiftl (lit 1) (.mul (V "n") (V "n"))) (V "n")) (V "M")).size = 9 := by
        simp
      rw [this]
      omega
    · intro σ h
      simp only [h.2, Nat.sub_zero]
      have : (Cond.lt (.add (.shiftl (lit 1) (.mul (V "n") (V "n"))) (V "n")) (V "M")).size = 9 := by
        simp
      rw [this]
    · rintro σ σ' - ⟨⟨hM, hk⟩, hfalse⟩
      obtain ⟨v, hv, hiff⟩ := nCond_eval hb σ' hM hk
      rw [hv] at hfalse
      have : v = false := Option.some.inj hfalse
      have : ¬ σ'.vars "n" < n := fun h => by
        have := hiff.mpr h; rw [‹v = false›] at this; simp at this
      omega
  have hA : Spec B (fun σ => σ.vars "M" = nM n) (asg "n" (lit 0)) (fun σ σ' => σ' = σ.setVar "n" 0) 2 :=
    Spec.pre (assign_lit_spec (B := B) "n" 0 (by have := hb.five_lt_B; omega)) (fun _ _ => trivial)
  unfold nCom
  exact Spec.mono (Spec.seq hA hloop (fun σ σ1 hM e => by rw [e]; exact ⟨by simpa using hM, by simp⟩)
    (fun σ σ1 σ2 _ _ hp => hp)) le_rfl

theorem h2Com_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.vars "M" = nM n) h2Com
      (fun _ σ' => σ'.vars "nn" = n * n ∧ σ'.vars "T" = nT n ∧ σ'.vars "Z" = nZ n ∧
        σ'.vars "V" = nV n ∧ σ'.vars "np" = n + 1 ∧ σ'.vars "pw" = 1) 60 := by
  unfold h2Com
  run_vcg
  all_goals
    have hnv : σ.vars "n" = n := ‹σ.vars "n" = n›
    have hMv : σ.vars "M" = nM n := ‹σ.vars "M" = nM n›
    have hBnn := hb.nn_lt
    have hBn := hb.n_lt
    have hBM := hb.nM_lt
    have hBT := hb.nT_lt
    have hBZ := hb.nZ_lt
    have hBV := hb.nV_lt
    have hB5 := hb.five_lt_B
    have hBn1 : n + 1 < B := hb.lt_U (by have := n_succ_le_zLen n; unfold Ub; omega)
    have hTv : nM n - n = nT n := by unfold nM; omega
    have e2 : nZ n = 2 ^ n := rfl
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (try simp only [hnv, hMv])
  all_goals (first | omega | (rw [hTv, one_mul, ← e2]; exact hBV) |
    exact ⟨trivial, hTv, by rw [one_mul, e2], by rw [hTv, one_mul, ← e2]; rfl, trivial, trivial⟩)

theorem pwBody_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => σ.vars "np" = n + 1 ∧ σ.vars "pw" = (n + 1) ^ σ.vars "i" ∧ σ.vars "i" < n + 1)
      (.seq (asg "pw" (.mul (V "pw") (V "np"))) (bump "i"))
      (fun σ σ' => σ'.vars "pw" = σ.vars "pw" * σ.vars "np" ∧ σ'.vars "i" = σ.vars "i" + 1) 20 := by
  run_vcg
  all_goals
    have hnp : σ.vars "np" = n + 1 := ‹σ.vars "np" = n + 1›
    have hpw : σ.vars "pw" = (n + 1) ^ σ.vars "i" := ‹σ.vars "pw" = (n + 1) ^ σ.vars "i"›
    have hi : σ.vars "i" < n + 1 := ‹σ.vars "i" < n + 1›
    have hKB := hb.Kn_lt
    have hB5 := hb.five_lt_B
    have hn1 : n + 1 < B := hb.lt_U (by have := n_succ_le_zLen n; unfold Ub; omega)
    have hle : (n + 1) ^ σ.vars "i" * (n + 1) ≤ (n + 1) ^ (n + 1) := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) hi
    have hK : Kn n = (n + 1) ^ (n + 1) + 1 := rfl
    have h1 : σ.vars "pw" * (n + 1) ≤ (n + 1) ^ (n + 1) := by rw [hpw]; exact hle
    have h2 : σ.vars "pw" ≤ (n + 1) ^ (n + 1) := le_trans (Nat.le_mul_of_pos_right _ (by omega)) h1
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (try simp only [hnp])
  all_goals (first | omega | exact ⟨trivial, trivial⟩)

theorem pwCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => σ.vars "np" = n + 1 ∧ σ.vars "pw" = 1) pwCom
      (fun _ σ' => σ'.vars "pw" = (n + 1) ^ (n + 1)) ((20 + 4) * (n + 1) + 6) := by
  have hn1 : n + 1 < B := hb.lt_U (by have := n_succ_le_zLen n; unfold Ub; omega)
  have hs := scan_spec (B := B) "i" "np" (n + 1) 20 (.seq (asg "pw" (.mul (V "pw") (V "np"))) (bump "i"))
    (fun σ => σ.vars "np" = n + 1) (fun k σ => σ.vars "pw" = (n + 1) ^ k)
    (stable_var "np" (fun v => v = n + 1) (by decide)) hn1 (fun σ h => h) ?_
  · unfold pwCom
    refine Spec.pre (Spec.post hs ?_) ?_
    · rintro σ σ' - ⟨-, hpw, -⟩
      exact hpw
    · rintro σ ⟨hnp, hpw⟩
      exact ⟨by simpa using hnp, by simpa using hpw⟩
  · intro k hk σ ⟨hnp, hik, hpw⟩
    obtain ⟨σ', hr, h1, h2⟩ := pwBody_vals hb σ ⟨hnp, by rw [hpw, hik], by omega⟩
    refine ⟨σ', hr, by omega, ?_⟩
    rw [h1, hpw, hnp, pow_succ]

theorem h4Com_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => σ.vars "pw" = (n + 1) ^ (n + 1) ∧ σ.vars "N" = nN n ∧ σ.vars "M" = nM n ∧
        σ.vars "nn" = n * n ∧ σ.vars "T" = nT n ∧ σ.arrs "z" = ilpWord n cnt bb) h4Com
      (fun _ σ' => σ'.vars "K" = Kn n ∧ σ'.vars "R" = Rd n ∧ σ'.vars "D" = Dn n ∧
        σ'.vars "rb" = 2 + nM n * nN n ∧ σ'.vars "tn" = 2 + nT n * nN n ∧ σ'.vars "bb" = bb) 80 := by
  unfold h4Com
  run_vcg
  all_goals
    have hpw : σ.vars "pw" = (n + 1) ^ (n + 1) := ‹σ.vars "pw" = (n + 1) ^ (n + 1)›
    have hN : σ.vars "N" = nN n := ‹σ.vars "N" = nN n›
    have hM : σ.vars "M" = nM n := ‹σ.vars "M" = nM n›
    have hnn : σ.vars "nn" = n * n := ‹σ.vars "nn" = n * n›
    have hT : σ.vars "T" = nT n := ‹σ.vars "T" = nT n›
    have hz : σ.arrs "z" = ilpWord n cnt bb := ‹σ.arrs "z" = ilpWord n cnt bb›
    have hK : Kn n = (n + 1) ^ (n + 1) + 1 := rfl
    have hBK := hb.Kn_lt
    have hBR := hb.Rd_lt
    have hBD := hb.Dn_lt
    have hBrb := hb.rb_lt
    have hBtn := hb.tn_lt
    have hBN := hb.nN_lt
    have hBM := hb.nM_lt
    have hBnn := hb.nn_lt
    have hBz := hb.zLen_lt
    have hB5 := hb.five_lt_B
    have hBv : bb < B := hb.lt_U (by have := hb.hbb; unfold Ub; omega)
    have hlz : (σ.arrs "z").length = zLen n := by rw [hz, ilpWord_length]
    have hTM : nT n < nM n := by unfold nM; have := hb.n1; omega
    have hzv : (σ.arrs "z").getD (2 + nM n * nN n + nT n) 0 = bb := by
      rw [hz, ilpWord_rhs n cnt bb hTM]; unfold rhs; rw [if_neg (lt_irrefl _)]
    have hidx : 2 + nM n * nN n + nT n < zLen n := by unfold zLen; omega
    have hRd : Rd n = Kn n + 1 := rfl
    have hDn : Dn n = nN n + 2 * (n * n) + 1 := rfl
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (try simp only [hpw, hN, hM, hnn, hT] at *)
  all_goals (first | omega | exact ⟨hK.symm, by omega, hDn.symm, trivial, trivial, hzv⟩)

/-- What the machine holds after reading the word: the counts, the word and the arrays. -/
structure Read0 (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (σ : Env) : Prop where
  hN : σ.vars "N" = nN n
  hM : σ.vars "M" = nM n
  hz : σ.arrs "z" = ilpWord n cnt bb
  ldg : (σ.arrs "dg").length = Dn n
  lhl : (σ.arrs "hl").length = nT n
  lkd : (σ.arrs "kd").length = nN n
  lrk : (σ.arrs "rkA").length = nN n
  lsg : (σ.arrs "sg").length = nT n
  lS : (σ.arrs "S").length = n
  lwv : (σ.arrs "wv").length = nN n
  les : (σ.arrs "es").length = nT n
  lxv : (σ.arrs "xv").length = nN n

/-- **The header.** -/
theorem hdrCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => Read0 n cnt bb σ) hdrCom (fun _ σ' => Ctx n cnt bb σ')
      ((2 + (14 * n + 10)) + (60 + (((20 + 4) * (n + 1) + 6) + 80))) := by
  intro σ0 h0
  obtain ⟨σ1, r1, hn1, hv1, ha1, -, -⟩ := (nCom_spec hb).frame σ0 h0.hM
  have hM1 : σ1.vars "M" = nM n := by rw [hv1 "M" (by decide)]; exact h0.hM
  obtain ⟨σ2, r2, ⟨hnn2, hT2, hZ2, hV2, hnp2, hpw2⟩, hv2, ha2, -, -⟩ :=
    (h2Com_vals hb).frame σ1 ⟨hn1, hM1⟩
  obtain ⟨σ3, r3, hpw3, hv3, ha3, -, -⟩ := (pwCom_spec hb).frame σ2 ⟨hnp2, hpw2⟩
  have hz3 : σ3.arrs "z" = ilpWord n cnt bb := by
    rw [ha3 "z" (by decide), ha2 "z" (by decide), ha1 "z" (by decide)]; exact h0.hz
  have hN3 : σ3.vars "N" = nN n := by
    rw [hv3 "N" (by decide), hv2 "N" (by decide), hv1 "N" (by decide)]; exact h0.hN
  have hM3 : σ3.vars "M" = nM n := by
    rw [hv3 "M" (by decide), hv2 "M" (by decide), hM1]
  have hnn3 : σ3.vars "nn" = n * n := by rw [hv3 "nn" (by decide)]; exact hnn2
  have hT3 : σ3.vars "T" = nT n := by rw [hv3 "T" (by decide)]; exact hT2
  obtain ⟨σ4, r4, ⟨hK4, hR4, hD4, hrb4, htn4, hbb4⟩, hv4, ha4, -, -⟩ :=
    (h4Com_vals hb).frame σ3 ⟨hpw3, hN3, hM3, hnn3, hT3, hz3⟩
  refine ⟨σ4, ?_, ?_⟩
  · exact Run.mono (r1.seq (r2.seq (r3.seq r4))) (by omega)
  · have hlen : ∀ a, (σ4.arrs a).length = (σ0.arrs a).length := fun a => by
      rw [run_len_arrs r4 a, run_len_arrs r3 a, run_len_arrs r2 a, run_len_arrs r1 a]
    refine
      { hN := ?_, hM := ?_, hn := ?_, hT := ?_, hZ := ?_, hV := ?_, hK := hK4, hR := hR4, hD := hD4,
        hrb := hrb4, htn := htn4, hnn := ?_, hbb := hbb4, hz := ?_, ldg := ?_, lhl := ?_, lkd := ?_,
        lrk := ?_, lsg := ?_, lS := ?_, lwv := ?_, les := ?_, lxv := ?_ }
    · rw [hv4 "N" (by decide)]; exact hN3
    · rw [hv4 "M" (by decide)]; exact hM3
    · rw [hv4 "n" (by decide), hv3 "n" (by decide), hv2 "n" (by decide)]; exact hn1
    · rw [hv4 "T" (by decide)]; exact hT3
    · rw [hv4 "Z" (by decide), hv3 "Z" (by decide)]; exact hZ2
    · rw [hv4 "V" (by decide), hv3 "V" (by decide)]; exact hV2
    · rw [hv4 "nn" (by decide)]; exact hnn3
    · rw [ha4 "z" (by decide)]; exact hz3
    · rw [hlen]; exact h0.ldg
    · rw [hlen]; exact h0.lhl
    · rw [hlen]; exact h0.lkd
    · rw [hlen]; exact h0.lrk
    · rw [hlen]; exact h0.lsg
    · rw [hlen]; exact h0.lS
    · rw [hlen]; exact h0.lwv
    · rw [hlen]; exact h0.les
    · rw [hlen]; exact h0.lxv

end

end Lax117284Proofs.Machine.Ilp
