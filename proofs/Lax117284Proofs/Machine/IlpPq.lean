import Lax117284Proofs.Machine.IlpS2

/-!
The sums `P` and `Q` of a row of `H`.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section


/-- Facts about the current entry of `H` and the current row. -/
theorem pqFacts {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) {σ : Env} (hC : CE n cnt bb v σ) (hr : σ.vars "r" < n)
    (hj : σ.vars "j" < n) :
    σ.vars "N" + σ.vars "r" * σ.vars "n" + σ.vars "j" = hpIdx n (σ.vars "r") (σ.vars "j") ∧
    σ.vars "N" + σ.vars "nn" + σ.vars "r" * σ.vars "n" + σ.vars "j" =
      hnIdx n (σ.vars "r") (σ.vars "j") ∧
    (σ.arrs "dg").getD (hpIdx n (σ.vars "r") (σ.vars "j")) 0 ≤ Kn n ∧
    (σ.arrs "dg").getD (hnIdx n (σ.vars "r") (σ.vars "j")) 0 ≤ Kn n ∧
    hpIdx n (σ.vars "r") (σ.vars "j") < (σ.arrs "dg").length ∧
    hnIdx n (σ.vars "r") (σ.vars "j") < (σ.arrs "dg").length ∧
    σ.vars "r" * σ.vars "n" < B := by
  have hNv := hC.1.hN
  have hnv := hC.1.hn
  have hnnv := hC.1.hnn
  have hp := hpIdx_lt hr hj
  have hh := hnIdx_lt hr hj
  have hD : nN n + 2 * (n * n) < Dn n := by unfold Dn; omega
  have hDl := hC.1.ldg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hNv, hnv]; unfold hpIdx; ring
  · rw [hNv, hnv, hnnv]; unfold hnIdx; ring
  · rw [hC.2, getD_arrOf_lt (by omega)]; exact hv _ (by omega)
  · rw [hC.2, getD_arrOf_lt (by omega)]; exact hv _ (by omega)
  · omega
  · omega
  · rw [hnv]
    have : σ.vars "r" * n ≤ n * n := Nat.mul_le_mul_right _ hr.le
    have := hb.nn_lt
    omega

theorem pqBody_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "r" < n ∧ σ.vars "j" < n ∧
        (σ.arrs "S").getD (σ.vars "j") 0 ≤ nN n * (Kn n + vb) ∧
        σ.vars "P" + Pterm n vb ≤ Pbd n vb ∧ σ.vars "Q" + Pterm n vb ≤ Pbd n vb)
      pqInner
      (fun σ σ' => σ'.vars "j" = σ.vars "j" + 1 ∧
        σ'.vars "P" = σ.vars "P" +
          ((σ.arrs "dg").getD (hpIdx n (σ.vars "r") (σ.vars "j")) 0 * bb +
            (σ.arrs "dg").getD (hnIdx n (σ.vars "r") (σ.vars "j")) 0 * (σ.arrs "S").getD (σ.vars "j") 0) ∧
        σ'.vars "Q" = σ.vars "Q" +
          ((σ.arrs "dg").getD (hpIdx n (σ.vars "r") (σ.vars "j")) 0 * (σ.arrs "S").getD (σ.vars "j") 0 +
            (σ.arrs "dg").getD (hnIdx n (σ.vars "r") (σ.vars "j")) 0 * bb)) 80 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hr : σ.vars "r" < n := ‹σ.vars "r" < n›
    have hj : σ.vars "j" < n := ‹σ.vars "j" < n›
    have hSj : (σ.arrs "S").getD (σ.vars "j") 0 ≤ nN n * (Kn n + vb) :=
      ‹(σ.arrs "S").getD (σ.vars "j") 0 ≤ nN n * (Kn n + vb)›
    have hPb : σ.vars "P" + Pterm n vb ≤ Pbd n vb := ‹σ.vars "P" + Pterm n vb ≤ Pbd n vb›
    have hQb : σ.vars "Q" + Pterm n vb ≤ Pbd n vb := ‹σ.vars "Q" + Pterm n vb ≤ Pbd n vb›
    obtain ⟨e1, e2, hpv, hnv, hlp, hln, hrn⟩ := pqFacts hb v hv hC hr hj
    have hbbv := hC.1.hbb
    have hpv' : (σ.arrs "dg").getD (σ.vars "N" + σ.vars "r" * σ.vars "n" + σ.vars "j") 0 ≤ Kn n := by
      rw [e1]; exact hpv
    have hnv' : (σ.arrs "dg").getD (σ.vars "N" + σ.vars "nn" + σ.vars "r" * σ.vars "n" + σ.vars "j") 0 ≤ Kn n := by
      rw [e2]; exact hnv
    have hbb' : σ.vars "bb" ≤ vb := by have := hb.hbb; omega
    have hprod1 := Nat.mul_le_mul hpv' hbb'
    have hprod2 := Nat.mul_le_mul hnv' hSj
    have hprod3 := Nat.mul_le_mul hpv' hSj
    have hprod4 := Nat.mul_le_mul hnv' hbb'
    have hPT : Pterm n vb ≤ Pbd n vb := by
      unfold Pbd; exact Nat.le_mul_of_pos_left _ hb.n1
    have hPterm : Kn n * vb + Kn n * (nN n * (Kn n + vb)) = Pterm n vb := rfl
    have hlS : (σ.arrs "S").length = n := hC.1.lS
    have hBP := hb.Pbd_lt
    have hBD := hb.Dn_lt
    have hBS := hb.SB_lt
    have hDl := hC.1.ldg
    have hBtn := hb.tn_lt
    have hBn := hb.n_lt
    have hBN := hb.nN_lt
    have hBnn := hb.nn_lt
    have hBK := hb.Kn_lt
    have hB5 := hb.five_lt_B
    have hNv := hC.1.hN
    have hnnv := hC.1.hnn
    have hD : nN n + 2 * (n * n) < Dn n := by unfold Dn; omega
    have hnv' := hC.1.hn
    have hbbB : bb < B := hb.lt_U (by have := hb.hbb; unfold Ub; omega)
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | (refine ⟨trivial, ?_, ?_⟩ <;> rw [hbbv, ← e1, ← e2]))

/-- The sum `P` of a row. -/
def pSum (n : ℕ) (v : ℕ → ℕ) (bb : ℕ) (Sf : ℕ → ℕ) (r k : ℕ) : ℕ :=
  ∑ j ∈ range k, (v (hpIdx n r j) * bb + v (hnIdx n r j) * Sf j)

/-- The sum `Q` of a row. -/
def qSum (n : ℕ) (v : ℕ → ℕ) (bb : ℕ) (Sf : ℕ → ℕ) (r k : ℕ) : ℕ :=
  ∑ j ∈ range k, (v (hpIdx n r j) * Sf j + v (hnIdx n r j) * bb)

theorem pSum_succ (n : ℕ) (v : ℕ → ℕ) (bb : ℕ) (Sf : ℕ → ℕ) (r k : ℕ) :
    pSum n v bb Sf r (k + 1) = pSum n v bb Sf r k + (v (hpIdx n r k) * bb + v (hnIdx n r k) * Sf k) := by
  unfold pSum; rw [Finset.sum_range_succ]

theorem qSum_succ (n : ℕ) (v : ℕ → ℕ) (bb : ℕ) (Sf : ℕ → ℕ) (r k : ℕ) :
    qSum n v bb Sf r (k + 1) = qSum n v bb Sf r k + (v (hpIdx n r k) * Sf k + v (hnIdx n r k) * bb) := by
  unfold qSum; rw [Finset.sum_range_succ]

theorem pq_term_le {n vb : ℕ} {bb : ℕ} (hbb : bb ≤ vb) (v : ℕ → ℕ) (hv : ∀ q < Dn n, v q ≤ Kn n)
    (Sf : ℕ → ℕ) (j : ℕ) (hS : Sf j ≤ nN n * (Kn n + vb)) (r : ℕ) (hr : r < n) (hj : j < n) :
    v (hpIdx n r j) * bb + v (hnIdx n r j) * Sf j ≤ Pterm n vb ∧
    v (hpIdx n r j) * Sf j + v (hnIdx n r j) * bb ≤ Pterm n vb := by
  have hp := hpIdx_lt hr hj
  have hh := hnIdx_lt hr hj
  have hp' : v (hpIdx n r j) ≤ Kn n := hv _ (by unfold Dn; omega)
  have hn' : v (hnIdx n r j) ≤ Kn n := hv _ (by unfold Dn; omega)
  have h1 := Nat.mul_le_mul hp' hbb
  have h2 := Nat.mul_le_mul hn' hS
  have h3 := Nat.mul_le_mul hp' hS
  have h4 := Nat.mul_le_mul hn' hbb
  unfold Pterm
  constructor <;> omega

theorem pSum_le {n vb : ℕ} {bb : ℕ} (hbb : bb ≤ vb) (v : ℕ → ℕ) (hv : ∀ q < Dn n, v q ≤ Kn n)
    (Sf : ℕ → ℕ) (hS : ∀ j < n, Sf j ≤ nN n * (Kn n + vb)) (r : ℕ) (hr : r < n) (k : ℕ) (hk : k ≤ n) :
    pSum n v bb Sf r k ≤ k * Pterm n vb ∧ qSum n v bb Sf r k ≤ k * Pterm n vb := by
  induction k with
  | zero => simp [pSum, qSum]
  | succ k ih =>
    rw [pSum_succ, qSum_succ]
    have := pq_term_le hbb v hv Sf k (hS k (by omega)) r hr (by omega)
    have ih' := ih (by omega)
    constructor <;> nlinarith [ih'.1, ih'.2]

/-- **The sums `P` and `Q` of a row.** -/
theorem pqCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) (Sf : ℕ → ℕ) (hSf : ∀ j < n, Sf j ≤ nN n * (Kn n + vb))
    (r : ℕ) (hr : r < n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "r" = r ∧ σ.arrs "S" = arrOf n Sf)
      pqCom (fun _ σ' => CE n cnt bb v σ' ∧ σ'.vars "r" = r ∧ σ'.arrs "S" = arrOf n Sf ∧
        σ'.vars "P" = pSum n v bb Sf r n ∧ σ'.vars "Q" = qSum n v bb Sf r n)
      (2 + 2 + ((80 + 4) * n + 6)) := by
  have hs := scan_spec (B := B) "j" "n" n 80 pqInner
    (fun σ => CE n cnt bb v σ ∧ σ.vars "r" = r ∧ σ.arrs "S" = arrOf n Sf)
    (fun k σ => σ.vars "P" = pSum n v bb Sf r k ∧ σ.vars "Q" = qSum n v bb Sf r k)
    (Stable.and (CE.stable (by decide) (by decide) (by decide))
      (Stable.and (stable_var "r" (fun x => x = r) (by decide))
        (stable_arr "S" (fun l => l = arrOf n Sf) (by decide))))
    hb.n_lt (fun σ h => h.1.1.hn) ?_
  · have hA : Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "r" = r ∧ σ.arrs "S" = arrOf n Sf)
        (asg "P" (lit 0)) (fun σ σ' => σ' = σ.setVar "P" 0) 2 :=
      Spec.pre (assign_lit_spec (B := B) "P" 0 (by have := hb.five_lt_B; omega)) (fun _ _ => trivial)
    have hA' : Spec B (fun σ => (CE n cnt bb v σ ∧ σ.vars "r" = r ∧ σ.arrs "S" = arrOf n Sf) ∧
        σ.vars "P" = 0)
        (asg "Q" (lit 0)) (fun σ σ' => σ' = σ.setVar "Q" 0) 2 :=
      Spec.pre (assign_lit_spec (B := B) "Q" 0 (by have := hb.five_lt_B; omega)) (fun _ _ => trivial)
    have h2 : Spec B (fun σ => (CE n cnt bb v σ ∧ σ.vars "r" = r ∧ σ.arrs "S" = arrOf n Sf) ∧
        σ.vars "P" = 0)
        (.seq (asg "Q" (lit 0)) (forZ "j" "n" pqInner))
        (fun _ σ' => CE n cnt bb v σ' ∧ σ'.vars "r" = r ∧ σ'.arrs "S" = arrOf n Sf ∧
          σ'.vars "P" = pSum n v bb Sf r n ∧ σ'.vars "Q" = qSum n v bb Sf r n)
        (2 + ((80 + 4) * n + 6)) := by
      refine Spec.seq hA' hs ?_ ?_
      · intro σ σ1 hσ e
        rw [e]
        obtain ⟨⟨hC, hr', hS⟩, hP0⟩ := hσ
        refine ⟨⟨(hC.setVar (by decide) _).setVar (by decide) _, by simpa using hr',
          by simpa using hS⟩, ?_⟩
        simp [pSum, qSum, hP0]
      · intro σ σ1 σ2 hσ e hpost
        exact ⟨hpost.1.1, hpost.1.2.1, hpost.1.2.2, hpost.2.1.1, hpost.2.1.2⟩
    have h1 : Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "r" = r ∧ σ.arrs "S" = arrOf n Sf)
        (.seq (asg "P" (lit 0)) (.seq (asg "Q" (lit 0)) (forZ "j" "n" pqInner)))
        (fun _ σ' => CE n cnt bb v σ' ∧ σ'.vars "r" = r ∧ σ'.arrs "S" = arrOf n Sf ∧
          σ'.vars "P" = pSum n v bb Sf r n ∧ σ'.vars "Q" = qSum n v bb Sf r n)
        (2 + (2 + ((80 + 4) * n + 6))) := by
      refine Spec.seq hA h2 ?_ ?_
      · intro σ σ1 hσ e
        rw [e]
        obtain ⟨hC, hr', hS⟩ := hσ
        exact ⟨⟨hC.setVar (by decide) _, by simpa using hr', by simpa using hS⟩, by simp⟩
      · intro σ σ1 σ2 hσ e hpost
        exact hpost
    unfold pqCom
    exact Spec.mono h1 (by omega)
  · intro k hk σ ⟨⟨hC, hr', hS⟩, hjk, hP, hQ⟩
    have hkn : k < n := hk
    have hcnt : ((σ.arrs "S").getD (σ.vars "j") 0) = Sf k := by
      rw [hS, hjk, getD_arrOf_lt hk]
    have hPQ := pSum_le (hb.hbb : bb ≤ vb) v hv Sf hSf r hr k hk.le
    have hPT : (k + 1) * Pterm n vb ≤ Pbd n vb := by unfold Pbd; exact Nat.mul_le_mul_right _ hk
    obtain ⟨σ', hrun, h1, h2, h3⟩ := pqBody_vals hb v hv σ
      ⟨hC, by rw [hr']; exact hr, by omega, by rw [hcnt]; exact hSf k hk, by
        rw [hP]; nlinarith [hPQ.1], by rw [hQ]; nlinarith [hPQ.2]⟩
    refine ⟨σ', hrun, by omega, ?_, ?_⟩
    · rw [h2, hP, pSum_succ, hcnt, hr', hjk, hC.2, getD_arrOf_lt (by have := hpIdx_lt hr hk; unfold Dn; omega),
        getD_arrOf_lt (by have := hnIdx_lt hr hk; unfold Dn; omega)]
    · rw [h3, hQ, qSum_succ, hcnt, hr', hjk, hC.2, getD_arrOf_lt (by have := hpIdx_lt hr hk; unfold Dn; omega),
        getD_arrOf_lt (by have := hnIdx_lt hr hk; unfold Dn; omega)]

theorem certVec_Hp {n : ℕ} (v : ℕ → ℕ) {r j : ℕ} (hr : r < n) (hj : j < n) :
    (certVec n v).Hp r j = v (hpIdx n r j) := by simp [certVec, hr, hj]

theorem certVec_Hn {n : ℕ} (v : ℕ → ℕ) {r j : ℕ} (hr : r < n) (hj : j < n) :
    (certVec n v).Hn r j = v (hnIdx n r j) := by simp [certVec, hr, hj]

theorem pSum_eq_Pi (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (v : ℕ → ℕ) (r : ℕ) (hr : r < n) :
    pSum n v bb (fun j => Sj n cnt (dd n v) j) r n = Pi n cnt bb (certVec n v) r := by
  unfold pSum Pi
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [certVec_Hp v hr hj', certVec_Hn v hr hj']

theorem qSum_eq_Qi (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (v : ℕ → ℕ) (r : ℕ) (hr : r < n) :
    qSum n v bb (fun j => Sj n cnt (dd n v) j) r n = Qi n cnt bb (certVec n v) r := by
  unfold qSum Qi
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [certVec_Hp v hr hj', certVec_Hn v hr hj']

end

end Lax117284Proofs.Machine.Ilp
