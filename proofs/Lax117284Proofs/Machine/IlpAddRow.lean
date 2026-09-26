import Lax117284Proofs.Machine.IlpSg

/-!
Adding a multiple of a column of the client rows to the vector `S`.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical

theorem mul_le_of_le_one' (a c : ℕ) (h : c ≤ 1) : a * c ≤ a := by
  calc a * c ≤ a * 1 := Nat.mul_le_mul_left a h
    _ = a := mul_one a

/-- The coefficient of client `j` of the column `i`, as the machine reads it. -/
theorem z_client_coef {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {σ : Env} (hC : Ctx n cnt bb σ) {j c : ℕ}
    (hj : j < n) (hc : c < nN n) :
    (σ.arrs "z").getD (σ.vars "tn" + j * σ.vars "N" + c) 0 = coef n (nT n + j) c := by
  rw [hC.hz, hC.htn, hC.hN]
  have : 2 + nT n * nN n + j * nN n + c = 2 + (nT n + j) * nN n + c := by ring
  rw [this]
  exact ilpWord_coef n cnt bb (by unfold nM; omega) hc

theorem addRowBody_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nN n ∧ σ.vars "j" < n ∧
        σ.vars "mv" + (σ.arrs "S").getD (σ.vars "j") 0 < B)
      addRowBody
      (fun σ σ' => σ'.vars "j" = σ.vars "j" + 1 ∧
        σ'.arrs "S" = (σ.arrs "S").set (σ.vars "j")
          ((σ.arrs "S").getD (σ.vars "j") 0 + σ.vars "mv" * coef n (nT n + σ.vars "j") (σ.vars "i")))
      30 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nN n := ‹σ.vars "i" < nN n›
    have hj : σ.vars "j" < n := ‹σ.vars "j" < n›
    have hmS : σ.vars "mv" + (σ.arrs "S").getD (σ.vars "j") 0 < B :=
      ‹σ.vars "mv" + (σ.arrs "S").getD (σ.vars "j") 0 < B›
    have hzc := z_client_coef hC.1 hj hi
    have hcf := coef_le_one n (nT n + σ.vars "j") (σ.vars "i")
    have hprod := mul_le_of_le_one' (σ.vars "mv") ((σ.arrs "z").getD
      (σ.vars "tn" + σ.vars "j" * σ.vars "N" + σ.vars "i") 0) (by rw [hzc]; exact hcf)
    have hidx : σ.vars "tn" + σ.vars "j" * σ.vars "N" + σ.vars "i" < zLen n := by
      rw [hC.1.htn, hC.1.hN]
      have h1 : 2 + (nT n + σ.vars "j") * nN n + σ.vars "i" < 2 + nM n * nN n :=
        idx_lt_zLen (by unfold nM; omega) hi
      have h2 : 2 + nT n * nN n + σ.vars "j" * nN n + σ.vars "i" =
          2 + (nT n + σ.vars "j") * nN n + σ.vars "i" := by ring
      have := rb_le_zLen n
      omega
    have hlz : (σ.arrs "z").length = zLen n := by rw [hC.1.hz, ilpWord_length]
    have hlS : (σ.arrs "S").length = n := hC.1.lS
    have htnv := hC.1.htn
    have hNv := hC.1.hN
    have hBn := hb.n_lt
    have hB5 := hb.five_lt_B
    have hBN := hb.nN_lt
    have hBz := hb.zLen_lt
    have hBtn := hb.tn_lt
    have hjN : σ.vars "j" * σ.vars "N" < B := by
      rw [hC.1.hN]
      have : σ.vars "j" * nN n ≤ (n - 1) * nN n := Nat.mul_le_mul_right _ (by omega)
      have h3 : (n - 1) * nN n ≤ nT n * nN n := Nat.mul_le_mul_right _ (by
        have := nn_le_nT n; have : n ≤ n * n := Nat.le_mul_self n; omega)
      have := hb.tn_lt
      omega
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | (refine ⟨trivial, ?_⟩; rw [hzc]))

/-- **The row loop**: `S[j] += m * coef (T + j) c` for every client `j`. -/
theorem addRow_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (c m : ℕ) (hc : c < nN n) (S0 : ℕ → ℕ) (hS0 : ∀ j < n, m + S0 j < B) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" = c ∧ σ.vars "mv" = m ∧
        σ.arrs "S" = arrOf n S0)
      addRow
      (fun _ σ' => CE n cnt bb v σ' ∧ σ'.vars "i" = c ∧ σ'.vars "mv" = m ∧
        σ'.arrs "S" = arrOf n (fun j => S0 j + m * coef n (nT n + j) c))
      ((30 + 4) * n + 6) := by
  have hs := scan_spec (B := B) "j" "n" n 30 addRowBody
    (fun σ => CE n cnt bb v σ ∧ σ.vars "i" = c ∧ σ.vars "mv" = m)
    (fun k σ => σ.arrs "S" = arrOf n (fun j => S0 j + if j < k then m * coef n (nT n + j) c else 0))
    (Stable.and (CE.stable (by decide) (by decide) (by decide))
      (Stable.and (stable_var "i" (fun x => x = c) (by decide))
        (stable_var "mv" (fun x => x = m) (by decide))))
    hb.n_lt (fun σ h => h.1.1.hn) ?_
  · refine (Spec.pre hs ?_).post ?_
    · rintro σ ⟨hC, hi, hm, hS⟩
      refine ⟨⟨hC.setVar (by decide) _, by simpa using hi, by simpa using hm⟩, ?_⟩
      simpa using hS
    · rintro σ σ' - ⟨⟨hC, hi, hm⟩, hS, -⟩
      refine ⟨hC, hi, hm, ?_⟩
      rw [hS]
      exact arrOf_congr fun j hj => by simp [hj]
  · intro k hk σ ⟨⟨hC, hi, hm⟩, hjk, hS⟩
    have hSk : (σ.arrs "S").getD (σ.vars "j") 0 = S0 k := by
      rw [hS, hjk, getD_arrOf_lt hk]; simp
    obtain ⟨σ', hr, h1, h2⟩ := addRowBody_vals hb v σ
      ⟨hC, by omega, by omega, by rw [hSk, hm]; exact hS0 k hk⟩
    refine ⟨σ', hr, by omega, ?_⟩
    rw [h2, hSk, hS, hi, hm, hjk, set_arrOf]
    refine arrOf_congr fun j _ => ?_
    by_cases h : j = k
    · subst h; simp
    · rw [if_neg h]
      have : (j < k + 1) ↔ (j < k) := by omega
      simp only [this]

end Lax117284Proofs.Machine.Ilp
