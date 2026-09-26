import Lax117284Proofs.Machine.IlpEval

/-!
The odometer: add one to the number whose base-`R` digits are in `dg`.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

theorem odoBody_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => Ctx n cnt bb σ ∧ σ.vars "q" < Dn n ∧ σ.vars "cy" ≤ 1 ∧
        (σ.arrs "dg").getD (σ.vars "q") 0 < Rd n)
      odoBody
      (fun σ σ' => σ'.vars "q" = σ.vars "q" + 1 ∧
        σ'.vars "cy" = ((σ.arrs "dg").getD (σ.vars "q") 0 + σ.vars "cy") / Rd n ∧
        σ'.arrs "dg" = (σ.arrs "dg").set (σ.vars "q")
          (((σ.arrs "dg").getD (σ.vars "q") 0 + σ.vars "cy") -
            ((σ.arrs "dg").getD (σ.vars "q") 0 + σ.vars "cy") / Rd n * Rd n)) 40 := by
  run_vcg
  all_goals
    have hC : Ctx n cnt bb σ := ‹Ctx n cnt bb σ›
    have hq : σ.vars "q" < Dn n := ‹σ.vars "q" < Dn n›
    have hcy : σ.vars "cy" ≤ 1 := ‹σ.vars "cy" ≤ 1›
    have hd : (σ.arrs "dg").getD (σ.vars "q") 0 < Rd n := ‹(σ.arrs "dg").getD (σ.vars "q") 0 < Rd n›
    have hR := hC.hR
    have hldg := hC.ldg
    have hBR := hb.Rd_lt
    have hBD := hb.Dn_lt
    have hB5 := hb.five_lt_B
    have hdiv : ((σ.arrs "dg").getD (σ.vars "q") 0 + σ.vars "cy") / σ.vars "R" ≤ 1 := by
      apply Nat.div_le_of_le_mul
      omega
    have hprod := mul_le_of_le_one_left'
      (((σ.arrs "dg").getD (σ.vars "q") 0 + σ.vars "cy") / σ.vars "R") (σ.vars "R") hdiv
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | (refine ⟨trivial, ?_⟩; rw [hR]; exact ⟨rfl, rfl⟩))

theorem encR_top (R : ℕ) (f : ℕ → ℕ) (k : ℕ) : encR R f (k + 1) = encR R f k + f k * R ^ k := by
  unfold encR; rw [Finset.sum_range_succ]

theorem encR_congr' (R : ℕ) {f g : ℕ → ℕ} {k : ℕ} (h : ∀ q < k, f q = g q) :
    encR R f k = encR R g k := by
  unfold encR
  exact Finset.sum_congr rfl fun q hq => by rw [h q (Finset.mem_range.mp hq)]

theorem odo_arith (S F c fk X R cy' v : ℕ) (hS : S + c * X = F + 1) (hv : v = fk + c)
    (hcy : cy' * R ≤ v) : S + (v - cy' * R) * X + cy' * (X * R) = F + fk * X + 1 := by
  have h1 : (v - cy' * R) * X + cy' * R * X = v * X := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hcy]
  have h2 : cy' * (X * R) = cy' * R * X := by ring
  rw [h2]
  have h3 : v * X = fk * X + c * X := by rw [hv]; ring
  omega

theorem encR_digitsOf {R : ℕ} (hR : 0 < R) :
    ∀ (D t : ℕ), t < R ^ D → encR R (digitsOf R t) D = t := by
  intro D
  induction D with
  | zero => intro t ht; simp at ht; simp [encR, ht]
  | succ D ih =>
    intro t ht
    rw [encR_succ']
    have h1 : t / R < R ^ D := by
      rw [pow_succ'] at ht
      exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; simpa [mul_comm] using ht)
    have h2 : encR R (fun q => digitsOf R t (q + 1)) D = encR R (digitsOf R (t / R)) D := by
      refine encR_congr' R fun q _ => ?_
      unfold digitsOf
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
    rw [h2, ih _ h1]
    unfold digitsOf
    simp only [pow_zero, Nat.div_one]
    exact Nat.mod_add_div t R

/-- **The odometer**: the digits of `t` become the digits of `t + 1`, the carry is `1` exactly when
`t + 1` is the number of vectors. -/
theorem odoCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (t : ℕ)
    (ht : t < Rd n ^ Dn n) :
    Spec B (fun σ => Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) t))
      odoCom
      (fun _ σ' => Ctx n cnt bb σ' ∧ σ'.vars "cy" = (if t + 1 = Rd n ^ Dn n then 1 else 0) ∧
        σ'.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) ((t + 1) % Rd n ^ Dn n)))
      (2 + ((40 + 4) * Dn n + 6)) := by
  have hR : 0 < Rd n := by unfold Rd; omega
  set f := digitsOf (Rd n) t with hf
  have hfR : ∀ q, f q < Rd n := fun q => digitsOf_lt hR t q
  have hEf : encR (Rd n) f (Dn n) = t := encR_digitsOf hR (Dn n) t ht
  have hs := scan_spec (B := B) "q" "D" (Dn n) 40 odoBody (Ctx n cnt bb)
    (fun k σ => ∃ g, σ.arrs "dg" = arrOf (Dn n) g ∧ σ.vars "cy" ≤ 1 ∧ (∀ r, k ≤ r → g r = f r) ∧
      (∀ r < Dn n, g r < Rd n) ∧
      encR (Rd n) g k + σ.vars "cy" * Rd n ^ k = encR (Rd n) f k + 1)
    (Ctx.stable (by decide) (by decide)) hb.Dn_lt (fun σ h => h.hD) ?_
  · have hA : Spec B (fun σ => Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) f) (asg "cy" (lit 1))
        (fun σ σ' => σ' = σ.setVar "cy" 1) 2 :=
      Spec.pre (assign_lit_spec (B := B) "cy" 1 hb.one_lt_B) (fun _ _ => trivial)
    have hs' : Spec B (fun σ => Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) f ∧ σ.vars "cy" = 1)
        (forZ "q" "D" odoBody)
        (fun _ σ' => Ctx n cnt bb σ' ∧ σ'.vars "cy" = (if t + 1 = Rd n ^ Dn n then 1 else 0) ∧
          σ'.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) ((t + 1) % Rd n ^ Dn n)))
        ((40 + 4) * Dn n + 6) := by
      refine (Spec.pre hs ?_).post ?_
      · rintro σ ⟨hC, hdg, hcy⟩
        refine ⟨hC.setVar (by decide) _, ⟨f, by simpa using hdg, by simp [hcy], fun r _ => rfl,
          fun r _ => hfR r, by simp [hcy, encR]⟩⟩
      · rintro σ σ' - ⟨hC, ⟨g, hg, hcy, hgf, hgR, henc⟩, hq⟩
        refine ⟨hC, ?_⟩
        rw [hEf] at henc
        obtain ⟨hlt, hdig⟩ := digits_encR hR (Dn n) g (fun q hq => hgR q hq)
        have hcyc : σ'.vars "cy" = 0 ∨ σ'.vars "cy" = 1 := by omega
        rcases hcyc with h0 | h1
        · rw [h0] at henc
          have hnc : encR (Rd n) g (Dn n) = t + 1 := by omega
          have hlt' : t + 1 < Rd n ^ Dn n := by rw [← hnc]; exact hlt
          rw [if_neg (by omega), Nat.mod_eq_of_lt hlt', h0]
          refine ⟨rfl, ?_⟩
          rw [hg]
          refine arrOf_congr fun q hq => ?_
          rw [← hnc]; exact (hdig q hq).symm
        · rw [h1] at henc
          have hnc : encR (Rd n) g (Dn n) = 0 := by
            have : Rd n ^ Dn n ≥ t + 1 := ht
            have hh : t + 1 ≤ Rd n ^ Dn n := ht
            omega
          have heq : t + 1 = Rd n ^ Dn n := by
            have := hlt; omega
          rw [if_pos heq, heq, Nat.mod_self, h1]
          refine ⟨rfl, ?_⟩
          rw [hg]
          refine arrOf_congr fun q hq => ?_
          rw [← hdig q hq, hnc]
    unfold odoCom
    refine Spec.mono (Spec.seq hA hs' ?_ ?_) le_rfl
    · intro σ σ1 hσ e
      rw [e]
      exact ⟨hσ.1.setVar (by decide) _, by simpa using hσ.2, by simp⟩
    · intro σ σ1 σ2 hσ e hpost
      exact hpost
  · intro k hk σ ⟨hC, hqk, g, hg, hcy, hgf, hgR, henc⟩
    have hgk : g k = f k := hgf k le_rfl
    have hDl := hC.ldg
    have hd : (σ.arrs "dg").getD (σ.vars "q") 0 = f k := by
      rw [hg, hqk, getD_arrOf_lt hk, hgk]
    obtain ⟨σ', hr, h1, h2, h3⟩ := odoBody_vals hb σ
      ⟨hC, by omega, hcy, by rw [hd]; exact hfR k⟩
    have hv : (σ.arrs "dg").getD (σ.vars "q") 0 + σ.vars "cy" = f k + σ.vars "cy" := by rw [hd]
    have hcy' : σ'.vars "cy" = (f k + σ.vars "cy") / Rd n := by rw [h2, hv]
    have hcy1 : σ'.vars "cy" ≤ 1 := by
      rw [hcy']
      apply Nat.div_le_of_le_mul
      have := hfR k; omega
    have hdm : (σ'.vars "cy") * Rd n ≤ f k + σ.vars "cy" := by
      rw [hcy']; exact Nat.div_mul_le_self _ _
    refine ⟨σ', hr, by omega, ⟨fun r => if r = k then (f k + σ.vars "cy") - σ'.vars "cy" * Rd n else g r,
      ?_, hcy1, ?_, ?_, ?_⟩⟩
    · rw [h3, hd, hqk, hg, set_arrOf, hcy']
    · intro r hr
      have : r ≠ k := by omega
      simp only [this, if_false]; exact hgf r (by omega)
    · intro r hr
      by_cases h : r = k
      · subst h; simp only [if_true]
        have hh := Nat.div_add_mod' (f r + σ.vars "cy") (Rd n)
        have hm := Nat.mod_lt (f r + σ.vars "cy") hR
        rw [hcy']
        have : f r + σ.vars "cy" - (f r + σ.vars "cy") / Rd n * Rd n = (f r + σ.vars "cy") % Rd n := by
          omega
        rw [this]; exact hm
      · simp only [h, if_false]; exact hgR r hr
    · have hc1 : encR (Rd n) (fun r => if r = k then (f k + σ.vars "cy") - σ'.vars "cy" * Rd n else g r) k = encR (Rd n) g k :=
        encR_congr' (Rd n) fun q hq => by simp [Nat.ne_of_lt hq]
      rw [encR_top, encR_top, hc1]
      simp only [if_true]
      have := odo_arith (encR (Rd n) g k) (encR (Rd n) f k) (σ.vars "cy") (f k) (Rd n ^ k) (Rd n)
        (σ'.vars "cy") (f k + σ.vars "cy") henc rfl hdm
      rw [pow_succ]
      exact this

end

end Lax117284Proofs.Machine.Ilp
