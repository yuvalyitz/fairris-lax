import Lax117284Proofs.Machine.IlpKdLoop

/-!
The rank pass: the rank of every column among the extras, and the number of extras.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical

theorem rk_succ' (n : ℕ) (d : ℕ → ℕ) (k : ℕ) :
    rk n d (k + 1) = rk n d k + if isExtra n d k then 1 else 0 := by
  unfold rk
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : isExtra n d k
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg h, if_neg h]; simp

theorem card_Ext_eq_rk (n : ℕ) (d : ℕ → ℕ) : (Ext n d).card = rk n d (nN n) := rfl

/-- What one turn of the rank pass stores. -/
theorem rkBody_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => Ctx n cnt bb σ ∧ σ.vars "i" < nN n ∧ σ.vars "E" < nN n ∧
        (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3)
      rkBody
      (fun σ σ' => σ'.vars "i" = σ.vars "i" + 1 ∧
        σ'.arrs "rkA" = (σ.arrs "rkA").set (σ.vars "i") (σ.vars "E") ∧
        σ'.vars "E" = σ.vars "E" + (if (σ.arrs "kd").getD (σ.vars "i") 0 = 2 then 1 else 0)) 40 := by
  run_vcg
  all_goals
    have hctx : Ctx n cnt bb σ := ‹Ctx n cnt bb σ›
    have hlk : (σ.arrs "kd").length = nN n := hctx.lkd
    have hlr : (σ.arrs "rkA").length = nN n := hctx.lrk
    have hBN := hb.nN_lt
    have hB5 := hb.five_lt_B
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | simp_all)

/-- **The rank pass.** -/
theorem rkCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
        ∃ f, σ.arrs "rkA" = arrOf (nN n) f)
      rkCom
      (fun _ σ' => CE n cnt bb v σ' ∧ σ'.arrs "rkA" = arrOf (nN n) (rk n (dd n v)) ∧
        σ'.vars "E" = (Ext n (dd n v)).card) (2 + ((40 + 4) * nN n + 6)) := by
  have hs := scan_spec (B := B) "i" "N" (nN n) 40 rkBody
    (fun σ => CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)))
    (fun k σ => (∃ f, σ.arrs "rkA" = arrOf (nN n) f ∧ ∀ c < k, f c = rk n (dd n v) c) ∧
      σ.vars "E" = rk n (dd n v) k)
    (Stable.and (CE.stable (by decide) (by decide) (by decide))
      (stable_arr "kd" (fun l => l = arrOf (nN n) (kindOf n (dd n v))) (by decide)))
    hb.nN_lt (fun σ h => h.1.1.hN) ?_
  · have hA : Spec B (fun σ => CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
        ∃ f, σ.arrs "rkA" = arrOf (nN n) f) (asg "E" (lit 0)) (fun σ σ' => σ' = σ.setVar "E" 0) 2 :=
      Spec.mono (Spec.assign (fun σ _ => evalB_lit (by have := hb.five_lt_B; omega))) (by simp)
    refine (Spec.seq hA hs ?_ ?_).mono le_rfl
    · rintro σ σ' ⟨hC, hkd, f, hf⟩ rfl
      refine ⟨⟨hC.setVar (by decide) _ |>.setVar (by decide) _, by simpa using hkd⟩,
        ⟨f, by simpa using hf, fun c hc => absurd hc (by omega)⟩, by simp [rk]⟩
    · rintro σ σ' σ'' ⟨hC, hkd, f, hf⟩ rfl ⟨⟨hC', hkd'⟩, ⟨⟨f', hf', hfk⟩, hE⟩, -⟩
      refine ⟨hC', by rw [hf']; exact arrOf_congr hfk, ?_⟩
      rw [hE, card_Ext_eq_rk]
  · intro k hk σ ⟨⟨hC, hkd⟩, hik, ⟨f, hf, hfk⟩, hE⟩
    have hEle : rk n (dd n v) k ≤ k := by
      unfold rk
      calc _ ≤ (Finset.range k).card := Finset.card_filter_le _ _
        _ = k := Finset.card_range k
    have hkd' : (σ.arrs "kd").getD (σ.vars "i") 0 = kindOf n (dd n v) k := by
      rw [hkd, hik]; exact getD_arrOf_lt hk
    have hkd3 : (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 := by
      rw [hkd']
      unfold kindOf; split_ifs <;> omega
    obtain ⟨σ', hr, h1, h2, h3⟩ := rkBody_vals hb σ ⟨hC.1, by omega, by omega, hkd3⟩
    refine ⟨σ', hr, by omega, ⟨fun j => if j = k then rk n (dd n v) k else f j, ?_, ?_⟩, ?_⟩
    · rw [h2, hf, hik, hE, set_arrOf]
    · intro c hc
      by_cases h : c = k
      · simp [h]
      · simp only [h, if_false]; exact hfk c (by omega)
    · rw [h3, hE, rk_succ', hkd']
      simp only [kindOf_eq_two]

end Lax117284Proofs.Machine.Ilp
