import Lax117284Proofs.Treewidth.Fun.E3C2

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E3C

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars CT

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem leKC_runs (kmax : ℕ) (c : CT) (hB : 1 < B) (s : ℕ) (hs : sz c ≤ s) :
    Runs Δ' B fLeKC [toVal kmax, toVal c] (toVal (decide (c.maxEntry ≤ kmax))) (40 * s + 10) := by
  have h1 := maxEntry_runs hΔ B (by omega) c
  refine Runs.mk (hΔ _ _ Δ_leKC) ?_
  by_cases hk : c.maxEntry ≤ kmax
  · have : ¬ kmax < c.maxEntry := by omega
    simp only [hk, decide_true, toVal_true]
    ev_start
    · ev_run
    · omega
  · have : kmax < c.maxEntry := by omega
    simp only [hk, decide_false, toVal_false]
    ev_start
    · ev_run
    · omega

theorem normOf_runs (path : List ℕ) (pl : CT.Plan) (c : CT) (Cn : ℕ)
    (hnorm : Runs Δ' B fNormId [toVal c] (toVal (norm c)) Cn) :
    Runs Δ' B fNormOf [Val.nat 0, toVal (path, pl, c)] (toVal (norm c)) (Cn + 6) := by
  refine Runs.mk (hΔ _ _ Δ_normOf) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

theorem introC_runs (U Q P G Ω Qc Q₀ Cn Sn : ℕ) (Bs : Finset ℕ) (kmax M v : ℕ) (N : Finset ℕ)
    (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (hP : Q * (3 * M) ≤ P)
    (hQc : 1000 * ((U + 1) * Ω) ≤ Qc)
    (hQ₀ : 100 * (P * G) + 4 * (Qc * (U + 1) * G) + 500 * ((U + 1) * G) + 1000 * (U + 1) ≤ Q₀)
    (hv : v ≤ U) (hN : N.card ≤ U)
    (hG : ∀ ν : CT, Good Bs ν → maxEntry ν ≤ kmax → count ν ≤ M →
      (wtopPlans v ν).length + 1 ≤ G ∧ (allChains ν.S N).length + 1 ≤ G ∧
      (attachPlans v N ν).length ≤ G ∧ (introPlans v N ν).length ≤ G)
    (hΩ : ∀ ν : CT, Good Bs ν → (chainCands ν.S N).length + 1 ≤ Ω) (hB : 10 * U + 600 < B)
    (t : CT) (hU : sz t ≤ U) (hM : mx t ≤ U) (hg : Good Bs t) (hm : maxEntry t ≤ kmax) (hc : count t ≤ M)
    (hnorm : ∀ x ∈ introPlans v N t, Runs Δ' B fNormId [toVal x.2.2] (toVal (norm x.2.2)) Cn)
    (hsz : ∀ x ∈ introPlans v N t, sz (norm x.2.2) ≤ Sn) :
    Runs Δ' B fIntroC [toVal kmax, toVal v, toVal N, toVal t] (toVal (introC kmax v N t))
      (Q₀ * (3 * count t - 1) + (G * (Cn + 40 * Sn + 80) + 100)) := by
  have hid := ids_lt (B := B) (by omega)
  have hip := introPlans_runs hΔ B U Q P G Ω Qc Q₀ Bs kmax M v N hQ hP hQc hQ₀ hv hN hG hΩ hB t hU hM hg hm hc
  have hOG := (hG t hg hm hc).2.2.2
  have hmap := map_runs (y1 hΔ) B fNormOf (Val.nat 0) (fun r : List ℕ × CT.Plan × CT => norm r.2.2)
    (fun _ => Cn + 6) (introPlans v N t)
    (fun r hr => by obtain ⟨path, pl, c⟩ := r; exact normOf_runs hΔ B path pl c Cn (hnorm _ hr))
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap
  have hfil := filter_runs (y1 hΔ) B fLeKC (toVal kmax) (fun c : CT => decide (c.maxEntry ≤ kmax))
    (fun _ => 40 * Sn + 10) ((introPlans v N t).map (fun r : List ℕ × CT.Plan × CT => norm r.2.2))
    (fun c hc' => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc'
      exact leKC_runs hΔ B kmax _ (by omega) Sn (hsz r hr))
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map] at hfil
  have hshow : introC kmax v N t =
      ((introPlans v N t).map (fun r : List ℕ × CT.Plan × CT => norm r.2.2)).filter
        (fun c : CT => decide (c.maxEntry ≤ kmax)) := rfl
  rw [hshow]
  refine Runs.mk (hΔ _ _ Δ_introC) ?_
  ev_start
  · ev_run
  · have e1 : (introPlans v N t).length * (Cn + 6) ≤ G * (Cn + 6) := Nat.mul_le_mul_right _ hOG
    have e2 : (introPlans v N t).length * (40 * Sn + 10) ≤ G * (40 * Sn + 10) := Nat.mul_le_mul_right _ hOG
    have e3 : G * (Cn + 40 * Sn + 80) = G * (Cn + 6) + G * (40 * Sn + 10) + 64 * G := by ring
    clear hG hΩ hnorm hsz hmap hfil hip hshow
    omega

end proofs
end E3C
end Lax117284Proofs.Treewidth.Fun
