import Lax117284Proofs.Treewidth.Fun.E3C1

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E3C

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars CT

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

mutual
theorem introPlans_runs_rec (U Q P G Ω Qc Q₀ : ℕ) (Bs : Finset ℕ) (kmax M v : ℕ) (N : Finset ℕ)
    (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (hP : Q * (3 * M) ≤ P)
    (hQc : 1000 * ((U + 1) * Ω) ≤ Qc)
    (hQ₀ : 100 * (P * G) + 4 * (Qc * (U + 1) * G) + 500 * ((U + 1) * G) + 1000 * (U + 1) ≤ Q₀)
    (hv : v ≤ U) (hN : N.card ≤ U)
    (hG : ∀ ν : CT, Good Bs ν → maxEntry ν ≤ kmax → count ν ≤ M →
      (wtopPlans v ν).length + 1 ≤ G ∧ (allChains ν.S N).length + 1 ≤ G ∧
      (attachPlans v N ν).length ≤ G ∧ (introPlans v N ν).length ≤ G)
    (hΩ : ∀ ν : CT, Good Bs ν → (chainCands ν.S N).length + 1 ≤ Ω) (hB : 10 * U + 600 < B) :
    ∀ (t : CT), sz t ≤ U → mx t ≤ U → Good Bs t → maxEntry t ≤ kmax → count t ≤ M →
      Runs Δ' B fIntroPlans [toVal v, toVal N, toVal t] (toVal (introPlans v N t)) (Q₀ * (3 * count t - 1))
  | CT.node S y ks, hU, hM, hg, hm, hc => by
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
    have hu1 : 1000 ≤ 1000 * (U + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos U)
    have hQ₀1 : 1000 ≤ Q₀ := le_trans hu1 (le_trans (Nat.le_add_left _ _) hQ₀)
    have hid := ids_lt (B := B) (by omega)
    have hid' := E3B.ids_lt (B := B) (by omega)
    have hid'' := E3A.ids_lt (B := B) (by omega)
    obtain ⟨hgk, hmk⟩ := kids_good hg hm
    have hcnt : count (CT.node S y ks) = 1 + countL ks := rfl
    have hG' := hG (CT.node S y ks) hg hm hc
    have hΩ' : (chainCands S N).length + 1 ≤ Ω := hΩ _ hg
    have hkids : ∀ k ∈ ks, sz k ≤ U ∧ mx k ≤ U ∧ Good Bs k ∧ maxEntry k ≤ kmax ∧ count k ≤ M :=
      fun k hk => ⟨le_trans (sz_le_of_mem hk) (by omega), le_trans (mx_le_of_mem hk) (by omega), hgk k hk, hmk k hk,
        le_trans (count_le_countL_of_mem hk) (by omega)⟩
    have hrec := introKids_runs_rec U Q P G Ω Qc Q₀ Bs kmax M v N hQ hP hQc hQ₀ hv hN hG hΩ hB ks [] S y hkids
      (by simp only [List.length_nil, Nat.zero_add]; exact le_trans (length_le_sz ks) (by omega))
    have hPt : Q * (3 * count (CT.node S y ks) - 1) ≤ P :=
      le_trans (Nat.mul_le_mul_left _ (by omega)) hP
    have hwt := E3B.wtopPlans_runs (xB hΔ) B U Q hQ P v S y ks hU hM hv (by omega) hPt
    have hfil := filter_runs (y1 hΔ) B fSubN (toVal N)
      (fun p : CT.Plan × CT × Finset ℕ => decide (N ⊆ p.2.2))
      (fun p => 60 * (N.card + p.2.2.card) + 30) (wtopPlans v (CT.node S y ks))
      (fun p _ => by obtain ⟨pl, c, s⟩ := p; exact subN_runs hΔ B N pl c s (by omega))
    have hsum := sum_map_le (fun p : CT.Plan × CT × Finset ℕ => 60 * (N.card + p.2.2.card) + 30) (120 * U + 30)
      (wtopPlans v (CT.node S y ks))
      (fun p hp => by
        have h1 := Finset.card_le_card (wtopPlans_sub v S y ks p hp)
        have h2 := card_verts_le_sz (CT.node S y ks)
        show 60 * (N.card + p.2.2.card) + 30 ≤ 120 * U + 30
        omega)
    have hmap1 := map_runs (y1 hΔ) B fMk1 (Val.nat 0)
      (fun p : CT.Plan × CT × Finset ℕ => ((([] : List ℕ), p.1, p.2.1) : List ℕ × CT.Plan × CT)) (fun _ => 8)
      ((wtopPlans v (CT.node S y ks)).filter (fun p : CT.Plan × CT × Finset ℕ => decide (N ⊆ p.2.2)))
      (fun p _ => by obtain ⟨pl, c, s⟩ := p; exact mk1_runs hΔ B pl c s (by omega))
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap1
    have hlenF : ((wtopPlans v (CT.node S y ks)).filter (fun p : CT.Plan × CT × Finset ℕ => decide (N ⊆ p.2.2))).length ≤
        (wtopPlans v (CT.node S y ks)).length := List.length_filter_le _ _
    have hsubS := Lib3.subset_runs (y3 hΔ) B (by omega) N S (decide (N ⊆ S)) (by simp)
    have hshow : introPlans v N (CT.node S y ks) =
        ((wtopPlans v (CT.node S y ks)).filter (fun p : CT.Plan × CT × Finset ℕ => decide (N ⊆ p.2.2))).map
          (fun p : CT.Plan × CT × Finset ℕ => ((([] : List ℕ), p.1, p.2.1) : List ℕ × CT.Plan × CT)) ++
        (if N ⊆ S then (attachPlans v N (CT.node S y ks)).map
          (fun p : CT.Plan × CT => ((([] : List ℕ), p.1, p.2) : List ℕ × CT.Plan × CT)) else []) ++
        introKids v N S y [] ks := rfl
    by_cases hNS : N ⊆ S
    · have hQc' : 1000 * ((U + 1) * ((chainCands S N).length + 1)) ≤ Qc :=
        le_trans (Nat.mul_le_mul_left 1000 (Nat.mul_le_mul_left _ hΩ')) hQc
      have hatt := E3B.attachPlans_runs (xB hΔ) B U Qc v N S y ks hNS hU hM hv hQc' (by omega)
      have hmap2 := map_runs (y1 hΔ) B fMk2 (Val.nat 0)
        (fun p : CT.Plan × CT => ((([] : List ℕ), p.1, p.2) : List ℕ × CT.Plan × CT)) (fun _ => 7)
        (attachPlans v N (CT.node S y ks))
        (fun p _ => by obtain ⟨pl, c⟩ := p; exact mk2_runs hΔ B pl c (by omega))
      simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap2
      have ha1 := append_runs (y1 hΔ) B
        (((wtopPlans v (CT.node S y ks)).filter (fun p : CT.Plan × CT × Finset ℕ => decide (N ⊆ p.2.2))).map
          (fun p : CT.Plan × CT × Finset ℕ => ((([] : List ℕ), p.1, p.2.1) : List ℕ × CT.Plan × CT)))
        ((attachPlans v N (CT.node S y ks)).map
          (fun p : CT.Plan × CT => ((([] : List ℕ), p.1, p.2) : List ℕ × CT.Plan × CT)))
      have ha2 := append_runs (y1 hΔ) B
        (((wtopPlans v (CT.node S y ks)).filter (fun p : CT.Plan × CT × Finset ℕ => decide (N ⊆ p.2.2))).map
          (fun p : CT.Plan × CT × Finset ℕ => ((([] : List ℕ), p.1, p.2.1) : List ℕ × CT.Plan × CT)) ++
        (attachPlans v N (CT.node S y ks)).map
          (fun p : CT.Plan × CT => ((([] : List ℕ), p.1, p.2) : List ℕ × CT.Plan × CT)))
        (introKids v N S y [] ks)
      rw [hshow, if_pos hNS]
      refine Runs.mk (hΔ _ _ Δ_introPlans) ?_
      simp only [hNS, decide_true] at hsubS
      simp only [toVal_ct, toVal_nil] at hrec hwt hatt ⊢
      ev_start
      · ev_run
      · simp only [List.length_append, List.length_map]
        obtain ⟨hG1, hG2, hG3, hG4⟩ := hG'
        have hLw : (wtopPlans v (CT.node S y ks)).length ≤ G := by omega
        have e1 : P * ((wtopPlans v (CT.node S y ks)).length + 1) ≤ P * G := Nat.mul_le_mul_left _ hG1
        have e2 : (wtopPlans v (CT.node S y ks)).length * (120 * U + 30) ≤ G * (120 * U + 30) :=
          Nat.mul_le_mul_right _ hLw
        have e2' : G * (120 * U + 30) = 120 * (U * G) + 30 * G := by ring
        have e3 : Qc * (U + 1) * (2 * (allChains S N).length + 2) ≤ Qc * (U + 1) * (2 * G) :=
          Nat.mul_le_mul_left _ (by simp only [CT.S] at hG2; omega)
        have e3' : Qc * (U + 1) * (2 * G) = 2 * (Qc * (U + 1) * G) := by ring
        have e4 : (U + 1) * G = U * G + G := by ring
        have e5 : Q₀ * (3 * count (CT.node S y ks) - 1) = Q₀ * (3 * countL ks + 1) + Q₀ := by
          rw [hcnt]; have : 3 * (1 + countL ks) - 1 = (3 * countL ks + 1) + 1 := by omega
          rw [this]; ring
        have e6 := le_trans hlenF hLw
        rw [e5]
        clear hG hΩ hkids hgk hmk hwt hfil hmap1 hatt hmap2 ha1 ha2 hrec hsubS hshow hid hid' hid''
        omega
    · have ha1 := append_runs (y1 hΔ) B
        (((wtopPlans v (CT.node S y ks)).filter (fun p : CT.Plan × CT × Finset ℕ => decide (N ⊆ p.2.2))).map
          (fun p : CT.Plan × CT × Finset ℕ => ((([] : List ℕ), p.1, p.2.1) : List ℕ × CT.Plan × CT)))
        ([] : List (List ℕ × CT.Plan × CT))
      have ha2 := append_runs (y1 hΔ) B
        (((wtopPlans v (CT.node S y ks)).filter (fun p : CT.Plan × CT × Finset ℕ => decide (N ⊆ p.2.2))).map
          (fun p : CT.Plan × CT × Finset ℕ => ((([] : List ℕ), p.1, p.2.1) : List ℕ × CT.Plan × CT)) ++ [])
        (introKids v N S y [] ks)
      rw [hshow, if_neg hNS]
      refine Runs.mk (hΔ _ _ Δ_introPlans) ?_
      simp only [hNS, decide_false] at hsubS
      simp only [toVal_ct, toVal_nil] at hrec hwt ha1 ha2 ⊢
      ev_start
      · ev_run
      · simp only [List.length_append, List.length_map, List.length_nil]
        obtain ⟨hG1, hG2, hG3, hG4⟩ := hG'
        have hLw : (wtopPlans v (CT.node S y ks)).length ≤ G := by omega
        have e1 : P * ((wtopPlans v (CT.node S y ks)).length + 1) ≤ P * G := Nat.mul_le_mul_left _ hG1
        have e2 : (wtopPlans v (CT.node S y ks)).length * (120 * U + 30) ≤ G * (120 * U + 30) :=
          Nat.mul_le_mul_right _ hLw
        have e2' : G * (120 * U + 30) = 120 * (U * G) + 30 * G := by ring
        have e4 : (U + 1) * G = U * G + G := by ring
        have e5 : Q₀ * (3 * count (CT.node S y ks) - 1) = Q₀ * (3 * countL ks + 1) + Q₀ := by
          rw [hcnt]; have : 3 * (1 + countL ks) - 1 = (3 * countL ks + 1) + 1 := by omega
          rw [this]; ring
        have e6 := le_trans hlenF hLw
        rw [e5]
        clear hG hΩ hkids hgk hmk hwt hfil hmap1 ha1 ha2 hrec hsubS hshow hid hid' hid''
        omega
theorem introKids_runs_rec (U Q P G Ω Qc Q₀ : ℕ) (Bs : Finset ℕ) (kmax M v : ℕ) (N : Finset ℕ)
    (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (hP : Q * (3 * M) ≤ P)
    (hQc : 1000 * ((U + 1) * Ω) ≤ Qc)
    (hQ₀ : 100 * (P * G) + 4 * (Qc * (U + 1) * G) + 500 * ((U + 1) * G) + 1000 * (U + 1) ≤ Q₀)
    (hv : v ≤ U) (hN : N.card ≤ U)
    (hG : ∀ ν : CT, Good Bs ν → maxEntry ν ≤ kmax → count ν ≤ M →
      (wtopPlans v ν).length + 1 ≤ G ∧ (allChains ν.S N).length + 1 ≤ G ∧
      (attachPlans v N ν).length ≤ G ∧ (introPlans v N ν).length ≤ G)
    (hΩ : ∀ ν : CT, Good Bs ν → (chainCands ν.S N).length + 1 ≤ Ω) (hB : 10 * U + 600 < B) :
    ∀ (ks pre : List CT) (S : Finset ℕ) (y : List ℕ),
      (∀ k ∈ ks, sz k ≤ U ∧ mx k ≤ U ∧ Good Bs k ∧ maxEntry k ≤ kmax ∧ count k ≤ M) → pre.length + ks.length ≤ U →
      Runs Δ' B fIntroKids [toVal v, toVal N, toVal S, toVal y, toVal pre, toVal ks]
        (toVal (introKids v N S y pre ks)) (Q₀ * (3 * countL ks + 1))
  | [], pre, S, y, hks, hpre => by
    have hu1 : 1000 ≤ 1000 * (U + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos U)
    have hQ₀1 : 1000 ≤ Q₀ := le_trans hu1 (le_trans (Nat.le_add_left _ _) hQ₀)
    have hid := ids_lt (B := B) (by omega)
    refine Runs.mk (hΔ _ _ Δ_introKids) ?_
    simp only [introKids]
    ev_start
    · ev_run
    · simp [countL]; omega
  | k :: post, pre, S, y, hks, hpre => by
    have hu1 : 1000 ≤ 1000 * (U + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos U)
    have hQ₀1 : 1000 ≤ Q₀ := le_trans hu1 (le_trans (Nat.le_add_left _ _) hQ₀)
    have hid := ids_lt (B := B) (by omega)
    obtain ⟨hk1, hk2, hk3, hk4, hk5⟩ := hks k (List.mem_cons_self ..)
    have hks' : ∀ k' ∈ post, sz k' ≤ U ∧ mx k' ≤ U ∧ Good Bs k' ∧ maxEntry k' ≤ kmax ∧ count k' ≤ M :=
      fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')
    have hip := introPlans_runs_rec U Q P G Ω Qc Q₀ Bs kmax M v N hQ hP hQc hQ₀ hv hN hG hΩ hB k hk1 hk2 hk3 hk4 hk5
    have hrec := introKids_runs_rec U Q P G Ω Qc Q₀ Bs kmax M v N hQ hP hQc hQ₀ hv hN hG hΩ hB post (pre ++ [k]) S y hks'
      (by simp only [List.length_append, List.length_cons, List.length_nil] at hpre ⊢; omega)
    have hlen := length_runs (y1 hΔ) B pre (by simp only [List.length_cons, List.length_nil] at hpre; omega)
    have hOG := (hG k hk3 hk4 hk5).2.2.2
    have hmap := map_runs (y1 hΔ) B fKid (toVal (pre.length, S, y, pre, post))
      (fun r : List ℕ × CT.Plan × CT => ((pre.length :: r.1, r.2.1, CT.node S y (pre ++ r.2.2 :: post)) : List ℕ × CT.Plan × CT))
      (fun _ => 10 * pre.length + 40) (introPlans v N k)
      (fun r _ => by obtain ⟨path, pl, c⟩ := r; exact kid_runs hΔ B S y pre post path pl c)
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap
    have hap1 := append_runs (y1 hΔ) B pre [k]
    simp only [toVal_cons, toVal_nil] at hap1
    have hap2 := append_runs (y1 hΔ) B
      ((introPlans v N k).map (fun r : List ℕ × CT.Plan × CT => ((pre.length :: r.1, r.2.1, CT.node S y (pre ++ r.2.2 :: post)) : List ℕ × CT.Plan × CT)))
      (introKids v N S y (pre ++ [k]) post)
    have hshow : introKids v N S y pre (k :: post) =
        (introPlans v N k).map (fun r : List ℕ × CT.Plan × CT => ((pre.length :: r.1, r.2.1, CT.node S y (pre ++ r.2.2 :: post)) : List ℕ × CT.Plan × CT)) ++
        introKids v N S y (pre ++ [k]) post := rfl
    rw [hshow]
    refine Runs.mk (hΔ _ _ Δ_introKids) ?_
    simp only [toVal_cons, toVal_pair] at hmap ⊢
    ev_start
    · ev_run
    · simp only [List.length_map]
      have hcnt := count_pos k
      have hpl : pre.length ≤ U := by simp only [List.length_cons] at hpre; omega
      have e1 : (introPlans v N k).length * (10 * pre.length + 40) ≤ G * (10 * U + 40) :=
        Nat.mul_le_mul hOG (by omega)
      have e2 : G * (10 * U + 40) = 10 * (U * G) + 40 * G := by ring
      have e3 : (U + 1) * G = U * G + G := by ring
      have e4 : Q₀ * (3 * countL (k :: post) + 1) =
          Q₀ * (3 * count k - 1) + Q₀ * (3 * countL post + 1) + Q₀ := by
        have : 3 * countL (k :: post) + 1 = (3 * count k - 1) + (3 * countL post + 1) + 1 := by
          simp only [countL]; omega
        rw [this]; ring
      have e5 : 100 * (P * G) + 4 * (Qc * (U + 1) * G) ≥ 0 := Nat.zero_le _
      rw [e4]
      clear hG hΩ hks hks'
      omega
end

end proofs

theorem introPlans_runs_pair : (type_of% @introPlans_runs_rec) ∧ (type_of% @introKids_runs_rec) :=
  ⟨@introPlans_runs_rec, @introKids_runs_rec⟩

theorem introPlans_runs : type_of% @introPlans_runs_rec := introPlans_runs_pair.1

end E3C
end Lax117284Proofs.Treewidth.Fun
