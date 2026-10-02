import Lax117284Proofs.Treewidth.Fun.E2Sz

/-!
# WP E2 (3): `keep`, `normNode`, `norm` as F-functions

* `keep_runs`, `normNode_runs` (cost `3000 (m+1) (s+1)^4`, `m` = number of kids);
* `norm_runs_aux` : `Runs fNorm [toVal c] (toVal (norm c)) (3100 · wt c · (sz c + 1)^4)`, `wt c = 2 count c - 1`
  (the per-node local cost is charged through the potential `tree_step` of `E2Base`);
* `norm_runs` : cost `6200 (s + 1)^5` for `sz c ≤ s`, hypothesis `14000 (s+1)^5 < B`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT Lib1 Lax117284Proofs.Treewidth.Seq

theorem length_le_countL : ∀ ks : List CT, ks.length ≤ countL ks
  | [] => by simp [countL]
  | k :: ks => by
    have := length_le_countL ks; have := count_ge_one k
    simp only [List.length_cons, countL]; omega

theorem sum_map_add_const {α : Type} (l : List α) (f : α → ℕ) (c : ℕ) :
    (l.map (fun a => f a + c)).sum = (l.map f).sum + c * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

section norm
variable {rid : ℕ} {Δ' : ℕ → Option Tm} (hΔ : e2Δ rid ⊑ Δ') (hE : E1A.Δ ⊑ Δ') (B : ℕ)
include hΔ

omit hE in
theorem keep_runs (S : Finset ℕ) (k : CT) (s : ℕ) (hS : sz S ≤ s) (hk : sz k ≤ s) (hB : 200 * (s + 1) < B) :
    Runs Δ' B fKeep [toVal S, toVal k] (toVal (keep S k)) (130 * (s + 1)) := by
  obtain ⟨kS, ky, kks⟩ := k
  have hSk : sz kS ≤ s := by have := sz_S_le kS ky kks; omega
  have hB1 : 1 < B := by omega
  have h1 := sz_finset_card S
  have h2 := sz_finset_card kS
  have hsub := Lib3.subset_runs (ext3 hΔ) B (by omega) kS S (decide (kS ⊆ S)) (by simp)
  have hsub' : Runs Δ' B Lib3.fSubsetS [toVal kS, toVal S] (toVal (decide (kS ⊆ S))) (120 * s + 20) :=
    hsub.mono (by omega)
  clear hsub
  refine Runs.mk (hΔ _ _ (Δ_keep rid)) ?_
  simp only [toVal_ct]
  cases kks with
  | nil =>
    by_cases hs : kS ⊆ S
    · have : keep S (node kS ky []) = false := by simp [keep, isLeaf, CT.kids, CT.S, hs]
      rw [this]
      simp only [hs, decide_true] at hsub'
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
    · have : keep S (node kS ky []) = true := by simp [keep, isLeaf, CT.kids, CT.S, hs]
      rw [this]
      simp only [hs, decide_false] at hsub'
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
  | cons k ks =>
    have : keep S (node kS ky (k :: ks)) = true := by simp [keep, isLeaf, CT.kids]
    rw [this]
    ev_start
    · ev_run
    · omega

include hE in
theorem normNode_runs (S : Finset ℕ) (y : List ℕ) (ks : List CT) (s : ℕ)
    (hS : sz S ≤ s) (hy : sz y ≤ s) (hks : sz ks ≤ s) (hB : 4000 * (ks.length + 1) * (s + 1) ^ 4 < B) :
    Runs Δ' B fNormNode [toVal S, toVal y, toVal ks] (toVal (normNode S y ks))
      (3000 * (ks.length + 1) * (s + 1) ^ 4) := by
  have hm : ks.length ≤ s := le_trans (length_le_sz ks) hks
  have h1 : s + 1 ≤ (s + 1) ^ 4 := by
    calc s + 1 = (s + 1) ^ 1 := (pow_one _).symm
      _ ≤ (s + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (s + 1) ^ 3 ≤ (s + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h0 : 1 ≤ (s + 1) ^ 4 := le_trans (by omega) h1
  have hQ1 : (ks.length + 1) * (s + 1) ≤ (ks.length + 1) * (s + 1) ^ 4 := Nat.mul_le_mul_left _ h1
  have hQ2 : (s + 1) ^ 4 ≤ (ks.length + 1) * (s + 1) ^ 4 := by nlinarith
  have hB1 : 1 < B := by nlinarith
  have hkeep : fKeep < B := by show 164 < B; nlinarith
  have hfilt := Lib1.filter_runs (ext1 hΔ) B fKeep (toVal S) (keep S) (fun _ => 130 * (s + 1)) ks
    (fun k hk => keep_runs hΔ B S k s hS (le_trans (sz_le_of_mem hk) hks) (by nlinarith))
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hfilt
  have hfilt' : Runs Δ' B fFilter [.nat fKeep, toVal S, toVal ks] (toVal (ks.filter (keep S)))
      (200 * ((ks.length + 1) * (s + 1) ^ 4)) := hfilt.mono (by nlinarith)
  clear hfilt
  have hFsz := sz_filter_le (keep S) ks
  rw [normNode_eq]
  refine Runs.mk (hΔ _ _ (Δ_normNode rid)) ?_
  generalize hF : ks.filter (keep S) = F at hfilt' hFsz ⊢
  cases F with
  | nil =>
    have htake := Lib1.take_runs (ext1 hΔ) B 1 y hB1
    rw [normF_nil]
    simp only [toVal_ct]
    ev_start
    · ev_run
    · have := min_le_left 1 y.length
      nlinarith
  | cons k F' =>
    cases F' with
    | nil =>
      have hk1 : sz [k] ≤ s := le_trans hFsz hks
      have hk2 : sz k + 2 ≤ sz [k] := sz_mem_add_two (List.mem_singleton_self k)
      obtain ⟨kS, ky, kks⟩ := k
      have hn := sz_ct_node' kS ky kks
      have hkS : sz kS ≤ s := by omega
      have hky : sz ky ≤ s := by omega
      have hkks : sz kks ≤ s := by omega
      have hly : y.length ≤ s := le_trans (length_le_sz y) hy
      have hlky : ky.length ≤ s := le_trans (length_le_sz ky) hky
      have hlt : ((y ++ ky).length + 1) ^ 3 ≤ 8 * (s + 1) ^ 3 := by
        have : (y ++ ky).length + 1 ≤ 2 * (s + 1) := by simp only [List.length_append]; omega
        calc ((y ++ ky).length + 1) ^ 3 ≤ (2 * (s + 1)) ^ 3 := Nat.pow_le_pow_left this 3
          _ = 8 * (s + 1) ^ 3 := by ring
      have happ := Lib1.append_runs (ext1 hΔ) B y ky
      have htyp := E1A.typical_runs hE B hB1 (y ++ ky)
      have hmin : ∀ a b : ℕ, min a b ≤ a := fun a b => min_le_left a b
      by_cases hSk : kS = S
      · have heq := Lib1.eqV_runs_typed (ext1 hΔ) B hB1 kS S true (by simp [hSk])
        have hcond : (node kS ky kks).S = S := hSk
        rw [normF_single, if_pos hcond]
        simp only [CT.y, CT.kids]
        simp only [toVal_ct]
        simp only [toVal_cons, toVal_nil, toVal_ct] at hfilt' ⊢
        ev_start
        · ev_run
        · have := hmin (sz kS) (sz S)
          have := min_le_left (30 * min (sz kS) (sz S)) 0
          nlinarith
      · have heq := Lib1.eqV_runs_typed (ext1 hΔ) B hB1 kS S false (by simp [hSk])
        have hcond : ¬ (node kS ky kks).S = S := hSk
        rw [normF_single, if_neg hcond]
        simp only [toVal_ct]
        simp only [toVal_cons, toVal_nil, toVal_ct] at hfilt' ⊢
        ev_start
        · ev_run
        · have := hmin (sz kS) (sz S)
          nlinarith
    | cons k2 F'' =>
      have hsort := sortKids_runs hΔ B S (k :: k2 :: F'') s hS (le_trans hFsz hks) (by nlinarith)
      have hsrt : fSortKids < B := by show 163 < B; nlinarith
      rw [normF_ge2]
      simp only [toVal_ct]
      simp only [toVal_cons, toVal_nil, toVal_ct] at hfilt' hsort ⊢
      ev_start
      · ev_run
      · nlinarith

include hE in
theorem norm_runs_aux (c : CT) (hB : 7000 * (2 * count c) * (sz c + 1) ^ 4 < B) :
    Runs Δ' B fNorm [toVal c] (toVal (norm c)) (3100 * wt c * (sz c + 1) ^ 4) := by
  induction c using CT.ind with
  | h S y ks ih =>
    have hwt := wt_node S y ks
    have hcnode : count (node S y ks) = 1 + countL ks := rfl
    have hsz := sz_ks_le S y ks
    have hSz := sz_S_le S y ks
    have hyz := sz_y_le S y ks
    set T := (sz (node S y ks) + 1) ^ 4 with hT
    have hT1 : 1 ≤ T := Nat.one_le_pow _ _ (by omega)
    have hm : ks.length ≤ sz ks := length_le_sz ks
    have hcpos := count_ge_one (node S y ks)
    have hcm : ks.length + 1 ≤ count (node S y ks) := by
      have := length_le_countL ks; rw [hcnode]; omega
    have hB' : 4000 * (ks.length + 1) * T < B := by nlinarith
    have hnn := normNode_runs hΔ hE B S y (ks.map norm) (sz (node S y ks)) (by omega) (by omega)
      (by have := sz_map_le norm ks (fun k hk => sz_norm_le k); omega) (by rw [List.length_map]; exact hB')
    have hnormC : ∀ k ∈ ks, Runs Δ' B fNormC [Val.nat 0, toVal k] (toVal (norm k))
        (3100 * wt k * (sz k + 1) ^ 4 + 3) := by
      intro k hk
      have hk1 := ih k hk (by
        have h6 : count k ≤ count (node S y ks) := by
          have := count_le_countL_of_mem hk; rw [hcnode]; omega
        have h7 := sz_le_of_mem_kids (S := S) (y := y) hk
        have h8 : (sz k + 1) ^ 4 ≤ T := Nat.pow_le_pow_left (by omega) 4
        have h9 : 7000 * (2 * count k) * (sz k + 1) ^ 4 ≤ 7000 * (2 * count (node S y ks)) * T :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h6)) h8
        exact lt_of_le_of_lt h9 hB)
      refine Runs.mk (hΔ _ _ (Δ_normC rid)) ?_
      ev_start
      · ev_run
      · omega
    have hmap := Lib1.map_runs (ext1 hΔ) B fNormC (Val.nat 0) norm (fun k => 3100 * wt k * (sz k + 1) ^ 4 + 3) ks hnormC
    have hlit : fNormC < B := by show 167 < B; nlinarith
    have hts := tree_step ks (fun k => sz k + 1) 3100 4 (sz (node S y ks) + 1)
      (fun k hk => by have := sz_le_of_mem_kids (S := S) (y := y) hk; omega)
    rw [sum_map_add_const] at hmap
    simp only [List.length_map] at hnn
    rw [← hT] at hts hnn
    rw [norm_node, normL_eq_map]
    refine Runs.mk (hΔ _ _ (Δ_norm rid)) ?_
    simp only [toVal_ct]
    ev_start
    · ev_run
    · rw [hwt]
      have := Nat.mul_le_mul_left (ks.length + 1) hT1
      nlinarith

include hE in
theorem norm_runs (c : CT) (s : ℕ) (hc : sz c ≤ s) (hB : 14000 * (s + 1) ^ 5 < B) :
    Runs Δ' B fNorm [toVal c] (toVal (norm c)) (6200 * (s + 1) ^ 5) := by
  have h1 := count_le_sz c
  have hT : (sz c + 1) ^ 5 ≤ (s + 1) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have hp4 : (s + 1) ^ 4 * (s + 1) = (s + 1) ^ 5 := by ring
  have hp4' : (sz c + 1) ^ 4 ≤ (s + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h2 : 2 * count c * (sz c + 1) ^ 4 ≤ 2 * (s + 1) ^ 5 := by
    have : count c ≤ s + 1 := by omega
    calc 2 * count c * (sz c + 1) ^ 4 ≤ 2 * (s + 1) * (s + 1) ^ 4 :=
          Nat.mul_le_mul (by omega) hp4'
      _ = 2 * (s + 1) ^ 5 := by rw [← hp4]; ring
  refine (norm_runs_aux hΔ hE B c (by nlinarith)).mono ?_
  have h3 : wt c ≤ 2 * count c := by unfold wt; omega
  calc 3100 * wt c * (sz c + 1) ^ 4 ≤ 3100 * (2 * count c) * (sz c + 1) ^ 4 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3)
    _ = 3100 * (2 * count c * (sz c + 1) ^ 4) := by ring
    _ ≤ 3100 * (2 * (s + 1) ^ 5) := Nat.mul_le_mul_left _ h2
    _ = 6200 * (s + 1) ^ 5 := by ring

end norm

end E2
end Lax117284Proofs.Treewidth.Fun
