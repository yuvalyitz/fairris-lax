import Lax117284Proofs.Treewidth.Fun.E2Forget
import Lax117284Proofs.Treewidth.Size.Statements
import Lax117284Proofs.Treewidth.Size.Lattice

/-!
# WP E2 (5): `joinC`, part 1 — Lean-level facts and the helpers (`subMap`, `allLe`, `joinYs`, `mapKK`, `consAll`)

Notation: `xb nb k = cbound nb k 1 = 2^(4(nb+k+2))` (so `cbound nb k m = (xb nb k)^m`);  `4^(2k+1) ≤ xb`, `k+1 ≤ xb`, `256 ≤ xb`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT Lib1 Lax117284Proofs.Treewidth.Seq

/-! ## Lean-level facts -/

/-- `ys` of `joinC`. -/
def joinYsL (c kmax : ℕ) (y y' : List ℕ) : List (List ℕ) :=
  (((ringTypList y y').map (fun d => d.map (· - c))).dedup).filter (fun d => d.all (· ≤ kmax))

theorem cbound_eq_pow (b k m : ℕ) : cbound b k m = (cbound b k 1) ^ m := by
  unfold cbound; rw [← pow_mul]; congr 1; ring

abbrev xb (nb k : ℕ) : ℕ := cbound nb k 1

theorem xb_ge (nb k : ℕ) : 256 ≤ xb nb k := by
  unfold xb cbound
  calc 256 = 2 ^ 8 := by norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem xb_ring (nb k : ℕ) : 4 ^ (2 * k + 1) ≤ xb nb k := by
  unfold xb cbound
  calc 4 ^ (2 * k + 1) = 2 ^ (2 * (2 * k + 1)) := by rw [pow_mul]; norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem xb_k (nb k : ℕ) : k + 1 ≤ xb nb k := by
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  unfold xb cbound
  have : 2 ^ k ≤ 2 ^ ((2 * nb + 2 * k + 4) * (2 * 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem ringTypList_mem_length_le {a b d : List ℕ} {L₁ L₂ : ℕ} (ha : ∀ x ∈ a, x ≤ L₁) (hb : ∀ x ∈ b, x ≤ L₂)
    (hd : d ∈ ringTypList a b) : d.length ≤ 2 * (L₁ + L₂) + 1 := by
  unfold ringTypList at hd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hd
  obtain ⟨-, hty⟩ := latticeStates_sound hs
  rw [hty]
  exact typical_length_le' (pathSum_le ha hb _)

theorem countL_eq_sum : ∀ ks : List CT, countL ks = (ks.map count).sum
  | [] => by simp [countL]
  | k :: ks => by simp [countL, countL_eq_sum ks]

theorem sum_pow_le {Z : ℕ} (hZ : 2 ≤ Z) : ∀ l : List ℕ, (∀ c ∈ l, 1 ≤ c) → (l.map (fun c => Z ^ c)).sum ≤ Z ^ l.sum
  | [], _ => by simp
  | c :: l, h => by
    have hc := h c (by simp)
    have ih := sum_pow_le hZ l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, pow_add]
    by_cases hl : l = []
    · subst hl; simp
    · have hs : 1 ≤ l.sum := by
        obtain ⟨x, l', rfl⟩ := List.exists_cons_of_ne_nil hl
        have := h x (by simp); simp only [List.sum_cons]; omega
      have h1 : 2 ≤ Z ^ c := le_trans hZ (by calc Z = Z ^ 1 := (pow_one Z).symm
                                                  _ ≤ Z ^ c := Nat.pow_le_pow_right (by omega) hc)
      have h2 : 2 ≤ Z ^ l.sum := le_trans hZ (by calc Z = Z ^ 1 := (pow_one Z).symm
                                                    _ ≤ Z ^ l.sum := Nat.pow_le_pow_right (by omega) hs)
      nlinarith

theorem sum_count_pow_le {Z : ℕ} (hZ : 2 ≤ Z) (ks : List CT) :
    (ks.map (fun k => Z ^ count k)).sum ≤ Z ^ countL ks := by
  have := sum_pow_le hZ (ks.map count) (by intro c hc; obtain ⟨k, -, rfl⟩ := List.mem_map.1 hc; exact count_ge_one k)
  rw [countL_eq_sum]
  simpa [List.map_map, Function.comp_def] using this

theorem sum_count_mul (ks : List CT) (R : ℕ) : (ks.map (fun k => count k * R)).sum = countL ks * R := by
  induction ks with
  | nil => simp [countL]
  | cons k ks ih => simp only [List.map_cons, List.sum_cons, countL, ih]; ring

theorem sum_map_const_mul {α : Type} (l : List α) (c : ℕ) : (l.map (fun _ => c)).sum = l.length * c := by
  simp [List.map_const', List.sum_replicate]

theorem sum_map_le_card {α : Type} (l : List α) (f : α → ℕ) (c : ℕ) (h : ∀ a ∈ l, f a ≤ c) :
    (l.map f).sum ≤ l.length * c := by
  have := List.sum_le_card_nsmul (l.map f) c (by
    intro x hx; obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx; exact h a ha)
  simpa using this

/-! ## `Runs` helpers -/

section helpers
variable {rid : ℕ} {Δ' : ℕ → Option Tm} (hΔ : e2Δ rid ⊑ Δ') (B : ℕ)
include hΔ

theorem flatMap_runs_le {α β : Type} [ToVal α] [ToVal β] (fid : ℕ) (ctx : Val) (g : α → List β) (cf : α → ℕ)
    (l : List α) (n c : ℕ) (hn : ∀ a ∈ l, (g a).length ≤ n) (hc : ∀ a ∈ l, cf a ≤ c)
    (hf : ∀ a ∈ l, Runs Δ' B fid [ctx, toVal a] (toVal (g a)) (cf a)) :
    Runs Δ' B fFlatMap [.nat fid, ctx, toVal l] (toVal (l.flatMap g)) (l.length * (c + 10 * n + 20) + 8) := by
  refine (Lib1.flatMap_runs (ext1 hΔ) B fid ctx g cf l hf).mono ?_
  have := sum_map_le_card l (fun a => cf a + 10 * (g a).length + 20) (c + 10 * n + 20)
    (fun a ha => by have := hc a ha; have := hn a ha; omega)
  omega

theorem subC_runs (c e : ℕ) : Runs Δ' B fSubC [toVal c, toVal e] (toVal (e - c)) 4 := by
  refine Runs.mk (hΔ _ _ (Δ_subC rid)) ?_
  ev_start
  · ev_run
  · omega

theorem subMap_runs (c : ℕ) (d : List ℕ) (hB : 1000 + 30 * d.length < B) :
    Runs Δ' B fSubMap [toVal c, toVal d] (toVal (d.map (· - c))) (30 * d.length + 20) := by
  have h := Lib1.map_runs (ext1 hΔ) B fSubC (toVal c) (fun e => e - c) (fun _ => 4) d
    (fun e _ => subC_runs hΔ B c e)
  rw [sum_map_const_mul] at h
  have hl : fSubC < B := by show 170 < B; omega
  refine Runs.mk (hΔ _ _ (Δ_subMap rid)) ?_
  ev_start
  · ev_run
  · omega

theorem leK_runs (kmax e : ℕ) (hB : 1 < B) : Runs Δ' B fLeK [toVal kmax, toVal e] (toVal (decide (e ≤ kmax))) 8 := by
  refine Runs.mk (hΔ _ _ (Δ_leK rid)) ?_
  by_cases h : e ≤ kmax
  · have h' : ¬ kmax < e := by omega
    simp only [h, decide_true, toVal_true]
    ev_start
    · ev_run
    · omega
  · have h' : kmax < e := by omega
    simp only [h, decide_false, toVal_false]
    ev_start
    · ev_run
    · omega

theorem allLe_runs (kmax : ℕ) (d : List ℕ) (hB : 1000 + 30 * d.length < B) :
    Runs Δ' B fAllLe [toVal kmax, toVal d] (toVal (d.all (· ≤ kmax))) (30 * d.length + 20 + 8 * d.length) := by
  have h := Lib1.all_runs (ext1 hΔ) B fLeK (toVal kmax) (fun e => decide (e ≤ kmax)) (fun _ => 8) d
    (fun e _ => leK_runs hΔ B kmax e (by omega)) (by omega)
  rw [sum_map_const_mul] at h
  have hl : fLeK < B := by show 172 < B; omega
  refine Runs.mk (hΔ _ _ (Δ_allLe rid)) ?_
  ev_start
  · ev_run
  · omega

theorem joinYs_runs (S : Finset ℕ) (k : ℕ) (y y' : List ℕ) (R0 X : ℕ)
    (hy : ∀ x ∈ y, x ≤ k) (hy' : ∀ x ∈ y', x ≤ k)
    (hX : 4 ^ (2 * k + 1) ≤ X) (hkX : k + 1 ≤ X) (hX8 : 8 ≤ X)
    (hring : Runs Δ' B rid [toVal y, toVal y'] (toVal (ringTypList y y')) R0)
    (hB : R0 + 8 * S.card + 4000 * X ^ 3 + 1000 < B) :
    Runs Δ' B fJoinYs [toVal S, toVal k, toVal y, toVal y'] (toVal (joinYsL S.card k y y'))
      (R0 + 8 * S.card + 4000 * X ^ 3) := by
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hX3 : X ^ 2 ≤ X ^ 3 := by nlinarith
  have hrl : (ringTypList y y').length ≤ X := by
    have := ringTypList_length_le hy hy'
    have h2 : 4 ^ (k + k + 1) = 4 ^ (2 * k + 1) := by congr 1; omega
    omega
  have hd : ∀ d ∈ ringTypList y y', d.length ≤ 4 * k + 1 := fun d hd' => by
    have := ringTypList_mem_length_le hy hy' hd'; omega
  have hB1 : 1 < B := by omega
  have hcard := Lib4.card_runs (ext4 hΔ) B S (by omega)
  have hmap := Lib1.map_runs (ext1 hΔ) B fSubMap (toVal S.card) (fun d => d.map (· - S.card))
    (fun _ => 120 * k + 50) (ringTypList y y') (fun d hd' =>
      (subMap_runs hΔ B S.card d (by have := hd d hd'; omega)).mono (by have := hd d hd'; omega))
  rw [sum_map_const_mul] at hmap
  have hl2 : ((ringTypList y y').map (fun d => d.map (· - S.card))).length = (ringTypList y y').length := by simp
  have hs2 : ∀ a ∈ (ringTypList y y').map (fun d => d.map (· - S.card)), sz a ≤ 8 * k + 3 := by
    intro a ha
    obtain ⟨d, hd', rfl⟩ := List.mem_map.1 ha
    rw [sz_list_nat, List.length_map]
    have := hd d hd'; omega
  have hdd := Lib2.dedup_runs (ext2 hΔ) B hB1 (8 * k + 3) _ hs2
  have hddl : (((ringTypList y y').map (fun d => d.map (· - S.card))).dedup).length ≤ (ringTypList y y').length := by
    have := (List.dedup_sublist ((ringTypList y y').map (fun d => d.map (· - S.card)))).length_le
    omega
  have hfilt := Lib1.filter_runs (ext1 hΔ) B fAllLe (toVal k) (fun d => d.all (· ≤ k))
    (fun _ => 152 * k + 58) (((ringTypList y y').map (fun d => d.map (· - S.card))).dedup) (fun d hd' => by
      have hd2 := List.mem_dedup.1 hd'
      obtain ⟨d0, hd0, rfl⟩ := List.mem_map.1 hd2
      have := hd d0 hd0
      refine (allLe_runs hΔ B k _ (by rw [List.length_map]; omega)).mono ?_
      rw [List.length_map]; omega)
  rw [sum_map_const_mul] at hfilt
  have hlA : fAllLe < B := by show 173 < B; omega
  have hlS : fSubMap < B := by show 171 < B; omega
  unfold joinYsL
  refine Runs.mk (hΔ _ _ (Δ_joinYs rid)) ?_
  rw [hl2] at hdd
  ev_start
  · ev_run
  · set n := (ringTypList y y').length with hn
    set m := (((ringTypList y y').map (fun d => d.map (· - S.card))).dedup).length with hm
    have h1 : n * (k + 1) ≤ X * X := Nat.mul_le_mul hrl hkX
    have h2 : m * (k + 1) ≤ X * X := Nat.mul_le_mul (le_trans hddl hrl) hkX
    have h3 : (k + 1) * (n + 1) ^ 2 ≤ X * (2 * X) ^ 2 := by
      apply Nat.mul_le_mul hkX
      exact Nat.pow_le_pow_left (by omega) 2
    have h4 : m ≤ X := le_trans hddl hrl
    nlinarith

end helpers

end E2
end Lax117284Proofs.Treewidth.Fun
