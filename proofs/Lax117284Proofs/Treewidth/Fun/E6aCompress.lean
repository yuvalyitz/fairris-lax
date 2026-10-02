import Lax117284Proofs.Treewidth.Fun.E6aDefs
import Lax117284Proofs.Treewidth.Wrap.CompressSize

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6a (3): `compress` (with `flatKids`)

* `flatKids_runs` : cost `100 (s+1) · sz L` for `sz X ≤ s`;
* `compress_runs` : cost `200 (s+1)² · wt t` (`wt t = 2 size t − 1`) for `sz t ≤ s`;
* `embeds_compress` : `Embeds … fCompress … compress (400 (sz t + sz (compress t) + 1)³)`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6a

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees Lib1

/-! ## sizes -/

theorem sz_rt_node' (X : Finset ℕ) (ks : List RT) : sz (RT.node X ks) = sz X + sz ks + 1 := by
  simp only [sz, toVal_rt, Val.size]

theorem sz_map_le6 {α β : Type} [ToVal α] [ToVal β] (f : α → β) : ∀ l : List α,
    (∀ a ∈ l, sz (f a) ≤ sz a) → sz (l.map f) ≤ sz l
  | [], _ => by simp
  | a :: l, h => by
    have h1 := h a (by simp)
    have ih := sz_map_le6 f l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.map_cons, sz_cons, sz_cons]; omega

theorem sz_flatKids_le (X : Finset ℕ) : ∀ L : List RT, sz (flatKids X L) ≤ sz L
  | [] => by simp [flatKids]
  | .node Y ls :: rest => by
    have ih := sz_flatKids_le X rest
    rw [flatKids]
    by_cases hY : Y ⊆ X
    · simp only [hY, if_true]
      have := sz_append ls (flatKids X rest)
      rw [sz_cons, sz_rt_node']
      have := sz_pos Y
      omega
    · simp only [hY, if_false]
      rw [sz_cons, sz_cons, sz_rt_node']
      omega

theorem sz_compress_le : ∀ t : RT, sz (compress t) ≤ sz t := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    rw [RT.compress_node, sz_rt_node', sz_rt_node']
    have h1 := sz_flatKids_le X (ks.map compress)
    have h2 := sz_map_le6 compress ks ih
    omega

/-! ## the potential `wt t = 2 · size t − 1` -/

def wtR (t : RT) : ℕ := 2 * t.size - 1

theorem wtR_node (X : Finset ℕ) (ks : List RT) : wtR (.node X ks) = 2 * (ks.map RT.size).sum + 1 := by
  simp [wtR, RT.size_node]; omega

theorem sum_wtR : ∀ ks : List RT, (ks.map wtR).sum + ks.length = 2 * (ks.map RT.size).sum
  | [] => by simp
  | k :: ks => by
    have h := sum_wtR ks
    have h1 := RT.size_pos k
    simp only [List.map_cons, List.sum_cons, List.length_cons, wtR]
    omega

theorem sum_le_wtR : ∀ (ks : List RT) (cf : RT → ℕ) (C : ℕ),
    (∀ k ∈ ks, cf k ≤ C * wtR k + 3) → (ks.map cf).sum ≤ C * (ks.map wtR).sum + 3 * ks.length
  | [], _, _, _ => by simp
  | k :: ks, cf, C, h => by
    have h1 := h k (by simp)
    have ih := sum_le_wtR ks cf C (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-! ## `flatKids` -/

section flat
variable {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ') (B : ℕ)
include hΔ

theorem flatKids_runs (X : Finset ℕ) (s : ℕ) (hX : sz X ≤ s) (hB : 1000 < B) :
    ∀ L : List RT, Runs Δ' B fFlatKids [toVal X, toVal L] (toVal (flatKids X L)) (100 * (s + 1) * sz L) := by
  have hXc : X.card ≤ s := le_trans (by rw [sz_finset]; omega) hX
  intro L
  induction L with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_flatKids) ?_
    ev_start
    · ev_run
    · simp; nlinarith
  | cons k rest ih =>
    obtain ⟨Y, ls⟩ := k
    have hYc : Y.card ≤ sz Y := by rw [sz_finset]; omega
    have hlsl : ls.length ≤ sz ls := length_le_sz ls
    have hsub := Lib3.subset_runs (ext3 hΔ) B (by omega) Y X (decide (Y ⊆ X)) (by simp)
    have happ := append_runs (ext1 hΔ) B ls (flatKids X rest)
    have hsl : sz (RT.node Y ls :: rest) = sz Y + sz ls + sz rest + 2 := by
      rw [sz_cons, sz_rt_node']; omega
    have hlsl' : ls.length ≤ sz ls := length_le_sz ls
    refine Runs.mk (hΔ _ _ Δ_flatKids) ?_
    rw [flatKids]
    simp only [toVal_cons, toVal_rt]
    by_cases hY : Y ⊆ X
    · simp only [hY, if_true, decide_true, toVal_true] at hsub ⊢
      ev_start
      · ev_run
        apply EvLe.iteT
        · ev_sub
        · ev_side
        · ev_run
      · rw [hsl]
        nlinarith
    · simp only [hY, if_false, decide_false, toVal_false] at hsub ⊢
      ev_start
      · ev_run
        apply EvLe.iteF
        · case hc => ev_sub
        · ev_side
        · ev_run
      · rw [hsl]
        nlinarith

theorem compress_runs (hB : 1000 < B) (s : ℕ) : ∀ t : RT, sz t ≤ s →
    Runs Δ' B fCompress [toVal t] (toVal (compress t)) (200 * (s + 1) ^ 2 * wtR t) := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro hs
    rw [sz_rt_node'] at hs
    have hXs : sz X ≤ s := by omega
    have hks : sz ks ≤ s := by omega
    have hkid : ∀ k ∈ ks, sz k ≤ s := fun k hk => le_trans (sz_le_of_mem hk) hks
    have hc642 : fCompressC < B := by show 642 < B; omega
    have hf : ∀ k ∈ ks, Runs Δ' B fCompressC [.nat 0, toVal k] (toVal (compress k))
        (200 * (s + 1) ^ 2 * wtR k + 3) := by
      intro k hk
      have h1 := ih k hk (hkid k hk)
      refine Runs.mk (hΔ _ _ Δ_compressC) ?_
      ev_start
      · ev_run
      · omega
    have hmap := map_runs (ext1 hΔ) B fCompressC (.nat 0) compress (fun k => 200 * (s + 1) ^ 2 * wtR k + 3) ks hf
    have hsum := sum_le_wtR ks (fun k => 200 * (s + 1) ^ 2 * wtR k + 3) (200 * (s + 1) ^ 2) (fun k _ => le_refl _)
    have hsk : sz (ks.map compress) ≤ s :=
      le_trans (sz_map_le6 compress ks (fun k _ => sz_compress_le k)) hks
    have hflat := flatKids_runs hΔ B X s hXs hB (ks.map compress)
    have hlen := length_le_sz ks
    have hw := sum_wtR ks
    have hwn := wtR_node X ks
    have hP : 1 ≤ (s + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hP2 : (s + 1) * s ≤ (s + 1) ^ 2 := by nlinarith
    refine Runs.mk (hΔ _ _ Δ_compress) ?_
    rw [RT.compress_node]
    simp only [toVal_rt]
    ev_start
    · ev_run
    · rw [hwn]
      nlinarith

end flat

theorem wtR_le_sz (t : RT) : wtR t ≤ 2 * sz t := by
  have := size_le_sz t; unfold wtR; omega

section embeds
variable {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ')
include hΔ

/-- **`compress`** (`fCompress`, argument `t`), unconditionally; output-sensitive cost of degree 3. -/
theorem embeds_compress : Embeds Δ' fCompress (fun _ : RT => True) compress
    (fun t => 400 * (sz t + sz (compress t) + 1) ^ 3) := by
  intro B t _ hfit
  have hc : 400 * (sz t + sz (compress t) + 1) ^ 3 + 3 < B := hfit.cost_lt
  have hp1 := sz_pos t
  have hp2 := sz_pos (compress t)
  have hS : 3 ≤ sz t + sz (compress t) + 1 := by omega
  have hS3 : 27 ≤ (sz t + sz (compress t) + 1) ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_left hS 3
  have h1000 : 1000 < B := by omega
  have h := compress_runs (Δ' := Δ') hΔ B h1000 (sz t) t le_rfl
  refine h.mono ?_
  have hw := wtR_le_sz t
  have hsq : (sz t + 1) ^ 2 ≤ (sz t + sz (compress t) + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h3 : (sz t + sz (compress t) + 1) ^ 3 = (sz t + sz (compress t) + 1) ^ 2 * (sz t + sz (compress t) + 1) := by ring
  show 200 * (sz t + 1) ^ 2 * wtR t ≤ 400 * (sz t + sz (compress t) + 1) ^ 3
  rw [h3]
  have : (sz t + 1) ^ 2 * wtR t ≤ (sz t + sz (compress t) + 1) ^ 2 * (2 * (sz t + sz (compress t) + 1)) :=
    Nat.mul_le_mul hsq (by omega)
  nlinarith

end embeds

end E6a
end Lax117284Proofs.Treewidth.Fun
