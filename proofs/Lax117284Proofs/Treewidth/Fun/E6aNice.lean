import Lax117284Proofs.Treewidth.Fun.E6aCompress
import Lax117284Proofs.Treewidth.Wrap.NiceSizeConn

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6a (4): the building blocks of `niceOf` — `NT.bag`, `introMany`, `forgetMany`, `conv`, the join fold
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6a

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees Lib1

theorem card_bag_le_inner : ∀ nt : NT, nt.bag.card ≤ nt.inner
  | .leaf => by simp [NT.bag, NT.inner]
  | .intro v c => by
    have h := card_bag_le_inner c
    have := Finset.card_insert_le v c.bag
    simp only [NT.bag, NT.inner]; omega
  | .forget v c => by
    have h := card_bag_le_inner c
    have := Finset.card_erase_le (a := v) (s := c.bag)
    simp only [NT.bag, NT.inner]; omega
  | .join a b => by
    have h := card_bag_le_inner a
    simp only [NT.bag, NT.inner]; omega

theorem sum_le_wtR' : ∀ (ks : List RT) (cf : RT → ℕ) (C D : ℕ),
    (∀ k ∈ ks, cf k ≤ C * wtR k + D) → (ks.map cf).sum ≤ C * (ks.map wtR).sum + D * ks.length
  | [], _, _, _, _ => by simp
  | k :: ks, cf, C, D, h => by
    have h1 := h k (by simp)
    have ih := sum_le_wtR' ks cf C D (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- a kid's nice tree is no larger than the nice tree of the node -/
theorem niceOf_kid_size {X : Finset ℕ} {ks : List RT} {k : RT} (hk : k ∈ ks) :
    (niceOf k).size ≤ (niceOf (.node X ks)).size := by
  rcases ks with _ | ⟨k0, ks'⟩
  · simp at hk
  · have h1 := niceOf_size_cons X k0 ks'
    have h2 : (conv X (niceOf k)).size + 1 ≤ ((k0 :: ks').map (fun k' => (conv X (niceOf k')).size + 1)).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem (f := fun k' => (conv X (niceOf k')).size + 1) hk)
    have h3 := conv_size_kid X k
    omega

section niceOf
variable {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ') (B : ℕ)
include hΔ

theorem bag_runs (hB : 1000 < B) : ∀ nt : NT,
    Runs Δ' B fBagNT [toVal nt] (toVal nt.bag) (100 * (nt.inner + 1) ^ 2) := by
  intro nt
  induction nt with
  | leaf =>
    refine Runs.mk (hΔ _ _ Δ_bagNT) ?_
    ev_start
    · ev_run
    · simp [NT.inner, NT.bag]
  | intro v c ih =>
    have h1 := Lib3.insert_runs (ext3 hΔ) B v c.bag
    have hc := card_bag_le_inner c
    refine Runs.mk (hΔ _ _ Δ_bagNT) ?_
    simp only [NT.bag, toVal_nt_intro]
    ev_start
    · ev_run
    · simp only [NT.inner]; nlinarith
  | forget v c ih =>
    have h1 := Lib3.erase_runs (ext3 hΔ) B v c.bag
    have hc := card_bag_le_inner c
    refine Runs.mk (hΔ _ _ Δ_bagNT) ?_
    simp only [NT.bag, toVal_nt_forget]
    ev_start
    · ev_run
    · simp only [NT.inner]; nlinarith
  | join a b iha ihb =>
    refine Runs.mk (hΔ _ _ Δ_bagNT) ?_
    simp only [NT.bag, toVal_nt_join]
    have h3 : (a.inner + 1) ^ 2 + 3 ≤ (a.inner + b.inner + 1 + 1) ^ 2 := by
      nlinarith [Nat.zero_le a.inner, Nat.zero_le b.inner]
    ev_start
    · ev_run
    · simp only [NT.inner]; nlinarith

theorem introMany_runs (hB : 1000 < B) : ∀ (l : List ℕ) (t : NT),
    Runs Δ' B fIntroMany [toVal l, toVal t] (toVal (introMany l t)) (40 * l.length + 10) := by
  intro l
  induction l with
  | nil =>
    intro t
    refine Runs.mk (hΔ _ _ Δ_introMany) ?_
    ev_start
    · ev_run
    · simp
  | cons x l ih =>
    intro t
    have h1 := ih (NT.intro x t)
    refine Runs.mk (hΔ _ _ Δ_introMany) ?_
    rw [introMany_cons]
    ev_start
    · ev_run
    · simp; omega

theorem forgetMany_runs (hB : 1000 < B) : ∀ (l : List ℕ) (t : NT),
    Runs Δ' B fForgetMany [toVal l, toVal t] (toVal (forgetMany l t)) (40 * l.length + 10) := by
  intro l
  induction l with
  | nil =>
    intro t
    refine Runs.mk (hΔ _ _ Δ_forgetMany) ?_
    ev_start
    · ev_run
    · simp
  | cons x l ih =>
    intro t
    have h1 := ih (NT.forget x t)
    refine Runs.mk (hΔ _ _ Δ_forgetMany) ?_
    rw [forgetMany_cons]
    ev_start
    · ev_run
    · simp; omega

theorem joinFold_runs (hB : 1000 < B) : ∀ (ts : List NT) (t : NT),
    Runs Δ' B fJoinFold [toVal ts, toVal t] (toVal (ts.foldl NT.join t)) (40 * ts.length + 10) := by
  intro ts
  induction ts with
  | nil =>
    intro t
    refine Runs.mk (hΔ _ _ Δ_joinFold) ?_
    ev_start
    · ev_run
    · simp
  | cons x ts ih =>
    intro t
    have h1 := ih (NT.join t x)
    refine Runs.mk (hΔ _ _ Δ_joinFold) ?_
    rw [List.foldl_cons]
    ev_start
    · ev_run
    · simp; omega

theorem conv_runs (hB : 1000 < B) (X : Finset ℕ) (t : NT) (s : ℕ) (hX : X.card ≤ s) (ht : t.inner ≤ s) :
    Runs Δ' B fConv [toVal X, toVal t] (toVal (conv X t)) (500 * (s + 1) ^ 2) := by
  have hb := bag_runs hΔ B hB t
  have hbc := card_bag_le_inner t
  have hc1 : (X \ t.bag).card ≤ s := le_trans (Finset.card_le_card Finset.sdiff_subset) hX
  have hc2 : (t.bag \ X).card ≤ s := le_trans (Finset.card_le_card Finset.sdiff_subset) (le_trans hbc ht)
  have hd1 : Runs Δ' B Lib3.fDiffS [toVal X, toVal t.bag] (toVal ((X \ t.bag).sort (· ≤ ·)))
      (60 * (X.card + t.bag.card) + 20) := Lib3.sdiff_runs (ext3 hΔ) B X t.bag
  have hd2 : Runs Δ' B Lib3.fDiffS [toVal t.bag, toVal X] (toVal ((t.bag \ X).sort (· ≤ ·)))
      (60 * (t.bag.card + X.card) + 20) := Lib3.sdiff_runs (ext3 hΔ) B t.bag X
  have hf := forgetMany_runs hΔ B hB ((t.bag \ X).sort (· ≤ ·)) t
  rw [Finset.length_sort] at hf
  have hi := introMany_runs hΔ B hB ((X \ t.bag).sort (· ≤ ·)) (forgetMany ((t.bag \ X).sort (· ≤ ·)) t)
  rw [Finset.length_sort] at hi
  refine Runs.mk (hΔ _ _ Δ_conv) ?_
  unfold conv
  ev_start
  · ev_run
  · nlinarith

theorem niceOf_runs (hB : 1000 < B) (s : ℕ) : ∀ t : RT, sz t ≤ s → (niceOf t).size ≤ s →
    Runs Δ' B fNiceOf [toVal t] (toVal (niceOf t)) (1000 * (s + 1) ^ 2 * wtR t) := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro hs hn
    rw [sz_rt_node'] at hs
    have hXs : sz X ≤ s := by omega
    have hXc : X.card ≤ s := le_trans (by rw [sz_finset]; omega) hXs
    have hks : sz ks ≤ s := by omega
    have hkid : ∀ k ∈ ks, sz k ≤ s := fun k hk => le_trans (sz_le_of_mem hk) hks
    have hkn : ∀ k ∈ ks, (niceOf k).size ≤ s := fun k hk => le_trans (niceOf_kid_size hk) hn
    have hc647 : fConvNice < B := by show 647 < B; omega
    have hP : 1 ≤ (s + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hf : ∀ k ∈ ks, Runs Δ' B fConvNice [toVal X, toVal k] (toVal (conv X (niceOf k)))
        (1000 * (s + 1) ^ 2 * wtR k + (500 * (s + 1) ^ 2 + 10)) := by
      intro k hk
      have h1 := ih k hk (hkid k hk) (hkn k hk)
      have hin : (niceOf k).inner ≤ s := by
        have := (inner_lt_size (niceOf k)).1; have := hkn k hk; omega
      have h2 := conv_runs hΔ B hB X (niceOf k) s hXc hin
      refine Runs.mk (hΔ _ _ Δ_convNice) ?_
      ev_start
      · ev_run
      · omega
    have hmap := map_runs (ext1 hΔ) B fConvNice (toVal X) (fun k => conv X (niceOf k))
      (fun k => 1000 * (s + 1) ^ 2 * wtR k + (500 * (s + 1) ^ 2 + 10)) ks hf
    have hsum := sum_le_wtR' ks (fun k => 1000 * (s + 1) ^ 2 * wtR k + (500 * (s + 1) ^ 2 + 10))
      (1000 * (s + 1) ^ 2) (500 * (s + 1) ^ 2 + 10) (fun k _ => le_refl _)
    have hlen := length_le_sz ks
    have hw := sum_wtR ks
    have hwn := wtR_node X ks
    rcases ks with _ | ⟨k, ks'⟩
    · have hi : Runs Δ' B fIntroMany [toVal X, toVal NT.leaf] (toVal (introMany (X.sort (· ≤ ·)) NT.leaf))
          (40 * X.card + 10) := by
        have := introMany_runs hΔ B hB (X.sort (· ≤ ·)) NT.leaf
        rw [Finset.length_sort] at this
        exact this
      refine Runs.mk (hΔ _ _ Δ_niceOf) ?_
      rw [niceOf_node]
      simp only [List.map_nil, toVal_rt] at hmap ⊢
      ev_start
      · ev_run
      · rw [hwn]
        simp only [List.map_nil, List.sum_nil, List.length_nil] at *
        nlinarith
    · have hj := joinFold_runs hΔ B hB (ks'.map (fun k' => conv X (niceOf k'))) (conv X (niceOf k))
      rw [List.length_map] at hj
      refine Runs.mk (hΔ _ _ Δ_niceOf) ?_
      rw [niceOf_node]
      simp only [List.map_cons, toVal_rt] at hmap ⊢
      ev_start
      · ev_run
      · rw [hwn]
        simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum hmap hw hlen hs ⊢
        nlinarith

end niceOf

end E6a
end Lax117284Proofs.Treewidth.Fun
