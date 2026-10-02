import Lax117284Proofs.Treewidth.Fun.E2Defs

/-!
# WP E2 (1): arithmetic of tree recursions, size lemmas, `verts`, `keyLe`, `sortKids`

* `wt c = 2·count c - 1`; `tree_step` : the potential argument that turns a per-node cost `C·(m+1)·s^e`
  (`m` = number of kids) into the whole-tree bound `C·wt c·s^e ≤ 2C·count·s^e`;
* `card_verts_le : |verts c| ≤ sz c`, `sz_relE_le`, `sz_norm_le`;
* `verts_runs`, `keyLe_runs`, `sortKids_runs`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT Lib1

/-! ## potentials -/

def wt (c : CT) : ℕ := 2 * c.count - 1

theorem count_ge_one (c : CT) : 1 ≤ c.count := by cases c; simp only [count]; omega

theorem wt_node (S : Finset ℕ) (y : List ℕ) (ks : List CT) : wt (node S y ks) = 2 * countL ks + 1 := by
  simp [wt, count]; omega

theorem sum_wt : ∀ ks : List CT, (ks.map wt).sum + ks.length = 2 * countL ks
  | [] => by simp [countL]
  | k :: ks => by
    have h := sum_wt ks
    have h1 := count_ge_one k
    simp only [List.map_cons, List.sum_cons, List.length_cons, countL, wt]
    omega

theorem sum_le_aux {α : Type} (l : List α) (u : α → ℕ) (C e sc : ℕ) (wf : α → ℕ)
    (h : ∀ a ∈ l, u a ≤ sc) :
    (l.map (fun a => C * wf a * (u a) ^ e)).sum ≤ C * sc ^ e * (l.map wf).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have h2 : u a ^ e ≤ sc ^ e := Nat.pow_le_pow_left (h a (List.mem_cons_self ..)) e
    simp only [List.map_cons, List.sum_cons]
    have h3 : C * wf a * u a ^ e ≤ C * sc ^ e * wf a := by
      calc C * wf a * u a ^ e = C * (wf a) * u a ^ e := rfl
        _ ≤ C * wf a * sc ^ e := Nat.mul_le_mul_left _ h2
        _ = C * sc ^ e * wf a := by ring
    nlinarith

/-- The potential argument: kids' bounds `C·wt k·(u k)^e` plus the local `C·(m+1)·sc^e` fit in `C·wt c·sc^e`. -/
theorem tree_step (ks : List CT) (u : CT → ℕ) (C e sc : ℕ) (h : ∀ k ∈ ks, u k ≤ sc) :
    (ks.map (fun k => C * wt k * (u k) ^ e)).sum + C * (ks.length + 1) * sc ^ e ≤
      C * (2 * countL ks + 1) * sc ^ e := by
  have h1 := sum_le_aux ks u C e sc wt h
  have h2 := sum_wt ks
  have h3 : C * sc ^ e * (ks.map wt).sum + C * (ks.length + 1) * sc ^ e = C * (2 * countL ks + 1) * sc ^ e := by
    rw [← h2]; ring
  omega

/-! ## sizes -/

theorem sz_finset_card (S : Finset ℕ) : S.card ≤ sz S := by rw [sz_finset]; omega

theorem sz_ct_node' (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    sz (node S y ks) = sz S + sz y + sz ks + 2 := by rw [sz_ct_node]; omega

theorem card_vertsL_le (ks : List CT) (h : ∀ k ∈ ks, (verts k).card ≤ sz k) : (vertsL ks).card ≤ sz ks := by
  induction ks with
  | nil => simp [vertsL]
  | cons k ks ih =>
    have h1 := h k (by simp)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [sz_cons]
    simp only [vertsL]
    have := Finset.card_union_le (verts k) (vertsL ks)
    omega

theorem card_verts_le (c : CT) : (verts c).card ≤ sz c := by
  induction c using CT.ind with
  | h S y ks ih =>
    have h1 := card_vertsL_le ks ih
    have h2 := Finset.card_union_le S (vertsL ks)
    have h3 := sz_finset_card S
    rw [sz_ct_node']
    have : verts (node S y ks) = S ∪ vertsL ks := rfl
    rw [this]
    have := sz_pos y
    omega

theorem card_vertsL_le' (ks : List CT) : (vertsL ks).card ≤ sz ks :=
  card_vertsL_le ks (fun k _ => card_verts_le k)

theorem sz_le_of_mem_kids {k : CT} {S : Finset ℕ} {y : List ℕ} {ks : List CT} (h : k ∈ ks) :
    sz k < sz (node S y ks) := by
  have := sz_le_of_mem h
  rw [sz_ct_node']
  have := sz_pos S; have := sz_pos y
  omega

theorem sz_S_le (S : Finset ℕ) (y : List ℕ) (ks : List CT) : sz S < sz (node S y ks) := by
  rw [sz_ct_node']; have := sz_pos y; have := sz_pos ks; omega

theorem sz_y_le (S : Finset ℕ) (y : List ℕ) (ks : List CT) : sz y < sz (node S y ks) := by
  rw [sz_ct_node']; have := sz_pos S; have := sz_pos ks; omega

theorem sz_ks_le (S : Finset ℕ) (y : List ℕ) (ks : List CT) : sz ks < sz (node S y ks) := by
  rw [sz_ct_node']; have := sz_pos S; have := sz_pos y; omega

/-! ## `Ext` plumbing -/

section ext
variable {rid : ℕ} {Δ' : ℕ → Option Tm}

theorem ext1 (hΔ : e2Δ rid ⊑ Δ') : Lib1.Δ ⊑ Δ' := Ext.trans Lib.ext1 (Ext.trans (ext_lib rid) hΔ)
theorem ext2 (hΔ : e2Δ rid ⊑ Δ') : Lib2.Δ ⊑ Δ' := Ext.trans Lib.ext2 (Ext.trans (ext_lib rid) hΔ)
theorem ext3 (hΔ : e2Δ rid ⊑ Δ') : Lib3.Δ ⊑ Δ' := Ext.trans Lib.ext3 (Ext.trans (ext_lib rid) hΔ)
theorem ext4 (hΔ : e2Δ rid ⊑ Δ') : Lib4.Δ ⊑ Δ' := Ext.trans Lib.ext4 (Ext.trans (ext_lib rid) hΔ)
end ext

/-! ## `verts` -/

section verts
variable {rid : ℕ} {Δ' : ℕ → Option Tm} (hΔ : e2Δ rid ⊑ Δ') (B : ℕ)
include hΔ

theorem vertsL_runs (ks : List CT) (cv : CT → ℕ) (s : ℕ) (hs : (vertsL ks).card ≤ s)
    (hB : (ks.map cv).sum + ks.length * (120 * s + 40) + 10 + 8 * s + 8 < B)
    (hf : ∀ k ∈ ks, Runs Δ' B fVerts [toVal k] (toVal (verts k)) (cv k)) :
    Runs Δ' B fVertsL [toVal ks] (toVal (vertsL ks)) ((ks.map cv).sum + ks.length * (120 * s + 40) + 10) := by
  induction ks with
  | nil =>
    refine Runs.mk (hΔ _ _ (Δ_vertsL rid)) ?_
    simp only [vertsL, toVal_empty_finset]
    ev_start
    · ev_run
    · simp
  | cons k ks ih =>
    have hsub : vertsL ks ⊆ vertsL (k :: ks) := Finset.subset_union_right
    have hsub' : verts k ⊆ vertsL (k :: ks) := Finset.subset_union_left
    have hs1 : (vertsL ks).card ≤ s := le_trans (Finset.card_le_card hsub) hs
    have hs2 : (verts k).card ≤ s := le_trans (Finset.card_le_card hsub') hs
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hB
    have ih := ih hs1 (by nlinarith [Nat.zero_le (ks.length * (120 * s + 40))])
      (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    have h1 := hf k (List.mem_cons_self ..)
    have h2 := Lib3.union_runs (ext3 hΔ) B (verts k) (vertsL ks)
    refine Runs.mk (hΔ _ _ (Δ_vertsL rid)) ?_
    simp only [vertsL]
    ev_start
    · ev_run
    · simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith [Nat.zero_le (ks.length * (120 * s + 40))]

theorem verts_runs (c : CT) (hB : 300 * (2 * count c) * sz c + 300 < B) :
    Runs Δ' B fVerts [toVal c] (toVal (verts c)) (220 * wt c * sz c) := by
  induction c using CT.ind with
  | h S y ks ih =>
    have hwt := wt_node S y ks
    have hcs := card_vertsL_le' ks
    have hsz := sz_ks_le S y ks
    have hSz := sz_S_le S y ks
    have hcard := card_verts_le (node S y ks)
    have hcnt := count_ge_one (node S y ks)
    have hcnode : count (node S y ks) = 1 + countL ks := rfl
    have hvl := vertsL_runs hΔ B ks (fun k => 220 * wt k * sz k) (sz ks) hcs (by
        have := tree_step ks sz 220 1 (sz (node S y ks)) (fun k hk => (sz_le_of_mem_kids hk).le)
        simp only [pow_one] at this
        have h4 : ks.length ≤ sz ks := length_le_sz ks
        have h5 := sz_pos ks
        nlinarith [Nat.zero_le (ks.length * sz ks), Nat.zero_le (countL ks)])
      (fun k hk => ih k hk (by
        have h6 : count k ≤ count (node S y ks) := by
          have := count_le_countL_of_mem hk; rw [hcnode]; omega
        have h7 := sz_le_of_mem_kids (S := S) (y := y) hk
        nlinarith [Nat.zero_le (count k), Nat.zero_le (sz k)]))
    have h2 := Lib3.union_runs (ext3 hΔ) B S (vertsL ks)
    refine Runs.mk (hΔ _ _ (Δ_verts rid)) ?_
    have hv : verts (node S y ks) = S ∪ vertsL ks := rfl
    rw [hv]
    simp only [toVal_ct]
    ev_start
    · ev_run
    · have hts := tree_step ks sz 220 1 (sz (node S y ks)) (fun k hk => (sz_le_of_mem_kids hk).le)
      simp only [pow_one] at hts
      have h5 : ks.length * (120 * sz ks + 40) ≤ ks.length * (120 * sz (node S y ks)) :=
        Nat.mul_le_mul_left _ (by omega)
      have h6 := sz_finset_card S
      rw [hwt]
      nlinarith

end verts

/-! ## `keyLe`, `sortKids` -/

theorem finset_shape (T : Finset ℕ) :
    (T = ∅ ∧ toVal T = Val.nat 0 ∧ T.min = ⊤) ∨
    (∃ m r, toVal T = Val.cons (Val.nat m) r ∧ T.min = (m : WithTop ℕ)) := by
  by_cases h : T = ∅
  · subst h; left; simp
  · right
    have hne : T.Nonempty := Finset.nonempty_iff_ne_empty.2 h
    have hcard : 0 < (T.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]; exact Finset.card_pos.2 hne
    have h0 := @Finset.min'_eq_sorted_zero _ _ T hne
    have h1 := Finset.coe_min' hne
    generalize hs : T.sort (· ≤ ·) = l at hcard
    cases l with
    | nil => simp at hcard
    | cons m r =>
      refine ⟨m, toVal r, ?_, ?_⟩
      · rw [toVal_finset, hs]; rfl
      · rw [← h1, h0]
        simp [hs]

section key
variable {rid : ℕ} {Δ' : ℕ → Option Tm} (hΔ : e2Δ rid ⊑ Δ') (B : ℕ)
include hΔ

theorem verts_runs_le (c : CT) (s : ℕ) (hc : sz c ≤ s) (hB : 1000 * (s + 1) ^ 2 < B) :
    Runs Δ' B fVerts [toVal c] (toVal (verts c)) (440 * (s + 1) ^ 2) := by
  have h1 := count_le_sz c
  have h2 : wt c ≤ 2 * count c := by unfold wt; omega
  have h3 : 220 * wt c * sz c ≤ 440 * (s + 1) ^ 2 := by
    have : count c * sz c ≤ (s + 1) ^ 2 := by nlinarith [Nat.zero_le (sz c)]
    nlinarith [Nat.zero_le (wt c), Nat.zero_le (sz c)]
  refine (verts_runs hΔ B c ?_).mono h3
  have : count c * sz c ≤ (s + 1) ^ 2 := by nlinarith [Nat.zero_le (sz c)]
  nlinarith

theorem keyLe_runs (S : Finset ℕ) (a b : CT) (s : ℕ) (hS : sz S ≤ s) (ha : sz a ≤ s) (hb : sz b ≤ s)
    (hB : 1000 * (s + 1) ^ 2 + 100 < B) :
    Runs Δ' B fKeyLe [toVal S, toVal a, toVal b] (toVal (decide (key S a ≤ key S b))) (1000 * (s + 1) ^ 2) := by
  have hsq : 1 ≤ (s + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hva := verts_runs_le hΔ B a s ha (by omega)
  have hvb := verts_runs_le hΔ B b s hb (by omega)
  have hda := Lib3.sdiff_runs (ext3 hΔ) B (verts a) S
  have hdb := Lib3.sdiff_runs (ext3 hΔ) B (verts b) S
  have ca := card_verts_le a
  have cb := card_verts_le b
  have cS := sz_finset_card S
  have hda' : Runs Δ' B Lib3.fDiffS [toVal (verts a), toVal S] (toVal (verts a \ S)) (60 * (2 * s) + 20) :=
    hda.mono (by omega)
  have hdb' : Runs Δ' B Lib3.fDiffS [toVal (verts b), toVal S] (toVal (verts b \ S)) (60 * (2 * s) + 20) :=
    hdb.mono (by omega)
  clear hda hdb
  refine Runs.mk (hΔ _ _ (Δ_keyLe rid)) ?_
  rcases finset_shape (verts a \ S) with ⟨he1, hv1, hm1⟩ | ⟨m1, r1, hv1, hm1⟩ <;>
  rcases finset_shape (verts b \ S) with ⟨he2, hv2, hm2⟩ | ⟨m2, r2, hv2, hm2⟩ <;>
  rw [hv1] at hda' <;> rw [hv2] at hdb'
  · have : decide (key S a ≤ key S b) = true := by simp [key, hm1, hm2]
    rw [this]
    ev_start
    · ev_run
    · nlinarith
  · have : decide (key S a ≤ key S b) = false := by simp [key, hm1, hm2]
    rw [this]
    ev_start
    · ev_run
    · nlinarith
  · have : decide (key S a ≤ key S b) = true := by simp [key, hm1, hm2]
    rw [this]
    ev_start
    · ev_run
    · nlinarith
  · by_cases hle : m1 ≤ m2
    · have : decide (key S a ≤ key S b) = true := by simp [key, hm1, hm2, hle]
      rw [this]
      have h' : ¬ m2 < m1 := by omega
      ev_start
      · ev_run
      · nlinarith
    · have : decide (key S a ≤ key S b) = false := by simp [key, hm1, hm2, hle]
      rw [this]
      have h' : m2 < m1 := by omega
      ev_start
      · ev_run
      · nlinarith

theorem sortKids_runs (S : Finset ℕ) (ks : List CT) (s : ℕ) (hS : sz S ≤ s) (hks : sz ks ≤ s)
    (hB : 1200 * (s + 1) ^ 4 < B) :
    Runs Δ' B fSortKids [toVal S, toVal ks] (toVal (sortKids S ks)) (1100 * (s + 1) ^ 4) := by
  have hsq : 1 ≤ (s + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hs4 : (s + 1) ^ 4 = (s + 1) ^ 2 * (s + 1) ^ 2 := by ring
  have hf : ∀ x ∈ ks, ∀ y ∈ ks, Runs Δ' B fKeyLe [toVal S, toVal x, toVal y]
      (toVal (decide (key S x ≤ key S y))) (1000 * (s + 1) ^ 2) := fun x hx y hy =>
    keyLe_runs hΔ B S x y s hS (le_trans (sz_le_of_mem hx) hks) (le_trans (sz_le_of_mem hy) hks) (by nlinarith)
  have h := Lib2.mergeSort_runs (ext2 hΔ) B fKeyLe (toVal S) (fun a b => decide (key S a ≤ key S b)) (1000 * (s + 1) ^ 2)
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; exact le_trans h1 h2)
    (by intro a b; simpa using le_total (key S a) (key S b)) ks hf
  have hl : ks.length ≤ s := le_trans (length_le_sz ks) hks
  have hl2 : (ks.length + 1) ^ 2 ≤ (s + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hlt : fKeyLe < B := by
    show 162 < B
    nlinarith
  refine Runs.mk (hΔ _ _ (Δ_sortKids rid)) ?_
  unfold sortKids
  ev_start
  · ev_run
  · nlinarith

end key

end E2
end Lax117284Proofs.Treewidth.Fun
