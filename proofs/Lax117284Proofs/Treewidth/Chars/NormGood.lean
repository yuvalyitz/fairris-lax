import Lax117284Proofs.Treewidth.Chars.NormConfl

/-!
# `norm` produces well-formed characteristics (work package C1)

`good_norm : Loc B q → Conn q → Good B (norm q)` — `Loc` is the local part of `Good` that survives relabelling
(labels in `B`, typical non-empty sequences at least `|S|`); the remaining clauses of `Good` (no prunable leaf kid,
single kids change label, strict key order, leaf runs have one entry) are *produced* by `norm`.
`maxEntry_norm_le : maxEntry (norm q) ≤ maxEntry q`.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

namespace CT

mutual
/-- The local shape invariants of `Good` that do not mention the kids' order or pruning. -/
def Loc (B : Finset ℕ) : CT → Prop
  | node S y ks => S ⊆ B ∧ typical y = y ∧ y ≠ [] ∧ (∀ e ∈ y, S.card ≤ e) ∧ LocL B ks
def LocL (B : Finset ℕ) : List CT → Prop
  | [] => True
  | k :: ks => Loc B k ∧ LocL B ks
end

theorem LocL_iff {B : Finset ℕ} {ks : List CT} : LocL B ks ↔ ∀ k ∈ ks, Loc B k := by
  induction ks with
  | nil => simp [LocL]
  | cons k ks ih => simp [LocL, ih]

theorem GoodL_iff {B : Finset ℕ} {ks : List CT} : GoodL B ks ↔ ∀ k ∈ ks, Good B k := by
  induction ks with
  | nil => simp [GoodL]
  | cons k ks ih => simp [GoodL, ih]

mutual
theorem loc_of_good {B : Finset ℕ} : ∀ q : CT, Good B q → Loc B q
  | node S y ks, h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, locL_of_goodL ks h.2.2.2.2.2.2.2.2⟩
theorem locL_of_goodL {B : Finset ℕ} : ∀ ks : List CT, GoodL B ks → LocL B ks
  | [], _ => trivial
  | k :: ks, h => ⟨loc_of_good k h.1, locL_of_goodL ks h.2⟩
end

mutual
theorem loc_relabel_erase {B : Finset ℕ} (x : ℕ) : ∀ q : CT, Loc B q → Loc (B.erase x) (relabel (fun S => S.erase x) q)
  | node S y ks, h => by
    refine ⟨Finset.erase_subset_erase x h.1, h.2.1, h.2.2.1, fun e he => ?_, ?_⟩
    · exact (Finset.card_erase_le).trans (h.2.2.2.1 e he)
    · exact locL_relabel_erase x ks h.2.2.2.2
theorem locL_relabel_erase {B : Finset ℕ} (x : ℕ) : ∀ ks : List CT, LocL B ks →
    LocL (B.erase x) (relabelL (fun S => S.erase x) ks)
  | [], _ => trivial
  | k :: ks, h => ⟨loc_relabel_erase x k h.1, locL_relabel_erase x ks h.2⟩
end

/-- The cut-down sequence of a run is typical. -/
theorem typical_take_one {y : List ℕ} (hy : y ≠ []) : typical (y.take 1) = y.take 1 := by
  cases y with
  | nil => exact absurd rfl hy
  | cons a l => simpa using typical_singleton a

theorem good_normF {B S : Finset ℕ} {y : List ℕ} {F : List CT} (hS : S ⊆ B) (hyt : typical y = y) (hyne : y ≠ [])
    (hge : ∀ e ∈ y, S.card ≤ e) (hF : ∀ n ∈ F, Good B n ∧ ¬ (n.kids = [] ∧ n.S ⊆ S))
    (hd : F.Pairwise (fun a b => key S a ≠ key S b)) : Good B (normF S y F) := by
  match F, hF, hd with
  | [], _, _ =>
    rw [normF_nil]
    refine ⟨hS, typical_take_one hyne, ?_, ?_, fun _ => ?_, by simp, by simp, by simp, trivial⟩
    · cases y with
      | nil => exact absurd rfl hyne
      | cons a l => simp
    · intro e he; exact hge e (List.mem_of_mem_take he)
    · cases y with
      | nil => exact absurd rfl hyne
      | cons a l => simp
  | [k], hF, _ =>
    rw [normF_single]
    obtain ⟨hk, hkp⟩ := hF k (by simp)
    split_ifs with hkS
    · obtain ⟨Sk, yk, kk⟩ := k
      simp only [CT.S] at hkS; subst hkS
      simp only [Good] at hk
      obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, hk9⟩ := hk
      simp only [CT.kids] at hkp
      have hkk : kk ≠ [] := fun e => hkp ⟨e, subset_rfl⟩
      refine ⟨hS, typical_typical _, typical_ne_nil (by simp [hyne]), ?_, fun e => absurd e hkk, hk6, hk7, hk8, hk9⟩
      intro e he
      rcases List.mem_append.1 (mem_of_mem_typical he) with h | h
      · exact hge e h
      · exact hk4 e h
    · refine ⟨hS, hyt, hyne, hge, fun e => by simp at e, ?_, ?_, by simp, ⟨hk, trivial⟩⟩
      · intro j hj hjk; simp at hj; subst hj; exact fun h => hkp ⟨hjk, h⟩
      · intro j hj; have : k = j := by simpa using hj
        subst this; exact hkS
  | a :: b :: t, hF, hd =>
    rw [normF_ge2]
    have hne : sortKids S (a :: b :: t) ≠ [] := sortKids_ne_nil (by simp)
    refine ⟨hS, hyt, hyne, hge, fun e => absurd e hne, ?_, ?_, sortKids_strict hd, ?_⟩
    · intro k hk hkk; rw [mem_sortKids] at hk; exact fun h => (hF k hk).2 ⟨hkk, h⟩
    · intro k hk; have := length_sortKids S (a :: b :: t); rw [hk] at this; simp at this
    · rw [GoodL_iff]; intro k hk; rw [mem_sortKids] at hk; exact (hF k hk).1

mutual
theorem good_norm {B : Finset ℕ} : ∀ q : CT, Loc B q → Conn q → Good B (norm q)
  | node S y ks, h, hc => by
    rw [norm_node']
    apply good_normF h.1 h.2.1 h.2.2.1 h.2.2.2.1
    · intro n hn
      obtain ⟨hn1, hn2⟩ := List.mem_filter.1 hn
      refine ⟨?_, keep_eq_true_iff.1 hn2⟩
      have := goodL_normL ks h.2.2.2.2 hc.1
      rw [normL_eq_map, GoodL_iff] at this
      exact this n hn1
    · exact survivors_keys_distinct hc
theorem goodL_normL {B : Finset ℕ} : ∀ ks : List CT, LocL B ks → ConnL ks → GoodL B (normL ks)
  | [], _, _ => trivial
  | k :: ks, h, hc => ⟨good_norm k h.1 hc.1, goodL_normL ks h.2 hc.2⟩
end

/-! ## the largest entry -/

theorem foldr_max_le_iff {l : List ℕ} {n : ℕ} : l.foldr max 0 ≤ n ↔ ∀ e ∈ l, e ≤ n := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem maxEntryL_le_iff {ks : List CT} {n : ℕ} :
    maxEntryL ks ≤ n ↔ ∀ k ∈ ks, maxEntry k ≤ n := by
  induction ks with
  | nil => simp [maxEntryL]
  | cons k ks ih => simp [maxEntryL, ih]

theorem maxEntry_le_iff {S : Finset ℕ} {y : List ℕ} {ks : List CT} {n : ℕ} :
    maxEntry (node S y ks) ≤ n ↔ (∀ e ∈ y, e ≤ n) ∧ ∀ k ∈ ks, maxEntry k ≤ n := by
  rw [maxEntry, max_le_iff, foldr_max_le_iff, maxEntryL_le_iff]

theorem maxEntry_kid_le {k q : CT} (h : k ∈ q.kids) : maxEntry k ≤ maxEntry q := by
  cases q with
  | node S y ks =>
    have := (maxEntry_le_iff (n := maxEntry (node S y ks))).1 le_rfl
    exact this.2 k h

theorem maxEntry_normF_le {S : Finset ℕ} {y : List ℕ} {K : List CT} {n : ℕ}
    (hy : ∀ e ∈ y, e ≤ n) (hK : ∀ k ∈ K, maxEntry k ≤ n) : maxEntry (normF S y (K.filter (keep S))) ≤ n := by
  have hF : ∀ k ∈ K.filter (keep S), maxEntry k ≤ n := fun k hk => hK k (List.mem_filter.1 hk).1
  generalize K.filter (keep S) = F at hF
  match F, hF with
  | [], _ =>
    rw [normF_nil, maxEntry_le_iff]
    exact ⟨fun e he => hy e (List.mem_of_mem_take he), by simp⟩
  | [k], hF =>
    rw [normF_single]
    split_ifs with hS
    · obtain ⟨Sk, yk, kk⟩ := k
      have hk := maxEntry_le_iff.1 (hF (node Sk yk kk) (by simp))
      rw [maxEntry_le_iff]
      refine ⟨fun e he => ?_, hk.2⟩
      rcases List.mem_append.1 (mem_of_mem_typical he) with h | h
      · exact hy e h
      · exact hk.1 e h
    · rw [maxEntry_le_iff]
      refine ⟨hy, fun j hj => ?_⟩
      simp at hj; subst hj; exact hF _ (by simp)
  | a :: b :: t, hF =>
    rw [normF_ge2, maxEntry_le_iff]
    exact ⟨hy, fun k hk => hF k (mem_sortKids.1 hk)⟩

mutual
theorem maxEntry_norm_le : ∀ q : CT, maxEntry (norm q) ≤ maxEntry q
  | node S y ks => by
    have h := (maxEntry_le_iff (n := maxEntry (node S y ks))).1 le_rfl
    have hL := maxEntryL_norm_le ks
    rw [norm_node']
    apply maxEntry_normF_le h.1
    intro k hk
    obtain ⟨k0, hk0, rfl⟩ := List.mem_map.1 hk
    exact (maxEntry_norm_le_mem ks k0 hk0).trans (h.2 k0 hk0)
theorem maxEntryL_norm_le : ∀ ks : List CT, maxEntryL (normL ks) ≤ maxEntryL ks
  | [] => le_rfl
  | k :: ks => by
    simp only [normL, maxEntryL]
    exact max_le_max (maxEntry_norm_le k) (maxEntryL_norm_le ks)
theorem maxEntry_norm_le_mem : ∀ (ks : List CT), ∀ k ∈ ks, maxEntry (norm k) ≤ maxEntry k
  | [], k, hk => by simp at hk
  | k' :: ks, k, hk => by
    rcases List.mem_cons.1 hk with e | hk
    · rw [e]; exact maxEntry_norm_le k'
    · exact maxEntry_norm_le_mem ks k hk
end

mutual
theorem maxEntry_relabel (f : Finset ℕ → Finset ℕ) : ∀ q : CT, maxEntry (relabel f q) = maxEntry q
  | node S y ks => by simp only [relabel, maxEntry, maxEntryL_relabelL f ks]
theorem maxEntryL_relabelL (f : Finset ℕ → Finset ℕ) : ∀ ks : List CT, maxEntryL (relabelL f ks) = maxEntryL ks
  | [] => rfl
  | k :: ks => by simp only [relabelL, maxEntryL, maxEntry_relabel f k, maxEntryL_relabelL f ks]
end

end CT

end Lax117284Proofs.Treewidth.Chars
