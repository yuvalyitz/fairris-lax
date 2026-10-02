import Lax117284Proofs.Treewidth.Size.Alph

/-!
# Size bounds (WP P1), part 2: `joinC`, `joinKids`, `ringTypList`

* `joinC_nodup`  (unconditional): `joinC` produces a duplicate-free list; `joinKids` too;
* `joinC_count`  : every result of `joinC a b` has the shape (number of runs) of `a`;
* `joinC_length_le_good` : for `Good B a`, `Good B b`, `maxEntry a ≤ kmax`:
  `|joinC kmax a b| ≤ cbound |B| kmax (count a)`; likewise `joinKids`;
* `joinC_length_le` : for `Wf B kmax a`, `Wf B kmax b`: `|joinC kmax a b| ≤ charBound |B| kmax ≤ 2^{16 (|B|+kmax+2)^3}`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

namespace CT

theorem joinKids_nodup (kmax : ℕ) : ∀ (ks ks' : List CT), (∀ k ∈ ks, ∀ b, (joinC kmax k b).Nodup) →
    (joinKids kmax ks ks').Nodup
  | [], [], _ => by simp [joinKids]
  | [], _ :: _, _ => by simp [joinKids]
  | _ :: _, [], _ => by simp [joinKids]
  | k :: ks, k' :: ks', h => by
    simp only [joinKids]
    rw [List.nodup_flatMap]
    have hrest := joinKids_nodup kmax ks ks' (fun k1 hk1 => h k1 (List.mem_cons_of_mem _ hk1))
    refine ⟨fun c _ => hrest.map (fun a b hab => by simpa using hab), ?_⟩
    refine (h k (by simp) k').imp ?_
    intro c c' hne
    rw [Function.onFun, List.disjoint_left]
    intro x hx hx'
    obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
    obtain ⟨l', _, hl'⟩ := List.mem_map.1 hx'
    exact hne (List.cons.inj hl'.symm).1

theorem joinC_nodup (kmax : ℕ) : ∀ (a b : CT), (joinC kmax a b).Nodup := by
  intro a
  induction a using CT.ind with
  | h S y ks ih =>
    intro b
    cases b with
    | node S' y' ks' =>
      rw [joinC]
      split_ifs with hc
      · rw [List.nodup_flatMap]
        have hkk := joinKids_nodup kmax ks ks' ih
        refine ⟨fun kk _ => ?_, ?_⟩
        · exact (List.Nodup.filter _ (List.nodup_dedup _)).map (fun a b hab => by simpa using hab)
        · refine hkk.imp ?_
          intro kk kk' hne
          rw [Function.onFun, List.disjoint_left]
          intro x hx hx'
          obtain ⟨d, _, rfl⟩ := List.mem_map.1 hx
          obtain ⟨d', _, hd'⟩ := List.mem_map.1 hx'
          have := CT.node.inj hd'
          exact hne this.2.2.symm
      · exact List.nodup_nil

theorem joinKids_count (kmax : ℕ) : ∀ (ks ks' kk : List CT),
    (∀ k ∈ ks, ∀ b c, c ∈ joinC kmax k b → count c = count k) → kk ∈ joinKids kmax ks ks' →
    countL kk = countL ks
  | [], [], kk, _, h => by
    simp only [joinKids, List.mem_singleton] at h
    subst h; rfl
  | [], _ :: _, kk, _, h => by simp [joinKids] at h
  | _ :: _, [], kk, _, h => by simp [joinKids] at h
  | k :: ks, k' :: ks', kk, hk, h => by
    simp only [joinKids, List.mem_flatMap, List.mem_map] at h
    obtain ⟨c, hc, l, hl, rfl⟩ := h
    have h1 := hk k (by simp) k' c hc
    have h2 := joinKids_count kmax ks ks' l (fun k1 hk1 => hk k1 (List.mem_cons_of_mem _ hk1)) hl
    simp only [countL, h1, h2]

theorem joinC_count (kmax : ℕ) : ∀ (a b c : CT), c ∈ joinC kmax a b → count c = count a := by
  intro a
  induction a using CT.ind with
  | h S y ks ih =>
    intro b c hc
    cases b with
    | node S' y' ks' =>
      rw [joinC] at hc
      split_ifs at hc with hcond
      · rw [List.mem_flatMap] at hc
        obtain ⟨kk, hkk, hc⟩ := hc
        obtain ⟨d, _, rfl⟩ := List.mem_map.1 hc
        have := joinKids_count kmax ks ks' kk ih hkk
        simp only [count, this]
      · simp at hc

theorem cbound_add (b k m₁ m₂ : ℕ) : cbound b k (m₁ + m₂) = cbound b k m₁ * cbound b k m₂ := by
  unfold cbound
  rw [← pow_add]
  congr 1
  ring

theorem joinC_length_le_good {B : Finset ℕ} {kmax : ℕ} {a b : CT} (ha : Good B a) (hb : Good B b) :
    (joinC kmax a b).length ≤ cbound B.card kmax (count a) := by
  refine length_le_of_nodup (joinC_nodup kmax a b) ?_
  intro c hc
  obtain ⟨g, -, m, -⟩ := joinC_aux B kmax a b c ha hb hc
  exact ⟨g, m, (joinC_count kmax a b c hc).le⟩

theorem joinKids_length_le_good {B : Finset ℕ} {kmax : ℕ} : ∀ (ks ks' : List CT), GoodL B ks → GoodL B ks' →
    (joinKids kmax ks ks').length ≤ cbound B.card kmax (countL ks)
  | [], [], _, _ => by simp [joinKids, cbound, countL]
  | [], _ :: _, _, _ => by simp [joinKids]
  | _ :: _, [], _, _ => by simp [joinKids]
  | k :: ks, k' :: ks', ha, hb => by
    simp only [joinKids]
    have h1 := joinC_length_le_good (kmax := kmax) ha.1 hb.1
    have h2 := joinKids_length_le_good (kmax := kmax) ks ks' ha.2 hb.2
    have h3 : ((joinC kmax k k').flatMap (fun c => (joinKids kmax ks ks').map (c :: ·))).length =
        (joinC kmax k k').length * (joinKids kmax ks ks').length := by
      refine length_flatMap_eq ?_
      intro c _
      simp
    rw [h3, countL, cbound_add]
    exact Nat.mul_le_mul h1 h2

/-- **`joinC` on well-formed characteristics**: at most `charBound |B| kmax` results. -/
theorem joinC_length_le_charBound {B : Finset ℕ} {kmax : ℕ} {a b : CT} (ha : Wf B kmax a) (hb : Wf B kmax b) :
    (joinC kmax a b).length ≤ charBound B.card kmax := by
  rw [charBound_eq_cbound]
  exact le_trans (joinC_length_le_good ha.good hb.good) (cbound_mono le_rfl le_rfl ha.count_le)

theorem charBound_le_pow (b k : ℕ) : charBound b k ≤ 2 ^ (16 * (b + k + 2) ^ 3) := by
  unfold charBound
  apply Nat.pow_le_pow_right (by norm_num)
  have h1 : (b + 1) ^ 2 ≤ (b + k + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : b + k + 2 ≤ b + k + 2 := le_rfl
  calc 16 * (b + 1) ^ 2 * (b + k + 2) ≤ 16 * (b + k + 2) ^ 2 * (b + k + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 16 h1) h2
    _ = 16 * (b + k + 2) ^ 3 := by ring

/-- **`joinC_length_le`** (Machine.lean's statement, with the sharper constant 16). -/
theorem joinC_length_le {B : Finset ℕ} {kmax : ℕ} {a b : CT} (ha : Wf B kmax a) (hb : Wf B kmax b) :
    (joinC kmax a b).length ≤ 2 ^ (16 * (B.card + kmax + 2) ^ 3) :=
  le_trans (joinC_length_le_charBound ha hb) (charBound_le_pow _ _)

end CT

end Lax117284Proofs.Treewidth.Chars
