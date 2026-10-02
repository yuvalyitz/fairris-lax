import Lax117284Proofs.Treewidth.Size.Alph
import Lax117284Proofs.Treewidth.Chars.IntroPlansMem

/-!
# Size bounds (WP P1), part 3: the number of introduce plans

For a run tree `t` with `Good B t` and `maxEntry t ≤ kmax` (so every run sequence has length `≤ Y := 2 kmax + 1`),
with `K := 4 kmax + 4 = 2Y + 2`:

* `winPlans v lo t` has at most `K^(2·count t − 1)` elements (`kidChoices v ks`: at most `K^(2·countL ks)`);
* `wtopPlans v t` has at most `(2Y+1)·K^(2·count t − 1)`;
* `allChains S N` has at most `(2^|S| + 1)^(|S|+2)`; `attachPlans v N t` at most `(2Y+1)` times that;
* `introPlans v N t` has at most `count t · A` elements, `A = (2Y+1)(K^(2M) + (2^b+1)^(b+2))` when `count t ≤ M`,
  `|S| ≤ b` for all labels.

With `M = runBound b`, this is `≤ 2^(64 (b+kmax+2)^3)` (`introPlans_length_le`).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

namespace CT

theorem count_pos (t : CT) : 1 ≤ count t := by
  cases t with
  | node S y ks => simp [count]

theorem count_le_countL_of_mem : ∀ {ks : List CT} {k : CT}, k ∈ ks → count k ≤ countL ks
  | [], k, h => by simp at h
  | k' :: ks, k, h => by
    simp only [countL]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := count_le_countL_of_mem h
      omega

/-- The run sequences of a `Good`, `≤ kmax`-bounded run have length `≤ 2 kmax + 1`. -/
theorem y_length_le {B S : Finset ℕ} {y : List ℕ} {ks : List CT} {kmax : ℕ} (hg : Good B (node S y ks))
    (hm : maxEntry (node S y ks) ≤ kmax) : y.length ≤ 2 * kmax + 1 := by
  have h1 : ∀ x ∈ y, x ≤ kmax := ((maxEntry_le_iff).1 hm).1
  have := typical_length_le' h1
  rwa [hg.typical_eq] at this

theorem kids_good {B S : Finset ℕ} {y : List ℕ} {ks : List CT} {kmax : ℕ} (hg : Good B (node S y ks))
    (hm : maxEntry (node S y ks) ≤ kmax) :
    (∀ k ∈ ks, Good B k) ∧ (∀ k ∈ ks, maxEntry k ≤ kmax) :=
  ⟨hg.kids, ((maxEntry_le_iff).1 hm).2⟩

theorem pow_step {K c : ℕ} (hK : 2 ≤ K) (hc : 1 ≤ c) : 1 + K ^ (2 * c - 1) ≤ K ^ (2 * c) := by
  have h1 : 1 ≤ K ^ (2 * c - 1) := Nat.one_le_pow _ _ (by omega)
  have h2 : K ^ (2 * c) = K * K ^ (2 * c - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [h2]
  nlinarith

theorem pow_step2 {K n Y : ℕ} (hK : K = 2 * Y + 2) : 2 * Y + K ^ (2 * n) ≤ K ^ (2 * n + 1) := by
  have h1 : 1 ≤ K ^ (2 * n) := Nat.one_le_pow _ _ (by omega)
  rw [pow_succ]
  generalize K ^ (2 * n) = P at h1 ⊢
  rw [hK]
  nlinarith

mutual
theorem winPlans_length_le_rec (v kmax : ℕ) (B : Finset ℕ) : ∀ (lo : ℕ) (t : CT), Good B t → maxEntry t ≤ kmax →
    (winPlans v lo t).length ≤ (4 * kmax + 4) ^ (2 * count t - 1)
  | lo, node S y ks, hg, hm => by
    obtain ⟨hgk, hmk⟩ := kids_good hg hm
    have hy := y_length_le hg hm
    have hkc := kidChoices_length_le_rec v kmax B ks hgk hmk
    have hcount : 2 * count (node S y ks) - 1 = 2 * countL ks + 1 := by simp only [count]; omega
    rw [hcount]
    have h := pow_step2 (K := 4 * kmax + 4) (n := countL ks) (Y := 2 * kmax + 1) (by ring)
    simp only [winPlans, List.length_append, List.length_map, List.length_range']
    omega
theorem kidChoices_length_le_rec (v kmax : ℕ) (B : Finset ℕ) : ∀ (ks : List CT), (∀ k ∈ ks, Good B k) →
    (∀ k ∈ ks, maxEntry k ≤ kmax) → (kidChoices v ks).length ≤ (4 * kmax + 4) ^ (2 * countL ks)
  | [], _, _ => by simp [kidChoices, countL]
  | k :: ks, hg, hm => by
    have h1 := winPlans_length_le_rec v kmax B 0 k (hg k (by simp)) (hm k (by simp))
    have h2 := kidChoices_length_le_rec v kmax B ks (fun k' hk' => hg k' (List.mem_cons_of_mem _ hk'))
      (fun k' hk' => hm k' (List.mem_cons_of_mem _ hk'))
    have h3 : 1 + (4 * kmax + 4) ^ (2 * count k - 1) ≤ (4 * kmax + 4) ^ (2 * count k) :=
      pow_step (by omega) (count_pos k)
    have h4 : (kidChoices v (k :: ks)).length =
        (1 + (winPlans v 0 k).length) * (kidChoices v ks).length := by
      simp only [kidChoices]
      rw [length_flatMap_eq (n := (kidChoices v ks).length)]
      · simp only [List.length_cons, List.length_map]; rw [Nat.add_comm]
      · intro o _; simp
    rw [h4, countL, mul_add, pow_add]
    exact Nat.mul_le_mul (le_trans (by omega) h3) h2
end

theorem winPlans_length_le_pair : (type_of% @winPlans_length_le_rec) ∧ (type_of% @kidChoices_length_le_rec) :=
  ⟨@winPlans_length_le_rec, @kidChoices_length_le_rec⟩

theorem winPlans_length_le : type_of% @winPlans_length_le_rec := winPlans_length_le_pair.1

theorem wtopPlans_length_le (v kmax : ℕ) (B : Finset ℕ) {t : CT} (hg : Good B t) (hm : maxEntry t ≤ kmax) :
    (wtopPlans v t).length ≤ (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * count t - 1) := by
  cases t with
  | node S y ks =>
    have hy := y_length_le hg hm
    have hW : ∀ lo, (winPlans v lo (node S y ks)).length ≤ (4 * kmax + 4) ^ (2 * count (node S y ks) - 1) :=
      fun lo => winPlans_length_le v kmax B lo _ hg hm
    set W := (4 * kmax + 4) ^ (2 * count (node S y ks) - 1) with hWdef
    have h1 : ((List.range y.length).flatMap fun f =>
        (winPlans v f (node S y ks)).map fun p =>
          (Plan.top (some (Cut.t1 f)) p.1, node S (y.take (f + 1)) [p.2.1], p.2.2)).length ≤ y.length * W := by
      refine le_trans (length_flatMap_le (n := W) ?_) (by simp)
      intro f _
      simpa using hW f
    have h2 : ((List.range (y.length - 1)).flatMap fun f =>
        (winPlans v (f + 1) (node S y ks)).map fun p =>
          (Plan.top (some (Cut.t2 f)) p.1, node S (y.take (f + 1)) [p.2.1], p.2.2)).length ≤ (y.length - 1) * W := by
      refine le_trans (length_flatMap_le (n := W) ?_) (by simp)
      intro f _
      simpa using hW (f + 1)
    have h0 := hW 0
    simp only [wtopPlans, List.length_append, List.length_map]
    have h3 : y.length * W ≤ (2 * kmax + 1) * W := Nat.mul_le_mul_right _ hy
    have h4 : (y.length - 1) * W ≤ (2 * kmax + 1) * W := Nat.mul_le_mul_right _ (by omega)
    nlinarith

/-! ## `allChains` -/

theorem chainsGo_length_le (cands : List (Finset ℕ)) : ∀ (fuel : ℕ) (bound : Finset ℕ) (chain : List (Finset ℕ)),
    (chainsGo cands fuel bound chain).length ≤ (cands.length + 1) ^ (fuel + 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro bound chain
    simp only [chainsGo, List.length_map]
    have := List.length_filter_le (fun x => decide (x ⊆ bound)) cands
    simpa using le_trans this (by omega)
  | succ f ih =>
    intro bound chain
    simp only [chainsGo, List.length_append, List.length_map]
    have h1 := List.length_filter_le (fun x => decide (x ⊆ bound)) cands
    have h2 : ((cands.filter (fun X => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound)))).flatMap
        (fun X => chainsGo cands f X (chain ++ [X]))).length ≤ cands.length * (cands.length + 1) ^ (f + 1) := by
      refine le_trans (length_flatMap_le (n := (cands.length + 1) ^ (f + 1)) (fun X _ => ih X _)) ?_
      exact Nat.mul_le_mul_right _ (List.length_filter_le _ _)
    have h3 : cands.length ≤ (cands.length + 1) ^ (f + 1) :=
      le_trans (Nat.le_succ _) (Nat.le_self_pow (by omega) _)
    have h4 : (cands.length + 1) ^ (f + 1 + 1) = cands.length * (cands.length + 1) ^ (f + 1) +
        (cands.length + 1) ^ (f + 1) := by ring
    omega

theorem chainCands_length (S N : Finset ℕ) : (chainCands S N).length = 2 ^ (S \ N).card := by
  simp [chainCands, List.length_sublists]

theorem allChains_length_le {S : Finset ℕ} (N : Finset ℕ) {b : ℕ} (hS : S.card ≤ b) :
    (allChains S N).length ≤ (2 ^ b + 1) ^ (b + 2) := by
  unfold allChains
  refine le_trans (chainsGo_length_le _ _ _ _) ?_
  rw [chainCands_length]
  have h1 : 2 ^ (S \ N).card ≤ 2 ^ b :=
    Nat.pow_le_pow_right (by norm_num) (le_trans (Finset.card_le_card Finset.sdiff_subset) hS)
  calc (2 ^ (S \ N).card + 1) ^ (S.card + 1 + 1) ≤ (2 ^ b + 1) ^ (S.card + 1 + 1) :=
        Nat.pow_le_pow_left (by omega) _
    _ ≤ (2 ^ b + 1) ^ (b + 2) := Nat.pow_le_pow_right (by positivity) (by omega)

theorem attachPlans_length_le (v kmax : ℕ) (B : Finset ℕ) (N : Finset ℕ) {b : ℕ} {t : CT} (hg : Good B t)
    (hm : maxEntry t ≤ kmax) (hb : t.S.card ≤ b) :
    (attachPlans v N t).length ≤ (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3) := by
  cases t with
  | node S y ks =>
    have hy := y_length_le hg hm
    have hc := allChains_length_le (S := S) N (b := b) hb
    simp only [attachPlans]
    refine le_trans (length_flatMap_le (n := 4 * kmax + 3) ?_) (Nat.mul_le_mul_right _ hc)
    intro cm _
    simp only [List.length_cons, List.length_append, List.length_map, List.length_range]
    omega

/-! ## `introPlans` -/

theorem introKids_length_le (v : ℕ) (N S : Finset ℕ) (y : List ℕ) (f : CT → ℕ) :
    ∀ (ks pre : List CT), (∀ k ∈ ks, (introPlans v N k).length ≤ f k) →
      (introKids v N S y pre ks).length ≤ (ks.map f).sum
  | [], _, _ => by simp [introKids]
  | k :: post, pre, h => by
    simp only [introKids, List.length_append, List.length_map, List.map_cons, List.sum_cons]
    have h1 := h k (by simp)
    have h2 := introKids_length_le v N S y f post (pre ++ [k]) (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    omega

theorem sum_map_count_le (A : ℕ) : ∀ (ks : List CT), (ks.map (fun k => count k * A)).sum = countL ks * A
  | [] => by simp [countL]
  | k :: ks => by
    simp only [List.map_cons, List.sum_cons, countL, sum_map_count_le A ks]
    ring

/-- **The number of introduce plans**, with the run bound `M` and the label bound `b` as parameters. -/
theorem introPlans_length_le_aux (v kmax : ℕ) (B : Finset ℕ) (N : Finset ℕ) (M b : ℕ)
    (hb : ∀ S : Finset ℕ, S ⊆ B → S.card ≤ b) :
    ∀ (t : CT), Good B t → maxEntry t ≤ kmax → count t ≤ M →
      (introPlans v N t).length ≤ count t * ((4 * kmax + 3) * (4 * kmax + 4) ^ (2 * M) +
        (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3)) := by
  intro t
  induction t using CT.ind with
  | h S y ks ih =>
    intro hg hm hc
    obtain ⟨hgk, hmk⟩ := kids_good hg hm
    set A := (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * M) + (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3) with hA
    have hw := wtopPlans_length_le v kmax B hg hm
    have ha := attachPlans_length_le v kmax B N (b := b) hg hm (hb S hg.label_sub)
    have hpow : (4 * kmax + 4) ^ (2 * count (node S y ks) - 1) ≤ (4 * kmax + 4) ^ (2 * M) :=
      Nat.pow_le_pow_right (by omega) (by have := count_pos (node S y ks); omega)
    have hw' : (wtopPlans v (node S y ks)).length ≤ (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * M) :=
      le_trans hw (Nat.mul_le_mul_left _ hpow)
    have hkids : (introKids v N S y [] ks).length ≤ countL ks * A := by
      have := introKids_length_le v N S y (fun k => count k * A) ks [] (by
        intro k hk
        exact ih k hk (hgk k hk) (hmk k hk)
          (le_trans (count_le_countL_of_mem hk) (by simp only [count] at hc; omega)))
      rwa [sum_map_count_le] at this
    have hcount : count (node S y ks) * A = A + countL ks * A := by
      simp only [count]; ring
    rw [hcount]
    have h1 := List.length_filter_le (fun p : Plan × CT × Finset ℕ => decide (N ⊆ p.2.2))
      (wtopPlans v (node S y ks))
    simp only [introPlans, List.length_append, List.length_map]
    by_cases hNS : N ⊆ S
    · simp only [hNS, if_true, List.length_map]
      omega
    · simp only [hNS, if_false, List.length_nil]
      omega

theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self

theorem four_mul_le (kmax : ℕ) : 4 * kmax + 4 ≤ 2 ^ (kmax + 2) := by
  have := succ_le_two_pow kmax
  rw [pow_add]; omega

theorem intro_exponent_le (b kmax : ℕ) :
    (2 * b + 2) + (kmax + 2) + ((kmax + 2) * (2 * runBound b) + (b + 1) * (b + 2)) + 1 ≤
      64 * (b + kmax + 2) ^ 3 := by
  unfold runBound
  set s := b + kmax + 2 with hs
  have h2 : 2 ≤ s := by omega
  have hb1 : b + 1 ≤ s := by omega
  have hk2 : kmax + 2 ≤ s := by omega
  have hb2 : b + 2 ≤ s := by omega
  have e1 : (kmax + 2) * (2 * ((2 * b + 2) * (2 * b + 2))) ≤ 8 * s ^ 3 := by
    have : (kmax + 2) * (2 * ((2 * b + 2) * (2 * b + 2))) = 8 * ((kmax + 2) * ((b + 1) * (b + 1))) := by ring
    rw [this]
    have h := Nat.mul_le_mul hk2 (Nat.mul_le_mul hb1 hb1)
    have h' : s * (s * s) = s ^ 3 := by ring
    omega
  have e2 : (b + 1) * (b + 2) ≤ s ^ 3 := by
    have := Nat.mul_le_mul hb1 hb2
    have h3 : s ^ 2 ≤ s ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  have e3 : 2 * b + 2 + (kmax + 2) + 1 ≤ 3 * s := by omega
  have e4 : 3 * s ≤ s ^ 3 := by
    have h5 : s * 3 ≤ s * (s * s) := Nat.mul_le_mul_left s (by nlinarith)
    have h' : s * (s * s) = s ^ 3 := by ring
    omega
  omega

/-- **`introPlans_length_le`** (WP P1 (a)): the number of introduce plans of a well-formed characteristic. -/
theorem introPlans_length_le {v : ℕ} {N B : Finset ℕ} {kmax : ℕ} {t : CT} (hw : t.Wf B kmax) :
    (introPlans v N t).length ≤ 2 ^ (64 * (B.card + kmax + 2) ^ 3) := by
  have hb : ∀ S : Finset ℕ, S ⊆ B → S.card ≤ B.card := fun S h => Finset.card_le_card h
  have h := introPlans_length_le_aux v kmax B N (runBound B.card) B.card hb t hw.good hw.bounded hw.count_le
  refine le_trans h ?_
  set b := B.card
  set M := runBound b with hM
  have hM1 : M ≤ 2 ^ (2 * b + 2) := by
    rw [hM]; unfold runBound
    have h1 : (b + 1) ≤ 2 ^ b := succ_le_two_pow b
    have h2 : (2 * b + 2) * (2 * b + 2) = 4 * ((b + 1) * (b + 1)) := by ring
    have h3 : (b + 1) * (b + 1) ≤ 2 ^ b * 2 ^ b := Nat.mul_le_mul h1 h1
    have h4 : 2 ^ (2 * b + 2) = 4 * (2 ^ b * 2 ^ b) := by
      rw [show 2 * b + 2 = b + b + 2 by ring, pow_add, pow_add]; ring
    rw [h2, h4]
    omega
  have hK : (4 * kmax + 4) ^ (2 * M) ≤ 2 ^ ((kmax + 2) * (2 * M)) := by
    rw [pow_mul 2 (kmax + 2) (2 * M)]
    exact Nat.pow_le_pow_left (four_mul_le kmax) _
  have hC : (2 ^ b + 1) ^ (b + 2) ≤ 2 ^ ((b + 1) * (b + 2)) := by
    have : 2 ^ b + 1 ≤ 2 ^ (b + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := b); omega
    calc (2 ^ b + 1) ^ (b + 2) ≤ (2 ^ (b + 1)) ^ (b + 2) := Nat.pow_le_pow_left this _
      _ = _ := by rw [← pow_mul]
  have h34 : 4 * kmax + 3 ≤ 2 ^ (kmax + 2) := le_trans (by omega) (four_mul_le kmax)
  set E1 := (kmax + 2) * (2 * M)
  set E2 := (b + 1) * (b + 2)
  have hA : (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * M) + (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3) ≤
      2 ^ (kmax + 2) * 2 ^ (E1 + E2 + 1) := by
    have a1 : (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * M) ≤ 2 ^ (kmax + 2) * 2 ^ E1 := Nat.mul_le_mul h34 hK
    have a2 : (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3) ≤ 2 ^ E2 * 2 ^ (kmax + 2) := Nat.mul_le_mul hC h34
    have b1 : 2 ^ E1 ≤ 2 ^ (E1 + E2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have b2 : 2 ^ E2 ≤ 2 ^ (E1 + E2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ (E1 + E2 + 1) = 2 * 2 ^ (E1 + E2) := by rw [pow_succ]; ring
    rw [this]
    nlinarith [Nat.mul_le_mul_left (2 ^ (kmax + 2)) b1, Nat.mul_le_mul_left (2 ^ (kmax + 2)) b2]
  calc t.count * ((4 * kmax + 3) * (4 * kmax + 4) ^ (2 * M) + (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3))
      ≤ M * ((4 * kmax + 3) * (4 * kmax + 4) ^ (2 * M) + (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3)) :=
        Nat.mul_le_mul_right _ hw.count_le
    _ ≤ 2 ^ (2 * b + 2) * (2 ^ (kmax + 2) * 2 ^ (E1 + E2 + 1)) := Nat.mul_le_mul hM1 hA
    _ = 2 ^ ((2 * b + 2) + (kmax + 2) + (E1 + E2 + 1)) := by rw [← pow_add, ← pow_add]; congr 1; omega
    _ ≤ 2 ^ (64 * (b + kmax + 2) ^ 3) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have := intro_exponent_le b kmax
      omega

end CT

end Lax117284Proofs.Treewidth.Chars
