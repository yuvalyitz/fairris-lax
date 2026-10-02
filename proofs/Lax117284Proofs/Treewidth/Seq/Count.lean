import Lax117284Proofs.Treewidth.Seq.Structure
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Lemma 3.5: the number of typical sequences (Bodlaender–Kloks)

`typicalSeqs L` is the finite set of non-empty typical sequences with entries in `{0, …, L}`
(the sequences `τ a` for non-empty `a` over `{0, …, L}`).  It is computable: all lists over
`{0, …, L}` of length `≤ 2 L + 1` are enumerated (this is complete by Lemma 3.3 (ii)) and
filtered by `typical l = l`.

`card_typicalSeqs_le : 3 * (typicalSeqs L).card ≤ 8 * 4 ^ L` (the paper: at most `8/3 · 2^{2L}`).
The proof follows the paper's idea: a non-empty normal form `n` contains its minimum `m` exactly
once, `n = P ++ m :: Q`, or its maximum exactly once; then `n` is determined by `m` together with
the *sets* of values of `P` and `Q` (uniqueness of spirals), which gives an injection into a set
of cardinality `Σ_m 4^{L-m}` (resp. `Σ_M 4^M`).
-/

namespace Lax117284Proofs.Treewidth.Seq

/-! ### The enumeration -/

/-- All lists of length exactly `n` over `{0, …, L}`. -/
def listsLen (L : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | n + 1 => ((Finset.range (L + 1)) ×ˢ listsLen L n).image (fun p => p.1 :: p.2)

theorem mem_listsLen {L n : ℕ} {l : List ℕ} :
    l ∈ listsLen L n ↔ l.length = n ∧ ∀ x ∈ l, x ≤ L := by
  induction n generalizing l with
  | zero =>
    simp only [listsLen, Finset.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.1 h
  | succ n ih =>
    simp only [listsLen, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
    constructor
    · rintro ⟨a, t, ⟨ha, ht⟩, rfl⟩
      obtain ⟨h1, h2⟩ := ih.1 ht
      refine ⟨by simp [h1], ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · exact h2 x hx
    · rintro ⟨h1, h2⟩
      cases l with
      | nil => simp at h1
      | cons a t =>
        refine ⟨a, t, ⟨?_, ih.2 ⟨by simpa using h1, fun x hx => h2 x (by simp [hx])⟩⟩, rfl⟩
        have := h2 a (by simp); omega

/-- The non-empty typical sequences with entries in `{0, …, L}`. -/
def typicalSeqs (L : ℕ) : Finset (List ℕ) :=
  ((Finset.range (2 * L + 2)).biUnion (listsLen L)).filter (fun l => l ≠ [] ∧ typical l = l)

/-- Membership in `typicalSeqs`. -/
theorem mem_typicalSeqs {L : ℕ} {l : List ℕ} :
    l ∈ typicalSeqs L ↔ l ≠ [] ∧ (∀ x ∈ l, x ≤ L) ∧ typical l = l := by
  unfold typicalSeqs
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range, mem_listsLen]
  constructor
  · rintro ⟨⟨n, -, -, hb⟩, h1, h2⟩; exact ⟨h1, hb, h2⟩
  · rintro ⟨h1, hb, h2⟩
    refine ⟨⟨l.length, ?_, rfl, hb⟩, h1, h2⟩
    have := typical_length_le' hb
    rw [h2] at this; omega

/-- The typical sequences over `{0, …, L}` are exactly the `τ a`, `a ≠ []` over `{0, …, L}`. -/
theorem mem_typicalSeqs_iff_exists {L : ℕ} {l : List ℕ} :
    l ∈ typicalSeqs L ↔ ∃ a : List ℕ, a ≠ [] ∧ (∀ x ∈ a, x ≤ L) ∧ typical a = l := by
  rw [mem_typicalSeqs]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨l, h1, h2, h3⟩
  · rintro ⟨a, h1, h2, rfl⟩
    exact ⟨typical_ne_nil h1, (typical_upper_iff a L).2 h2, typical_typical a⟩

theorem nf_of_mem_typicalSeqs {L : ℕ} {l : List ℕ} (h : l ∈ typicalSeqs L) : NF l :=
  isTypical_iff_nf.1 (mem_typicalSeqs.1 h).2.2

/-! ### The injection -/

/-- The code of a normal form whose minimum is unique: `(m, set of P, set of Q)`. -/
def RelMin (n : List ℕ) (c : Σ _ : ℕ, Finset ℕ × Finset ℕ) : Prop :=
  ∃ P m Q, n = P ++ m :: Q ∧ (∀ x ∈ P, m < x) ∧ (∀ x ∈ Q, m < x) ∧
    c = ⟨m, (P.toFinset, Q.toFinset)⟩

/-- The code of a normal form whose maximum is unique. -/
def RelMax (n : List ℕ) (c : Σ _ : ℕ, Finset ℕ × Finset ℕ) : Prop :=
  ∃ P M Q, n = P ++ M :: Q ∧ (∀ x ∈ P, x < M) ∧ (∀ x ∈ Q, x < M) ∧
    c = ⟨M, (P.toFinset, Q.toFinset)⟩

theorem nf_split_left {P Q : List ℕ} {m : ℕ} (h : NF (P ++ m :: Q)) : NF (P ++ [m]) := by
  have : P ++ m :: Q = (P ++ [m]) ++ Q := by simp
  rw [this] at h; exact h.append_left

theorem nf_split_right {P Q : List ℕ} {m : ℕ} (h : NF (P ++ m :: Q)) : NF (Q.reverse ++ [m]) := by
  have := nf_reverse h.append_right
  simpa using this

theorem code_eq {m m' : ℕ} {a b a' b' : Finset ℕ}
    (h : (⟨m, (a, b)⟩ : Σ _ : ℕ, Finset ℕ × Finset ℕ) = ⟨m', (a', b')⟩) :
    m = m' ∧ a = a' ∧ b = b' := by
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 h
  have h3 := eq_of_heq h2
  simp only [Prod.mk.injEq] at h3
  exact ⟨h1, h3.1, h3.2⟩

theorem mem_iff_of_toFinset_eq {u u' : List ℕ} (h : u.toFinset = u'.toFinset) (x : ℕ) :
    x ∈ u ↔ x ∈ u' := by
  rw [← List.mem_toFinset, ← List.mem_toFinset, h]

theorem relMin_subsingleton {n n' : List ℕ} {c : Σ _ : ℕ, Finset ℕ × Finset ℕ}
    (h : NF n) (h' : NF n') (r : RelMin n c) (r' : RelMin n' c) : n = n' := by
  obtain ⟨P, m, Q, rfl, hP, hQ, rfl⟩ := r
  obtain ⟨P', m', Q', rfl, hP', hQ', hc⟩ := r'
  obtain ⟨rfl, hc1, hc2⟩ := code_eq hc
  have e1 : P = P' :=
    spiral_unique_gt (nf_split_left h) (nf_split_left h') hP hP'
      (mem_iff_of_toFinset_eq hc1)
  have e2 : Q.reverse = Q'.reverse :=
    spiral_unique_gt (nf_split_right h) (nf_split_right h')
      (fun x hx => hQ x (List.mem_reverse.1 hx)) (fun x hx => hQ' x (List.mem_reverse.1 hx))
      (fun x => by
        rw [List.mem_reverse, List.mem_reverse]; exact mem_iff_of_toFinset_eq hc2 x)
  rw [e1, List.reverse_inj.1 e2]

theorem relMax_subsingleton {n n' : List ℕ} {c : Σ _ : ℕ, Finset ℕ × Finset ℕ}
    (h : NF n) (h' : NF n') (r : RelMax n c) (r' : RelMax n' c) : n = n' := by
  obtain ⟨P, m, Q, rfl, hP, hQ, rfl⟩ := r
  obtain ⟨P', m', Q', rfl, hP', hQ', hc⟩ := r'
  obtain ⟨rfl, hc1, hc2⟩ := code_eq hc
  have e1 : P = P' :=
    spiral_unique_lt (nf_split_left h) (nf_split_left h') hP hP'
      (mem_iff_of_toFinset_eq hc1)
  have e2 : Q.reverse = Q'.reverse :=
    spiral_unique_lt (nf_split_right h) (nf_split_right h')
      (fun x hx => hQ x (List.mem_reverse.1 hx)) (fun x hx => hQ' x (List.mem_reverse.1 hx))
      (fun x => by
        rw [List.mem_reverse, List.mem_reverse]; exact mem_iff_of_toFinset_eq hc2 x)
  rw [e1, List.reverse_inj.1 e2]

/-- Codes with unique minimum `m`: `m ≤ L`, both sets inside `(m, L]`. -/
def codesMin (L : ℕ) : Finset (Σ _ : ℕ, Finset ℕ × Finset ℕ) :=
  (Finset.range (L + 1)).sigma
    (fun m => (Finset.Ioc m L).powerset ×ˢ (Finset.Ioc m L).powerset)

/-- Codes with unique maximum `M ≤ L`: both sets inside `[0, M)`. -/
def codesMax (L : ℕ) : Finset (Σ _ : ℕ, Finset ℕ × Finset ℕ) :=
  (Finset.range (L + 1)).sigma
    (fun M => (Finset.range M).powerset ×ˢ (Finset.range M).powerset)

theorem geom4 (L : ℕ) : 3 * ∑ i ∈ Finset.range (L + 1), 4 ^ i + 1 = 4 ^ (L + 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, mul_add, pow_succ 4 (L + 1)]
    generalize 4 ^ (L + 1) = t at *
    omega

theorem card_codesMax (L : ℕ) : 3 * (codesMax L).card + 1 = 4 ^ (L + 1) := by
  unfold codesMax
  rw [Finset.card_sigma]
  have : ∀ M ∈ Finset.range (L + 1),
      ((Finset.range M).powerset ×ˢ (Finset.range M).powerset).card = 4 ^ M := by
    intro M _
    rw [Finset.card_product, Finset.card_powerset, Finset.card_range, ← mul_pow]
    rfl
  rw [Finset.sum_congr rfl this]
  exact geom4 L

theorem card_codesMin (L : ℕ) : 3 * (codesMin L).card + 1 = 4 ^ (L + 1) := by
  unfold codesMin
  rw [Finset.card_sigma]
  have : ∀ m ∈ Finset.range (L + 1),
      ((Finset.Ioc m L).powerset ×ˢ (Finset.Ioc m L).powerset).card = 4 ^ (L + 1 - 1 - m) := by
    intro m _
    rw [Finset.card_product, Finset.card_powerset, Nat.card_Ioc, ← mul_pow]
    congr 1
  rw [Finset.sum_congr rfl this, Finset.sum_range_reflect (fun i => 4 ^ i) (L + 1)]
  exact geom4 L

/-- The relation between a typical sequence and its code. -/
def CodeRel (n : List ℕ) : (Σ _ : ℕ, Finset ℕ × Finset ℕ) ⊕ (Σ _ : ℕ, Finset ℕ × Finset ℕ) → Prop :=
  Sum.elim (RelMin n) (RelMax n)

/-- **Lemma 3.5** (counting typical sequences): at most `8/3 · 4^L` (the paper: `8/3 · 2^{2L}`). -/
theorem card_typicalSeqs_le (L : ℕ) : 3 * (typicalSeqs L).card ≤ 8 * 4 ^ L := by
  have hcard : (typicalSeqs L).card ≤ ((codesMin L).disjSum (codesMax L)).card := by
    apply Finset.card_le_card_of_forall_subsingleton CodeRel
    · intro n hn
      have hmem := mem_typicalSeqs.1 hn
      have hnf := nf_of_mem_typicalSeqs hn
      rcases nf_extreme_decomp hnf hmem.1 with ⟨P, m, Q, rfl, hP, hQ⟩ | ⟨P, M, Q, rfl, hP, hQ⟩
      · refine ⟨Sum.inl ⟨m, (P.toFinset, Q.toFinset)⟩, ?_, P, m, Q, rfl, hP, hQ, rfl⟩
        rw [Finset.inl_mem_disjSum]
        unfold codesMin
        have hmL := hmem.2.1 m (by simp)
        rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_product, Finset.mem_powerset,
          Finset.mem_powerset]
        refine ⟨by show m < L + 1; omega, ?_, ?_⟩
        · intro x hx
          rw [List.mem_toFinset] at hx
          rw [Finset.mem_Ioc]; exact ⟨hP x hx, hmem.2.1 x (by simp [hx])⟩
        · intro x hx
          rw [List.mem_toFinset] at hx
          rw [Finset.mem_Ioc]; exact ⟨hQ x hx, hmem.2.1 x (by simp [hx])⟩
      · refine ⟨Sum.inr ⟨M, (P.toFinset, Q.toFinset)⟩, ?_, P, M, Q, rfl, hP, hQ, rfl⟩
        rw [Finset.inr_mem_disjSum]
        unfold codesMax
        have hML := hmem.2.1 M (by simp)
        rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_product, Finset.mem_powerset,
          Finset.mem_powerset]
        refine ⟨by show M < L + 1; omega, ?_, ?_⟩
        · intro x hx
          rw [List.mem_toFinset] at hx
          rw [Finset.mem_range]; exact hP x hx
        · intro x hx
          rw [List.mem_toFinset] at hx
          rw [Finset.mem_range]; exact hQ x hx
    · intro c _ a ha a' ha'
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨ha1', ha2'⟩ := ha'
      rcases c with c | c
      · exact relMin_subsingleton (nf_of_mem_typicalSeqs ha1) (nf_of_mem_typicalSeqs ha1') ha2 ha2'
      · exact relMax_subsingleton (nf_of_mem_typicalSeqs ha1) (nf_of_mem_typicalSeqs ha1') ha2 ha2'
  rw [Finset.card_disjSum] at hcard
  have h1 := card_codesMin L
  have h2 := card_codesMax L
  have h3 := pow_succ 4 L
  generalize 4 ^ L = t at *
  generalize 4 ^ (L + 1) = s at *
  omega

/-! ### Remark 3.4: the bound of Lemma 3.3 (ii) is sharp

The sequence `… (L-2) 2 (L-1) 1 L 0 L 1 (L-1) 2 (L-2) …` is a normal form of length `2 L + 1`
with maximum `L`.  Position `i ≤ 2 L` has distance `d = |i - L|` from the centre and value
`d / 2` if `d` is even, `L - (d - 1) / 2` if `d` is odd. -/

/-- The value at distance `d` from the centre. -/
def zzv (L d : ℕ) : ℕ := if d % 2 = 0 then d / 2 else L - (d - 1) / 2

/-- The value at position `i` (`0 ≤ i ≤ 2 L`). -/
def zz (L i : ℕ) : ℕ := if i ≤ L then zzv L (L - i) else zzv L (i - L)

/-- The sharp example of Remark 3.4. -/
def sharp (L : ℕ) : List ℕ := (List.range (2 * L + 1)).map (zz L)

theorem sharp_length (L : ℕ) : (sharp L).length = 2 * L + 1 := by simp [sharp]

theorem ent_sharp {L i : ℕ} (h : i ≤ 2 * L) : ent (sharp L) i = zz L i := by
  rw [ent_eq_getElem (by simp [sharp]; omega)]
  simp [sharp]

theorem zz_le {L i : ℕ} (h : i ≤ 2 * L) : zz L i ≤ L := by
  unfold zz zzv; split_ifs <;> omega

theorem zz_ne {L i : ℕ} (h : i + 1 ≤ 2 * L) : zz L i ≠ zz L (i + 1) := by
  unfold zz zzv; split_ifs <;> omega

theorem zz_left {L i : ℕ} (h : i + 2 ≤ L) :
    (zz L i < zz L (i + 1) ∧ zz L (i + 2) < zz L (i + 1) ∧
      zz L (i + 1) - zz L i < zz L (i + 1) - zz L (i + 2)) ∨
    (zz L (i + 1) < zz L i ∧ zz L (i + 1) < zz L (i + 2) ∧
      zz L i - zz L (i + 1) < zz L (i + 2) - zz L (i + 1)) := by
  unfold zz zzv; split_ifs <;> omega

theorem zz_right {L i : ℕ} (h : L ≤ i) (h2 : i + 2 ≤ 2 * L) :
    (zz L i < zz L (i + 1) ∧ zz L (i + 2) < zz L (i + 1) ∧
      zz L (i + 1) - zz L (i + 2) < zz L (i + 1) - zz L i) ∨
    (zz L (i + 1) < zz L i ∧ zz L (i + 1) < zz L (i + 2) ∧
      zz L (i + 2) - zz L (i + 1) < zz L i - zz L (i + 1)) := by
  unfold zz zzv; split_ifs <;> omega

theorem zz_zig {L i : ℕ} (h : i + 2 ≤ 2 * L) :
    (zz L i < zz L (i + 1) ∧ zz L (i + 2) < zz L (i + 1)) ∨
    (zz L (i + 1) < zz L i ∧ zz L (i + 1) < zz L (i + 2)) := by
  unfold zz zzv; split_ifs <;> omega

theorem arith_end {a b c e : ℕ}
    (h : (a < b ∧ c < b ∧ b - a < b - c) ∨ (b < a ∧ b < c ∧ a - b < c - b))
    (hb : InR b a e) (hc : InR c a e) : False := by
  unfold InR at hb hc; omega

/-- **Remark 3.4**: `sharp L` is a normal form. -/
theorem nf_sharp (L : ℕ) : NF (sharp L) := by
  rw [nf_iff]
  constructor
  · rintro k ⟨hk, he⟩
    rw [sharp_length] at hk
    rw [ent_sharp (by omega), ent_sharp (by omega)] at he
    exact zz_ne (by omega) he
  · rintro k j ⟨hkj, hj, hz⟩
    rw [sharp_length] at hj
    have e := fun m (h1 : k < m) (h2 : m < j) => hz m h1 h2
    have hv : ∀ m, m ≤ 2 * L → ent (sharp L) m = zz L m := fun m hm => ent_sharp hm
    by_cases h2 : j = k + 2
    · subst h2
      have := e (k + 1) (by omega) (by omega)
      rw [hv _ (by omega), hv _ (by omega), hv _ (by omega)] at this
      have := zz_zig (L := L) (i := k) (by omega)
      unfold InR at *; omega
    · have hb1 := e (k + 1) (by omega) (by omega)
      have hb2 := e (k + 2) (by omega) (by omega)
      have hb3 := e (j - 1) (by omega) (by omega)
      have hb4 := e (j - 2) (by omega) (by omega)
      rw [hv _ (by omega), hv _ (by omega), hv _ (by omega)] at hb1 hb2 hb3 hb4
      by_cases hL : k + 2 ≤ L
      · exact arith_end (zz_left hL) hb1 hb2
      · have hj2 : j - 2 + 2 = j := by omega
        have hj1 : j - 2 + 1 = j - 1 := by omega
        have hr := zz_right (L := L) (i := j - 2) (by omega) (by omega)
        rw [hj2, hj1] at hr
        exact arith_end (a := zz L j) (b := zz L (j - 1)) (c := zz L (j - 2)) (e := zz L k)
          (by omega) hb3.symm hb4.symm

theorem maxOf_sharp (L : ℕ) : maxOf (sharp L) = L := by
  apply le_antisymm
  · apply maxOf_le
    intro x hx
    simp only [sharp, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact zz_le (by omega)
  · rcases Nat.eq_zero_or_pos L with rfl | hL
    · exact Nat.zero_le _
    · have : zz L (L + 1) = L := by unfold zz zzv; split_ifs <;> omega
      have hm : zz L (L + 1) ∈ sharp L := by
        simp only [sharp, List.mem_map, List.mem_range]
        exact ⟨L + 1, by omega, rfl⟩
      have := le_maxOf hm
      omega

/-- **Remark 3.4**: Lemma 3.3 (ii) is sharp for every `L`. -/
theorem typical_sharp (L : ℕ) :
    typical (sharp L) = sharp L ∧ maxOf (sharp L) = L ∧ (sharp L).length = 2 * L + 1 :=
  ⟨typical_of_nf (nf_sharp L), maxOf_sharp L, sharp_length L⟩

end Lax117284Proofs.Treewidth.Seq
