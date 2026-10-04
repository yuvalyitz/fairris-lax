import Lax117284Proofs.Treewidth.Seq.Structure
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Intervals
import Lax117284Proofs.Treewidth.Chars.CountRuns
import Lax117284Proofs.Treewidth.Chars.Alg
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Option

/-! ### `Lax117284Proofs.Treewidth.Seq.Count` -/

section
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

end Lax117284Proofs.Treewidth.Seq

end

/-! ### `Lax117284Proofs.Treewidth.Chars.CountCard` -/

section
/-!
# Counting characteristics (2): the number of well-formed characteristics

`wf_finite` and `card_wf_le : #{t | Wf B kmax t} ≤ charBound |B| kmax`.

A characteristic is written as a **bracket word** over the alphabet `Tok = Option (label × sequence)`:
`enc (node S y ks) = some (S, y) :: (enc ks ++ [none])`, i.e. a run opens with its data and closes with `none`.
This is a prefix code (`enc_prefix`), so `enc` is injective.  A well-formed characteristic has `≤ M = (2b+2)²` runs
(`Wf.count_le`), hence its word has length `≤ 2M`, over the alphabet `none`, or `some (S, y)` with `S ⊆ B` and `y` a
non-empty typical sequence with entries `≤ kmax`.  There are at most `(2^b · (8/3) 4^kmax + 2)^{2M}` such words, and
`2^b·(8/3)·4^kmax + 2 ≤ 2^{2b + 2kmax + 4}` gives `charBound` (with room to spare).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

/-! ## lists of bounded length over a finite alphabet -/

/-- All lists of length `≤ n` over the alphabet `A`. -/
def listsLE {α : Type} [DecidableEq α] (A : Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | n + 1 => insert [] ((A ×ˢ listsLE A n).image (fun p => p.1 :: p.2))

theorem mem_listsLE {α : Type} [DecidableEq α] {A : Finset α} {n : ℕ} {l : List α} :
    l ∈ listsLE A n ↔ l.length ≤ n ∧ ∀ a ∈ l, a ∈ A := by
  induction n generalizing l with
  | zero =>
    simp only [listsLE, Finset.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.1 (by omega)
  | succ n ih =>
    simp only [listsLE, Finset.mem_insert, Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro (rfl | ⟨a, t, ⟨ha, ht⟩, rfl⟩)
      · simp
      · obtain ⟨h1, h2⟩ := ih.1 ht
        refine ⟨by simp; omega, ?_⟩
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ha
        · exact h2 x hx
    · rintro ⟨h1, h2⟩
      cases l with
      | nil => exact Or.inl rfl
      | cons a t =>
        refine Or.inr ⟨a, t, ⟨h2 a (by simp), ih.2 ⟨by simpa using h1, fun x hx => h2 x (by simp [hx])⟩⟩, rfl⟩

theorem card_listsLE {α : Type} [DecidableEq α] (A : Finset α) (n : ℕ) :
    (listsLE A n).card ≤ (A.card + 1) ^ n := by
  induction n with
  | zero => simp [listsLE]
  | succ n ih =>
    have h1 : (listsLE A (n + 1)).card ≤ ((A ×ˢ listsLE A n).image (fun p => p.1 :: p.2)).card + 1 := by
      exact Finset.card_insert_le ([] : List α) ((A ×ˢ listsLE A n).image (fun p => p.1 :: p.2))
    have h2 := Finset.card_image_le (s := A ×ˢ listsLE A n) (f := fun p : α × List α => p.1 :: p.2)
    rw [Finset.card_product] at h2
    have h3 : A.card * (listsLE A n).card ≤ A.card * (A.card + 1) ^ n := Nat.mul_le_mul_left _ ih
    have h4 : 1 ≤ (A.card + 1) ^ n := Nat.one_le_pow _ _ (by omega)
    have h5 : (A.card + 1) ^ (n + 1) = A.card * (A.card + 1) ^ n + (A.card + 1) ^ n := by ring
    omega

/-! ## bracket words of characteristics -/

/-- Tokens: `some (label, sequence)` opens a run, `none` closes it. -/
abbrev Tok := Option (Finset ℕ × List ℕ)

namespace CT

mutual
/-- The bracket word of a characteristic. -/
def enc : CT → List Tok
  | node S y ks => some (S, y) :: (encL ks ++ [none])
def encL : List CT → List Tok
  | [] => []
  | k :: ks => enc k ++ encL ks
end

theorem encL_length : ∀ {ks : List CT}, (∀ k ∈ ks, (enc k).length = 2 * count k) →
    (encL ks).length = 2 * countL ks
  | [], _ => by simp [encL, countL]
  | k :: ks, h => by
    have h1 := h k (by simp)
    have h2 := encL_length (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    simp only [encL, countL, List.length_append]
    omega

theorem enc_length (t : CT) : (enc t).length = 2 * count t := by
  induction t using ind with
  | h S y ks ih =>
    have := encL_length ih
    simp only [enc, count, List.length_cons, List.length_append, List.length_nil]
    omega

theorem enc_ne_nil_some (t : CT) : ∃ a l, enc t = some a :: l := by
  cases t with
  | node S y ks => exact ⟨(S, y), _, rfl⟩

/-- The forest part of the prefix-code property. -/
theorem encL_prefix : ∀ {ks : List CT},
    (∀ k ∈ ks, ∀ (t' : CT) (R R' : List Tok), enc k ++ R = enc t' ++ R' → k = t' ∧ R = R') →
    ∀ (ks' : List CT) (R R' : List Tok), encL ks ++ none :: R = encL ks' ++ none :: R' → ks = ks' ∧ R = R'
  | [], _, ks', R, R', h => by
    cases ks' with
    | nil => simpa [encL] using h
    | cons k' rest' =>
      obtain ⟨a, l, hk'⟩ := enc_ne_nil_some k'
      simp [encL, hk'] at h
  | k :: ks, hP, ks', R, R', h => by
    cases ks' with
    | nil =>
      obtain ⟨a, l, hk⟩ := enc_ne_nil_some k
      simp [encL, hk] at h
    | cons k' ks'' =>
      have h1 : enc k ++ (encL ks ++ none :: R) = enc k' ++ (encL ks'' ++ none :: R') := by
        simpa [encL, List.append_assoc] using h
      obtain ⟨rfl, h2⟩ := hP k (by simp) k' _ _ h1
      obtain ⟨rfl, rfl⟩ := encL_prefix (fun k'' hk'' => hP k'' (List.mem_cons_of_mem _ hk'')) ks'' R R' h2
      exact ⟨rfl, rfl⟩

/-- `enc` is a prefix code. -/
theorem enc_prefix (t : CT) : ∀ (t' : CT) (R R' : List Tok), enc t ++ R = enc t' ++ R' → t = t' ∧ R = R' := by
  induction t using ind with
  | h S y ks ih =>
    intro t' R R' h
    cases t' with
    | node S' y' ks' =>
      simp only [enc, List.cons_append, List.cons.injEq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, h⟩ := h
      have h' : encL ks ++ none :: R = encL ks' ++ none :: R' := by simpa using h
      obtain ⟨rfl, rfl⟩ := encL_prefix ih ks' R R' h'
      exact ⟨rfl, rfl⟩

theorem enc_injective : Function.Injective enc := by
  intro t t' h
  exact (enc_prefix t t' [] [] (by simpa using h)).1

/-! ## the alphabet -/

/-- The tokens that can occur in a well-formed characteristic over `B` with entries `≤ kmax`. -/
def charAlph (B : Finset ℕ) (kmax : ℕ) : Finset Tok :=
  Finset.insertNone (B.powerset ×ˢ typicalSeqs kmax)

theorem card_charAlph (B : Finset ℕ) (kmax : ℕ) :
    (charAlph B kmax).card = 2 ^ B.card * (typicalSeqs kmax).card + 1 := by
  simp [charAlph, Finset.card_insertNone, Finset.card_product, Finset.card_powerset]

theorem encL_mem {ks : List CT} {a : Tok} : a ∈ encL ks ↔ ∃ k ∈ ks, a ∈ enc k := by
  induction ks with
  | nil => simp [encL]
  | cons k ks ih => simp [encL, ih]

theorem le_foldr_max {e : ℕ} : ∀ {y : List ℕ}, e ∈ y → e ≤ y.foldr max 0
  | [], h => by simp at h
  | a :: y, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (le_foldr_max h) (le_max_right _ _)

theorem maxEntry_le_maxEntryL : ∀ {ks : List CT} {k : CT}, k ∈ ks → maxEntry k ≤ maxEntryL ks
  | [], k, h => by simp at h
  | k' :: ks, k, h => by
    simp only [maxEntryL]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (maxEntry_le_maxEntryL h) (le_max_right _ _)

theorem Good.typical_eq {B S : Finset ℕ} {y : List ℕ} {ks : List CT} (h : Good B (.node S y ks)) :
    typical y = y := by
  unfold Good at h; exact h.2.1

theorem Good.seq_ne_nil {B S : Finset ℕ} {y : List ℕ} {ks : List CT} (h : Good B (.node S y ks)) :
    y ≠ [] := by
  unfold Good at h; exact h.2.2.1

theorem enc_mem_alph {B : Finset ℕ} {kmax : ℕ} (t : CT) :
    Good B t → maxEntry t ≤ kmax → ∀ a ∈ enc t, a ∈ charAlph B kmax := by
  induction t using ind with
  | h S y ks ih =>
    intro hg hm a ha
    have hm' : max (y.foldr max 0) (maxEntryL ks) ≤ kmax := hm
    simp only [enc, List.mem_cons, List.mem_append] at ha
    rcases ha with rfl | ha | (rfl | ha)
    · rw [charAlph, Finset.mem_insertNone]
      intro x hx
      rw [Option.mem_def, Option.some.injEq] at hx
      subst hx
      rw [Finset.mem_product, Finset.mem_powerset, mem_typicalSeqs]
      exact ⟨hg.label_sub, hg.seq_ne_nil, fun e he => le_trans (le_foldr_max he) (le_trans (le_max_left _ _) hm'),
        hg.typical_eq⟩
    · obtain ⟨k, hk, hak⟩ := encL_mem.1 ha
      exact ih k hk (hg.kids k hk) (le_trans (maxEntry_le_maxEntryL hk) (le_trans (le_max_right _ _) hm')) a hak
    · rw [charAlph, Finset.mem_insertNone]
      intro x hx
      simp at hx
    · simp at ha

/-! ## the numeric bound -/

theorem card_num (b k s : ℕ) (hs : 3 * s ≤ 8 * 4 ^ k) :
    (2 ^ b * s + 1 + 1) ^ (2 * runBound b) ≤ charBound b k := by
  unfold charBound
  have hX : 2 ^ b ≤ 4 ^ b := Nat.pow_le_pow_left (by norm_num) b
  have hX1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hY : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have hs' : s ≤ 3 * 4 ^ k := by omega
  have hPQ : 2 ^ (2 * b + 2 * k + 4) = 4 ^ b * 4 ^ k * 16 := by
    rw [pow_add, pow_add, pow_mul, pow_mul]; norm_num
  have h1 : 2 ^ b * s + 1 + 1 ≤ 2 ^ (2 * b + 2 * k + 4) := by
    rw [hPQ]
    have h2 : 2 ^ b * s ≤ 4 ^ b * (3 * 4 ^ k) := Nat.mul_le_mul hX hs'
    have h3 : 1 ≤ 4 ^ b * 4 ^ k := Nat.mul_le_mul (le_trans hX1 hX) hY
    nlinarith
  calc (2 ^ b * s + 1 + 1) ^ (2 * runBound b)
      ≤ (2 ^ (2 * b + 2 * k + 4)) ^ (2 * runBound b) := Nat.pow_le_pow_left h1 _
    _ = 2 ^ ((2 * b + 2 * k + 4) * (2 * runBound b)) := by rw [← pow_mul]
    _ = 2 ^ (16 * (b + 1) ^ 2 * (b + k + 2)) := by
      congr 1
      unfold runBound
      ring

end CT

/-! ## the theorems -/

open CT in
theorem wf_maps (B : Finset ℕ) (kmax : ℕ) :
    Set.MapsTo enc {t : CT | CT.Wf B kmax t} ↑(listsLE (charAlph B kmax) (2 * runBound B.card)) := by
  intro t ht
  have ht' : CT.Wf B kmax t := ht
  rw [Finset.mem_coe, mem_listsLE, enc_length]
  refine ⟨?_, enc_mem_alph t ht'.good ht'.bounded⟩
  have := ht'.count_le
  omega

open CT in
theorem wf_finite (B : Finset ℕ) (kmax : ℕ) : {t : CT | CT.Wf B kmax t}.Finite :=
  Set.Finite.of_injOn (wf_maps B kmax) enc_injective.injOn (Finset.finite_toSet _)

open CT in
/-- **The counting bound (paper Lemma 4.1 / 5.3 / A–Z §3.6).** -/
theorem card_wf_le (B : Finset ℕ) (kmax : ℕ) : {t : CT | CT.Wf B kmax t}.ncard ≤ charBound B.card kmax := by
  have h1 : {t : CT | CT.Wf B kmax t}.ncard ≤ (↑(listsLE (charAlph B kmax) (2 * runBound B.card)) : Set (List Tok)).ncard :=
    Set.ncard_le_ncard_of_injOn enc (wf_maps B kmax) enc_injective.injOn (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h1
  refine le_trans h1 (le_trans (card_listsLE _ _) ?_)
  rw [card_charAlph]
  exact card_num B.card kmax _ (card_typicalSeqs_le kmax)

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.CountTables` -/

section
/-!
# Counting characteristics (3): table sizes and the closed form of `charBound`

* `charBound_le : charBound (l+1) (k+1) ≤ 2^(720 l³)` for `k < l`, `1 ≤ l` (the exponent is
  `16 (l+2)² (l+k+4) ≤ 16 · 9 l² · 5 l`);
* `tables_length_le`, `tables_length_le_of_width`: every table has at most `charBound (l+1) (k+1)` entries, because it is
  duplicate-free and consists of well-formed characteristics.  The latter fact (`tables_wf`, preservation of `CT.Wf` by
  `forgetC`/`joinC`/`introC`) is proved elsewhere; here it is the explicit hypothesis `TablesWf`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

/-! ## `charBound` -/

theorem charBound_mono {b b' : ℕ} (k : ℕ) (h : b ≤ b') : charBound b k ≤ charBound b' k := by
  unfold charBound
  apply Nat.pow_le_pow_right (by norm_num)
  have h1 : (b + 1) ^ 2 ≤ (b' + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : b + k + 2 ≤ b' + k + 2 := by omega
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 16 h1) h2

/-! ## tables -/

theorem tables_nodup (adj : Adj) (k : ℕ) (nt : NT) : (tables adj k nt).Nodup := by
  cases nt <;> simp [tables, forgetTable, introTable, joinTable, List.nodup_dedup]

/-- The one fact about tables that the counting needs (`tables_wf` of `proofs-todo/Statements.lean`: `Wf` is
preserved by `forgetC`, `joinC`, `introC`). -/
def TablesWf : Prop :=
  ∀ {adj : Adj} {k : ℕ} {nt : NT}, nt.Good adj → ∀ c ∈ tables adj k nt, CT.Wf nt.bag (k + 1) c

/-- Every table has at most `charBound (ℓ+1) (k+1)` entries (as the lists are duplicate-free). -/
theorem tables_length_le (tables_wf : TablesWf) {adj : Adj} {k l : ℕ} {nt : NT} (hg : nt.Good adj)
    (hb : nt.bag.card ≤ l + 1) :
    (tables adj k nt).length ≤ charBound (l + 1) (k + 1) := by
  have h1 : (tables adj k nt).length = (tables adj k nt).toFinset.card :=
    (List.toFinset_card_of_nodup (tables_nodup adj k nt)).symm
  have h2 : ((tables adj k nt).toFinset : Set CT) ⊆ {t : CT | CT.Wf nt.bag (k + 1) t} := by
    intro c hc
    exact tables_wf hg c (List.mem_toFinset.1 hc)
  have h3 : (tables adj k nt).toFinset.card ≤ {t : CT | CT.Wf nt.bag (k + 1) t}.ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard h2 (wf_finite _ _)
  exact le_trans (h1 ▸ h3) (le_trans (card_wf_le nt.bag (k + 1)) (charBound_mono (k + 1) hb))

theorem bag_card_le_of_width {nt : NT} {l : ℕ} (hw : nt.toRT.Width l) : nt.bag.card ≤ l + 1 :=
  hw nt.bag (by cases nt <;> simp [NT.toRT, RT.bags, NT.bag])

/-- (blueprint `tables_all_length_le`, with the vacuous hypotheses removed) if a nice tree has width `≤ l`, every
table of it is small. -/
theorem tables_length_le_of_width (tables_wf : TablesWf) {adj : Adj} {k l : ℕ} {nt : NT} (hg : nt.Good adj)
    (hw : nt.toRT.Width l) :
    (tables adj k nt).length ≤ charBound (l + 1) (k + 1) :=
  tables_length_le tables_wf hg (bag_card_le_of_width hw)

end Lax117284Proofs.Treewidth.Chars

end
