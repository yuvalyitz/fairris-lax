import Lax117284Proofs.Treewidth.Chars.CountRuns
import Lax117284Proofs.Treewidth.Chars.Alg
import Lax117284Proofs.Treewidth.Seq.Count
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Option

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
