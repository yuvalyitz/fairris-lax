import Lax117284Proofs.Treewidth.Chars.TablesJoin
import Lax117284Proofs.Treewidth.Chars.CountTables

/-!
# Size bounds (WP P1), part 1: counting trees by their number of runs

`CountCard` counts the well-formed characteristics via the bracket word `enc`; the count there uses the global bound
`count ≤ runBound |B|`.  Here the same injection is used with an arbitrary bound `m` on the number of runs and *no*
`Wf`/`Conn` hypothesis (only `Good B`, `maxEntry ≤ kmax`): the number of such trees is at most
`(2^{2b+2kmax+4})^{2m}` (`ncard_good_le`), and any duplicate-free list of them has at most `cbound b kmax m` elements.
This is what bounds `joinKids` (whose kids are *not* `Wf B`, but are `Good B`).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- `2^{(2b+2kmax+4)·2m}`: the crude bound on the number of `Good B` trees with entries `≤ kmax` and `≤ m` runs. -/
def cbound (b kmax m : ℕ) : ℕ := 2 ^ ((2 * b + 2 * kmax + 4) * (2 * m))

theorem cbound_mono {b b' k k' m m' : ℕ} (hb : b ≤ b') (hk : k ≤ k') (hm : m ≤ m') :
    cbound b k m ≤ cbound b' k' m' := by
  unfold cbound
  apply Nat.pow_le_pow_right (by norm_num)
  exact Nat.mul_le_mul (by omega) (by omega)

theorem charBound_eq_cbound (b kmax : ℕ) : charBound b kmax = cbound b kmax (runBound b) := by
  unfold charBound cbound runBound
  congr 1
  ring

theorem alph_le (b k : ℕ) : (2 ^ b * (typicalSeqs k).card + 1 + 1) ≤ 2 ^ (2 * b + 2 * k + 4) := by
  have hs := card_typicalSeqs_le k
  have hX : 2 ^ b ≤ 4 ^ b := Nat.pow_le_pow_left (by norm_num) b
  have hX1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hY : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have hs' : (typicalSeqs k).card ≤ 3 * 4 ^ k := by omega
  have hPQ : 2 ^ (2 * b + 2 * k + 4) = 4 ^ b * 4 ^ k * 16 := by
    rw [pow_add, pow_add, pow_mul, pow_mul]; norm_num
  rw [hPQ]
  have h2 : 2 ^ b * (typicalSeqs k).card ≤ 4 ^ b * (3 * 4 ^ k) := Nat.mul_le_mul hX hs'
  have h3 : 1 ≤ 4 ^ b * 4 ^ k := Nat.mul_le_mul (le_trans hX1 hX) hY
  nlinarith

theorem good_maps (B : Finset ℕ) (kmax m : ℕ) :
    Set.MapsTo enc {t : CT | Good B t ∧ t.maxEntry ≤ kmax ∧ t.count ≤ m}
      ↑(listsLE (charAlph B kmax) (2 * m)) := by
  intro t ht
  obtain ⟨hg, hm, hc⟩ := ht
  rw [Finset.mem_coe, mem_listsLE, enc_length]
  exact ⟨by omega, enc_mem_alph t hg hm⟩

theorem ncard_good_le (B : Finset ℕ) (kmax m : ℕ) :
    {t : CT | Good B t ∧ t.maxEntry ≤ kmax ∧ t.count ≤ m}.ncard ≤ cbound B.card kmax m := by
  have hfin : (↑(listsLE (charAlph B kmax) (2 * m)) : Set (List Tok)).Finite := Finset.finite_toSet _
  have h1 : {t : CT | Good B t ∧ t.maxEntry ≤ kmax ∧ t.count ≤ m}.ncard ≤
      (↑(listsLE (charAlph B kmax) (2 * m)) : Set (List Tok)).ncard :=
    Set.ncard_le_ncard_of_injOn enc (good_maps B kmax m) enc_injective.injOn hfin
  rw [Set.ncard_coe_finset] at h1
  refine le_trans h1 (le_trans (card_listsLE _ _) ?_)
  rw [card_charAlph]
  unfold cbound
  calc (2 ^ B.card * (typicalSeqs kmax).card + 1 + 1) ^ (2 * m)
      ≤ (2 ^ (2 * B.card + 2 * kmax + 4)) ^ (2 * m) := Nat.pow_le_pow_left (alph_le _ _) _
    _ = _ := by rw [← pow_mul]

/-- A duplicate-free list of `Good B` trees with entries `≤ kmax` and `≤ m` runs is short. -/
theorem length_le_of_nodup {B : Finset ℕ} {kmax m : ℕ} {l : List CT} (hnd : l.Nodup)
    (h : ∀ c ∈ l, Good B c ∧ c.maxEntry ≤ kmax ∧ c.count ≤ m) : l.length ≤ cbound B.card kmax m := by
  have h1 : l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
  have h2 : ((l.toFinset : Finset CT) : Set CT) ⊆ {t : CT | Good B t ∧ t.maxEntry ≤ kmax ∧ t.count ≤ m} := by
    intro c hc
    exact h c (List.mem_toFinset.1 hc)
  have h3 : l.toFinset.card ≤ {t : CT | Good B t ∧ t.maxEntry ≤ kmax ∧ t.count ≤ m}.ncard := by
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard h2 ?_
    refine Set.Finite.subset (Set.Finite.of_injOn (f := enc) (good_maps B kmax m) enc_injective.injOn
      (Finset.finite_toSet _)) ?_
    exact fun _ h => h
  exact le_trans (h1 ▸ h3) (ncard_good_le B kmax m)

/-! ## list-length helpers -/

theorem length_flatMap_le {α β : Type} {l : List α} {f : α → List β} {n : ℕ} (h : ∀ x ∈ l, (f x).length ≤ n) :
    (l.flatMap f).length ≤ l.length * n := by
  rw [List.length_flatMap]
  have := List.sum_le_card_nsmul (l.map fun a => (f a).length) n (by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact h a ha)
  simpa using this

theorem length_flatMap_eq {α β : Type} {l : List α} {f : α → List β} {n : ℕ} (h : ∀ x ∈ l, (f x).length = n) :
    (l.flatMap f).length = l.length * n := by
  rw [List.length_flatMap]
  have : l.map (fun a => (f a).length) = l.map (fun _ => n) := List.map_congr_left h
  rw [this]
  simp

end Lax117284Proofs.Treewidth.Chars
