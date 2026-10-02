import Lax117284Proofs.Treewidth.Size.Tables

/-!
# Size bounds (WP P1), part 6: the size of a characteristic (its cons-tree)

`CT.vsz` is the number of cells of the cons-tree view of a characteristic used by the machine
(`encCT (node S y ks) = cons (list S) (cons (list y) (list of kids))`, a list of length `n` having `2n + 1` cells).
`RB b Y t` says every run has a label of at most `b` vertices and a sequence of at most `Y` entries; then
`vsz t + 1 ≤ count t · (2b + 2Y + 6)` (`vsz_le`).  A `Wf B kmax` characteristic has `count ≤ (2|B|+2)^2`, `Y = 2 kmax + 1`,
so its size is `≤ (2|B|+2)^2 (2|B| + 4 kmax + 8)`, a polynomial in `k` (`Wf.vsz_le`, `tables_vsz_le`).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

namespace CT

mutual
/-- Number of cells of the cons-tree view of a characteristic (mirrors `Val.size (encCT t)` of `Machine.lean`). -/
def vsz : CT → ℕ
  | node S y ks => (2 * S.card + 1) + ((2 * y.length + 1) + vszL ks + 1) + 1
def vszL : List CT → ℕ
  | [] => 1
  | k :: ks => vsz k + vszL ks + 1
end

mutual
/-- Every run has at most `b` label vertices and at most `Y` sequence entries. -/
def RB (b Y : ℕ) : CT → Prop
  | node S y ks => S.card ≤ b ∧ y.length ≤ Y ∧ RBL b Y ks
def RBL (b Y : ℕ) : List CT → Prop
  | [] => True
  | k :: ks => RB b Y k ∧ RBL b Y ks
end

theorem RBL_iff {b Y : ℕ} : ∀ {ks : List CT}, RBL b Y ks ↔ ∀ k ∈ ks, RB b Y k
  | [] => by simp [RBL]
  | k :: ks => by simp [RBL, RBL_iff (ks := ks)]

theorem RB.kids {b Y : ℕ} {S : Finset ℕ} {y : List ℕ} {ks : List CT} (h : RB b Y (node S y ks)) :
    ∀ k ∈ ks, RB b Y k := RBL_iff.1 h.2.2

theorem RB.of_good {B : Finset ℕ} {kmax : ℕ} : ∀ {t : CT}, Good B t → maxEntry t ≤ kmax →
    RB B.card (2 * kmax + 1) t := by
  intro t
  induction t using CT.ind with
  | h S y ks ih =>
    intro hg hm
    obtain ⟨hgk, hmk⟩ := kids_good hg hm
    refine ⟨Finset.card_le_card hg.label_sub, y_length_le hg hm, RBL_iff.2 fun k hk => ih k hk (hgk k hk) (hmk k hk)⟩

theorem vsz_le {b Y : ℕ} : ∀ {t : CT}, RB b Y t → t.vsz + 1 ≤ count t * (2 * b + 2 * Y + 6) := by
  intro t
  induction t using CT.ind with
  | h S y ks ih =>
    intro h
    obtain ⟨h1, h2, h3⟩ := h
    have hk : ∀ k ∈ ks, RB b Y k := RBL_iff.1 h3
    have hL : ∀ ks' : List CT, (∀ k ∈ ks', RB b Y k) → (∀ k ∈ ks', k.vsz + 1 ≤ count k * (2 * b + 2 * Y + 6)) →
        vszL ks' ≤ 1 + countL ks' * (2 * b + 2 * Y + 6) := by
      intro ks'
      induction ks' with
      | nil => intro _ _; simp [vszL, countL]
      | cons k ks'' ihl =>
        intro hh1 hh2
        have := ihl (fun k' hk' => hh1 k' (List.mem_cons_of_mem _ hk'))
          (fun k' hk' => hh2 k' (List.mem_cons_of_mem _ hk'))
        have h0 := hh2 k (by simp)
        simp only [vszL, countL]
        nlinarith
    have := hL ks hk (fun k hk' => ih k hk' (hk k hk'))
    simp only [vsz, count]
    nlinarith

theorem count_mul_le {b Y : ℕ} {t : CT} (h : RB b Y t) : t.vsz ≤ count t * (2 * b + 2 * Y + 6) := by
  have := vsz_le h; omega

/-- **The size of a well-formed characteristic.** -/
theorem Wf.vsz_le {B : Finset ℕ} {kmax : ℕ} {t : CT} (h : Wf B kmax t) :
    t.vsz ≤ runBound B.card * (2 * B.card + 2 * (2 * kmax + 1) + 6) :=
  le_trans (count_mul_le (RB.of_good h.good h.bounded)) (Nat.mul_le_mul_right _ h.count_le)

theorem runBound_mul_le (k : ℕ) : runBound (k + 2) * (2 * (k + 2) + 2 * (2 * (k + 1) + 1) + 6) ≤ 128 * (k + 2) ^ 3 := by
  unfold runBound
  nlinarith [Nat.zero_le k, sq_nonneg k]

/-- The size of every entry of every table is `≤ 128 (k+2)^3` (bags have at most `k + 2` vertices). -/
theorem tables_vsz_le {adj : Adj} {k : ℕ} {nt : NT} (hg : nt.Good adj) (hw : nt.toRT.Width (k + 1)) :
    ∀ c ∈ tables adj k nt, c.vsz ≤ 128 * (k + 2) ^ 3 := by
  intro c hc
  have hB : nt.bag.card ≤ k + 2 := bag_card_le_of_width hw
  have h := (tables_wf hg c hc).vsz_le
  refine le_trans h (le_trans ?_ (runBound_mul_le k))
  have h1 : runBound nt.bag.card ≤ runBound (k + 2) := by
    unfold runBound; exact Nat.mul_le_mul (by omega) (by omega)
  exact Nat.mul_le_mul h1 (by omega)

end CT

end Lax117284Proofs.Treewidth.Chars
