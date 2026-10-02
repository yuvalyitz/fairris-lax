import Lax117284Proofs.Treewidth.Chars.IntroPlansMem

/-!
# Prefixing a run with an exact chain (work package C4, part 8)

If the run `k = node S yk kk` has the same label as its (single non-junk) parent node of size `s`, the normal form
merges them into one run whose sequence is `typical (s ++ yk)`.  The options of `k`, and the options that end exactly at
the junction, lift *syntactically* to the options of the *exact* run `k' = node S (s ++ yk) kk` (cut indices shift by
`|s|`); `IR_mono` then moves them to the typical run.

* `winR_prefix`   — parent flagged, `W` continues into `k`  (`r ↦ preC (plus1 s) r`);
* `winR_end`      — parent flagged, `W` ends at the junction;
* `wtopR_wrap`    — parent unflagged, `W` starts at the root of `k`  (`r ↦ node S s [r]`);
* `IR_prefix`     — parent unflagged, any option of `k`;
* `attR_junction` — parent unflagged, a new branch hangs at the parent node.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- Prefix the sequence of the root run. -/
def preC (s : List ℕ) : CT → CT
  | node S y ks => node S (s ++ y) ks

theorem splits_shift {s y d1 d2 : List ℕ} (h : (d1, d2) ∈ splits y) : (s ++ d1, d2) ∈ splits (s ++ y) := by
  rw [mem_splits_iff] at h ⊢
  rcases h with ⟨f, hf, rfl, rfl⟩ | ⟨f, hf, rfl, rfl⟩
  · left
    refine ⟨s.length + f, by simp; omega, ?_, ?_⟩
    · rw [show s.length + f + 1 = s.length + (f + 1) by omega, List.take_length_add_append]
    · rw [List.drop_length_add_append]
  · right
    refine ⟨s.length + f, by simp; omega, ?_, ?_⟩
    · rw [show s.length + f + 1 = s.length + (f + 1) by omega, List.take_length_add_append]
    · rw [show s.length + f + 1 = s.length + (f + 1) by omega, List.drop_length_add_append]

theorem splits_junction {s y : List ℕ} (hs : s ≠ []) (hy : y ≠ []) : (s, y) ∈ splits (s ++ y) := by
  rw [mem_splits_iff]
  right
  have h1 : 0 < s.length := List.length_pos_iff.2 hs
  have h2 : 0 < y.length := List.length_pos_iff.2 hy
  refine ⟨s.length - 1, by simp; omega, ?_, ?_⟩
  · rw [show s.length - 1 + 1 = s.length by omega]
    simpa using (List.take_length_add_append (l₁ := s) (l₂ := y) 0).symm
  · rw [show s.length - 1 + 1 = s.length by omega]
    simpa using (List.drop_length_add_append (l₁ := s) (l₂ := y) 0).symm

theorem plus1_append (a b : List ℕ) : plus1 (a ++ b) = plus1 a ++ plus1 b := by simp [plus1]

/-- Parent flagged, `W` continues into the run. -/
theorem winR_prefix (v : ℕ) (S : Finset ℕ) (yk : List ℕ) (kk : List CT) (s : List ℕ) {r : CT} {c : Finset ℕ}
    (h : WinR v (node S yk kk) r c) :
    ∃ r', WinR v (node S (s ++ yk) kk) r' c ∧ r' = preC (plus1 s) r := by
  rcases h with ⟨d1, d2, hd, rfl, rfl⟩ | ⟨kids, cv, hk, rfl, rfl⟩
  · exact ⟨_, Or.inl ⟨s ++ d1, d2, splits_shift hd, by rw [plus1_append], rfl⟩, by simp [preC, plus1_append]⟩
  · exact ⟨_, Or.inr ⟨kids, cv, hk, by rw [plus1_append], rfl⟩, by simp [preC, plus1_append]⟩

/-- Parent flagged, `W` ends at the junction. -/
theorem winR_end (v : ℕ) (S : Finset ℕ) {yk : List ℕ} (kk : List CT) {s : List ℕ} (hs : s ≠ []) (hy : yk ≠ []) :
    WinR v (node S (s ++ yk) kk) (node (insert v S) (plus1 s) [node S yk kk]) S :=
  Or.inl ⟨s, yk, splits_junction hs hy, rfl, rfl⟩

/-- Parent unflagged, `W` starts at the root of the run. -/
theorem wtopR_wrap (v : ℕ) (S : Finset ℕ) {yk : List ℕ} (kk : List CT) {s : List ℕ} (hs : s ≠ []) (hy : yk ≠ [])
    {r : CT} {c : Finset ℕ} (h : WinR v (node S yk kk) r c) :
    WtopR v (node S (s ++ yk) kk) (node S s [r]) c :=
  Or.inr ⟨s, yk, r, splits_junction hs hy, h, rfl⟩

/-- Parent unflagged, a new branch hangs at the parent node. -/
theorem attR_junction (v : ℕ) (N : Finset ℕ) (S : Finset ℕ) {yk : List ℕ} (kk : List CT) {s : List ℕ} (hs : s ≠ [])
    (hy : yk ≠ []) {chain : List (Finset ℕ)} {M : Finset ℕ} (h : (chain, M) ∈ allChains S N) :
    AttR v N (node S (s ++ yk) kk) (node S s [pathSubtree v chain M, node S yk kk]) :=
  ⟨chain, M, h, Or.inr ⟨s, yk, splits_junction hs hy, rfl⟩⟩

/-- Parent unflagged, any option of the run lifts to the exact run. -/
theorem IR_prefix (v : ℕ) (N : Finset ℕ) (S : Finset ℕ) {yk : List ℕ} (kk : List CT) {s : List ℕ} (hs : s ≠ [])
    (hy : yk ≠ []) {r : CT} (h : IR v N (node S yk kk) r) :
    ∃ r', IR v N (node S (s ++ yk) kk) r' ∧
      ((r.S = S ∧ r' = preC s r) ∨ (r.S = insert v S ∧ r' = node S s [r])) := by
  cases h with
  | top hw hN =>
    rename_i c
    rcases hw with hw | ⟨d1, d2, X, hd, hX, rfl⟩
    · refine ⟨node S s [r], IR.top (wtopR_wrap v S kk hs hy hw) hN, Or.inr ⟨?_, rfl⟩⟩
      rcases hw with ⟨d1, d2, hd, rfl, rfl⟩ | ⟨kids, cv, hk, rfl, rfl⟩ <;> rfl
    · exact ⟨node S (s ++ d1) [X], IR.top (Or.inr ⟨s ++ d1, d2, X, splits_shift hd, hX, rfl⟩) hN,
        Or.inl ⟨rfl, rfl⟩⟩
  | att hNS ha =>
    obtain ⟨chain, M, hcm, hr⟩ := ha
    rcases hr with rfl | ⟨d1, d2, hd, rfl⟩
    · exact ⟨node S (s ++ yk) (kk ++ [pathSubtree v chain M]),
        IR.att hNS ⟨chain, M, hcm, Or.inl rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨node S (s ++ d1) [pathSubtree v chain M, node S d2 kk],
        IR.att hNS ⟨chain, M, hcm, Or.inr ⟨s ++ d1, d2, splits_shift hd, rfl⟩⟩, Or.inl ⟨rfl, rfl⟩⟩
  | kid hk =>
    rename_i pre k post r1
    exact ⟨node S (s ++ yk) (pre ++ r1 :: post), IR.kid hk, Or.inl ⟨rfl, rfl⟩⟩

end Lax117284Proofs.Treewidth.Chars
