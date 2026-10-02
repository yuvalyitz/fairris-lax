import Lax117284Proofs.Treewidth.Size.RealF
import Lax117284Proofs.Treewidth.Size.PlanSize

/-!
# Size bounds (WP P1): the statements in the shape of `proofs-todo/Machine.lean`

* `joinC_length_le_64` / `introC_length_le_64` : the typed `2^(64 (|B| + kmax + 2)^3)` bounds;
* `tables_length_le_C0`, `tables_pre_le_C0` : with the constant `C0 = 30000` of `Machine.lean` (`≤ 2^(C0 (k+2)^3)`), for
  the tables themselves and for the lists *before* `dedup` in `forgetTable`/`introTable`/`joinTable`;
* `extract_size_le` : `Machine.lean`'s statement with the extra hypothesis `nt.toRT.Width (k + 1)` (bags of at most
  `k + 2` vertices); the constant `4 * (k + 3)` is kept (the proof gives `2 * k + 8`).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- `Machine.lean`'s `C0`. -/
def sizeC0 : ℕ := 30000

theorem joinC_length_le_64 {B : Finset ℕ} {kmax : ℕ} {a b : CT} (ha : a.Wf B kmax) (hb : b.Wf B kmax) :
    (CT.joinC kmax a b).length ≤ 2 ^ (64 * (B.card + kmax + 2) ^ 3) :=
  le_trans (CT.joinC_length_le ha hb) (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem introC_length_le_64 {v kmax : ℕ} {N B : Finset ℕ} {t : CT} (hw : t.Wf B kmax) :
    (CT.introC kmax v N t).length ≤ 2 ^ (64 * (B.card + kmax + 2) ^ 3) :=
  CT.introC_length_le' hw

theorem tables_length_le_C0 {adj : Adj} {k : ℕ} {nt : NT} (hg : nt.Good adj) (hw : nt.toRT.Width (k + 1)) :
    (tables adj k nt).length ≤ 2 ^ (sizeC0 * (k + 2) ^ 3) :=
  le_trans (tables_length_le_pow hg hw) (Nat.pow_le_pow_right (by norm_num) (by unfold sizeC0; omega))

/-- Every list built by a table step (forget, introduce, join), before and after `dedup`, has at most
`2^(C0 (k+2)^3)` elements; the elements are characteristics of size `≤ 128 (k+2)^3`. -/
theorem tables_pre_le_C0 {adj : Adj} {k : ℕ} :
    (∀ {x : ℕ} {c : NT}, c.Good adj → c.toRT.Width (k + 1) →
      ((tables adj k c).map (CT.forgetC x)).length ≤ 2 ^ (sizeC0 * (k + 2) ^ 3)) ∧
    (∀ {v : ℕ} {c : NT} (N : Finset ℕ), c.Good adj → c.toRT.Width (k + 1) →
      ((tables adj k c).flatMap (CT.introC (k + 1) v N)).length ≤ 2 ^ (sizeC0 * (k + 2) ^ 3)) ∧
    (∀ {a b : NT}, (NT.join a b).Good adj → (NT.join a b).toRT.Width (k + 1) →
      ((tables adj k a).flatMap fun ca => (tables adj k b).flatMap fun cb => CT.joinC (k + 1) ca cb).length ≤
        2 ^ (sizeC0 * (k + 2) ^ 3)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x c hg hw
    exact le_trans (forgetTable_pre_le hg hw) (Nat.pow_le_pow_right (by norm_num) (by unfold sizeC0; omega))
  · intro v c N hg hw
    exact le_trans (introTable_pre_le hg hw N) (Nat.pow_le_pow_right (by norm_num) (by unfold sizeC0; omega))
  · intro a b hg hw
    exact le_trans (joinTable_pre_le hg hw) (Nat.pow_le_pow_right (by norm_num) (by unfold sizeC0; omega))

/-- **`extract_size_le`** (repaired: with the width hypothesis). -/
theorem extract_size_le {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) {nt : NT} (hg : nt.Good adj)
    (hW : nt.under ⊆ W) (hw : nt.toRT.Width (k + 1)) : ∀ c ∈ tables adj k nt, ∀ t, extract adj k nt c = some t →
      t.size ≤ 4 * (k + 3) * nt.size :=
  extract_size_le' hs hg hW hw

end Lax117284Proofs.Treewidth.Chars
