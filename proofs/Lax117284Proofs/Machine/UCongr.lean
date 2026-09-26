import Lax117284Proofs.UnitPGraph
import Lax117284Proofs.Machine.InstSem

/-!
The graph depends on the due dates of the jobs of the table only.
-/

namespace Lax117284Proofs.Machine.UCongr

open Lax117284Proofs.UnitPGraph

theorem find_congr (p q : ℕ → Bool) (l : List ℕ) (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      have ha := h a (by simp)
      have ht : t.find? p = t.find? q := ih (fun x hx => h x (by simp [hx]))
      simp [List.find?_cons, ha, ht]

theorem repN_congr {n : ℕ} {d d' : ℕ → ℕ} {i j : ℕ}
    (h : ∀ jj < n, d (i * n + jj) = d' (i * n + jj)) (hj : j < n) :
    repN n d i j = repN n d' i j := by
  unfold repN
  rw [find_congr _ (fun j' => decide (d' (i * n + j') = d' (i * n + j))) _ (fun x hx => by
    have hx' := List.mem_range.mp hx
    simp [h x hx', h j hj])]

theorem entry_congr {n m k : ℕ} {d d' : ℕ → ℕ} (h : ∀ t < m * n, d t = d' t) {r : ℕ}
    (hr : r < m * n) (c : ℕ) : entry n m k d r c = entry n m k d' r c := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at hr; simp at hr
    · exact h0
  have hi : r / n < m := (Nat.div_lt_iff_lt_mul hn).mpr hr
  have hj : r % n < n := Nat.mod_lt _ hn
  have hrep : repN n d (r / n) (r % n) = repN n d' (r / n) (r % n) :=
    repN_congr (fun jj hjj => h _ (InstSem.cell_lt hi hjj)) hj
  unfold entry
  rw [hrep]

theorem graphNums_congr {n m k : ℕ} {d d' : ℕ → ℕ} (h : ∀ t < m * n, d t = d' t) :
    graphNums n m k d = graphNums n m k d' := by
  unfold graphNums
  split_ifs with hk
  · congr 1
    refine List.flatMap_congr fun r hr => ?_
    exact List.map_congr_left fun c _ => entry_congr h (List.mem_range.mp hr) c
  · rfl
  · rfl

end Lax117284Proofs.Machine.UCongr
