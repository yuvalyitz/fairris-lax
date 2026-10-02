import Lax117284Proofs.Treewidth.Chars.Lattice
import Lax117284Proofs.Treewidth.Seq.Symmetry
import Lax117284Proofs.Treewidth.Seq.Structure

/-!
# Sequence-level content of the join (C3)

* `Ext.map`, `Dom.map_mono`, `Dom.exists_le`: small extra API on `Ext`/`Dom`;
* `join_seq`: the exact sum of two exact sequences (minus the label size) is dominated by an element of the run
  sequences produced by `joinC`, i.e. Lemma 3.14 in the form used by `char_join_dom`.
-/

namespace Lax117284Proofs.Treewidth.Seq

/-! ## `Ext`, `Dom` and monotone maps -/

theorem Ext.map' (g : ℕ → ℕ) : ∀ {a w : List ℕ}, Ext a w → Ext (a.map g) (w.map g) := by
  intro a
  induction a with
  | nil => intro w h; rw [ext_nil_iff] at h; subst h; exact ext_nil_nil
  | cons x a ih =>
    intro w h
    obtain ⟨p, u, rfl, hu⟩ := ext_cons_iff.1 h
    refine ext_cons_iff.2 ⟨p, u.map g, ?_, ih hu⟩
    simp [List.map_replicate]

theorem LeSeq.map_mono {g : ℕ → ℕ} (hg : ∀ x y, x ≤ y → g x ≤ g y) {a b : List ℕ} (h : LeSeq a b) :
    LeSeq (a.map g) (b.map g) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih => exact List.Forall₂.cons (hg _ _ hab) ih

theorem Dom.map_mono {g : ℕ → ℕ} (hg : ∀ x y, x ≤ y → g x ≤ g y) {a b : List ℕ} (h : Dom a b) :
    Dom (a.map g) (b.map g) := by
  obtain ⟨a', b', ha, hb, hle⟩ := h
  exact ⟨a'.map g, b'.map g, ha.map' g, hb.map' g, hle.map_mono hg⟩

theorem LeSeq.exists_le {a b : List ℕ} (h : LeSeq a b) : ∀ x ∈ a, ∃ y ∈ b, x ≤ y := by
  induction h with
  | nil => intro x hx; simp at hx
  | @cons p q as bs hpq _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨q, List.mem_cons_self, hpq⟩
    · obtain ⟨y, hy, hxy⟩ := ih x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩

theorem Dom.exists_le {a b : List ℕ} (h : Dom a b) {x : ℕ} (hx : x ∈ a) : ∃ y ∈ b, x ≤ y := by
  obtain ⟨a', b', ha, hb, hle⟩ := h
  obtain ⟨y, hy, hxy⟩ := hle.exists_le x ((ha.mem).2 hx)
  exact ⟨y, (hb.mem).1 hy, hxy⟩

theorem zadd_mem {e1 e2 : List ℕ} (hl : e1.length = e2.length) {w : ℕ} (hw : w ∈ zadd e1 e2) :
    ∃ x ∈ e1, ∃ y ∈ e2, w = x + y := by
  induction e1 generalizing e2 with
  | nil => simp [zadd] at hw
  | cons a e1 ih =>
    cases e2 with
    | nil => simp at hl
    | cons b e2 =>
      simp only [zadd, List.zipWith_cons_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact ⟨a, List.mem_cons_self, b, List.mem_cons_self, rfl⟩
      · obtain ⟨x, hx, y, hy, rfl⟩ := ih (by simpa using hl) hw
        exact ⟨x, List.mem_cons_of_mem _ hx, y, List.mem_cons_of_mem _ hy, rfl⟩

theorem Dom.ne_nil_left {a b : List ℕ} (h : Dom a b) (hb : b ≠ []) : a ≠ [] := by
  rintro rfl
  obtain ⟨a', b', ha, hb', hle⟩ := h
  rw [ext_nil_iff] at ha
  subst ha
  have : b' = [] := List.length_eq_zero_iff.1 (by simpa using (LeSeq.length_eq hle).symm)
  subst this
  exact hb (ext_nil_right.1 hb')

end Lax117284Proofs.Treewidth.Seq

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq CT

/-! ## the join of two exact sequences -/

/-- Lemma 3.14 in the form used by the join: `e3 = e1 + e2 - s` is dominated by (the `s`-shift of) a typical ring sum
of `τ e1, τ e2`, and that shift is one of the run sequences that `joinC` produces. -/
theorem join_seq {e1 e2 : List ℕ} {s kmax : ℕ} (hl : e1.length = e2.length) (hne : e1 ≠ [])
    (h1 : ∀ x ∈ e1, s ≤ x) (hkm : ∀ x ∈ (zadd e1 e2).map (· - s), x ≤ kmax) :
    ∃ d ∈ (((ringTypList (typical e1) (typical e2)).map (fun d => d.map (· - s))).dedup.filter
        (fun d => d.all (· ≤ kmax))), Dom d (typical ((zadd e1 e2).map (· - s))) := by
  have hR : RingSum e1 e2 (zadd e1 e2) := RingSum.mk (Ext.refl _) (Ext.refl _) hl
  obtain ⟨c', hc', hdom⟩ := RingSum.dom_typical hR
  have hd0 : typical c' ∈ ringTyp (typical e1) (typical e2) :=
    (mem_ringTyp (typical_ne_nil hne)).2 ⟨c', hc', rfl⟩
  have hdom' : Dom (typical c') (typical (zadd e1 e2)) := dom_typical_iff.1 hdom
  have hge : ∀ x ∈ zadd e1 e2, s ≤ x := by
    intro x hx
    obtain ⟨p, hp, q, _, rfl⟩ := zadd_mem hl hx
    have := h1 p hp; omega
  refine ⟨(typical c').map (· - s), ?_, ?_⟩
  · rw [List.mem_filter, List.mem_dedup, List.mem_map]
    refine ⟨⟨typical c', mem_ringTypList.2 hd0, rfl⟩, ?_⟩
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    obtain ⟨w, hw, hzw⟩ := hdom'.exists_le hz
    have hw' := mem_of_mem_typical hw
    have := hkm (w - s) (List.mem_map.2 ⟨w, hw', rfl⟩)
    simpa using (by omega : z - s ≤ kmax)
  · rw [typical_map_sub _ s hge]
    exact hdom'.map_mono (fun x y h => Nat.sub_le_sub_right h s)

end Lax117284Proofs.Treewidth.Chars
