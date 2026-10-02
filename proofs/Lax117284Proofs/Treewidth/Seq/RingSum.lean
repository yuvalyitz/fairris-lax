import Lax117284Proofs.Treewidth.Seq.Dom

/-!
# The ring sum `a ⊕ b` (Def. 3.8) and Lemmas 3.12, 3.13, 3.14

`RingSum a b c` says `c ∈ a ⊕ b`: `c = a* + b*` for extensions `a* ∈ E(a)`, `b* ∈ E(b)` of the
same length.
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- Entrywise sum of two sequences (of the same length). -/
abbrev zadd (a b : List ℕ) : List ℕ := List.zipWith (· + ·) a b

/-- `c ∈ a ⊕ b` (Def. 3.8). -/
def RingSum (a b c : List ℕ) : Prop :=
  ∃ a' b', Ext a a' ∧ Ext b b' ∧ a'.length = b'.length ∧ c = zadd a' b'

/-- The set `a ⊕ b`. -/
def ringSum (a b : List ℕ) : Set (List ℕ) := {c | RingSum a b c}

theorem RingSum.mk {a b a' b' : List ℕ} (h1 : Ext a a') (h2 : Ext b b')
    (h3 : a'.length = b'.length) : RingSum a b (zadd a' b') := ⟨a', b', h1, h2, h3, rfl⟩

/-- Common refinement of two extensions of two sequences of equal length, respecting the base
positions: after further repetition the two extensions have the same length and the sum is an
extension of the sum of the bases. -/
theorem ext_zip : ∀ {a b u v : List ℕ}, Ext a u → Ext b v → a.length = b.length →
    ∃ u' v', Ext u u' ∧ Ext v v' ∧ u'.length = v'.length ∧ Ext (zadd a b) (zadd u' v') := by
  intro a
  induction a with
  | nil =>
    intro b u v hu hv hl
    rw [ext_nil_iff] at hu; subst hu
    have : b = [] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
    subst this
    rw [ext_nil_iff] at hv; subst hv
    exact ⟨[], [], ext_nil_nil, ext_nil_nil, rfl, ext_nil_nil⟩
  | cons x a ih =>
    intro b u v hu hv hl
    cases b with
    | nil => simp at hl
    | cons y b =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      obtain ⟨p, u0, rfl, hu0⟩ := ext_cons_iff.mp hu
      obtain ⟨q, v0, rfl, hv0⟩ := ext_cons_iff.mp hv
      obtain ⟨u0', v0', h1, h2, h3, h4⟩ := ih hu0 hv0 hl
      set N := (p + 1) * (q + 1) with hN
      have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hpN : p + 1 ≤ N := by nlinarith
      have hqN : q + 1 ≤ N := by nlinarith
      refine ⟨List.replicate N x ++ u0', List.replicate N y ++ v0',
        Ext.append (ext_replicate (by omega) hpN) h1,
        Ext.append (ext_replicate (by omega) hqN) h2, by simp [h3], ?_⟩
      have hz : zadd (List.replicate N x ++ u0') (List.replicate N y ++ v0') =
          List.replicate N (x + y) ++ zadd u0' v0' := by
        unfold zadd
        rw [List.zipWith_append (by simp)]
        simp
      rw [hz]
      obtain ⟨N', hN'⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      rw [hN']
      unfold zadd
      rw [List.zipWith_cons_cons]
      exact ext_cons_iff.mpr ⟨N', zadd u0' v0', by simp, h4⟩

/-- **Lemma 3.13**. -/
theorem RingSum.dom_of_dom {a b a₀ b₀ : List ℕ} (hab : a.length = b.length)
    (ha : Dom a₀ a) (hb : Dom b₀ b) : ∃ y₀, RingSum a₀ b₀ y₀ ∧ Dom y₀ (zadd a b) := by
  obtain ⟨a0', a', h1, h2, h3⟩ := ha
  obtain ⟨b0', b', h4, h5, h6⟩ := hb
  obtain ⟨u', v', hu, hv, hlen, hz⟩ := ext_zip h2 h5 hab
  obtain ⟨x, hx, hxu⟩ := ext_lift hu h3
  obtain ⟨z, hz', hzv⟩ := ext_lift hv h6
  have hlx : x.length = z.length := by
    rw [LeSeq.length_eq hxu, LeSeq.length_eq hzv, hlen]
  refine ⟨zadd x z, ⟨x, z, h1.trans hx, h4.trans hz', hlx, rfl⟩, ?_⟩
  exact ⟨zadd x z, zadd u' v', Ext.refl _, hz, LeSeq.zipWith_add hxu hzv⟩

/-- **Lemma 3.14**: every element of `a ⊕ b` dominates an element of `τ(a) ⊕ τ(b)`. -/
theorem RingSum.dom_typical {a b c : List ℕ} (h : RingSum a b c) :
    ∃ c', RingSum (typical a) (typical b) c' ∧ Dom c' c := by
  obtain ⟨a', b', ha', hb', hl, rfl⟩ := h
  obtain ⟨y₀, hy, hd⟩ := RingSum.dom_of_dom (a := a') (b := b') (a₀ := typical a') (b₀ := typical b')
    hl (domEquiv_typical a').1 (domEquiv_typical b').1
  rw [ha'.typical, hb'.typical] at hy
  exact ⟨y₀, hy, hd⟩

end Lax117284Proofs.Treewidth.Seq
