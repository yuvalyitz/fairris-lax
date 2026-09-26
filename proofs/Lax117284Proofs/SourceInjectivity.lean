import Lax117284Proofs.Codes
import Lax117284Proofs.Lemma14Graph
import Lax117284.BoundedSat
import Lax117284.TwoSatisfiability
import Lax117284.JustInTime
import Lax117284.MulticolouredIndepSet

/-!
A word determines the source instance it encodes, for each of the four source problems.
-/

namespace Lax117284Proofs.SourceInjectivity

open Lax117284Proofs.Codes Lax117284.Problems Lax434930.PolynomialTime

/-! ### Just in time -/

theorem jit_encode_inj {R R' : Lax117284.JustInTime.Instance}
    (h : Lax117284.JustInTime.encodeInstance R = Lax117284.JustInTime.encodeInstance R') :
    R = R' := by
  obtain ⟨n, m, p, d, hp, hd⟩ := R
  obtain ⟨n', m', p', d', hp', hd'⟩ := R'
  simp only [Lax117284.JustInTime.encodeInstance, List.append_assoc] at h
  obtain ⟨hn, h⟩ := encodeNat_prefixFree _ _ _ _ h
  obtain ⟨hm, h⟩ := encodeNat_prefixFree _ _ _ _ h
  subst hn; subst hm
  obtain ⟨hdd, h⟩ := flatMap_inj encodeNat_prefixFree n d d' _ _ h
  obtain ⟨hpp, -⟩ := flatMap_inj (encodeNat_prefixFree.fin n) m p p' [] [] (by simpa using h)
  subst hdd; subst hpp
  rfl

/-! ### 2-SAT -/

theorem twoSat_encode_inj {φ φ' : Lax117284.TwoSatisfiability.Formula}
    (h : Lax117284.TwoSatisfiability.encodeFormula φ
      = Lax117284.TwoSatisfiability.encodeFormula φ') : φ = φ' := by
  obtain ⟨v, c, l⟩ := φ
  obtain ⟨v', c', l'⟩ := φ'
  simp only [Lax117284.TwoSatisfiability.encodeFormula, List.append_assoc] at h
  obtain ⟨hv, h⟩ := encodeNat_prefixFree _ _ _ _ h
  obtain ⟨hc, h⟩ := encodeNat_prefixFree _ _ _ _ h
  subst hv; subst hc
  have hcode : PrefixFree fun q : Fin 2 → ℕ × Bool =>
      (List.finRange 2).flatMap fun α => encodeNat (q α).1 ++ [(q α).2] :=
    natBool_prefixFree.fin 2
  obtain ⟨hl, -⟩ := flatMap_inj hcode c
    (fun i α => (((l i α).1 : ℕ), (l i α).2)) (fun i α => (((l' i α).1 : ℕ), (l' i α).2))
    [] [] (by simpa using h)
  have : l = l' := funext fun i => funext fun α => by
    have := congrFun (congrFun hl i) α
    simp only [Prod.mk.injEq] at this
    exact Prod.ext (Fin.ext this.1) this.2
  subst this
  rfl

/-! ### [2,3]-bounded 3-SAT -/

theorem boundedSat_encode_inj {φ φ' : Lax117284.BoundedSat.Formula}
    (h : Lax117284.BoundedSat.encodeFormula φ = Lax117284.BoundedSat.encodeFormula φ') :
    φ = φ' := by
  obtain ⟨v, t, u, a, b, occ⟩ := φ
  obtain ⟨v', t', u', a', b', occ'⟩ := φ'
  simp only [Lax117284.BoundedSat.encodeFormula, List.append_assoc] at h
  obtain ⟨hv, h⟩ := encodeNat_prefixFree _ _ _ _ h
  obtain ⟨ht, h⟩ := encodeNat_prefixFree _ _ _ _ h
  obtain ⟨hu, h⟩ := encodeNat_prefixFree _ _ _ _ h
  subst hv; subst ht; subst hu
  have hcode2 : PrefixFree fun q : Fin 2 → ℕ × Bool =>
      (List.finRange 2).flatMap fun α => encodeNat (q α).1 ++ [(q α).2] :=
    natBool_prefixFree.fin 2
  have hcode3 : PrefixFree fun q : Fin 3 → ℕ × Bool =>
      (List.finRange 3).flatMap fun α => encodeNat (q α).1 ++ [(q α).2] :=
    natBool_prefixFree.fin 3
  obtain ⟨ha, h⟩ := flatMap_inj hcode2 t
    (fun i α => (((a i α).1 : ℕ), (a i α).2)) (fun i α => (((a' i α).1 : ℕ), (a' i α).2))
    _ _ (by simpa using h)
  obtain ⟨hb, -⟩ := flatMap_inj hcode3 u
    (fun i α => (((b i α).1 : ℕ), (b i α).2)) (fun i α => (((b' i α).1 : ℕ), (b' i α).2))
    [] [] (by simpa using h)
  have haa : a = a' := funext fun i => funext fun α => by
    have := congrFun (congrFun ha i) α
    simp only [Prod.mk.injEq] at this
    exact Prod.ext (Fin.ext this.1) this.2
  have hbb : b = b' := funext fun i => funext fun α => by
    have := congrFun (congrFun hb i) α
    simp only [Prod.mk.injEq] at this
    exact Prod.ext (Fin.ext this.1) this.2
  subst haa; subst hbb
  rfl

/-! ### Multicoloured independent set -/

/-- Equal square blocks of bits, read row by row, have equal entries. -/
theorem matrix_inj (V : ℕ) : ∀ (n : ℕ) (g g' : ℕ → ℕ → Bool),
    (List.range n).flatMap (fun w => (List.range V).map (g w))
      = (List.range n).flatMap (fun w => (List.range V).map (g' w)) →
    ∀ w < n, ∀ w' < V, g w w' = g' w w' := by
  intro n
  induction n with
  | zero => intro g g' _ w hw; omega
  | succ n ih =>
    intro g g' h w hw w' hw'
    rw [List.range_succ_eq_map] at h
    simp only [List.flatMap_cons, List.flatMap_map] at h
    obtain ⟨h0, h1⟩ := List.append_inj h (by simp)
    rcases Nat.eq_zero_or_pos w with rfl | hpos
    · exact (List.map_inj_left.1 h0) w' (List.mem_range.2 hw')
    · have := ih (fun a => g (a + 1)) (fun a => g' (a + 1)) (by simpa using h1) (w - 1)
        (by omega) w' hw'
      simpa [Nat.sub_add_cancel hpos] using this

theorem mis_encode_inj {G G' : Lax117284.MulticolouredIndepSet.Instance}
    (h : Lax117284.MulticolouredIndepSet.encodeInstance G
      = Lax117284.MulticolouredIndepSet.encodeInstance G') : G = G' := by
  classical
  obtain ⟨c, s, gr, hg⟩ := G
  obtain ⟨c, s, gr', hg'⟩ := G'
  simp only [Lax117284.MulticolouredIndepSet.encodeInstance, List.append_assoc] at h
  obtain ⟨hc, h⟩ := encodeNat_prefixFree _ _ _ _ h
  obtain ⟨hs, h⟩ := encodeNat_prefixFree _ _ _ _ h
  subst hc; subst hs
  have hadj := matrix_inj (c * s) (c * s)
    (fun w w' => Lax117284.MulticolouredIndepSet.Instance.adjAt ⟨c, s, gr, hg⟩ w w')
    (fun w w' => Lax117284.MulticolouredIndepSet.Instance.adjAt ⟨c, s, gr', hg'⟩ w w')
    (by simpa [Lax117284.MulticolouredIndepSet.Instance.vertices] using h)
  have hgr : gr = gr' := by
    ext u v
    have hu := Lax117284Proofs.Lemma14Graph.num_lt ⟨c, s, gr, hg⟩ u
    have hv := Lax117284Proofs.Lemma14Graph.num_lt ⟨c, s, gr, hg⟩ v
    have h1 := hadj (Lax117284Proofs.Lemma14Graph.num ⟨c, s, gr, hg⟩ u) hu
      (Lax117284Proofs.Lemma14Graph.num ⟨c, s, gr, hg⟩ v) hv
    have e1 := Lax117284Proofs.Lemma14Graph.adjAt_num ⟨c, s, gr, hg⟩ u v
    have e2 := Lax117284Proofs.Lemma14Graph.adjAt_num ⟨c, s, gr', hg'⟩ u v
    have hn : Lax117284Proofs.Lemma14Graph.num ⟨c, s, gr', hg'⟩ u
        = Lax117284Proofs.Lemma14Graph.num ⟨c, s, gr, hg⟩ u := rfl
    have hn' : Lax117284Proofs.Lemma14Graph.num ⟨c, s, gr', hg'⟩ v
        = Lax117284Proofs.Lemma14Graph.num ⟨c, s, gr, hg⟩ v := rfl
    rw [hn, hn'] at e2
    rw [← e1, ← e2]
    simp only [h1]
  subst hgr
  rfl

end Lax117284Proofs.SourceInjectivity
