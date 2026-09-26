import Lax117284Proofs.Machine.InstSem
import Lax117284.Corollary8

/-!
The reduction that adds a conflict-free day, on the numbers of a stream: what it writes.
-/

namespace Lax117284Proofs.Machine.FreeSem

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem

/-- The largest processing time on the first day, computed as a running maximum. -/
def gapOf (ns : List ℕ) : ℕ :=
  (List.range (ns.getD 0 0)).foldl (fun g j => max g (ns.getD (2 + 2 * j) 0)) 0

/-- The numbers of the output: the counts with one more day, the old table, the new day, and
the fairness parameter plus one. -/
def outFree (ns : List ℕ) : List ℕ :=
  [ns.getD 0 0, ns.getD 1 0 + 1] ++ (ns.drop 2).take (2 * (ns.getD 1 0 * ns.getD 0 0)) ++
    (List.range (ns.getD 0 0)).flatMap (fun j => [ns.getD (2 + 2 * j) 0, (j + 1) * gapOf ns]) ++
    [paramOf ns + 1]

lemma foldl_max_le (f : ℕ → ℕ) (b : ℕ) : ∀ (n : ℕ) (g : ℕ),
    g ≤ b → (∀ j < n, f j ≤ b) → (List.range n).foldl (fun g j => max g (f j)) g ≤ b
  | 0, g, hg, _ => by simpa using hg
  | n + 1, g, hg, hf => by
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have := foldl_max_le f b n g hg (fun j hj => hf j (by omega))
    exact max_le this (hf n (by omega))

lemma le_foldl_max_of_lt (f : ℕ → ℕ) : ∀ (n : ℕ) (g j : ℕ), j < n →
    f j ≤ (List.range n).foldl (fun g j => max g (f j)) g
  | 0, g, j, hj => by omega
  | n + 1, g, j, hj => by
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rcases Nat.lt_or_ge j n with h | h
    · exact le_trans (le_foldl_max_of_lt f n g j h) (le_max_left _ _)
    · have : j = n := by omega
      subst this
      exact le_max_right _ _

/-- The gap of the instance is the running maximum. -/
theorem gap_instOf (ns : List ℕ) (hv : Valid ns) (hpos : 0 < ns.getD 1 0) :
    Lax117284.Corollary8.gap (instOf ns hv) = gapOf ns := by
  unfold Lax117284.Corollary8.gap gapOf
  have hcell : ∀ j < ns.getD 0 0, (instOf ns hv).pAt 0 j = ns.getD (2 + 2 * j) 0 := by
    intro j hj
    have hn : 0 < ns.getD 0 0 := by omega
    have ht : j < ns.getD 1 0 * ns.getD 0 0 := by
      have := Nat.mul_le_mul_right (ns.getD 0 0) (show 1 ≤ ns.getD 1 0 by omega)
      omega
    have := (instOf_pAt ns hv ht).1
    rwa [Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj] at this
  apply le_antisymm
  · refine Finset.sup_le fun j _ => ?_
    have h := hcell j j.isLt
    have := le_foldl_max_of_lt (fun j => ns.getD (2 + 2 * j) 0) (ns.getD 0 0) 0 j j.isLt
    show (instOf ns hv).pAt 0 (j : ℕ) ≤ _
    rw [h]; exact this
  · refine foldl_max_le _ _ _ _ (Nat.zero_le _) fun j hj => ?_
    rw [← hcell j hj]
    exact Finset.le_sup (f := fun j : Fin (instOf ns hv).clients => (instOf ns hv).pAt 0 (j : ℕ))
      (Finset.mem_univ ⟨j, hj⟩)

section AddFree

variable (I : Instance)

lemma pAt_add_old {i j : ℕ} (hi : i < I.days) (hj : j < I.clients) :
    (Lax117284.Corollary8.addFreeDay I).pAt i j = I.pAt i j := by
  have hi' : i < I.days + 1 := by omega
  simp [Instance.pAt, Lax117284.Corollary8.addFreeDay, hi, hj, hi']

lemma dAt_add_old {i j : ℕ} (hi : i < I.days) (hj : j < I.clients) :
    (Lax117284.Corollary8.addFreeDay I).dAt i j = I.dAt i j := by
  have hi' : i < I.days + 1 := by omega
  simp [Instance.dAt, Lax117284.Corollary8.addFreeDay, hi, hj, hi']

lemma pAt_add_new {j : ℕ} (hj : j < I.clients) :
    (Lax117284.Corollary8.addFreeDay I).pAt I.days j = I.pAt 0 j := by
  have hi' : I.days < I.days + 1 := by omega
  simp [Instance.pAt, Lax117284.Corollary8.addFreeDay, hj, hi']

lemma dAt_add_new {j : ℕ} (hj : j < I.clients) :
    (Lax117284.Corollary8.addFreeDay I).dAt I.days j
      = (j + 1) * Lax117284.Corollary8.gap I := by
  have hi' : I.days < I.days + 1 := by omega
  simp [Instance.dAt, Lax117284.Corollary8.addFreeDay, hj, hi']

end AddFree

/-- **The numbers of the instance with a day added.** -/
theorem instToks_addFreeDay (ns : List ℕ) (hv : Valid ns) (hs : Shape eU ns)
    (hpos : 0 < ns.getD 1 0) :
    instToks (Lax117284.Corollary8.addFreeDay (instOf ns hv)) =
      [ns.getD 0 0, ns.getD 1 0 + 1] ++ (ns.drop 2).take (2 * (ns.getD 1 0 * ns.getD 0 0)) ++
        (List.range (ns.getD 0 0)).flatMap
          (fun j => [ns.getD (2 + 2 * j) 0, (j + 1) * gapOf ns]) := by
  set I := instOf ns hv with hI
  have hn : ns.getD 0 0 = I.clients := rfl
  have hm : ns.getD 1 0 = I.days := rfl
  have hcl : (Lax117284.Corollary8.addFreeDay I).clients = I.clients := rfl
  have hdy : (Lax117284.Corollary8.addFreeDay I).days = I.days + 1 := rfl
  have hlen : 2 + 2 * (I.days * I.clients) ≤ ns.length := by
    have := hs.2; simp only [eU] at this; rw [hn, hm] at this; omega
  have hgap := gap_instOf ns hv hpos
  unfold instToks
  rw [hcl, hdy, Nat.add_mul, one_mul, List.range_add, List.flatMap_append, List.flatMap_map]
  have part1 : (List.range (I.days * I.clients)).flatMap (fun t =>
      [(Lax117284.Corollary8.addFreeDay I).pAt (t / I.clients) (t % I.clients),
       (Lax117284.Corollary8.addFreeDay I).dAt (t / I.clients) (t % I.clients)])
      = (ns.drop 2).take (2 * (ns.getD 1 0 * ns.getD 0 0)) := by
    rw [← flatMap_pairs ns 2 _ (by rw [hn, hm]; omega)]
    refine List.flatMap_congr fun t ht => ?_
    have ht' : t < I.days * I.clients := List.mem_range.mp ht
    have hn0 : 0 < I.clients := by
      rcases Nat.eq_zero_or_pos I.clients with h | h
      · rw [h] at ht'; simp at ht'
      · exact h
    have h1 : t / I.clients < I.days := by
      rw [Nat.div_lt_iff_lt_mul hn0]; exact ht'
    have h2 : t % I.clients < I.clients := Nat.mod_lt _ hn0
    rw [pAt_add_old I h1 h2, dAt_add_old I h1 h2]
    have := instOf_pAt ns hv (t := t) (by rw [hn, hm] at *; exact ht')
    simp only [List.cons.injEq, and_true]
    exact this
  have part2 : (List.range I.clients).flatMap (fun a =>
      [(Lax117284.Corollary8.addFreeDay I).pAt ((I.days * I.clients + a) / I.clients)
        ((I.days * I.clients + a) % I.clients),
       (Lax117284.Corollary8.addFreeDay I).dAt ((I.days * I.clients + a) / I.clients)
        ((I.days * I.clients + a) % I.clients)])
      = (List.range (ns.getD 0 0)).flatMap
          (fun j => [ns.getD (2 + 2 * j) 0, (j + 1) * gapOf ns]) := by
    rw [hn]
    refine List.flatMap_congr fun j hj => ?_
    have hj' : j < I.clients := List.mem_range.mp hj
    have hq : (I.days * I.clients + j) / I.clients = I.days := by
      rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj', Nat.add_zero]
    have hr : (I.days * I.clients + j) % I.clients = j := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj']
    rw [hq, hr, pAt_add_new I hj', dAt_add_new I hj', hgap]
    have ht : j < I.days * I.clients := by
      have := Nat.mul_le_mul_right I.clients (show 1 ≤ I.days by rw [hm] at hpos; omega)
      omega
    have := (instOf_pAt ns hv (t := j) (by rw [hn, hm] at *; simpa using ht)).1
    rw [hn, Nat.div_eq_of_lt hj', Nat.mod_eq_of_lt hj'] at this
    show [(instOf ns hv).pAt 0 j, _] = _
    rw [this]
  rw [part1, part2]
  simp only [List.append_assoc, hn, hm]

/-- **The reduction writes the numbers of the instance with a day added.** -/
theorem free_eq (ns : List ℕ) (hv : Valid ns) (hs : Shape eU ns) (hpos : 0 < ns.getD 1 0) :
    Lax117284.Corollary8.reduceFreeDay (numCode ns) = numCode (outFree ns) := by
  classical
  have hI : encodeUniform (instOf ns hv) (paramOf ns) = numCode ns := by
    rw [encodeUniform, encodeInstance_eq]
    conv_rhs => rw [← instToks_instOf ns hv hs]
    rw [numCode_append]
    simp [numCode]
  have hg : ∃ (I : Instance) (k : ℕ), encodeUniform I k = numCode ns ∧ 0 < I.days :=
    ⟨instOf ns hv, paramOf ns, hI, hpos⟩
  unfold Lax117284.Corollary8.reduceFreeDay
  rw [dif_pos hg]
  have key : ∀ (I' : Instance) (k' : ℕ), encodeUniform I' k' = numCode ns →
      encodeUniform (Lax117284.Corollary8.addFreeDay I') (k' + 1) = numCode (outFree ns) := by
    intro I' k' h'
    obtain ⟨rfl, rfl⟩ := Injectivity.encodeUniform_inj (h'.trans hI.symm)
    rw [encodeUniform, encodeInstance_eq, instToks_addFreeDay ns hv hs hpos]
    unfold outFree
    simp only [numCode_append, List.append_assoc, numCode_cons, numCode_nil, List.append_nil]
  exact key _ _ hg.choose_spec.choose_spec.1

/-- **A word that is not the code of a valid stream is rejected.** -/
theorem free_rej (w : Word)
    (h : ¬ ∃ ns : List ℕ, w = numCode ns ∧ Shape eU ns ∧ Valid ns ∧ 0 < ns.getD 1 0) :
    Lax117284.Corollary8.reduceFreeDay w = rejected := by
  classical
  unfold Lax117284.Corollary8.reduceFreeDay
  rw [dif_neg (fun hg => h ((uniform_iff w).1 hg))]

end Lax117284Proofs.Machine.FreeSem
