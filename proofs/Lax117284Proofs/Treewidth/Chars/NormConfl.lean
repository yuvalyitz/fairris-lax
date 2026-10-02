import Lax117284Proofs.Treewidth.Chars.NormConn

/-!
# Confluence of the normal form under forgetting a vertex (work package C1)

`norm_relabel_norm`: `norm (relabel (erase x) (norm p)) = norm (relabel (erase x) p)` for connected `p` whose
sequences are non-empty.

**Statement audit.**  The statement of `proofs-todo/Statements.lean` (arbitrary `f`, arbitrary `p`) is false in three ways,
each checked by `#eval` (see the delivery report):
* `f` must be monotone for `⊆` (else pruned leaves are no longer prunable) — only `f = erase x` is ever used;
* a run with an empty sequence breaks it (`take 1 (typical ([] ++ y))` vs `take 1 []`);
* the *sorting* of `norm` is by `key`, and the keys of two kids can tie after forgetting a vertex unless the kids are
  connected (own disjoint vertex sets): `Conn p` is needed.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

namespace CT

/-! ## sequence facts -/

theorem head_push (t : List ℕ) (x y : ℕ) : (push (x :: t) y).head? = some x := by
  unfold push cut
  by_cases h : ∀ z ∈ t, InR z x y
  · rw [if_pos h]
    by_cases h2 : t = [] ∧ x = y
    · rw [if_pos h2]; simp [h2.2]
    · rw [if_neg h2]; simp
  · rw [if_neg h]; simp

theorem head_foldl_push (z : List ℕ) : ∀ (t : List ℕ) (x : ℕ), t.head? = some x → (z.foldl push t).head? = some x := by
  induction z with
  | nil => intro t x h; exact h
  | cons a z ih =>
    intro t x h
    cases t with
    | nil => simp at h
    | cons x' t' =>
      simp only [List.head?_cons, Option.some.injEq] at h; subst h
      exact ih _ _ (head_push t' x' a)

theorem head_typical_cons (a : ℕ) (l : List ℕ) : (typical (a :: l)).head? = some a := by
  have : typical (a :: l) = l.foldl push [a] := by
    simp [typical, push_nil]
  rw [this]
  exact head_foldl_push l [a] a rfl

theorem take_one_of_head {l : List ℕ} {a : ℕ} (h : l.head? = some a) : l.take 1 = [a] := by
  cases l with
  | nil => simp at h
  | cons b l => simp at h; simp [h]

/-- The first entry of a concatenation's typical sequence is the first entry of the first part. -/
theorem typical_append_take_one {y : List ℕ} (hy : y ≠ []) (z : List ℕ) :
    (typical (y ++ z)).take 1 = y.take 1 := by
  cases y with
  | nil => exact absurd rfl hy
  | cons a l =>
    rw [List.cons_append, take_one_of_head (head_typical_cons a (l ++ z))]
    simp

/-! ## non-empty sequences -/

mutual
/-- All run sequences are non-empty. -/
def YNe : CT → Prop
  | node S y ks => y ≠ [] ∧ YNeL ks
def YNeL : List CT → Prop
  | [] => True
  | k :: ks => YNe k ∧ YNeL ks
end

theorem YNeL_iff {ks : List CT} : YNeL ks ↔ ∀ k ∈ ks, YNe k := by
  induction ks with
  | nil => simp [YNeL]
  | cons k ks ih => simp [YNeL, ih]

/-! ## the relabelling -/

/-- Forget the vertex `x` from every label. -/
abbrev rl (x : ℕ) : CT → CT := relabel (fun S => S.erase x)

theorem rl_node (x : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    rl x (node S y ks) = node (S.erase x) y (ks.map (rl x)) := relabel_node _ _ _ _

/-- `norm ∘ rl x`. -/
def g (x : ℕ) (n : CT) : CT := norm (rl x n)

theorem norm_rl_node (x : ℕ) (S : Finset ℕ) (y : List ℕ) (F : List CT) :
    norm (rl x (node S y F)) = normF (S.erase x) y ((F.map (g x)).filter (keep (S.erase x))) := by
  rw [rl_node, norm_node', List.map_map]; rfl

/-- A pruned kid stays pruned. -/
theorem keep_g_false (x : ℕ) {S : Finset ℕ} {n : CT} (h : keep S n = false) :
    keep (S.erase x) (g x n) = false := by
  obtain ⟨h1, h2⟩ := keep_eq_false_iff.1 h
  obtain ⟨Sn, yn, kn⟩ := n
  simp only [CT.kids, CT.S] at h1 h2; subst h1
  unfold g
  rw [rl_node, norm_node']
  simp only [List.map_nil, List.filter_nil, normF_nil]
  rw [keep_eq_false_iff]
  exact ⟨rfl, Finset.erase_subset_erase x h2⟩

theorem filter_g (x : ℕ) (S : Finset ℕ) (K : List CT) :
    (K.map (g x)).filter (keep (S.erase x)) = ((K.filter (keep S)).map (g x)).filter (keep (S.erase x)) := by
  induction K with
  | nil => rfl
  | cons n K ih =>
    by_cases hn : keep S n = true
    · simp [List.filter_cons, hn, ih]
    · have hn' : keep S n = false := by simpa using hn
      have := keep_g_false x hn'
      simp [List.filter_cons, hn', this, ih]

/-- A permutation of the (filtered) kids with distinct keys does not change the normal form. -/
theorem normF_perm {S : Finset ℕ} {y : List ℕ} {L1 L2 : List CT} (hp : L1.Perm L2)
    (hd : L2.Pairwise (fun a b => key S a ≠ key S b)) : normF S y L1 = normF S y L2 := by
  match L1, L2, hp, hd with
  | [], [], _, _ => rfl
  | [], _ :: _, hp, _ => exact absurd hp.length_eq (by simp)
  | _ :: _, [], hp, _ => exact absurd hp.length_eq (by simp)
  | [a], [b], hp, _ =>
    have : a = b := by simpa using hp.eq_singleton
    subst this; rfl
  | [a], _ :: _ :: _, hp, _ => exact absurd hp.length_eq (by simp)
  | _ :: _ :: _, [b], hp, _ => exact absurd hp.length_eq (by simp)
  | a :: b :: t, c :: d :: u, hp, hd =>
    rw [normF_ge2, normF_ge2]
    congr 1
    haveI : Std.Symm (fun a b : CT => key S a ≠ key S b) := ⟨fun a b h => Ne.symm h⟩
    apply List.Perm.eq_of_pairwise (le := fun a b => key S a ≤ key S b)
    · intro a b ha hb h1 h2
      have ha' : a ∈ c :: d :: u := (sortKids_perm S _).mem_iff.1 ha |> hp.mem_iff.1
      have hb' : b ∈ c :: d :: u := (sortKids_perm S _).mem_iff.1 hb
      by_contra hne
      exact hd.forall ha' hb' hne (le_antisymm h1 h2)
    · exact sortKids_pairwise _ _
    · exact sortKids_pairwise _ _
    · exact ((sortKids_perm S _).trans hp).trans (sortKids_perm S _).symm

theorem g_node (x : ℕ) (S : Finset ℕ) (y : List ℕ) (F : List CT) :
    g x (node S y F) = normF (S.erase x) y ((F.map (g x)).filter (keep (S.erase x))) := norm_rl_node x S y F

theorem keep_normF_nil (S : Finset ℕ) (y : List ℕ) : keep S (normF S y []) = false := by
  rw [keep_eq_false_iff]; exact ⟨rfl, subset_rfl⟩

theorem keep_normF_ne {S : Finset ℕ} {y : List ℕ} {N : List CT} (hN : N ≠ []) (hk : ∀ n ∈ N, keep S n = true) :
    keep S (normF S y N) = true := by
  rw [keep_eq_true_iff]
  match N, hN, hk with
  | [k'], _, hk =>
    rw [normF_single]
    have hk' := keep_eq_true_iff.1 (hk k' (by simp))
    split_ifs with hS
    · intro ⟨h1, h2⟩
      exact hk' ⟨h1, by rw [hS]⟩
    · intro ⟨h1, _⟩; exact absurd h1 (by simp [CT.kids])
  | a :: b :: t, _, hk =>
    rw [normF_ge2]
    intro ⟨h1, _⟩
    exact sortKids_ne_nil (by simp) h1

theorem take_take_one (y : List ℕ) : (y.take 1).take 1 = y.take 1 := by simp [List.take_take]

theorem typ_assoc_l (a b c : List ℕ) : typical (typical (a ++ b) ++ c) = typical (a ++ b ++ c) :=
  (typical_append_typical_left (a ++ b) c).symm

theorem typ_assoc_r (a b c : List ℕ) : typical (a ++ typical (b ++ c)) = typical (a ++ (b ++ c)) :=
  (typical_append_typical_right a (b ++ c)).symm

/-- The one-step invariance, at a node. -/
theorem nrn_step (x : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) (hy : y ≠ [])
    (hd : ((ks.map (g x)).filter (keep (S.erase x))).Pairwise
      (fun a b => key (S.erase x) a ≠ key (S.erase x) b))
    (IH : ∀ k ∈ ks, g x (norm k) = g x k) :
    norm (rl x (norm (node S y ks))) = norm (rl x (node S y ks)) := by
  have hK : ks.map (g x) = (ks.map norm).map (g x) := by
    rw [List.map_map]; apply List.map_congr_left; intro k hk; exact (IH k hk).symm
  rw [hK, filter_g x S (ks.map norm)] at hd
  rw [norm_node', norm_rl_node, hK, filter_g x S (ks.map norm)]
  generalize (ks.map norm).filter (keep S) = F0 at hd ⊢
  match F0, hd with
  | [], _ =>
    simp [normF_nil, norm_rl_node, take_take_one]
  | [k], _ =>
    obtain ⟨Sk, yk, kk⟩ := k
    rw [normF_single]
    by_cases hS : (node Sk yk kk).S = S
    · rw [if_pos hS]
      simp only [CT.S] at hS; subst hS
      simp only [CT.kids, CT.y]
      rw [norm_rl_node]
      simp only [List.map_cons, List.map_nil]
      rw [g_node]
      generalize hN : (kk.map (g x)).filter (keep (Sk.erase x)) = N
      have hkeep : ∀ n ∈ N, keep (Sk.erase x) n = true := by
        intro n hn; rw [← hN] at hn; exact (List.mem_filter.1 hn).2
      match N, hN, hkeep with
      | [], hN, _ =>
        rw [List.filter_cons_of_neg (by rw [keep_normF_nil]; simp), List.filter_nil, normF_nil, normF_nil,
          typical_append_take_one hy]
      | [k'], hN, hkeep =>
        have hM : keep (Sk.erase x) (normF (Sk.erase x) yk [k']) = true :=
          keep_normF_ne (by simp) hkeep
        rw [List.filter_cons_of_pos hM, List.filter_nil, normF_single (Sk.erase x) y, normF_S, if_pos rfl,
          normF_single (Sk.erase x) yk k', normF_single (Sk.erase x) _ k']
        by_cases hk' : k'.S = Sk.erase x
        · simp only [if_pos hk', CT.y, CT.kids]
          rw [typ_assoc_l, typ_assoc_r, List.append_assoc]
        · simp only [if_neg hk', CT.y, CT.kids]
      | a :: b :: t, hN, hkeep =>
        have hM : keep (Sk.erase x) (normF (Sk.erase x) yk (a :: b :: t)) = true :=
          keep_normF_ne (by simp) hkeep
        rw [List.filter_cons_of_pos hM, List.filter_nil, normF_single (Sk.erase x) y, normF_S, if_pos rfl,
          normF_ge2, normF_ge2]
        rfl
    · rw [if_neg hS, norm_rl_node]
  | a :: b :: t, hd =>
    rw [normF_ge2, norm_rl_node]
    apply normF_perm _ hd
    exact ((List.Perm.map _ (sortKids_perm S _)).filter _)

mutual
theorem g_norm_rec (x : ℕ) : ∀ q : CT, Conn q → YNe q → g x (norm q) = g x q
  | node S y ks, hc, hy => by
    have IH := g_normL_rec x ks hc.1 hy.2
    have hk : KidsConn (S.erase x) (ks.map (rl x)) := by
      have := conn_relabel_erase x _ hc
      rw [relabel_node, conn_node] at this
      exact this
    have hd : ((ks.map (g x)).filter (keep (S.erase x))).Pairwise
        (fun a b => key (S.erase x) a ≠ key (S.erase x) b) := by
      have := survivors_keys_distinct hk
      rw [List.map_map] at this
      exact this
    exact nrn_step x S y ks hy.1 hd IH
theorem g_normL_rec (x : ℕ) : ∀ ks : List CT, ConnL ks → YNeL ks → ∀ k ∈ ks, g x (norm k) = g x k
  | [], _, _, k, hk => by simp at hk
  | k' :: ks, hc, hy, k, hk => by
    rcases List.mem_cons.1 hk with e | hk
    · rw [e]; exact g_norm_rec x k' hc.1 hy.1
    · exact g_normL_rec x ks hc.2 hy.2 k hk
end

theorem g_norm_pair : (type_of% @g_norm_rec) ∧ (type_of% @g_normL_rec) :=
  ⟨@g_norm_rec, @g_normL_rec⟩

theorem g_norm : type_of% @g_norm_rec := g_norm_pair.1

/-- **Confluence of the normal form** under forgetting a vertex (repaired statement: `f = erase x`, `p` connected with
non-empty sequences; see the module docstring). -/
theorem norm_relabel_norm (x : ℕ) {p : CT} (hc : Conn p) (hy : YNe p) :
    norm (relabel (fun S => S.erase x) (norm p)) = norm (relabel (fun S => S.erase x) p) :=
  g_norm x p hc hy

end CT

end Lax117284Proofs.Treewidth.Chars
