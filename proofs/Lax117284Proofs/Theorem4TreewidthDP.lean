import Lax117284Proofs.ConflictGraph
import Lax117284Proofs.Treewidth

/-!
# Theorem 4, second bullet: fixed-parameter tractability for `m + τ`

> **Theorem 19.** `1 | rep | min_j ∑_i Z_{i,j}` is solvable in `2^{O(τm)} · n` time.
>
> We will be particularly interested in schedules that are defined only on subsets of
> clients. Let `X ⊆ V`. We say that a schedule `σ = (σ₁,…,σ_m)` is *defined on `X`* if
> `σ_i ⊆ X` for each day `i`. We say that `σ` is *feasible and fair on `X`* if `σ` is
> feasible, defined on `X`, and we have `∑_j Z_{i,j} ≥ k` for each client `j ∈ X`. […] We
> let `Σ(X)` denote the set of all feasible and fair schedules on `X`.
>
> We compute a dynamic programming table `T` on the nodes of `𝒯`, in bottom-up fashion, to
> determine whether the set `Σ(X)` is non-empty. For any node `X` of `𝒯`, and any schedule
> `σ ∈ Σ(X)`, we have a corresponding entry `T[X, σ]` in `T` where the following invariant
> will hold:
> `T[X, σ] = 1 ⟺ σ = σ* ∩ X for some σ* ∈ Σ(V(𝒯_X))`.

`Tab` is that table, written as a predicate on schedules and recursed over the four shapes
of `NiceTree`; `tab_iff` is the invariant, and `exists_tab_iff_hasFairSchedule` is the
theorem it adds up to. The whole argument is `Treewidth.lean`'s two separation lemmas plus
bookkeeping:

* at an **introduce node** the new client `j` has no neighbour deeper in the subtree outside
  the child's bag (`adj_mem_bag_of_intro`), so gluing the child's witness to `σ` cannot
  create a conflict;
* at a **join node** the two subtrees' private parts are non-adjacent (`not_adj_of_join`),
  so the two witnesses can be glued day by day.

Lemma 18's count — `|Σ(X)| = O(2^{τm})` for a bag of at most `τ + 1` clients — is
`card_definedOn_le`. The `2^{O(τm)} · n` running time that it and the table together give is
a resource claim, not yet stated (see `Theorem4.lean`'s FPT wrapper).

Ported from the pre-Lax `FairRIS/Proofs-FairRIS/Theorem19_TreewidthDP.lean`, whose `Instance`
has the same fields as `Lax117284Proofs.Model.Instance` verbatim, and whose `Treewidth.lean`/
`ConflictGraph.lean` this Lax port already carries unchanged.
-/

namespace Lax117284Proofs.Model

namespace Instance

variable {I : Instance}

/-! ## 1. Schedules defined on a set of clients -/

/-- `σ` cut down to the clients of `X`. -/
def restr (X : Finset I.Client) (σ : I.Schedule) : I.Schedule := fun i => σ i ∩ X

@[simp] lemma mem_restr {X : Finset I.Client} {σ : I.Schedule} {i : I.Day} {j : I.Client} :
    j ∈ restr X σ i ↔ j ∈ σ i ∧ j ∈ X := Finset.mem_inter

lemma restr_subset {X : Finset I.Client} (σ : I.Schedule) (i : I.Day) : restr X σ i ⊆ σ i :=
  Finset.inter_subset_left

lemma restr_restr (X Y : Finset I.Client) (σ : I.Schedule) :
    restr X (restr Y σ) = restr (X ∩ Y) σ := by
  funext i
  ext j
  simp only [mem_restr, Finset.mem_inter]
  tauto

lemma restr_eq_self {X : Finset I.Client} {σ : I.Schedule} (h : ∀ i, σ i ⊆ X) :
    restr X σ = σ := by
  funext i
  exact Finset.inter_eq_left.2 (h i)

lemma restr_of_subset {X Y : Finset I.Client} (hXY : X ⊆ Y) (σ : I.Schedule) :
    restr X (restr Y σ) = restr X σ := by
  rw [restr_restr, Finset.inter_eq_left.2 hXY]

lemma served_restr_of_mem {X : Finset I.Client} {σ : I.Schedule} {j : I.Client} (hj : j ∈ X) :
    served (restr X σ) j = served σ j :=
  served_congr fun i => by simp [hj]

variable (I) in
/-- **`Σ(X)`**: the feasible schedules defined on `X` that are fair for every client of
`X`. -/
def Sigma (k : I.Client → ℕ) (X : Finset I.Client) (σ : I.Schedule) : Prop :=
  (∀ i, σ i ⊆ X) ∧ Feasible σ ∧ ∀ j ∈ X, k j ≤ served σ j

variable {k : I.Client → ℕ}

/-- Cutting a member of `Σ(Y)` down to a subset `X ⊆ Y` lands in `Σ(X)`. -/
lemma Sigma.restr {X Y : Finset I.Client} (hXY : X ⊆ Y) {σ : I.Schedule}
    (h : Sigma I k Y σ) : Sigma I k X (restr X σ) := by
  refine ⟨fun i => Finset.inter_subset_right, h.2.1.mono fun i => restr_subset σ i, ?_⟩
  intro j hj
  rw [served_restr_of_mem hj]
  exact h.2.2 j (hXY hj)

/-! ## 2. Lemma 18: how many schedules a bag admits

> **Lemma 18.** Let `X ⊆ V` be a subset of at most `τ + 1` clients. Then
> `|Σ(X)| = O(2^{τm})`, and we can compute `Σ(X)` in `2^{O(τm)}` time. -/

/-! ## 3. The dynamic-programming table -/

variable (k) in
/-- **The table of Theorem 19**, as a predicate: `Tab k T σ` is the paper's `T[X, σ] = 1`
for `X` the bag at the root of `T`. -/
def Tab : NiceTree I.Client → I.Schedule → Prop
  | .leaf b, σ => Sigma I k b σ
  | .intro j c, σ => Sigma I k (insert j c.bag) σ ∧ Tab c (restr c.bag σ)
  | .forget j c, σ => ∃ σ', Tab c σ' ∧ restr (c.bag.erase j) σ' = σ
  | .join l r, σ => Tab l σ ∧ Tab r σ

/-! ### The invariant -/

open NiceTree

/-- **The invariant of Theorem 19's table.** A schedule is in the table at a node exactly
when it is the restriction to that node's bag of a feasible, fair schedule on everything the
subtree covers. -/
theorem tab_iff : ∀ (T : NiceTree I.Client), T.Coherent →
    EdgesCovered I.overallGraph T → ∀ σ : I.Schedule,
      Tab k T σ ↔ ∃ σ', Sigma I k T.verts σ' ∧ restr T.bag σ' = σ := by
  intro T
  induction T with
  | leaf b =>
    intro _ _ σ
    constructor
    · intro h
      exact ⟨σ, h, restr_eq_self h.1⟩
    · rintro ⟨σ', hσ', rfl⟩
      simp only [verts_leaf] at hσ'
      show Sigma I k b (restr b σ')
      rw [restr_eq_self hσ'.1]
      exact hσ'
  | intro j c ih =>
    intro hcoh hcov σ
    obtain ⟨hj, hcohc⟩ := hcoh
    have hcovc : EdgesCovered I.overallGraph c := EdgesCovered.intro_child hj hcov
    constructor
    · rintro ⟨hσbag, hrec⟩
      obtain ⟨σ', hσ', hres⟩ := (ih hcohc hcovc _).1 hrec
      -- glue the child's witness to `σ`
      refine ⟨fun i => σ' i ∪ σ i, ⟨?_, ?_, ?_⟩, ?_⟩
      · intro i x hx
        rcases Finset.mem_union.1 hx with hx | hx
        · exact Finset.mem_insert_of_mem (hσ'.1 i hx)
        · exact Finset.mem_insert.2 ((Finset.mem_insert.1 (hσbag.1 i hx)).imp id
            fun h' => bag_subset_verts c h')
      · -- feasibility
        intro i x hx y hy hne hc
        have key : ∀ a ∈ σ' i, ∀ b ∈ σ i, a ≠ b → ¬ I.Conflict i a b := by
          intro a ha b hb hab hcf
          rcases Finset.mem_insert.1 (hσbag.1 i hb) with rfl | hbc
          · -- `b = j`, which forces `a` into the child's bag
            have hadj : I.overallGraph.Adj b a := ⟨fun hh => hab hh.symm, i, conflict_symm hcf⟩
            have hain : a ∈ c.bag := adj_mem_bag_of_intro hj hcov (hσ'.1 i ha) hadj
            have : a ∈ σ i := by
              have : a ∈ restr c.bag σ' i := mem_restr.2 ⟨ha, hain⟩
              rw [hres] at this
              exact (mem_restr.1 this).1
            exact hσbag.2.1 i a this b hb hab hcf
          · have : b ∈ σ' i := by
              have : b ∈ restr c.bag σ i := mem_restr.2 ⟨hb, hbc⟩
              rw [← hres] at this
              exact (mem_restr.1 this).1
            exact hσ'.2.1 i a ha b this hab hcf
        rcases Finset.mem_union.1 hx with hx | hx <;> rcases Finset.mem_union.1 hy with hy | hy
        · exact hσ'.2.1 i x hx y hy hne hc
        · exact key x hx y hy hne hc
        · exact key y hy x hx (Ne.symm hne) (conflict_symm hc)
        · exact hσbag.2.1 i x hx y hy hne hc
      · -- fairness
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact le_trans (hσbag.2.2 x (Finset.mem_insert_self _ _))
            (served_mono (fun i => Finset.subset_union_right) x)
        · exact le_trans (hσ'.2.2 x hx) (served_mono (fun i => Finset.subset_union_left) x)
      · -- the restriction is `σ` again
        funext i
        ext x
        simp only [mem_restr, Finset.mem_union]
        constructor
        · rintro ⟨hx | hx, hxb⟩
          · rcases Finset.mem_insert.1 hxb with rfl | hxc
            · exact absurd (hσ'.1 i hx) hj
            · have : x ∈ restr c.bag σ' i := mem_restr.2 ⟨hx, hxc⟩
              rw [hres] at this
              exact (mem_restr.1 this).1
          · exact hx
        · intro hx
          exact ⟨Or.inr hx, hσbag.1 i hx⟩
    · rintro ⟨σ', hσ', rfl⟩
      have hbagsub : insert j c.bag ⊆ insert j c.verts :=
        Finset.insert_subset_insert _ (bag_subset_verts c)
      refine ⟨hσ'.restr hbagsub, ?_⟩
      refine (ih hcohc hcovc _).2 ⟨restr c.verts σ', hσ'.restr (by simp [Finset.subset_insert]), ?_⟩
      simp only [bag_intro]
      rw [restr_of_subset (bag_subset_verts c),
        restr_of_subset (Finset.subset_insert j c.bag)]
  | forget j c ih =>
    intro hcoh hcov σ
    obtain ⟨hjb, hcohc⟩ := hcoh
    have hcovc : EdgesCovered I.overallGraph c := EdgesCovered.forget_child hcov
    simp only [bag_forget, verts_forget]
    constructor
    · rintro ⟨σ'', hrec, rfl⟩
      obtain ⟨σ', hσ', hres⟩ := (ih hcohc hcovc _).1 hrec
      refine ⟨σ', hσ', ?_⟩
      rw [← hres, restr_of_subset (Finset.erase_subset j c.bag)]
    · rintro ⟨σ', hσ', rfl⟩
      refine ⟨restr c.bag σ', (ih hcohc hcovc _).2 ⟨σ', hσ', rfl⟩, ?_⟩
      rw [restr_of_subset (Finset.erase_subset j c.bag)]
  | join l r ihl ihr =>
    intro hcoh hcov σ
    obtain ⟨hbag, hco, hcohl, hcohr⟩ := hcoh
    have hcovl : EdgesCovered I.overallGraph l := EdgesCovered.join_left hco hcov
    have hcovr : EdgesCovered I.overallGraph r := EdgesCovered.join_right hbag hco hcov
    constructor
    · rintro ⟨hl, hr⟩
      obtain ⟨σl, hσl, hresl⟩ := (ihl hcohl hcovl _).1 hl
      obtain ⟨σr, hσr, hresr⟩ := (ihr hcohr hcovr _).1 hr
      refine ⟨fun i => σl i ∪ σr i, ⟨?_, ?_, ?_⟩, ?_⟩
      · intro i x hx
        rcases Finset.mem_union.1 hx with hx | hx
        · exact Finset.mem_union_left _ (hσl.1 i hx)
        · exact Finset.mem_union_right _ (hσr.1 i hx)
      · -- feasibility: the private parts are non-adjacent
        intro i x hx y hy hne hc
        have hmemL : ∀ a, a ∈ σl i → a ∈ l.bag → a ∈ σ i := by
          intro a ha hab
          have h1 : a ∈ restr l.bag σl i := mem_restr.2 ⟨ha, hab⟩
          rw [hresl] at h1
          exact h1
        have hmemR : ∀ a, a ∈ σr i → a ∈ l.bag → a ∈ σ i := by
          intro a ha hab
          have h1 : a ∈ restr r.bag σr i := mem_restr.2 ⟨ha, hbag ▸ hab⟩
          rw [hresr] at h1
          exact h1
        have hbackL : ∀ a, a ∈ σ i → a ∈ σl i := by
          intro a ha
          rw [← hresl] at ha
          exact (mem_restr.1 ha).1
        have hbackR : ∀ a, a ∈ σ i → a ∈ σr i := by
          intro a ha
          rw [← hresr] at ha
          exact (mem_restr.1 ha).1
        have key : ∀ a ∈ σl i, ∀ b ∈ σr i, a ≠ b → ¬ I.Conflict i a b := by
          intro a ha b hb hab hcf
          by_cases hain : a ∈ l.bag
          · exact hσr.2.1 i a (hbackR a (hmemL a ha hain)) b hb hab hcf
          · by_cases hbin : b ∈ l.bag
            · exact hσl.2.1 i a ha b (hbackL b (hmemR b hb hbin)) hab hcf
            · exact not_adj_of_join hco hcov (hσl.1 i ha) hain (hσr.1 i hb) hbin ⟨hab, i, hcf⟩
        rcases Finset.mem_union.1 hx with hx | hx <;> rcases Finset.mem_union.1 hy with hy | hy
        · exact hσl.2.1 i x hx y hy hne hc
        · exact key x hx y hy hne hc
        · exact key y hy x hx (Ne.symm hne) (conflict_symm hc)
        · exact hσr.2.1 i x hx y hy hne hc
      · intro x hx
        rcases Finset.mem_union.1 hx with hx | hx
        · exact le_trans (hσl.2.2 x hx) (served_mono (fun i => Finset.subset_union_left) x)
        · exact le_trans (hσr.2.2 x hx) (served_mono (fun i => Finset.subset_union_right) x)
      · funext i
        ext x
        simp only [mem_restr, Finset.mem_union, bag_join]
        constructor
        · rintro ⟨hx | hx, hxb⟩
          · have h1 : x ∈ restr l.bag σl i := mem_restr.2 ⟨hx, hxb⟩
            rw [hresl] at h1
            exact h1
          · have h1 : x ∈ restr r.bag σr i := mem_restr.2 ⟨hx, hbag ▸ hxb⟩
            rw [hresr] at h1
            exact h1
        · intro hx
          rw [← hresl] at hx
          exact ⟨Or.inl (mem_restr.1 hx).1, (mem_restr.1 hx).2⟩
    · rintro ⟨σ', hσ', rfl⟩
      constructor
      · refine (ihl hcohl hcovl _).2 ⟨restr l.verts σ', hσ'.restr Finset.subset_union_left, ?_⟩
        rw [restr_of_subset (bag_subset_verts l), bag_join]
      · refine (ihr hcohr hcovr _).2 ⟨restr r.verts σ', hσ'.restr Finset.subset_union_right, ?_⟩
        rw [restr_of_subset (bag_subset_verts r), bag_join, hbag]

/-- **Theorem 19's correctness.** The table at the root is non-empty exactly when the
instance has a feasible, fair schedule. -/
theorem exists_tab_iff_hasFairSchedule {T : NiceTree I.Client}
    (h : NiceTree.IsNice I.overallGraph T) :
    (∃ σ, Tab k T σ) ↔ I.HasFairSchedule k := by
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨σ', hσ', -⟩ := (tab_iff T h.coherent (EdgesCovered.of_isNice h) σ).1 hσ
    exact ⟨σ', hσ'.2.1, fun j => hσ'.2.2 j (h.covers j)⟩
  · rintro ⟨σ, hfeas, hfair⟩
    refine ⟨restr T.bag σ, (tab_iff T h.coherent (EdgesCovered.of_isNice h) _).2
      ⟨σ, ⟨fun i x _ => h.covers x, hfeas, fun j _ => hfair j⟩, rfl⟩⟩

end Instance

end Lax117284Proofs.Model
