import Lax117284Proofs.Treewidth.Chars.IntroJunk
import Lax117284Proofs.Treewidth.Chars.IntroPrefix
import Lax117284Proofs.Treewidth.Chars.IntroMono

/-!
# Set-up for the main induction of `char_intro_dom` (work package C4, part 9)

The source `a = norm (uT P)` and the target `T = norm (fT v P)` of a flagged profile tree `P = node S e w ks` are both
`normF` of a list of kids obtained from the kept kids; on the source side the kept kids are sorted by key
(`order`).  Shapes of `a`: *non-merge* (`node S [e] (order.map gA)`) or *merge* (a single kept kid with the same label).
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## comparing normal forms up to a permutation -/

theorem align' {S1 : Finset ℕ} {y y' : List ℕ} (hy : Dom y y') {X : Type} (τ : List X) (h1 h2 : X → CT)
    (L2 : List CT) (hperm : (τ.map h2).Perm L2) (hd : ∀ K ∈ τ, DomC (h1 K) (h2 K))
    (hkd : L2.Pairwise (fun a b => key S1 a ≠ key S1 b)) :
    DomC (normF S1 y (τ.map h1)) (normF S1 y' L2) := by
  have hL : DomCL (τ.map h1) (τ.map h2) := by
    rw [domCL_iff, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 hd
  have h := normF_mono (S := S1) hy hL
  rw [normF_perm hperm hkd] at h
  exact h

/-- The merge comparison: a run `node S' y1 kids1` dominating the kid `T1` and prefixed by the exact entry list `e'`
is dominated by the merge of `e'` with `T1`. -/
theorem merge_cmp {S' : Finset ℕ} {e' : List ℕ} (he : e' ≠ []) {y1 : List ℕ} {kids1 : List CT} {T1 : CT}
    (h : DomC (norm (CT.node S' y1 kids1)) T1) (hk : keep S' T1 = true) :
    DomC (norm (CT.node S' (e' ++ y1) kids1)) (normF S' e' [T1]) := by
  set F1 := (kids1.map norm).filter (keep S') with hF1
  have hF : ∀ k ∈ F1, keep S' k = true := fun k hk => (List.mem_filter.1 hk).2
  have h1 : norm (CT.node S' y1 kids1) = normF S' y1 F1 := norm_node' _ _ _
  have h2 : norm (CT.node S' (e' ++ y1) kids1) = normF S' (e' ++ y1) F1 := norm_node' _ _ _
  rw [h1] at h
  have hkeep : keep S' (normF S' y1 F1) = true := by rw [domC_keep S' h]; exact hk
  have hML := normF_merge S' he hF (y := y1)
  rw [List.filter_cons_of_pos hkeep, List.filter_nil] at hML
  rw [h2]
  have hA : DomC (normF S' (e' ++ y1) F1) (normF S' (typical (e' ++ y1)) F1) :=
    normF_mono (domEquiv_typical (e' ++ y1)).2 (domCL_iff.2 (List.forall₂_same.2 (fun k _ => DomC.refl k)))
  have hB : DomC (normF S' e' [normF S' y1 F1]) (normF S' e' [T1]) :=
    normF_mono (Dom.refl e') ⟨h, trivial⟩
  rw [← hML] at hA
  exact DomC.trans hA hB

theorem winR_cov_ge {v : ℕ} {S : Finset ℕ} {y : List ℕ} {ks : List CT} {r : CT} {c : Finset ℕ}
    (h : WinR v (node S y ks) r c) : S ⊆ c := by
  rcases h with ⟨d1, d2, hd, rfl, rfl⟩ | ⟨kids, cv, hk, rfl, rfl⟩
  · exact subset_rfl
  · exact Finset.subset_union_left

theorem kidR_of_forall (v : ℕ) {X : Type} (g : X → CT) (rk : X → CT)
    (ck : X → Finset ℕ) : ∀ τ : List X,
    (∀ K ∈ τ, (rk K = g K ∧ ck K = ∅) ∨ WinR v (g K) (rk K) (ck K)) →
    ∃ cv, KidR v (τ.map g) (τ.map rk) cv ∧ ∀ K ∈ τ, ck K ⊆ cv := by
  intro τ
  induction τ with
  | nil => intro _; exact ⟨∅, ⟨rfl, rfl⟩, by simp⟩
  | cons K τ ih =>
    intro h
    obtain ⟨cv, hkid, hsub⟩ := ih (fun K' hK' => h K' (List.mem_cons_of_mem _ hK'))
    refine ⟨ck K ∪ cv, ⟨rk K, τ.map rk, ck K, cv, rfl, rfl, ?_, hkid⟩, ?_⟩
    · rcases h K List.mem_cons_self with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr h1
    · intro K' hK'
      rcases List.mem_cons.1 hK' with rfl | hK'
      · exact Finset.subset_union_left
      · exact (hsub K' hK').trans Finset.subset_union_right

namespace FT

/-- The normalised source profile of a kid. -/
def gA (K : FT) : CT := norm (uT K)
/-- The normalised target profile of a kid. -/
def fN (v : ℕ) (K : FT) : CT := norm (fT v K)
/-- The kids that survive the pruning on the source side. -/
def kept (S : Finset ℕ) (ks : List FT) : List FT := ks.filter (fun K => keep S (gA K))
/-- ... in the order of the source characteristic. -/
def order (S : Finset ℕ) (ks : List FT) : List FT :=
  (kept S ks).mergeSort (fun A B => decide (key S (gA A) ≤ key S (gA B)))
/-- The kids that survive the pruning on the target side. -/
def fkept (v : ℕ) (S1 : Finset ℕ) (ks : List FT) : List FT := ks.filter (fun K => keep S1 (fN v K))

theorem mem_kept {S : Finset ℕ} {ks : List FT} {K : FT} : K ∈ kept S ks ↔ K ∈ ks ∧ keep S (gA K) = true := by
  simp [kept]

theorem order_perm (S : Finset ℕ) (ks : List FT) : (order S ks).Perm (kept S ks) :=
  List.mergeSort_perm _ _

theorem sort_eq (S : Finset ℕ) (ks : List FT) :
    sortKids S ((kept S ks).map gA) = (order S ks).map gA := by
  unfold sortKids order
  exact (List.map_mergeSort (l := kept S ks) (f := gA)
    (r := fun A B => decide (key S (gA A) ≤ key S (gA B)))
    (s := fun a b => decide (key S a ≤ key S b)) (fun a _ b _ => rfl)).symm

theorem a_eq (S : Finset ℕ) (e : ℕ) (w : Bool) (ks : List FT) :
    norm (uT (node S e w ks)) = normF S [e] ((kept S ks).map gA) := by
  rw [uT_node, norm_node']
  congr 1
  rw [List.map_map]
  show (ks.map (fun K => norm (uT K))).filter (keep S) = (ks.filter (fun K => keep S (gA K))).map gA
  rw [List.filter_map]
  rfl

theorem T_eq (v : ℕ) (S : Finset ℕ) (e : ℕ) (w : Bool) (ks : List FT) :
    norm (fT v (node S e w ks)) =
      normF (if w then insert v S else S) [if w then e + 1 else e]
        ((fkept v (if w then insert v S else S) ks).map (fN v)) := by
  rw [fT_node, norm_node']
  congr 1
  rw [List.map_map]
  show (ks.map (fun K => norm (fT v K))).filter (keep (if w then insert v S else S)) =
    (ks.filter (fun K => keep (if w then insert v S else S) (fN v K))).map (fN v)
  rw [List.filter_map]
  rfl

theorem a_nonmerge (S : Finset ℕ) (e : ℕ) (w : Bool) (ks : List FT)
    (h : ∀ K1, kept S ks = [K1] → (gA K1).S ≠ S) :
    norm (uT (node S e w ks)) = CT.node S [e] ((order S ks).map gA) := by
  rw [a_eq]
  have hs := sort_eq S ks
  generalize hσ : kept S ks = σ at hs ⊢
  have hord : order S ks = σ.mergeSort (fun A B => decide (key S (gA A) ≤ key S (gA B))) := by
    rw [order, hσ]
  match σ, hσ, hord, hs with
  | [], _, hord, hs =>
    rw [hord]; simp [normF_nil]
  | [K1], hσ, hord, hs =>
    rw [hord]
    simp only [List.map_cons, List.map_nil]
    rw [normF_single, if_neg (h K1 hσ)]
    simp
  | K1 :: K2 :: rest, hσ, hord, hs =>
    simp only [List.map_cons] at hs ⊢
    rw [normF_ge2, hs]

theorem a_merge (S : Finset ℕ) (e : ℕ) (w : Bool) (ks : List FT) {K1 : FT} (hσ : kept S ks = [K1])
    (hS : (gA K1).S = S) :
    norm (uT (node S e w ks)) = CT.node S (typical ([e] ++ (gA K1).y)) (gA K1).kids := by
  rw [a_eq, hσ]
  simp only [List.map_cons, List.map_nil]
  rw [normF_single, if_pos hS]

end FT

end Lax117284Proofs.Treewidth.Chars
