import Lax117284Proofs.Treewidth.Chars.Norm
import Lax117284Proofs.Treewidth.Chars.Alg
import Lax117284Proofs.Treewidth.Seq.Concat

/-!
# Characteristics through the analysis: `norm (profF f B t) = (analyze B t).charF f` (C3)

The normal form of a profile depends on the *shape and labels* of the tree only; the sizes enter through the exact
sequences of the chains.  We make this precise: for an arbitrary "size function" `f : Finset ℕ → ℕ` on bags,

* `RT.profF f B t` is the profile of `t` with sizes `f X` instead of `|X|`;
* `AR.charF f` reads a characteristic off an analysis with sizes `f (bag)`;
* `norm_profF : norm (profF f B t) = (analyze B t).charF f`.

Since `analyze B t` does not depend on `f`, the characteristics of `t` and of its restrictions (whose sizes are
`|X ∩ U|`) are all read off the *same* analysis.  This is what makes the exact join layer a run-wise statement.
-/

namespace Lax117284Proofs.Treewidth.Trees.RT

open Lax117284Proofs.Treewidth.Chars

mutual
/-- The profile with sizes `f X` (instead of `|X|`). -/
def profF (f : Finset ℕ → ℕ) (B : Finset ℕ) : RT → CT
  | .node X ks => .node (X ∩ B) [f X] (profFL f B ks)
def profFL (f : Finset ℕ → ℕ) (B : Finset ℕ) : List RT → List CT
  | [] => []
  | k :: ks => profF f B k :: profFL f B ks
end

theorem profFL_eq (f : Finset ℕ → ℕ) (B : Finset ℕ) : ∀ ks : List RT, profFL f B ks = ks.map (profF f B)
  | [] => rfl
  | k :: ks => by simp [profFL, profFL_eq f B ks]

theorem profF_node (f : Finset ℕ → ℕ) (B X : Finset ℕ) (ks : List RT) :
    profF f B (.node X ks) = .node (X ∩ B) [f X] (ks.map (profF f B)) := by
  simp [profF, profFL_eq]

theorem prof_node (B X : Finset ℕ) (ks : List RT) :
    prof B (.node X ks) = .node (X ∩ B) [X.card] (ks.map (prof B)) := by
  have h : ∀ ks : List RT, profL B ks = ks.map (prof B) := by
    intro ks
    induction ks with
    | nil => rfl
    | cons k ks ih => simp [profL, ih]
  simp [prof, h]

theorem prof_eq_profF (B : Finset ℕ) : ∀ t : RT, prof B t = profF Finset.card B t := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    rw [prof_node, profF_node]
    congr 1
    exact List.map_congr_left ih

/-- Restricting to `U ⊇ B` changes only the sizes. -/
theorem prof_restrict {B U : Finset ℕ} (hB : B ⊆ U) (t : RT) :
    prof B (restrict U t) = profF (fun X => (X ∩ U).card) B t := by
  induction t using RT.ind with
  | _ X ks ih =>
    rw [restrict_node, prof_node, profF_node]
    have e : X ∩ U ∩ B = X ∩ B := by
      ext x; simp only [Finset.mem_inter]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, hB h2⟩, h2⟩
    rw [e]
    congr 1
    rw [List.map_map]
    exact List.map_congr_left (fun k hk => ih k hk)

end Lax117284Proofs.Treewidth.Trees.RT

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## induction on `AR` -/

mutual
theorem AR.ind_rec {P : AR → Prop} (h : ∀ S c ks, (∀ k ∈ ks, P k) → P (.run S c ks)) : ∀ r, P r
  | .run S c ks => h S c ks (AR.indL_rec h ks)
theorem AR.indL_rec {P : AR → Prop} (h : ∀ S c ks, (∀ k ∈ ks, P k) → P (.run S c ks)) :
    ∀ ks : List AR, ∀ k ∈ ks, P k
  | [] => by simp
  | k' :: ks => by
    intro k hk
    rcases List.mem_cons.1 hk with e | hk
    · exact e ▸ AR.ind_rec h k'
    · exact AR.indL_rec h ks k hk
end

theorem AR.ind_pair : (type_of% @AR.ind_rec) ∧ (type_of% @AR.indL_rec) :=
  ⟨@AR.ind_rec, @AR.indL_rec⟩

theorem AR.ind : type_of% @AR.ind_rec := AR.ind_pair.1

/-! ## `charF` -/

mutual
/-- The characteristic read off an analysis, with sizes `f (bag)` along the chains. -/
def AR.charF (f : Finset ℕ → ℕ) : AR → CT
  | .run S c ks => CT.node S (typical (c.map (fun n => f n.bag))) (AR.charFL f ks)
def AR.charFL (f : Finset ℕ → ℕ) : List AR → List CT
  | [] => []
  | k :: ks => AR.charF f k :: AR.charFL f ks
end

theorem AR.charFL_eq (f : Finset ℕ → ℕ) : ∀ ks : List AR, AR.charFL f ks = ks.map (AR.charF f)
  | [] => rfl
  | k :: ks => by simp [AR.charFL, AR.charFL_eq f ks]

theorem AR.charF_run (f : Finset ℕ → ℕ) (S : Finset ℕ) (c : List CNode) (ks : List AR) :
    AR.charF f (.run S c ks) = CT.node S (typical (c.map (fun n => f n.bag))) (ks.map (AR.charF f)) := by
  simp [AR.charF, AR.charFL_eq]

theorem AR.charL_eq : ∀ ks : List AR, AR.charL ks = ks.map AR.char
  | [] => rfl
  | k :: ks => by simp [AR.charL, AR.charL_eq ks]

theorem AR.char_run (S : Finset ℕ) (c : List CNode) (ks : List AR) :
    AR.char (.run S c ks) = CT.node S (typical (c.map (fun n => n.bag.card))) (ks.map AR.char) := by
  simp [AR.char, AR.charL_eq]

theorem AR.char_eq_charF : ∀ r : AR, AR.char r = AR.charF Finset.card r := by
  intro r
  induction r using AR.ind with
  | _ S c ks ih =>
    rw [AR.char_run, AR.charF_run]
    congr 1
    exact List.map_congr_left ih

@[simp] theorem AR.S_charF (f : Finset ℕ → ℕ) (r : AR) : (AR.charF f r).S = r.S := by
  cases r; rfl

theorem AR.isLeaf_charF (f : Finset ℕ → ℕ) (r : AR) : (AR.charF f r).isLeaf = r.isLeaf := by
  cases r with
  | run S c ks => cases ks <;> simp [AR.charF_run, CT.isLeaf, AR.isLeaf, CT.kids, AR.kids]

theorem AR.keep_charF (f : Finset ℕ → ℕ) (S : Finset ℕ) (r : AR) :
    CT.keep S (AR.charF f r) = !(r.isLeaf && decide (r.S ⊆ S)) := by
  simp [CT.keep, AR.isLeaf_charF]

theorem AR.verts_charF_eq (f g : Finset ℕ → ℕ) : ∀ r : AR, CT.verts (AR.charF f r) = CT.verts (AR.charF g r) := by
  intro r
  induction r using AR.ind with
  | _ S c ks ih =>
    rw [AR.charF_run, AR.charF_run]
    ext v
    rw [CT.mem_verts, CT.mem_verts]
    simp only [List.mem_map]
    constructor
    · rintro (h | ⟨_, ⟨k, hk, rfl⟩, hv⟩)
      · exact Or.inl h
      · exact Or.inr ⟨_, ⟨k, hk, rfl⟩, (ih k hk) ▸ hv⟩
    · rintro (h | ⟨_, ⟨k, hk, rfl⟩, hv⟩)
      · exact Or.inl h
      · exact Or.inr ⟨_, ⟨k, hk, rfl⟩, (ih k hk).symm ▸ hv⟩

theorem AR.key_char (f : Finset ℕ → ℕ) (S : Finset ℕ) (r : AR) :
    CT.key S r.char = CT.key S (AR.charF f r) := by
  unfold CT.key
  rw [AR.char_eq_charF, AR.verts_charF_eq Finset.card f]

/-! ## the sorting commutes with `charF` -/

theorem sortAR_charF (f : Finset ℕ → ℕ) (S : Finset ℕ) (l : List AR) :
    (sortAR S l).map (AR.charF f) = CT.sortKids S (l.map (AR.charF f)) := by
  unfold sortAR CT.sortKids
  apply List.map_mergeSort
  intro a _ b _
  simp only [AR.key_char f]

/-! ## the case analysis of `analyzeNode` -/

/-- The three cases of `analyzeNode`, as a function of the surviving kids. -/
def mkNode (S X : Finset ℕ) (junk : List RT) : List AR → AR
  | [] => .run S [⟨X, junk⟩] []
  | [k] => if k.S = S then .run S (⟨X, junk⟩ :: k.chain) k.kids else .run S [⟨X, junk⟩] [k]
  | a :: b :: t => .run S [⟨X, junk⟩] (sortAR S (a :: b :: t))

theorem typical_single (z : ℕ) : typical [z] = [z] := by simp [typical, push_nil]

theorem normF_charF (f : Finset ℕ → ℕ) (S X : Finset ℕ) (junk : List RT) :
    ∀ core : List AR, normF S [f X] (core.map (AR.charF f)) = (mkNode S X junk core).charF f := by
  intro core
  match core with
  | [] =>
    simp [normF_nil, mkNode, AR.charF_run, typical_single]
  | [k] =>
    rw [List.map_singleton, normF_single]
    obtain ⟨S', c, ks⟩ := k
    have e1 : (AR.charF f (.run S' c ks)).S = S' := by simp [AR.S_charF, AR.S]
    rw [e1]
    by_cases h : S' = S
    · subst h
      simp only [mkNode, AR.S, if_true, AR.chain, AR.kids, AR.charF_run, List.map_cons, CT.y, CT.kids]
      rw [← typical_append_typical_right [f X] (c.map (fun n => f n.bag))]
      rfl
    · simp [mkNode, AR.S, h, AR.charF_run, typical_single]
  | a :: b :: t =>
    rw [List.map_cons, List.map_cons, normF_ge2]
    simp only [mkNode, AR.charF_run, List.map_cons, List.map_nil, typical_single]
    rw [← List.map_cons, ← List.map_cons, sortAR_charF]

theorem analyzeL_eq (B : Finset ℕ) : ∀ ks : List RT, analyzeL B ks = ks.map (fun k => (k, analyze B k))
  | [] => rfl
  | k :: ks => by simp [analyzeL, analyzeL_eq B ks]

theorem analyze_node (B X : Finset ℕ) (ks : List RT) :
    analyze B (.node X ks) = analyzeNode B X (ks.map (fun k => (k, analyze B k))) := by
  simp [analyze, analyzeL_eq]

theorem analyzeNode_eq (B X : Finset ℕ) (kids : List (RT × AR)) :
    analyzeNode B X kids =
      mkNode (X ∩ B) X ((kids.filter (fun p => p.2.isLeaf && decide (p.2.S ⊆ X ∩ B))).map Prod.fst)
        ((kids.filter (fun p => !(p.2.isLeaf && decide (p.2.S ⊆ X ∩ B)))).map Prod.snd) := by
  unfold analyzeNode
  dsimp only
  generalize ((kids.filter (fun p => !(p.2.isLeaf && decide (p.2.S ⊆ X ∩ B)))).map Prod.snd) = core
  rcases core with _ | ⟨k, _ | ⟨k2, t⟩⟩ <;> rfl

theorem filter_keep_map (f : Finset ℕ → ℕ) (S : Finset ℕ) :
    ∀ L : List (RT × AR), ((L.map (fun p => AR.charF f p.2)).filter (CT.keep S)) =
      ((L.filter (fun p => !(p.2.isLeaf && decide (p.2.S ⊆ S)))).map Prod.snd).map (AR.charF f)
  | [] => rfl
  | p :: L => by
    simp only [List.map_cons, List.filter_cons, AR.keep_charF]
    split <;> simp [filter_keep_map f S L, *]

/-- **The characteristic of a profile is read off the analysis.** -/
theorem norm_profF (f : Finset ℕ → ℕ) (B : Finset ℕ) : ∀ t : RT, norm (RT.profF f B t) = (analyze B t).charF f := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    rw [RT.profF_node, norm_node', analyze_node, analyzeNode_eq]
    have e1 : (ks.map (RT.profF f B)).map norm = ks.map (fun k => (analyze B k).charF f) := by
      rw [List.map_map]; exact List.map_congr_left (fun k hk => ih k hk)
    rw [e1]
    have e2 : ks.map (fun k => (analyze B k).charF f) =
        (ks.map (fun k => (k, analyze B k))).map (fun p => AR.charF f p.2) := by
      rw [List.map_map]; rfl
    rw [e2, filter_keep_map, normF_charF]

/-- `analyze` computes the characteristic (`RT.char`). -/
theorem char_eq_charF (B : Finset ℕ) (t : RT) : t.char B = (analyze B t).charF Finset.card := by
  unfold RT.char
  rw [RT.prof_eq_profF, norm_profF]

end Lax117284Proofs.Treewidth.Chars
