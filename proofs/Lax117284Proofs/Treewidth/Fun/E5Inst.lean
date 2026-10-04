import Lax117284Proofs.Treewidth.Fun.E1
import Lax117284Proofs.Treewidth.Fun.ToValAlgSize
import Lax117284Proofs.Treewidth.Fun.ToValAlg
import Lax117284Proofs.Treewidth.Chars.Alg
import Lax117284Proofs.Treewidth.Chars.JoinShape
import Lax117284Proofs.Treewidth.Fun.E2
import Lax117284Proofs.Treewidth.Fun.E3
import Lax117284Proofs.Treewidth.Fun.E3Assembly

/-! ### `Lax117284Proofs.Treewidth.Fun.E5Util` -/

section
/-!
# WP E5 (0): generic arithmetic and size lemmas used by the E5 layers

* sums of per-element costs (`sum_map_le_mul`, `sum_map_const`);
* `sz` of `take / drop / filter / map / append / perm` of lists;
* powers `t ^ d` of `t = s + 1` as atoms (`pw_le`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E5

open ToVal

/-! ## sums -/

theorem sum_map_const {α : Type} (l : List α) (c : ℕ) : (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-! ## powers of `t = s + 1` -/

theorem le_pw {t : ℕ} (ht : 1 ≤ t) {d : ℕ} (hd : 1 ≤ d) : t ≤ t ^ d := by
  calc t = t ^ 1 := (pow_one t).symm
    _ ≤ t ^ d := Nat.pow_le_pow_right ht hd

theorem one_le_pw {t : ℕ} (ht : 1 ≤ t) (d : ℕ) : 1 ≤ t ^ d := Nat.one_le_pow _ _ ht

/-! ## sizes of list operations -/

theorem sz_filter_le' {α : Type} [ToVal α] (p : α → Bool) : ∀ l : List α, sz (l.filter p) ≤ sz l
  | [] => by simp
  | a :: l => by
    have ih := sz_filter_le' p l
    rw [List.filter_cons]
    split_ifs
    · rw [sz_cons, sz_cons]; omega
    · rw [sz_cons]; omega

theorem sz_map_le' {α β : Type} [ToVal α] [ToVal β] (f : α → β) : ∀ l : List α,
    (∀ a ∈ l, sz (f a) ≤ sz a) → sz (l.map f) ≤ sz l
  | [], _ => by simp
  | a :: l, h => by
    have h1 := h a (by simp)
    have ih := sz_map_le' f l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.map_cons, sz_cons, sz_cons]; omega

theorem sz_append_le {α : Type} [ToVal α] (l₁ l₂ : List α) : sz (l₁ ++ l₂) ≤ sz l₁ + sz l₂ := by
  have := sz_append l₁ l₂; omega

theorem sz_perm' {α : Type} [ToVal α] {l l' : List α} (h : l.Perm l') : sz l = sz l' := by
  rw [sz_list, sz_list, h.length_eq, (h.map sz).sum_eq]

theorem sz_mem_lt {α : Type} [ToVal α] {a : α} {l : List α} (h : a ∈ l) : sz a + 2 ≤ sz l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [sz_cons]
    rcases List.mem_cons.mp h with rfl | h
    · have := sz_pos l; omega
    · have := ih h; have := sz_pos b; omega

theorem sz_getD_le {α : Type} [ToVal α] (l : List α) (i : ℕ) (d : α) : sz (l.getD i d) ≤ sz l + sz d := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp [sz_cons]; omega
    | succ i => have := ih i; simp only [List.getD_cons_succ, sz_cons]; omega

theorem sz_finset_le_of_subset {S T : Finset ℕ} (h : S ⊆ T) : sz S ≤ sz T := by
  rw [sz_finset, sz_finset]; have := Finset.card_le_card h; omega

theorem sz_inter_le (S T : Finset ℕ) : sz (S ∩ T) ≤ sz S :=
  sz_finset_le_of_subset Finset.inter_subset_left

theorem sz_insert_le (a : ℕ) (S : Finset ℕ) : sz (insert a S) ≤ sz S + 2 := by
  rw [sz_finset, sz_finset]
  have := Finset.card_insert_le a S
  omega

theorem sz_union_le (S T : Finset ℕ) : sz (S ∪ T) ≤ sz S + sz T := by
  rw [sz_finset, sz_finset, sz_finset]
  have := Finset.card_union_le S T
  omega

theorem card_le_sz (S : Finset ℕ) : S.card ≤ sz S := by rw [sz_finset]; omega

/-! ## `typical` does not lengthen -/

theorem typical_length_le_aux (t : List ℕ) : ∀ (a : List ℕ),
    (a.foldl Lax117284Proofs.Treewidth.Seq.push t).length ≤ t.length + a.length
  | [] => by simp
  | y :: a => by
    have h := typical_length_le_aux (Lax117284Proofs.Treewidth.Seq.push t y) a
    have h2 : (Lax117284Proofs.Treewidth.Seq.push t y).length ≤ t.length + 1 := by
      simp only [Lax117284Proofs.Treewidth.Seq.push, List.length_append, List.length_singleton]
      have := E1A.length_cut_le t y; omega
    simp only [List.foldl_cons, List.length_cons]; omega

theorem typical_length_le (a : List ℕ) : (Lax117284Proofs.Treewidth.Seq.typical a).length ≤ a.length := by
  have := typical_length_le_aux [] a
  simpa [Lax117284Proofs.Treewidth.Seq.typical] using this

/-! ## reaching the library / E1 from an extension of `e1Δ` -/

section plumbing
variable {Δ : ℕ → Option Tm}

theorem lib_of (hE : E1.e1Δ ⊑ Δ) : Lib.Δ ⊑ Δ := Ext.trans E1.extLib hE
theorem l1 (hE : E1.e1Δ ⊑ Δ) : Lib1.Δ ⊑ Δ := Ext.trans Lib.ext1 (lib_of hE)
theorem l2 (hE : E1.e1Δ ⊑ Δ) : Lib2.Δ ⊑ Δ := Ext.trans Lib.ext2 (lib_of hE)
theorem l3 (hE : E1.e1Δ ⊑ Δ) : Lib3.Δ ⊑ Δ := Ext.trans Lib.ext3 (lib_of hE)
theorem l4 (hE : E1.e1Δ ⊑ Δ) : Lib4.Δ ⊑ Δ := Ext.trans Lib.ext4 (lib_of hE)
theorem eA (hE : E1.e1Δ ⊑ Δ) : E1A.Δ ⊑ Δ := Ext.trans E1.extA hE
theorem eB (hE : E1.e1Δ ⊑ Δ) : E1B.Δ ⊑ Δ := Ext.trans E1.extB hE
theorem eD (hE : E1.e1Δ ⊑ Δ) : E1D.Δ ⊑ Δ := Ext.trans E1.ext hE
end plumbing

/-- every id of `e1Δ` is `< 158` -/
theorem e1Δ_lt {f : ℕ} {b : Tm} (h : E1.e1Δ f = some b) : f < 158 := by
  unfold E1.e1Δ Lib.extend layerΔ at h
  by_cases h1 : 128 ≤ f
  · simp only [h1, if_true] at h; exact E1.e1Tbl_lt h
  · have := h1
    omega

theorem lt_of_bnd {B s N : ℕ} (hB : 3000 + 400 * (s + 1) < B) (hN : N ≤ 3000) : N < B := by omega

end E5
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E5Ext` -/

section
/-!
# WP E5 (1): the external functions E5 calls, as hypotheses

`E5` embeds `analyze … realJoin`; these call functions owned by other work packages:

| function | owner | id | shape of the hypothesis |
|---|---|---|---|
| `CT.norm` | E2 | `166` (`E5.idNorm`) | `Ext5.norm` : `Runs` for `sz c ≤ s`, cost `cNorm s`, plus `sz (norm c) ≤ sz c` |
| `decide (CT.key S a ≤ CT.key S b)` | E2 | `162` (`E5.idKeyLe`) | `Ext5.keyLe` |
| `CT.domCB` | E2 | `181` (`E5.idDomC`) | `Ext5.domC` (precondition `Ext5.PD`) |
| `CT.joinC` | E2 | `177` (`E5.idJoinC`) | `ExtJ` (precondition `PJ`, cost `cJ`) |
| `CT.introPlans` | E3 | passed at run time (first argument of `realIntro`) | `ExtIP` (precondition `PIP`, cost `cIP`) |

The E2 ids are those of the docstring table of `Fun/E2Defs.lean` (contract: the assembler must use them, or re-point
`E5.idNorm …`).  Every hypothesis has the same shape as the corresponding `E2`/`E3` theorem
(`E2.norm_runs`, `E2.keyLe_runs`, …): *for every `B` above the cost, the function runs within the cost*.  The cost functions
are abstract (`ℕ → ℕ` in the size bound `s`), so nothing here depends on the constants of E2/E3.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E5

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees

abbrev idKeyLe : ℕ := 162
abbrev idNorm : ℕ := 166
abbrev idJoinC : ℕ := 177
abbrev idDomC : ℕ := 181

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The E2 functions used by `sortAR`, `RT.char`, `realIntro`, `realJoin`. -/
structure Ext5 (Δ' : ℕ → Option Tm) where
  cKey : ℕ → ℕ
  keyLe : ∀ (B s : ℕ) (S : Finset ℕ) (a b : CT), sz S ≤ s → sz a ≤ s → sz b ≤ s → cKey s < B →
    Runs Δ' B idKeyLe [toVal S, toVal a, toVal b] (toVal (decide (CT.key S a ≤ CT.key S b))) (cKey s)
  cNorm : ℕ → ℕ
  norm : ∀ (B s : ℕ) (c : CT), sz c ≤ s → cNorm s < B →
    Runs Δ' B idNorm [toVal c] (toVal (CT.norm c)) (cNorm s)
  norm_sz : ∀ c : CT, sz (CT.norm c) ≤ sz c
  /-- precondition of `domCB` (E2: run sequences of both arguments have length `≤ L`, `CT.RB`) -/
  PD : ℕ → CT → CT → Prop
  cDom : ℕ → ℕ
  domC : ∀ (B s : ℕ) (a b : CT), PD s a b → sz a ≤ s → sz b ≤ s → cDom s < B →
    Runs Δ' B idDomC [toVal a, toVal b] (toVal (CT.domCB a b)) (cDom s)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- `CT.joinC` (E2). -/
structure ExtJ (Δ' : ℕ → Option Tm) where
  PJ : ℕ → CT → CT → Prop
  cJ : ℕ → CT → CT → ℕ
  joinC : ∀ (B kmax : ℕ) (a b : CT), PJ kmax a b → cJ kmax a b < B →
    Runs Δ' B idJoinC [toVal kmax, toVal a, toVal b] (toVal (CT.joinC kmax a b)) (cJ kmax a b)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- `CT.introPlans` (E3), called through the id `ip`. -/
structure ExtIP (Δ' : ℕ → Option Tm) where
  ip : ℕ
  PIP : ℕ → Finset ℕ → CT → Prop
  cIP : ℕ → Finset ℕ → CT → ℕ
  introPlans : ∀ (B v : ℕ) (N : Finset ℕ) (t : CT), PIP v N t → cIP v N t < B →
    Runs Δ' B ip [toVal v, toVal N, toVal t] (toVal (CT.introPlans v N t)) (cIP v N t)

end E5
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E5A` -/

section
/-!
# WP E5 (layer A): small helpers, `AR.char`, `AR.toRT`, `RT.prof`, `RT.char`

Ids `448 …`:

| id | function | arguments |
|---|---|---|
| 448 `fNthD` | `List.getD` | `[xs, i, d]` |
| 449 `fCards` | `ns.map (·.bag.card)` | `[ns]` |
| 450 `fCharAR` | `AR.char` | `[r]` |
| 451 `fCharARL` | `AR.charL` | `[ks]` |
| 452 `fChainToRT` | `AR.chainToRT` | `[ns, ks]` |
| 453 `fToRT` | `AR.toRT` | `[r]` |
| 454 `fToRTL` | `AR.toRTL` | `[ks]` |
| 455 `fProf` | `RT.prof B t` | `[B, t]` |
| 456 `fProfL` | `RT.profL B ks` | `[B, ks]` |
| 457 `fChar` | `RT.char B t` (calls `norm`, id `E5.idNorm`) | `[B, t]` |

Cost shape: every function has cost `κ · (#nodes) · (s+1)^d` where `s` bounds the sizes of the arguments.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E5A

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5

abbrev fNthD : ℕ := 448
abbrev fCards : ℕ := 449
abbrev fCharAR : ℕ := 450
abbrev fCharARL : ℕ := 451
abbrev fChainToRT : ℕ := 452
abbrev fToRT : ℕ := 453
abbrev fToRTL : ℕ := 454
abbrev fProf : ℕ := 455
abbrev fProfL : ℕ := 456
abbrev fChar : ℕ := 457

/-! ## the terms -/

/-- `xs.getD i d` -/
def nthDTm : Tm :=
  .ite (.isNat (V 0)) (V 2)
    (.ite (.eq (V 1) (.lit 0)) (.fst (V 0)) (.call fNthD [.snd (V 0), .sub (V 1) (.lit 1), V 2]))

/-- `ns.map (·.bag.card)` -/
def cardsTm : Tm :=
  .ite (.isNat (V 0)) (V 0)
    (.cons (.call fLength [.fst (.fst (V 0))]) (.call fCards [.snd (V 0)]))

/-- `AR.char` -/
def charARTm : Tm :=
  .cons (.fst (V 0))
    (.cons (.call E1A.fTypical [.call fCards [.fst (.snd (V 0))]]) (.call fCharARL [.snd (.snd (V 0))]))

def charARLTm : Tm :=
  .ite (.isNat (V 0)) (V 0) (.cons (.call fCharAR [.fst (V 0)]) (.call fCharARL [.snd (V 0)]))

/-- `AR.chainToRT ns ks` -/
def chainToRTTm : Tm :=
  .ite (.isNat (V 0)) (.cons (.lit 0) (V 1))
    (.ite (.isNat (.snd (V 0)))
      (.cons (.fst (.fst (V 0))) (.call fAppend [.snd (.fst (V 0)), V 1]))
      (.cons (.fst (.fst (V 0)))
        (.call fAppend [.snd (.fst (V 0)), .cons (.call fChainToRT [.snd (V 0), V 1]) (.lit 0)])))

def toRTTm : Tm := .call fChainToRT [.fst (.snd (V 0)), .call fToRTL [.snd (.snd (V 0))]]

def toRTLTm : Tm :=
  .ite (.isNat (V 0)) (V 0) (.cons (.call fToRT [.fst (V 0)]) (.call fToRTL [.snd (V 0)]))

/-- `RT.prof B t` -/
def profTm : Tm :=
  .cons (.call Lib3.fInterS [.fst (V 1), V 0])
    (.cons (.cons (.call fLength [.fst (V 1)]) (.lit 0)) (.call fProfL [V 0, .snd (V 1)]))

def profLTm : Tm :=
  .ite (.isNat (V 1)) (V 1) (.cons (.call fProf [V 0, .fst (V 1)]) (.call fProfL [V 0, .snd (V 1)]))

/-- `RT.char B t = norm (prof B t)` -/
def charTm : Tm := .call idNorm [.call fProf [V 0, V 1]]

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 448 => some nthDTm | 449 => some cardsTm | 450 => some charARTm | 451 => some charARLTm
  | 452 => some chainToRTTm | 453 => some toRTTm | 454 => some toRTLTm | 455 => some profTm
  | 456 => some profLTm | 457 => some charTm | _ => none

def Δ : ℕ → Option Tm := layerΔ E1.e1Δ 448 tbl

abbrev size : ℕ := 458

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 458 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h448 : 448 ≤ f := by omega
    simp only [h448, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem extE1 : E1.e1Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := e1Δ_lt h; omega)

theorem Δ_nthD : Δ fNthD = some nthDTm := by simp [Δ, layerΔ_ge tbl (show 448 ≤ fNthD by decide)]; rfl
theorem Δ_cards : Δ fCards = some cardsTm := by simp [Δ, layerΔ_ge tbl (show 448 ≤ fCards by decide)]; rfl
theorem Δ_charAR : Δ fCharAR = some charARTm := by simp [Δ, layerΔ_ge tbl (show 448 ≤ fCharAR by decide)]; rfl
theorem Δ_charARL : Δ fCharARL = some charARLTm := by simp [Δ, layerΔ_ge tbl (show 448 ≤ fCharARL by decide)]; rfl
theorem Δ_chainToRT : Δ fChainToRT = some chainToRTTm := by
  simp [Δ, layerΔ_ge tbl (show 448 ≤ fChainToRT by decide)]; rfl
theorem Δ_toRT : Δ fToRT = some toRTTm := by simp [Δ, layerΔ_ge tbl (show 448 ≤ fToRT by decide)]; rfl
theorem Δ_toRTL : Δ fToRTL = some toRTLTm := by simp [Δ, layerΔ_ge tbl (show 448 ≤ fToRTL by decide)]; rfl
theorem Δ_prof : Δ fProf = some profTm := by simp [Δ, layerΔ_ge tbl (show 448 ≤ fProf by decide)]; rfl
theorem Δ_profL : Δ fProfL = some profLTm := by simp [Δ, layerΔ_ge tbl (show 448 ≤ fProfL by decide)]; rfl
theorem Δ_char : Δ fChar = some charTm := by simp [Δ, layerΔ_ge tbl (show 448 ≤ fChar by decide)]; rfl

/-! ## counting runs of an analysis -/

mutual
/-- number of runs -/
def cnt : AR → ℕ
  | .run _ _ ks => 1 + cntL ks
def cntL : List AR → ℕ
  | [] => 0
  | k :: ks => cnt k + cntL ks
end

theorem cnt_pos : ∀ r : AR, 1 ≤ cnt r
  | .run _ _ ks => by simp only [cnt]; omega

theorem length_le_cntL : ∀ ks : List AR, ks.length ≤ cntL ks
  | [] => by simp [cntL]
  | k :: ks => by
    have := length_le_cntL ks; have := cnt_pos k
    simp only [cntL, List.length_cons]; omega

theorem cnt_le_sz : ∀ r : AR, cnt r ≤ sz r := by
  have hL : ∀ ks : List AR, (∀ k ∈ ks, cnt k ≤ sz k) → cntL ks ≤ sz ks := by
    intro ks
    induction ks with
    | nil => intro _; simp [cntL]
    | cons k ks ih =>
      intro h
      have := h k (by simp)
      have := ih (fun k hk => h k (by simp [hk]))
      rw [sz_cons]; simp only [cntL]; omega
  intro r
  induction r using AR.ind with
  | h S c ks ih =>
    have := hL ks ih
    rw [sz_ar]; simp only [cnt]
    have := sz_pos S; have := sz_pos c
    omega

theorem sz_S_lt (S : Finset ℕ) (c : List CNode) (ks : List AR) : sz S < sz (AR.run S c ks) := by
  rw [sz_ar]; have := sz_pos c; have := sz_pos ks; omega
theorem sz_c_lt (S : Finset ℕ) (c : List CNode) (ks : List AR) : sz c < sz (AR.run S c ks) := by
  rw [sz_ar]; have := sz_pos S; have := sz_pos ks; omega
theorem sz_ks_lt (S : Finset ℕ) (c : List CNode) (ks : List AR) : sz ks < sz (AR.run S c ks) := by
  rw [sz_ar]; have := sz_pos S; have := sz_pos c; omega

/-- the number of nodes of a chain is at most its cell count (`2 |ns| + 1 ≤ sz ns`). -/
theorem sz_chain_ge : ∀ ns : List CNode, 4 * ns.length + 1 ≤ sz ns
  | [] => by simp
  | n :: ns => by
    have := sz_chain_ge ns
    obtain ⟨b, j⟩ := n
    rw [sz_cons, sz_cnode]
    have := sz_pos b; have := sz_pos j
    simp only [List.length_cons]; omega


theorem sz_rt_X_lt (X : Finset ℕ) (ks : List RT) : sz X < sz (RT.node X ks) := by
  rw [sz_rt_node]; have := sz_pos ks; omega
theorem sz_rt_ks_lt (X : Finset ℕ) (ks : List RT) : sz ks < sz (RT.node X ks) := by
  rw [sz_rt_node]; have := sz_pos X; omega

mutual
theorem sz_charAR_le_rec : ∀ r : AR, sz r.char ≤ sz r
  | .run S c ks => by
    have h1 := sz_charARL_le_rec ks
    have h2 := sz_chain_ge c
    have h3 := typical_length_le (c.map (fun n => n.bag.card))
    rw [List.length_map] at h3
    rw [sz_ar]
    simp only [AR.char, sz_ct_node, sz_list_nat, List.length_map]
    omega
theorem sz_charARL_le_rec : ∀ ks : List AR, sz (AR.charL ks) ≤ sz ks
  | [] => by simp [AR.charL]
  | k :: ks => by
    have h1 := sz_charAR_le_rec k
    have h2 := sz_charARL_le_rec ks
    simp only [AR.charL, sz_cons]; omega
end

theorem sz_charAR_le_pair : (type_of% @sz_charAR_le_rec) ∧ (type_of% @sz_charARL_le_rec) :=
  ⟨@sz_charAR_le_rec, @sz_charARL_le_rec⟩

theorem sz_charAR_le : type_of% @sz_charAR_le_rec := sz_charAR_le_pair.1

mutual
theorem sz_prof_le_rec (Bd : Finset ℕ) : ∀ t : RT, sz (t.prof Bd) ≤ sz t + 4 * t.size
  | .node X ks => by
    have h1 := sz_profL_le_rec Bd ks
    have h2 := sz_inter_le X Bd
    simp only [RT.prof, sz_ct_node, sz_rt_node, RT.size]
    have : sz [X.card] = 3 := by simp [sz_cons]
    rw [this]
    omega
theorem sz_profL_le_rec (Bd : Finset ℕ) : ∀ ks : List RT, sz (RT.profL Bd ks) ≤ sz ks + 4 * RT.sizeL ks
  | [] => by simp [RT.profL, RT.sizeL]
  | k :: ks => by
    have h1 := sz_prof_le_rec Bd k
    have h2 := sz_profL_le_rec Bd ks
    simp only [RT.profL, sz_cons, RT.sizeL]; omega
end

theorem sz_prof_le_pair : (type_of% @sz_prof_le_rec) ∧ (type_of% @sz_profL_le_rec) :=
  ⟨@sz_prof_le_rec, @sz_profL_le_rec⟩

theorem sz_prof_le : type_of% @sz_prof_le_rec := sz_prof_le_pair.1

theorem sz_prof_le5 (Bd : Finset ℕ) (t : RT) : sz (t.prof Bd) ≤ 5 * sz t := by
  have := sz_prof_le Bd t; have := size_le_sz t; omega

/-! ## the lemmas -/

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem nthD_runs {α : Type} [ToVal α] (hB : 1 < B) (xs : List α) (i : ℕ) (d : α) :
    Runs Δ' B fNthD [toVal xs, toVal i, toVal d] (toVal (xs.getD i d)) (16 * xs.length + 12) := by
  induction xs generalizing i with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_nthD) ?_
    simp only [List.getD_nil]
    ev_start
    · ev_run
    · simp
  | cons x xs ih =>
    refine Runs.mk (hΔ _ _ Δ_nthD) ?_
    cases i with
    | zero =>
      simp only [List.getD_cons_zero]
      ev_start
      · ev_run
      · simp only [List.length_cons]; omega
    | succ i =>
      have h1 := ih i
      simp only [List.getD_cons_succ]
      ev_start
      · ev_run
      · simp only [List.length_cons]; omega

theorem cards_runs (ns : List CNode) (hB : 8 * sz ns + 20 < B) :
    Runs Δ' B fCards [toVal ns] (toVal (ns.map (fun n => n.bag.card))) (20 * sz ns + 8) := by
  induction ns with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_cards) ?_
    simp only [List.map_nil]
    ev_start
    · ev_run
    · simp
  | cons n ns ih =>
    obtain ⟨b, j⟩ := n
    have hs : sz (CNode.mk b j :: ns) = sz b + sz j + 1 + sz ns + 1 := by rw [sz_cons, sz_cnode]
    have hb := card_le_sz b
    have h1 := Lib4.card_runs (l4 (Ext.trans extE1 hΔ)) B b (by omega)
    have h2 := ih (by omega)
    refine Runs.mk (hΔ _ _ Δ_cards) ?_
    simp only [List.map_cons]
    ev_start
    · ev_run
    · have := sz_pos j; rw [hs]; omega

mutual
theorem charAR_runs_rec (s : ℕ) (hB : 100 * (s + 1) < B) : ∀ r : AR, sz r ≤ s →
    Runs Δ' B fCharAR [toVal r] (toVal r.char) (400 * (s + 1) ^ 3 * cnt r)
  | .run S c ks, hs => by
    have hcs : sz c ≤ s := by have := sz_c_lt S c ks; omega
    have hks : sz ks ≤ s := by have := sz_ks_lt S c ks; omega
    have h1 := cards_runs hΔ B c (by omega)
    have h2 := E1A.typical_runs (eA (Ext.trans extE1 hΔ)) B (by omega) (c.map (fun n => n.bag.card))
    have h3 := charARL_runs_rec s hB ks hks
    have hlen : (c.map (fun n => n.bag.card)).length ≤ s := by
      have := sz_chain_ge c; rw [List.length_map]; omega
    have h4 : ((c.map (fun n => n.bag.card)).length + 1) ^ 3 ≤ (s + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h5 : ks.length ≤ s := by have := length_le_sz ks; omega
    have h6 : s + 1 ≤ (s + 1) ^ 3 := le_pw (by omega) (by omega)
    refine Runs.mk (hΔ _ _ Δ_charAR) ?_
    simp only [AR.char, toVal_ct, toVal_ar, cnt]
    ev_start
    · ev_run
    · generalize (s + 1) ^ 3 = T at *
      have e : 400 * T * (1 + cntL ks) = 400 * T + 400 * T * cntL ks := by ring
      rw [e]
      nlinarith
theorem charARL_runs_rec (s : ℕ) (hB : 100 * (s + 1) < B) : ∀ ks : List AR, sz ks ≤ s →
    Runs Δ' B fCharARL [toVal ks] (toVal (AR.charL ks)) (400 * (s + 1) ^ 3 * cntL ks + 20 * ks.length + 8)
  | [], hs => by
    refine Runs.mk (hΔ _ _ Δ_charARL) ?_
    simp only [AR.charL, cntL]
    ev_start
    · ev_run
    · simp
  | k :: ks, hs => by
    have hk : sz k ≤ s := by have := sz_head_lt k ks; omega
    have hks : sz ks ≤ s := by have := sz_tail_lt k ks; omega
    have h1 := charAR_runs_rec s hB k hk
    have h2 := charARL_runs_rec s hB ks hks
    have h3 := cnt_pos k
    have h6 : s + 1 ≤ (s + 1) ^ 3 := le_pw (by omega) (by omega)
    refine Runs.mk (hΔ _ _ Δ_charARL) ?_
    simp only [AR.charL, cntL, toVal_cons, List.length_cons]
    ev_start
    · ev_run
    · generalize (s + 1) ^ 3 = T at *
      have e : 400 * T * (cnt k + cntL ks) = 400 * T * cnt k + 400 * T * cntL ks := by ring
      rw [e]
      nlinarith
end

end proofs

theorem charAR_runs_pair : (type_of% @charAR_runs_rec) ∧ (type_of% @charARL_runs_rec) :=
  ⟨@charAR_runs_rec, @charARL_runs_rec⟩

theorem charAR_runs : type_of% @charAR_runs_rec := charAR_runs_pair.1

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem chainToRT_runs : ∀ (ns : List CNode) (ks : List RT), 1 < B →
    Runs Δ' B fChainToRT [toVal ns, toVal ks] (toVal (AR.chainToRT ns ks)) (40 * sz ns + 20)
  | [], ks, hB => by
    refine Runs.mk (hΔ _ _ Δ_chainToRT) ?_
    simp only [AR.chainToRT, toVal_rt, toVal_empty_finset]
    ev_start
    · ev_run
    · simp
  | [n], ks, hB => by
    obtain ⟨b, j⟩ := n
    have h1 := Lib1.append_runs (l1 (Ext.trans extE1 hΔ)) B j ks
    refine Runs.mk (hΔ _ _ Δ_chainToRT) ?_
    simp only [AR.chainToRT, toVal_rt, toVal_cnode]
    ev_start
    · ev_run
    · have := sz_pos b; have := length_le_sz j
      simp only [sz_cons, sz_cnode]
      have : sz ([] : List CNode) = 1 := rfl
      omega
  | n :: m :: r, ks, hB => by
    obtain ⟨b, j⟩ := n
    have h1 := Lib1.append_runs (l1 (Ext.trans extE1 hΔ)) B j [AR.chainToRT (m :: r) ks]
    have h2 := chainToRT_runs (m :: r) ks hB
    refine Runs.mk (hΔ _ _ Δ_chainToRT) ?_
    simp only [AR.chainToRT, toVal_rt, toVal_cnode]
    ev_start
    · ev_run
    · have := sz_pos b; have := length_le_sz j
      have h3 : sz (CNode.mk b j :: m :: r) = sz b + sz j + 1 + sz (m :: r) + 1 := by
        rw [sz_cons, sz_cnode]
      omega

mutual
theorem toRT_runs_rec (s : ℕ) (hB : 100 * (s + 1) < B) : ∀ r : AR, sz r ≤ s →
    Runs Δ' B fToRT [toVal r] (toVal (AR.toRT r)) (100 * (s + 1) * cnt r)
  | .run S c ks, hs => by
    have hcs : sz c ≤ s := by have := sz_c_lt S c ks; omega
    have hks : sz ks ≤ s := by have := sz_ks_lt S c ks; omega
    have h1 := chainToRT_runs hΔ B c (AR.toRTL ks) (by omega)
    have h2 := toRTL_runs_rec s hB ks hks
    have h5 : ks.length ≤ s := by have := length_le_sz ks; omega
    refine Runs.mk (hΔ _ _ Δ_toRT) ?_
    simp only [AR.toRT, toVal_ar, cnt]
    ev_start
    · ev_run
    · generalize hT : s + 1 = T at *
      have e : 100 * T * (1 + cntL ks) = 100 * T + 100 * T * cntL ks := by ring
      rw [e]
      nlinarith
theorem toRTL_runs_rec (s : ℕ) (hB : 100 * (s + 1) < B) : ∀ ks : List AR, sz ks ≤ s →
    Runs Δ' B fToRTL [toVal ks] (toVal (AR.toRTL ks)) (100 * (s + 1) * cntL ks + 20 * ks.length + 8)
  | [], hs => by
    refine Runs.mk (hΔ _ _ Δ_toRTL) ?_
    simp only [AR.toRTL, cntL]
    ev_start
    · ev_run
    · simp
  | k :: ks, hs => by
    have hk : sz k ≤ s := by have := sz_head_lt k ks; omega
    have hks : sz ks ≤ s := by have := sz_tail_lt k ks; omega
    have h1 := toRT_runs_rec s hB k hk
    have h2 := toRTL_runs_rec s hB ks hks
    have h3 := cnt_pos k
    refine Runs.mk (hΔ _ _ Δ_toRTL) ?_
    simp only [AR.toRTL, cntL, toVal_cons, List.length_cons]
    ev_start
    · ev_run
    · generalize hT : s + 1 = T at *
      have e : 100 * T * (cnt k + cntL ks) = 100 * T * cnt k + 100 * T * cntL ks := by ring
      rw [e]
      nlinarith
end

end proofs

theorem toRT_runs_pair : (type_of% @toRT_runs_rec) ∧ (type_of% @toRTL_runs_rec) :=
  ⟨@toRT_runs_rec, @toRTL_runs_rec⟩

theorem toRT_runs : type_of% @toRT_runs_rec := toRT_runs_pair.1

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

mutual
theorem prof_runs_rec (Bd : Finset ℕ) (s : ℕ) (hB : 100 * (s + 1) < B) (hBd : sz Bd ≤ s) : ∀ t : RT, sz t ≤ s →
    Runs Δ' B fProf [toVal Bd, toVal t] (toVal (t.prof Bd)) (200 * (s + 1) * t.size)
  | .node X ks, hs => by
    have hX : sz X ≤ s := by have := sz_rt_X_lt X ks; omega
    have hks : sz ks ≤ s := by have := sz_rt_ks_lt X ks; omega
    have h1 := Lib3.inter_runs (l3 (Ext.trans extE1 hΔ)) B X Bd
    have hc := card_le_sz X
    have h2 := Lib4.card_runs (l4 (Ext.trans extE1 hΔ)) B X (by omega)
    have h3 := profL_runs_rec Bd s hB hBd ks hks
    have h5 : ks.length ≤ s := by have := length_le_sz ks; omega
    have hc1 := card_le_sz Bd
    refine Runs.mk (hΔ _ _ Δ_prof) ?_
    simp only [RT.prof, toVal_ct, toVal_rt, RT.size]
    ev_start
    · ev_run
    · rw [sz_finset] at hX hBd
      generalize hT : s + 1 = T at *
      have e : 200 * T * (1 + RT.sizeL ks) = 200 * T + 200 * T * RT.sizeL ks := by ring
      rw [e]
      nlinarith
theorem profL_runs_rec (Bd : Finset ℕ) (s : ℕ) (hB : 100 * (s + 1) < B) (hBd : sz Bd ≤ s) : ∀ ks : List RT, sz ks ≤ s →
    Runs Δ' B fProfL [toVal Bd, toVal ks] (toVal (RT.profL Bd ks))
      (200 * (s + 1) * RT.sizeL ks + 20 * ks.length + 8)
  | [], hs => by
    refine Runs.mk (hΔ _ _ Δ_profL) ?_
    simp only [RT.profL, RT.sizeL]
    ev_start
    · ev_run
    · simp
  | k :: ks, hs => by
    have hk : sz k ≤ s := by have := sz_head_lt k ks; omega
    have hks : sz ks ≤ s := by have := sz_tail_lt k ks; omega
    have h1 := prof_runs_rec Bd s hB hBd k hk
    have h2 := profL_runs_rec Bd s hB hBd ks hks
    have h3 : 1 ≤ k.size := by cases k; simp [RT.size]
    refine Runs.mk (hΔ _ _ Δ_profL) ?_
    simp only [RT.profL, RT.sizeL, toVal_cons, List.length_cons]
    ev_start
    · ev_run
    · generalize hT : s + 1 = T at *
      have e : 200 * T * (k.size + RT.sizeL ks) = 200 * T * k.size + 200 * T * RT.sizeL ks := by ring
      rw [e]
      nlinarith
end

end proofs

theorem prof_runs_pair : (type_of% @prof_runs_rec) ∧ (type_of% @profL_runs_rec) :=
  ⟨@prof_runs_rec, @profL_runs_rec⟩

theorem prof_runs : type_of% @prof_runs_rec := prof_runs_pair.1

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem char_runs (E : Ext5 Δ') (Bd : Finset ℕ) (t : RT) (s : ℕ) (hst : sz t ≤ s) (hBd : sz Bd ≤ s)
    (hB : 100 * (s + 1) + E.cNorm (5 * s) < B) :
    Runs Δ' B fChar [toVal Bd, toVal t] (toVal (t.char Bd)) (200 * (s + 1) * t.size + E.cNorm (5 * s) + 8) := by
  have h1 := prof_runs hΔ B Bd s (by omega) hBd t hst
  have h2 := E.norm B (5 * s) (t.prof Bd) (le_trans (sz_prof_le5 Bd t) (by omega)) (by omega)
  refine Runs.mk (hΔ _ _ Δ_char) ?_
  simp only [RT.char]
  ev_start
  · ev_run
  · omega

end proofs
end E5A
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E5B` -/

section
/-!
# WP E5 (layer B): `sortAR`, `analyzeNode`, `analyze`

Ids `460 …`:

| id | function | arguments |
|---|---|---|
| 460 `fKeyLeAR` | `decide (key S a.char ≤ key S b.char)` (comparison of `sortAR`) | `[S, a, b]` |
| 461 `fSortAR` | `sortAR` | `[S, ks]` |
| 462 `fPruned` | the predicate `p.2.isLeaf && decide (p.2.S ⊆ S)` | `[S, p]` |
| 463 `fNotPruned` | its negation | `[S, p]` |
| 464 `fFstP` / 465 `fSndP` | `p.1` / `p.2` (`map` callees) | `[_, p]` |
| 466 `fAnalyzeNode` | `analyzeNode` | `[Bd, X, kids]` |
| 467 `fAnalyze` | `analyze` | `[Bd, t]` |
| 468 `fAnalyzeL` | `analyzeL` | `[Bd, ks]` |

The recursion of `analyze` is charged per node: `Runs … fAnalyze … (cA E s · t.size)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E5B

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5 E5A

abbrev fKeyLeAR : ℕ := 460
abbrev fSortAR : ℕ := 461
abbrev fPruned : ℕ := 462
abbrev fNotPruned : ℕ := 463
abbrev fFstP : ℕ := 464
abbrev fSndP : ℕ := 465
abbrev fAnalyzeNode : ℕ := 466
abbrev fAnalyze : ℕ := 467
abbrev fAnalyzeL : ℕ := 468

/-- the pruning predicate of `analyzeNode` -/
abbrev prunedP (S : Finset ℕ) : RT × AR → Bool := fun p => p.2.isLeaf && decide (p.2.S ⊆ S)

def keyLeARTm : Tm := .call idKeyLe [V 0, .call fCharAR [V 1], .call fCharAR [V 2]]

def sortARTm : Tm := .call Lib2.fISort [.lit fKeyLeAR, V 0, V 1]

def prunedTm : Tm :=
  .mul (.isNat (.snd (.snd (.snd (V 1))))) (.call Lib3.fSubsetS [.fst (.snd (V 1)), V 0])

def notPrunedTm : Tm := .sub (.lit 1) (.call fPruned [V 0, V 1])

def fstPTm : Tm := .fst (V 1)
def sndPTm : Tm := .snd (V 1)

/-- environment after the three `let`s: `[core, junk, S, Bd, X, kids]` -/
def analyzeNodeTm : Tm :=
  .letE (.call Lib3.fInterS [V 1, V 0])
    (.letE (.call fMap [.lit fFstP, .lit 0, .call fFilter [.lit fPruned, V 0, V 3]])
      (.letE (.call fMap [.lit fSndP, .lit 0, .call fFilter [.lit fNotPruned, V 1, V 4]])
        (.ite (.isNat (V 0))
          (.cons (V 2) (.cons (.cons (.cons (V 4) (V 1)) (.lit 0)) (.lit 0)))
          (.ite (.isNat (.snd (V 0)))
            (.ite (.call fEqV [.fst (.fst (V 0)), V 2])
              (.cons (V 2) (.cons (.cons (.cons (V 4) (V 1)) (.fst (.snd (.fst (V 0)))))
                (.snd (.snd (.fst (V 0))))))
              (.cons (V 2) (.cons (.cons (.cons (V 4) (V 1)) (.lit 0)) (.cons (.fst (V 0)) (.lit 0)))))
            (.cons (V 2) (.cons (.cons (.cons (V 4) (V 1)) (.lit 0)) (.call fSortAR [V 2, V 0])))))))

def analyzeTm : Tm :=
  .call fAnalyzeNode [V 0, .fst (V 1), .call fAnalyzeL [V 0, .snd (V 1)]]

def analyzeLTm : Tm :=
  .ite (.isNat (V 1)) (V 1)
    (.cons (.cons (.fst (V 1)) (.call fAnalyze [V 0, .fst (V 1)])) (.call fAnalyzeL [V 0, .snd (V 1)]))

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 460 => some keyLeARTm | 461 => some sortARTm | 462 => some prunedTm | 463 => some notPrunedTm
  | 464 => some fstPTm | 465 => some sndPTm | 466 => some analyzeNodeTm | 467 => some analyzeTm
  | 468 => some analyzeLTm | _ => none

def Δ : ℕ → Option Tm := layerΔ E5A.Δ 460 tbl

abbrev size : ℕ := 469

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 469 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h460 : 460 ≤ f := by omega
    simp only [h460, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem extA : E5A.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E5A.Δ_lt h; simp [E5A.size] at this; omega)
theorem extE1 : E1.e1Δ ⊑ Δ := Ext.trans E5A.extE1 extA

theorem Δ_keyLeAR : Δ fKeyLeAR = some keyLeARTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fKeyLeAR by decide)]; rfl
theorem Δ_sortAR : Δ fSortAR = some sortARTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fSortAR by decide)]; rfl
theorem Δ_pruned : Δ fPruned = some prunedTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fPruned by decide)]; rfl
theorem Δ_notPruned : Δ fNotPruned = some notPrunedTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fNotPruned by decide)]; rfl
theorem Δ_fstP : Δ fFstP = some fstPTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fFstP by decide)]; rfl
theorem Δ_sndP : Δ fSndP = some sndPTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fSndP by decide)]; rfl
theorem Δ_analyzeNode : Δ fAnalyzeNode = some analyzeNodeTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fAnalyzeNode by decide)]; rfl
theorem Δ_analyze : Δ fAnalyze = some analyzeTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fAnalyze by decide)]; rfl
theorem Δ_analyzeL : Δ fAnalyzeL = some analyzeLTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fAnalyzeL by decide)]; rfl

/-! ## sizes -/

theorem sz_mkNode_le (S X : Finset ℕ) (junk : List RT) (core : List AR) :
    sz (mkNode S X junk core) ≤ sz S + sz X + sz junk + sz core + 7 := by
  rcases core with _ | ⟨k, _ | ⟨k2, t⟩⟩
  · simp only [mkNode, sz_ar, sz_cons, sz_cnode]
    have : sz ([] : List CNode) = 1 := rfl
    have : sz ([] : List AR) = 1 := rfl
    omega
  · obtain ⟨Sk, ck, kk⟩ := k
    simp only [mkNode, AR.S, AR.chain, AR.kids]
    by_cases h : Sk = S
    · subst h
      simp only [if_true, sz_ar, sz_cons, sz_cnode]
      have : sz ([] : List AR) = 1 := rfl
      omega
    · simp only [h, if_false, sz_ar, sz_cons, sz_cnode]
      have : sz ([] : List AR) = 1 := rfl
      have : sz ([] : List CNode) = 1 := rfl
      omega
  · have hp := sz_perm' (List.mergeSort_perm (k :: k2 :: t) (fun a b => decide (CT.key S a.char ≤ CT.key S b.char)))
    simp only [mkNode, sortAR, sz_ar, sz_cons, sz_cnode] at hp ⊢
    have : sz ([] : List CNode) = 1 := rfl
    omega

theorem sz_junk_core (l : List (RT × AR)) (pr : RT × AR → Bool) (h : ∀ p ∈ l, sz p.2 ≤ 5 * sz p.1) :
    sz ((l.filter pr).map Prod.fst) + sz ((l.filter (fun p => !pr p)).map Prod.snd) ≤
      2 + 5 * (l.map (fun p => sz p.1 + 1)).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hp := h p (List.mem_cons_self ..)
    by_cases hpr : pr p = true
    · simp only [List.filter_cons, hpr, Bool.not_true, Bool.false_eq_true, if_true, if_false, List.map_cons,
        List.sum_cons, sz_cons]
      omega
    · simp only [Bool.not_eq_true] at hpr
      simp only [List.filter_cons, hpr, Bool.not_false, Bool.false_eq_true, if_true, if_false, List.map_cons,
        List.sum_cons, sz_cons]
      omega

theorem sz_analyze_le (Bd : Finset ℕ) (t : RT) : sz (analyze Bd t) ≤ 5 * sz t := by
  induction t using RT.ind with
  | h X ks ih =>
    rw [analyze_node, analyzeNode_eq]
    have hk : ∀ p ∈ ks.map (fun k => (k, analyze Bd k)), sz p.2 ≤ 5 * sz p.1 := by
      intro p hp
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
      exact ih k hk
    have h1 := sz_junk_core _ (fun p => p.2.isLeaf && decide (p.2.S ⊆ X ∩ Bd)) hk
    have h2 := sz_mkNode_le (X ∩ Bd) X (((ks.map (fun k => (k, analyze Bd k))).filter
        (fun p => p.2.isLeaf && decide (p.2.S ⊆ X ∩ Bd))).map Prod.fst)
      (((ks.map (fun k => (k, analyze Bd k))).filter
        (fun p => !(p.2.isLeaf && decide (p.2.S ⊆ X ∩ Bd)))).map Prod.snd)
    have h3 := sz_inter_le X Bd
    have h4 : (ks.map (fun k => (k, analyze Bd k))).map (fun p => sz p.1 + 1) = ks.map (fun k => sz k + 1) := by
      rw [List.map_map]; rfl
    have h5 : sz ks = 1 + (ks.map (fun k => sz k + 1)).sum := by
      rw [sz_list]
      have : ∀ l : List RT, (l.map sz).sum + l.length = (l.map (fun k => sz k + 1)).sum := by
        intro l; induction l with
        | nil => simp
        | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
      have := this ks
      omega
    rw [h4] at h1
    rw [sz_rt_node]
    omega

theorem sz_analyzeL_le (Bd : Finset ℕ) (ks : List RT) : sz (analyzeL Bd ks) ≤ 6 * sz ks := by
  rw [analyzeL_eq]
  have key : ∀ l : List RT, sz (l.map (fun k => (k, analyze Bd k))) ≤ 6 * sz l := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      have := sz_analyze_le Bd a
      simp only [List.map_cons, sz_cons, sz_pair]
      omega
  exact key ks

/-! ## the comparison and the sort -/

/-- cost of `sortAR` on inputs of size `≤ s`, `ck` the cost of one `keyLe`. -/
def cSort (s ck : ℕ) : ℕ := (800 * (s + 1) ^ 4 + ck + 80) * (s + 1) ^ 2 + 8

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem keyLeAR_runs (E : Ext5 Δ') (S : Finset ℕ) (a b : AR) (s : ℕ) (hS : sz S ≤ s) (ha : sz a ≤ s)
    (hb : sz b ≤ s) (hB : 1000 + 100 * (s + 1) + E.cKey s < B) :
    Runs Δ' B fKeyLeAR [toVal S, toVal a, toVal b] (toVal (decide (CT.key S a.char ≤ CT.key S b.char)))
      (800 * (s + 1) ^ 4 + E.cKey s + 10) := by
  have hΔ' : E5A.Δ ⊑ Δ' := Ext.trans extA hΔ
  have h1 := charAR_runs hΔ' B s (by omega) a ha
  have h2 := charAR_runs hΔ' B s (by omega) b hb
  have h3 := E.keyLe B s S a.char b.char hS (le_trans (sz_charAR_le a) ha) (le_trans (sz_charAR_le b) hb) (by omega)
  have ca := le_trans (cnt_le_sz a) ha
  have cb := le_trans (cnt_le_sz b) hb
  have e1 : 400 * (s + 1) ^ 3 * cnt a ≤ 400 * (s + 1) ^ 4 := by
    calc 400 * (s + 1) ^ 3 * cnt a ≤ 400 * (s + 1) ^ 3 * (s + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = 400 * (s + 1) ^ 4 := by ring
  have e2 : 400 * (s + 1) ^ 3 * cnt b ≤ 400 * (s + 1) ^ 4 := by
    calc 400 * (s + 1) ^ 3 * cnt b ≤ 400 * (s + 1) ^ 3 * (s + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = 400 * (s + 1) ^ 4 := by ring
  refine Runs.mk (hΔ _ _ Δ_keyLeAR) ?_
  ev_start
  · ev_run
  · omega

theorem sortAR_runs (E : Ext5 Δ') (S : Finset ℕ) (ks : List AR) (s : ℕ) (hS : sz S ≤ s) (hks : sz ks ≤ s)
    (hB : 1000 + 100 * (s + 1) + E.cKey s < B) :
    Runs Δ' B fSortAR [toVal S, toVal ks] (toVal (sortAR S ks)) (cSort s (E.cKey s)) := by
  have hΔ2 : Lib2.Δ ⊑ Δ' := l2 (Ext.trans extE1 hΔ)
  have h1 := Lib2.mergeSort_runs hΔ2 B fKeyLeAR (toVal S) (fun a b : AR => decide (CT.key S a.char ≤ CT.key S b.char))
    (800 * (s + 1) ^ 4 + E.cKey s + 10)
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; exact le_trans hab hbc)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) ks
    (fun x hx y hy => keyLeAR_runs hΔ B E S x y s hS (le_trans (sz_le_of_mem hx) hks)
      (le_trans (sz_le_of_mem hy) hks) hB)
  have hlen : ks.length ≤ s := le_trans (length_le_sz ks) hks
  have h2 : (ks.length + 1) ^ 2 ≤ (s + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h3 : 1 ≤ (s + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hk : fKeyLeAR < B := by show 460 < B; omega
  refine Runs.mk (hΔ _ _ Δ_sortAR) ?_
  unfold sortAR
  ev_start
  · ev_run
  · unfold cSort
    have h4 : (800 * (s + 1) ^ 4 + E.cKey s + 10 + 60) * (ks.length + 1) ^ 2 ≤
        (800 * (s + 1) ^ 4 + E.cKey s + 10 + 60) * (s + 1) ^ 2 := Nat.mul_le_mul_left _ h2
    nlinarith

theorem pruned_runs (S : Finset ℕ) (p : RT × AR) (s : ℕ) (hS : sz S ≤ s) (hp : sz p ≤ s)
    (hB : 1000 + 100 * (s + 1) < B) :
    Runs Δ' B fPruned [toVal S, toVal p] (toVal (prunedP S p)) (130 * (s + 1)) := by
  obtain ⟨r, ⟨Sa, c, ka⟩⟩ := p
  have hSa : sz Sa ≤ s := by
    have := sz_S_lt Sa c ka; have := sz_pair_le (a := r) (b := AR.run Sa c ka); omega
  have h1 := card_le_sz S
  have h2 := card_le_sz Sa
  have hsub := Lib3.subset_runs (l3 (Ext.trans extE1 hΔ)) B (by omega) Sa S (decide (Sa ⊆ S)) (by simp)
  have hsub' : Runs Δ' B Lib3.fSubsetS [toVal Sa, toVal S] (toVal (decide (Sa ⊆ S))) (120 * s + 20) :=
    hsub.mono (by omega)
  clear hsub
  refine Runs.mk (hΔ _ _ Δ_pruned) ?_
  simp only [toVal_pair, toVal_ar]
  cases ka with
  | nil =>
    by_cases hs : Sa ⊆ S
    · have : prunedP S (r, AR.run Sa c []) = true := by simp [AR.isLeaf, AR.kids, AR.S, hs]
      rw [this]
      simp only [hs, decide_true] at hsub'
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
    · have : prunedP S (r, AR.run Sa c []) = false := by simp [AR.isLeaf, AR.kids, AR.S, hs]
      rw [this]
      simp only [hs, decide_false] at hsub'
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
  | cons k ks =>
    have : prunedP S (r, AR.run Sa c (k :: ks)) = false := by simp [AR.isLeaf, AR.kids]
    rw [this]
    ev_start
    · ev_run
      all_goals (first | omega | (simp; done) | (simp; omega))
    · omega

theorem notPruned_runs (S : Finset ℕ) (p : RT × AR) (s : ℕ) (hS : sz S ≤ s) (hp : sz p ≤ s)
    (hB : 1000 + 100 * (s + 1) < B) :
    Runs Δ' B fNotPruned [toVal S, toVal p] (toVal (!prunedP S p)) (130 * (s + 1) + 6) := by
  have h1 := pruned_runs hΔ B S p s hS hp hB
  have hk : fPruned < B := by show 462 < B; omega
  refine Runs.mk (hΔ _ _ Δ_notPruned) ?_
  cases hq : prunedP S p
  · simp only [hq] at h1
    simp only [Bool.not_false]
    ev_start
    · ev_run
      all_goals (first | omega | (simp; done) | (simp; omega))
    · omega
  · simp only [hq] at h1
    simp only [Bool.not_true]
    ev_start
    · ev_run
      all_goals (first | omega | (simp; done) | (simp; omega))
    · omega

theorem fstP_runs (ctx : Val) (p : RT × AR) : Runs Δ' B fFstP [ctx, toVal p] (toVal p.1) 3 := by
  obtain ⟨r, a⟩ := p
  refine Runs.mk (hΔ _ _ Δ_fstP) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

theorem sndP_runs (ctx : Val) (p : RT × AR) : Runs Δ' B fSndP [ctx, toVal p] (toVal p.2) 3 := by
  obtain ⟨r, a⟩ := p
  refine Runs.mk (hΔ _ _ Δ_sndP) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

/-- local cost of `analyzeNode` -/
def cAN (s ck : ℕ) : ℕ := 1000 * (s + 1) ^ 2 + cSort s ck

theorem analyzeNode_runs (E : Ext5 Δ') (Bd X : Finset ℕ) (kids : List (RT × AR)) (s : ℕ)
    (hBd : sz Bd ≤ s) (hX : sz X ≤ s) (hk : sz kids ≤ s) (hB : 1000 + 100 * (s + 1) + E.cKey s < B) :
    Runs Δ' B fAnalyzeNode [toVal Bd, toVal X, toVal kids] (toVal (analyzeNode Bd X kids)) (cAN s (E.cKey s)) := by
  have hE1 := Ext.trans extE1 hΔ
  have hS := Lib3.inter_runs (l3 hE1) B X Bd
  have hSsz : sz (X ∩ Bd) ≤ s := le_trans (sz_inter_le X Bd) hX
  have hlen : kids.length ≤ s := le_trans (length_le_sz kids) hk
  have hc1 := card_le_sz X
  have hc2 := card_le_sz Bd
  rw [sz_finset] at hX hBd
  have hkp : fPruned < B := by show 462 < B; omega
  have hkn : fNotPruned < B := by show 463 < B; omega
  have hkf : fFstP < B := by show 464 < B; omega
  have hks : fSndP < B := by show 465 < B; omega
  have hf1 := Lib1.filter_runs (l1 hE1) B fPruned (toVal (X ∩ Bd)) (prunedP (X ∩ Bd)) (fun _ => 130 * (s + 1)) kids
    (fun p hp => pruned_runs hΔ B _ p s hSsz (le_trans (sz_le_of_mem hp) hk) (by omega))
  have hf2 := Lib1.filter_runs (l1 hE1) B fNotPruned (toVal (X ∩ Bd)) (fun p => !prunedP (X ∩ Bd) p)
    (fun _ => 130 * (s + 1) + 6) kids
    (fun p hp => notPruned_runs hΔ B _ p s hSsz (le_trans (sz_le_of_mem hp) hk) (by omega))
  simp only [E5.sum_map_const] at hf1 hf2
  have hl1 : (kids.filter (prunedP (X ∩ Bd))).length ≤ kids.length := List.length_filter_le _ _
  have hl2 : (kids.filter (fun p => !prunedP (X ∩ Bd) p)).length ≤ kids.length := List.length_filter_le _ _
  have hm1 := Lib1.map_runs (l1 hE1) B fFstP (Val.nat 0) Prod.fst (fun _ => 3) (kids.filter (prunedP (X ∩ Bd)))
    (fun p _ => fstP_runs hΔ B _ p)
  have hm2 := Lib1.map_runs (l1 hE1) B fSndP (Val.nat 0) Prod.snd (fun _ => 3)
    (kids.filter (fun p => !prunedP (X ∩ Bd) p)) (fun p _ => sndP_runs hΔ B _ p)
  simp only [E5.sum_map_const] at hm1 hm2
  have hjsz : sz ((kids.filter (prunedP (X ∩ Bd))).map Prod.fst) ≤ s :=
    le_trans (sz_map_le' _ _ (fun p _ => (sz_pair_le (a := p.1) (b := p.2)).1))
      (le_trans (sz_filter_le' _ _) hk) |>.trans (le_refl _)
  have hcsz : sz ((kids.filter (fun p => !prunedP (X ∩ Bd) p)).map Prod.snd) ≤ s :=
    le_trans (sz_map_le' _ _ (fun p _ => (sz_pair_le (a := p.1) (b := p.2)).2))
      (le_trans (sz_filter_le' _ _) hk) |>.trans (le_refl _)
  rw [analyzeNode_eq]
  generalize (kids.filter (prunedP (X ∩ Bd))).map Prod.fst = junk at hm1 hjsz ⊢
  generalize (kids.filter (fun p => !prunedP (X ∩ Bd) p)).map Prod.snd = core at hm2 hcsz ⊢
  have hP1 : kids.length * (130 * (s + 1)) ≤ 130 * (s + 1) ^ 2 := by
    calc kids.length * (130 * (s + 1)) ≤ s * (130 * (s + 1)) := Nat.mul_le_mul_right _ hlen
      _ ≤ 130 * (s + 1) ^ 2 := by nlinarith
  have hP2 : kids.length * (130 * (s + 1) + 6) ≤ 136 * (s + 1) ^ 2 := by
    calc kids.length * (130 * (s + 1) + 6) ≤ s * (130 * (s + 1) + 6) := Nat.mul_le_mul_right _ hlen
      _ ≤ 136 * (s + 1) ^ 2 := by nlinarith
  have hs1 : s + 1 ≤ (s + 1) ^ 2 := le_pw (by omega) (by omega)
  have hs2 : 1 ≤ (s + 1) ^ 2 := one_le_pw (by omega) 2
  have hkc : 0 ≤ cSort s (E.cKey s) := Nat.zero_le _
  refine Runs.mk (hΔ _ _ Δ_analyzeNode) ?_
  rcases core with _ | ⟨k, _ | ⟨k2, t⟩⟩
  · simp only [mkNode, toVal_ar, toVal_cons, toVal_nil, toVal_cnode]
    simp only [toVal_nil] at hm2
    ev_start
    · ev_run
    · unfold cAN
      omega
  · obtain ⟨Sk, ck, kk⟩ := k
    simp only [toVal_cons, toVal_nil, toVal_ar] at hm2
    have hSk : sz Sk ≤ s := by
      have := sz_S_lt Sk ck kk
      have : sz (AR.run Sk ck kk) < sz [AR.run Sk ck kk] := by rw [sz_cons]; have := sz_pos ([] : List AR); omega
      omega
    by_cases hSkeq : Sk = X ∩ Bd
    · have heq := Lib1.eqV_runs_typed (l1 hE1) B (by omega) Sk (X ∩ Bd) true (by simp [hSkeq])
      simp only [mkNode, AR.S, AR.chain, AR.kids, hSkeq, if_true, toVal_ar, toVal_cons, toVal_nil, toVal_cnode]
      have hmin : min (sz (X ∩ Bd)) (sz (X ∩ Bd)) ≤ s := le_trans (min_le_left _ _) hSsz
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done))
      · unfold cAN
        have : 30 * min (sz (X ∩ Bd)) (sz (X ∩ Bd)) ≤ 30 * s := by omega
        omega
    · have heq := Lib1.eqV_runs_typed (l1 hE1) B (by omega) Sk (X ∩ Bd) false (by simp [hSkeq])
      simp only [mkNode, AR.S, AR.chain, AR.kids, hSkeq, if_false, toVal_ar, toVal_cons, toVal_nil, toVal_cnode]
      have hmin : min (sz Sk) (sz (X ∩ Bd)) ≤ s := le_trans (min_le_left _ _) hSk
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done))
      · unfold cAN
        have : 30 * min (sz Sk) (sz (X ∩ Bd)) ≤ 30 * s := by omega
        omega
  · have hsort := sortAR_runs hΔ B E (X ∩ Bd) (k :: k2 :: t) s hSsz hcsz hB
    have hksort : fSortAR < B := by show 461 < B; omega
    simp only [toVal_cons, toVal_nil] at hm2
    simp only [mkNode, toVal_ar, toVal_cons, toVal_nil, toVal_cnode]
    simp only [toVal_cons] at hsort
    ev_start
    · ev_run
    · unfold cAN
      omega

/-- constant of the per-node cost of `analyze` (`ck6 = E.cKey (6 s)`) -/
def cA (s ck6 : ℕ) : ℕ := cAN (6 * s) ck6 + 20 * s + 100

mutual
theorem analyze_runs_rec (E : Ext5 Δ') (Bd : Finset ℕ) (s : ℕ) (hBd : sz Bd ≤ s)
    (hB : 1000 + 100 * (6 * s + 1) + E.cKey (6 * s) < B) : ∀ t : RT, sz t ≤ s →
    Runs Δ' B fAnalyze [toVal Bd, toVal t] (toVal (analyze Bd t)) (cA s (E.cKey (6 * s)) * t.size)
  | .node X ks, hs => by
    have hX : sz X ≤ s := by have := sz_rt_X_lt X ks; omega
    have hks : sz ks ≤ s := by have := sz_rt_ks_lt X ks; omega
    have hlen : ks.length ≤ s := le_trans (length_le_sz ks) hks
    have h1 := analyzeNode_runs hΔ B E Bd X (analyzeL Bd ks) (6 * s) (by omega) (by omega)
      (le_trans (sz_analyzeL_le Bd ks) (by omega)) (by omega)
    have h2 := analyzeL_runs_rec E Bd s hBd hB ks hks
    have hka : fAnalyzeL < B := by show 468 < B; omega
    have hkb : fAnalyzeNode < B := by show 466 < B; omega
    refine Runs.mk (hΔ _ _ Δ_analyze) ?_
    simp only [analyze, toVal_rt, RT.size]
    ev_start
    · ev_run
    · have e : cA s (E.cKey (6 * s)) * (1 + RT.sizeL ks) =
          cA s (E.cKey (6 * s)) + cA s (E.cKey (6 * s)) * RT.sizeL ks := by ring
      rw [e]
      unfold cA
      omega
theorem analyzeL_runs_rec (E : Ext5 Δ') (Bd : Finset ℕ) (s : ℕ) (hBd : sz Bd ≤ s)
    (hB : 1000 + 100 * (6 * s + 1) + E.cKey (6 * s) < B) : ∀ ks : List RT, sz ks ≤ s →
    Runs Δ' B fAnalyzeL [toVal Bd, toVal ks] (toVal (analyzeL Bd ks))
      (cA s (E.cKey (6 * s)) * RT.sizeL ks + 20 * ks.length + 8)
  | [], hs => by
    refine Runs.mk (hΔ _ _ Δ_analyzeL) ?_
    simp only [analyzeL, RT.sizeL]
    ev_start
    · ev_run
    · simp
  | k :: ks, hs => by
    have hk : sz k ≤ s := by have := sz_head_lt k ks; omega
    have hks : sz ks ≤ s := by have := sz_tail_lt k ks; omega
    have h1 := analyze_runs_rec E Bd s hBd hB k hk
    have h2 := analyzeL_runs_rec E Bd s hBd hB ks hks
    have hka : fAnalyze < B := by show 467 < B; omega
    have hkb : fAnalyzeL < B := by show 468 < B; omega
    refine Runs.mk (hΔ _ _ Δ_analyzeL) ?_
    simp only [analyzeL, RT.sizeL, toVal_cons, toVal_pair, List.length_cons]
    ev_start
    · ev_run
    · have e : cA s (E.cKey (6 * s)) * (k.size + RT.sizeL ks) =
          cA s (E.cKey (6 * s)) * k.size + cA s (E.cKey (6 * s)) * RT.sizeL ks := by ring
      rw [e]
      omega
end

end proofs

theorem analyze_runs_pair : (type_of% @analyze_runs_rec) ∧ (type_of% @analyzeL_runs_rec) :=
  ⟨@analyze_runs_rec, @analyzeL_runs_rec⟩

theorem analyze_runs : type_of% @analyze_runs_rec := analyze_runs_pair.1

end E5B
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E5C1` -/

section
/-!
# WP E5 (layer C1): chain surgery — `dupAfter`, `cutAt`, `addV`, `addJunk`, `branchRT`

Ids `470 …`:

| id | function | arguments |
|---|---|---|
| 470 `fDupAfter` | `dupAfter` | `[i, ns]` |
| 471 `fCutAt` | `cutAt` | `[y, w, c, ns]` |
| 472 `fInRng` | `decide (s ≤ i) && e.elim true (fun e => decide (i ≤ e))` | `[s, e, i]` |
| 473 `fAddVAux` | `addV` with a running index (`addVL`) | `[v, s, e, i, ns]` |
| 474 `fAddV` | `addV` | `[v, s, e, ns]` |
| 475 `fAddJunkAux` | `addJunk` with a running index (`addJunkL`) | `[x, br, i, ns]` |
| 476 `fAddJunk` | `addJunk` | `[x, br, ns]` |
| 477 `fBranchRT` | `branchRT` | `[v, chain, M]` |
| 478 `fNxt` | `l.getD (f + 1) 0`, computed by `drop` (no arithmetic on `f`) | `[f, l]` |

The Lean `mapIdx` is replaced by the recursion with a running index (`addVL`, `addJunkL`; `addV_eq`, `addJunk_eq`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E5C1

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5 E5A

abbrev fDupAfter : ℕ := 470
abbrev fCutAt : ℕ := 471
abbrev fInRng : ℕ := 472
abbrev fAddVAux : ℕ := 473
abbrev fAddV : ℕ := 474
abbrev fAddJunkAux : ℕ := 475
abbrev fAddJunk : ℕ := 476
abbrev fBranchRT : ℕ := 477
abbrev fNxt : ℕ := 478

/-- `a ≤ b` as a term (`1 - (b < a)`) -/
abbrev leT (a b : Tm) : Tm := .sub (.lit 1) (.lt b a)

/-! ## the Lean side: `addV`, `addJunk` with a running index -/

/-- the test of `addV` -/
abbrev inRng (s : ℕ) (e : Option ℕ) (i : ℕ) : Bool := decide (s ≤ i) && e.elim true (fun e => decide (i ≤ e))

def addVL (v s : ℕ) (e : Option ℕ) : ℕ → List CNode → List CNode
  | _, [] => []
  | i, n :: ns => (if inRng s e i then (⟨insert v n.bag, n.junk⟩ : CNode) else n) :: addVL v s e (i + 1) ns

def addJunkL (x : ℕ) (br : RT) : ℕ → List CNode → List CNode
  | _, [] => []
  | i, n :: ns => (if i = x then (⟨n.bag, n.junk ++ [br]⟩ : CNode) else n) :: addJunkL x br (i + 1) ns

theorem mapIdx_addVL (v s : ℕ) (e : Option ℕ) : ∀ (ns : List CNode) (i : ℕ),
    ns.mapIdx (fun j n => if inRng s e (i + j) then (⟨insert v n.bag, n.junk⟩ : CNode) else n) = addVL v s e i ns
  | [], i => by simp [addVL]
  | n :: ns, i => by
    rw [List.mapIdx_cons, addVL]
    simp only [Nat.add_zero]
    congr 1
    have := mapIdx_addVL v s e ns (i + 1)
    rw [← this]
    congr 1
    funext j m
    rw [show i + (j + 1) = i + 1 + j by omega]

theorem addV_eq (v s : ℕ) (e : Option ℕ) (ns : List CNode) : addV v s e ns = addVL v s e 0 ns := by
  have := mapIdx_addVL v s e ns 0
  simp only [Nat.zero_add] at this
  exact this

theorem mapIdx_addJunkL (x : ℕ) (br : RT) : ∀ (ns : List CNode) (i : ℕ),
    ns.mapIdx (fun j n => if i + j = x then (⟨n.bag, n.junk ++ [br]⟩ : CNode) else n) = addJunkL x br i ns
  | [], i => by simp [addJunkL]
  | n :: ns, i => by
    rw [List.mapIdx_cons, addJunkL]
    simp only [Nat.add_zero]
    congr 1
    have := mapIdx_addJunkL x br ns (i + 1)
    rw [← this]
    congr 1
    funext j m
    rw [show i + (j + 1) = i + 1 + j by omega]

theorem addJunk_eq (x : ℕ) (br : RT) (ns : List CNode) : addJunk x br ns = addJunkL x br 0 ns := by
  have := mapIdx_addJunkL x br ns 0
  simp only [Nat.zero_add] at this
  exact this

/-! ## the terms -/

def dupAfterTm : Tm :=
  .ite (.lt (V 0) (.call fLength [V 1]))
    (.call fAppend
      [.call fAppend [.call fTake [.add (V 0) (.lit 1), V 1],
        .cons (.cons (.fst (.call fNthD [V 1, V 0, .lit 0])) (.lit 0)) (.lit 0)],
       .call fDrop [.add (V 0) (.lit 1), V 1]])
    (V 1)

/-- `l.getD (f + 1) 0` without computing `f + 1`; `[f, l]` -/
def nxtTm : Tm :=
  .letE (.call fDrop [V 0, V 1])
    (.ite (.isNat (V 0)) (.lit 0) (.ite (.isNat (.snd (V 0))) (.lit 0) (.fst (.snd (V 0)))))

/-- environment `[y, w, c, ns]` -/
def cutAtTm : Tm :=
  .ite (.eq (.fst (V 2)) (.lit 1))
    (.letE (.call fNthD [V 1, .snd (V 2), .lit 0])
      (.cons (.call fDupAfter [V 0, V 4]) (V 0)))
    (.cons (V 3)
      (.ite (.lt (.call fNthD [V 0, .snd (V 2), .lit 0]) (.call fNxt [.snd (V 2), V 0]))
        (.call fNthD [V 1, .snd (V 2), .lit 0])
        (.sub (.call fNxt [.snd (V 2), V 1]) (.lit 1))))

/-- `[s, e, i]` -/
def inRngTm : Tm :=
  .mul (leT (V 0) (V 2)) (.ite (.isNat (V 1)) (.lit 1) (leT (V 2) (.snd (V 1))))

/-- `[v, s, e, i, ns]` -/
def addVAuxTm : Tm :=
  .ite (.isNat (V 4)) (V 4)
    (.cons
      (.ite (.call fInRng [V 1, V 2, V 3])
        (.cons (.call Lib3.fInsertS [V 0, .fst (.fst (V 4))]) (.snd (.fst (V 4))))
        (.fst (V 4)))
      (.call fAddVAux [V 0, V 1, V 2, .add (V 3) (.lit 1), .snd (V 4)]))

def addVTm : Tm := .call fAddVAux [V 0, V 1, V 2, .lit 0, V 3]

/-- `[x, br, i, ns]` -/
def addJunkAuxTm : Tm :=
  .ite (.isNat (V 3)) (V 3)
    (.cons
      (.ite (.eq (V 2) (V 0))
        (.cons (.fst (.fst (V 3))) (.call fAppend [.snd (.fst (V 3)), .cons (V 1) (.lit 0)]))
        (.fst (V 3)))
      (.call fAddJunkAux [V 0, V 1, .add (V 2) (.lit 1), .snd (V 3)]))

def addJunkTm : Tm := .call fAddJunkAux [V 0, V 1, .lit 0, V 2]

/-- `[v, chain, M]` -/
def branchRTTm : Tm :=
  .ite (.isNat (V 1)) (.cons (.call Lib3.fInsertS [V 0, V 2]) (.lit 0))
    (.cons (.fst (V 1)) (.cons (.call fBranchRT [V 0, .snd (V 1), V 2]) (.lit 0)))

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 470 => some dupAfterTm | 471 => some cutAtTm | 472 => some inRngTm | 473 => some addVAuxTm
  | 474 => some addVTm | 475 => some addJunkAuxTm | 476 => some addJunkTm | 477 => some branchRTTm
  | 478 => some nxtTm
  | _ => none

def Δ : ℕ → Option Tm := layerΔ E5B.Δ 470 tbl

abbrev size : ℕ := 479

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 479 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h470 : 470 ≤ f := by omega
    simp only [h470, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem extB : E5B.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E5B.Δ_lt h; simp [E5B.size] at this; omega)
theorem extA : E5A.Δ ⊑ Δ := Ext.trans E5B.extA extB
theorem extE1 : E1.e1Δ ⊑ Δ := Ext.trans E5B.extE1 extB

theorem Δ_dupAfter : Δ fDupAfter = some dupAfterTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fDupAfter by decide)]; rfl
theorem Δ_cutAt : Δ fCutAt = some cutAtTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fCutAt by decide)]; rfl
theorem Δ_inRng : Δ fInRng = some inRngTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fInRng by decide)]; rfl
theorem Δ_addVAux : Δ fAddVAux = some addVAuxTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fAddVAux by decide)]; rfl
theorem Δ_addV : Δ fAddV = some addVTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fAddV by decide)]; rfl
theorem Δ_addJunkAux : Δ fAddJunkAux = some addJunkAuxTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fAddJunkAux by decide)]; rfl
theorem Δ_addJunk : Δ fAddJunk = some addJunkTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fAddJunk by decide)]; rfl
theorem Δ_branchRT : Δ fBranchRT = some branchRTTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fBranchRT by decide)]; rfl
theorem Δ_nxt : Δ fNxt = some nxtTm := by
  simp [Δ, layerΔ_ge tbl (show 470 ≤ fNxt by decide)]; rfl

/-! ## sizes -/

theorem sz_dupAfter_le (i : ℕ) (ns : List CNode) : sz (dupAfter i ns) ≤ 2 * sz ns + 3 := by
  unfold dupAfter
  split
  · omega
  · rename_i n hn
    obtain ⟨b, j⟩ := n
    have hmem : (CNode.mk b j) ∈ ns := List.mem_of_getElem? hn
    have h1 := sz_mem_lt hmem
    have h2 := sz_append (ns.take (i + 1)) [CNode.mk b []]
    have h3 := sz_append (ns.take (i + 1) ++ [CNode.mk b []]) (ns.drop (i + 1))
    have h4 := sz_append (ns.take (i + 1)) (ns.drop (i + 1))
    rw [List.take_append_drop] at h4
    have h6 : sz [CNode.mk b []] = sz b + 4 := by
      simp only [sz_cons, sz_cnode]; have : sz ([] : List RT) = 1 := rfl; have : sz ([] : List CNode) = 1 := rfl; omega
    rw [sz_cnode] at h1
    dsimp only
    omega

theorem sz_cutAt_le (y w : List ℕ) (c : CT.Cut) (ns : List CNode) : sz (cutAt y w c ns).1 ≤ 2 * sz ns + 3 := by
  cases c with
  | t1 f => simp only [cutAt]; exact sz_dupAfter_le _ _
  | t2 f => simp only [cutAt]; omega

theorem sz_addVL_le (v s : ℕ) (e : Option ℕ) : ∀ (i : ℕ) (ns : List CNode),
    sz (addVL v s e i ns) ≤ sz ns + 2 * ns.length
  | i, [] => by simp [addVL]
  | i, n :: ns => by
    obtain ⟨b, j⟩ := n
    have ih := sz_addVL_le v s e (i + 1) ns
    have := sz_insert_le v b
    simp only [addVL, List.length_cons, sz_cons, sz_cnode]
    split_ifs <;> simp only [sz_cons, sz_cnode] <;> omega

theorem sz_addV_le (v s : ℕ) (e : Option ℕ) (ns : List CNode) : sz (addV v s e ns) ≤ 2 * sz ns := by
  rw [addV_eq]
  have := sz_addVL_le v s e 0 ns
  have := sz_chain_ge ns
  omega

theorem addJunkL_of_lt (x : ℕ) (br : RT) : ∀ (i : ℕ) (ns : List CNode), x < i → addJunkL x br i ns = ns
  | i, [], _ => by simp [addJunkL]
  | i, n :: ns, h => by
    simp only [addJunkL, if_neg (show ¬ i = x by omega)]
    rw [addJunkL_of_lt x br (i + 1) ns (by omega)]

theorem sz_addJunkL_le (x : ℕ) (br : RT) : ∀ (i : ℕ) (ns : List CNode),
    sz (addJunkL x br i ns) ≤ sz ns + sz br + 2
  | i, [] => by simp [addJunkL]
  | i, n :: ns => by
    obtain ⟨b, j⟩ := n
    have ih := sz_addJunkL_le x br (i + 1) ns
    have := sz_append j [br]
    have h2 : sz [br] = sz br + 2 := by rw [sz_cons]; simp
    by_cases hix : i = x
    · rw [addJunkL, if_pos hix, addJunkL_of_lt x br (i + 1) ns (by omega)]
      simp only [sz_cons, sz_cnode]
      omega
    · rw [addJunkL, if_neg hix]
      simp only [sz_cons, sz_cnode]
      omega

theorem sz_addJunk_le (x : ℕ) (br : RT) (ns : List CNode) : sz (addJunk x br ns) ≤ sz ns + sz br + 2 := by
  rw [addJunk_eq]; exact sz_addJunkL_le x br 0 ns

theorem sz_branchRT_le (v : ℕ) (chain : List (Finset ℕ)) (M : Finset ℕ) :
    sz (branchRT v chain M) ≤ 3 * sz chain + sz M + 4 := by
  induction chain with
  | nil =>
    have := sz_insert_le v M
    simp only [branchRT, List.foldr_nil, sz_rt_node, sz_cons]
    have : sz ([] : List RT) = 1 := rfl
    have : sz ([] : List (Finset ℕ)) = 1 := rfl
    omega
  | cons X chain ih =>
    simp only [branchRT, List.foldr_cons, sz_rt_node, sz_cons] at ih ⊢
    have : sz ([] : List RT) = 1 := rfl
    have := sz_pos X; have := sz_pos chain
    omega

/-! ## the lemmas -/

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem nthD_in_runs {α : Type} [ToVal α] (hB : 1 < B) (xs : List α) (i : ℕ) (d : Val) (hi : i < xs.length) :
    Runs Δ' B fNthD [toVal xs, toVal i, d] (toVal xs[i]) (16 * i + 12) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    have hΔA : E5A.Δ ⊑ Δ' := Ext.trans extA hΔ
    refine Runs.mk (hΔA _ _ E5A.Δ_nthD) ?_
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      ev_start
      · ev_run
      · omega
    | succ i =>
      have h1 := ih i (by simpa using hi)
      simp only [List.getElem_cons_succ]
      ev_start
      · ev_run
      · omega

theorem dupAfter_runs (i : ℕ) (ns : List CNode) (hB : 1000 + 100 * (sz ns + 1) < B) :
    Runs Δ' B fDupAfter [toVal i, toVal ns] (toVal (dupAfter i ns)) (40 * sz ns + 100) := by
  have hE1 := Ext.trans extE1 hΔ
  have hlen := length_le_sz ns
  have hc := sz_chain_ge ns
  have h1 := Lib1.length_runs (l1 hE1) B ns (by omega)
  by_cases hi : i < ns.length
  · have hn := nthD_in_runs hΔ B (by omega) ns i (Val.nat 0) hi
    have h2 := Lib1.take_runs (l1 hE1) B (i + 1) ns (by omega)
    have h3 := Lib1.drop_runs (l1 hE1) B (i + 1) ns (by omega)
    have hd : dupAfter i ns = ns.take (i + 1) ++ [(⟨(ns[i]).bag, []⟩ : CNode)] ++ ns.drop (i + 1) := by
      simp only [dupAfter, List.getElem?_eq_getElem hi]
    have h4 := Lib1.append_runs (l1 hE1) B (ns.take (i + 1)) [(⟨(ns[i]).bag, []⟩ : CNode)]
    have h5 := Lib1.append_runs (l1 hE1) B (ns.take (i + 1) ++ [(⟨(ns[i]).bag, []⟩ : CNode)]) (ns.drop (i + 1))
    have hm1 : min (i + 1) ns.length ≤ ns.length := min_le_right _ _
    have hm2 : (ns.take (i + 1)).length ≤ ns.length := by simp
    refine Runs.mk (hΔ _ _ Δ_dupAfter) ?_
    rw [hd]
    ev_start
    · ev_run
    · simp only [List.length_append, List.length_singleton] at *
      omega
  · have hd : dupAfter i ns = ns := by
      simp only [dupAfter, List.getElem?_eq_none (by omega : ns.length ≤ i)]
    refine Runs.mk (hΔ _ _ Δ_dupAfter) ?_
    rw [hd]
    ev_start
    · ev_run
    · omega

omit hΔ in
theorem getD_succ_eq (l : List ℕ) (f : ℕ) :
    l.getD (f + 1) 0 = (match l.drop f with | [] => 0 | [_] => 0 | _ :: y :: _ => y) := by
  rw [← show (l.drop f).getD 1 0 = l.getD (f + 1) 0 by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  rcases l.drop f with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> simp

theorem nxt_runs (f : ℕ) (l : List ℕ) (hB : 1 < B) :
    Runs Δ' B fNxt [toVal f, toVal l] (toVal (l.getD (f + 1) 0)) (20 * l.length + 30) := by
  have hE1 := Ext.trans extE1 hΔ
  have h1 := Lib1.drop_runs (l1 hE1) B f l hB
  have hm : min f l.length ≤ l.length := min_le_right _ _
  rw [getD_succ_eq]
  refine Runs.mk (hΔ _ _ Δ_nxt) ?_
  rcases hd : l.drop f with _ | ⟨x, _ | ⟨y, r⟩⟩
  · rw [hd] at h1
    simp only []
    ev_start
    · ev_run
    · omega
  · rw [hd] at h1
    simp only []
    ev_start
    · ev_run
    · omega
  · rw [hd] at h1
    simp only []
    ev_start
    · ev_run
    · omega

theorem cutAt_runs (y w : List ℕ) (c : CT.Cut) (ns : List CNode) (s : ℕ) (hy : y.length ≤ s) (hw : w.length ≤ s)
    (hns : sz ns ≤ s) (hB : 1000 + 100 * (2 * s + 1) < B) :
    Runs Δ' B fCutAt [toVal y, toVal w, toVal c, toVal ns] (toVal (cutAt y w c ns)) (100 * s + 400) := by
  have hE1 := Ext.trans extE1 hΔ
  have hΔA : E5A.Δ ⊑ Δ' := Ext.trans extA hΔ
  have hB1 : 1 < B := by omega
  have hkd : fDupAfter < B := by show 470 < B; omega
  have hkn : fNxt < B := by show 478 < B; omega
  cases c with
  | t1 f =>
    have hw1 := E5A.nthD_runs hΔA B hB1 w f 0
    have hd := dupAfter_runs hΔ B (w.getD f 0) ns (by omega)
    refine Runs.mk (hΔ _ _ Δ_cutAt) ?_
    simp only [cutAt, toVal_pair, toVal_cut_t1]
    ev_start
    · ev_run
    · have := length_le_sz ns
      omega
  | t2 f =>
    have hy1 := E5A.nthD_runs hΔA B hB1 y f 0
    have hy2 := nxt_runs hΔ B f y hB1
    have hw1 := E5A.nthD_runs hΔA B hB1 w f 0
    have hw2 := nxt_runs hΔ B f w hB1
    refine Runs.mk (hΔ _ _ Δ_cutAt) ?_
    simp only [cutAt, toVal_pair, toVal_cut_t2]
    by_cases hlt : y.getD f 0 < y.getD (f + 1) 0
    · simp only [hlt, if_true]
      ev_start
      · ev_run
      · omega
    · simp only [hlt, if_false]
      ev_start
      · ev_run
      · omega

theorem inRng_runs (s : ℕ) (e : Option ℕ) (i : ℕ) (hB : 1 < B) :
    Runs Δ' B fInRng [toVal s, toVal e, toVal i] (toVal (inRng s e i)) 20 := by
  refine Runs.mk (hΔ _ _ Δ_inRng) ?_
  cases e with
  | none =>
    by_cases h1 : s ≤ i
    · have : inRng s none i = true := by simp [inRng, h1]
      rw [this]
      have h1' : ¬ i < s := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1']; done) | (simp [h1']; omega))
      · omega
    · have : inRng s none i = false := by simp [inRng, h1]
      rw [this]
      have h1' : i < s := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1']; done) | (simp [h1']; omega))
      · omega
  | some e0 =>
    by_cases h1 : s ≤ i <;> by_cases h2 : i ≤ e0
    · have : inRng s (some e0) i = true := by simp [inRng, h1, h2]
      rw [this]
      have h1' : ¬ i < s := by omega
      have h2' : ¬ e0 < i := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1', h2']; done) | (simp [h1', h2']; omega))
      · omega
    · have : inRng s (some e0) i = false := by simp [inRng, h1, h2]
      rw [this]
      have h1' : ¬ i < s := by omega
      have h2' : e0 < i := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1', h2']; done) | (simp [h1', h2']; omega))
      · omega
    · have : inRng s (some e0) i = false := by simp [inRng, h1, h2]
      rw [this]
      have h1' : i < s := by omega
      have h2' : ¬ e0 < i := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1', h2']; done) | (simp [h1', h2']; omega))
      · omega
    · have : inRng s (some e0) i = false := by simp [inRng, h1, h2]
      rw [this]
      have h1' : i < s := by omega
      have h2' : e0 < i := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1', h2']; done) | (simp [h1', h2']; omega))
      · omega

theorem addVAux_runs (v s : ℕ) (e : Option ℕ) : ∀ (ns : List CNode) (i : ℕ), i + sz ns + 1000 < B →
    Runs Δ' B fAddVAux [toVal v, toVal s, toVal e, toVal i, toVal ns] (toVal (addVL v s e i ns)) (80 * sz ns + 8)
  | [], i, hB => by
    refine Runs.mk (hΔ _ _ Δ_addVAux) ?_
    simp only [addVL]
    ev_start
    · ev_run
    · simp
  | n :: ns, i, hB => by
    obtain ⟨b, j⟩ := n
    have hE1 := Ext.trans extE1 hΔ
    have hs : sz (CNode.mk b j :: ns) = sz b + sz j + 1 + sz ns + 1 := by rw [sz_cons, sz_cnode]
    have hc1 := card_le_sz b
    have hb1 := sz_pos j
    have hin := inRng_runs hΔ B s e i (by omega)
    have hi2 := Lib3.insert_runs (l3 hE1) B v b
    have ih := addVAux_runs v s e ns (i + 1) (by omega)
    have hk : fInRng < B := by show 472 < B; omega
    have hk2 : fAddVAux < B := by show 473 < B; omega
    refine Runs.mk (hΔ _ _ Δ_addVAux) ?_
    simp only [toVal_cons, toVal_cnode]
    by_cases hc : inRng s e i = true
    · simp only [hc] at hin
      simp only [addVL, hc, if_true, toVal_cons, toVal_cnode]
      ev_start
      · ev_run
      · have hsb := sz_finset b
        omega
    · simp only [Bool.not_eq_true] at hc
      simp only [hc] at hin
      simp only [addVL, hc, Bool.false_eq_true, if_false, toVal_cons, toVal_cnode]
      ev_start
      · ev_run
      · omega

theorem addV_runs (v s : ℕ) (e : Option ℕ) (ns : List CNode) (hB : sz ns + 1000 < B) :
    Runs Δ' B fAddV [toVal v, toVal s, toVal e, toVal ns] (toVal (addV v s e ns)) (80 * sz ns + 20) := by
  have h1 := addVAux_runs hΔ B v s e ns 0 (by omega)
  have hk : fAddVAux < B := by show 473 < B; omega
  refine Runs.mk (hΔ _ _ Δ_addV) ?_
  rw [addV_eq]
  ev_start
  · ev_run
  · omega

theorem addJunkAux_runs (x : ℕ) (br : RT) : ∀ (ns : List CNode) (i : ℕ), i + sz ns + 1000 < B →
    Runs Δ' B fAddJunkAux [toVal x, toVal br, toVal i, toVal ns] (toVal (addJunkL x br i ns)) (60 * sz ns + 8)
  | [], i, hB => by
    refine Runs.mk (hΔ _ _ Δ_addJunkAux) ?_
    simp only [addJunkL]
    ev_start
    · ev_run
    · simp
  | n :: ns, i, hB => by
    obtain ⟨b, j⟩ := n
    have hE1 := Ext.trans extE1 hΔ
    have hs : sz (CNode.mk b j :: ns) = sz b + sz j + 1 + sz ns + 1 := by rw [sz_cons, sz_cnode]
    have hb1 := sz_pos b
    have hj1 := length_le_sz j
    have ih := addJunkAux_runs x br ns (i + 1) (by omega)
    have hk2 : fAddJunkAux < B := by show 475 < B; omega
    refine Runs.mk (hΔ _ _ Δ_addJunkAux) ?_
    simp only [toVal_cons, toVal_cnode]
    by_cases hix : i = x
    · have ha := Lib1.append_runs (l1 hE1) B j [br]
      simp only [addJunkL, hix, if_true, toVal_cons, toVal_cnode]
      subst hix
      ev_start
      · ev_run
      · omega
    · simp only [addJunkL, hix, if_false, toVal_cons, toVal_cnode]
      ev_start
      · ev_run
      · omega

theorem addJunk_runs (x : ℕ) (br : RT) (ns : List CNode) (hB : sz ns + 1000 < B) :
    Runs Δ' B fAddJunk [toVal x, toVal br, toVal ns] (toVal (addJunk x br ns)) (60 * sz ns + 20) := by
  have h1 := addJunkAux_runs hΔ B x br ns 0 (by omega)
  have hk : fAddJunkAux < B := by show 475 < B; omega
  refine Runs.mk (hΔ _ _ Δ_addJunk) ?_
  rw [addJunk_eq]
  ev_start
  · ev_run
  · omega

theorem branchRT_runs (v : ℕ) (chain : List (Finset ℕ)) (M : Finset ℕ) (hB : 1000 + 100 * (sz chain + sz M + 1) < B) :
    Runs Δ' B fBranchRT [toVal v, toVal chain, toVal M] (toVal (branchRT v chain M))
      (40 * sz chain + 40 * sz M + 100) := by
  have hE1 := Ext.trans extE1 hΔ
  induction chain with
  | nil =>
    have hi := Lib3.insert_runs (l3 hE1) B v M
    have hc := card_le_sz M
    refine Runs.mk (hΔ _ _ Δ_branchRT) ?_
    simp only [branchRT, List.foldr_nil, toVal_rt, toVal_nil]
    ev_start
    · ev_run
    · have : sz ([] : List (Finset ℕ)) = 1 := rfl
      omega
  | cons X chain ih =>
    have ih := ih (by simp only [sz_cons] at hB; omega)
    have hk : fBranchRT < B := by show 477 < B; omega
    refine Runs.mk (hΔ _ _ Δ_branchRT) ?_
    simp only [branchRT, List.foldr_cons, toVal_rt, toVal_cons, toVal_nil] at ih ⊢
    ev_start
    · ev_run
    · simp only [sz_cons]
      have := sz_pos X
      omega

end proofs
end E5C1
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E5C2` -/

section
/-!
# WP E5 (layer C2): `processRun`, `applyKids`, `applyOpt`

Ids `480 …`:

| id | function | arguments |
|---|---|---|
| 480 `fMapP1` | `Option.map (· + 1)` | `[o]` |
| 481 `fEndStep` | the `endStep` of `processRun` | `[y, wp, w, ns]` |
| 482 `fPreStep` | the `preStep` of `processRun` | `[y, wp, pre, endS]` |
| 483 `fProcessRun` | `processRun` | `[v, pre, w, r]` |
| 484 `fApplyKids` | `applyKids` | `[v, ps, ks]` |
| 485 `fApplyOpt` | `applyOpt` | `[v, p, k]` |

The Lean `let`/`match` of `processRun` is exposed as `endStepL`, `preStepL` (`processRun_eq`).
Cost: `cPR s · wn w` where `wn` counts the nodes of the region plan.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Lax117284Proofs.Treewidth.Fun
namespace E5C2

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5 E5A E5C1

abbrev fMapP1 : ℕ := 480
abbrev fEndStep : ℕ := 481
abbrev fPreStep : ℕ := 482
abbrev fProcessRun : ℕ := 483
abbrev fApplyKids : ℕ := 484
abbrev fApplyOpt : ℕ := 485

/-! ## the Lean side -/

def endStepL (y wp : List ℕ) (w : CT.WPlan) (ns : List CNode) : List CNode × Option ℕ :=
  match w with
  | .endAt c => ((cutAt y wp c ns).1, some (cutAt y wp c ns).2)
  | .whole _ => (ns, none)

def preStepL (y wp : List ℕ) (pre : Option CT.Cut) (endS : List CNode × Option ℕ) :
    List CNode × ℕ × Option ℕ :=
  match pre with
  | none => (endS.1, 0, endS.2)
  | some c => ((cutAt y wp c endS.1).1, (cutAt y wp c endS.1).2 + 1,
      if c.isT1 then endS.2.map (· + 1) else endS.2)

theorem processRun_eq (v : ℕ) (pre : Option CT.Cut) (w : CT.WPlan) (S : Finset ℕ) (ns : List CNode)
    (ks : List AR) :
    processRun v pre w (.run S ns ks) =
      .run S (addV v (preStepL (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card))) (witnesses (ns.map (fun n => n.bag.card)))
          pre (endStepL (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card))) (witnesses (ns.map (fun n => n.bag.card))) w ns)).2.1
        (preStepL (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card))) (witnesses (ns.map (fun n => n.bag.card)))
          pre (endStepL (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card))) (witnesses (ns.map (fun n => n.bag.card))) w ns)).2.2
        (preStepL (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card))) (witnesses (ns.map (fun n => n.bag.card)))
          pre (endStepL (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card))) (witnesses (ns.map (fun n => n.bag.card))) w ns)).1)
        (match w with | .endAt _ => ks | .whole ps => applyKids v ps ks) := by
  cases w <;> cases pre <;> (simp only [processRun, endStepL, preStepL]; try rfl)

/-! ## the terms -/

def mapP1Tm : Tm := .ite (.isNat (V 0)) (.lit 0) (.cons (.lit 1) (.add (.snd (V 0)) (.lit 1)))

/-- `[y, wp, w, ns]` -/
def endStepTm : Tm :=
  .ite (.eq (.fst (V 2)) (.lit 1))
    (.letE (.call fCutAt [V 0, V 1, .snd (V 2), V 3])
      (.cons (.fst (V 0)) (.cons (.lit 1) (.snd (V 0)))))
    (.cons (V 3) (.lit 0))

/-- `[y, wp, pre, endS]` -/
def preStepTm : Tm :=
  .ite (.isNat (V 2))
    (.cons (.fst (V 3)) (.cons (.lit 0) (.snd (V 3))))
    (.letE (.call fCutAt [V 0, V 1, .snd (V 2), .fst (V 3)])
      (.cons (.fst (V 0))
        (.cons (.add (.snd (V 0)) (.lit 1))
          (.ite (.eq (.fst (.snd (V 3))) (.lit 1)) (.call fMapP1 [.snd (V 4)]) (.snd (V 4))))))

/-- `[v, pre, w, r]` -/
def processRunTm : Tm :=
  .letE (.call fCards [.fst (.snd (V 3))])
    (.letE (.call E1A.fTypical [V 0])
      (.letE (.call E1B.fWitnesses [V 1])
        (.letE (.call fEndStep [V 1, V 0, V 5, .fst (.snd (V 6))])
          (.letE (.call fPreStep [V 2, V 1, V 5, V 0])
            (.letE (.call fAddV [V 5, .fst (.snd (V 0)), .snd (.snd (V 0)), .fst (V 0)])
              (.cons (.fst (V 9))
                (.cons (V 0)
                  (.ite (.eq (.fst (V 8)) (.lit 1)) (.snd (.snd (V 9)))
                    (.call fApplyKids [V 6, .snd (V 8), .snd (.snd (V 9))])))))))))

/-- `[v, ps, ks]` -/
def applyKidsTm : Tm :=
  .ite (.isNat (V 1)) (V 2)
    (.ite (.isNat (V 2)) (.lit 0)
      (.cons (.call fApplyOpt [V 0, .fst (V 1), .fst (V 2)])
        (.call fApplyKids [V 0, .snd (V 1), .snd (V 2)])))

/-- `[v, p, k]` -/
def applyOptTm : Tm :=
  .ite (.isNat (V 1)) (V 2) (.call fProcessRun [V 0, .lit 0, .snd (V 1), V 2])

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 480 => some mapP1Tm | 481 => some endStepTm | 482 => some preStepTm | 483 => some processRunTm
  | 484 => some applyKidsTm | 485 => some applyOptTm | _ => none

def Δ : ℕ → Option Tm := layerΔ E5C1.Δ 480 tbl

abbrev size : ℕ := 486

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 486 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h480 : 480 ≤ f := by omega
    simp only [h480, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem ext1 : E5C1.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E5C1.Δ_lt h; simp [E5C1.size] at this; omega)
theorem extB : E5B.Δ ⊑ Δ := Ext.trans E5C1.extB ext1
theorem extA : E5A.Δ ⊑ Δ := Ext.trans E5C1.extA ext1
theorem extE1 : E1.e1Δ ⊑ Δ := Ext.trans E5C1.extE1 ext1

theorem Δ_mapP1 : Δ fMapP1 = some mapP1Tm := by
  simp [Δ, layerΔ_ge tbl (show 480 ≤ fMapP1 by decide)]; rfl
theorem Δ_endStep : Δ fEndStep = some endStepTm := by
  simp [Δ, layerΔ_ge tbl (show 480 ≤ fEndStep by decide)]; rfl
theorem Δ_preStep : Δ fPreStep = some preStepTm := by
  simp [Δ, layerΔ_ge tbl (show 480 ≤ fPreStep by decide)]; rfl
theorem Δ_processRun : Δ fProcessRun = some processRunTm := by
  simp [Δ, layerΔ_ge tbl (show 480 ≤ fProcessRun by decide)]; rfl
theorem Δ_applyKids : Δ fApplyKids = some applyKidsTm := by
  simp [Δ, layerΔ_ge tbl (show 480 ≤ fApplyKids by decide)]; rfl
theorem Δ_applyOpt : Δ fApplyOpt = some applyOptTm := by
  simp [Δ, layerΔ_ge tbl (show 480 ≤ fApplyOpt by decide)]; rfl

/-! ## witnesses are small -/

theorem wpush_snd_le (L : ℕ) : ∀ (st : List (ℕ × ℕ)) (y j : ℕ), (∀ p ∈ st, p.2 ≤ L) → j ≤ L →
    ∀ p ∈ wpush st y j, p.2 ≤ L
  | [], y, j, _, hj => by
    intro p hp; simp only [wpush, List.mem_singleton] at hp; subst hp; exact hj
  | (x, i) :: t, y, j, hst, hj => by
    intro p hp
    have hi : i ≤ L := hst (x, i) (by simp)
    have ht : ∀ q ∈ t, q.2 ≤ L := fun q hq => hst q (List.mem_cons_of_mem _ hq)
    rw [E1B.wpush_cons] at hp
    split_ifs at hp with h1 h2
    · simp only [List.mem_singleton] at hp; subst hp; exact hi
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hi
      · exact hj
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact hi
      · exact wpush_snd_le L t y j ht hj p hp

theorem witnessesAux_snd_le (L : ℕ) : ∀ (l : List ℕ) (j : ℕ) (st : List (ℕ × ℕ)),
    (∀ p ∈ st, p.2 ≤ L) → j + l.length ≤ L → ∀ p ∈ witnessesAux j st l, p.2 ≤ L
  | [], j, st, hst, _ => by simpa [witnessesAux] using hst
  | y :: l, j, st, hst, hj => by
    simp only [witnessesAux]
    simp only [List.length_cons] at hj
    exact witnessesAux_snd_le L l (j + 1) (wpush st y j) (wpush_snd_le L st y j hst (by omega)) (by omega)

theorem witnesses_le (a : List ℕ) : ∀ e ∈ witnesses a, e ≤ a.length := by
  intro e he
  unfold witnesses at he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
  exact witnessesAux_snd_le a.length a 0 [] (by simp) (by omega) p hp

theorem cutAt_snd_le (y w : List ℕ) (L : ℕ) (hw : ∀ e ∈ w, e ≤ L) (c : CT.Cut) (ns : List CNode) :
    (cutAt y w c ns).2 ≤ L := by
  have key : ∀ f, w.getD f 0 ≤ L := by
    intro f
    by_cases hf : f < w.length
    · rw [List.getD_eq_getElem _ _ hf]; exact hw _ (List.getElem_mem hf)
    · rw [List.getD_eq_default _ _ (by omega)]; omega
  cases c with
  | t1 f => simp only [cutAt]; exact key f
  | t2 f =>
    simp only [cutAt]
    split_ifs
    · exact key f
    · have := key (f + 1); omega

/-! ## sizes of the steps -/

theorem sz_endStep_le (y wp : List ℕ) (w : CT.WPlan) (ns : List CNode) :
    sz (endStepL y wp w ns).1 ≤ 2 * sz ns + 3 := by
  cases w with
  | endAt c => simp only [endStepL]; exact sz_cutAt_le y wp c ns
  | whole ps => simp only [endStepL]; omega

theorem endStep_snd_le (y wp : List ℕ) (L : ℕ) (hw : ∀ e ∈ wp, e ≤ L) (w : CT.WPlan) (ns : List CNode) :
    ∀ e, (endStepL y wp w ns).2 = some e → e ≤ L := by
  intro e he
  cases w with
  | endAt c =>
    simp only [endStepL, Option.some.injEq] at he
    rw [← he]; exact cutAt_snd_le y wp L hw c ns
  | whole ps => simp [endStepL] at he

theorem sz_preStep_le (y wp : List ℕ) (pre : Option CT.Cut) (endS : List CNode × Option ℕ) :
    sz (preStepL y wp pre endS).1 ≤ 2 * sz endS.1 + 3 := by
  cases pre with
  | none => simp only [preStepL]; omega
  | some c => simp only [preStepL]; exact sz_cutAt_le y wp c endS.1

theorem preStep_snd_le (y wp : List ℕ) (L : ℕ) (hw : ∀ e ∈ wp, e ≤ L) (pre : Option CT.Cut)
    (endS : List CNode × Option ℕ) (hE2 : ∀ e, endS.2 = some e → e ≤ L) :
    (preStepL y wp pre endS).2.1 ≤ L + 1 ∧ ∀ e, (preStepL y wp pre endS).2.2 = some e → e ≤ L + 1 := by
  cases pre with
  | none => simp only [preStepL]; exact ⟨by omega, fun e he => by have := hE2 e he; omega⟩
  | some c =>
    have h1 := cutAt_snd_le y wp L hw c endS.1
    refine ⟨by simp only [preStepL]; omega, fun e he => ?_⟩
    simp only [preStepL] at he
    split_ifs at he with hc
    · obtain ⟨e', he', rfl⟩ := Option.map_eq_some_iff.1 he
      have := hE2 e' he'; omega
    · have := hE2 e he; omega

/-! ## region plans: size measure -/

mutual
def wn : CT.WPlan → ℕ
  | .endAt _ => 1
  | .whole ps => 1 + wnL ps
def wnL : List (Option CT.WPlan) → ℕ
  | [] => 0
  | p :: ps => wnO p + wnL ps
def wnO : Option CT.WPlan → ℕ
  | none => 1
  | some p => wn p
end

/-- the local cost bound of `processRun` -/
def cPR (s : ℕ) : ℕ := 3000 * (s + 1) ^ 3

/-! ## sizes of the results -/

theorem sz_processRun_aux (v : ℕ) (pre : Option CT.Cut) (w : CT.WPlan) (S : Finset ℕ) (ns : List CNode)
    (ks : List AR) : sz ((processRun v pre w (.run S ns ks)).chain) ≤ 8 * sz ns + 18 ∧
    (processRun v pre w (.run S ns ks)).S = S := by
  rw [processRun_eq]
  refine ⟨?_, rfl⟩
  simp only [AR.chain]
  refine le_trans (sz_addV_le _ _ _ _) ?_
  have h1 := sz_preStep_le (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card)))
    (witnesses (ns.map (fun n => n.bag.card))) pre
    (endStepL (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card)))
      (witnesses (ns.map (fun n => n.bag.card))) w ns)
  have h2 := sz_endStep_le (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card)))
    (witnesses (ns.map (fun n => n.bag.card))) w ns
  omega

mutual
theorem sz_processRun_le_rec (v : ℕ) : ∀ (pre : Option CT.Cut) (w : CT.WPlan) (r : AR),
    sz (processRun v pre w r) ≤ 8 * sz r + 18 * wn w
  | pre, .endAt c, .run S ns ks => by
    have h := sz_processRun_aux v pre (.endAt c) S ns ks
    rw [processRun_eq]
    simp only [wn, sz_ar]
    rw [processRun_eq] at h
    simp only [AR.chain] at h
    omega
  | pre, .whole ps, .run S ns ks => by
    have h := sz_processRun_aux v pre (.whole ps) S ns ks
    have hk := sz_applyKids_le_rec v ps ks
    rw [processRun_eq]
    simp only [wn, sz_ar]
    rw [processRun_eq] at h
    simp only [AR.chain] at h
    omega
theorem sz_applyKids_le_rec (v : ℕ) : ∀ (ps : List (Option CT.WPlan)) (ks : List AR),
    sz (applyKids v ps ks) ≤ 8 * sz ks + 18 * wnL ps
  | [], ks => by simp only [applyKids, wnL]; omega
  | p :: ps, [] => by simp [applyKids, sz_cons]; have := sz_pos ([] : List AR); omega
  | p :: ps, k :: ks => by
    have h1 := sz_applyOpt_le_rec v p k
    have h2 := sz_applyKids_le_rec v ps ks
    simp only [applyKids, wnL, sz_cons]
    omega
theorem sz_applyOpt_le_rec (v : ℕ) : ∀ (p : Option CT.WPlan) (k : AR),
    sz (applyOpt v p k) ≤ 8 * sz k + 18 * wnO p
  | none, k => by simp only [applyOpt, wnO]; omega
  | some p, k => by
    have := sz_processRun_le_rec v none p k
    simp only [applyOpt, wnO]; exact this
end

theorem sz_processRun_le_pair : (type_of% @sz_processRun_le_rec) ∧ (type_of% @sz_applyKids_le_rec) ∧ (type_of% @sz_applyOpt_le_rec) :=
  ⟨@sz_processRun_le_rec, @sz_applyKids_le_rec, @sz_applyOpt_le_rec⟩

theorem sz_processRun_le : type_of% @sz_processRun_le_rec := sz_processRun_le_pair.1


mutual
theorem wn_le_sz_rec : ∀ w : CT.WPlan, wn w ≤ sz w
  | .endAt c => by simp [wn, sz_pos]; have := sz_pos (CT.WPlan.endAt c); omega
  | .whole ps => by
    have := wnL_le_sz_rec ps
    have h : sz (CT.WPlan.whole ps) = sz ps + 2 := by simp only [sz, toVal_wp_whole, Val.size]; omega
    simp only [wn]; omega
theorem wnL_le_sz_rec : ∀ ps : List (Option CT.WPlan), wnL ps ≤ sz ps
  | [] => by simp [wnL]
  | p :: ps => by
    have := wnO_le_sz_rec p
    have := wnL_le_sz_rec ps
    simp only [wnL, sz_cons]; omega
theorem wnO_le_sz_rec : ∀ p : Option CT.WPlan, wnO p ≤ sz p
  | none => by simp [wnO]
  | some p => by
    have := wn_le_sz_rec p
    simp only [wnO, sz_some]; omega
end

theorem wn_le_sz_pair : (type_of% @wn_le_sz_rec) ∧ (type_of% @wnL_le_sz_rec) ∧ (type_of% @wnO_le_sz_rec) :=
  ⟨@wn_le_sz_rec, @wnL_le_sz_rec, @wnO_le_sz_rec⟩

theorem wn_le_sz : type_of% @wn_le_sz_rec := wn_le_sz_pair.1


/-! ## the lemmas -/

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem mapP1_runs (o : Option ℕ) (hB : 1 < B) (ho : ∀ e, o = some e → e + 2 < B) :
    Runs Δ' B fMapP1 [toVal o] (toVal (o.map (· + 1))) 12 := by
  refine Runs.mk (hΔ _ _ Δ_mapP1) ?_
  cases o with
  | none =>
    simp only [Option.map_none]
    ev_start
    · ev_run
    · omega
  | some e =>
    have := ho e rfl
    simp only [Option.map_some, toVal_some]
    ev_start
    · ev_run
    · omega

theorem endStep_runs (y wp : List ℕ) (w : CT.WPlan) (ns : List CNode) (s : ℕ) (hy : y.length ≤ s)
    (hwp : wp.length ≤ s) (hns : sz ns ≤ s) (hB : 3000 + 400 * (s + 1) < B) :
    Runs Δ' B fEndStep [toVal y, toVal wp, toVal w, toVal ns] (toVal (endStepL y wp w ns)) (100 * s + 440) := by
  have hkc : fCutAt < B := lt_of_bnd hB (by decide)
  cases w with
  | endAt c =>
    have h1 := cutAt_runs (Ext.trans ext1 hΔ) B y wp c ns s hy hwp hns (by omega)
    refine Runs.mk (hΔ _ _ Δ_endStep) ?_
    simp only [endStepL, toVal_wp_endAt, toVal_pair, toVal_some]
    ev_start
    · ev_run
    · omega
  | whole ps =>
    refine Runs.mk (hΔ _ _ Δ_endStep) ?_
    simp only [endStepL, toVal_wp_whole, toVal_pair, toVal_none]
    ev_start
    · ev_run
    · omega

theorem preStep_runs (y wp : List ℕ) (pre : Option CT.Cut) (endS : List CNode × Option ℕ) (s : ℕ)
    (hy : y.length ≤ s) (hwp : wp.length ≤ s) (hL : ∀ e ∈ wp, e ≤ s) (hE : sz endS.1 ≤ s)
    (hE2 : ∀ e, endS.2 = some e → e ≤ s) (hB : 3000 + 400 * (s + 1) < B) :
    Runs Δ' B fPreStep [toVal y, toVal wp, toVal pre, toVal endS] (toVal (preStepL y wp pre endS))
      (100 * s + 500) := by
  have hkc : fCutAt < B := lt_of_bnd hB (by decide)
  have hkm : fMapP1 < B := lt_of_bnd hB (by decide)
  have hB1 : 1 < B := by omega
  cases pre with
  | none =>
    refine Runs.mk (hΔ _ _ Δ_preStep) ?_
    simp only [preStepL, toVal_pair, toVal_none]
    ev_start
    · ev_run
    · omega
  | some c =>
    have h1 := cutAt_runs (Ext.trans ext1 hΔ) B y wp c endS.1 s hy hwp hE (by omega)
    have h2 := cutAt_snd_le y wp s hL c endS.1
    have h3 := mapP1_runs hΔ B endS.2 hB1 (fun e he => by have := hE2 e he; omega)
    refine Runs.mk (hΔ _ _ Δ_preStep) ?_
    cases c with
    | t1 f =>
      simp only [preStepL, toVal_pair, toVal_some, toVal_cut_t1, CT.Cut.isT1, if_true]
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
    | t2 f =>
      simp only [preStepL, toVal_pair, toVal_some, toVal_cut_t2, CT.Cut.isT1, Bool.false_eq_true, if_false]
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega

omit hΔ in
theorem length_witnesses_le (a : List ℕ) : (witnesses a).length ≤ a.length := by
  have := E1B.length_witAux_le a [] 0
  simpa [witnesses] using this

mutual
theorem processRun_runs_rec (s : ℕ) (hB : 3000 + 400 * (8 * s + 16) < B) (v : ℕ) :
    ∀ (pre : Option CT.Cut) (w : CT.WPlan) (r : AR), sz r ≤ s →
    Runs Δ' B fProcessRun [toVal v, toVal pre, toVal w, toVal r] (toVal (processRun v pre w r))
      (cPR s * wn w)
  | pre, .endAt c, .run S ns ks, hr => by
    have hns : sz ns ≤ s := by have := sz_c_lt S ns ks; omega
    have hE1 := Ext.trans extE1 hΔ
    have hΔA : E5A.Δ ⊑ Δ' := Ext.trans extA hΔ
    have hlen := length_le_sz ns
    have hc4 := sz_chain_ge ns
    have hB1 : 1 < B := by omega
    have hB2 : 3000 + 400 * (s + 1) < B := by omega
    have hB3 : 3000 + 400 * ((2 * s + 3) + 1) < B := by omega
    rw [processRun_eq]
    simp only [wn]
    generalize hsizes : ns.map (fun n => n.bag.card) = sizes
    have hsl : sizes.length = ns.length := by rw [← hsizes]; simp
    have hy : (Lax117284Proofs.Treewidth.Seq.typical sizes).length ≤ s := le_trans (E5.typical_length_le sizes) (by omega)
    have hwpl : (witnesses sizes).length ≤ s := le_trans (length_witnesses_le sizes) (by omega)
    have hL : ∀ e ∈ witnesses sizes, e ≤ s := fun e he => le_trans (witnesses_le sizes e he) (by omega)
    have hcards := cards_runs hΔA B ns (by omega)
    rw [hsizes] at hcards
    have htyp := E1A.typical_runs (eA hE1) B hB1 sizes
    have hwit := E1B.witnesses_runs (eB hE1) B sizes (by omega)
    have hend := endStep_runs hΔ B (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) (.endAt c) ns s hy hwpl hns hB2
    have hE := sz_endStep_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) (.endAt c) ns
    have hE2 := endStep_snd_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) s hL (.endAt c) ns
    generalize hend' : endStepL (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) (.endAt c) ns = endS at hend hE hE2 ⊢
    have hpre' := preStep_runs hΔ B (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) pre endS (2 * s + 3) (by omega) (by omega)
      (fun e he => by have := hL e he; omega) (by omega) (fun e he => by have := hE2 e he; omega) hB3
    have hS1 := sz_preStep_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) pre endS
    have hS2 := preStep_snd_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) s hL pre endS hE2
    generalize hpre'' : preStepL (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) pre endS = preS at hpre' hS1 hS2 ⊢
    have hadd := addV_runs (Ext.trans ext1 hΔ) B v preS.2.1 preS.2.2 preS.1 (by omega)
    have hk1 : fCards < B := lt_of_bnd hB2 (by decide)
    have hk2 : fEndStep < B := lt_of_bnd hB2 (by decide)
    have hk3 : fPreStep < B := lt_of_bnd hB2 (by decide)
    have hk4 : fAddV < B := lt_of_bnd hB2 (by decide)
    have hT : (sizes.length + 1) ^ 3 ≤ (s + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hT1 : s + 1 ≤ (s + 1) ^ 3 := le_pw (by omega) (by omega)
    have hcp : cPR s = 3000 * (s + 1) ^ 3 := rfl
    refine Runs.mk (hΔ _ _ Δ_processRun) ?_
    simp only [toVal_ar, toVal_wp_endAt]
    ev_start
    · ev_run
    · omega
  | pre, .whole ps, .run S ns ks, hr => by
    have hns : sz ns ≤ s := by have := sz_c_lt S ns ks; omega
    have hks : sz ks ≤ s := by have := sz_ks_lt S ns ks; omega
    have hE1 := Ext.trans extE1 hΔ
    have hΔA : E5A.Δ ⊑ Δ' := Ext.trans extA hΔ
    have hlen := length_le_sz ns
    have hlk := length_le_sz ks
    have hc4 := sz_chain_ge ns
    have hB1 : 1 < B := by omega
    have hB2 : 3000 + 400 * (s + 1) < B := by omega
    have hB3 : 3000 + 400 * ((2 * s + 3) + 1) < B := by omega
    have hK := applyKids_runs_rec s hB v ps ks hks
    rw [processRun_eq]
    simp only [wn]
    generalize hsizes : ns.map (fun n => n.bag.card) = sizes
    have hsl : sizes.length = ns.length := by rw [← hsizes]; simp
    have hy : (Lax117284Proofs.Treewidth.Seq.typical sizes).length ≤ s := le_trans (E5.typical_length_le sizes) (by omega)
    have hwpl : (witnesses sizes).length ≤ s := le_trans (length_witnesses_le sizes) (by omega)
    have hL : ∀ e ∈ witnesses sizes, e ≤ s := fun e he => le_trans (witnesses_le sizes e he) (by omega)
    have hcards := cards_runs hΔA B ns (by omega)
    rw [hsizes] at hcards
    have htyp := E1A.typical_runs (eA hE1) B hB1 sizes
    have hwit := E1B.witnesses_runs (eB hE1) B sizes (by omega)
    have hend := endStep_runs hΔ B (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) (.whole ps) ns s hy hwpl hns hB2
    simp only [toVal_wp_whole] at hend
    have hE := sz_endStep_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) (.whole ps) ns
    have hE2 := endStep_snd_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) s hL (.whole ps) ns
    generalize hend' : endStepL (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) (.whole ps) ns = endS at hend hE hE2 ⊢
    have hpre' := preStep_runs hΔ B (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) pre endS (2 * s + 3) (by omega) (by omega)
      (fun e he => by have := hL e he; omega) (by omega) (fun e he => by have := hE2 e he; omega) hB3
    have hS1 := sz_preStep_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) pre endS
    have hS2 := preStep_snd_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) s hL pre endS hE2
    generalize hpre'' : preStepL (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) pre endS = preS at hpre' hS1 hS2 ⊢
    have hadd := addV_runs (Ext.trans ext1 hΔ) B v preS.2.1 preS.2.2 preS.1 (by omega)
    have hk1 : fCards < B := lt_of_bnd hB2 (by decide)
    have hk2 : fEndStep < B := lt_of_bnd hB2 (by decide)
    have hk3 : fPreStep < B := lt_of_bnd hB2 (by decide)
    have hk4 : fAddV < B := lt_of_bnd hB2 (by decide)
    have hk5 : fApplyKids < B := lt_of_bnd hB2 (by decide)
    have hT : (sizes.length + 1) ^ 3 ≤ (s + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hT1 : s + 1 ≤ (s + 1) ^ 3 := le_pw (by omega) (by omega)
    have hcp : cPR s = 3000 * (s + 1) ^ 3 := rfl
    have e : cPR s * (1 + wnL ps) = cPR s + cPR s * wnL ps := by ring
    refine Runs.mk (hΔ _ _ Δ_processRun) ?_
    simp only [toVal_ar, toVal_wp_whole]
    ev_start
    · ev_run
    · rw [e]; omega

theorem applyKids_runs_rec (s : ℕ) (hB : 3000 + 400 * (8 * s + 16) < B) (v : ℕ) :
    ∀ (ps : List (Option CT.WPlan)) (ks : List AR), sz ks ≤ s →
    Runs Δ' B fApplyKids [toVal v, toVal ps, toVal ks] (toVal (applyKids v ps ks))
      (cPR s * wnL ps + 60 * ks.length + 8)
  | [], ks, hks => by
    refine Runs.mk (hΔ _ _ Δ_applyKids) ?_
    simp only [applyKids, wnL]
    ev_start
    · ev_run
    · omega
  | p :: ps, [], hks => by
    refine Runs.mk (hΔ _ _ Δ_applyKids) ?_
    simp only [applyKids]
    ev_start
    · ev_run
    · omega
  | p :: ps, k :: ks, hks => by
    have hk : sz k ≤ s := by have := sz_head_lt k ks; omega
    have hks' : sz ks ≤ s := by have := sz_tail_lt k ks; omega
    have h1 := applyOpt_runs_rec s hB v p k hk
    have h2 := applyKids_runs_rec s hB v ps ks hks'
    have hB2 : 3000 + 400 * (s + 1) < B := by omega
    have hk1 : fApplyOpt < B := lt_of_bnd hB2 (by decide)
    have hk2 : fApplyKids < B := lt_of_bnd hB2 (by decide)
    refine Runs.mk (hΔ _ _ Δ_applyKids) ?_
    simp only [applyKids, wnL, toVal_cons, List.length_cons]
    ev_start
    · ev_run
    · have e : cPR s * (wnO p + wnL ps) = cPR s * wnO p + cPR s * wnL ps := by ring
      rw [e]; omega

theorem applyOpt_runs_rec (s : ℕ) (hB : 3000 + 400 * (8 * s + 16) < B) (v : ℕ) :
    ∀ (p : Option CT.WPlan) (k : AR), sz k ≤ s →
    Runs Δ' B fApplyOpt [toVal v, toVal p, toVal k] (toVal (applyOpt v p k)) (cPR s * wnO p + 20)
  | none, k, hk => by
    refine Runs.mk (hΔ _ _ Δ_applyOpt) ?_
    simp only [applyOpt, wnO]
    ev_start
    · ev_run
    · omega
  | some p, k, hk => by
    have h1 := processRun_runs_rec s hB v none p k hk
    have hB2 : 3000 + 400 * (s + 1) < B := by omega
    have hk1 : fProcessRun < B := lt_of_bnd hB2 (by decide)
    refine Runs.mk (hΔ _ _ Δ_applyOpt) ?_
    simp only [applyOpt, wnO, toVal_some]
    ev_start
    · ev_run
    · omega

end

end proofs

theorem processRun_runs_pair : (type_of% @processRun_runs_rec) ∧ (type_of% @applyKids_runs_rec) ∧ (type_of% @applyOpt_runs_rec) :=
  ⟨@processRun_runs_rec, @applyKids_runs_rec, @applyOpt_runs_rec⟩

theorem processRun_runs : type_of% @processRun_runs_rec := processRun_runs_pair.1

end E5C2
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E5C3` -/

section
/-!
# WP E5 (layer C3): `applyAt`, `applyRun`, `applyPlan`

Ids `490 …`:

| id | function | arguments |
|---|---|---|
| 490 `fAttCut` | the cut of `applyAt` for an attach plan | `[y, wp, c, ns]` |
| 491 `fApplyAt` | `applyAt` | `[v, p, r]` |
| 492 `fModifyRun` | `modifyNth (applyRun v p rest) i` | `[v, p, rest, i, ks]` |
| 493 `fApplyRun` | `applyRun` | `[v, p, path, r]` |
| 494 `fApplyPlan` | `applyPlan` | `[v, N, Bd, path, p, t]` |

`applyPlan v N Bd path p t = (applyRun v p path (analyze Bd t)).toRT`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Lax117284Proofs.Treewidth.Fun
namespace E5C3

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5 E5A E5C1 E5C2

abbrev fAttCut : ℕ := 490
abbrev fApplyAt : ℕ := 491
abbrev fModifyRun : ℕ := 492
abbrev fApplyRun : ℕ := 493
abbrev fApplyPlan : ℕ := 494

/-! ## the Lean side -/

/-- the cut of `applyAt` for an attach plan -/
def attCut (y wp : List ℕ) (c : Option CT.Cut) (ns : List CNode) : List CNode × ℕ :=
  match c with
  | none => (ns, ns.length - 1)
  | some ct => cutAt y wp ct ns

theorem applyAt_att (v : ℕ) (c : Option CT.Cut) (chain : List (Finset ℕ)) (M S : Finset ℕ) (ns : List CNode)
    (ks : List AR) :
    applyAt v (.att c chain M) (.run S ns ks) =
      .run S (addJunk (attCut (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card)))
          (witnesses (ns.map (fun n => n.bag.card))) c ns).2 (branchRT v chain M)
        (attCut (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card)))
          (witnesses (ns.map (fun n => n.bag.card))) c ns).1) ks := by
  cases c <;> simp only [applyAt, attCut]

/-- weight of a plan -/
def wnP : CT.Plan → ℕ
  | .att _ _ _ => 1
  | .top _ w => wn w

/-- local cost of `applyAt` -/
def cAA (s : ℕ) (p : CT.Plan) : ℕ := cPR s * wnP p + 100 * (sz p + 1)

/-- size growth constant of a plan -/
def gP (p : CT.Plan) : ℕ := 18 * sz p + 11

/-! ## the terms -/

/-- `[y, wp, c, ns]` -/
def attCutTm : Tm :=
  .ite (.isNat (V 2))
    (.cons (V 3) (.sub (.call fLength [V 3]) (.lit 1)))
    (.call fCutAt [V 0, V 1, .snd (V 2), V 3])

/-- `[v, p, r]` -/
def applyAtTm : Tm :=
  .ite (.eq (.fst (V 1)) (.lit 1))
    (.letE (.call fCards [.fst (.snd (V 2))])
      (.letE (.call E1A.fTypical [V 0])
        (.letE (.call E1B.fWitnesses [V 1])
          (.letE (.call fAttCut [V 1, V 0, .fst (.snd (V 4)), .fst (.snd (V 5))])
            (.cons (.fst (V 6))
              (.cons (.call fAddJunk [.snd (V 0),
                        .call fBranchRT [V 4, .fst (.snd (.snd (V 5))), .snd (.snd (.snd (V 5)))], .fst (V 0)])
                (.snd (.snd (V 6)))))))))
    (.call fProcessRun [V 0, .fst (.snd (V 1)), .snd (.snd (V 1)), V 2])

/-- `[v, p, rest, i, ks]` -/
def modifyRunTm : Tm :=
  .ite (.isNat (V 4)) (V 4)
    (.ite (.eq (V 3) (.lit 0))
      (.cons (.call fApplyRun [V 0, V 1, V 2, .fst (V 4)]) (.snd (V 4)))
      (.cons (.fst (V 4)) (.call fModifyRun [V 0, V 1, V 2, .sub (V 3) (.lit 1), .snd (V 4)])))

/-- `[v, p, path, r]` -/
def applyRunTm : Tm :=
  .ite (.isNat (V 2)) (.call fApplyAt [V 0, V 1, V 3])
    (.cons (.fst (V 3))
      (.cons (.fst (.snd (V 3)))
        (.call fModifyRun [V 0, V 1, .snd (V 2), .fst (V 2), .snd (.snd (V 3))])))

/-- `[v, N, Bd, path, p, t]` -/
def applyPlanTm : Tm :=
  .call E5A.fToRT [.call fApplyRun [V 0, V 4, V 3, .call E5B.fAnalyze [V 2, V 5]]]

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 490 => some attCutTm | 491 => some applyAtTm | 492 => some modifyRunTm | 493 => some applyRunTm
  | 494 => some applyPlanTm | _ => none

def Δ : ℕ → Option Tm := layerΔ E5C2.Δ 490 tbl

abbrev size : ℕ := 495

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 495 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h490 : 490 ≤ f := by omega
    simp only [h490, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem ext2 : E5C2.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E5C2.Δ_lt h; simp [E5C2.size] at this; omega)
theorem ext1 : E5C1.Δ ⊑ Δ := Ext.trans E5C2.ext1 ext2
theorem extB : E5B.Δ ⊑ Δ := Ext.trans E5C2.extB ext2
theorem extA : E5A.Δ ⊑ Δ := Ext.trans E5C2.extA ext2
theorem extE1 : E1.e1Δ ⊑ Δ := Ext.trans E5C2.extE1 ext2

theorem Δ_attCut : Δ fAttCut = some attCutTm := by
  simp [Δ, layerΔ_ge tbl (show 490 ≤ fAttCut by decide)]; rfl
theorem Δ_applyAt : Δ fApplyAt = some applyAtTm := by
  simp [Δ, layerΔ_ge tbl (show 490 ≤ fApplyAt by decide)]; rfl
theorem Δ_modifyRun : Δ fModifyRun = some modifyRunTm := by
  simp [Δ, layerΔ_ge tbl (show 490 ≤ fModifyRun by decide)]; rfl
theorem Δ_applyRun : Δ fApplyRun = some applyRunTm := by
  simp [Δ, layerΔ_ge tbl (show 490 ≤ fApplyRun by decide)]; rfl
theorem Δ_applyPlan : Δ fApplyPlan = some applyPlanTm := by
  simp [Δ, layerΔ_ge tbl (show 490 ≤ fApplyPlan by decide)]; rfl

/-! ## sizes -/

theorem sz_attCut_le (y wp : List ℕ) (c : Option CT.Cut) (ns : List CNode) :
    sz (attCut y wp c ns).1 ≤ 2 * sz ns + 3 := by
  cases c with
  | none => simp only [attCut]; omega
  | some ct => simp only [attCut]; exact sz_cutAt_le y wp ct ns

theorem sz_applyAt_le (v : ℕ) (p : CT.Plan) (r : AR) : sz (applyAt v p r) ≤ 8 * sz r + gP p := by
  cases p with
  | att c chain M =>
    obtain ⟨S, ns, ks⟩ := r
    rw [applyAt_att]
    have h1 := sz_attCut_le (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card)))
      (witnesses (ns.map (fun n => n.bag.card))) c ns
    have h2 := sz_addJunk_le (attCut (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card)))
      (witnesses (ns.map (fun n => n.bag.card))) c ns).2 (branchRT v chain M)
      (attCut (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card)))
      (witnesses (ns.map (fun n => n.bag.card))) c ns).1
    have h3 := sz_branchRT_le v chain M
    have h4 : sz (CT.Plan.att c chain M) = sz c + sz chain + sz M + 4 := sz_plan_att c chain M
    simp only [gP, sz_ar]
    omega
  | top pre w =>
    have h1 := sz_processRun_le v pre w r
    have h2 := wn_le_sz w
    have h4 : sz (CT.Plan.top pre w) = sz pre + sz w + 3 := sz_plan_top pre w
    simp only [applyAt, gP]
    omega

theorem sz_modifyNth_le (f : AR → AR) (G : ℕ) (hf : ∀ x, sz (f x) ≤ 8 * sz x + G) :
    ∀ (i : ℕ) (l : List AR), sz (modifyNth f i l) ≤ 8 * sz l + G
  | _, [] => by simp only [modifyNth]; omega
  | 0, a :: l => by
    have := hf a
    simp only [modifyNth, sz_cons]; omega
  | i + 1, a :: l => by
    have := sz_modifyNth_le f G hf i l
    simp only [modifyNth, sz_cons]; omega

theorem sz_applyRun_le (v : ℕ) (p : CT.Plan) : ∀ (path : List ℕ) (r : AR), sz (applyRun v p path r) ≤ 8 * sz r + gP p
  | [], r => by simp only [applyRun]; exact sz_applyAt_le v p r
  | i :: rest, .run S ns ks => by
    have := sz_modifyNth_le (applyRun v p rest) (gP p) (fun x => sz_applyRun_le v p rest x) i ks
    simp only [applyRun, sz_ar]
    omega

/-! ## the lemmas -/

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem attCut_runs (y wp : List ℕ) (c : Option CT.Cut) (ns : List CNode) (s : ℕ) (hy : y.length ≤ s)
    (hwp : wp.length ≤ s) (hns : sz ns ≤ s) (hB : 3000 + 400 * (s + 1) < B) :
    Runs Δ' B fAttCut [toVal y, toVal wp, toVal c, toVal ns] (toVal (attCut y wp c ns)) (100 * s + 460) := by
  have hE1 := Ext.trans extE1 hΔ
  have hlen := length_le_sz ns
  have hkc : fCutAt < B := lt_of_bnd hB (by decide)
  cases c with
  | none =>
    have h1 := Lib1.length_runs (l1 hE1) B ns (by omega)
    refine Runs.mk (hΔ _ _ Δ_attCut) ?_
    simp only [attCut, toVal_pair, toVal_none]
    ev_start
    · ev_run
    · omega
  | some ct =>
    have h1 := cutAt_runs (Ext.trans ext1 hΔ) B y wp ct ns s hy hwp hns (by omega)
    refine Runs.mk (hΔ _ _ Δ_attCut) ?_
    simp only [attCut, toVal_some]
    ev_start
    · ev_run
    · omega

theorem applyAt_runs (s : ℕ) (hB : 3000 + 400 * (8 * s + 16) < B) (v : ℕ) (p : CT.Plan) (r : AR)
    (hr : sz r ≤ s) (hp : sz p ≤ s) :
    Runs Δ' B fApplyAt [toVal v, toVal p, toVal r] (toVal (applyAt v p r)) (cAA s p + 20) := by
  have hE1 := Ext.trans extE1 hΔ
  have hΔA : E5A.Δ ⊑ Δ' := Ext.trans extA hΔ
  have hB2 : 3000 + 400 * (s + 1) < B := by omega
  have hB1 : 1 < B := by omega
  cases p with
  | top pre w =>
    have h4 : sz (CT.Plan.top pre w) = sz pre + sz w + 3 := sz_plan_top pre w
    have hw := wn_le_sz w
    have h1 := processRun_runs (Ext.trans ext2 hΔ) B s hB v pre w r hr
    have hk : fProcessRun < B := lt_of_bnd hB2 (by decide)
    refine Runs.mk (hΔ _ _ Δ_applyAt) ?_
    simp only [applyAt, toVal_plan_top]
    ev_start
    · ev_run
    · unfold cAA; simp only [wnP]; omega
  | att c chain M =>
    obtain ⟨S, ns, ks⟩ := r
    have hns : sz ns ≤ s := by have := sz_c_lt S ns ks; omega
    have hlen := length_le_sz ns
    have hc4 := sz_chain_ge ns
    have h4 : sz (CT.Plan.att c chain M) = sz c + sz chain + sz M + 4 := sz_plan_att c chain M
    rw [applyAt_att]
    generalize hsizes : ns.map (fun n => n.bag.card) = sizes
    have hsl : sizes.length = ns.length := by rw [← hsizes]; simp
    have hy : (Lax117284Proofs.Treewidth.Seq.typical sizes).length ≤ s := le_trans (E5.typical_length_le sizes) (by omega)
    have hwpl : (witnesses sizes).length ≤ s := le_trans (length_witnesses_le sizes) (by omega)
    have hcards := cards_runs (Ext.trans extA hΔ) B ns (by omega)
    rw [hsizes] at hcards
    have htyp := E1A.typical_runs (eA hE1) B hB1 sizes
    have hwit := E1B.witnesses_runs (eB hE1) B sizes (by omega)
    have hatt := attCut_runs hΔ B (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) c ns s hy hwpl hns hB2
    have hSz := sz_attCut_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) c ns
    generalize hat' : attCut (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) c ns = cr at hatt hSz ⊢
    have hbr := E5C1.branchRT_runs (Ext.trans ext1 hΔ) B v chain M (by omega)
    have hadd := E5C1.addJunk_runs (Ext.trans ext1 hΔ) B cr.2 (branchRT v chain M) cr.1 (by omega)
    have hk1 : fCards < B := lt_of_bnd hB2 (by decide)
    have hk2 : fAttCut < B := lt_of_bnd hB2 (by decide)
    have hk3 : fAddJunk < B := lt_of_bnd hB2 (by decide)
    have hk4 : fBranchRT < B := lt_of_bnd hB2 (by decide)
    have hT : (sizes.length + 1) ^ 3 ≤ (s + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hT1 : s + 1 ≤ (s + 1) ^ 3 := le_pw (by omega) (by omega)
    have hcp : cPR s = 3000 * (s + 1) ^ 3 := rfl
    refine Runs.mk (hΔ _ _ Δ_applyAt) ?_
    simp only [toVal_plan_att, toVal_ar]
    ev_start
    · ev_run
    · unfold cAA; simp only [wnP]; omega

theorem applyRun_runs (s : ℕ) (hB : 3000 + 400 * (8 * s + 16) < B) (v : ℕ) (p : CT.Plan) (hp : sz p ≤ s) :
    ∀ (path : List ℕ) (r : AR), sz r ≤ s →
    Runs Δ' B fApplyRun [toVal v, toVal p, toVal path, toVal r] (toVal (applyRun v p path r))
      (path.length * (20 * s + 60) + cAA s p + 40)
  | [], r, hr => by
    have h1 := applyAt_runs hΔ B s hB v p r hr hp
    have hB2 : 3000 + 400 * (s + 1) < B := by omega
    have hk : fApplyAt < B := lt_of_bnd hB2 (by decide)
    refine Runs.mk (hΔ _ _ Δ_applyRun) ?_
    simp only [applyRun, toVal_nil, List.length_nil]
    ev_start
    · ev_run
    · omega
  | i :: rest, .run S ns ks, hr => by
    have ih := applyRun_runs s hB v p hp rest
    have hks : sz ks ≤ s := by have := sz_ks_lt S ns ks; omega
    have hB2 : 3000 + 400 * (s + 1) < B := by omega
    have hk1 : fModifyRun < B := lt_of_bnd hB2 (by decide)
    have hk2 : fApplyRun < B := lt_of_bnd hB2 (by decide)
    have hmod : ∀ (l : List AR) (i : ℕ), sz l ≤ s →
        Runs Δ' B fModifyRun [toVal v, toVal p, toVal rest, toVal i, toVal l]
          (toVal (modifyNth (applyRun v p rest) i l))
          (20 * l.length + 20 + (rest.length * (20 * s + 60) + cAA s p + 40)) := by
      intro l
      induction l with
      | nil =>
        intro i _
        refine Runs.mk (hΔ _ _ Δ_modifyRun) ?_
        simp only [modifyNth]
        ev_start
        · ev_run
        · omega
      | cons k l ihl =>
        intro i hl
        have hk : sz k ≤ s := by have := sz_head_lt k l; omega
        have hl' : sz l ≤ s := by have := sz_tail_lt k l; omega
        refine Runs.mk (hΔ _ _ Δ_modifyRun) ?_
        cases i with
        | zero =>
          have h1 := ih k hk
          simp only [modifyNth, toVal_cons]
          ev_start
          · ev_run
          · simp only [List.length_cons]; omega
        | succ i =>
          have h1 := ihl i hl'
          simp only [modifyNth, toVal_cons]
          ev_start
          · ev_run
          · simp only [List.length_cons]; omega
    have h1 := hmod ks i hks
    have hl := length_le_sz ks
    have e : (rest.length + 1) * (20 * s + 60) = rest.length * (20 * s + 60) + (20 * s + 60) := by ring
    refine Runs.mk (hΔ _ _ Δ_applyRun) ?_
    simp only [applyRun, toVal_ar, toVal_cons, List.length_cons]
    ev_start
    · ev_run
    · rw [e]; omega

omit hΔ in
theorem wnP_le_sz (p : CT.Plan) : wnP p ≤ sz p := by
  cases p with
  | att c chain M => simp only [wnP]; have := sz_pos (CT.Plan.att c chain M); omega
  | top pre w =>
    have := wn_le_sz w
    have h4 : sz (CT.Plan.top pre w) = sz pre + sz w + 3 := sz_plan_top pre w
    simp only [wnP]; omega

/-- cost of `applyPlan` (`ck6 = E.cKey (6 s)`) -/
def cApplyPlan (s ck6 : ℕ) : ℕ :=
  E5B.cA s ck6 * s + s * (100 * s + 60) + (cPR (5 * s) * s + 100 * (s + 1) + 40) +
    100 * (58 * s + 11 + 1) * (58 * s + 11) + 100

theorem applyPlan_runs (E : Ext5 Δ') (v : ℕ) (N Bd : Finset ℕ) (path : List ℕ) (p : CT.Plan) (t : RT) (s : ℕ)
    (hBd : sz Bd ≤ s) (ht : sz t ≤ s) (hp : sz p ≤ s) (hpath : path.length ≤ s)
    (hB : 20000 + 20000 * (s + 1) + E.cKey (6 * s) < B) :
    Runs Δ' B fApplyPlan [toVal v, toVal N, toVal Bd, toVal path, toVal p, toVal t]
      (toVal (applyPlan v N Bd path p t)) (cApplyPlan s (E.cKey (6 * s))) := by
  have hana := E5B.analyze_runs (Ext.trans extB hΔ) B E Bd s hBd (by omega) t ht
  have hsa : sz (analyze Bd t) ≤ 5 * s := le_trans (E5B.sz_analyze_le Bd t) (by omega)
  have hrun := applyRun_runs hΔ B (5 * s) (by omega) v p (by omega) path (analyze Bd t) hsa
  have hszr := sz_applyRun_le v p path (analyze Bd t)
  have hszr' : sz (applyRun v p path (analyze Bd t)) ≤ 58 * s + 11 := by
    simp only [gP] at hszr; omega
  have hrt := E5A.toRT_runs (Ext.trans extA hΔ) B (58 * s + 11) (by omega) (applyRun v p path (analyze Bd t)) hszr'
  have hcnt := cnt_le_sz (applyRun v p path (analyze Bd t))
  have t1 : E5B.cA s (E.cKey (6 * s)) * t.size ≤ E5B.cA s (E.cKey (6 * s)) * s :=
    Nat.mul_le_mul_left _ (le_trans (size_le_sz t) ht)
  have t2 : path.length * (20 * (5 * s) + 60) ≤ s * (100 * s + 60) := by
    calc path.length * (20 * (5 * s) + 60) ≤ s * (20 * (5 * s) + 60) := Nat.mul_le_mul_right _ hpath
      _ = s * (100 * s + 60) := by ring
  have t3 : cAA (5 * s) p ≤ cPR (5 * s) * s + 100 * (s + 1) := by
    unfold cAA
    have := wnP_le_sz p
    have : cPR (5 * s) * wnP p ≤ cPR (5 * s) * s := Nat.mul_le_mul_left _ (by omega)
    omega
  have t4 : 100 * (58 * s + 11 + 1) * cnt (applyRun v p path (analyze Bd t)) ≤
      100 * (58 * s + 11 + 1) * (58 * s + 11) := Nat.mul_le_mul_left _ (by omega)
  have hB2 : 3000 + 400 * (s + 1) < B := by omega
  have hk1 : fApplyRun < B := lt_of_bnd hB2 (by decide)
  have hk2 : E5B.fAnalyze < B := lt_of_bnd hB2 (by decide)
  have hk3 : E5A.fToRT < B := lt_of_bnd hB2 (by decide)
  refine Runs.mk (hΔ _ _ Δ_applyPlan) ?_
  simp only [applyPlan]
  ev_start
  · ev_run
  · unfold cApplyPlan
    omega

end proofs
end E5C3
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E5R` -/

section
/-!
# WP E5 (layer R): `realIntro`

Ids `500 …`:

| id | function | arguments |
|---|---|---|
| 500 `fEntLeY` | `decide (y.foldr max 0 ≤ kmax)` | `[kmax, y]` |
| 501 `fEntLeL` | `decide (CT.maxEntryL ks ≤ kmax)` | `[kmax, ks]` |
| 502 `fEntLe` | `decide (c.maxEntry ≤ kmax)` | `[kmax, c]` |
| 503 `fPredIntro` | the predicate of `realIntro`'s `find?` (context `(target, kmax)`) | `[ctx, r]` |
| 504 `fRealIntro` | `realIntro` (the id of `introPlans` is the first argument) | `[ip, kmax, v, N, Bd, t, target]` |
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Lax117284Proofs.Treewidth.Fun
namespace E5R

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5 E5A E5C1 E5C2 E5C3

abbrev fEntLeY : ℕ := 500
abbrev fEntLeL : ℕ := 501
abbrev fEntLe : ℕ := 502
abbrev fPredIntro : ℕ := 503
abbrev fRealIntro : ℕ := 504

/-- the predicate of `realIntro` -/
abbrev predI (kmax : ℕ) (target : CT) : List ℕ × CT.Plan × CT → Bool :=
  fun r => CT.domCB (CT.norm r.2.2) target && decide ((CT.norm r.2.2).maxEntry ≤ kmax)

/-! ## the terms -/

def entLeYTm : Tm :=
  .ite (.isNat (V 1)) (.lit 1) (.mul (E5C1.leT (.fst (V 1)) (V 0)) (.call fEntLeY [V 0, .snd (V 1)]))

def entLeLTm : Tm :=
  .ite (.isNat (V 1)) (.lit 1) (.mul (.call fEntLe [V 0, .fst (V 1)]) (.call fEntLeL [V 0, .snd (V 1)]))

def entLeTm : Tm :=
  .mul (.call fEntLeY [V 0, .fst (.snd (V 1))]) (.call fEntLeL [V 0, .snd (.snd (V 1))])

def predIntroTm : Tm :=
  .letE (.call idNorm [.snd (.snd (V 1))])
    (.mul (.call idDomC [V 0, .fst (V 1)]) (.call fEntLe [.snd (V 1), V 0]))

def realIntroTm : Tm :=
  .letE (.callv (V 0) [V 2, V 3, .call fChar [V 4, V 5]])
    (.letE (.call Lib4.fFind [.lit fPredIntro, .cons (V 7) (V 2), V 0])
      (.ite (.isNat (V 0)) (.lit 0)
        (.cons (.lit 1)
          (.call fApplyPlan [V 4, V 5, V 6, .fst (.snd (V 0)), .fst (.snd (.snd (V 0))), V 7]))))

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 500 => some entLeYTm | 501 => some entLeLTm | 502 => some entLeTm | 503 => some predIntroTm
  | 504 => some realIntroTm | _ => none

def Δ : ℕ → Option Tm := layerΔ E5C3.Δ 500 tbl

abbrev size : ℕ := 505

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 505 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h500 : 500 ≤ f := by omega
    simp only [h500, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem ext3 : E5C3.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E5C3.Δ_lt h; simp [E5C3.size] at this; omega)
theorem extB : E5B.Δ ⊑ Δ := Ext.trans E5C3.extB ext3
theorem extA : E5A.Δ ⊑ Δ := Ext.trans E5C3.extA ext3
theorem extE1 : E1.e1Δ ⊑ Δ := Ext.trans E5C3.extE1 ext3

theorem Δ_entLeY : Δ fEntLeY = some entLeYTm := by
  simp [Δ, layerΔ_ge tbl (show 500 ≤ fEntLeY by decide)]; rfl
theorem Δ_entLeL : Δ fEntLeL = some entLeLTm := by
  simp [Δ, layerΔ_ge tbl (show 500 ≤ fEntLeL by decide)]; rfl
theorem Δ_entLe : Δ fEntLe = some entLeTm := by
  simp [Δ, layerΔ_ge tbl (show 500 ≤ fEntLe by decide)]; rfl
theorem Δ_predIntro : Δ fPredIntro = some predIntroTm := by
  simp [Δ, layerΔ_ge tbl (show 500 ≤ fPredIntro by decide)]; rfl
theorem Δ_realIntro : Δ fRealIntro = some realIntroTm := by
  simp [Δ, layerΔ_ge tbl (show 500 ≤ fRealIntro by decide)]; rfl

/-! ## `maxEntry ≤ kmax` -/

theorem sz_ct_ks_lt (S : Finset ℕ) (y : List ℕ) (ks : List CT) : sz ks < sz (CT.node S y ks) := by
  rw [sz_ct_node]; have := sz_pos S; have := sz_pos y; omega
theorem sz_ct_y_lt (S : Finset ℕ) (y : List ℕ) (ks : List CT) : sz y < sz (CT.node S y ks) := by
  rw [sz_ct_node]; have := sz_pos S; have := sz_pos ks; omega

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem entLeY_runs (kmax : ℕ) (hB : 1 < B) : ∀ y : List ℕ,
    Runs Δ' B fEntLeY [toVal kmax, toVal y] (toVal (decide (y.foldr max 0 ≤ kmax))) (20 * y.length + 10)
  | [] => by
    refine Runs.mk (hΔ _ _ Δ_entLeY) ?_
    simp only [List.foldr_nil, Nat.zero_le, decide_true]
    ev_start
    · ev_run
    · simp
  | a :: y => by
    have ih := entLeY_runs kmax hB y
    refine Runs.mk (hΔ _ _ Δ_entLeY) ?_
    by_cases h1 : a ≤ kmax <;> by_cases h2 : y.foldr max 0 ≤ kmax
    · have e : decide ((a :: y).foldr max 0 ≤ kmax) = true := by simp [List.foldr_cons, h1, h2]
      rw [e]; simp only [h2, decide_true] at ih
      have h1' : ¬ kmax < a := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1']; done) | (simp [h1']; omega))
      · simp only [List.length_cons]; omega
    · have e : decide ((a :: y).foldr max 0 ≤ kmax) = false := by simp [List.foldr_cons, h1, h2]
      rw [e]; simp only [h2, decide_false] at ih
      have h1' : ¬ kmax < a := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1']; done) | (simp [h1']; omega))
      · simp only [List.length_cons]; omega
    · have e : decide ((a :: y).foldr max 0 ≤ kmax) = false := by simp [List.foldr_cons, h1, h2]
      rw [e]; simp only [h2] at ih
      have h1' : kmax < a := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1']; done) | (simp [h1']; omega))
      · simp only [List.length_cons]; omega
    · have e : decide ((a :: y).foldr max 0 ≤ kmax) = false := by simp [List.foldr_cons, h1, h2]
      rw [e]; simp only [h2] at ih
      have h1' : kmax < a := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1']; done) | (simp [h1']; omega))
      · simp only [List.length_cons]; omega

mutual
theorem entLe_runs_rec (kmax : ℕ) (hB : 1 < B) (hk : fEntLe < B) : ∀ c : CT,
    Runs Δ' B fEntLe [toVal kmax, toVal c] (toVal (decide (c.maxEntry ≤ kmax))) (30 * sz c + 10)
  | .node S y ks => by
    have h1 := entLeY_runs hΔ B kmax hB y
    have h2 := entLeL_runs_rec kmax hB hk ks
    have hkl : fEntLeL < B := by
      have : fEntLeL < fEntLe := by decide
      omega
    have hky : fEntLeY < B := by
      have : fEntLeY < fEntLe := by decide
      omega
    have hy := length_le_sz y
    have hs := sz_ct_node S y ks
    have hyv := sz_pos y
    refine Runs.mk (hΔ _ _ Δ_entLe) ?_
    simp only [toVal_ct]
    have e : decide ((CT.node S y ks).maxEntry ≤ kmax) =
        (decide (y.foldr max 0 ≤ kmax) && decide (CT.maxEntryL ks ≤ kmax)) := by
      simp only [CT.maxEntry, max_le_iff, Bool.decide_and]
    rw [e]
    by_cases a1 : y.foldr max 0 ≤ kmax <;> by_cases a2 : CT.maxEntryL ks ≤ kmax
    · simp only [a1, a2, decide_true] at h1 h2 ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · have := sz_pos S; omega
    · simp only [a1, a2, decide_true, decide_false] at h1 h2 ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · have := sz_pos S; omega
    · simp only [a1, a2, decide_true, decide_false] at h1 h2 ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · have := sz_pos S; omega
    · simp only [a1, a2, decide_true, decide_false] at h1 h2 ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · have := sz_pos S; omega
theorem entLeL_runs_rec (kmax : ℕ) (hB : 1 < B) (hk : fEntLe < B) : ∀ ks : List CT,
    Runs Δ' B fEntLeL [toVal kmax, toVal ks] (toVal (decide (CT.maxEntryL ks ≤ kmax))) (30 * sz ks + 10)
  | [] => by
    refine Runs.mk (hΔ _ _ Δ_entLeL) ?_
    simp only [CT.maxEntryL, Nat.zero_le, decide_true]
    ev_start
    · ev_run
    · simp
  | k :: ks => by
    have h1 := entLe_runs_rec kmax hB hk k
    have h2 := entLeL_runs_rec kmax hB hk ks
    have hkc : fEntLeL < B := by
      have : fEntLeL < fEntLe := by decide
      omega
    refine Runs.mk (hΔ _ _ Δ_entLeL) ?_
    have e : decide (CT.maxEntryL (k :: ks) ≤ kmax) =
        (decide (k.maxEntry ≤ kmax) && decide (CT.maxEntryL ks ≤ kmax)) := by
      simp only [CT.maxEntryL, max_le_iff, Bool.decide_and]
    rw [e]
    simp only [toVal_cons, sz_cons]
    by_cases a1 : k.maxEntry ≤ kmax <;> by_cases a2 : CT.maxEntryL ks ≤ kmax
    · simp only [a1, a2, decide_true] at h1 h2 ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
    · simp only [a1, a2, decide_true, decide_false] at h1 h2 ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
    · simp only [a1, a2, decide_true, decide_false] at h1 h2 ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
    · simp only [a1, a2, decide_true, decide_false] at h1 h2 ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
end

end proofs

theorem entLe_runs_pair : (type_of% @entLe_runs_rec) ∧ (type_of% @entLeL_runs_rec) :=
  ⟨@entLe_runs_rec, @entLeL_runs_rec⟩

theorem entLe_runs : type_of% @entLe_runs_rec := entLe_runs_pair.1

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

omit hΔ in
theorem sz_plan_res_le (r : List ℕ × CT.Plan × CT) : sz r.2.2 ≤ sz r ∧ sz r.1 ≤ sz r ∧ sz r.2.1 ≤ sz r := by
  obtain ⟨a, b, c⟩ := r
  simp only [sz_pair]
  omega

/-- cost of the predicate of `realIntro` -/
def cPredI (cnorm cdom s : ℕ) : ℕ := cnorm + cdom + 30 * s + 100

theorem predIntro_runs (E : Ext5 Δ') (kmax : ℕ) (target : CT) (r : List ℕ × CT.Plan × CT) (s : ℕ)
    (hr : sz r ≤ s) (htg : sz target ≤ s) (hPD : E.PD s (CT.norm r.2.2) target) (hB : 1000 + 100 * (s + 1) + E.cNorm s + E.cDom s < B) :
    Runs Δ' B fPredIntro [toVal (target, kmax), toVal r] (toVal (predI kmax target r))
      (cPredI (E.cNorm s) (E.cDom s) s) := by
  have hr' := (sz_plan_res_le r).1
  have hn := E.norm B s r.2.2 (by omega) (by omega)
  have hnsz := E.norm_sz r.2.2
  have hd := E.domC B s (CT.norm r.2.2) target hPD (by omega) htg (by omega)
  have hk : fEntLe < B := by
    have : fEntLe < 1000 := by decide
    omega
  have he := entLe_runs hΔ B kmax (by omega) hk (CT.norm r.2.2)
  have hsz := sz_pos (CT.norm r.2.2)
  refine Runs.mk (hΔ _ _ Δ_predIntro) ?_
  by_cases a1 : CT.domCB (CT.norm r.2.2) target = true <;> by_cases a2 : (CT.norm r.2.2).maxEntry ≤ kmax
  · have e : predI kmax target r = true := by simp [predI, a1, a2]
    rw [e]
    simp only [a1, a2, decide_true] at hd he
    ev_start
    · ev_run
      all_goals (first | omega | (simp; done) | (simp; omega))
    · unfold cPredI; omega
  · have e : predI kmax target r = false := by simp [predI, a1, a2]
    rw [e]
    simp only [a1, a2, decide_true, decide_false] at hd he
    ev_start
    · ev_run
      all_goals (first | omega | (simp; done) | (simp; omega))
    · unfold cPredI; omega
  · have e : predI kmax target r = false := by simp [predI, a1, a2]
    rw [e]
    simp only [Bool.not_eq_true] at a1
    simp only [a1, a2, decide_true, decide_false] at hd he
    ev_start
    · ev_run
      all_goals (first | omega | (simp; done) | (simp; omega))
    · unfold cPredI; omega
  · have e : predI kmax target r = false := by simp [predI, a1, a2]
    rw [e]
    simp only [Bool.not_eq_true] at a1
    simp only [a1, a2, decide_true, decide_false] at hd he
    ev_start
    · ev_run
      all_goals (first | omega | (simp; done) | (simp; omega))
    · unfold cPredI; omega

/-- cost of `realIntro` -/
def cRealIntro (s L cnorm5 cnorm cdom ck6 cip : ℕ) : ℕ :=
  (200 * (s + 1) * s + cnorm5 + 8) + cip + (24 * L + 6 + L * cPredI cnorm cdom s) + cApplyPlan s ck6 + 100

theorem realIntro_runs (E : Ext5 Δ') (X : ExtIP Δ') (kmax v : ℕ) (N Bd : Finset ℕ) (t : RT) (target : CT)
    (s L : ℕ) (hBd : sz Bd ≤ s) (ht : sz t ≤ s) (htg : sz target ≤ s)
    (hPIP : X.PIP v N (t.char Bd)) (hLen : (CT.introPlans v N (t.char Bd)).length ≤ L)
    (hplans : ∀ r ∈ CT.introPlans v N (t.char Bd), sz r ≤ s)
    (hPD : ∀ r ∈ CT.introPlans v N (t.char Bd), E.PD s (CT.norm r.2.2) target)
    (hB : 20000 + 20000 * (s + 1) + E.cKey (6 * s) + E.cNorm (5 * s) + E.cNorm s + E.cDom s +
      X.cIP v N (t.char Bd) < B) :
    Runs Δ' B fRealIntro [Val.nat X.ip, toVal kmax, toVal v, toVal N, toVal Bd, toVal t, toVal target]
      (toVal (realIntro kmax v N Bd t target))
      (cRealIntro s L (E.cNorm (5 * s)) (E.cNorm s) (E.cDom s) (E.cKey (6 * s)) (X.cIP v N (t.char Bd))) := by
  have hE1 := Ext.trans extE1 hΔ
  have hch := E5A.char_runs (Ext.trans extA hΔ) B E Bd t s ht hBd (by omega)
  have hip := X.introPlans B v N (t.char Bd) hPIP (by omega)
  have hfind := Lib4.find_runs (l4 hE1) B fPredIntro (toVal (target, kmax)) (predI kmax target)
    (fun _ => cPredI (E.cNorm s) (E.cDom s) s) (CT.introPlans v N (t.char Bd))
    (fun r hr => predIntro_runs hΔ B E kmax target r s (hplans r hr) htg (hPD r hr) (by omega)) (by omega)
  simp only [E5.sum_map_const] at hfind
  have hmul : (CT.introPlans v N (t.char Bd)).length * cPredI (E.cNorm s) (E.cDom s) s ≤
      L * cPredI (E.cNorm s) (E.cDom s) s := Nat.mul_le_mul_right _ hLen
  have hts : 200 * (s + 1) * t.size ≤ 200 * (s + 1) * s := Nat.mul_le_mul_left _ (le_trans (size_le_sz t) ht)
  have hB2 : 3000 + 400 * (s + 1) < B := by omega
  have hk1 : fChar < B := lt_of_bnd hB2 (by decide)
  have hk2 : fPredIntro < B := lt_of_bnd hB2 (by decide)
  have hk3 : fApplyPlan < B := lt_of_bnd hB2 (by decide)
  have hk4 : Lib4.fFind < B := lt_of_bnd hB2 (by decide)
  have hgoal : realIntro kmax v N Bd t target =
      ((CT.introPlans v N (t.char Bd)).find? (predI kmax target)).map (fun r => applyPlan v N Bd r.1 r.2.1 t) := rfl
  rw [hgoal]
  rcases hf : (CT.introPlans v N (t.char Bd)).find? (predI kmax target) with _ | r
  · rw [hf] at hfind
    refine Runs.mk (hΔ _ _ Δ_realIntro) ?_
    simp only [Option.map_none]
    ev_start
    · ev_run
    · unfold cRealIntro; omega
  · rw [hf] at hfind
    have hrmem : r ∈ CT.introPlans v N (t.char Bd) := List.mem_of_find?_eq_some hf
    have hr1 := hplans r hrmem
    have hs := sz_plan_res_le r
    have hpath := length_le_sz r.1
    have hap := applyPlan_runs (Ext.trans ext3 hΔ) B E v N Bd r.1 r.2.1 t s hBd ht (by omega) (by omega) (by omega)
    refine Runs.mk (hΔ _ _ Δ_realIntro) ?_
    simp only [Option.map_some, toVal_some]
    ev_start
    · ev_run
    · unfold cRealIntro; omega

end proofs
end E5R
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E5D` -/

section
/-!
# WP E5 (layer D): `mergeChain`, `mergeAR`, `mergeKids`, `mergeReal`, `realJoin`

Ids `520 …`:

| id | function | arguments |
|---|---|---|
| 520 `fMergeChain` | `mergeChain` | `[na, nb, prev, path]` |
| 521 `fMergeAR` | `mergeAR` | `[a, b, target]` |
| 522 `fMergeKids` | `mergeKids` | `[ka, kb, tk]` |
| 523 `fMergeReal` | `mergeReal` | `[Bd, ta, tb, target]` |
| 524 `fPredJoin` | the predicate `fun d => domCB d target` of `realJoin` (context `target`) | `[target, d]` |
| 525 `fRealJoin` | `realJoin` | `[kmax, Bd, ta, tb, target]` |
| 526 `fFlagI` / 527 `fFlagJ` | the "first visit" flags of `mergeChain` | `[prev, i]` / `[prev, j]` |

The lattice path search is E1's `findPath` (id `E1D.fFindPath = 156`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Lax117284Proofs.Treewidth.Fun
namespace E5D

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5 E5A E5C1

abbrev fMergeChain : ℕ := 520
abbrev fMergeAR : ℕ := 521
abbrev fMergeKids : ℕ := 522
abbrev fMergeReal : ℕ := 523
abbrev fPredJoin : ℕ := 524
abbrev fRealJoin : ℕ := 525
abbrev fFlagI : ℕ := 526
abbrev fFlagJ : ℕ := 527

/-! ## the Lean side -/

/-- first visit of the `a`-side node -/
abbrev flagI (prev : Option (ℕ × ℕ)) (i : ℕ) : Bool := prev.elim true (fun p => decide (p.1 ≠ i))
/-- first visit of the `b`-side node -/
abbrev flagJ (prev : Option (ℕ × ℕ)) (j : ℕ) : Bool := prev.elim true (fun p => decide (p.2 ≠ j))

/-- the default chain node of `mergeChain` -/
abbrev dflt : CNode := ⟨∅, []⟩

theorem mergeChain_cons (na nb : List CNode) (prev : Option (ℕ × ℕ)) (i j : ℕ) (rest : List (ℕ × ℕ)) :
    mergeChain na nb prev ((i, j) :: rest) =
      ⟨(na.getD i dflt).bag ∪ (nb.getD j dflt).bag,
        (if flagI prev i then (na.getD i dflt).junk else []) ++
          (if flagJ prev j then (nb.getD j dflt).junk else [])⟩ :: mergeChain na nb (some (i, j)) rest := rfl

/-- `path` has at most `|sa| + |sb|` steps -/
theorem findPath_len {sa sb : List ℕ} {c : ℕ} {want : List ℕ} {P : List (ℕ × ℕ)}
    (h : findPath sa sb c want = some P) : P.length ≤ sa.length + sb.length := by
  unfold findPath at h
  obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.1 h
  have hm := List.mem_of_find?_eq_some hst
  have := E1D.latticeStates_path_length hm
  simpa using this

/-! ## the terms -/

/-- `[prev, i]` -/
def flagITm : Tm := .ite (.isNat (V 0)) (.lit 1) (.sub (.lit 1) (.eq (.fst (.snd (V 0))) (V 1)))
/-- `[prev, j]` -/
def flagJTm : Tm := .ite (.isNat (V 0)) (.lit 1) (.sub (.lit 1) (.eq (.snd (.snd (V 0))) (V 1)))

/-- `[na, nb, prev, path]` -/
def mergeChainTm : Tm :=
  .ite (.isNat (V 3)) (V 3)
    (.letE (.call fNthD [V 0, .fst (.fst (V 3)), .cons (.lit 0) (.lit 0)])
      (.letE (.call fNthD [V 2, .snd (.fst (V 4)), .cons (.lit 0) (.lit 0)])
        (.cons
          (.cons (.call Lib3.fUnionS [.fst (V 1), .fst (V 0)])
            (.call fAppend
              [.ite (.call fFlagI [V 4, .fst (.fst (V 5))]) (.snd (V 1)) (.lit 0),
               .ite (.call fFlagJ [V 4, .snd (.fst (V 5))]) (.snd (V 0)) (.lit 0)]))
          (.call fMergeChain [V 2, V 3, .cons (.lit 1) (.fst (V 5)), .snd (V 5)]))))

/-- `[a, b, target]` -/
def mergeARTm : Tm :=
  .letE (.call fCards [.fst (.snd (V 0))])
    (.letE (.call fCards [.fst (.snd (V 2))])
      (.letE (.call E1D.fFindPath [V 1, V 0, .call fLength [.fst (V 2)], .fst (.snd (V 4))])
        (.ite (.isNat (V 0)) (.lit 0)
          (.letE (.call fMergeKids [.snd (.snd (V 3)), .snd (.snd (V 4)), .snd (.snd (V 5))])
            (.ite (.isNat (V 0)) (.lit 0)
              (.cons (.lit 1)
                (.cons (.fst (V 4))
                  (.cons (.call fMergeChain [.fst (.snd (V 4)), .fst (.snd (V 5)), .lit 0, .snd (V 1)])
                    (.snd (V 0))))))))))

/-- `[ka, kb, tk]` -/
def mergeKidsTm : Tm :=
  .ite (.isNat (V 0))
    (.ite (.isNat (V 1)) (.ite (.isNat (V 2)) (.cons (.lit 1) (.lit 0)) (.lit 0)) (.lit 0))
    (.ite (.isNat (V 1)) (.lit 0)
      (.ite (.isNat (V 2)) (.lit 0)
        (.letE (.call fMergeAR [.fst (V 0), .fst (V 1), .fst (V 2)])
          (.ite (.isNat (V 0)) (.lit 0)
            (.letE (.call fMergeKids [.snd (V 1), .snd (V 2), .snd (V 3)])
              (.ite (.isNat (V 0)) (.lit 0)
                (.cons (.lit 1) (.cons (.snd (V 1)) (.snd (V 0))))))))))

/-- `[Bd, ta, tb, target]` -/
def mergeRealTm : Tm :=
  .letE (.call fMergeAR [.call E5B.fAnalyze [V 0, V 1], .call E5B.fAnalyze [V 0, V 2], V 3])
    (.ite (.isNat (V 0)) (.lit 0) (.cons (.lit 1) (.call E5A.fToRT [.snd (V 0)])))

/-- `[target, d]` -/
def predJoinTm : Tm := .call idDomC [V 1, V 0]

/-- `[kmax, Bd, ta, tb, target]` -/
def realJoinTm : Tm :=
  .letE (.call idJoinC [V 0, .call fChar [V 1, V 2], .call fChar [V 1, V 3]])
    (.letE (.call Lib4.fFind [.lit fPredJoin, V 5, V 0])
      (.ite (.isNat (V 0)) (.lit 0) (.call fMergeReal [V 3, V 4, V 5, .snd (V 0)])))

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 520 => some mergeChainTm | 521 => some mergeARTm | 522 => some mergeKidsTm | 523 => some mergeRealTm
  | 524 => some predJoinTm | 525 => some realJoinTm | 526 => some flagITm | 527 => some flagJTm | _ => none

def Δ : ℕ → Option Tm := layerΔ E5R.Δ 520 tbl

abbrev size : ℕ := 528

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 528 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h520 : 520 ≤ f := by omega
    simp only [h520, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem extR : E5R.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E5R.Δ_lt h; simp [E5R.size] at this; omega)
theorem extB : E5B.Δ ⊑ Δ := Ext.trans E5R.extB extR
theorem extA : E5A.Δ ⊑ Δ := Ext.trans E5R.extA extR
theorem extE1 : E1.e1Δ ⊑ Δ := Ext.trans E5R.extE1 extR

theorem Δ_mergeChain : Δ fMergeChain = some mergeChainTm := by
  simp [Δ, layerΔ_ge tbl (show 520 ≤ fMergeChain by decide)]; rfl
theorem Δ_mergeAR : Δ fMergeAR = some mergeARTm := by
  simp [Δ, layerΔ_ge tbl (show 520 ≤ fMergeAR by decide)]; rfl
theorem Δ_mergeKids : Δ fMergeKids = some mergeKidsTm := by
  simp [Δ, layerΔ_ge tbl (show 520 ≤ fMergeKids by decide)]; rfl
theorem Δ_mergeReal : Δ fMergeReal = some mergeRealTm := by
  simp [Δ, layerΔ_ge tbl (show 520 ≤ fMergeReal by decide)]; rfl
theorem Δ_predJoin : Δ fPredJoin = some predJoinTm := by
  simp [Δ, layerΔ_ge tbl (show 520 ≤ fPredJoin by decide)]; rfl
theorem Δ_realJoin : Δ fRealJoin = some realJoinTm := by
  simp [Δ, layerΔ_ge tbl (show 520 ≤ fRealJoin by decide)]; rfl
theorem Δ_flagI : Δ fFlagI = some flagITm := by
  simp [Δ, layerΔ_ge tbl (show 520 ≤ fFlagI by decide)]; rfl
theorem Δ_flagJ : Δ fFlagJ = some flagJTm := by
  simp [Δ, layerΔ_ge tbl (show 520 ≤ fFlagJ by decide)]; rfl

/-! ## sizes -/

theorem sz_dflt : sz dflt = 3 := by
  simp only [dflt, sz_cnode, sz_finset]; simp [sz_nil]

theorem sz_mergeChain_le (na nb : List CNode) : ∀ (P : List (ℕ × ℕ)) (prev : Option (ℕ × ℕ)),
    sz (mergeChain na nb prev P) ≤ P.length * (sz na + sz nb + 8) + 1
  | [], _ => by simp [mergeChain]
  | (i, j) :: rest, prev => by
    have ih := sz_mergeChain_le na nb rest (some (i, j))
    rw [mergeChain_cons]
    have h1 := sz_getD_le na i dflt
    have h2 := sz_getD_le nb j dflt
    have h3 := sz_dflt
    have hA : sz (na.getD i dflt) = sz (na.getD i dflt).bag + sz (na.getD i dflt).junk + 1 :=
      sz_cnode _ _
    have hB : sz (nb.getD j dflt) = sz (nb.getD j dflt).bag + sz (nb.getD j dflt).junk + 1 :=
      sz_cnode _ _
    have h4 := sz_union_le (na.getD i dflt).bag (nb.getD j dflt).bag
    have h5 := sz_append_le (if flagI prev i then (na.getD i dflt).junk else [])
      (if flagJ prev j then (nb.getD j dflt).junk else [])
    have h6 : sz (if flagI prev i then (na.getD i dflt).junk else []) ≤ sz (na.getD i dflt).junk := by
      split_ifs
      · exact le_refl _
      · have : sz ([] : List RT) = 1 := rfl; have := sz_pos (na.getD i dflt).junk; omega
    have h7 : sz (if flagJ prev j then (nb.getD j dflt).junk else []) ≤ sz (nb.getD j dflt).junk := by
      split_ifs
      · exact le_refl _
      · have : sz ([] : List RT) = 1 := rfl; have := sz_pos (nb.getD j dflt).junk; omega
    simp only [sz_cons, sz_cnode, List.length_cons]
    have := sz_pos (na.getD i dflt).junk
    have := sz_pos (nb.getD j dflt).junk
    nlinarith


/-! ## size of the merged analysis -/

theorem arith_merge (Yc Wl sS Y : ℕ) (hY : Yc + Wl + sS + 4 ≤ Y) :
    sS + Yc * (Yc + 8) + 3 + 9 * Wl ^ 2 ≤ 9 * Y ^ 2 := by
  nlinarith [Nat.zero_le (Yc * Wl), Nat.zero_le (Wl * sS), Nat.zero_le (Yc * sS), Nat.zero_le Yc, Nat.zero_le Wl,
    Nat.mul_le_mul hY hY, Nat.zero_le sS]

mutual
theorem sz_mergeAR_le_rec : ∀ (a b : AR) (c : CT) (r : AR), mergeAR a b c = some r →
    sz r ≤ 9 * (sz a + sz b) ^ 2
  | .run S na ka, .run S' nb kb, .node S'' ty tk, r, h => by
    simp only [mergeAR] at h
    split at h
    · simp at h
    · rename_i path hp
      obtain ⟨ks, hks, rfl⟩ := Option.map_eq_some_iff.1 h
      have h1 := sz_mergeKids_le_rec ka kb tk ks hks
      have hpl := findPath_len hp
      simp only [List.length_map] at hpl
      have h2 := sz_mergeChain_le na nb path none
      have h3 := sz_chain_ge na
      have h4 := sz_chain_ge nb
      have hpc : path.length * (sz na + sz nb + 8) ≤ (sz na + sz nb) * (sz na + sz nb + 8) :=
        Nat.mul_le_mul_right _ (by omega)
      have h5 := arith_merge (sz na + sz nb) (sz ka + sz kb) (sz S) (sz (AR.run S na ka) + sz (AR.run S' nb kb))
        (by rw [sz_ar, sz_ar]; have := sz_pos S'; omega)
      rw [sz_ar]
      simp only [sz_ar] at h5 ⊢
      omega
theorem sz_mergeKids_le_rec : ∀ (ka kb : List AR) (tk : List CT) (ks : List AR), mergeKids ka kb tk = some ks →
    sz ks ≤ 9 * (sz ka + sz kb) ^ 2
  | [], [], [], ks, h => by
    simp only [mergeKids, Option.some.injEq] at h; subst h
    simp only [sz_nil]; norm_num
  | a :: as, b :: bs, t :: ts, ks, h => by
    simp only [mergeKids] at h
    obtain ⟨r, hr, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h2
    have h1 := sz_mergeAR_le_rec a b t r hr
    have h3 := sz_mergeKids_le_rec as bs ts l hl
    simp only [sz_cons]
    nlinarith [Nat.zero_le ((sz a + sz b) * (sz as + sz bs)), sz_pos a, sz_pos b, sz_pos as, sz_pos bs]
  | [], [], _ :: _, _, h => by simp [mergeKids] at h
  | [], _ :: _, _, _, h => by simp [mergeKids] at h
  | _ :: _, [], _, _, h => by simp [mergeKids] at h
  | _ :: _, _ :: _, [], _, h => by simp [mergeKids] at h
end

theorem sz_mergeAR_le_pair : (type_of% @sz_mergeAR_le_rec) ∧ (type_of% @sz_mergeKids_le_rec) :=
  ⟨@sz_mergeAR_le_rec, @sz_mergeKids_le_rec⟩

theorem sz_mergeAR_le : type_of% @sz_mergeAR_le_rec := sz_mergeAR_le_pair.1


/-! ## chain cardinalities and the cost constants -/

mutual
/-- every chain node of the analysis has a bag of at most `L` vertices -/
def ARcard (L : ℕ) : AR → Prop
  | .run _ c ks => (∀ n ∈ c, n.bag.card ≤ L) ∧ ARcardL L ks
def ARcardL (L : ℕ) : List AR → Prop
  | [] => True
  | k :: ks => ARcard L k ∧ ARcardL L ks
end

/-- the cost of one `findPath` call (chains of at most `s` nodes, entries `≤ L`, target sequence of length `≤ s`) -/
def fpBound (s L : ℕ) : ℕ :=
  6000 * (s + 1) * (s + 1) * (4 ^ (L + L + 1) + 1) ^ 2 * (2 * (L + L) + 1 + 2) ^ 2 +
    4 ^ (L + L + 1) * (100 * 3 ^ (2 * (L + L) + 1 + s) + 100 * (2 * (L + L) + 1) + 100) + 12 * (s + s) + 200

/-- local cost of `mergeAR` -/
def cMA (s L : ℕ) : ℕ := fpBound s L + 600 * (s + 3) ^ 2 + 200 * (s + 1) + 300

theorem ARcardL_iff {L : ℕ} : ∀ ks : List AR, ARcardL L ks ↔ ∀ k ∈ ks, ARcard L k
  | [] => by simp [ARcardL]
  | k :: ks => by simp [ARcardL, ARcardL_iff ks]

theorem ARcard_mkNode (L : ℕ) (S X : Finset ℕ) (junk : List RT) (core : List AR) (hX : X.card ≤ L)
    (hc : ∀ k ∈ core, ARcard L k) : ARcard L (mkNode S X junk core) := by
  rcases core with _ | ⟨k, _ | ⟨k2, t⟩⟩
  · simp only [mkNode, ARcard, ARcardL]
    exact ⟨by simpa using hX, trivial⟩
  · obtain ⟨Sk, ck, kk⟩ := k
    have hk := hc _ (List.mem_singleton_self _)
    simp only [mkNode, AR.S, AR.chain, AR.kids]
    by_cases h : Sk = S
    · simp only [h, if_true, ARcard]
      simp only [ARcard] at hk
      refine ⟨?_, hk.2⟩
      intro n hn
      rcases List.mem_cons.1 hn with rfl | hn
      · exact hX
      · exact hk.1 n hn
    · simp only [h, if_false, ARcard, ARcardL]
      exact ⟨by simpa using hX, hk, trivial⟩
  · simp only [mkNode, ARcard]
    refine ⟨by simpa using hX, ?_⟩
    rw [ARcardL_iff]
    intro x hx
    unfold sortAR at hx
    have hx' : x ∈ (k :: k2 :: t) :=
      (List.mergeSort_perm (k :: k2 :: t) (fun a b => decide (CT.key S a.char ≤ CT.key S b.char))).mem_iff.1 hx
    exact hc x hx'

theorem ARcard_analyze (L : ℕ) (Bd : Finset ℕ) (t : RT) :
    (∀ X ∈ t.bags, X.card ≤ L) → ARcard L (analyze Bd t) := by
  induction t using RT.ind with
  | h X ks ih =>
    intro hb
    rw [analyze_node, analyzeNode_eq]
    apply ARcard_mkNode
    · exact hb X (by simp [RT.bags])
    · intro k hk
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hk
      obtain ⟨hp1, _⟩ := List.mem_filter.1 hp
      obtain ⟨k0, hk0, rfl⟩ := List.mem_map.1 hp1
      exact ih k0 hk0 (fun Y hY => hb Y (by
        simp only [RT.bags, List.mem_cons]
        exact Or.inr ((RT.mem_bagsL_iff ks Y).2 ⟨k0, hk0, hY⟩)))

/-! ## the lemmas -/

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem flagI_runs (prev : Option (ℕ × ℕ)) (i : ℕ) (hB : 1 < B) :
    Runs Δ' B fFlagI [toVal prev, toVal i] (toVal (flagI prev i)) 20 := by
  refine Runs.mk (hΔ _ _ Δ_flagI) ?_
  rcases prev with _ | ⟨pi, pj⟩
  · simp only [Option.elim]
    ev_start
    · ev_run
    · omega
  · by_cases h : pi = i
    · subst h
      simp only [Option.elim, ne_eq, not_true_eq_false, decide_false, toVal_some, toVal_pair]
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
    · simp only [Option.elim, ne_eq, h, not_false_eq_true, decide_true, toVal_some, toVal_pair]
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h]; done) | (simp [h]; omega))
      · omega

theorem flagJ_runs (prev : Option (ℕ × ℕ)) (j : ℕ) (hB : 1 < B) :
    Runs Δ' B fFlagJ [toVal prev, toVal j] (toVal (flagJ prev j)) 20 := by
  refine Runs.mk (hΔ _ _ Δ_flagJ) ?_
  rcases prev with _ | ⟨pi, pj⟩
  · simp only [Option.elim]
    ev_start
    · ev_run
    · omega
  · by_cases h : pj = j
    · subst h
      simp only [Option.elim, ne_eq, not_true_eq_false, decide_false, toVal_some, toVal_pair]
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
    · simp only [Option.elim, ne_eq, h, not_false_eq_true, decide_true, toVal_some, toVal_pair]
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h]; done) | (simp [h]; omega))
      · omega

theorem mergeChain_runs (s : ℕ) (hB : 1000 + 100 * (s + 1) < B) (na nb : List CNode) (hna : sz na ≤ s)
    (hnb : sz nb ≤ s) : ∀ (path : List (ℕ × ℕ)) (prev : Option (ℕ × ℕ)),
    Runs Δ' B fMergeChain [toVal na, toVal nb, toVal prev, toVal path] (toVal (mergeChain na nb prev path))
      (250 * (s + 3) * path.length + 8)
  | [], prev => by
    refine Runs.mk (hΔ _ _ Δ_mergeChain) ?_
    simp only [mergeChain, List.length_nil]
    ev_start
    · ev_run
    · omega
  | (i, j) :: rest, prev => by
    have hE1 := Ext.trans extE1 hΔ
    have hΔA : E5A.Δ ⊑ Δ' := Ext.trans extA hΔ
    have hB1 : 1 < B := by omega
    have ih := mergeChain_runs s hB na nb hna hnb rest (some (i, j))
    have hn1 := E5A.nthD_runs hΔA B hB1 na i dflt
    have hn2 := E5A.nthD_runs hΔA B hB1 nb j dflt
    simp only [dflt, toVal_cnode, toVal_empty_finset, toVal_nil] at hn1 hn2
    have hfi := flagI_runs hΔ B prev i hB1
    have hfj := flagJ_runs hΔ B prev j hB1
    have hu := Lib3.union_runs (l3 hE1) B (na.getD i dflt).bag (nb.getD j dflt).bag
    have hla := length_le_sz na
    have hlb := length_le_sz nb
    have hga := sz_getD_le na i dflt
    have hgb := sz_getD_le nb j dflt
    have hd := sz_dflt
    have hA : sz (na.getD i dflt) = sz (na.getD i dflt).bag + sz (na.getD i dflt).junk + 1 := sz_cnode _ _
    have hBg : sz (nb.getD j dflt) = sz (nb.getD j dflt).bag + sz (nb.getD j dflt).junk + 1 := sz_cnode _ _
    have hc1 := card_le_sz (na.getD i dflt).bag
    have hc2 := card_le_sz (nb.getD j dflt).bag
    have hj1 := length_le_sz (na.getD i dflt).junk
    have hj2 := length_le_sz (nb.getD j dflt).junk
    have hk : fFlagI < B := by have : fFlagI < 1000 := by decide
                               omega
    have hk2 : fFlagJ < B := by have : fFlagJ < 1000 := by decide
                                omega
    have hk3 : fMergeChain < B := by have : fMergeChain < 1000 := by decide
                                     omega
    have hap := Lib1.append_runs (l1 hE1) B (if flagI prev i then (na.getD i dflt).junk else [])
      (if flagJ prev j then (nb.getD j dflt).junk else [])
    have hjl1 : (if flagI prev i then (na.getD i dflt).junk else []).length ≤ (na.getD i dflt).junk.length := by
      split_ifs <;> simp
    have hjl2 : (if flagJ prev j then (nb.getD j dflt).junk else []).length ≤ (nb.getD j dflt).junk.length := by
      split_ifs <;> simp
    have e : 250 * (s + 3) * (rest.length + 1) = 250 * (s + 3) * rest.length + 250 * (s + 3) := by ring
    refine Runs.mk (hΔ _ _ Δ_mergeChain) ?_
    rw [mergeChain_cons]
    simp only [toVal_cons, toVal_pair, toVal_cnode, List.length_cons]
    by_cases hI : flagI prev i = true <;> by_cases hJ : flagJ prev j = true
    · simp only [hI, hJ, if_true] at hfi hfj hap ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · rw [e]; try simp only [List.length_nil]
        omega
    · simp only [Bool.not_eq_true] at hJ
      simp only [hI, hJ, if_true, Bool.false_eq_true, if_false] at hfi hfj hap ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · rw [e]; try simp only [List.length_nil]
        omega
    · simp only [Bool.not_eq_true] at hI
      simp only [hI, hJ, if_true, Bool.false_eq_true, if_false] at hfi hfj hap ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · rw [e]; try simp only [List.length_nil]
        omega
    · simp only [Bool.not_eq_true] at hI hJ
      simp only [hI, hJ, Bool.false_eq_true, if_false] at hfi hfj hap ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · rw [e]; try simp only [List.length_nil]
        omega

/-- cost of `mergeReal` -/
def cMergeReal (s L ck6 : ℕ) : ℕ :=
  2 * (E5B.cA s ck6 * s) + cMA (5 * s) L * (5 * s) + 100 * (900 * (s * s) + 1) * (900 * (s * s)) + 100

theorem predJoin_runs (E : Ext5 Δ') (target d : CT) (s : ℕ) (hd : sz d ≤ s) (htg : sz target ≤ s)
    (hPD : E.PD s d target)
    (hB : 1000 + E.cDom s < B) :
    Runs Δ' B fPredJoin [toVal target, toVal d] (toVal (CT.domCB d target)) (E.cDom s + 10) := by
  have h1 := E.domC B s d target hPD hd htg (by omega)
  refine Runs.mk (hΔ _ _ Δ_predJoin) ?_
  ev_start
  · ev_run
  · omega

/-- cost of `realJoin` -/
def cRealJoin (s L Lj cnorm5 cdom ck6 cj : ℕ) : ℕ :=
  2 * (200 * (s + 1) * s + cnorm5 + 8) + cj + (24 * Lj + 6 + Lj * (cdom + 10)) + cMergeReal s L ck6 + 100

end proofs
end E5D
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E5W` -/

section
/-!
# WP E5 (layer W): tuple-argument wrappers and the `Embeds` statements

Ids `530 …` (the functions of `Embeds` take *one* argument, the tuple):

| id | wrapper of | argument tuple |
|---|---|---|
| 530 `fAnalyzeP` | `analyze` | `(Bd, t)` |
| 531 `fCutAtP` | `cutAt` | `(y, w, c, ns)` |
| 532 `fApplyPlanP` | `applyPlan` | `(v, N, Bd, path, p, t)` |
| 533 `fMergeRealP` | `mergeReal` | `(Bd, ta, tb, target)` |
| 534 `fRealIntroP` | `realIntro` | `(ip, kmax, v, N, Bd, t, target)` (`ip` = id of `introPlans`) |
| 535 `fRealJoinP` | `realJoin` | `(kmax, Bd, ta, tb, target)` |

Tuples are right-nested pairs, `(a, b, c) = (a, (b, c))`.  Every `embeds_*` theorem is stated for an arbitrary table
`Δ'` extending `E5W.Δ` (equivalently `e5Δ`, see `E5Tbl`) and the hypothesis records `Ext5` (norm, key, domC),
`ExtIP` (introPlans), `ExtJ` (joinC), which the assembler instantiates by the theorems of WPs E2/E3.
The costs are `κ · (S+1)^d`-shaped in the size `S` of the argument (and, for `realIntro`/`realJoin`, of the list of plans/join
options), plus the symbolic costs of the external functions; see the docstrings.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Lax117284Proofs.Treewidth.Fun
namespace E5W

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5 E5A

abbrev fAnalyzeP : ℕ := 530
abbrev fCutAtP : ℕ := 531
abbrev fApplyPlanP : ℕ := 532
abbrev fMergeRealP : ℕ := 533
abbrev fRealIntroP : ℕ := 534
abbrev fRealJoinP : ℕ := 535

/-! ## the terms -/

def analyzePTm : Tm := .call E5B.fAnalyze [.fst (V 0), .snd (V 0)]

def cutAtPTm : Tm :=
  .call E5C1.fCutAt [.fst (V 0), .fst (.snd (V 0)), .fst (.snd (.snd (V 0))), .snd (.snd (.snd (V 0)))]

def applyPlanPTm : Tm :=
  .call E5C3.fApplyPlan
    [.fst (V 0), .fst (.snd (V 0)), .fst (.snd (.snd (V 0))), .fst (.snd (.snd (.snd (V 0)))),
     .fst (.snd (.snd (.snd (.snd (V 0))))), .snd (.snd (.snd (.snd (.snd (V 0)))))]

def mergeRealPTm : Tm :=
  .call E5D.fMergeReal [.fst (V 0), .fst (.snd (V 0)), .fst (.snd (.snd (V 0))), .snd (.snd (.snd (V 0)))]

def realIntroPTm : Tm :=
  .call E5R.fRealIntro
    [.fst (V 0), .fst (.snd (V 0)), .fst (.snd (.snd (V 0))), .fst (.snd (.snd (.snd (V 0)))),
     .fst (.snd (.snd (.snd (.snd (V 0))))), .fst (.snd (.snd (.snd (.snd (.snd (V 0)))))),
     .snd (.snd (.snd (.snd (.snd (.snd (V 0))))))]

def realJoinPTm : Tm :=
  .call E5D.fRealJoin
    [.fst (V 0), .fst (.snd (V 0)), .fst (.snd (.snd (V 0))), .fst (.snd (.snd (.snd (V 0)))),
     .snd (.snd (.snd (.snd (V 0))))]

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 530 => some analyzePTm | 531 => some cutAtPTm | 532 => some applyPlanPTm | 533 => some mergeRealPTm
  | 534 => some realIntroPTm | 535 => some realJoinPTm | _ => none

def Δ : ℕ → Option Tm := layerΔ E5D.Δ 530 tbl

abbrev size : ℕ := 536

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 536 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h530 : 530 ≤ f := by omega
    simp only [h530, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem extD : E5D.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E5D.Δ_lt h; simp [E5D.size] at this; omega)
theorem extR : E5R.Δ ⊑ Δ := Ext.trans E5D.extR extD

/-! ## costs -/

/-- `analyze`: `S = sz (Bd, t)`; the second summand is the threshold for `B`. -/
def costAnalyze {Δ' : ℕ → Option Tm} (E : Ext5 Δ') (a : Finset ℕ × RT) : ℕ :=
  E5B.cA (sz a) (E.cKey (6 * sz a)) * sz a + (20000 + 20000 * (sz a + 1) + E.cKey (6 * sz a))

def costCutAt (a : List ℕ × List ℕ × CT.Cut × List CNode) : ℕ := 100 * sz a + 400 + (20000 + 20000 * (sz a + 1))

def costApplyPlan {Δ' : ℕ → Option Tm} (E : Ext5 Δ') (a : ℕ × Finset ℕ × Finset ℕ × List ℕ × CT.Plan × RT) : ℕ :=
  E5C3.cApplyPlan (sz a) (E.cKey (6 * sz a)) + (20000 + 20000 * (sz a + 1) + E.cKey (6 * sz a))

/-- `mergeReal`, with `L` a bound on the bag sizes of both trees. -/
def costMergeReal {Δ' : ℕ → Option Tm} (E : Ext5 Δ') (L : ℕ) (a : Finset ℕ × RT × RT × CT) : ℕ :=
  E5D.cMergeReal (sz a) L (E.cKey (6 * sz a)) + (200000 + 100000 * (sz a + 1) ^ 2 + E.cKey (6 * sz a))

/-- the total size `S` used by `realIntro`: the argument and the list of plans -/
def sizeRI (a : ℕ × ℕ × ℕ × Finset ℕ × Finset ℕ × RT × CT) : ℕ :=
  sz a + sz (CT.introPlans a.2.2.1 a.2.2.2.1 (a.2.2.2.2.2.1.char a.2.2.2.2.1))

/-- `realIntro` on `(ip, kmax, v, N, Bd, t, target)`: `L = S` bounds the number of plans, `S` the size of each -/
def costRealIntro {Δ' : ℕ → Option Tm} (E : Ext5 Δ') (X : ExtIP Δ') (a : ℕ × ℕ × ℕ × Finset ℕ × Finset ℕ × RT × CT) : ℕ :=
  E5R.cRealIntro (sizeRI a) (sizeRI a) (E.cNorm (5 * sizeRI a)) (E.cNorm (sizeRI a)) (E.cDom (sizeRI a))
      (E.cKey (6 * sizeRI a)) (X.cIP a.2.2.1 a.2.2.2.1 (a.2.2.2.2.2.1.char a.2.2.2.2.1)) +
    (20000 + 20000 * (sizeRI a + 1) + E.cKey (6 * sizeRI a) + E.cNorm (5 * sizeRI a) + E.cNorm (sizeRI a) +
      E.cDom (sizeRI a) + X.cIP a.2.2.1 a.2.2.2.1 (a.2.2.2.2.2.1.char a.2.2.2.2.1))

/-- the total size `S` used by `realJoin`: the argument and the list of join options -/
def sizeRJ (a : ℕ × Finset ℕ × RT × RT × CT) : ℕ :=
  sz a + sz (CT.joinC a.1 (a.2.2.1.char a.2.1) (a.2.2.2.1.char a.2.1))

/-- `realJoin` on `(kmax, Bd, ta, tb, target)` (`L` bounds the bag sizes) -/
def costRealJoin {Δ' : ℕ → Option Tm} (E : Ext5 Δ') (X : ExtJ Δ') (L : ℕ) (a : ℕ × Finset ℕ × RT × RT × CT) : ℕ :=
  E5D.cRealJoin (sizeRJ a) L (sizeRJ a) (E.cNorm (5 * sizeRJ a)) (E.cDom (sizeRJ a)) (E.cKey (6 * sizeRJ a))
      (X.cJ a.1 (a.2.2.1.char a.2.1) (a.2.2.2.1.char a.2.1)) +
    (200000 + 100000 * (sizeRJ a + 1) ^ 2 + E.cKey (6 * sizeRJ a) + E.cNorm (5 * sizeRJ a) + E.cDom (sizeRJ a) +
      X.cJ a.1 (a.2.2.1.char a.2.1) (a.2.2.2.1.char a.2.1))

/-! ## the `Embeds` statements -/

section embeds
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ')
include hΔ

end embeds

end E5W
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E5Tbl` -/

section
/-!
# WP E5: the table `e5Tbl` (ids `448 … 535`) and its assembly

`e5Tbl : ℕ → Option Tm` is the union of the layer tables `E5A … E5W` (disjoint ids), `e5Δ = layerΔ e1Δ 448 e5Tbl`
(the E1 functions are contained in it: E5 calls `typical`, `witnesses`, `findPath`).  `E5W.Δ = e5Δ` (`e5_eq`).

**How the assembler uses it.**  Let `T` be the assembled table (`layerΔ Lib.Δ 128 T` the assembled Δ).  If `e1Tbl ⊑ T` and
`e5Tbl ⊑ T` then `e5Δ ⊑ layerΔ Lib.Δ 128 T` (`ext_asm`; `ext_orElse_left/right` for the two usual shapes of `T`), and every
theorem `embeds_* : … Δ' …` of `E5W`, stated for `Δ' ⊒ E5W.Δ`, applies to `Δ' := layerΔ Lib.Δ 128 T`.  External functions:
`CT.norm` (id `E5.idNorm = 166`), `decide (key S a ≤ key S b)` (`E5.idKeyLe = 162`), `CT.domCB` (`E5.idDomC = 181`),
`CT.joinC` (`E5.idJoinC = 177`) come from E2, `CT.introPlans` from E3 (its id is `ExtIP.ip`); they are hypotheses
(`Ext5`, `ExtJ`, `ExtIP` of `E5Ext`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E5Tbl

/-- the functions of WP E5: ids `448 … 535`. -/
def e5Tbl : ℕ → Option Tm := fun f =>
  if 530 ≤ f then E5W.tbl f else if 520 ≤ f then E5D.tbl f else if 500 ≤ f then E5R.tbl f
  else if 490 ≤ f then E5C3.tbl f else if 480 ≤ f then E5C2.tbl f else if 470 ≤ f then E5C1.tbl f
  else if 460 ≤ f then E5B.tbl f else E5A.tbl f

/-- E1's library plus the E5 functions. -/
def e5Δ : ℕ → Option Tm := layerΔ E1.e1Δ 448 e5Tbl

theorem e5_eq : E5W.Δ = e5Δ := by
  funext f
  simp only [E5W.Δ, E5D.Δ, E5R.Δ, E5C3.Δ, E5C2.Δ, E5C1.Δ, E5B.Δ, E5A.Δ, e5Δ, e5Tbl, layerΔ]
  by_cases h1 : 530 ≤ f
  · have : 448 ≤ f := by omega
    simp [h1, this]
  by_cases h2 : 520 ≤ f
  · have : 448 ≤ f := by omega
    simp [h1, h2, this]
  by_cases h3 : 500 ≤ f
  · have : 448 ≤ f := by omega
    simp [h1, h2, h3, this]
  by_cases h4 : 490 ≤ f
  · have : 448 ≤ f := by omega
    simp [h1, h2, h3, h4, this]
  by_cases h5 : 480 ≤ f
  · have : 448 ≤ f := by omega
    simp [h1, h2, h3, h4, h5, this]
  by_cases h6 : 470 ≤ f
  · have : 448 ≤ f := by omega
    simp [h1, h2, h3, h4, h5, h6, this]
  by_cases h7 : 460 ≤ f
  · have : 448 ≤ f := by omega
    simp [h1, h2, h3, h4, h5, h6, h7, this]
  by_cases h8 : 448 ≤ f
  · simp [h1, h2, h3, h4, h5, h6, h7, h8]
  · simp [h1, h2, h3, h4, h5, h6, h7, h8]

/-- the last layer is the whole E5 table. -/
theorem ext : E5W.Δ ⊑ e5Δ := by rw [e5_eq]; exact Ext.refl _

/-- ids of the E5 table: `448 ≤ f < 536` -/
theorem e5Tbl_range {f : ℕ} {b : Tm} (h : e5Tbl f = some b) : 448 ≤ f ∧ f < 536 := by
  have h' : e5Δ f = some b := by
    unfold e5Δ layerΔ
    by_cases h448 : 448 ≤ f
    · simp [h448, h]
    · exfalso
      simp only [e5Tbl] at h
      split_ifs at h <;> first | omega | (unfold E5A.tbl at h; split at h <;> first | omega | simp at h)
  rw [← e5_eq] at h'
  have := E5W.Δ_lt h'
  refine ⟨?_, by simpa [E5W.size] using this⟩
  by_contra hf
  simp only [e5Tbl] at h
  split_ifs at h <;> first | omega | (unfold E5A.tbl at h; split at h <;> first | omega | simp at h)

theorem e5Tbl_ge {f : ℕ} {b : Tm} (h : e5Tbl f = some b) : 448 ≤ f := (e5Tbl_range h).1
theorem e5Tbl_lt {f : ℕ} {b : Tm} (h : e5Tbl f = some b) : f < 536 := (e5Tbl_range h).2

/-- **assembly**: if the assembled table `T` contains `e1Tbl` and `e5Tbl`, `e5Δ` is contained in `layerΔ Lib.Δ 128 T`. -/
theorem ext_asm (T : ℕ → Option Tm) (h1 : E1.e1Tbl ⊑ T) (h5 : e5Tbl ⊑ T) : e5Δ ⊑ layerΔ Lib.Δ 128 T := by
  intro f b h
  unfold e5Δ layerΔ at h
  by_cases h448 : 448 ≤ f
  · simp only [h448, if_true] at h
    have := h5 f b h
    have h128 : 128 ≤ f := by omega
    simp [layerΔ, h128, this]
  · simp only [h448, if_false] at h
    unfold E1.e1Δ Lib.extend layerΔ at h
    by_cases h128 : 128 ≤ f
    · simp only [h128, if_true] at h
      simp [layerΔ, h128, h1 f b h]
    · simp only [h128, if_false] at h
      simp [layerΔ, h128, h]

end E5Tbl
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E5Inst` -/

section
/-!
# WP E5: discharging the external hypotheses from the theorems of E2 and E3

`E5Ext` states what E5 needs from `norm`, `key`, `domCB`, `joinC` (E2) and `introPlans` (E3) as hypothesis records.  Here they
are *instantiated* by the proved theorems `E2.norm_runs_e12`, `E2.keyLe_runs`, `E2.domC_runs_e12`, `E2.joinC_runs_e12`,
`E3C.introPlans_runs` (with abstract costs equal to the thresholds of those theorems, so that the `Runs` facts are
`Runs.mono`-weakened).  Nothing of E5 depends on this file: it is the glue for the assembler.

* `ext5_e2 L` : `Ext5 Δ'` for every `Δ'` containing `e2Δ 152` and `e1Δ`; `Ext5.PD s a b := RB s L a ∧ RB s L b`
  (run sequences of length `≤ L`).
* `extJ_e2` : `ExtJ Δ'` (`PJ kmax a b := ∃ B0, a.Wf B0 kmax ∧ b.Wf B0 kmax`).
* `extIP_e3 …` : `ExtIP Δ'` (`ip = 325`) from `E3C.introPlans_runs`, for the parameters of that theorem.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Lax117284Proofs.Treewidth.Fun
namespace E5Inst

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT E5

/-- costs of the E2 functions used by E5, as functions of the size bound `s` -/
def cKeyE2 (s : ℕ) : ℕ := 1000 * (s + 1) ^ 2 + 100
def cNormE2 (s : ℕ) : ℕ := 14000 * (s + 1) ^ 5
def cDomE2 (L s : ℕ) : ℕ := (30 * s + 60 * 3 ^ (2 * L) + 100) * (2 * s) + 1000

/-- `E5.Ext5` from E2: `norm` (id 166), `key` (162), `domCB` (181; run sequences of length `≤ L`). -/
def ext5_e2 (L : ℕ) {Δ' : ℕ → Option Tm} (hΔ : E2.e2Δ E1C.fRingTypList ⊑ Δ') (hE1 : E1.e1Δ ⊑ Δ') : Ext5 Δ' where
  cKey := cKeyE2
  keyLe := fun B s S a b hS ha hb hB =>
    (E2.keyLe_runs hΔ B S a b s hS ha hb (by unfold cKeyE2 at hB; omega)).mono (by unfold cKeyE2; omega)
  cNorm := cNormE2
  norm := fun B s c hc hB =>
    (E2.norm_runs_e12 hΔ hE1 B c s hc hB).mono (by
      have : 1 ≤ (s + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
      unfold cNormE2; omega)
  norm_sz := E2.sz_norm_le
  PD := fun s a b => RB s L a ∧ RB s L b
  cDom := cDomE2 L
  domC := fun B s a b hab hsa hsb hB => by
    have hcnt := count_le_sz a
    have hc : (30 * s + 60 * 3 ^ (2 * L) + 100) * (2 * a.count) ≤ (30 * s + 60 * 3 ^ (2 * L) + 100) * (2 * s) :=
      Nat.mul_le_mul_left _ (by have := le_trans hcnt hsa; omega)
    have h := E2.domC_runs_e12 hΔ hE1 B L s a b hab.1 hab.2 hsa hsb (by unfold cDomE2 at hB; omega)
    exact h.mono (by unfold cDomE2; omega)

/-- `E5.ExtJ` from E2 (`joinC`, id 177): `a, b` well formed over a common boundary with entries `≤ kmax`. -/
def extJ_e2 {Δ' : ℕ → Option Tm} (hΔ : E2.e2Δ E1C.fRingTypList ⊑ Δ') (hE1 : E1.e1Δ ⊑ Δ') : ExtJ Δ' where
  PJ := fun kmax a b => ∃ B0 : Finset ℕ, a.Wf B0 kmax ∧ b.Wf B0 kmax
  cJ := fun kmax a b =>
    28000 * (sz a + sz b + 1) * 2 ^ (48 * (a.verts.card + kmax + 2) ^ 3) + 2000 * (sz a + sz b + 1) + 2000 +
      E2.R0k kmax + 1000
  joinC := fun B kmax a b hab hB => by
    obtain ⟨B0, ha, hb⟩ := hab
    have hv : a.verts = B0 := ha.verts_eq
    subst hv
    have h := E2.joinC_runs_e12 hΔ hE1 B ha hb (sz a + sz b) (by omega) (by omega) (by simpa using hB)
    refine h.mono ?_
    have hj : 14000 * (sz a + sz b + 1) * 2 ^ (48 * (a.verts.card + kmax + 2) ^ 3) ≤
        28000 * (sz a + sz b + 1) * 2 ^ (48 * (a.verts.card + kmax + 2) ^ 3) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- `E5.ExtIP` from `E3C.introPlans_runs` (id `325`), for the parameters of that theorem. -/
def extIP_e3 (U Q P G Ω Qc Q₀ : ℕ) (Bs : Finset ℕ) (kmax M : ℕ)
    (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (hP : Q * (3 * M) ≤ P) (hQc : 1000 * ((U + 1) * Ω) ≤ Qc)
    (hQ₀ : 100 * (P * G) + 4 * (Qc * (U + 1) * G) + 500 * ((U + 1) * G) + 1000 * (U + 1) ≤ Q₀)
    (hG : ∀ (v : ℕ) (N : Finset ℕ) (ν : CT), Good Bs ν → maxEntry ν ≤ kmax → count ν ≤ M →
      (wtopPlans v ν).length + 1 ≤ G ∧ (allChains ν.S N).length + 1 ≤ G ∧
      (attachPlans v N ν).length ≤ G ∧ (introPlans v N ν).length ≤ G)
    (hΩ : ∀ (N : Finset ℕ) (ν : CT), Good Bs ν → (chainCands ν.S N).length + 1 ≤ Ω)
    {Δ' : ℕ → Option Tm} (hΔ : E3C.Δ ⊑ Δ') : ExtIP Δ' where
  ip := E3C.fIntroPlans
  PIP := fun v N t => v ≤ U ∧ N.card ≤ U ∧ sz t ≤ U ∧ mx t ≤ U ∧ Good Bs t ∧ maxEntry t ≤ kmax ∧ count t ≤ M
  cIP := fun _ _ t => Q₀ * (3 * count t - 1) + (10 * U + 600)
  introPlans := fun B v N t ⟨hv, hN, hs, hm, hg, hk, hc⟩ hB =>
    (E3C.introPlans_runs hΔ B U Q P G Ω Qc Q₀ Bs kmax M v N hQ hP hQc hQ₀ hv hN (fun ν => hG v N ν)
      (fun ν => hΩ N ν) (by omega) t hs hm hg hk hc).mono (by omega)

/-! ## a worked assembly: E1 + E2 + E3 + E5 -/

/-- the union of the tables of E1, E2, E3 (as in `E3.Assembly`) and E5 -/
def asm5Tbl : ℕ → Option Tm := orElseΔ E3.asmTbl E5Tbl.e5Tbl

def asm5Δ : ℕ → Option Tm := layerΔ Lib.Δ 128 asm5Tbl

theorem asmTbl_lt {f : ℕ} {b : Tm} (h : E3.asmTbl f = some b) : f < 333 := by
  unfold E3.asmTbl orElseΔ at h
  rcases h1 : E1.e1Tbl f with _ | c
  · rcases h2 : E2.e2Tbl E1C.fRingTypList f with _ | c'
    · rcases h3 : E3.e3Tbl f with _ | c''
      · simp [h1, h2, h3] at h
      · have := (E3.e3Tbl_lt h3).2; omega
    · have := (E2.e2Tbl_lt _ h2).2; omega
  · have := E1.e1Tbl_lt h1; omega

end E5Inst
end Lax117284Proofs.Treewidth.Fun

end
