import Lax117284Proofs.Treewidth.Fun.ToVal
import Lax117284Proofs.Treewidth.Wrap.ImproveC

/-!
# WP E0 (1): `ToVal` instances for the data types of the algorithm

Types that flow through `tables`, `extract`, `realIntro`, `realJoin`, `niceOf`, `compress`, `NT.addEverywhere`,
`NT.encode`, `improveC`, `decomposeC`, `introPlans`, `joinC`, `ringTypList`, `mergeReal`, `analyze`:

| type | view |
|---|---|
| `CT` (`node S y ks`) | `cons (S) (cons (y) (ks))`, `ks` the ordinary list view |
| `RT` (`node X ks`) | `cons (X) (ks)` |
| `NT` | `leaf = 0`, `intro v c = (1, (v, c))`, `forget v c = (2, (v, c))`, `join a b = (3, (a, b))` (right-nested `cons`) |
| `CNode` | `cons bag junk` |
| `AR` (`run S chain ks`) | `cons S (cons chain ks)` |
| `Cut` | `t1 f = (1, f)`, `t2 f = (2, f)` |
| `WPlan` | `endAt c = (1, c)`, `whole ps = (2, ps)` |
| `Plan` | `att c chain M = (1, (c, (chain, M)))`, `top pre w = (2, (pre, w))` |
| `WithTop ℕ` (`CT.key`) | as `Option ℕ` (`⊤ = 0`, `↑n = (1, n)`) |

Everything else is already an instance of `Prod/List/Option/ℕ/Bool/Finset ℕ`: `LState = List ℕ × List (ℕ × ℕ)`,
`List (List ℕ × Plan × CT)` (`introPlans`), `Option RT`, `Option (List AR)`, lattice paths `List (ℕ × ℕ)`, …
`Adj` (a function) is *not* a value: the machine receives the graph word `x` and reads adjacency off it (`adjOfWord`).

Injectivity of the nested ones is proved by mutual structural recursion.  After each instance a `toVal_*` simp lemma
gives the view in terms of the *ordinary* list/option views (`encCTL ks = toVal ks` etc.).
-/

namespace Lax117284Proofs.Treewidth.Fun

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees

/-! ## `CT` -/

mutual
def encCT : CT → Val
  | .node S y ks => .cons (toVal S) (.cons (toVal y) (encCTL ks))
def encCTL : List CT → Val
  | [] => .nat 0
  | k :: ks => .cons (encCT k) (encCTL ks)
end

mutual
theorem encCT_inj : ∀ a b : CT, encCT a = encCT b → a = b
  | .node S y ks, .node S' y' ks', h => by
    simp only [encCT, Val.cons.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have e1 : S = S' := ToVal.inj h1
    have e2 : y = y' := ToVal.inj h2
    have e3 := encCTL_inj ks ks' h3
    subst e1 e2 e3; rfl
theorem encCTL_inj : ∀ a b : List CT, encCTL a = encCTL b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [encCTL] at h
  | _ :: _, [], h => by simp [encCTL] at h
  | k :: ks, k' :: ks', h => by
    simp only [encCTL, Val.cons.injEq] at h
    rw [encCT_inj k k' h.1, encCTL_inj ks ks' h.2]
end

instance : ToVal CT := ⟨encCT, fun a b h => encCT_inj a b h⟩

theorem encCTL_eq : ∀ ks : List CT, encCTL ks = toVal ks
  | [] => rfl
  | k :: ks => by simp only [encCTL, toVal_cons]; rw [encCTL_eq ks]; rfl

@[simp] theorem toVal_ct (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    toVal (CT.node S y ks) = Val.cons (toVal S) (Val.cons (toVal y) (toVal ks)) := by
  show encCT _ = _
  simp only [encCT, encCTL_eq]

/-! ## `RT` -/

mutual
def encRT : RT → Val
  | .node X ks => .cons (toVal X) (encRTL ks)
def encRTL : List RT → Val
  | [] => .nat 0
  | k :: ks => .cons (encRT k) (encRTL ks)
end

mutual
theorem encRT_inj : ∀ a b : RT, encRT a = encRT b → a = b
  | .node X ks, .node X' ks', h => by
    simp only [encRT, Val.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 : X = X' := ToVal.inj h1
    have e2 := encRTL_inj ks ks' h2
    subst e1 e2; rfl
theorem encRTL_inj : ∀ a b : List RT, encRTL a = encRTL b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [encRTL] at h
  | _ :: _, [], h => by simp [encRTL] at h
  | k :: ks, k' :: ks', h => by
    simp only [encRTL, Val.cons.injEq] at h
    rw [encRT_inj k k' h.1, encRTL_inj ks ks' h.2]
end

instance : ToVal RT := ⟨encRT, fun a b h => encRT_inj a b h⟩

theorem encRTL_eq : ∀ ks : List RT, encRTL ks = toVal ks
  | [] => rfl
  | k :: ks => by simp only [encRTL, toVal_cons]; rw [encRTL_eq ks]; rfl

@[simp] theorem toVal_rt (X : Finset ℕ) (ks : List RT) :
    toVal (RT.node X ks) = Val.cons (toVal X) (toVal ks) := by
  show encRT _ = _
  simp only [encRT, encRTL_eq]

/-! ## `NT` -/

def encNT : NT → Val
  | .leaf => .nat 0
  | .intro v c => .cons (.nat 1) (.cons (.nat v) (encNT c))
  | .forget v c => .cons (.nat 2) (.cons (.nat v) (encNT c))
  | .join a b => .cons (.nat 3) (.cons (encNT a) (encNT b))

theorem encNT_inj : ∀ a b : NT, encNT a = encNT b → a = b
  | .leaf, .leaf, _ => rfl
  | .leaf, .intro _ _, h => by simp [encNT] at h
  | .leaf, .forget _ _, h => by simp [encNT] at h
  | .leaf, .join _ _, h => by simp [encNT] at h
  | .intro _ _, .leaf, h => by simp [encNT] at h
  | .forget _ _, .leaf, h => by simp [encNT] at h
  | .join _ _, .leaf, h => by simp [encNT] at h
  | .intro v c, .intro v' c', h => by
    simp only [encNT, Val.cons.injEq, Val.nat.injEq, true_and] at h
    rw [h.1, encNT_inj c c' h.2]
  | .forget v c, .forget v' c', h => by
    simp only [encNT, Val.cons.injEq, Val.nat.injEq, true_and] at h
    rw [h.1, encNT_inj c c' h.2]
  | .join a b, .join a' b', h => by
    simp only [encNT, Val.cons.injEq, true_and] at h
    rw [encNT_inj a a' h.1, encNT_inj b b' h.2]
  | .intro _ _, .forget _ _, h => by simp [encNT] at h
  | .intro _ _, .join _ _, h => by simp [encNT] at h
  | .forget _ _, .intro _ _, h => by simp [encNT] at h
  | .forget _ _, .join _ _, h => by simp [encNT] at h
  | .join _ _, .intro _ _, h => by simp [encNT] at h
  | .join _ _, .forget _ _, h => by simp [encNT] at h

instance : ToVal NT := ⟨encNT, fun a b h => encNT_inj a b h⟩

@[simp] theorem toVal_nt_leaf : toVal NT.leaf = Val.nat 0 := rfl
@[simp] theorem toVal_nt_intro (v : ℕ) (c : NT) :
    toVal (NT.intro v c) = Val.cons (.nat 1) (.cons (.nat v) (toVal c)) := rfl
@[simp] theorem toVal_nt_forget (v : ℕ) (c : NT) :
    toVal (NT.forget v c) = Val.cons (.nat 2) (.cons (.nat v) (toVal c)) := rfl
@[simp] theorem toVal_nt_join (a b : NT) :
    toVal (NT.join a b) = Val.cons (.nat 3) (.cons (toVal a) (toVal b)) := rfl

/-! ## `CNode`, `AR` -/

instance : ToVal CNode := ⟨fun n => .cons (toVal n.bag) (toVal n.junk), by
  rintro ⟨b, j⟩ ⟨b', j'⟩ h
  simp only [Val.cons.injEq] at h
  have e1 : b = b' := ToVal.inj h.1
  have e2 : j = j' := ToVal.inj h.2
  subst e1 e2; rfl⟩

@[simp] theorem toVal_cnode (b : Finset ℕ) (j : List RT) :
    toVal (CNode.mk b j) = Val.cons (toVal b) (toVal j) := rfl

mutual
def encAR : AR → Val
  | .run S c ks => .cons (toVal S) (.cons (toVal c) (encARL ks))
def encARL : List AR → Val
  | [] => .nat 0
  | k :: ks => .cons (encAR k) (encARL ks)
end

mutual
theorem encAR_inj : ∀ a b : AR, encAR a = encAR b → a = b
  | .run S c ks, .run S' c' ks', h => by
    simp only [encAR, Val.cons.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have e1 : S = S' := ToVal.inj h1
    have e2 : c = c' := ToVal.inj h2
    have e3 := encARL_inj ks ks' h3
    subst e1 e2 e3; rfl
theorem encARL_inj : ∀ a b : List AR, encARL a = encARL b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [encARL] at h
  | _ :: _, [], h => by simp [encARL] at h
  | k :: ks, k' :: ks', h => by
    simp only [encARL, Val.cons.injEq] at h
    rw [encAR_inj k k' h.1, encARL_inj ks ks' h.2]
end

instance : ToVal AR := ⟨encAR, fun a b h => encAR_inj a b h⟩

theorem encARL_eq : ∀ ks : List AR, encARL ks = toVal ks
  | [] => rfl
  | k :: ks => by simp only [encARL, toVal_cons]; rw [encARL_eq ks]; rfl

@[simp] theorem toVal_ar (S : Finset ℕ) (c : List CNode) (ks : List AR) :
    toVal (AR.run S c ks) = Val.cons (toVal S) (Val.cons (toVal c) (toVal ks)) := by
  show encAR _ = _
  simp only [encAR, encARL_eq]

/-! ## `CT.Cut`, `CT.WPlan`, `CT.Plan` -/

instance : ToVal CT.Cut := ⟨fun c => match c with
    | .t1 f => .cons (.nat 1) (.nat f)
    | .t2 f => .cons (.nat 2) (.nat f), by
  intro a b h
  cases a <;> cases b <;> simp at h ⊢ <;> exact h⟩

@[simp] theorem toVal_cut_t1 (f : ℕ) : toVal (CT.Cut.t1 f) = Val.cons (.nat 1) (.nat f) := rfl
@[simp] theorem toVal_cut_t2 (f : ℕ) : toVal (CT.Cut.t2 f) = Val.cons (.nat 2) (.nat f) := rfl

mutual
def encWP : CT.WPlan → Val
  | .endAt c => .cons (.nat 1) (toVal c)
  | .whole ps => .cons (.nat 2) (encWPL ps)
def encWPL : List (Option CT.WPlan) → Val
  | [] => .nat 0
  | p :: ps => .cons (encWPO p) (encWPL ps)
def encWPO : Option CT.WPlan → Val
  | none => .nat 0
  | some p => .cons (.nat 1) (encWP p)
end

mutual
theorem encWP_inj : ∀ a b : CT.WPlan, encWP a = encWP b → a = b
  | .endAt c, .endAt c', h => by
    simp only [encWP, Val.cons.injEq, true_and] at h
    rw [show c = c' from ToVal.inj h]
  | .whole ps, .whole ps', h => by
    simp only [encWP, Val.cons.injEq, true_and] at h
    rw [encWPL_inj ps ps' h]
  | .endAt _, .whole _, h => by simp [encWP] at h
  | .whole _, .endAt _, h => by simp [encWP] at h
theorem encWPL_inj : ∀ a b : List (Option CT.WPlan), encWPL a = encWPL b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [encWPL] at h
  | _ :: _, [], h => by simp [encWPL] at h
  | p :: ps, p' :: ps', h => by
    simp only [encWPL, Val.cons.injEq] at h
    rw [encWPO_inj p p' h.1, encWPL_inj ps ps' h.2]
theorem encWPO_inj : ∀ a b : Option CT.WPlan, encWPO a = encWPO b → a = b
  | none, none, _ => rfl
  | none, some _, h => by simp [encWPO] at h
  | some _, none, h => by simp [encWPO] at h
  | some p, some p', h => by
    simp only [encWPO, Val.cons.injEq, true_and] at h
    rw [encWP_inj p p' h]
end

instance : ToVal CT.WPlan := ⟨encWP, fun a b h => encWP_inj a b h⟩

theorem encWPO_eq : ∀ p : Option CT.WPlan, encWPO p = toVal p
  | none => rfl
  | some _ => rfl

theorem encWPL_eq : ∀ ps : List (Option CT.WPlan), encWPL ps = toVal ps
  | [] => rfl
  | p :: ps => by simp only [encWPL, toVal_cons]; rw [encWPL_eq ps, encWPO_eq]

@[simp] theorem toVal_wp_endAt (c : CT.Cut) : toVal (CT.WPlan.endAt c) = Val.cons (.nat 1) (toVal c) := rfl
@[simp] theorem toVal_wp_whole (ps : List (Option CT.WPlan)) :
    toVal (CT.WPlan.whole ps) = Val.cons (.nat 2) (toVal ps) := by
  show encWP _ = _
  simp only [encWP, encWPL_eq]

instance : ToVal CT.Plan := ⟨fun p => match p with
    | .att c ch M => .cons (.nat 1) (.cons (toVal c) (.cons (toVal ch) (toVal M)))
    | .top pre w => .cons (.nat 2) (.cons (toVal pre) (toVal w)), by
  intro a b h
  cases a <;> cases b <;> simp at h
  · obtain ⟨h1, h2, h3⟩ := h
    have e1 : _ = _ := ToVal.inj h1
    have e2 : _ = _ := ToVal.inj h2
    have e3 : _ = _ := ToVal.inj h3
    subst e1 e2 e3; rfl
  · obtain ⟨h1, h2⟩ := h
    have e1 : _ = _ := ToVal.inj h1
    have e2 : _ = _ := ToVal.inj h2
    subst e1 e2; rfl⟩

@[simp] theorem toVal_plan_att (c : Option CT.Cut) (ch : List (Finset ℕ)) (M : Finset ℕ) :
    toVal (CT.Plan.att c ch M) = Val.cons (.nat 1) (Val.cons (toVal c) (Val.cons (toVal ch) (toVal M))) := rfl
@[simp] theorem toVal_plan_top (pre : Option CT.Cut) (w : CT.WPlan) :
    toVal (CT.Plan.top pre w) = Val.cons (.nat 2) (Val.cons (toVal pre) (toVal w)) := rfl

/-! ## `WithTop ℕ` (the key of `CT.key`) -/

instance : ToVal (WithTop ℕ) := ⟨fun x => toVal (show Option ℕ from x), fun _ _ h => ToVal.inj (α := Option ℕ) h⟩

@[simp] theorem toVal_withTop_top : toVal (⊤ : WithTop ℕ) = Val.nat 0 := rfl
@[simp] theorem toVal_withTop_coe (n : ℕ) : toVal ((n : ℕ) : WithTop ℕ) = Val.cons (.nat 1) (.nat n) := rfl

end Lax117284Proofs.Treewidth.Fun
