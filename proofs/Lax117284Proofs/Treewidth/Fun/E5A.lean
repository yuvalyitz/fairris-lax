import Lax117284Proofs.Treewidth.Fun.E5Ext
import Lax117284Proofs.Treewidth.Chars.Alg

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
theorem sz_charAR_le : ∀ r : AR, sz r.char ≤ sz r
  | .run S c ks => by
    have h1 := sz_charARL_le ks
    have h2 := sz_chain_ge c
    have h3 := typical_length_le (c.map (fun n => n.bag.card))
    rw [List.length_map] at h3
    rw [sz_ar]
    simp only [AR.char, sz_ct_node, sz_list_nat, List.length_map]
    omega
theorem sz_charARL_le : ∀ ks : List AR, sz (AR.charL ks) ≤ sz ks
  | [] => by simp [AR.charL]
  | k :: ks => by
    have h1 := sz_charAR_le k
    have h2 := sz_charARL_le ks
    simp only [AR.charL, sz_cons]; omega
end

theorem sz_chainToRT_le : ∀ (ns : List CNode) (ks : List RT), sz (AR.chainToRT ns ks) ≤ sz ns + sz ks + 2
  | [], ks => by simp [AR.chainToRT, sz_rt_node, sz_finset]
  | [n], ks => by
    obtain ⟨b, j⟩ := n
    have := sz_append j ks
    simp only [AR.chainToRT, sz_rt_node, sz_cons, sz_cnode]
    have : sz ([] : List CNode) = 1 := rfl
    omega
  | n :: m :: r, ks => by
    obtain ⟨b, j⟩ := n
    have ih := sz_chainToRT_le (m :: r) ks
    have h1 := sz_append j [AR.chainToRT (m :: r) ks]
    have h2 : sz [AR.chainToRT (m :: r) ks] = sz (AR.chainToRT (m :: r) ks) + 2 := by
      rw [sz_cons]; simp
    have h3 : sz (CNode.mk b j :: m :: r) = sz b + sz j + 1 + sz (m :: r) + 1 := by
      rw [sz_cons, sz_cnode]
    simp only [AR.chainToRT, sz_rt_node]
    omega

mutual
theorem sz_toRT_le : ∀ r : AR, sz (AR.toRT r) ≤ sz r
  | .run S c ks => by
    have h1 := sz_toRTL_le ks
    have h2 := sz_chainToRT_le c (AR.toRTL ks)
    have := sz_pos S
    rw [sz_ar]
    simp only [AR.toRT]
    omega
theorem sz_toRTL_le : ∀ ks : List AR, sz (AR.toRTL ks) ≤ sz ks
  | [] => by simp [AR.toRTL]
  | k :: ks => by
    have h1 := sz_toRT_le k
    have h2 := sz_toRTL_le ks
    simp only [AR.toRTL, sz_cons]; omega
end

mutual
theorem sz_prof_le (Bd : Finset ℕ) : ∀ t : RT, sz (t.prof Bd) ≤ sz t + 4 * t.size
  | .node X ks => by
    have h1 := sz_profL_le Bd ks
    have h2 := sz_inter_le X Bd
    simp only [RT.prof, sz_ct_node, sz_rt_node, RT.size]
    have : sz [X.card] = 3 := by simp [sz_cons]
    rw [this]
    omega
theorem sz_profL_le (Bd : Finset ℕ) : ∀ ks : List RT, sz (RT.profL Bd ks) ≤ sz ks + 4 * RT.sizeL ks
  | [] => by simp [RT.profL, RT.sizeL]
  | k :: ks => by
    have h1 := sz_prof_le Bd k
    have h2 := sz_profL_le Bd ks
    simp only [RT.profL, sz_cons, RT.sizeL]; omega
end

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
theorem charAR_runs (s : ℕ) (hB : 100 * (s + 1) < B) : ∀ r : AR, sz r ≤ s →
    Runs Δ' B fCharAR [toVal r] (toVal r.char) (400 * (s + 1) ^ 3 * cnt r)
  | .run S c ks, hs => by
    have hcs : sz c ≤ s := by have := sz_c_lt S c ks; omega
    have hks : sz ks ≤ s := by have := sz_ks_lt S c ks; omega
    have h1 := cards_runs hΔ B c (by omega)
    have h2 := E1A.typical_runs (eA (Ext.trans extE1 hΔ)) B (by omega) (c.map (fun n => n.bag.card))
    have h3 := charARL_runs s hB ks hks
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
theorem charARL_runs (s : ℕ) (hB : 100 * (s + 1) < B) : ∀ ks : List AR, sz ks ≤ s →
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
    have h1 := charAR_runs s hB k hk
    have h2 := charARL_runs s hB ks hks
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
theorem toRT_runs (s : ℕ) (hB : 100 * (s + 1) < B) : ∀ r : AR, sz r ≤ s →
    Runs Δ' B fToRT [toVal r] (toVal (AR.toRT r)) (100 * (s + 1) * cnt r)
  | .run S c ks, hs => by
    have hcs : sz c ≤ s := by have := sz_c_lt S c ks; omega
    have hks : sz ks ≤ s := by have := sz_ks_lt S c ks; omega
    have h1 := chainToRT_runs hΔ B c (AR.toRTL ks) (by omega)
    have h2 := toRTL_runs s hB ks hks
    have h5 : ks.length ≤ s := by have := length_le_sz ks; omega
    refine Runs.mk (hΔ _ _ Δ_toRT) ?_
    simp only [AR.toRT, toVal_ar, cnt]
    ev_start
    · ev_run
    · generalize hT : s + 1 = T at *
      have e : 100 * T * (1 + cntL ks) = 100 * T + 100 * T * cntL ks := by ring
      rw [e]
      nlinarith
theorem toRTL_runs (s : ℕ) (hB : 100 * (s + 1) < B) : ∀ ks : List AR, sz ks ≤ s →
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
    have h1 := toRT_runs s hB k hk
    have h2 := toRTL_runs s hB ks hks
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

mutual
theorem prof_runs (Bd : Finset ℕ) (s : ℕ) (hB : 100 * (s + 1) < B) (hBd : sz Bd ≤ s) : ∀ t : RT, sz t ≤ s →
    Runs Δ' B fProf [toVal Bd, toVal t] (toVal (t.prof Bd)) (200 * (s + 1) * t.size)
  | .node X ks, hs => by
    have hX : sz X ≤ s := by have := sz_rt_X_lt X ks; omega
    have hks : sz ks ≤ s := by have := sz_rt_ks_lt X ks; omega
    have h1 := Lib3.inter_runs (l3 (Ext.trans extE1 hΔ)) B X Bd
    have hc := card_le_sz X
    have h2 := Lib4.card_runs (l4 (Ext.trans extE1 hΔ)) B X (by omega)
    have h3 := profL_runs Bd s hB hBd ks hks
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
theorem profL_runs (Bd : Finset ℕ) (s : ℕ) (hB : 100 * (s + 1) < B) (hBd : sz Bd ≤ s) : ∀ ks : List RT, sz ks ≤ s →
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
    have h1 := prof_runs Bd s hB hBd k hk
    have h2 := profL_runs Bd s hB hBd ks hks
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
