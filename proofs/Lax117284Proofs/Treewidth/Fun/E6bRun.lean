import Lax117284Proofs.Treewidth.Fun.E4Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lax117284Proofs.Treewidth.Fun.Lib4
import Lax117284Proofs.Treewidth.Fun.E5Inst
import Lax117284Proofs.Treewidth.Size.Cells
import Lax117284Proofs.OmegaFresh
import Lax117284Proofs.Treewidth.Size.Statements
import Lax117284Proofs.Treewidth.Chars.Extract
import Lax117284Proofs.Treewidth.Fun.ToValAlgSize

/-! ### `Lax117284Proofs.Treewidth.Fun.E4Steps` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E4 (3): the three table steps, with abstract size parameters

`forgetTable_runs`, `introTable_runs`, `joinTable_runs`: the cost is stated in terms of bounds on the input list
(`L` = length, `s` = size of every entry) and on the intermediate list; `E4Tables` instantiates them with the P1 bounds.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E4

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT

theorem sq_lt_of_le {a b B : ℕ} (h : a ≤ b) (hb : (b + 2) ^ 2 < B) : (a + 2) ^ 2 < B :=
  lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hb

theorem sum_map_le_aux {α : Type} (f : α → ℕ) (c : ℕ) (l : List α) (h : ∀ a ∈ l, f a ≤ c) :
    (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem sz_forgetC_le (x : ℕ) (c : CT) : sz (CT.forgetC x c) ≤ sz c := by
  unfold CT.forgetC
  exact le_trans (E2.sz_norm_le _) (E2.sz_relabel_le x c)

/-- the cost of the forget step -/
def forgetCostF (s L : ℕ) : ℕ := 7300 * (s + 1) ^ 5 * (L + 1) ^ 2
/-- the cost of the introduce step -/
def introCostF (Ci Lg L sOut Lp : ℕ) : ℕ := L * (Ci + 10 * Lg + 100) + 100 + 60 * (sOut + 1) * (Lp + 1) ^ 2
/-- the cost of the join step -/
def joinCostF (Cj La Lb Lj sOut : ℕ) : ℕ :=
  La * (Lb * (Cj + 10 * Lj + 50) + 40 + 10 * (Lb * Lj) + 20) + 100 + 60 * (sOut + 1) * (La * (Lb * Lj) + 1) ^ 2

section steps
variable {Δ' : ℕ → Option Tm} (hΔ : Ext4 Δ') (B : ℕ)
include hΔ

/-- **forget step**: `forgetTable x T = dedup (map (forgetC x) T)` with entries of size `≤ s`, `|T| ≤ L`. -/
theorem forgetTable_runs (x : ℕ) (T : List CT) (s L : ℕ) (hs : ∀ c ∈ T, sz c ≤ s) (hL : T.length ≤ L)
    (hB : (forgetCostF s L + 2) ^ 2 < B) :
    Runs Δ' B fForgetTable [toVal x, toVal T] (toVal (forgetTable x T)) (forgetCostF s L) := by
  unfold forgetCostF at hB ⊢
  have hQ : 1 ≤ (s + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hQs : s + 1 ≤ (s + 1) ^ 5 := by
    calc s + 1 = (s + 1) ^ 1 := (pow_one _).symm
      _ ≤ (s + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hCpos : 1 ≤ 7300 * (s + 1) ^ 5 * (L + 1) ^ 2 := by
    have : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hB1 : 1 < B := by
    have := hB; nlinarith [Nat.pow_le_pow_left (show 2 ≤ 7300 * (s + 1) ^ 5 * (L + 1) ^ 2 + 2 by omega) 2]
  have hB500 : 500 < B := by
    have h1 : 7300 ≤ 7300 * (s + 1) ^ 5 * (L + 1) ^ 2 := by
      have : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      nlinarith
    have h2 : (7300 + 2) ^ 2 ≤ (7300 * (s + 1) ^ 5 * (L + 1) ^ 2 + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hf : ∀ a ∈ T, Runs Δ' B E2.fForgetC [toVal x, toVal a] (toVal (CT.forgetC x a)) (7000 * (s + 1) ^ 5) := by
    intro a ha
    refine E2.forgetC_runs_fits hΔ.e2 hΔ.e1 B x a s (hs a ha) ?_
    refine sq_lt_of_le ?_ hB
    have : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hmap := map_runs hΔ.l1 B E2.fForgetC (toVal x) (CT.forgetC x) (fun _ => 7000 * (s + 1) ^ 5) T hf
  have hsum : (T.map (fun _ => 7000 * (s + 1) ^ 5)).sum = T.length * (7000 * (s + 1) ^ 5) := by simp
  rw [hsum] at hmap
  have hs' : ∀ a ∈ T.map (CT.forgetC x), sz a ≤ s := by
    intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    exact le_trans (sz_forgetC_le x c) (hs c hc)
  have hdd := Lib2.dedup_runs hΔ.l2 B hB1 s (T.map (CT.forgetC x)) hs'
  rw [List.length_map] at hdd
  have hid : E2.fForgetC < B := by show 169 < B; omega
  refine Runs.mk (hΔ.e4 _ _ Δ_forgetTable) ?_
  unfold forgetTable
  ev_start
  · ev_run
  · have hm : T.length + 1 ≤ L + 1 := by omega
    have e1 : (T.length + 1) ^ 2 ≤ (L + 1) ^ 2 := Nat.pow_le_pow_left hm 2
    have e2 : (s + 1) * (T.length + 1) ^ 2 ≤ (s + 1) ^ 5 * (L + 1) ^ 2 := Nat.mul_le_mul hQs e1
    have e3 : T.length * (7000 * (s + 1) ^ 5) ≤ L * (7000 * (s + 1) ^ 5) := Nat.mul_le_mul_right _ hL
    have e4 : L + 1 ≤ (L + 1) ^ 2 := by nlinarith
    have e5 : L * (7000 * (s + 1) ^ 5) ≤ 7000 * (s + 1) ^ 5 * (L + 1) ^ 2 := by nlinarith
    nlinarith

/-- one call of the `flatMap` callee of the introduce step -/
theorem introCb_runs (kmax v : ℕ) (N Bs : Finset ℕ) (t : CT) (hw : t.Wf Bs kmax) (U : ℕ)
    (hU : sz t ≤ U) (hM : mx t ≤ U) (hv : v ≤ U) (hN : N.card ≤ U) (hk : kmax ≤ U)
    (hB : E3C.introCCost (U + 1) (Bs.card + kmax + 2) + 40 < B) :
    Runs Δ' B fIntroCb [toVal (kmax, v, N), toVal t] (toVal (introC kmax v N t))
      (E3C.introCCost (U + 1) (Bs.card + kmax + 2) + 30) := by
  have h := E3C.introC_runs_wf hΔ.e3 B kmax v N t Bs hw U hU hM hv hN hk
    (fun c s hc hb => E2.norm_runs_e12 hΔ.e2 hΔ.e1 B c s hc hb) E2.sz_norm_le (by omega)
  refine Runs.mk (hΔ.e4 _ _ Δ_introCb) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

/-- **introduce step**: `introTable kmax v N T = dedup (T.flatMap (introC kmax v N))`. -/
theorem introTable_runs (kmax v : ℕ) (N Bs : Finset ℕ) (T : List CT) (U Ci Lg L sOut Lp : ℕ)
    (hT : ∀ t ∈ T, t.Wf Bs kmax) (hsz : ∀ t ∈ T, sz t ≤ U) (hmx : ∀ t ∈ T, mx t ≤ U)
    (hv : v ≤ U) (hN : N.card ≤ U) (hk : kmax ≤ U)
    (hCi : E3C.introCCost (U + 1) (Bs.card + kmax + 2) ≤ Ci)
    (hLg : ∀ t ∈ T, (introC kmax v N t).length ≤ Lg) (hL : T.length ≤ L)
    (hout : ∀ e ∈ T.flatMap (introC kmax v N), sz e ≤ sOut)
    (hLp : (T.flatMap (introC kmax v N)).length ≤ Lp)
    (hB : (introCostF Ci Lg L sOut Lp + 2) ^ 2 < B) :
    Runs Δ' B fIntroTable [toVal kmax, toVal v, toVal N, toVal T] (toVal (introTable kmax v N T))
      (introCostF Ci Lg L sOut Lp) := by
  unfold introCostF at hB ⊢
  set COST := L * (Ci + 10 * Lg + 100) + 100 + 60 * (sOut + 1) * (Lp + 1) ^ 2 with hCOST
  have hC100 : 100 ≤ COST := by omega
  have hB1 : 1 < B := by
    have := Nat.pow_le_pow_left (show 2 ≤ COST + 2 by omega) 2
    omega
  have hB500 : 500 < B := by
    have h2 : (100 + 2) ^ 2 ≤ (COST + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hf : ∀ t ∈ T, Runs Δ' B fIntroCb [toVal (kmax, v, N), toVal t] (toVal (introC kmax v N t))
      (Ci + 30) := by
    intro t ht
    have hL1 : 1 ≤ L := le_trans (List.length_pos_of_mem ht) hL
    have hle : Ci + 40 + 2 ≤ COST + 2 := by
      have : Ci ≤ L * (Ci + 10 * Lg + 100) := by nlinarith
      omega
    have hb2 : E3C.introCCost (U + 1) (Bs.card + kmax + 2) + 40 < B := by
      have h3 := Nat.pow_le_pow_left hle 2
      have h4 : Ci + 40 + 2 ≤ (Ci + 40 + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
      omega
    exact (introCb_runs hΔ B kmax v N Bs t (hT t ht) U (hsz t ht) (hmx t ht) hv hN hk hb2).mono
      (by omega)
  have hflat := flatMap_runs hΔ.l1 B fIntroCb (toVal (kmax, v, N)) (introC kmax v N) (fun _ => Ci + 30) T hf
  have hsum : (T.map (fun a => Ci + 30 + 10 * (introC kmax v N a).length + 20)).sum ≤
      T.length * (Ci + 10 * Lg + 100) := by
    refine le_trans (sum_map_le_aux _ (Ci + 10 * Lg + 100) T ?_) le_rfl
    intro a ha
    have := hLg a ha
    omega
  have hdd := Lib2.dedup_runs hΔ.l2 B hB1 sOut (T.flatMap (introC kmax v N)) hout
  have hid : fIntroCb < B := by show 389 < B; omega
  refine Runs.mk (hΔ.e4 _ _ Δ_introTable) ?_
  unfold introTable
  simp only [toVal_pair] at hflat
  ev_start
  · ev_run
  · have e1 : T.length * (Ci + 10 * Lg + 100) ≤ L * (Ci + 10 * Lg + 100) := Nat.mul_le_mul_right _ hL
    have e2 : (T.flatMap (introC kmax v N)).length + 1 ≤ Lp + 1 := by omega
    have e3 : (sOut + 1) * ((T.flatMap (introC kmax v N)).length + 1) ^ 2 ≤ (sOut + 1) * (Lp + 1) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e2 2)
    nlinarith

/-- the inner `flatMap` callee of the join step: `joinC kmax ca cb` -/
theorem joinInner_runs (kmax : ℕ) (B0 : Finset ℕ) (ca cb : CT) (ha : ca.Wf B0 kmax) (hb : cb.Wf B0 kmax)
    (s Cj : ℕ) (hsa : sz ca ≤ s) (hsb : sz cb ≤ s)
    (hCj : 14000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3) ≤ Cj) (hB : (Cj + 40) ^ 2 < B) :
    Runs Δ' B fJoinInner [toVal (kmax, ca), toVal cb] (toVal (joinC kmax ca cb)) (Cj + 30) := by
  have h := E2.joinC_runs_fits hΔ.e2 hΔ.e1 B ha hb s hsa hsb
    (lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hB)
  refine Runs.mk (hΔ.e4 _ _ Δ_joinInner) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

/-- the outer `flatMap` callee: `Tb.flatMap (joinC kmax ca ·)` -/
theorem joinOuter_runs (kmax : ℕ) (B0 : Finset ℕ) (ca : CT) (Tb : List CT) (ha : ca.Wf B0 kmax)
    (hb : ∀ cb ∈ Tb, cb.Wf B0 kmax) (s Cj Lb Lj : ℕ) (hsa : sz ca ≤ s) (hsb : ∀ cb ∈ Tb, sz cb ≤ s)
    (hCj : 14000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3) ≤ Cj)
    (hLj : ∀ cb ∈ Tb, (joinC kmax ca cb).length ≤ Lj) (hLb : Tb.length ≤ Lb)
    (hB : (Cj + 40) ^ 2 < B) (hB500 : 500 < B) :
    Runs Δ' B fJoinOuter [toVal (kmax, Tb), toVal ca] (toVal (Tb.flatMap (fun cb => joinC kmax ca cb)))
      (Lb * (Cj + 10 * Lj + 50) + 40) := by
  have hf : ∀ cb ∈ Tb, Runs Δ' B fJoinInner [toVal (kmax, ca), toVal cb] (toVal (joinC kmax ca cb)) (Cj + 30) :=
    fun cb hcb => joinInner_runs hΔ B kmax B0 ca cb ha (hb cb hcb) s Cj hsa (hsb cb hcb) hCj hB
  have hflat := flatMap_runs hΔ.l1 B fJoinInner (toVal (kmax, ca)) (fun cb => joinC kmax ca cb)
    (fun _ => Cj + 30) Tb hf
  have hsum : (Tb.map (fun cb => Cj + 30 + 10 * (joinC kmax ca cb).length + 20)).sum ≤
      Tb.length * (Cj + 10 * Lj + 50) := by
    refine sum_map_le_aux _ (Cj + 10 * Lj + 50) Tb ?_
    intro a ha
    have := hLj a ha
    omega
  have hid : fJoinInner < B := by show 391 < B; omega
  refine Runs.mk (hΔ.e4 _ _ Δ_joinOuter) ?_
  simp only [toVal_pair] at hflat ⊢
  ev_start
  · ev_run
  · have e1 : Tb.length * (Cj + 10 * Lj + 50) ≤ Lb * (Cj + 10 * Lj + 50) := Nat.mul_le_mul_right _ hLb
    omega

/-- **join step**: `joinTable kmax Ta Tb = dedup (Ta.flatMap fun ca => Tb.flatMap (joinC kmax ca ·))`. -/
theorem joinTable_runs (kmax : ℕ) (B0 : Finset ℕ) (Ta Tb : List CT) (s Cj La Lb Lj sOut : ℕ)
    (ha : ∀ a ∈ Ta, a.Wf B0 kmax) (hb : ∀ b ∈ Tb, b.Wf B0 kmax)
    (hsa : ∀ a ∈ Ta, sz a ≤ s) (hsb : ∀ b ∈ Tb, sz b ≤ s)
    (hCj : 14000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3) ≤ Cj)
    (hLj : ∀ a ∈ Ta, ∀ b ∈ Tb, (joinC kmax a b).length ≤ Lj) (hLa : Ta.length ≤ La) (hLb : Tb.length ≤ Lb)
    (hLa1 : 1 ≤ La) (hLb1 : 1 ≤ Lb)
    (hout : ∀ e ∈ Ta.flatMap (fun ca => Tb.flatMap (fun cb => joinC kmax ca cb)), sz e ≤ sOut)
    (hB : (joinCostF Cj La Lb Lj sOut + 2) ^ 2 < B) :
    Runs Δ' B fJoinTable [toVal kmax, toVal Ta, toVal Tb]
      (toVal (joinTable kmax Ta Tb)) (joinCostF Cj La Lb Lj sOut) := by
  unfold joinCostF at hB ⊢
  set COST := La * (Lb * (Cj + 10 * Lj + 50) + 40 + 10 * (Lb * Lj) + 20) + 100 +
        60 * (sOut + 1) * (La * (Lb * Lj) + 1) ^ 2 with hCOST
  have hC100 : 100 ≤ COST := by omega
  have hB1 : 1 < B := by
    have := Nat.pow_le_pow_left (show 2 ≤ COST + 2 by omega) 2
    omega
  have hB500 : 500 < B := by
    have h2 : (100 + 2) ^ 2 ≤ (COST + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hLb' : Lb * (Cj + 10 * Lj + 50) ≥ Cj := by nlinarith
  have hLa' : La * (Lb * (Cj + 10 * Lj + 50) + 40 + 10 * (Lb * Lj) + 20) ≥ Cj + 40 := by
    have : Lb * (Cj + 10 * Lj + 50) + 40 + 10 * (Lb * Lj) + 20 ≤
        La * (Lb * (Cj + 10 * Lj + 50) + 40 + 10 * (Lb * Lj) + 20) := Nat.le_mul_of_pos_left _ hLa1
    omega
  have hb2 : (Cj + 40) ^ 2 < B := by
    refine lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hB
  have hf : ∀ a ∈ Ta, Runs Δ' B fJoinOuter [toVal (kmax, Tb), toVal a]
      (toVal (Tb.flatMap (fun cb => joinC kmax a cb))) (Lb * (Cj + 10 * Lj + 50) + 40) := by
    intro a haT
    exact joinOuter_runs hΔ B kmax B0 a Tb (ha a haT) hb s Cj Lb Lj (hsa a haT) hsb hCj (hLj a haT) hLb hb2 hB500
  have hflat := flatMap_runs hΔ.l1 B fJoinOuter (toVal (kmax, Tb))
    (fun a => Tb.flatMap (fun cb => joinC kmax a cb)) (fun _ => Lb * (Cj + 10 * Lj + 50) + 40) Ta hf
  have hlen : ∀ a ∈ Ta, (Tb.flatMap (fun cb => joinC kmax a cb)).length ≤ Lb * Lj := by
    intro a haT
    refine le_trans (length_flatMap_le (n := Lj) (fun b hbT => hLj a haT b hbT)) ?_
    exact Nat.mul_le_mul_right _ hLb
  have hsum : (Ta.map (fun a => Lb * (Cj + 10 * Lj + 50) + 40 + 10 * (Tb.flatMap (fun cb => joinC kmax a cb)).length + 20)).sum ≤
      Ta.length * (Lb * (Cj + 10 * Lj + 50) + 40 + 10 * (Lb * Lj) + 20) := by
    refine sum_map_le_aux _ _ Ta ?_
    intro a haT
    have := hlen a haT
    omega
  have hlenp : (Ta.flatMap (fun ca => Tb.flatMap (fun cb => joinC kmax ca cb))).length ≤ La * (Lb * Lj) :=
    le_trans (length_flatMap_le (n := Lb * Lj) hlen) (Nat.mul_le_mul_right _ hLa)
  have hdd := Lib2.dedup_runs hΔ.l2 B hB1 sOut (Ta.flatMap (fun ca => Tb.flatMap (fun cb => joinC kmax ca cb))) hout
  have hid : fJoinOuter < B := by show 392 < B; omega
  refine Runs.mk (hΔ.e4 _ _ Δ_joinTable) ?_
  unfold joinTable
  simp only [toVal_pair] at hflat ⊢
  ev_start
  · ev_run
  · have e1 : Ta.length * (Lb * (Cj + 10 * Lj + 50) + 40 + 10 * (Lb * Lj) + 20) ≤
        La * (Lb * (Cj + 10 * Lj + 50) + 40 + 10 * (Lb * Lj) + 20) := Nat.mul_le_mul_right _ hLa
    have e2 : (Ta.flatMap (fun ca => Tb.flatMap (fun cb => joinC kmax ca cb))).length + 1 ≤ La * (Lb * Lj) + 1 := by omega
    have e3 : (sOut + 1) * ((Ta.flatMap (fun ca => Tb.flatMap (fun cb => joinC kmax ca cb))).length + 1) ^ 2 ≤
        (sOut + 1) * (La * (Lb * Lj) + 1) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e2 2)
    nlinarith

end steps

end E4
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E4Arith` -/

section
set_option linter.unusedSectionVars false

/-!
# WP E4 (2): the arithmetic of the per-node cost bound

`cnode M k = (M+1)^15 · 2^(4000 (k+2)^3)`.  With `Y = (k+2)^3 ≥ 8` every polynomial factor `128 Y + 1`, every numeral
constant and every quantity `L = 2^(a Y)` is a power of two, so each node bound is a chain of `2^_ ≤ 2^_`.
All lemmas are stated for an abstract `Y ≥ 8` (the exponent shapes are the ones the P1 bounds have).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E4

theorem pw_le {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

theorem lin_two_pow (Y : ℕ) (hY : 1 ≤ Y) : 128 * Y + 1 ≤ 2 ^ (9 * Y) := by
  have h1 : Y < 2 ^ Y := Nat.lt_two_pow_self
  have h2 : 128 * Y + 1 ≤ 2 ^ 8 * 2 ^ Y := by omega
  calc 128 * Y + 1 ≤ 2 ^ 8 * 2 ^ Y := h2
    _ = 2 ^ (8 + Y) := by rw [pow_add]
    _ ≤ 2 ^ (9 * Y) := pw_le (by omega)

theorem sq_two_pow (a : ℕ) : (2 ^ a + 1) ^ 2 ≤ 2 ^ (2 * a + 2) := by
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h2 : 2 ^ a + 1 ≤ 2 * 2 ^ a := by omega
  calc (2 ^ a + 1) ^ 2 ≤ (2 * 2 ^ a) ^ 2 := Nat.pow_le_pow_left h2 2
    _ = 2 ^ (2 * a + 2) := by ring

/-- the bound on the cost of the per-node work -/
def cnode (M k : ℕ) : ℕ := (M + 1) ^ 15 * 2 ^ (4000 * (k + 2) ^ 3)

theorem Q_ge (M : ℕ) : 1 ≤ (M + 1) ^ 15 := Nat.one_le_pow _ _ (by omega)

/-- `t ≤ 2^e` with `e ≤ 3990 Y` gives `t ≤ Q · R` (the common ceiling `Q = (M+1)^15`, `R = 2^(3990 Y)`) -/
theorem to_ceiling {t e Y : ℕ} (M : ℕ) (h : t ≤ 2 ^ e) (he : e ≤ 3990 * Y) :
    t ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) :=
  le_trans (le_trans h (pw_le he)) (Nat.le_mul_of_pos_left _ (Q_ge M))

theorem ceiling_sum {Y M : ℕ} (hY : 1 ≤ Y) {S : ℕ} (hS : S ≤ 8 * ((M + 1) ^ 15 * 2 ^ (3990 * Y))) :
    S ≤ (M + 1) ^ 15 * 2 ^ (4000 * Y) := by
  have h1 : 8 * ((M + 1) ^ 15 * 2 ^ (3990 * Y)) = (M + 1) ^ 15 * 2 ^ (3990 * Y + 3) := by rw [pow_add]; ring
  have h2 : 2 ^ (3990 * Y + 3) ≤ 2 ^ (4000 * Y) := pw_le (by omega)
  calc S ≤ 8 * ((M + 1) ^ 15 * 2 ^ (3990 * Y)) := hS
    _ = (M + 1) ^ 15 * 2 ^ (3990 * Y + 3) := h1
    _ ≤ (M + 1) ^ 15 * 2 ^ (4000 * Y) := Nat.mul_le_mul_left _ h2

theorem const_le_ceiling (M Y c e : ℕ) (hc : c ≤ 2 ^ e) (he : e ≤ 3990 * Y) :
    c ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := to_ceiling M hc he

/-! ### forget node -/

theorem forget_node (Y M : ℕ) (hY : 8 ≤ Y) :
    200 + 7300 * (128 * Y + 1) ^ 5 * (2 ^ (96 * Y) + 1) ^ 2 ≤ (M + 1) ^ 15 * 2 ^ (4000 * Y) := by
  have a1 : (128 * Y + 1) ^ 5 ≤ 2 ^ (45 * Y) := by
    calc (128 * Y + 1) ^ 5 ≤ (2 ^ (9 * Y)) ^ 5 := Nat.pow_le_pow_left (lin_two_pow Y (by omega)) 5
      _ = 2 ^ (45 * Y) := by rw [← pow_mul]; ring_nf
  have a2 := sq_two_pow (96 * Y)
  have a3 : 7300 * (128 * Y + 1) ^ 5 * (2 ^ (96 * Y) + 1) ^ 2 ≤ 2 ^ (13 + 45 * Y + (2 * (96 * Y) + 2)) := by
    calc 7300 * (128 * Y + 1) ^ 5 * (2 ^ (96 * Y) + 1) ^ 2 ≤ 2 ^ 13 * 2 ^ (45 * Y) * 2 ^ (2 * (96 * Y) + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) a1) a2
      _ = 2 ^ (13 + 45 * Y + (2 * (96 * Y) + 2)) := by rw [← pow_add, ← pow_add]
  have a4 := to_ceiling (Y := Y) M a3 (by omega)
  have a5 : 200 ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) :=
    const_le_ceiling M Y 200 8 (by norm_num) (by omega)
  refine ceiling_sum (by omega) ?_
  omega

/-! ### intro node -/

theorem intro_node (Y M X : ℕ) (hY : 8 ≤ Y) (hX : X ≤ Y) :
    200 + 60 * M ^ 2 + X * (28 * M + 120) +
      (2 ^ (96 * Y) * (10 ^ 16 * (128 * Y + M + 1) ^ 15 * 2 ^ (3456 * Y) + 10 * 2 ^ (1728 * Y) + 100) + 100 +
        60 * (128 * Y + 1) * (2 ^ (1824 * Y) + 1) ^ 2) ≤ (M + 1) ^ 15 * 2 ^ (4000 * Y) := by
  have hQ := Q_ge M
  have hY2 : Y < 2 ^ Y := Nat.lt_two_pow_self
  -- 60 M^2
  have t2 : 60 * M ^ 2 ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := by
    have h1 : M ^ 2 ≤ (M + 1) ^ 15 := le_trans (Nat.pow_le_pow_left (Nat.le_succ M) 2)
      (Nat.pow_le_pow_right (by omega) (by norm_num))
    have h2 : 60 ≤ 2 ^ (3990 * Y) := le_trans (by norm_num : 60 ≤ 2 ^ 6) (pw_le (by omega))
    calc 60 * M ^ 2 ≤ 2 ^ (3990 * Y) * (M + 1) ^ 15 := Nat.mul_le_mul h2 h1
      _ = _ := by ring
  -- X (28 M + 120)
  have t3 : X * (28 * M + 120) ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := by
    have h1 : 28 * M + 120 ≤ 2 ^ 7 * (M + 1) ^ 15 := by
      have : M + 1 ≤ (M + 1) ^ 15 := by
        calc M + 1 = (M + 1) ^ 1 := (pow_one _).symm
          _ ≤ (M + 1) ^ 15 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega
    have h2 : X ≤ 2 ^ Y := le_trans hX (le_of_lt hY2)
    calc X * (28 * M + 120) ≤ 2 ^ Y * (2 ^ 7 * (M + 1) ^ 15) := Nat.mul_le_mul h2 h1
      _ = (M + 1) ^ 15 * 2 ^ (Y + 7) := by rw [pow_add]; ring
      _ ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := Nat.mul_le_mul_left _ (pw_le (by omega))
  -- the introC term
  have hb : 128 * Y + M + 1 ≤ 2 ^ (9 * Y) * (M + 1) := by
    have h1 := lin_two_pow Y (by omega)
    have h2 : 128 * Y + M + 1 ≤ (128 * Y + 1) * (M + 1) := by nlinarith
    exact le_trans h2 (Nat.mul_le_mul_right _ h1)
  have t4 : 2 ^ (96 * Y) * (10 ^ 16 * (128 * Y + M + 1) ^ 15 * 2 ^ (3456 * Y)) ≤
      (M + 1) ^ 15 * 2 ^ (3990 * Y) := by
    have h1 : (128 * Y + M + 1) ^ 15 ≤ 2 ^ (135 * Y) * (M + 1) ^ 15 := by
      calc (128 * Y + M + 1) ^ 15 ≤ (2 ^ (9 * Y) * (M + 1)) ^ 15 := Nat.pow_le_pow_left hb 15
        _ = 2 ^ (135 * Y) * (M + 1) ^ 15 := by rw [mul_pow, ← pow_mul]; ring_nf
    have h2 : 10 ^ 16 ≤ 2 ^ 54 := by norm_num
    calc 2 ^ (96 * Y) * (10 ^ 16 * (128 * Y + M + 1) ^ 15 * 2 ^ (3456 * Y))
        ≤ 2 ^ (96 * Y) * (2 ^ 54 * (2 ^ (135 * Y) * (M + 1) ^ 15) * 2 ^ (3456 * Y)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul h2 h1))
      _ = (M + 1) ^ 15 * 2 ^ (96 * Y + 54 + 135 * Y + 3456 * Y) := by ring
      _ ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := Nat.mul_le_mul_left _ (pw_le (by omega))
  have t5 : 2 ^ (96 * Y) * (10 * 2 ^ (1728 * Y)) ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := by
    have : 2 ^ (96 * Y) * (10 * 2 ^ (1728 * Y)) ≤ 2 ^ (96 * Y) * (2 ^ 4 * 2 ^ (1728 * Y)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by norm_num))
    refine to_ceiling M (le_trans this (le_of_eq ?_)) (e := 96 * Y + (4 + 1728 * Y)) (by omega)
    ring
  have t6 : 2 ^ (96 * Y) * 100 ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := by
    have : 2 ^ (96 * Y) * 100 ≤ 2 ^ (96 * Y) * 2 ^ 7 :=
      Nat.mul_le_mul_left _ (by norm_num)
    refine to_ceiling M (le_trans this (le_of_eq ?_)) (e := 96 * Y + 7) (by omega)
    ring
  have t8 : 60 * (128 * Y + 1) * (2 ^ (1824 * Y) + 1) ^ 2 ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := by
    have a1 := lin_two_pow Y (by omega)
    have a2 := sq_two_pow (1824 * Y)
    have : 60 * (128 * Y + 1) * (2 ^ (1824 * Y) + 1) ^ 2 ≤ 2 ^ 6 * 2 ^ (9 * Y) * 2 ^ (2 * (1824 * Y) + 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) a1) a2
    refine to_ceiling M (le_trans this (le_of_eq ?_)) (e := 6 + 9 * Y + (2 * (1824 * Y) + 2)) (by omega)
    rw [← pow_add, ← pow_add]
  have t1 : 200 ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := const_le_ceiling M Y 200 8 (by norm_num) (by omega)
  have t7 : 100 ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := const_le_ceiling M Y 100 7 (by norm_num) (by omega)
  refine ceiling_sum (by omega) ?_
  have e : 2 ^ (96 * Y) * (10 ^ 16 * (128 * Y + M + 1) ^ 15 * 2 ^ (3456 * Y) + 10 * 2 ^ (1728 * Y) + 100) =
      2 ^ (96 * Y) * (10 ^ 16 * (128 * Y + M + 1) ^ 15 * 2 ^ (3456 * Y)) + 2 ^ (96 * Y) * (10 * 2 ^ (1728 * Y)) +
        2 ^ (96 * Y) * 100 := by ring
  rw [e]
  omega

/-! ### join node -/

theorem join_node (Y M : ℕ) (hY : 8 ≤ Y) :
    200 + (2 ^ (96 * Y) * (2 ^ (96 * Y) * (14000 * (128 * Y + 1) * 2 ^ (1296 * Y) + 10 * 2 ^ (432 * Y) + 50) + 40 +
        10 * (2 ^ (96 * Y) * 2 ^ (432 * Y)) + 20) + 100 +
      60 * (128 * Y + 1) * (2 ^ (96 * Y) * (2 ^ (96 * Y) * 2 ^ (432 * Y)) + 1) ^ 2) ≤
      (M + 1) ^ 15 * 2 ^ (4000 * Y) := by
  have hl := lin_two_pow Y (by omega)
  -- the join cost of one call
  have c1 : 14000 * (128 * Y + 1) * 2 ^ (1296 * Y) ≤ 2 ^ (1305 * Y + 14) := by
    calc 14000 * (128 * Y + 1) * 2 ^ (1296 * Y) ≤ 2 ^ 14 * 2 ^ (9 * Y) * 2 ^ (1296 * Y) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (by norm_num) hl)
      _ = 2 ^ (1305 * Y + 14) := by rw [← pow_add, ← pow_add]; ring_nf
  have c1' : 10 * 2 ^ (432 * Y) ≤ 2 ^ (1305 * Y + 14) := by
    calc 10 * 2 ^ (432 * Y) ≤ 2 ^ 4 * 2 ^ (432 * Y) := Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ (4 + 432 * Y) := by rw [← pow_add]
      _ ≤ 2 ^ (1305 * Y + 14) := pw_le (by omega)
  have c1'' : 50 ≤ 2 ^ (1305 * Y + 14) := le_trans (by norm_num : 50 ≤ 2 ^ 6) (pw_le (by omega))
  have cs : 14000 * (128 * Y + 1) * 2 ^ (1296 * Y) + 10 * 2 ^ (432 * Y) + 50 ≤ 2 ^ (1305 * Y + 16) := by
    have : 2 ^ (1305 * Y + 16) = 4 * 2 ^ (1305 * Y + 14) := by rw [pow_add, pow_add]; ring
    omega
  -- La * Cs
  have c2a : 2 ^ (96 * Y) * (14000 * (128 * Y + 1) * 2 ^ (1296 * Y) + 10 * 2 ^ (432 * Y) + 50) ≤
      2 ^ (1401 * Y + 16) := by
    calc _ ≤ 2 ^ (96 * Y) * 2 ^ (1305 * Y + 16) := Nat.mul_le_mul_left _ cs
      _ = 2 ^ (1401 * Y + 16) := by rw [← pow_add]; ring_nf
  have c2b : 10 * (2 ^ (96 * Y) * 2 ^ (432 * Y)) ≤ 2 ^ (1401 * Y + 16) := by
    calc 10 * (2 ^ (96 * Y) * 2 ^ (432 * Y)) ≤ 2 ^ 4 * (2 ^ (96 * Y) * 2 ^ (432 * Y)) :=
          Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ (4 + (96 * Y + 432 * Y)) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (1401 * Y + 16) := pw_le (by omega)
  have c2c : 40 ≤ 2 ^ (1401 * Y + 16) := le_trans (by norm_num : 40 ≤ 2 ^ 6) (pw_le (by omega))
  have c2d : 20 ≤ 2 ^ (1401 * Y + 16) := le_trans (by norm_num : 20 ≤ 2 ^ 5) (pw_le (by omega))
  have c2 : 2 ^ (96 * Y) * (14000 * (128 * Y + 1) * 2 ^ (1296 * Y) + 10 * 2 ^ (432 * Y) + 50) + 40 +
        10 * (2 ^ (96 * Y) * 2 ^ (432 * Y)) + 20 ≤ 2 ^ (1401 * Y + 18) := by
    have : 2 ^ (1401 * Y + 18) = 4 * 2 ^ (1401 * Y + 16) := by rw [pow_add, pow_add]; ring
    omega
  have c3 : 2 ^ (96 * Y) * (2 ^ (96 * Y) * (14000 * (128 * Y + 1) * 2 ^ (1296 * Y) + 10 * 2 ^ (432 * Y) + 50) + 40 +
        10 * (2 ^ (96 * Y) * 2 ^ (432 * Y)) + 20) ≤ 2 ^ (1497 * Y + 18) := by
    calc _ ≤ 2 ^ (96 * Y) * 2 ^ (1401 * Y + 18) := Nat.mul_le_mul_left _ c2
      _ = 2 ^ (1497 * Y + 18) := by rw [← pow_add]; ring_nf
  have c4 : 60 * (128 * Y + 1) * (2 ^ (96 * Y) * (2 ^ (96 * Y) * 2 ^ (432 * Y)) + 1) ^ 2 ≤
      2 ^ (1259 * Y + 8) := by
    have e : 2 ^ (96 * Y) * (2 ^ (96 * Y) * 2 ^ (432 * Y)) = 2 ^ (624 * Y) := by
      rw [← pow_add, ← pow_add]; ring_nf
    rw [e]
    have a2 := sq_two_pow (624 * Y)
    calc 60 * (128 * Y + 1) * (2 ^ (624 * Y) + 1) ^ 2 ≤ 2 ^ 6 * 2 ^ (9 * Y) * 2 ^ (2 * (624 * Y) + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) hl) a2
      _ = 2 ^ (6 + 9 * Y + (2 * (624 * Y) + 2)) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (1259 * Y + 8) := pw_le (by omega)
  have d1 := to_ceiling (Y := Y) M c3 (by omega)
  have d2 := to_ceiling (Y := Y) M c4 (by omega)
  have d3 : 100 ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := const_le_ceiling M Y 100 7 (by norm_num) (by omega)
  have d4 : 200 ≤ (M + 1) ^ 15 * 2 ^ (3990 * Y) := const_le_ceiling M Y 200 8 (by norm_num) (by omega)
  refine ceiling_sum (by omega) ?_
  omega

/-! ### the same bounds in terms of the step-cost functions -/

theorem forget_node' (Y M : ℕ) (hY : 8 ≤ Y) :
    200 + forgetCostF (128 * Y) (2 ^ (96 * Y)) ≤ (M + 1) ^ 15 * 2 ^ (4000 * Y) := by
  unfold forgetCostF; exact forget_node Y M hY

theorem intro_node' (Y M X : ℕ) (hY : 8 ≤ Y) (hX : X ≤ Y) :
    200 + 60 * M ^ 2 + X * (28 * M + 120) +
      introCostF (10 ^ 16 * (128 * Y + M + 1) ^ 15 * 2 ^ (3456 * Y)) (2 ^ (1728 * Y)) (2 ^ (96 * Y)) (128 * Y)
        (2 ^ (1824 * Y)) ≤ (M + 1) ^ 15 * 2 ^ (4000 * Y) := by
  unfold introCostF; exact intro_node Y M X hY hX

theorem join_node' (Y M : ℕ) (hY : 8 ≤ Y) :
    200 + joinCostF (14000 * (128 * Y + 1) * 2 ^ (1296 * Y)) (2 ^ (96 * Y)) (2 ^ (96 * Y)) (2 ^ (432 * Y))
      (128 * Y) ≤ (M + 1) ^ 15 * 2 ^ (4000 * Y) := by
  unfold joinCostF; exact join_node Y M hY

end E4
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E4Asm` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E4 (3b): the three recursion steps of `fTables`, with the callee facts as hypotheses

Small contexts (no numerics), so that `ev_run` and its `simp` side goals are fast.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E4

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT

section asm
variable {Δ' : ℕ → Option Tm} (hΔ : Ext4 Δ') (B : ℕ)
include hΔ

theorem forget_assemble (x : List ℕ) (k y : ℕ) (c : NT) (T R : List CT) (Cc CF C : ℕ) (hB : 500 < B)
    (IH : Runs Δ' B fTables [toVal x, toVal k, toVal c] (toVal T) Cc)
    (hF : Runs Δ' B fForgetTable [toVal y, toVal T] (toVal R) CF) (hC : 60 + Cc + CF ≤ C) :
    Runs Δ' B fTables [toVal x, toVal k, toVal (NT.forget y c)] (toVal R) C := by
  refine Runs.mk (hΔ.e4 _ _ Δ_tables) ?_
  simp only [toVal_nt_forget]
  ev_start
  · ev_run
  · omega

theorem intro_assemble (x : List ℕ) (k v : ℕ) (c : NT) (T R : List CT) (N : Finset ℕ) (Cc Cbag Cnb CI C : ℕ)
    (hB : 500 < B) (hk : k + 1 < B)
    (IH : Runs Δ' B fTables [toVal x, toVal k, toVal c] (toVal T) Cc)
    (hbag : Runs Δ' B fNtBag [toVal c] (toVal c.bag) Cbag)
    (hnb : Runs Δ' B fNbrs [toVal x, toVal v, toVal c.bag] (toVal N) Cnb)
    (hI : Runs Δ' B fIntroTable [toVal (k + 1), toVal v, toVal N, toVal T] (toVal R) CI)
    (hC : 100 + Cc + Cbag + Cnb + CI ≤ C) :
    Runs Δ' B fTables [toVal x, toVal k, toVal (NT.intro v c)] (toVal R) C := by
  refine Runs.mk (hΔ.e4 _ _ Δ_tables) ?_
  simp only [toVal_nt_intro]
  ev_start
  · ev_run
  · omega

theorem join_assemble (x : List ℕ) (k : ℕ) (a b : NT) (Ta Tb : List CT) (R : List CT) (Ca Cb CJ C : ℕ)
    (hB : 500 < B) (hk : k + 1 < B)
    (IHa : Runs Δ' B fTables [toVal x, toVal k, toVal a] (toVal Ta) Ca)
    (IHb : Runs Δ' B fTables [toVal x, toVal k, toVal b] (toVal Tb) Cb)
    (hJ : Runs Δ' B fJoinTable [toVal (k + 1), toVal Ta, toVal Tb] (toVal R) CJ)
    (hC : 100 + Ca + Cb + CJ ≤ C) :
    Runs Δ' B fTables [toVal x, toVal k, toVal (NT.join a b)] (toVal R) C := by
  refine Runs.mk (hΔ.e4 _ _ Δ_tables) ?_
  simp only [toVal_nt_join]
  ev_start
  · ev_run
  · omega

end asm

end E4
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E4Tables` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E4 (4): `tables` as an F-function (recursion over the nice tree), with the closed-form cost

`tables_runs`: for a good nice tree of width `≤ k + 1` whose size / labels are `≤ M`, on a graph word of length `≤ M`,
the function `fTables` computes `tables (adjOfWord x) k nt` within `nt.size · cnode M k` steps, where
`cnode M k = (M+1)^15 · 2^(4000 (k+2)^3)`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E4

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT

theorem Y_ge (k : ℕ) : 8 ≤ (k + 2) ^ 3 := by
  have : 2 ^ 3 ≤ (k + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  simpa using this

theorem X_le_Y (k : ℕ) : k + 2 ≤ (k + 2) ^ 3 := Nat.le_self_pow (by norm_num) _

theorem cnode_ge (M k : ℕ) : 1000 ≤ cnode M k := by
  unfold cnode
  have h1 := Q_ge M
  have hY := Y_ge k
  have h2 : 1000 ≤ 2 ^ (4000 * (k + 2) ^ 3) :=
    le_trans (by norm_num : 1000 ≤ 2 ^ 10) (pw_le (by omega))
  calc 1000 ≤ 2 ^ (4000 * (k + 2) ^ 3) := h2
    _ ≤ (M + 1) ^ 15 * 2 ^ (4000 * (k + 2) ^ 3) := Nat.le_mul_of_pos_left _ h1

theorem mx_intro_le (v : ℕ) (c : NT) : mx c ≤ mx (NT.intro v c) := by
  simp only [mx, toVal_nt_intro, Val.maxNat]; omega
theorem mx_forget_le (v : ℕ) (c : NT) : mx c ≤ mx (NT.forget v c) := by
  simp only [mx, toVal_nt_forget, Val.maxNat]; omega
theorem mx_join_left_le (a b : NT) : mx a ≤ mx (NT.join a b) := by
  simp only [mx, toVal_nt_join, Val.maxNat]; omega
theorem mx_join_right_le (a b : NT) : mx b ≤ mx (NT.join a b) := by
  simp only [mx, toVal_nt_join, Val.maxNat]; omega

/-! ### isolated numerics -/

theorem b500_of {B C S : ℕ} (hC : 1000 ≤ C) (hS : 1 ≤ S) (hB : (S * C + 2) ^ 2 < B) : 500 < B := by
  have h1 : 1000 ≤ S * C := le_trans hC (Nat.le_mul_of_pos_left _ hS)
  have h2 : (1000 + 2) ^ 2 ≤ (S * C + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem sq_size_mono {B a b C : ℕ} (h : a ≤ b) (hB : (b * C + 2) ^ 2 < B) : (a * C + 2) ^ 2 < B :=
  sq_lt_of_le (Nat.mul_le_mul_right _ h) hB

theorem sq_cost_le {B c C S : ℕ} (hc : c ≤ C) (hS : 1 ≤ S) (hB : (S * C + 2) ^ 2 < B) : (c + 2) ^ 2 < B :=
  sq_lt_of_le (le_trans hc (Nat.le_mul_of_pos_left _ hS)) hB

theorem cost_forget (s C F : ℕ) (h : 200 + F ≤ C) : 60 + s * C + F ≤ (s + 1) * C := by
  have : (s + 1) * C = s * C + C := by ring
  omega

theorem cost_join (a b C F : ℕ) (h : 200 + F ≤ C) : 100 + a * C + b * C + F ≤ (a + b + 1) * C := by
  have : (a + b + 1) * C = a * C + b * C + C := by ring
  omega

theorem cost_intro (s C Cbag Cnb CI M X : ℕ) (h : 200 + 60 * M ^ 2 + X * (28 * M + 120) + CI ≤ C)
    (hbag : Cbag ≤ 60 * M ^ 2) (hnb : Cnb ≤ X * (28 * M + 120) + 60) :
    100 + s * C + Cbag + Cnb + CI ≤ (s + 1) * C := by
  have : (s + 1) * C = s * C + C := by ring
  omega

theorem sz_sq_le {s M : ℕ} (h : s ≤ M) : 60 * s ^ 2 ≤ 60 * M ^ 2 :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2)

theorem nbrs_cost_le {c X L M : ℕ} (hc : c ≤ X) (hL : L ≤ M) : c * (28 * L + 120) + 60 ≤ X * (28 * M + 120) + 60 := by
  have := Nat.mul_le_mul hc (show 28 * L + 120 ≤ 28 * M + 120 by omega)
  omega

section tables
variable {Δ' : ℕ → Option Tm} (hΔ : Ext4 Δ') (B : ℕ)
include hΔ

theorem tables_runs (x : List ℕ) (k M : ℕ) (hxM : x.length ≤ M) (hn : (nOfWord x) ^ 2 < B) (hk : k + 2 < B) :
    ∀ nt : NT, nt.Good (adjOfWord x) → nt.toRT.Width (k + 1) → sz nt ≤ M → mx nt ≤ M →
      (nt.size * cnode M k + 2) ^ 2 < B →
      Runs Δ' B fTables [toVal x, toVal k, toVal nt] (toVal (tables (adjOfWord x) k nt))
        (nt.size * cnode M k) := by
  intro nt
  induction nt with
  | leaf =>
    intro hg hw hs hm hB
    have hc := cnode_ge M k
    have hsz : NT.size NT.leaf = 1 := rfl
    rw [hsz] at hB ⊢
    have hB500 : 500 < B := b500_of hc le_rfl hB
    have e : toVal (tables (adjOfWord x) k NT.leaf) =
        Val.cons (Val.cons (.nat 0) (.cons (.cons (.nat 0) (.nat 0)) (.nat 0))) (.nat 0) := by
      simp only [tables, CT.start, toVal_cons, toVal_ct, toVal_empty_finset, toVal_nil, toVal_nat]
    rw [e]
    refine Runs.mk (hΔ.e4 _ _ Δ_tables) ?_
    simp only [toVal_nt_leaf]
    ev_start
    · ev_run
    · omega
  | forget y c ih =>
    intro hg hw hs hm hB
    have hgc : c.Good (adjOfWord x) := hg.2
    have hwc : c.toRT.Width (k + 1) := NT.width_forget hw
    have hsc : sz c ≤ M := by have := sz_nt_forget y c; omega
    have hmc : mx c ≤ M := le_trans (mx_forget_le y c) hm
    have hcn := cnode_ge M k
    have hsize : (NT.forget y c).size = c.size + 1 := rfl
    have hB500 : 500 < B := b500_of hcn (by omega) hB
    have hB' := hB
    rw [hsize] at hB'
    have hBc : (c.size * cnode M k + 2) ^ 2 < B := sq_size_mono (Nat.le_succ _) hB'
    have hfn : 200 + forgetCostF (128 * (k + 2) ^ 3) (2 ^ (96 * (k + 2) ^ 3)) ≤ cnode M k :=
      forget_node' ((k + 2) ^ 3) M (Y_ge k)
    have IH := ih hgc hwc hsc hmc hBc
    have hF := forgetTable_runs hΔ B y (tables (adjOfWord x) k c) (128 * (k + 2) ^ 3) (2 ^ (96 * (k + 2) ^ 3))
      (tables_sz_le hgc hwc) (tables_length_le_pow hgc hwc)
      (sq_cost_le (S := (NT.forget y c).size) (by omega) (by rw [hsize]; omega) hB)
    have e : tables (adjOfWord x) k (NT.forget y c) = forgetTable y (tables (adjOfWord x) k c) := rfl
    rw [e]
    refine forget_assemble hΔ B x k y c _ _ _ _ _ hB500 IH hF ?_
    rw [hsize]
    exact cost_forget _ _ _ hfn
  | join a b iha ihb =>
    intro hg hw hs hm hB
    have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good (adjOfWord x) a ∧ NT.Good (adjOfWord x) b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adjOfWord x u v = true ∨ adjOfWord x v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
    obtain ⟨hab, -, hga, hgb, -⟩ := hg'
    have hwa : a.toRT.Width (k + 1) := NT.width_join_left hw
    have hwb : b.toRT.Width (k + 1) := NT.width_join_right hw
    have hsab := sz_nt_join a b
    have hsa : sz a ≤ M := by omega
    have hsb : sz b ≤ M := by omega
    have hma : mx a ≤ M := le_trans (mx_join_left_le a b) hm
    have hmb : mx b ≤ M := le_trans (mx_join_right_le a b) hm
    have hcn := cnode_ge M k
    have hsize : (NT.join a b).size = a.size + b.size + 1 := rfl
    have hB500 : 500 < B := b500_of hcn (by omega) hB
    have hB' := hB
    rw [hsize] at hB'
    have hBa : (a.size * cnode M k + 2) ^ 2 < B := sq_size_mono (by omega) hB'
    have hBb : (b.size * cnode M k + 2) ^ 2 < B := sq_size_mono (by omega) hB'
    have IHa := iha hga hwa hsa hma hBa
    have IHb := ihb hgb hwb hsb hmb hBb
    have hjn : 200 + joinCostF (14000 * (128 * (k + 2) ^ 3 + 1) * 2 ^ (1296 * (k + 2) ^ 3))
        (2 ^ (96 * (k + 2) ^ 3)) (2 ^ (96 * (k + 2) ^ 3)) (2 ^ (432 * (k + 2) ^ 3)) (128 * (k + 2) ^ 3) ≤
        cnode M k := join_node' ((k + 2) ^ 3) M (Y_ge k)
    have hcard : a.bag.card ≤ k + 2 := bag_card_le_of_width hwa
    have hs3 : a.bag.card + (k + 1) + 2 ≤ 3 * (k + 2) := by omega
    have hs33 : (a.bag.card + (k + 1) + 2) ^ 3 ≤ 27 * (k + 2) ^ 3 := by
      calc (a.bag.card + (k + 1) + 2) ^ 3 ≤ (3 * (k + 2)) ^ 3 := Nat.pow_le_pow_left hs3 3
        _ = 27 * (k + 2) ^ 3 := by ring
    have hCj : 14000 * (128 * (k + 2) ^ 3 + 1) * 2 ^ (48 * (a.bag.card + (k + 1) + 2) ^ 3) ≤
        14000 * (128 * (k + 2) ^ 3 + 1) * 2 ^ (1296 * (k + 2) ^ 3) :=
      Nat.mul_le_mul_left _ (pw_le (by omega))
    have hwfa : ∀ c ∈ tables (adjOfWord x) k a, c.Wf a.bag (k + 1) := fun c hc => tables_wf hga c hc
    have hwfb : ∀ c ∈ tables (adjOfWord x) k b, c.Wf a.bag (k + 1) := fun c hc => by
      rw [hab]; exact tables_wf hgb c hc
    have hmem : ∀ e, e ∈ (tables (adjOfWord x) k a).flatMap
        (fun ca => (tables (adjOfWord x) k b).flatMap (fun cb => joinC (k + 1) ca cb)) →
        e ∈ tables (adjOfWord x) k (NT.join a b) := by
      intro e he
      show e ∈ joinTable (k + 1) (tables (adjOfWord x) k a) (tables (adjOfWord x) k b)
      simp only [joinTable, List.mem_dedup]
      exact he
    have hJ := joinTable_runs hΔ B (k + 1) a.bag (tables (adjOfWord x) k a) (tables (adjOfWord x) k b)
      (128 * (k + 2) ^ 3) (14000 * (128 * (k + 2) ^ 3 + 1) * 2 ^ (1296 * (k + 2) ^ 3))
      (2 ^ (96 * (k + 2) ^ 3)) (2 ^ (96 * (k + 2) ^ 3)) (2 ^ (432 * (k + 2) ^ 3)) (128 * (k + 2) ^ 3)
      hwfa hwfb (tables_sz_le hga hwa) (tables_sz_le hgb hwb) hCj
      (fun a' ha' b' hb' => joinC_length_le_k hcard (hwfa a' ha') (hwfb b' hb'))
      (tables_length_le_pow hga hwa) (tables_length_le_pow hgb hwb) Nat.one_le_two_pow Nat.one_le_two_pow
      (fun e he => tables_sz_le hg hw e (hmem e he))
      (sq_cost_le (S := (NT.join a b).size) (by omega) (by rw [hsize]; omega) hB)
    have e : tables (adjOfWord x) k (NT.join a b) =
        joinTable (k + 1) (tables (adjOfWord x) k a) (tables (adjOfWord x) k b) := rfl
    rw [e]
    have hk1 : k + 1 < B := by omega
    refine join_assemble hΔ B x k a b _ _ _ _ _ _ _ hB500 hk1 IHa IHb hJ ?_
    rw [hsize]
    exact cost_join _ _ _ _ hjn
  | intro v c ih =>
    intro hg hw hs hm hB
    have hgfull := hg
    obtain ⟨hvB, -, -, hgc⟩ := hg
    have hwc : c.toRT.Width (k + 1) := NT.width_intro hw
    have hsc : sz c ≤ M := by have := sz_nt_intro v c; omega
    have hmc : mx c ≤ M := le_trans (mx_intro_le v c) hm
    have hvM : v ≤ M := le_trans (le_mx_nt (NT.intro v c) (by simp [NT.mentioned])) hm
    have hbagM : ∀ u ∈ c.bag, u ≤ M := fun u hu => le_trans (le_mx_nt c (bag_subset_mentioned c hu)) hmc
    have hcn := cnode_ge M k
    have hsize : (NT.intro v c).size = c.size + 1 := rfl
    have hB500 : 500 < B := b500_of hcn (by omega) hB
    have hB' := hB
    rw [hsize] at hB'
    have hBc : (c.size * cnode M k + 2) ^ 2 < B := sq_size_mono (Nat.le_succ _) hB'
    have IH := ih hgc hwc hsc hmc hBc
    have hin : 200 + 60 * M ^ 2 + (k + 2) * (28 * M + 120) +
        introCostF (10 ^ 16 * (128 * (k + 2) ^ 3 + M + 1) ^ 15 * 2 ^ (3456 * (k + 2) ^ 3))
          (2 ^ (1728 * (k + 2) ^ 3)) (2 ^ (96 * (k + 2) ^ 3)) (128 * (k + 2) ^ 3) (2 ^ (1824 * (k + 2) ^ 3)) ≤
        cnode M k := intro_node' ((k + 2) ^ 3) M (k + 2) (Y_ge k) (X_le_Y k)
    have hcard : c.bag.card ≤ k + 2 := bag_card_le_of_width hwc
    have hs3 : c.bag.card + (k + 1) + 2 ≤ 3 * (k + 2) := by omega
    have hs33 : (c.bag.card + (k + 1) + 2) ^ 3 ≤ 27 * (k + 2) ^ 3 := by
      calc (c.bag.card + (k + 1) + 2) ^ 3 ≤ (3 * (k + 2)) ^ 3 := Nat.pow_le_pow_left hs3 3
        _ = 27 * (k + 2) ^ 3 := by ring
    have hCi : E3C.introCCost (128 * (k + 2) ^ 3 + M + 1) (c.bag.card + (k + 1) + 2) ≤
        10 ^ 16 * (128 * (k + 2) ^ 3 + M + 1) ^ 15 * 2 ^ (3456 * (k + 2) ^ 3) := by
      unfold E3C.introCCost
      exact Nat.mul_le_mul_left _ (pw_le (by omega))
    have hwf : ∀ t ∈ tables (adjOfWord x) k c, t.Wf c.bag (k + 1) := fun t ht => tables_wf hgc t ht
    have hYk := X_le_Y k
    have hmem : ∀ e, e ∈ (tables (adjOfWord x) k c).flatMap (introC (k + 1) v (nbrs (adjOfWord x) v c.bag)) →
        e ∈ tables (adjOfWord x) k (NT.intro v c) := by
      intro e he
      show e ∈ introTable (k + 1) v (nbrs (adjOfWord x) v c.bag) (tables (adjOfWord x) k c)
      simp only [introTable, List.mem_dedup]
      exact he
    have hNc : (nbrs (adjOfWord x) v c.bag).card ≤ 128 * (k + 2) ^ 3 + M := by
      have h1 : nbrs (adjOfWord x) v c.bag ⊆ c.bag := Finset.filter_subset _ _
      have := Finset.card_le_card h1
      omega
    have hI := introTable_runs hΔ B (k + 1) v (nbrs (adjOfWord x) v c.bag) c.bag (tables (adjOfWord x) k c)
      (128 * (k + 2) ^ 3 + M) (10 ^ 16 * (128 * (k + 2) ^ 3 + M + 1) ^ 15 * 2 ^ (3456 * (k + 2) ^ 3))
      (2 ^ (1728 * (k + 2) ^ 3)) (2 ^ (96 * (k + 2) ^ 3)) (128 * (k + 2) ^ 3) (2 ^ (1824 * (k + 2) ^ 3))
      hwf (fun t ht => le_trans (tables_sz_le hgc hwc t ht) (Nat.le_add_right _ _))
      (fun t ht => mx_ct_le_of_wf (hwf t ht) (fun u hu => le_trans (hbagM u hu) (Nat.le_add_left _ _))
        (by omega))
      (by omega) hNc (by omega) hCi
      (fun t ht => introC_length_le hcard (hwf t ht)) (tables_length_le_pow hgc hwc)
      (fun e he => tables_sz_le hgfull hw e (hmem e he)) (introTable_pre_le hgc hwc _)
      (sq_cost_le (S := (NT.intro v c).size) (by omega) (by rw [hsize]; omega) hB)
    have hbag := ntBag_runs hΔ B hB500 c
    have hnb := nbrs_runs hΔ B x v c.bag hB500 hn
    have e : tables (adjOfWord x) k (NT.intro v c) =
        introTable (k + 1) v (nbrs (adjOfWord x) v c.bag) (tables (adjOfWord x) k c) := rfl
    rw [e]
    have hk1 : k + 1 < B := by omega
    refine intro_assemble hΔ B x k v c _ _ _ _ _ _ _ _ hB500 hk1 IH hbag hnb hI ?_
    rw [hsize]
    exact cost_intro _ _ _ _ _ M (k + 2) hin (sz_sq_le hsc) (nbrs_cost_le hcard hxM)

end tables

end E4
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E4` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E4: `tables` is computed in the table `e4Tbl` (ids `384 … 396`) — `E_tables`

`e4Tbl : ℕ → Option Tm` (`E4Defs`); `e4Δ = layerΔ Lib.Δ 128 e4Tbl`.  Every theorem is stated for an arbitrary table `Δ'`
with `Ext4 Δ'` (it contains the tables of E1, E2 (with `ringTypList` at `152`), E3 and `e4Δ`); the assembly obtains
`Ext4` from `E4Assembly.ext4_asm`.

| Lean function | id | arguments | theorem | cost |
|---|---|---|---|---|
| `adjOfWord x u v` | `fAdjW = 384` | `[x, u, v]` | `adjW_runs` | `28 |x| + 60` (`E4Base`) |
| `nbrs (adjOfWord x) v B` | `fNbrs = 386` | `[x, v, B]` | `nbrs_runs` | `|B| (28 |x| + 120) + 60` (`E4Base`) |
| `NT.bag nt` | `fNtBag = 387` | `[nt]` | `ntBag_runs` | `60 (sz nt)^2` (`E4Base`) |
| `forgetTable` | `fForgetTable = 388` | `[x, T]` | `forgetTable_runs` | `7300 (s+1)^5 (L+1)^2` (`E4Steps`) |
| `introTable` | `fIntroTable = 390` | `[kmax, v, N, T]` | `introTable_runs` | `introCostF` (`E4Steps`) |
| `joinTable` | `fJoinTable = 393` | `[kmax, Ta, Tb]` | `joinTable_runs` | `joinCostF` (`E4Steps`) |
| **`tables`** | `fTables = 394` | `[x, k, nt]` | **`tables_runs`** (`E4Tables`) | `nt.size · cnode M k` |
| `tables` (packed) | `fTablesUn = 395` | `[(x, k, nt)]` | **`E_tables`** | `(|x| + sz nt + 1)^16 · 2^(4000 (k+2)^3)` |
| `(tables …).head?` | `fTablesFirst = 396` | `[x, k, nt]` | `tables_first_runs` | as `tables`, `+ 40` |

`cnode M k = (M+1)^15 · 2^(4000 (k+2)^3)` with `M ≥ |x|, sz nt, mx nt`.  Adjacency is read from the word `x`
(`adjOfWord`, as in `proofs-todo/Machine.lean`); **no symmetry and no well-formedness of the word is needed** (`nth` returns `0`
out of range, exactly `List.getD`); the hypotheses are `nt.Good (adjOfWord x)` and `nt.toRT.Width (k+1)`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E4

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT

/-- the side conditions of the machine layer (`ntOk` of `proofs-todo/Machine.lean`) -/
def ntOk (x : List ℕ) (k : ℕ) (nt : NT) : Prop := nt.Good (adjOfWord x) ∧ nt.toRT.Width (k + 1)

theorem size_le_M {nt : NT} {M : ℕ} (h : sz nt ≤ M) : nt.size ≤ M := by
  have := size_le_sz_nt nt; omega

section top
variable {Δ' : ℕ → Option Tm} (hΔ : Ext4 Δ') (B : ℕ)
include hΔ

end top

end E4
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E4Assembly` -/

section
set_option linter.unusedSectionVars false

/-!
# WP E4: the worked assembly with E1 + E2 + E3 + E4 — `tables` in the union table

`asm4Tbl = e1Tbl ∪ e2Tbl 152 ∪ e3Tbl ∪ e4Tbl` (ids `128 … 157`, `160 … 182`, `256 … 332`, `384 … 396`) and
`asm4Δ = layerΔ Lib.Δ 128 asm4Tbl`.  The assembler that also adds E5/E6 takes any table `tbl'` with
`E3.asmTbl ⊑ tbl'` and `e4Tbl ⊑ tbl'` (e.g. `orElseΔ asm4Tbl e5Tbl`) and gets `Ext4 (layerΔ Lib.Δ 128 tbl')` from
`Ext4.of_tbl`; then `E_tables` (and every other E4 theorem) holds in `layerΔ Lib.Δ 128 tbl'`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E4

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees

theorem e4Tbl_disj_asm : ∀ f b, e4Tbl f = some b → E3.asmTbl f = none := by
  intro f b h
  have h4 := (e4Tbl_lt h).1
  unfold E3.asmTbl orElseΔ
  rcases h1 : E1.e1Tbl f with _ | c1
  · rcases h2 : E2.e2Tbl E1C.fRingTypList f with _ | c2
    · rcases h3 : E3.e3Tbl f with _ | c3
      · simp
      · have := (E3.e3Tbl_lt h3).2; omega
    · have := (E2.e2Tbl_lt _ h2).2; omega
  · have := E1.e1Tbl_lt h1; omega

/-- any table containing the E1–E3 union and `e4Tbl` gives the hypotheses of every E4 theorem -/
theorem Ext4.of_tbl {tbl' : ℕ → Option Tm} (ha : E3.asmTbl ⊑ tbl') (h4 : e4Tbl ⊑ tbl') :
    Ext4 (layerΔ Lib.Δ 128 tbl') :=
  ⟨Ext.trans E3.asm_ext_e1 (Ext.layer_mono ha), Ext.trans E3.asm_ext_e2 (Ext.layer_mono ha),
    Ext.trans E3.asm_ext_e3 (Ext.layer_mono ha), Ext.layer_mono h4⟩

/-- the union of E1–E4 -/
def asm4Tbl : ℕ → Option Tm := orElseΔ E3.asmTbl e4Tbl

/-- the assembled table -/
def asm4Δ : ℕ → Option Tm := layerΔ Lib.Δ 128 asm4Tbl

end E4
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6bFind` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6b (1): `findSome?` with the cost of the *examined prefix* only

`Lib4.findSome_runs` charges every element of the list.  `extract` searches the tables with `findSome?` and each
successful candidate performs a *recursive extraction*, so charging all successful candidates would multiply the
cost by the table length at every level.  Here: `prefixSome f l` is the list of examined elements (up to and including the
first `some`), and `findSome_first_runs` charges `Cn` per non-hit and `Ch` once, for the hit only.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lib1 Lib4

/-- the elements `findSome?` examines: up to and including the first `some` -/
def prefixSome {α β : Type} (f : α → Option β) : List α → List α
  | [] => []
  | a :: l => a :: (match f a with | none => prefixSome f l | some _ => [])

theorem prefixSome_length_le {α β : Type} (f : α → Option β) : ∀ l : List α, (prefixSome f l).length ≤ l.length
  | [] => by simp [prefixSome]
  | a :: l => by
    have := prefixSome_length_le f l
    cases h : f a <;> simp [prefixSome, h] <;> omega

theorem mem_prefixSome {α β : Type} (f : α → Option β) : ∀ {l : List α} {a : α}, a ∈ prefixSome f l → a ∈ l
  | [], a, h => by simp [prefixSome] at h
  | b :: l, a, h => by
    simp only [prefixSome] at h
    cases hb : f b with
    | none =>
      simp only [hb, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (mem_prefixSome f h)
    | some c =>
      simp only [hb, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h; simp

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Lib4.Δ ⊑ Δ') (B : ℕ) {α β : Type} [ToVal α] [ToVal β]
include hΔ

/-- the prefix form of `findSome_runs` -/
theorem findSome_pre_runs (fid : ℕ) (ctx : Val) (f : α → Option β) (cf : α → ℕ) (l : List α)
    (hf : ∀ a ∈ prefixSome f l, Runs Δ' B fid [ctx, toVal a] (toVal (f a)) (cf a)) (hB : 1 < B) :
    Runs Δ' B fFindSome [.nat fid, ctx, toVal l] (toVal (l.findSome? f))
      (24 * (prefixSome f l).length + 6 + ((prefixSome f l).map cf).sum) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_findSome) ?_
    ev_start
    · ev_run
    · simp [prefixSome]
  | cons a l ih =>
    have h1 := hf a (by simp [prefixSome])
    refine Runs.mk (hΔ _ _ Δ_findSome) ?_
    cases hp : f a with
    | none =>
      have ih := ih (fun x hx => hf x (by simp only [prefixSome, hp]; exact List.mem_cons_of_mem _ hx))
      simp only [hp] at h1
      simp only [List.findSome?_cons, hp]
      ev_start
      · ev_run
      · simp only [prefixSome, hp, List.length_cons, List.map_cons, List.sum_cons]; omega
    | some b =>
      simp only [hp] at h1
      simp only [List.findSome?_cons, hp]
      ev_start
      · ev_run
      · simp only [prefixSome, hp, List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil]
        omega

end proofs

theorem sum_prefix_le {α β : Type} (f : α → Option β) (cf : α → ℕ) (Cn Ch : ℕ) :
    ∀ l : List α, (∀ a ∈ l, f a = none → cf a ≤ Cn) → (∀ a ∈ l, (f a).isSome → cf a ≤ Ch) →
      ((prefixSome f l).map cf).sum ≤ (prefixSome f l).length * Cn + Ch
  | [], _, _ => by simp [prefixSome]
  | a :: l, hn, hs => by
    have ih := sum_prefix_le f cf Cn Ch l (fun x hx => hn x (List.mem_cons_of_mem _ hx))
      (fun x hx => hs x (List.mem_cons_of_mem _ hx))
    cases hp : f a with
    | none =>
      have h1 := hn a (List.mem_cons_self ..) hp
      simp only [prefixSome, hp, List.length_cons, List.map_cons, List.sum_cons]
      nlinarith
    | some b =>
      have h1 := hs a (List.mem_cons_self ..) (by simp [hp])
      simp only [prefixSome, hp, List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      omega

section proofs2
variable {Δ' : ℕ → Option Tm} (hΔ : Lib4.Δ ⊑ Δ') (B : ℕ) {α β : Type} [ToVal α] [ToVal β]
include hΔ

/-- **`findSome?` with a per-hit cost**: non-hits cost `≤ Cn`, hits `≤ Ch`; only the first hit is charged. -/
theorem findSome_first_runs (fid : ℕ) (ctx : Val) (f : α → Option β) (cf : α → ℕ) (l : List α) (Cn Ch : ℕ)
    (hf : ∀ a ∈ l, Runs Δ' B fid [ctx, toVal a] (toVal (f a)) (cf a))
    (hn : ∀ a ∈ l, f a = none → cf a ≤ Cn) (hs : ∀ a ∈ l, (f a).isSome → cf a ≤ Ch) (hB : 1 < B) :
    Runs Δ' B fFindSome [.nat fid, ctx, toVal l] (toVal (l.findSome? f)) (24 * l.length + 6 + l.length * Cn + Ch) := by
  have h := findSome_pre_runs hΔ B fid ctx f cf l (fun a ha => hf a (mem_prefixSome f ha)) hB
  have hsum := sum_prefix_le f cf Cn Ch l hn hs
  have hl := prefixSome_length_le f l
  refine h.mono ?_
  have : (prefixSome f l).length * Cn ≤ l.length * Cn := Nat.mul_le_mul_right _ hl
  omega

end proofs2

end E6b
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6bDefs` -/

section
/-!
# WP E6b (2): the table `e6bTbl` (ids `704 … 767`) — `extract`

`extract adj k nt target` (`Chars/Alg.lean`) searches with `findSome?`; here it is the recursive F-function `fExtract`.

| id | function | arguments |
|---|---|---|
| 704 `fExtract` | `extract (adjOfWord x) k nt target` (an `Option RT`) | `[x, k, nt, target]` |
| 705 `fFgCand` | forget candidate `cq ↦ if forgetC y cq = target then extract c cq else none` | `[(x,k,y,c,target), cq]` |
| 706 `fInCand` | introduce candidate (`realIntro` after a successful recursive extraction) | `[((k+1,v,N),x,k,c,bag,target), cq]` |
| 707 `fJnOuter` | join outer candidate `ca ↦ Tb.findSome? (inner ca)` | `[((x,k,a,b,bag,target), Tb), ca]` |
| 708 `fJnInner` | join inner candidate | `[(ca,x,k,a,b,bag,target), cb]` |
| 709 `fExtractUn` | packed `fExtract` | `[(x, k, nt, target)]` |
| 710 `fExtractFirst` | `match tables … with [] => none | c :: _ => extract … c` (the extraction step of `improveC`) | `[x, k, nt]` |

The tables are computed once per node (`fTables`, E4); `bag`, `nbrs` once per node; the candidates run over the table.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open Lib1

abbrev fExtract : ℕ := 704
abbrev fFgCand : ℕ := 705
abbrev fInCand : ℕ := 706
abbrev fJnOuter : ℕ := 707
abbrev fJnInner : ℕ := 708
abbrev fExtractUn : ℕ := 709
abbrev fExtractFirst : ℕ := 710

/-- `snd` applied `n` times -/
def sndN : ℕ → Tm → Tm
  | 0, t => t
  | n + 1, t => .snd (sndN n t)

/-- the `i`-th (not last) component of a right-nested tuple -/
def comp (i : ℕ) (t : Tm) : Tm := .fst (sndN i t)

/-- the option `some (RT.node ∅ [])` -/
def leafTm : Tm := .cons (.lit 1) (.cons (.lit 0) (.lit 0))

/-- forget candidate: environment `[ctx, cq]`, `ctx = (x, k, y, c, target)` -/
def fgCandTm : Tm :=
  .ite (.call fEqV [.call E2.fForgetC [comp 2 (V 0), V 1], sndN 4 (V 0)])
    (.call fExtract [comp 0 (V 0), comp 1 (V 0), comp 3 (V 0), V 1])
    (.lit 0)

/-- introduce candidate: environment `[ctx, cq]`, `ctx = ((k+1, v, N), x, k, c, bag, target)` -/
def inCandTm : Tm :=
  .ite (.call fMem [sndN 5 (V 0), .call E4.fIntroCb [comp 0 (V 0), V 1]])
    (.letE (.call fExtract [comp 1 (V 0), comp 2 (V 0), comp 3 (V 0), V 1])
      (.ite (.isNat (V 0)) (.lit 0)
        (.call E5R.fRealIntro [.lit E3C.fIntroPlans, .fst (comp 0 (V 1)), .fst (.snd (comp 0 (V 1))),
          .snd (.snd (comp 0 (V 1))), comp 4 (V 1), .snd (V 0), sndN 5 (V 1)])))
    (.lit 0)

/-- join inner candidate: environment `[ctxN, cb]`, `ctxN = (ca, x, k, a, b, bag, target)` -/
def jnInnerTm : Tm :=
  .ite (.call fMem [sndN 6 (V 0), .call E4.fJoinInner [.cons (.add (comp 2 (V 0)) (.lit 1)) (comp 0 (V 0)), V 1]])
    (.letE (.call fExtract [comp 1 (V 0), comp 2 (V 0), comp 3 (V 0), comp 0 (V 0)])
      (.ite (.isNat (V 0)) (.lit 0)
        (.letE (.call fExtract [comp 1 (V 1), comp 2 (V 1), comp 4 (V 1), V 2])
          (.ite (.isNat (V 0)) (.lit 0)
            (.call E5D.fRealJoin [.add (comp 2 (V 2)) (.lit 1), comp 5 (V 2), .snd (V 1), .snd (V 0),
              sndN 6 (V 2)])))))
    (.lit 0)

/-- join outer candidate: environment `[ctxO, ca]`, `ctxO = (ctxJ, Tb)`, `ctxJ = (x, k, a, b, bag, target)` -/
def jnOuterTm : Tm :=
  .call Lib4.fFindSome [.lit fJnInner, .cons (V 1) (.fst (V 0)), .snd (V 0)]

/-- `extract`: environment `[x, k, nt, target]` -/
def extractTm : Tm :=
  .ite (.isNat (V 2)) leafTm
    (.ite (.eq (.fst (V 2)) (.lit 1))
      (.letE (.call E4.fTables [V 0, V 1, .snd (.snd (V 2))])
        (.letE (.call E4.fNtBag [.snd (.snd (V 3))])
          (.letE (.call E4.fNbrs [V 2, .fst (.snd (V 4)), V 0])
            (.call Lib4.fFindSome [.lit fInCand,
              .cons (.cons (.add (V 4) (.lit 1)) (.cons (.fst (.snd (V 5))) (V 0)))
                (.cons (V 3) (.cons (V 4) (.cons (.snd (.snd (V 5))) (.cons (V 1) (V 6))))), V 2]))))
      (.ite (.eq (.fst (V 2)) (.lit 2))
        (.letE (.call E4.fTables [V 0, V 1, .snd (.snd (V 2))])
          (.call Lib4.fFindSome [.lit fFgCand,
            .cons (V 1) (.cons (V 2) (.cons (.fst (.snd (V 3))) (.cons (.snd (.snd (V 3))) (V 4)))), V 0]))
        (.letE (.call E4.fTables [V 0, V 1, .fst (.snd (V 2))])
          (.letE (.call E4.fTables [V 1, V 2, .snd (.snd (V 3))])
            (.letE (.call E4.fNtBag [.fst (.snd (V 4))])
              (.call Lib4.fFindSome [.lit fJnOuter,
                .cons (.cons (V 3) (.cons (V 4) (.cons (.fst (.snd (V 5))) (.cons (.snd (.snd (V 5)))
                  (.cons (V 0) (V 6)))))) (V 1), V 2]))))))

def extractUnTm : Tm :=
  .call fExtract [.fst (V 0), .fst (.snd (V 0)), .fst (.snd (.snd (V 0))), .snd (.snd (.snd (V 0)))]

def extractFirstTm : Tm :=
  .letE (.call E4.fTables [V 0, V 1, V 2])
    (.ite (.isNat (V 0)) (.lit 0) (.call fExtract [V 1, V 2, V 3, .fst (V 0)]))

/-- the functions of WP E6b: ids `704 … 767` -/
def e6bTbl : ℕ → Option Tm := fun f =>
  match f with
  | 704 => some extractTm | 705 => some fgCandTm | 706 => some inCandTm | 707 => some jnOuterTm
  | 708 => some jnInnerTm | 709 => some extractUnTm | 710 => some extractFirstTm
  | _ => none

/-- the E6b layer on top of the library (ids `≥ 128`) -/
def e6bΔ : ℕ → Option Tm := layerΔ Lib.Δ 128 e6bTbl

theorem e6bTbl_lt {f : ℕ} {b : Tm} (h : e6bTbl f = some b) : 704 ≤ f ∧ f < 768 := by
  unfold e6bTbl at h
  split at h <;> first | (simp at h; done) | omega

theorem Δ_extract : e6bΔ fExtract = some extractTm := by
  simp [e6bΔ, layerΔ_ge e6bTbl (show 128 ≤ fExtract by decide)]; rfl
theorem Δ_fgCand : e6bΔ fFgCand = some fgCandTm := by
  simp [e6bΔ, layerΔ_ge e6bTbl (show 128 ≤ fFgCand by decide)]; rfl
theorem Δ_inCand : e6bΔ fInCand = some inCandTm := by
  simp [e6bΔ, layerΔ_ge e6bTbl (show 128 ≤ fInCand by decide)]; rfl
theorem Δ_jnOuter : e6bΔ fJnOuter = some jnOuterTm := by
  simp [e6bΔ, layerΔ_ge e6bTbl (show 128 ≤ fJnOuter by decide)]; rfl
theorem Δ_jnInner : e6bΔ fJnInner = some jnInnerTm := by
  simp [e6bΔ, layerΔ_ge e6bTbl (show 128 ≤ fJnInner by decide)]; rfl
theorem Δ_extractFirst : e6bΔ fExtractFirst = some extractFirstTm := by
  simp [e6bΔ, layerΔ_ge e6bTbl (show 128 ≤ fExtractFirst by decide)]; rfl

/-- The hypotheses on a table `Δ'` used by every theorem of WP E6b: it contains E1–E4 (`Ext4`), the E5 layers
(`E5W.Δ`, which contains `analyze … realJoin`) and the E6b layer. -/
structure Ext6 (Δ' : ℕ → Option Tm) : Prop where
  e4 : E4.Ext4 Δ'
  e5 : E5W.Δ ⊑ Δ'
  e6 : e6bΔ ⊑ Δ'

end E6b
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6bMerge` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# WP E6b (5): `realJoin` with the target-sequence length as a separate parameter

**Why this file exists.**  the original (unprimed, now removed) `mergeAR_runs` of `E5D` bounded the cost of one `findPath` call by `fpBound s L`, which contains
`3^(2(L+L)+1+s)`: the length `lw` of the *target run sequence* is bounded by the global size bound `s` (`findPathCost_le`,
hypothesis `lw ≤ s`).  For `realJoin` on the trees built by `extract`, `s` must dominate the size of the *real trees*, which
grows with `|nt|`, so that bound is exponential in `|nt|`.  The run sequences of a characteristic of a boundary of `b` vertices
have length `≤ 2 kmax + 1` (`RB`), a bound independent of the tree.  Here: `fpBound'` with `3^(2(L+L)+1+Ly)`, and the
three statements `mergeAR_runs'`, `mergeKids_runs'`, `mergeReal_runs'`, `realJoin_runs'` re-proved with the extra
hypothesis `RB · Ly` on the target (proofs identical to `E5D`'s; only the `findPath` cost lemma differs).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E5D

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5 E5A E5C1

/-- the cost of one `findPath` call: chains of at most `s` nodes, entries `≤ L`, target sequence of length `≤ Ly` -/
def fpBound' (s L Ly : ℕ) : ℕ :=
  6000 * (s + 1) * (s + 1) * (4 ^ (L + L + 1) + 1) ^ 2 * (2 * (L + L) + 1 + 2) ^ 2 +
    4 ^ (L + L + 1) * (100 * 3 ^ (2 * (L + L) + 1 + Ly) + 100 * (2 * (L + L) + 1) + 100) + 12 * (s + s) + 200

theorem findPathCost_le' (la lb lw s L Ly : ℕ) (ha : la ≤ s) (hb : lb ≤ s) (hw : lw ≤ Ly) :
    6000 * (la + 1) * (lb + 1) * (4 ^ (L + L + 1) + 1) ^ 2 * (2 * (L + L) + 1 + 2) ^ 2 +
      4 ^ (L + L + 1) * (100 * 3 ^ (2 * (L + L) + 1 + lw) + 100 * (2 * (L + L) + 1) + 100) +
      12 * (la + lb) + 200 ≤ fpBound' s L Ly := by
  unfold fpBound'
  have h1 : 3 ^ (2 * (L + L) + 1 + lw) ≤ 3 ^ (2 * (L + L) + 1 + Ly) := Nat.pow_le_pow_right (by norm_num) (by omega_fresh)
  have h2 : 6000 * (la + 1) * (lb + 1) ≤ 6000 * (s + 1) * (s + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 6000 (by omega_fresh)) (by omega_fresh)
  have h3 : 6000 * (la + 1) * (lb + 1) * (4 ^ (L + L + 1) + 1) ^ 2 * (2 * (L + L) + 1 + 2) ^ 2 ≤
      6000 * (s + 1) * (s + 1) * (4 ^ (L + L + 1) + 1) ^ 2 * (2 * (L + L) + 1 + 2) ^ 2 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2)
  have h4 : 4 ^ (L + L + 1) * (100 * 3 ^ (2 * (L + L) + 1 + lw) + 100 * (2 * (L + L) + 1) + 100) ≤
      4 ^ (L + L + 1) * (100 * 3 ^ (2 * (L + L) + 1 + Ly) + 100 * (2 * (L + L) + 1) + 100) :=
    Nat.mul_le_mul_left _ (by omega_fresh)
  omega_fresh

/-- local cost of `mergeAR` -/
def cMA' (s L Ly : ℕ) : ℕ := fpBound' s L Ly + 600 * (s + 3) ^ 2 + 200 * (s + 1) + 300

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

mutual
theorem mergeAR_runs'_rec (s L Ly : ℕ) (hL : L ≤ s) (hB : 1000 + 100 * (s + 1) < B) :
    ∀ (a b : AR) (c : CT), sz a ≤ s → sz b ≤ s → sz c ≤ s → ARcard L a → ARcard L b → CT.RB s Ly c →
    Runs Δ' B fMergeAR [toVal a, toVal b, toVal c] (toVal (mergeAR a b c)) (cMA' s L Ly * cnt a)
  | .run S na ka, .run S' nb kb, .node S'' ty tk, ha, hb, hc, hca, hcb, hrb => by
    have hE1 := Ext.trans extE1 hΔ
    have hΔA : E5A.Δ ⊑ Δ' := Ext.trans extA hΔ
    have hB1 : 1 < B := by omega_fresh
    have hna : sz na ≤ s := by have := sz_c_lt S na ka; omega_fresh
    have hnb : sz nb ≤ s := by have := sz_c_lt S' nb kb; omega_fresh
    have hka : sz ka ≤ s := by have := sz_ks_lt S na ka; omega_fresh
    have hkb : sz kb ≤ s := by have := sz_ks_lt S' nb kb; omega_fresh
    have hSs : sz S ≤ s := by have := sz_S_lt S na ka; omega_fresh
    have hty : sz ty ≤ s := by have := E5R.sz_ct_y_lt S'' ty tk; omega_fresh
    have htk : sz tk ≤ s := by have := E5R.sz_ct_ks_lt S'' ty tk; omega_fresh
    have hlna := length_le_sz na
    have hlnb := length_le_sz nb
    have hlty := length_le_sz ty
    have hlka := length_le_sz ka
    have hcS := card_le_sz S
    have hcards1 := cards_runs hΔA B na (by omega_fresh)
    have hcards2 := cards_runs hΔA B nb (by omega_fresh)
    have hlen := Lib4.card_runs (l4 hE1) B S (by omega_fresh)
    have hcna : ∀ x ∈ na.map (fun n => n.bag.card), x ≤ L := by
      intro x hx; obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx; exact hca.1 n hn
    have hcnb : ∀ x ∈ nb.map (fun n => n.bag.card), x ≤ L := by
      intro x hx; obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx; exact hcb.1 n hn
    have hfp := E1D.findPath_runs (eD hE1) B (by omega_fresh) (na.map (fun n => n.bag.card))
      (nb.map (fun n => n.bag.card)) S.card ty L L hcna hcnb (by simp; omega_fresh)
    have hfpc := findPathCost_le' (na.map (fun n => n.bag.card)).length (nb.map (fun n => n.bag.card)).length
      ty.length s L Ly (by simp; omega_fresh) (by simp; omega_fresh) hrb.2.1
    have hkids := mergeKids_runs'_rec s L Ly hL hB ka kb tk hka hkb htk hca.2 hcb.2 hrb.2.2
    have hk1 : fMergeKids < B := by have : fMergeKids < 1000 := by decide
                                    omega_fresh
    have hk2 : fMergeChain < B := by have : fMergeChain < 1000 := by decide
                                     omega_fresh
    have hk3 : fCards < B := by have : fCards < 1000 := by decide
                                omega_fresh
    have hk4 : fLength < B := by have : fLength < 1000 := by decide
                                 omega_fresh
    have hk5 : E1D.fFindPath < B := by have : E1D.fFindPath < 1000 := by decide
                                       omega_fresh
    have hcnt := length_le_cntL ka
    have hcntp := cnt_pos (AR.run S na ka)
    have hcm : cMA' s L Ly = fpBound' s L Ly + 600 * (s + 3) ^ 2 + 200 * (s + 1) + 300 := rfl
    have e : cMA' s L Ly * (1 + cntL ka) = cMA' s L Ly + cMA' s L Ly * cntL ka := by ring
    have hs3 : (s + 3) ≤ (s + 3) ^ 2 := le_pw (by omega_fresh) (by omega_fresh)
    have hlen' : ka.length ≤ s := by omega_fresh
    simp only [cnt]
    rcases hfp' : findPath (na.map (fun n => n.bag.card)) (nb.map (fun n => n.bag.card)) S.card ty with _ | path
    · rw [hfp'] at hfp
      refine Runs.mk (hΔ _ _ Δ_mergeAR) ?_
      simp only [mergeAR, hfp', toVal_ar, toVal_ct, toVal_none]
      ev_start
      · ev_run
      · rw [e]
        simp only [List.length_map] at *
        omega_fresh
    · rw [hfp'] at hfp
      have hpl := findPath_len hfp'
      simp only [List.length_map] at hpl
      have hmc0 := mergeChain_runs hΔ B s hB na nb hna hnb path none
      have hmc : 250 * (s + 3) * path.length ≤ 500 * (s + 3) ^ 2 := by
        calc 250 * (s + 3) * path.length ≤ 250 * (s + 3) * (2 * (s + 3)) :=
              Nat.mul_le_mul_left _ (by omega_fresh)
          _ = 500 * (s + 3) ^ 2 := by ring
      rcases hks : mergeKids ka kb tk with _ | ks
      · rw [hks] at hkids
        refine Runs.mk (hΔ _ _ Δ_mergeAR) ?_
        simp only [mergeAR, hfp', hks, toVal_ar, toVal_ct, Option.map_none, toVal_none]
        ev_start
        · ev_run
        · rw [e]
          simp only [List.length_map] at *
          omega_fresh
      · rw [hks] at hkids
        refine Runs.mk (hΔ _ _ Δ_mergeAR) ?_
        simp only [mergeAR, hfp', hks, toVal_ar, toVal_ct, Option.map_some, toVal_some, toVal_none]
        ev_start
        · ev_run
        · rw [e]
          simp only [List.length_map] at *
          omega_fresh
theorem mergeKids_runs'_rec (s L Ly : ℕ) (hL : L ≤ s) (hB : 1000 + 100 * (s + 1) < B) :
    ∀ (ka kb : List AR) (tk : List CT), sz ka ≤ s → sz kb ≤ s → sz tk ≤ s → ARcardL L ka → ARcardL L kb → CT.RBL s Ly tk →
    Runs Δ' B fMergeKids [toVal ka, toVal kb, toVal tk] (toVal (mergeKids ka kb tk))
      (cMA' s L Ly * cntL ka + 40 * ka.length + 20)
  | [], [], [], _, _, _, _, _, _ => by
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    simp only [mergeKids, cntL, toVal_some, toVal_nil]
    ev_start
    · ev_run
    · omega_fresh
  | [], [], _ :: _, _, _, _, _, _, _ => by
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    simp only [mergeKids, cntL, toVal_none]
    ev_start
    · ev_run
    · omega_fresh
  | [], _ :: _, _, _, _, _, _, _, _ => by
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    simp only [mergeKids, cntL, toVal_none]
    ev_start
    · ev_run
    · omega_fresh
  | _ :: _, [], _, _, _, _, _, _, _ => by
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    simp only [mergeKids, toVal_none]
    ev_start
    · ev_run
    · omega_fresh
  | _ :: _, _ :: _, [], _, _, _, _, _, _ => by
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    simp only [mergeKids, toVal_none]
    ev_start
    · ev_run
    · omega_fresh
  | a :: as, b :: bs, t :: ts, hka, hkb, htk, hca, hcb, hrb => by
    have ha : sz a ≤ s := by have := sz_head_lt a as; omega_fresh
    have has : sz as ≤ s := by have := sz_tail_lt a as; omega_fresh
    have hb : sz b ≤ s := by have := sz_head_lt b bs; omega_fresh
    have hbs : sz bs ≤ s := by have := sz_tail_lt b bs; omega_fresh
    have ht : sz t ≤ s := by have := sz_head_lt t ts; omega_fresh
    have hts : sz ts ≤ s := by have := sz_tail_lt t ts; omega_fresh
    have h1 := mergeAR_runs'_rec s L Ly hL hB a b t ha hb ht hca.1 hcb.1 hrb.1
    have h2 := mergeKids_runs'_rec s L Ly hL hB as bs ts has hbs hts hca.2 hcb.2 hrb.2
    have hk1 : fMergeAR < B := by have : fMergeAR < 1000 := by decide
                                  omega_fresh
    have hk2 : fMergeKids < B := by have : fMergeKids < 1000 := by decide
                                    omega_fresh
    have hcm : cMA' s L Ly = fpBound' s L Ly + 600 * (s + 3) ^ 2 + 200 * (s + 1) + 300 := rfl
    have e : cMA' s L Ly * (cnt a + cntL as) = cMA' s L Ly * cnt a + cMA' s L Ly * cntL as := by ring
    have hcp := cnt_pos a
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    rcases hr : mergeAR a b t with _ | r
    · rw [hr] at h1
      simp only [mergeKids, hr, toVal_cons, toVal_none, cntL, List.length_cons]
      ev_start
      · ev_run
      · rw [e]; omega_fresh
    · rw [hr] at h1
      rcases hrs : mergeKids as bs ts with _ | rs
      · rw [hrs] at h2
        simp only [mergeKids, hr, hrs, Option.map_none, toVal_cons, toVal_none, cntL,
          List.length_cons]
        ev_start
        · ev_run
        · rw [e]; omega_fresh
      · rw [hrs] at h2
        simp only [mergeKids, hr, hrs, Option.map_some, toVal_cons, toVal_some, toVal_none, cntL,
          List.length_cons]
        ev_start
        · ev_run
        · rw [e]; omega_fresh
end

end proofs

theorem mergeAR_runs'_pair : (type_of% @mergeAR_runs'_rec) ∧ (type_of% @mergeKids_runs'_rec) :=
  ⟨@mergeAR_runs'_rec, @mergeKids_runs'_rec⟩

theorem mergeAR_runs' : type_of% @mergeAR_runs'_rec := mergeAR_runs'_pair.1

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ


/-- cost of `mergeReal` -/
def cMergeReal' (s L Ly ck6 : ℕ) : ℕ :=
  2 * (E5B.cA s ck6 * s) + cMA' (5 * s) L Ly * (5 * s) + 100 * (900 * (s * s) + 1) * (900 * (s * s)) + 100

theorem mergeReal_runs' (E : Ext5 Δ') (Bd : Finset ℕ) (ta tb : RT) (target : CT) (s L Ly : ℕ)
    (hBd : sz Bd ≤ s) (hta : sz ta ≤ s) (htb : sz tb ≤ s) (htg : sz target ≤ s) (hL : L ≤ 5 * s)
    (hca : ∀ X ∈ ta.bags, X.card ≤ L) (hcb : ∀ X ∈ tb.bags, X.card ≤ L) (hRB : CT.RB (5 * s) Ly target)
    (hB : 200000 + 100000 * (s + 1) ^ 2 + E.cKey (6 * s) < B) :
    Runs Δ' B fMergeReal [toVal Bd, toVal ta, toVal tb, toVal target] (toVal (mergeReal Bd ta tb target))
      (cMergeReal' s L Ly (E.cKey (6 * s))) := by
  have hq : (s + 1) ^ 2 = s * s + 2 * s + 1 := by ring
  have hq2 : 0 ≤ (s + 1) ^ 2 := Nat.zero_le _
  have hB1 : 1000 + 100 * (6 * s + 1) + E.cKey (6 * s) < B := by nlinarith
  have hB2 : 1000 + 100 * (5 * s + 1) < B := by nlinarith
  have hΔB : E5B.Δ ⊑ Δ' := Ext.trans extB hΔ
  have h1 := E5B.analyze_runs hΔB B E Bd s hBd hB1 ta hta
  have h2 := E5B.analyze_runs hΔB B E Bd s hBd hB1 tb htb
  have sa := le_trans (E5B.sz_analyze_le Bd ta) (by omega_fresh : 5 * sz ta ≤ 5 * s)
  have sb := le_trans (E5B.sz_analyze_le Bd tb) (by omega_fresh : 5 * sz tb ≤ 5 * s)
  have hm := mergeAR_runs' hΔ B (5 * s) L Ly hL hB2 (analyze Bd ta) (analyze Bd tb) target sa sb (by omega_fresh)
    (ARcard_analyze L Bd ta hca) (ARcard_analyze L Bd tb hcb) hRB
  have ca := le_trans (cnt_le_sz (analyze Bd ta)) sa
  have t1 : E5B.cA s (E.cKey (6 * s)) * ta.size ≤ E5B.cA s (E.cKey (6 * s)) * s :=
    Nat.mul_le_mul_left _ (le_trans (size_le_sz ta) hta)
  have t2 : E5B.cA s (E.cKey (6 * s)) * tb.size ≤ E5B.cA s (E.cKey (6 * s)) * s :=
    Nat.mul_le_mul_left _ (le_trans (size_le_sz tb) htb)
  have t3 : cMA' (5 * s) L Ly * cnt (analyze Bd ta) ≤ cMA' (5 * s) L Ly * (5 * s) := Nat.mul_le_mul_left _ ca
  have hk1 : fMergeAR < B := by have : fMergeAR < 1000 := by decide
                                omega_fresh
  have hk2 : E5B.fAnalyze < B := by have : E5B.fAnalyze < 1000 := by decide
                                    omega_fresh
  have hk3 : E5A.fToRT < B := by have : E5A.fToRT < 1000 := by decide
                                 omega_fresh
  have hgoal : mergeReal Bd ta tb target = (mergeAR (analyze Bd ta) (analyze Bd tb) target).map AR.toRT := rfl
  rw [hgoal]
  rcases hr : mergeAR (analyze Bd ta) (analyze Bd tb) target with _ | r
  · rw [hr] at hm
    refine Runs.mk (hΔ _ _ Δ_mergeReal) ?_
    simp only [Option.map_none]
    ev_start
    · ev_run
    · unfold cMergeReal'; omega_fresh
  · rw [hr] at hm
    have hsr := sz_mergeAR_le _ _ target r hr
    have hsr' : sz r ≤ 900 * (s * s) := by
      have : (sz (analyze Bd ta) + sz (analyze Bd tb)) ^ 2 ≤ (10 * s) ^ 2 := Nat.pow_le_pow_left (by omega_fresh) 2
      have e : (10 * s) ^ 2 = 100 * (s * s) := by ring
      omega_fresh
    have hcr := le_trans (cnt_le_sz r) hsr'
    have hrt := E5A.toRT_runs (Ext.trans extA hΔ) B (900 * (s * s)) (by nlinarith) r hsr'
    have t4 : 100 * (900 * (s * s) + 1) * cnt r ≤ 100 * (900 * (s * s) + 1) * (900 * (s * s)) :=
      Nat.mul_le_mul_left _ hcr
    refine Runs.mk (hΔ _ _ Δ_mergeReal) ?_
    simp only [Option.map_some, toVal_some]
    ev_start
    · ev_run
    · unfold cMergeReal'; omega_fresh

/-- cost of `realJoin` -/
def cRealJoin' (s L Ly Lj cnorm5 cdom ck6 cj : ℕ) : ℕ :=
  2 * (200 * (s + 1) * s + cnorm5 + 8) + cj + (24 * Lj + 6 + Lj * (cdom + 10)) + cMergeReal' s L Ly ck6 + 100

theorem realJoin_runs' (E : Ext5 Δ') (X : ExtJ Δ') (kmax : ℕ) (Bd : Finset ℕ) (ta tb : RT) (target : CT)
    (s L Ly Lj : ℕ) (hBd : sz Bd ≤ s) (hta : sz ta ≤ s) (htb : sz tb ≤ s) (htg : sz target ≤ s) (hL : L ≤ 5 * s)
    (hca : ∀ X ∈ ta.bags, X.card ≤ L) (hcb : ∀ X ∈ tb.bags, X.card ≤ L)
    (hPJ : X.PJ kmax (ta.char Bd) (tb.char Bd)) (hLen : (CT.joinC kmax (ta.char Bd) (tb.char Bd)).length ≤ Lj)
    (hjs : ∀ d ∈ CT.joinC kmax (ta.char Bd) (tb.char Bd), sz d ≤ s)
    (hPD : ∀ d ∈ CT.joinC kmax (ta.char Bd) (tb.char Bd), E.PD s d target)
    (hRB : ∀ d ∈ CT.joinC kmax (ta.char Bd) (tb.char Bd), CT.RB (5 * s) Ly d)
    (hB : 200000 + 100000 * (s + 1) ^ 2 + E.cKey (6 * s) + E.cNorm (5 * s) + E.cDom s +
      X.cJ kmax (ta.char Bd) (tb.char Bd) < B) :
    Runs Δ' B fRealJoin [toVal kmax, toVal Bd, toVal ta, toVal tb, toVal target]
      (toVal (realJoin kmax Bd ta tb target))
      (cRealJoin' s L Ly Lj (E.cNorm (5 * s)) (E.cDom s) (E.cKey (6 * s)) (X.cJ kmax (ta.char Bd) (tb.char Bd))) := by
  have hE1 := Ext.trans extE1 hΔ
  have hq2 : s + 1 ≤ (s + 1) ^ 2 := le_pw (by omega_fresh) (by omega_fresh)
  have hch1 := E5A.char_runs (Ext.trans extA hΔ) B E Bd ta s hta hBd (by nlinarith)
  have hch2 := E5A.char_runs (Ext.trans extA hΔ) B E Bd tb s htb hBd (by nlinarith)
  have hjc := X.joinC B kmax (ta.char Bd) (tb.char Bd) hPJ (by omega_fresh)
  have hfind := Lib4.find_runs (l4 hE1) B fPredJoin (toVal target) (fun d => CT.domCB d target)
    (fun _ => E.cDom s + 10) (CT.joinC kmax (ta.char Bd) (tb.char Bd))
    (fun d hd => predJoin_runs hΔ B E target d s (hjs d hd) htg (hPD d hd) (by nlinarith)) (by omega_fresh)
  simp only [E5.sum_map_const] at hfind
  have hmul : (CT.joinC kmax (ta.char Bd) (tb.char Bd)).length * (E.cDom s + 10) ≤ Lj * (E.cDom s + 10) :=
    Nat.mul_le_mul_right _ hLen
  have hts1 : 200 * (s + 1) * ta.size ≤ 200 * (s + 1) * s := Nat.mul_le_mul_left _ (le_trans (size_le_sz ta) hta)
  have hts2 : 200 * (s + 1) * tb.size ≤ 200 * (s + 1) * s := Nat.mul_le_mul_left _ (le_trans (size_le_sz tb) htb)
  have hk1 : fChar < B := by have : fChar < 1000 := by decide
                             nlinarith
  have hk2 : fPredJoin < B := by have : fPredJoin < 1000 := by decide
                                 nlinarith
  have hk3 : fMergeReal < B := by have : fMergeReal < 1000 := by decide
                                  nlinarith
  have hk4 : Lib4.fFind < B := by have : Lib4.fFind < 1000 := by decide
                                  nlinarith
  have hgoal : realJoin kmax Bd ta tb target =
      ((CT.joinC kmax (ta.char Bd) (tb.char Bd)).find? (fun d => CT.domCB d target)).bind
        (mergeReal Bd ta tb) := rfl
  rw [hgoal]
  rcases hf : (CT.joinC kmax (ta.char Bd) (tb.char Bd)).find? (fun d => CT.domCB d target) with _ | d
  · rw [hf] at hfind
    refine Runs.mk (hΔ _ _ Δ_realJoin) ?_
    simp only [Option.bind_none]
    ev_start
    · ev_run
    · unfold cRealJoin'; omega_fresh
  · rw [hf] at hfind
    have hdm : d ∈ CT.joinC kmax (ta.char Bd) (tb.char Bd) := List.mem_of_find?_eq_some hf
    have hmr := mergeReal_runs' hΔ B E Bd ta tb d s L Ly hBd hta htb (hjs d hdm) hL hca hcb (hRB d hdm) (by nlinarith)
    refine Runs.mk (hΔ _ _ Δ_realJoin) ?_
    simp only [Option.bind_some, toVal_some]
    ev_start
    · ev_run
    · unfold cRealJoin'; omega_fresh


end proofs
end E5D
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6bMath1` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6b (3): mathematics of the extraction cost analysis, part 1

* `char_wf` : the characteristic of a connected real tree covering the boundary is a well-formed characteristic
  (`Wf B (w+1)`) when the tree has width `w`.  (`extract` calls `realIntro`/`realJoin` on `t.char B` for the *real* trees
  it built, not on table entries, so the size bounds of the tables do not apply to them directly.)
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT

mutual
theorem loc_prof_rec (B : Finset ℕ) : ∀ t : RT, Loc B (RT.prof B t)
  | .node X ks => by
    rw [RT.prof_node]
    refine ⟨Finset.inter_subset_right, typical_singleton _, by simp, ?_, ?_⟩
    · intro e he
      simp only [List.mem_singleton] at he
      subst he
      exact Finset.card_le_card Finset.inter_subset_left
    · rw [← RT.profL_eq_map B ks]
      exact locL_profL_rec B ks
theorem locL_profL_rec (B : Finset ℕ) : ∀ ks : List RT, LocL B (RT.profL B ks)
  | [] => trivial
  | k :: ks => ⟨loc_prof_rec B k, locL_profL_rec B ks⟩
end

theorem loc_prof_pair : (type_of% @loc_prof_rec) ∧ (type_of% @locL_profL_rec) :=
  ⟨@loc_prof_rec, @locL_profL_rec⟩

theorem loc_prof : type_of% @loc_prof_rec := loc_prof_pair.1


/-- the characteristic of a connected real tree of width `w` covering `B` is well formed -/
theorem char_wf {B : Finset ℕ} {t : RT} {w : ℕ} (hc : t.Conn) (hB : B ⊆ t.verts) (hw : t.Width w) :
    (t.char B).Wf B (w + 1) := by
  unfold RT.char
  refine ⟨?_, good_norm _ (loc_prof B t) (RT.conn_prof B t hc), conn_norm _ (RT.conn_prof B t hc), ?_⟩
  · rw [verts_norm]
    ext u
    rw [RT.mem_verts_prof]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨hB h, h⟩
  · exact le_trans (maxEntry_norm_le _) (maxEntry_prof_le B t hw)

end E6b
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6bMath2` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6b (4): mathematics of the extraction cost analysis, part 2

Run sequences of the *un-normalised* results of `introPlans` (the inputs of `norm` and `domCB` in `realIntro`) have entries
`≤ maxEntry t + 1` (a region gets the new vertex) or `≤ b + 1` (a new branch: `M ∪ {v}`), so their run sequences have length
`≤ 2 K + 1`, and the plans themselves have size polynomial in `count t` and `b`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT

/-- `node S y ks` has `maxEntry + 1 ≤ K` iff entries and kids are `≤ K - 1` -/
theorem me_succ_iff {S : Finset ℕ} {y : List ℕ} {ks : List CT} {K : ℕ} :
    maxEntry (node S y ks) + 1 ≤ K ↔ K ≥ 1 ∧ (∀ e ∈ y, e + 1 ≤ K) ∧ ∀ k ∈ ks, maxEntry k + 1 ≤ K := by
  constructor
  · intro h
    have h' : maxEntry (node S y ks) ≤ K - 1 := by omega
    obtain ⟨h1, h2⟩ := maxEntry_le_iff.1 h'
    exact ⟨by omega, fun e he => by have := h1 e he; omega, fun k hk => by have := h2 k hk; omega⟩
  · rintro ⟨hK, h1, h2⟩
    have : maxEntry (node S y ks) ≤ K - 1 :=
      maxEntry_le_iff.2 ⟨fun e he => by have := h1 e he; omega, fun k hk => by have := h2 k hk; omega⟩
    omega

mutual
theorem winPlans_me_rec (v : ℕ) {K : ℕ} : ∀ (lo : ℕ) (t : CT), maxEntry t + 1 ≤ K →
    ∀ x ∈ winPlans v lo t, maxEntry x.2.1 ≤ K
  | lo, node S y ks, ht, x, hx => by
    obtain ⟨hK, hy, hks⟩ := me_succ_iff.1 ht
    have hnode : ∀ (y' : List ℕ) (ks' : List CT), (∀ e ∈ y', e ≤ K) → (∀ k ∈ ks', maxEntry k ≤ K) →
        ∀ S', maxEntry (node S' y' ks') ≤ K := fun y' ks' h1 h2 S' => maxEntry_le_iff.2 ⟨h1, h2⟩
    have hks' : ∀ k ∈ ks, maxEntry k ≤ K := fun k hk => by have := hks k hk; omega
    have hy' : ∀ e ∈ y, e ≤ K := fun e he => by have := hy e he; omega
    have hp1 : ∀ (z : List ℕ), (∀ e ∈ z, e ∈ y) → ∀ e ∈ plus1 z, e ≤ K := by
      intro z hz e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      exact hy e0 (hz e0 he0)
    have hdrop : ∀ n, ∀ e ∈ y.drop n, e ∈ y := fun n e he => List.mem_of_mem_drop he
    have hsl : ∀ n m, ∀ e ∈ (y.take n).drop m, e ∈ y := fun n m e he =>
      List.mem_of_mem_take (List.mem_of_mem_drop he)
    simp only [winPlans, List.mem_append, List.mem_map] at hx
    rcases hx with (⟨f, _, rfl⟩ | ⟨f, _, rfl⟩) | ⟨combo, hcombo, rfl⟩
    · refine hnode _ _ (hp1 _ (hsl _ _)) ?_ _
      intro k hk
      simp only [List.mem_singleton] at hk; subst hk
      exact hnode _ _ (fun e he => hy' e (hdrop _ e he)) hks' _
    · refine hnode _ _ (hp1 _ (hsl _ _)) ?_ _
      intro k hk
      simp only [List.mem_singleton] at hk; subst hk
      exact hnode _ _ (fun e he => hy' e (hdrop _ e he)) hks' _
    · have := kidChoices_me_rec v ks hks combo hcombo
      refine hnode _ _ (hp1 _ (fun e he => hdrop _ e he)) ?_ _
      intro k hk
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hk
      exact this o ho
theorem kidChoices_me_rec (v : ℕ) {K : ℕ} : ∀ (ks : List CT), (∀ k ∈ ks, maxEntry k + 1 ≤ K) →
    ∀ combo ∈ kidChoices v ks, ∀ o ∈ combo, maxEntry o.2.1 ≤ K
  | [], _, combo, h => by
    simp only [kidChoices, List.mem_singleton] at h; subst h; simp
  | k :: ks, hk, combo, h => by
    simp only [kidChoices, List.mem_flatMap, List.mem_map] at h
    obtain ⟨o, ho, combo', hcombo', rfl⟩ := h
    have ih := kidChoices_me_rec v ks (fun k' hk' => hk k' (List.mem_cons_of_mem _ hk')) combo' hcombo'
    have hk0 := hk k (by simp)
    have ho' : maxEntry o.2.1 ≤ K := by
      rcases List.mem_cons.1 ho with rfl | ho
      · simp only []; omega
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
        exact winPlans_me_rec v 0 k hk0 p hp
    intro o' hmem
    rcases List.mem_cons.1 hmem with rfl | hmem
    · exact ho'
    · exact ih o' hmem
end

theorem winPlans_me_pair : (type_of% @winPlans_me_rec) ∧ (type_of% @kidChoices_me_rec) :=
  ⟨@winPlans_me_rec, @kidChoices_me_rec⟩

theorem winPlans_me : type_of% @winPlans_me_rec := winPlans_me_pair.1


theorem wtopPlans_me (v : ℕ) {K : ℕ} {t : CT} (ht : maxEntry t + 1 ≤ K) :
    ∀ x ∈ wtopPlans v t, maxEntry x.2.1 ≤ K := by
  intro x hx
  cases t with
  | node S y ks =>
    obtain ⟨hK, hy, hks⟩ := me_succ_iff.1 ht
    simp only [wtopPlans, List.mem_append, List.mem_map, List.mem_flatMap] at hx
    rcases hx with (⟨p, hp, rfl⟩ | ⟨f, _, p, hp, rfl⟩) | ⟨f, _, p, hp, rfl⟩
    · exact winPlans_me v 0 _ ht p hp
    · have := winPlans_me v f _ ht p hp
      refine maxEntry_le_iff.2 ⟨fun e he => ?_, ?_⟩
      · have := hy e (List.mem_of_mem_take he); omega
      · intro k hk; simp only [List.mem_singleton] at hk; subst hk; exact this
    · have := winPlans_me v (f + 1) _ ht p hp
      refine maxEntry_le_iff.2 ⟨fun e he => ?_, ?_⟩
      · have := hy e (List.mem_of_mem_take he); omega
      · intro k hk; simp only [List.mem_singleton] at hk; subst hk; exact this

theorem pathSubtree_me {v : ℕ} {S : Finset ℕ} {b : ℕ} (hS : S.card ≤ b) :
    ∀ (chain : List (Finset ℕ)) (M : Finset ℕ), (∀ X ∈ chain, X ⊆ S) → M ⊆ S →
      maxEntry (pathSubtree v chain M) ≤ b + 1
  | [], M, _, hM => by
    have : pathSubtree v [] M = node (insert v M) [M.card + 1] [] := by simp [pathSubtree]
    rw [this]
    refine maxEntry_le_iff.2 ⟨fun e he => ?_, by simp⟩
    simp only [List.mem_singleton] at he; subst he
    have := Finset.card_le_card hM; omega
  | X :: chain, M, hX, hM => by
    have ih := pathSubtree_me (v := v) hS chain M (fun Z hZ => hX Z (List.mem_cons_of_mem _ hZ)) hM
    have hXS := hX X (by simp)
    have : pathSubtree v (X :: chain) M = node X [X.card] [pathSubtree v chain M] := by simp [pathSubtree]
    rw [this]
    refine maxEntry_le_iff.2 ⟨fun e he => ?_, fun k hk => ?_⟩
    · simp only [List.mem_singleton] at he; subst he
      have := Finset.card_le_card hXS; omega
    · simp only [List.mem_singleton] at hk; subst hk; exact ih

theorem attachPlans_me (v : ℕ) (N : Finset ℕ) {b K : ℕ} {S : Finset ℕ} {y : List ℕ} {ks : List CT}
    (hS : S.card ≤ b) (ht : maxEntry (node S y ks) ≤ K) (hb : b + 1 ≤ K) :
    ∀ x ∈ attachPlans v N (node S y ks), maxEntry x.2 ≤ K := by
  intro x hx
  obtain ⟨hy, hks⟩ := maxEntry_le_iff.1 ht
  simp only [attachPlans, List.mem_flatMap, List.mem_cons, List.mem_append, List.mem_map] at hx
  obtain ⟨⟨chain, M⟩, hcm, hx⟩ := hx
  obtain ⟨hM, hch⟩ := allChains_sub S N _ hcm
  simp only at hM hch
  have hbr := pathSubtree_me (v := v) hS chain M hch hM
  have hbr' : maxEntry (pathSubtree v chain M) ≤ K := le_trans hbr hb
  rcases hx with (rfl | ⟨f, _, rfl⟩) | ⟨f, _, rfl⟩
  · refine maxEntry_le_iff.2 ⟨hy, fun k hk => ?_⟩
    rcases List.mem_append.1 hk with hk | hk
    · exact hks k hk
    · simp only [List.mem_singleton] at hk; subst hk; exact hbr'
  · refine maxEntry_le_iff.2 ⟨fun e he => hy e (List.mem_of_mem_take he), fun k hk => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact hbr'
    · exact maxEntry_le_iff.2 ⟨fun e he => hy e (List.mem_of_mem_drop he), hks⟩
  · refine maxEntry_le_iff.2 ⟨fun e he => hy e (List.mem_of_mem_take he), fun k hk => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact hbr'
    · exact maxEntry_le_iff.2 ⟨fun e he => hy e (List.mem_of_mem_drop he), hks⟩

theorem introKids_me (v : ℕ) (N S : Finset ℕ) (y : List ℕ) {K : ℕ} (hy : ∀ e ∈ y, e ≤ K) :
    ∀ (ks pre : List CT), (∀ k ∈ pre, maxEntry k ≤ K) → (∀ k ∈ ks, maxEntry k ≤ K) →
      (∀ k ∈ ks, ∀ x ∈ introPlans v N k, maxEntry x.2.2 ≤ K) →
      ∀ x ∈ introKids v N S y pre ks, maxEntry x.2.2 ≤ K
  | [], _, _, _, _, x, hx => by simp [introKids] at hx
  | c0 :: post, pre, hpre, hk, ih, x, hx => by
    simp only [introKids, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨r, hr, rfl⟩ | hx
    · have h1 := ih c0 (by simp) r hr
      refine maxEntry_le_iff.2 ⟨hy, fun k' hk' => ?_⟩
      simp only [List.mem_append, List.mem_cons] at hk'
      rcases hk' with hk' | rfl | hk'
      · exact hpre k' hk'
      · exact h1
      · exact hk k' (List.mem_cons_of_mem _ hk')
    · exact introKids_me v N S y hy post (pre ++ [c0])
        (fun k' hk' => by
          rcases List.mem_append.1 hk' with h | h
          · exact hpre k' h
          · simp only [List.mem_singleton] at h; rw [h]; exact hk c0 (by simp))
        (fun k' hk' => hk k' (List.mem_cons_of_mem _ hk'))
        (fun k' hk' => ih k' (List.mem_cons_of_mem _ hk')) x hx

/-- the entries of the results of `introPlans`: `≤ K` when `maxEntry t + 1 ≤ K` and the labels have `≤ K - 1` vertices -/
theorem introPlans_me (v : ℕ) (N : Finset ℕ) {b K : ℕ} (hb : b + 1 ≤ K) :
    ∀ t : CT, LB b t → maxEntry t + 1 ≤ K → ∀ x ∈ introPlans v N t, maxEntry x.2.2 ≤ K := by
  intro t
  induction t using CT.ind with
  | h S y ks ih =>
    intro hlb hme x hx
    obtain ⟨hK, hy, hks⟩ := me_succ_iff.1 hme
    have hS : S.card ≤ b := hlb.1
    have hme' : maxEntry (node S y ks) ≤ K := by omega
    simp only [introPlans, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    rcases hx with (⟨p, ⟨hp, -⟩, rfl⟩ | hx) | hx
    · exact wtopPlans_me v hme p hp
    · split_ifs at hx with hN
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        exact attachPlans_me v N hS hme' hb p hp
      · simp at hx
    · refine introKids_me v N S y (fun e he => by have := hy e he; omega) ks [] (by simp)
        (fun k hk => by have := hks k hk; omega) (fun k hk => ?_) x hx
      exact ih k hk (hlb.kids k hk) (hks k hk)

/-! ### sizes of the plans -/

/-- the size bound of a plan (`count t` runs, labels of `≤ b` vertices) -/
def planSzBound (c b : ℕ) : ℕ := 16 * c + (b + 1) * (2 * b + 2) + 2 * b + 11

theorem planSzBound_mono {c c' : ℕ} (b : ℕ) (h : c ≤ c') : planSzBound c b ≤ planSzBound c' b := by
  unfold planSzBound; omega

theorem sz_cut_opt_le (o : Option Cut) : sz o ≤ 5 := by
  cases o with
  | none => simp
  | some c => cases c <;> simp [sz, Val.size]

theorem wtopPlans_plan_sz (v : ℕ) (t : CT) : ∀ x ∈ wtopPlans v t, sz x.1 ≤ 16 * count t + 5 := by
  intro x hx
  cases t with
  | node S y ks =>
    simp only [wtopPlans, List.mem_append, List.mem_map, List.mem_flatMap] at hx
    have key : ∀ (lo : ℕ) (p : WPlan × CT × Finset ℕ), p ∈ winPlans v lo (node S y ks) → ∀ pre : Option Cut,
        sz (Plan.top pre p.1) ≤ 16 * count (node S y ks) + 5 := by
      intro lo p hp pre
      have h1 := winPlans_wsz_le v lo (node S y ks) p hp
      have h2 := sz_wp_le p.1
      have h3 := sz_cut_opt_le pre
      rw [sz_plan_top]; omega
    rcases hx with (⟨p, hp, rfl⟩ | ⟨f, _, p, hp, rfl⟩) | ⟨f, _, p, hp, rfl⟩
    · exact key 0 p hp none
    · exact key f p hp _
    · exact key (f + 1) p hp _

theorem attachPlans_plan_sz (v : ℕ) (N : Finset ℕ) {b : ℕ} {S : Finset ℕ} {y : List ℕ} {ks : List CT}
    (hS : S.card ≤ b) : ∀ x ∈ attachPlans v N (node S y ks), sz x.1 ≤ (b + 1) * (2 * b + 2) + 2 * b + 11 := by
  intro x hx
  simp only [attachPlans, List.mem_flatMap, List.mem_cons, List.mem_append, List.mem_map] at hx
  obtain ⟨⟨chain, M⟩, hcm, hx⟩ := hx
  obtain ⟨hM, hch⟩ := allChains_sub S N _ hcm
  have hlen := allChains_chain_length_le S N _ hcm
  simp only at hM hch hlen
  have hchsz : sz chain ≤ 1 + (b + 1) * (2 * b + 2) := by
    have h1 := sz_list_le (l := chain) (s := 2 * b + 1) (fun X hX => by
      rw [sz_finset]; have := Finset.card_le_card (hch X hX); omega)
    have h2 : chain.length * (2 * b + 1 + 1) ≤ (b + 1) * (2 * b + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hMsz : sz M ≤ 2 * b + 1 := by
    rw [sz_finset]; have := Finset.card_le_card hM; omega
  have key : ∀ c : Option Cut, sz (Plan.att c chain M) ≤ (b + 1) * (2 * b + 2) + 2 * b + 11 := by
    intro c
    have := sz_cut_opt_le c
    rw [sz_plan_att]; omega
  rcases hx with (rfl | ⟨f, _, rfl⟩) | ⟨f, _, rfl⟩
  · exact key none
  · exact key _
  · exact key _

/-- **path and plan of every result of `introPlans` are small** -/
theorem introPlans_plan_sz (v : ℕ) (N : Finset ℕ) {b : ℕ} :
    ∀ t : CT, LB b t → ∀ x ∈ introPlans v N t, sz x.2.1 ≤ planSzBound (count t) b := by
  intro t
  induction t using CT.ind with
  | h S y ks ih =>
    intro hlb x hx
    have hS : S.card ≤ b := hlb.1
    have hcs : count (node S y ks) = 1 + countL ks := rfl
    simp only [introPlans, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    have hkid : ∀ (pre ks' : List CT), (∀ k ∈ ks', LB b k) →
        (∀ k ∈ ks', ∀ x ∈ introPlans v N k, sz x.2.1 ≤ planSzBound (count k) b) →
        ∀ x ∈ introKids v N S y pre ks', sz x.2.1 ≤ planSzBound (countL ks') b := by
      intro pre ks'
      induction ks' generalizing pre with
      | nil => intro _ _ x hx; simp [introKids] at hx
      | cons k post ihk =>
        intro hl h x hx
        simp only [introKids, List.mem_append, List.mem_map] at hx
        simp only [countL]
        rcases hx with ⟨r, hr, rfl⟩ | hx
        · have := h k (by simp) r hr
          refine le_trans this (planSzBound_mono b ?_)
          omega
        · have := ihk (pre ++ [k]) (fun k' hk' => hl k' (List.mem_cons_of_mem _ hk'))
            (fun k' hk' => h k' (List.mem_cons_of_mem _ hk')) x hx
          refine le_trans this (planSzBound_mono b ?_)
          omega
    rcases hx with (⟨p, ⟨hp, -⟩, rfl⟩ | hx) | hx
    · have := wtopPlans_plan_sz v (node S y ks) p hp
      simp only [planSzBound]; omega
    · split_ifs at hx with hN
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        have := attachPlans_plan_sz v N (y := y) (ks := ks) hS p hp
        simp only [planSzBound]; omega
      · simp at hx
    · have := hkid [] ks (fun k hk => hlb.kids k hk) (fun k hk => ih k hk (hlb.kids k hk)) x hx
      refine le_trans this (planSzBound_mono b ?_)
      omega

theorem introPlans_path_sz (v : ℕ) (N : Finset ℕ) (t : CT) : ∀ x ∈ introPlans v N t, sz x.1 ≤ 2 * count t := by
  intro x hx
  have := introPlans_path_le v N t x hx
  rw [sz_list_nat]; omega

/-- the size of a whole plan triple -/
theorem introPlans_sz_le (v : ℕ) (N : Finset ℕ) {b c0 Sct : ℕ} (t : CT) (hlb : LB b t) (hc : count t ≤ c0)
    (hct : ∀ x ∈ introPlans v N t, sz x.2.2 ≤ Sct) :
    ∀ x ∈ introPlans v N t, sz x ≤ 2 * c0 + planSzBound c0 b + Sct + 2 := by
  intro x hx
  have h1 := introPlans_path_sz v N t x hx
  have h2 := introPlans_plan_sz v N t hlb x hx
  have h3 := hct x hx
  have h4 := planSzBound_mono b hc
  have e : sz x = sz x.1 + (sz x.2.1 + sz x.2.2 + 1) + 1 := by
    obtain ⟨a, p, c⟩ := x; simp only [sz_pair]
  omega

end E6b
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6bZ` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6b (14): the `Z`-calculus

`x ≤ Z^p` bounds: monotone in `p`, closed under `*` (exponents add), `+` (exponent `+1`), `+1`, powers, and multiplication by a
numeral `c ≤ Z`.  Used to bound the polynomial cost functions of E2/E3/E5 (whose arguments are all `≤ Z^p` for the common
ceiling `Z = Zc M k`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

section zcalc
variable {Z : ℕ}

theorem zb_mono {x p q : ℕ} (h : x ≤ Z ^ p) (hpq : p ≤ q) (hZ : 1 ≤ Z) : x ≤ Z ^ q :=
  le_trans h (Nat.pow_le_pow_right hZ hpq)

theorem zb_mul {x y p q : ℕ} (h1 : x ≤ Z ^ p) (h2 : y ≤ Z ^ q) : x * y ≤ Z ^ (p + q) := by
  rw [pow_add]; exact Nat.mul_le_mul h1 h2

theorem zb_add {x y p r : ℕ} (h1 : x ≤ Z ^ p) (h2 : y ≤ Z ^ p) (hZ : 2 ≤ Z) (hpr : p + 1 ≤ r) : x + y ≤ Z ^ r := by
  have h3 : Z ^ p + Z ^ p ≤ Z ^ (p + 1) := by
    rw [pow_succ]
    have : 1 ≤ Z ^ p := Nat.one_le_pow _ _ (by omega)
    nlinarith
  exact le_trans (by omega) (le_trans h3 (Nat.pow_le_pow_right (by omega) hpr))

theorem zb_add' {x y p q r : ℕ} (h1 : x ≤ Z ^ p) (h2 : y ≤ Z ^ q) (hZ : 2 ≤ Z) (hp : p ≤ r) (hq : q ≤ r) :
    x + y ≤ Z ^ (r + 1) :=
  zb_add (zb_mono h1 hp (by omega)) (zb_mono h2 hq (by omega)) hZ le_rfl

/-- a sum: exponent `max + 1` (no bookkeeping needed at the call site) -/
theorem zb_addm {x y p q : ℕ} (h1 : x ≤ Z ^ p) (h2 : y ≤ Z ^ q) (hZ : 2 ≤ Z) : x + y ≤ Z ^ (max p q + 1) :=
  zb_add' h1 h2 hZ (le_max_left p q) (le_max_right p q)

theorem zb_succ {x p : ℕ} (h : x ≤ Z ^ p) (hZ : 2 ≤ Z) : x + 1 ≤ Z ^ (p + 1) :=
  zb_add (zb_mono h le_rfl (by omega)) (by
    have : 1 ≤ Z ^ p := Nat.one_le_pow _ _ (by omega)
    omega) hZ le_rfl

theorem zb_pow {x p : ℕ} (h : x ≤ Z ^ p) (n : ℕ) : x ^ n ≤ Z ^ (p * n) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left h n

theorem zb_num {c : ℕ} (hc : c ≤ Z) : c ≤ Z ^ 1 := by simpa using hc

theorem zb_cmul {c x p : ℕ} (hc : c ≤ Z) (h : x ≤ Z ^ p) : c * x ≤ Z ^ (1 + p) := by
  have := zb_mul (zb_num hc) h
  simpa [add_comm] using this

theorem cnum {c : ℕ} (hc : c ≤ 2 ^ 200) (hZ : 2 ^ 200 ≤ Z) : c ≤ Z := le_trans hc hZ

/-! ### the cost functions of E2, E5 -/

variable (hZ : 2 ^ 200 ≤ Z)
include hZ

theorem hZ2 : 2 ≤ Z := le_trans (by norm_num) hZ
theorem hZ1 : 1 ≤ Z := le_trans (by norm_num) hZ

theorem cKeyE2_z {s p : ℕ} (hs : s ≤ Z ^ p) : E5Inst.cKeyE2 s ≤ Z ^ (2 * p + 4) := by
  have h1 := zb_succ hs (hZ2 hZ)
  have h2 := zb_pow h1 2
  have h3 := zb_cmul (cnum (by norm_num : 1000 ≤ 2 ^ 200) hZ) h2
  have h4 := zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)
  have := zb_add' h3 h4 (hZ2 hZ) (r := 2 * p + 3) (by omega) (by omega)
  unfold E5Inst.cKeyE2
  exact zb_mono this (by omega) (hZ1 hZ)

theorem cNormE2_z {s p : ℕ} (hs : s ≤ Z ^ p) : E5Inst.cNormE2 s ≤ Z ^ (5 * p + 6) := by
  have h1 := zb_succ hs (hZ2 hZ)
  have h2 := zb_pow h1 5
  have h3 := zb_cmul (cnum (by norm_num : 14000 ≤ 2 ^ 200) hZ) h2
  unfold E5Inst.cNormE2
  exact zb_mono h3 (by omega) (hZ1 hZ)

theorem cDomE2_z {L s p t : ℕ} (h3 : 3 ^ (2 * L) ≤ Z ^ t) (ht : t ≤ p) (hs : s ≤ Z ^ p) :
    E5Inst.cDomE2 L s ≤ Z ^ (2 * p + 5) := by
  have a1 := zb_cmul (cnum (by norm_num : 30 ≤ 2 ^ 200) hZ) hs
  have a2 := zb_cmul (cnum (by norm_num : 60 ≤ 2 ^ 200) hZ) h3
  have a3 := zb_add' a1 a2 (hZ2 hZ) (r := p + 1) (by omega) (by omega)
  have a4 := zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)
  have a5 := zb_add' a3 a4 (hZ2 hZ) (r := p + 2) (by omega) (by omega)
  have a6 := zb_cmul (cnum (by norm_num : 2 ≤ 2 ^ 200) hZ) hs
  have a7 := zb_mul a5 a6
  have a8 := zb_num (cnum (by norm_num : 1000 ≤ 2 ^ 200) hZ)
  have a9 := zb_add' a7 a8 (hZ2 hZ) (r := 2 * p + 4) (by omega) (by omega)
  unfold E5Inst.cDomE2
  exact zb_mono a9 (by omega) (hZ1 hZ)

theorem cSort_z {s ck p q : ℕ} (hs : s ≤ Z ^ p) (hck : ck ≤ Z ^ q) (hq : q ≤ 4 * p + 5) :
    E5B.cSort s ck ≤ Z ^ (6 * p + 10) := by
  have b1 := zb_succ hs (hZ2 hZ)
  have b2 := zb_pow b1 4
  have b3 := zb_cmul (cnum (by norm_num : 800 ≤ 2 ^ 200) hZ) b2
  have b4 := zb_add' b3 hck (hZ2 hZ) (r := 4 * p + 5) (by omega) hq
  have b5 := zb_add' b4 (zb_num (cnum (by norm_num : 80 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := 4 * p + 6) (by omega) (by omega)
  have b6 := zb_pow b1 2
  have b7 := zb_mul b5 b6
  have b8 := zb_add' b7 (zb_num (cnum (by norm_num : 8 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := 6 * p + 9) (by omega) (by omega)
  unfold E5B.cSort
  exact zb_mono b8 (by omega) (hZ1 hZ)

theorem cAN_z {s ck p q : ℕ} (hs : s ≤ Z ^ p) (hck : ck ≤ Z ^ q) (hq : q ≤ 4 * p + 5) :
    E5B.cAN s ck ≤ Z ^ (6 * p + 11) := by
  have h1 := zb_succ hs (hZ2 hZ)
  have h2 := zb_pow h1 2
  have h3 := zb_cmul (cnum (by norm_num : 1000 ≤ 2 ^ 200) hZ) h2
  have h4 := cSort_z hZ hs hck hq
  have := zb_add' h3 h4 (hZ2 hZ) (r := 6 * p + 10) (by omega) le_rfl
  unfold E5B.cAN
  exact zb_mono this (by omega) (hZ1 hZ)

theorem cA_z {s ck p q : ℕ} (hs : s ≤ Z ^ p) (hck : ck ≤ Z ^ q) (hq : q ≤ 4 * p + 9) :
    E5B.cA s ck ≤ Z ^ (6 * p + 19) := by
  have h6 := zb_cmul (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ) hs
  have h1 := cAN_z hZ h6 hck (p := 1 + p) (by omega)
  have h2 := zb_cmul (cnum (by norm_num : 20 ≤ 2 ^ 200) hZ) hs
  have h3 := zb_add' h1 h2 (hZ2 hZ) (r := 6 * (1 + p) + 11) (by omega) (by omega)
  have h4 := zb_add' h3 (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := 6 * (1 + p) + 12) (by omega) (by omega)
  unfold E5B.cA
  exact zb_mono h4 (by omega) (hZ1 hZ)

theorem cPR_z {s p : ℕ} (hs : s ≤ Z ^ p) : E5C2.cPR s ≤ Z ^ (3 * p + 4) := by
  have h1 := zb_succ hs (hZ2 hZ)
  have h2 := zb_pow h1 3
  have h3 := zb_cmul (cnum (by norm_num : 3000 ≤ 2 ^ 200) hZ) h2
  unfold E5C2.cPR
  exact zb_mono h3 (by omega) (hZ1 hZ)

theorem cApplyPlan_z {s ck p q : ℕ} (hs : s ≤ Z ^ p) (hck : ck ≤ Z ^ q) (hq : q ≤ 4 * p + 9) :
    E5C3.cApplyPlan s ck ≤ Z ^ (7 * p + 24) := by
  have hcA := cA_z hZ hs hck hq
  have T1 := zb_mul hcA hs
  have s1 := zb_cmul (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ) hs
  have s2 := zb_add' s1 (zb_num (cnum (by norm_num : 60 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := p + 1) (by omega) (by omega)
  have T2 := zb_mul hs s2
  have s5 := zb_cmul (cnum (by norm_num : 5 ≤ 2 ^ 200) hZ) hs
  have hpr := cPR_z hZ s5
  have T3a := zb_mul hpr hs
  have s6 := zb_succ hs (hZ2 hZ)
  have s7 := zb_cmul (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ) s6
  have T3b := zb_add' T3a s7 (hZ2 hZ) (r := 4 * p + 8) (by omega) (by omega)
  have T3 := zb_add' T3b (zb_num (cnum (by norm_num : 40 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := 4 * p + 9) (by omega) (by omega)
  have u1 := zb_cmul (cnum (by norm_num : 58 ≤ 2 ^ 200) hZ) hs
  have u3 := zb_add' u1 (zb_num (cnum (by norm_num : 11 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := p + 1) (by omega) (by omega)
  have u2 := zb_succ u3 (hZ2 hZ)
  have T4a := zb_cmul (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ) u2
  have T4 := zb_mul T4a u3
  have v1 := zb_add' T1 T2 (hZ2 hZ) (r := 7 * p + 19) (by omega) (by omega)
  have v2 := zb_add' v1 T3 (hZ2 hZ) (r := 7 * p + 20) (by omega) (by omega)
  have v3 := zb_add' v2 T4 (hZ2 hZ) (r := 7 * p + 21) (by omega) (by omega)
  have v4 := zb_add' v3 (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := 7 * p + 22) (by omega) (by omega)
  unfold E5C3.cApplyPlan
  exact zb_mono v4 (by omega) (hZ1 hZ)

theorem fpBound'_z {s L Ly p t : ℕ} (hs : s ≤ Z ^ p) (h4 : 4 ^ (L + L + 1) ≤ Z ^ t)
    (h3 : 3 ^ (2 * (L + L) + 1 + Ly) ≤ Z ^ t) (hL : 2 * (L + L) + 1 + 2 ≤ Z ^ t) :
    E5D.fpBound' s L Ly ≤ Z ^ (2 * p + 4 * t + 8) := by
  have hs1 := zb_succ hs (hZ2 hZ)
  have A1 := zb_cmul (cnum (by norm_num : 6000 ≤ 2 ^ 200) hZ) hs1
  have A2 := zb_mul A1 hs1
  have A3 := zb_pow (zb_succ h4 (hZ2 hZ)) 2
  have A4 := zb_mul A2 A3
  have A5 := zb_pow hL 2
  have A6 := zb_mul A4 A5
  have B1 := zb_cmul (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ) h3
  have hL1 : 2 * (L + L) + 1 ≤ Z ^ t := le_trans (by omega) hL
  have B2 := zb_cmul (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ) hL1
  have B3 := zb_add' B1 B2 (hZ2 hZ) (r := t + 1) (by omega) (by omega)
  have B4 := zb_add' B3 (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := t + 2) (by omega) (by omega)
  have B5 := zb_mul h4 B4
  have C1 := zb_add' hs hs (hZ2 hZ) (r := p) le_rfl le_rfl
  have C2 := zb_cmul (cnum (by norm_num : 12 ≤ 2 ^ 200) hZ) C1
  have D1 := zb_add' A6 B5 (hZ2 hZ) (r := 2 * p + 4 * t + 5) (by omega) (by omega)
  have D2 := zb_add' D1 C2 (hZ2 hZ) (r := 2 * p + 4 * t + 6) (by omega) (by omega)
  have D3 := zb_add' D2 (zb_num (cnum (by norm_num : 200 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := 2 * p + 4 * t + 7) (by omega) (by omega)
  unfold E5D.fpBound'
  exact zb_mono D3 (by omega) (hZ1 hZ)

theorem cMA'_z {s L Ly p t : ℕ} (hs : s ≤ Z ^ p) (h4 : 4 ^ (L + L + 1) ≤ Z ^ t)
    (h3 : 3 ^ (2 * (L + L) + 1 + Ly) ≤ Z ^ t) (hL : 2 * (L + L) + 1 + 2 ≤ Z ^ t) :
    E5D.cMA' s L Ly ≤ Z ^ (2 * p + 4 * t + 11) := by
  have F := fpBound'_z hZ hs h4 h3 hL
  have hs3 := zb_add' hs (zb_num (cnum (by norm_num : 3 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := p + 1) (by omega) (by omega)
  have G1 := zb_cmul (cnum (by norm_num : 600 ≤ 2 ^ 200) hZ) (zb_pow hs3 2)
  have G2 := zb_cmul (cnum (by norm_num : 200 ≤ 2 ^ 200) hZ) (zb_succ hs (hZ2 hZ))
  have H1 := zb_add' F G1 (hZ2 hZ) (r := 2 * p + 4 * t + 8) (by omega) (by omega)
  have H2 := zb_add' H1 G2 (hZ2 hZ) (r := 2 * p + 4 * t + 9) (by omega) (by omega)
  have H3 := zb_add' H2 (zb_num (cnum (by norm_num : 300 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := 2 * p + 4 * t + 10) (by omega) (by omega)
  unfold E5D.cMA'
  exact zb_mono H3 (by omega) (hZ1 hZ)

theorem cMergeReal'_z {s L Ly ck p q t : ℕ} (hs : s ≤ Z ^ p) (hck : ck ≤ Z ^ q) (hq : q ≤ 4 * p + 9)
    (h4 : 4 ^ (L + L + 1) ≤ Z ^ t) (h3 : 3 ^ (2 * (L + L) + 1 + Ly) ≤ Z ^ t) (hL : 2 * (L + L) + 1 + 2 ≤ Z ^ t) :
    E5D.cMergeReal' s L Ly ck ≤ Z ^ (7 * p + 4 * t + 24) := by
  have hcA := cA_z hZ hs hck hq
  have T1 := zb_cmul (cnum (by norm_num : 2 ≤ 2 ^ 200) hZ) (zb_mul hcA hs)
  have s5 := zb_cmul (cnum (by norm_num : 5 ≤ 2 ^ 200) hZ) hs
  have hma := cMA'_z hZ s5 h4 h3 hL
  have T2 := zb_mul hma s5
  have ss := zb_mul hs hs
  have w1 := zb_cmul (cnum (by norm_num : 900 ≤ 2 ^ 200) hZ) ss
  have w2 := zb_succ w1 (hZ2 hZ)
  have w3 := zb_cmul (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ) w2
  have T3 := zb_mul w3 w1
  have v1 := zb_add' T1 T2 (hZ2 hZ) (r := 7 * p + 4 * t + 21) (by omega) (by omega)
  have v2 := zb_add' v1 T3 (hZ2 hZ) (r := 7 * p + 4 * t + 22) (by omega) (by omega)
  have v3 := zb_add' v2 (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) (hZ2 hZ) (r := 7 * p + 4 * t + 23) (by omega) (by omega)
  unfold E5D.cMergeReal'
  exact zb_mono v3 (by omega) (hZ1 hZ)

end zcalc

end E6b
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6bNum` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6b (6): the arithmetic of the cost bounds

`Yk k = (k+2)^3`, `Zc M k = (M+1) · 2^(1728 Yk k)`: a *common ceiling*.  Every quantity of the cost analysis is at most
a power of `Zc M k`: `M+1 ≤ Zc`, `2^(1728 Y) ≤ Zc`, `k+2 ≤ Y ≤ 2^Y`, constants `≤ 2^Y` (as `Y ≥ 8`).  The cost functions of
E2/E3/E5 are polynomials in the sizes, so bounding all their arguments by `Zc^a` bounds them by `C · Zc^d`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open E5R E5D

/-- `(k+2)^3` -/
def Yk (k : ℕ) : ℕ := (k + 2) ^ 3

/-- the common ceiling -/
def Zc (M k : ℕ) : ℕ := (M + 1) * 2 ^ (1728 * Yk k)

theorem Yk_ge (k : ℕ) : 8 ≤ Yk k := E4.Y_ge k
theorem lin_Yk (k : ℕ) : k + 2 ≤ Yk k := E4.X_le_Y k

theorem Zc_ge_M (M k : ℕ) : M + 1 ≤ Zc M k := by
  unfold Zc
  exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)

theorem Zc_ge_pow (M k : ℕ) : 2 ^ (1728 * Yk k) ≤ Zc M k := by
  unfold Zc
  exact Nat.le_mul_of_pos_left _ (by omega)

/-! ## the parameters of the `realIntro` call -/

/-- bound on the sizes of everything `realIntro` is applied to (trees, plans, characteristics) -/
def sI (M k : ℕ) : ℕ := 16000 * Yk k * (M + 1)
/-- bound on the run-sequence length of the results of `introPlans`: `2 (k+3) + 1` -/
def LrI (k : ℕ) : ℕ := 2 * k + 7
/-- bound on the number of plans -/
def LenI (k : ℕ) : ℕ := 2 ^ (1728 * Yk k)
/-- bound on every natural number of the input of `introPlans` -/
def UI (M k : ℕ) : ℕ := M + 128 * Yk k + k + 2

/-! ### the basic bounds by powers of `Zc` -/

theorem Zc_big (M k : ℕ) : 2 ^ 200 ≤ Zc M k :=
  le_trans (Nat.pow_le_pow_right (by norm_num) (by have := Yk_ge k; omega)) (Zc_ge_pow M k)

theorem b_pow (M k e j : ℕ) (he : e ≤ 1728 * Yk k * j) : 2 ^ e ≤ Zc M k ^ j := by
  calc 2 ^ e ≤ 2 ^ (1728 * Yk k * j) := Nat.pow_le_pow_right (by norm_num) he
    _ = (2 ^ (1728 * Yk k)) ^ j := by rw [pow_mul]
    _ ≤ Zc M k ^ j := Nat.pow_le_pow_left (Zc_ge_pow M k) j

theorem b_M (M k : ℕ) : M + 1 ≤ Zc M k ^ 1 := by simpa using Zc_ge_M M k

theorem b_Y (M k : ℕ) : Yk k ≤ Zc M k ^ 1 := by
  have h1 : Yk k < 2 ^ Yk k := Nat.lt_two_pow_self
  have h2 := b_pow M k (Yk k) 1 (by have := Yk_ge k; omega)
  omega

theorem b_k (M k : ℕ) : k + 2 ≤ Zc M k ^ 1 := le_trans (lin_Yk k) (b_Y M k)

theorem b_sI (M k : ℕ) : sI M k ≤ Zc M k ^ 1 := by
  unfold sI
  have h1 : Yk k < 2 ^ Yk k := Nat.lt_two_pow_self
  have h2 : 16000 * Yk k ≤ 2 ^ (1728 * Yk k) := by
    have h3 : 16000 * Yk k ≤ 2 ^ 14 * 2 ^ Yk k := Nat.mul_le_mul (by norm_num) (le_of_lt h1)
    have h4 : 2 ^ 14 * 2 ^ Yk k = 2 ^ (14 + Yk k) := by rw [pow_add]
    have h5 : 2 ^ (14 + Yk k) ≤ 2 ^ (1728 * Yk k) := Nat.pow_le_pow_right (by norm_num) (by have := Yk_ge k; omega)
    omega
  have := Nat.mul_le_mul_right (M + 1) h2
  unfold Zc
  simpa [mul_comm] using this

theorem b_UI (M k : ℕ) : UI M k + 1 ≤ Zc M k ^ 1 := by
  unfold UI
  have h1 : Yk k < 2 ^ Yk k := Nat.lt_two_pow_self
  have hk := lin_Yk k
  have h2 : 128 * Yk k + k + 3 ≤ 2 ^ (1728 * Yk k) := by
    have h3 : 130 * Yk k ≤ 2 ^ 8 * 2 ^ Yk k := Nat.mul_le_mul (by norm_num) (le_of_lt h1)
    have h4 : 2 ^ 8 * 2 ^ Yk k = 2 ^ (8 + Yk k) := by rw [pow_add]
    have h5 : 2 ^ (8 + Yk k) ≤ 2 ^ (1728 * Yk k) := Nat.pow_le_pow_right (by norm_num) (by have := Yk_ge k; omega)
    omega
  have h6 : M + 128 * Yk k + k + 2 + 1 ≤ (M + 1) * (128 * Yk k + k + 3) := by nlinarith
  have := Nat.mul_le_mul_left (M + 1) h2
  unfold Zc
  simp only [pow_one]
  nlinarith

theorem b_3pow (M k n : ℕ) (hn : 2 * n ≤ 1728 * Yk k) : 3 ^ n ≤ Zc M k ^ 1 := by
  have h1 : 3 ^ n ≤ 4 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have h2 : 4 ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have := b_pow M k (2 * n) 1 (by omega)
  omega

theorem b_4pow (M k n : ℕ) (hn : 2 * n ≤ 1728 * Yk k) : 4 ^ n ≤ Zc M k ^ 1 := by
  have h2 : 4 ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have := b_pow M k (2 * n) 1 (by omega)
  omega

theorem introCCost_z (M k : ℕ) : E3C.introCCost (UI M k + 1) (3 * (k + 2)) ≤ Zc M k ^ 18 := by
  unfold E3C.introCCost
  have hZ := Zc_big M k
  have h1 := zb_mul (zb_num (cnum (by norm_num : 10 ^ 16 ≤ 2 ^ 200) hZ)) (zb_pow (b_UI M k) 15)
  have h2 : 2 ^ (128 * (3 * (k + 2)) ^ 3) ≤ Zc M k ^ 2 := b_pow M k _ 2 (by unfold Yk; nlinarith)
  have := zb_mul h1 h2
  exact zb_mono this (by omega) (hZ1 hZ)

theorem cip_z (M k cip : ℕ) (hcip : cip ≤ 2 * E3C.introCCost (UI M k + 1) (3 * (k + 2))) : cip ≤ Zc M k ^ 19 := by
  have hZ := Zc_big M k
  have h := zb_cmul (cnum (by norm_num : 2 ≤ 2 ^ 200) hZ) (introCCost_z M k)
  exact le_trans hcip (zb_mono h (by omega) (hZ1 hZ))

/-- the exponent of the `realIntro` cost -/
def pRI : ℕ := 40

theorem numRI_cost (M k cip : ℕ) (hcip : cip ≤ 2 * E3C.introCCost (UI M k + 1) (3 * (k + 2))) :
    cRealIntro (sI M k) (LenI k) (E5Inst.cNormE2 (5 * sI M k)) (E5Inst.cNormE2 (sI M k))
      (E5Inst.cDomE2 (LrI k) (sI M k)) (E5Inst.cKeyE2 (6 * sI M k)) cip ≤ Zc M k ^ pRI := by
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have hs := b_sI M k
  have hs5 := zb_cmul (cnum (by norm_num : 5 ≤ 2 ^ 200) hZ) hs
  have hs6 := zb_cmul (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ) hs
  have hn5 := cNormE2_z hZ hs5
  have hn := cNormE2_z hZ hs
  have h3 : 3 ^ (2 * LrI k) ≤ Zc M k ^ 1 := b_3pow M k _ (by unfold LrI; have := Yk_ge k; have := lin_Yk k; omega)
  have hd := cDomE2_z hZ h3 (le_refl 1) hs
  have hk := cKeyE2_z hZ hs6
  have hap := cApplyPlan_z hZ hs hk (q := 2 * (1 + 1) + 4) (by omega)
  have hcipZ := cip_z M k cip hcip
  have hL : LenI k ≤ Zc M k ^ 1 := by unfold LenI; simpa using b_pow M k (1728 * Yk k) 1 (by omega)
  -- part 1
  have a := zb_cmul (cnum (by norm_num : 200 ≤ 2 ^ 200) hZ) (zb_succ hs hZ2')
  have b := zb_mul a hs
  have c := zb_add' b hn5 hZ2' (r := 5 * (1 + 1) + 6) (by omega) le_rfl
  have d := zb_add' c (zb_num (cnum (by norm_num : 8 ≤ 2 ^ 200) hZ)) hZ2' (r := 5 * (1 + 1) + 6 + 1) (by omega) (by omega)
  have e := zb_add' d hcipZ hZ2' (r := 19) (by omega) le_rfl
  -- part 3
  have f1 := zb_add' hn hd hZ2' (r := 5 * 1 + 6) (by omega) (by omega)
  have f2 := zb_add' f1 (zb_cmul (cnum (by norm_num : 30 ≤ 2 ^ 200) hZ) hs) hZ2' (r := 5 * 1 + 6 + 1) (by omega) (by omega)
  have f3 := zb_add' f2 (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) hZ2' (r := 5 * 1 + 6 + 2) (by omega) (by omega)
  have g1 := zb_mul hL f3
  have g2 := zb_add' (zb_cmul (cnum (by norm_num : 24 ≤ 2 ^ 200) hZ) hL) (zb_num (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ)) hZ2'
    (r := 2) (by omega) (by omega)
  have g3 := zb_add' g2 g1 hZ2' (r := 1 + (5 * 1 + 6 + 2 + 1)) (by omega) (by omega)
  have h1 := zb_add' e g3 hZ2' (r := 20) (by omega) (by omega)
  have h2 := zb_add' h1 hap hZ2' (r := 7 * 1 + 24) (by omega) (by omega)
  have h3' := zb_add' h2 (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) hZ2' (r := 7 * 1 + 24 + 1) (by omega) (by omega)
  unfold cRealIntro cPredI
  exact zb_mono h3' (by unfold pRI; omega) (hZ1 hZ)

theorem numRI_B (M k cip : ℕ) (hcip : cip ≤ 2 * E3C.introCCost (UI M k + 1) (3 * (k + 2))) :
    20000 + 20000 * (sI M k + 1) + E5Inst.cKeyE2 (6 * sI M k) + E5Inst.cNormE2 (5 * sI M k) +
      E5Inst.cNormE2 (sI M k) + E5Inst.cDomE2 (LrI k) (sI M k) + cip ≤ Zc M k ^ pRI := by
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have hs := b_sI M k
  have hs5 := zb_cmul (cnum (by norm_num : 5 ≤ 2 ^ 200) hZ) hs
  have hs6 := zb_cmul (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ) hs
  have hn5 := cNormE2_z hZ hs5
  have hn := cNormE2_z hZ hs
  have h3 : 3 ^ (2 * LrI k) ≤ Zc M k ^ 1 := b_3pow M k _ (by unfold LrI; have := Yk_ge k; have := lin_Yk k; omega)
  have hd := cDomE2_z hZ h3 (le_refl 1) hs
  have hk := cKeyE2_z hZ hs6
  have hcipZ := cip_z M k cip hcip
  have a := zb_cmul (cnum (by norm_num : 20000 ≤ 2 ^ 200) hZ) (zb_succ hs hZ2')
  have b := zb_add' (zb_num (cnum (by norm_num : 20000 ≤ 2 ^ 200) hZ)) a hZ2' (r := 3) (by omega) (by omega)
  have c := zb_add' b hk hZ2' (r := 2 * 2 + 4) (by omega) le_rfl
  have d := zb_add' c hn5 hZ2' (r := 5 * (1 + 1) + 6) (by omega) le_rfl
  have e := zb_add' d hn hZ2' (r := 5 * (1 + 1) + 6 + 1) (by omega) (by omega)
  have f := zb_add' e hd hZ2' (r := 5 * (1 + 1) + 6 + 2) (by omega) (by omega)
  have g := zb_add' f hcipZ hZ2' (r := 19) (by omega) le_rfl
  exact zb_mono g (by unfold pRI; omega) (hZ1 hZ)

/-! ## the parameters of the `realJoin` call -/

/-- bound on the run-sequence length of the join options: `2 (k+1) + 1` -/
def LrJ (k : ℕ) : ℕ := 2 * k + 3
/-- bound on the number of join options -/
def LenJ (k : ℕ) : ℕ := 2 ^ (432 * Yk k)
/-- bound on the cost `cJ` of the join call inside `realJoin` -/
def cJb (M k : ℕ) : ℕ :=
  28000 * (256 * Yk k + 1) * 2 ^ (1296 * Yk k) + 2000 * (256 * Yk k + 1) + 2000 + 6000 * 2 ^ (1296 * Yk k) + 1000

theorem cJb_z (M k : ℕ) : cJb M k ≤ Zc M k ^ 9 := by
  unfold cJb
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have hY := b_Y M k
  have h256 := zb_succ (zb_cmul (cnum (by norm_num : 256 ≤ 2 ^ 200) hZ) hY) hZ2'
  have hP : 2 ^ (1296 * Yk k) ≤ Zc M k ^ 1 := b_pow M k _ 1 (by omega)
  have A1 := zb_cmul (cnum (by norm_num : 28000 ≤ 2 ^ 200) hZ) h256
  have A2 := zb_mul A1 hP
  have B1 := zb_cmul (cnum (by norm_num : 2000 ≤ 2 ^ 200) hZ) h256
  have C1 := zb_cmul (cnum (by norm_num : 6000 ≤ 2 ^ 200) hZ) hP
  have v1 := zb_add' A2 B1 hZ2' (r := 5) (by omega) (by omega)
  have v2 := zb_add' v1 (zb_num (cnum (by norm_num : 2000 ≤ 2 ^ 200) hZ)) hZ2' (r := 6) (by omega) (by omega)
  have v3 := zb_add' v2 C1 hZ2' (r := 7) (by omega) (by omega)
  have v4 := zb_add' v3 (zb_num (cnum (by norm_num : 1000 ≤ 2 ^ 200) hZ)) hZ2' (r := 8) (by omega) (by omega)
  exact zb_mono v4 (by omega) (hZ1 hZ)

/-- the exponent of the `realJoin` cost -/
def pRJ : ℕ := 50

theorem numRJ_cost (M k cj : ℕ) (hcj : cj ≤ cJb M k) :
    cRealJoin' (sI M k) (k + 1) (LrJ k) (LenJ k) (E5Inst.cNormE2 (5 * sI M k))
      (E5Inst.cDomE2 (LrJ k) (sI M k)) (E5Inst.cKeyE2 (6 * sI M k)) cj ≤ Zc M k ^ pRJ := by
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have hs := b_sI M k
  have hs5 := zb_cmul (cnum (by norm_num : 5 ≤ 2 ^ 200) hZ) hs
  have hs6 := zb_cmul (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ) hs
  have hn5 := cNormE2_z hZ hs5
  have h3 : 3 ^ (2 * LrJ k) ≤ Zc M k ^ 1 := b_3pow M k _ (by unfold LrJ; have := Yk_ge k; have := lin_Yk k; omega)
  have hd := cDomE2_z hZ h3 (le_refl 1) hs
  have hk := cKeyE2_z hZ hs6
  have hcjZ : cj ≤ Zc M k ^ 9 := le_trans hcj (cJb_z M k)
  have hL : LenJ k ≤ Zc M k ^ 1 := by unfold LenJ; simpa using b_pow M k (432 * Yk k) 1 (by omega)
  have L4 : 4 ^ ((k + 1) + (k + 1) + 1) ≤ Zc M k ^ 2 :=
    zb_mono (b_4pow M k _ (by have := Yk_ge k; have := lin_Yk k; omega)) (by omega) (hZ1 hZ)
  have L3 : 3 ^ (2 * ((k + 1) + (k + 1)) + 1 + LrJ k) ≤ Zc M k ^ 2 :=
    zb_mono (b_3pow M k _ (by unfold LrJ; have := Yk_ge k; have := lin_Yk k; omega)) (by omega) (hZ1 hZ)
  have LL : 2 * ((k + 1) + (k + 1)) + 1 + 2 ≤ Zc M k ^ 2 := by
    have := zb_cmul (cnum (by norm_num : 4 ≤ 2 ^ 200) hZ) (b_k M k)
    exact le_trans (by omega) (zb_mono this (by omega) (hZ1 hZ))
  have hMR := cMergeReal'_z hZ hs hk (q := 2 * 2 + 4) (by omega) L4 L3 LL
  have a := zb_cmul (cnum (by norm_num : 200 ≤ 2 ^ 200) hZ) (zb_succ hs hZ2')
  have b := zb_mul a hs
  have c := zb_add' b hn5 hZ2' (r := 5 * (1 + 1) + 6) (by omega) le_rfl
  have d := zb_add' c (zb_num (cnum (by norm_num : 8 ≤ 2 ^ 200) hZ)) hZ2' (r := 5 * (1 + 1) + 6 + 1) (by omega) (by omega)
  have d2 := zb_cmul (cnum (by norm_num : 2 ≤ 2 ^ 200) hZ) d
  have e := zb_add' d2 hcjZ hZ2' (r := 20) (by omega) (by omega)
  have f1 := zb_add' hd (zb_num (cnum (by norm_num : 10 ≤ 2 ^ 200) hZ)) hZ2' (r := 7) (by omega) (by omega)
  have f2 := zb_mul hL f1
  have g2 := zb_add' (zb_cmul (cnum (by norm_num : 24 ≤ 2 ^ 200) hZ) hL) (zb_num (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ)) hZ2'
    (r := 2) (by omega) (by omega)
  have g3 := zb_add' g2 f2 hZ2' (r := 9) (by omega) (by omega)
  have h1 := zb_add' e g3 hZ2' (r := 21) (by omega) (by omega)
  have h2 := zb_add' h1 hMR hZ2' (r := 7 * 1 + 4 * 2 + 24) (by omega) (by omega)
  have h3' := zb_add' h2 (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) hZ2' (r := 7 * 1 + 4 * 2 + 25) (by omega) (by omega)
  unfold cRealJoin'
  exact zb_mono h3' (by unfold pRJ; omega) (hZ1 hZ)

theorem numRJ_B (M k cj : ℕ) (hcj : cj ≤ cJb M k) :
    200000 + 100000 * (sI M k + 1) ^ 2 + E5Inst.cKeyE2 (6 * sI M k) + E5Inst.cNormE2 (5 * sI M k) +
      E5Inst.cDomE2 (LrJ k) (sI M k) + cj ≤ Zc M k ^ pRJ := by
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have hs := b_sI M k
  have hs5 := zb_cmul (cnum (by norm_num : 5 ≤ 2 ^ 200) hZ) hs
  have hs6 := zb_cmul (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ) hs
  have hn5 := cNormE2_z hZ hs5
  have h3 : 3 ^ (2 * LrJ k) ≤ Zc M k ^ 1 := b_3pow M k _ (by unfold LrJ; have := Yk_ge k; have := lin_Yk k; omega)
  have hd := cDomE2_z hZ h3 (le_refl 1) hs
  have hk := cKeyE2_z hZ hs6
  have hcjZ : cj ≤ Zc M k ^ 9 := le_trans hcj (cJb_z M k)
  have a := zb_cmul (cnum (by norm_num : 100000 ≤ 2 ^ 200) hZ) (zb_pow (zb_succ hs hZ2') 2)
  have b := zb_add' (zb_num (cnum (by norm_num : 200000 ≤ 2 ^ 200) hZ)) a hZ2' (r := 5) (by omega) (by omega)
  have c := zb_add' b hk hZ2' (r := 2 * 2 + 4) (by omega) (by omega)
  have d := zb_add' c hn5 hZ2' (r := 5 * (1 + 1) + 6) (by omega) (by omega)
  have e := zb_add' d hd hZ2' (r := 5 * (1 + 1) + 7) (by omega) (by omega)
  have f := zb_add' e hcjZ hZ2' (r := 5 * (1 + 1) + 8) (by omega) (by omega)
  exact zb_mono f (by unfold pRJ; omega) (hZ1 hZ)

end E6b
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6bRealI` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# WP E6b (7): `realIntro` on the trees built by `extract`

`realIntro_at`: the F-function `E5R.fRealIntro` computes `realIntro (k+1) v N Bs t0 target` within `Zc^pRI` steps, where
`t0` is a real decomposition returned by the extraction of the child (`PTD adj c k t0`), `Bs = c.bag`.

What is used from the math layer: `PTD adj c k t0` (so `t0.char Bs` is a well-formed characteristic, `char_wf`),
`tables_wf` (the target is well formed), the P1 bounds (`Wf.vsz_le`, `introPlans_length_le`, `introPlans_vsz_le`), the
plan-size and entry bounds of `E6bMath2`, and `ir_aux` (goodness of the un-normalised results, hence of their `norm`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT E5R

/-- `10 U + 600` and the polynomial part of `cIP` are bounded by `2 · introCCost` -/
theorem cIP_le (Bs : Finset ℕ) (kmax U c : ℕ) (hb : Bs.card ≤ U) (hk : kmax + 1 ≤ U + 1) (hc : c ≤ U) :
    (100 * (1000 * (U + 1) * (U + 1) * (3 * runBound Bs.card) * E3C.Gp Bs.card kmax) +
      4 * (1000 * ((U + 1) * (2 ^ Bs.card + 1)) * (U + 1) * E3C.Gp Bs.card kmax) +
      500 * ((U + 1) * E3C.Gp Bs.card kmax) + 1000 * (U + 1)) * (3 * c - 1) + (10 * U + 600) ≤
    2 * E3C.introCCost (U + 1) (Bs.card + kmax + 2) := by
  have hX1 : 1 ≤ 2 ^ (64 * (Bs.card + kmax + 2) ^ 3) := Nat.one_le_two_pow
  have hW1 : 1 ≤ U + 1 := by omega
  have hGX := E3C.Gp_le Bs.card kmax
  have hΩX : 2 ^ Bs.card + 1 ≤ 2 * 2 ^ (64 * (Bs.card + kmax + 2) ^ 3) := by
    have h1 : 2 ^ Bs.card ≤ 2 ^ (64 * (Bs.card + kmax + 2) ^ 3) := Nat.pow_le_pow_right (by norm_num) (by
      have : Bs.card ≤ (Bs.card + kmax + 2) ^ 3 := by
        have : Bs.card ≤ Bs.card + kmax + 2 := by omega
        calc Bs.card ≤ Bs.card + kmax + 2 := this
          _ = (Bs.card + kmax + 2) ^ 1 := (pow_one _).symm
          _ ≤ (Bs.card + kmax + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega)
    omega
  obtain ⟨hMW, hSnW⟩ := E3C.Sn_le Bs.card kmax (U + 1) (by omega) (by omega)
  have hcost := E3C.final_arith (U + 1) (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) (runBound Bs.card) (E3C.Gp Bs.card kmax)
    (2 ^ Bs.card + 1) ((2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10)) c
    hW1 hX1 hGX hΩX hMW hSnW (by omega)
  have e : E3C.introCCost (U + 1) (Bs.card + kmax + 2) =
      10 ^ 16 * (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 := by
    unfold E3C.introCCost
    rw [← pow_mul, show 64 * (Bs.card + kmax + 2) ^ 3 * 2 = 128 * (Bs.card + kmax + 2) ^ 3 by ring]
  have h10 : 10 * U + 600 ≤ E3C.introCCost (U + 1) (Bs.card + kmax + 2) := by
    rw [e]
    have h1 : 1 ≤ (U + 1) ^ 15 := Nat.one_le_pow _ _ hW1
    have h2 : U + 1 ≤ (U + 1) ^ 15 := by
      calc U + 1 = (U + 1) ^ 1 := (pow_one _).symm
        _ ≤ (U + 1) ^ 15 := Nat.pow_le_pow_right hW1 (by norm_num)
    have h3 : 1 ≤ (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 := Nat.one_le_pow _ _ hX1
    have h4 : (U + 1) ^ 15 ≤ (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h5 : 10 ^ 16 * (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 =
        10 ^ 16 * ((U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2) := by rw [mul_assoc]
    rw [h5]; omega
  rw [e] at h10 ⊢
  omega

/-! ### numerical facts about `k` -/

theorem wf_sz_le {Bs : Finset ℕ} {k : ℕ} {t : CT} (hb : Bs.card ≤ k + 2) (h : t.Wf Bs (k + 1)) :
    sz t ≤ 128 * (k + 2) ^ 3 := by
  have h1 := Lax117284Proofs.Treewidth.Fun.CT.Wf.sz_le h
  refine le_trans h1 (le_trans ?_ (runBound_mul_le k))
  have h2 : runBound Bs.card ≤ runBound (k + 2) := by
    unfold runBound; exact Nat.mul_le_mul (by omega) (by omega)
  exact Nat.mul_le_mul h2 (by omega)

theorem plan_sz_num (M k b : ℕ) (hb : b ≤ k + 2) :
    2 * runBound b + planSzBound (runBound b) b +
      (2 * runBound b + b + 4) * (2 * b + 4 * (k + 1) + 10) + 2 ≤ sI M k := by
  unfold sI Yk planSzBound runBound
  have h1 : (2 * b + 2) * (2 * b + 2) ≤ (2 * k + 6) * (2 * k + 6) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (b + 1) * (2 * b + 2) ≤ (k + 3) * (2 * k + 6) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : (2 * (2 * b + 2) * (2 * b + 2) + b + 4) * (2 * b + 4 * (k + 1) + 10) ≤
      (2 * (2 * k + 6) * (2 * k + 6) + (k + 2) + 4) * (2 * (k + 2) + 4 * (k + 1) + 10) := by
    apply Nat.mul_le_mul <;> nlinarith
  have hM : 1 ≤ M + 1 := by omega
  have h4 : 16000 * (k + 2) ^ 3 ≤ 16000 * (k + 2) ^ 3 * (M + 1) := Nat.le_mul_of_pos_right _ hM
  have h5 : (2 * (2 * b + 2) * (2 * b + 2) + b + 4) * (2 * b + 4 * (k + 1) + 10) =
      (2 * ((2 * b + 2) * (2 * b + 2)) + b + 4) * (2 * b + 4 * (k + 1) + 10) := by ring
  nlinarith [Nat.zero_le k, sq_nonneg k, pow_pos (show 0 < k + 2 by omega) 3]

theorem t0_sz_num (M k cs : ℕ) (hc : cs ≤ M) : (2 * k + 8) * (2 * k + 6) * cs ≤ sI M k := by
  unfold sI Yk
  have h1 : (2 * k + 8) * (2 * k + 6) * cs ≤ (2 * k + 8) * (2 * k + 6) * (M + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : (2 * k + 8) * (2 * k + 6) ≤ 16000 * (k + 2) ^ 3 := by
    nlinarith [Nat.zero_le k, sq_nonneg k, pow_pos (show 0 < k + 2 by omega) 3]
  exact le_trans h1 (Nat.mul_le_mul_right _ h2)

theorem tg_sz_num (M k : ℕ) : 128 * (k + 2) ^ 3 ≤ sI M k := by
  unfold sI Yk
  have : 1 ≤ M + 1 := by omega
  nlinarith [pow_pos (show 0 < k + 2 by omega) 3]

theorem bag_sz_num (M k : ℕ) : 2 * (k + 2) + 1 ≤ sI M k := by
  unfold sI Yk
  have : 1 ≤ M + 1 := by omega
  nlinarith [pow_pos (show 0 < k + 2 by omega) 3, sq_nonneg k]

theorem introCCost_mono {W s s' : ℕ} (h : s ≤ s') : E3C.introCCost W s ≤ E3C.introCCost W s' := by
  unfold E3C.introCCost
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 3)))

theorem intro_len_num (k b : ℕ) (hb : b ≤ k + 2) : 64 * (b + (k + 1) + 2) ^ 3 ≤ 1728 * Yk k := by
  unfold Yk
  have h1 : b + (k + 1) + 2 ≤ 3 * (k + 2) := by omega
  have h2 : (b + (k + 1) + 2) ^ 3 ≤ (3 * (k + 2)) ^ 3 := Nat.pow_le_pow_left h1 3
  calc 64 * (b + (k + 1) + 2) ^ 3 ≤ 64 * (3 * (k + 2)) ^ 3 := Nat.mul_le_mul_left _ h2
    _ = 1728 * (k + 2) ^ 3 := by ring

/-! ### the `ExtIP` instance -/

/-- the instance of `E5.ExtIP` for characteristics over `Bs` with entries `≤ kmax` and naturals `≤ U` -/
def ipInst {Δ' : ℕ → Option Tm} (hΔ : E3C.Δ ⊑ Δ') (Bs : Finset ℕ) (kmax U : ℕ) : E5.ExtIP Δ' :=
  E5Inst.extIP_e3 U (1000 * (U + 1) * (U + 1)) (1000 * (U + 1) * (U + 1) * (3 * runBound Bs.card))
    (E3C.Gp Bs.card kmax) (2 ^ Bs.card + 1) (1000 * ((U + 1) * (2 ^ Bs.card + 1)))
    (100 * (1000 * (U + 1) * (U + 1) * (3 * runBound Bs.card) * E3C.Gp Bs.card kmax) +
      4 * (1000 * ((U + 1) * (2 ^ Bs.card + 1)) * (U + 1) * E3C.Gp Bs.card kmax) +
      500 * ((U + 1) * E3C.Gp Bs.card kmax) + 1000 * (U + 1))
    Bs kmax (runBound Bs.card) le_rfl le_rfl le_rfl le_rfl
    (fun v N ν hg hm hc => E3C.hG_of_good Bs kmax v N ν (runBound Bs.card) rfl hg hm hc)
    (fun N ν hg => E3C.hΩ_of_good Bs N ν hg) hΔ

theorem ipInst_ip {Δ' : ℕ → Option Tm} (hΔ : E3C.Δ ⊑ Δ') (Bs : Finset ℕ) (kmax U : ℕ) :
    (ipInst hΔ Bs kmax U).ip = E3C.fIntroPlans := rfl

theorem ipInst_PIP {Δ' : ℕ → Option Tm} (hΔ : E3C.Δ ⊑ Δ') (Bs : Finset ℕ) (kmax U v : ℕ) (N : Finset ℕ) (t : CT) :
    (ipInst hΔ Bs kmax U).PIP v N t ↔ (v ≤ U ∧ N.card ≤ U ∧ sz t ≤ U ∧ mx t ≤ U ∧ Good Bs t ∧ maxEntry t ≤ kmax ∧
      count t ≤ runBound Bs.card) := Iff.rfl

theorem ipInst_cIP {Δ' : ℕ → Option Tm} (hΔ : E3C.Δ ⊑ Δ') (Bs : Finset ℕ) (kmax U v : ℕ) (N : Finset ℕ) (t : CT) :
    (ipInst hΔ Bs kmax U).cIP v N t =
      (100 * (1000 * (U + 1) * (U + 1) * (3 * runBound Bs.card) * E3C.Gp Bs.card kmax) +
      4 * (1000 * ((U + 1) * (2 ^ Bs.card + 1)) * (U + 1) * E3C.Gp Bs.card kmax) +
      500 * ((U + 1) * E3C.Gp Bs.card kmax) + 1000 * (U + 1)) * (3 * count t - 1) + (10 * U + 600) := rfl

/-! ### the main statement -/

theorem realIntro_at {Δ' : ℕ → Option Tm} (hΔ : Ext6 Δ') (B : ℕ) {adj : Adj} {k M v : ℕ} {c : NT}
    (hg : (NT.intro v c).Good adj) (hw : (NT.intro v c).toRT.Width (k + 1))
    {t0 : RT} (hpt : PTD adj c k t0) {target : CT} (htg : target ∈ tables adj k (NT.intro v c))
    (hsz : sz t0 ≤ (2 * k + 8) * (2 * k + 6) * c.size) (hcM : c.size ≤ M) (hvM : v ≤ M)
    (hbagM : ∀ u ∈ c.bag, u ≤ M) (hB : (Zc M k ^ pRI + 2) ^ 2 < B) :
    Runs Δ' B E5R.fRealIntro [Val.nat E3C.fIntroPlans, toVal (k + 1), toVal v, toVal (nbrs adj v c.bag),
      toVal c.bag, toVal t0, toVal target]
      (toVal (realIntro (k + 1) v (nbrs adj v c.bag) c.bag t0 target)) (Zc M k ^ pRI) := by
  have hg0 := hg
  obtain ⟨hvB, -, -, hgc⟩ := hg
  have hwc : c.toRT.Width (k + 1) := NT.width_intro hw
  have hb : c.bag.card ≤ k + 2 := bag_card_le_of_width hwc
  have hcov : c.bag ⊆ t0.verts := by
    rw [hpt.1.verts_eq]; intro x hx; exact NT.bag_subset_under c hx
  have hwf : (t0.char c.bag).Wf c.bag (k + 1) := char_wf hpt.1.conn hcov hpt.2
  have hwt : target.Wf (insert v c.bag) (k + 1) := tables_wf hg0 target htg
  have hU1 : ∀ u ∈ c.bag, u ≤ UI M k := fun u hu => le_trans (hbagM u hu) (by unfold UI; omega)
  have hNcard : (nbrs adj v c.bag).card ≤ k + 2 :=
    le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hb
  have hsz' : sz (t0.char c.bag) ≤ 128 * (k + 2) ^ 3 := wf_sz_le hb hwf
  have hcnt : count (t0.char c.bag) ≤ runBound c.bag.card := hwf.count_le
  have hY := Yk_ge k
  have hUY : 128 * (k + 2) ^ 3 ≤ UI M k := by unfold UI Yk; omega
  have hmx : mx (t0.char c.bag) ≤ UI M k := mx_ct_le_of_wf hwf hU1 (by unfold UI; omega)
  have hΔ3 : E3C.Δ ⊑ Δ' := hΔ.e4.e3
  have hPIP : (ipInst hΔ3 c.bag (k + 1) (UI M k)).PIP v (nbrs adj v c.bag) (t0.char c.bag) := by
    rw [ipInst_PIP]
    refine ⟨by unfold UI; omega, by unfold UI; omega, le_trans hsz' hUY, hmx, hwf.good, hwf.bounded, hcnt⟩
  have hcip : (ipInst hΔ3 c.bag (k + 1) (UI M k)).cIP v (nbrs adj v c.bag) (t0.char c.bag) ≤
      2 * E3C.introCCost (UI M k + 1) (3 * (k + 2)) := by
    rw [ipInst_cIP]
    refine le_trans (cIP_le c.bag (k + 1) (UI M k) (count (t0.char c.bag)) ?_ ?_ ?_)
      (Nat.mul_le_mul_left _ (introCCost_mono ?_))
    · unfold UI; omega
    · unfold UI; omega
    · exact le_trans (count_le_sz _) (le_trans hsz' hUY)
    · omega
  have hLen : (introPlans v (nbrs adj v c.bag) (t0.char c.bag)).length ≤ LenI k := by
    refine le_trans (introPlans_length_le hwf) (Nat.pow_le_pow_right (by norm_num) ?_)
    exact intro_len_num k _ hb
  have hplans : ∀ r ∈ introPlans v (nbrs adj v c.bag) (t0.char c.bag), sz r ≤ sI M k := by
    intro r hr
    have hct : ∀ x ∈ introPlans v (nbrs adj v c.bag) (t0.char c.bag),
        sz x.2.2 ≤ (2 * runBound c.bag.card + c.bag.card + 4) * (2 * c.bag.card + 4 * (k + 1) + 10) := by
      intro x hx
      rw [sz_ct_eq]
      exact introPlans_vsz_le v _ hwf x hx
    have := introPlans_sz_le v (nbrs adj v c.bag) (b := c.bag.card) (t0.char c.bag) (LB.of_good hwf.good) hcnt hct r hr
    exact le_trans this (plan_sz_num M k _ hb)
  have hcardI : (insert v c.bag).card ≤ k + 3 := le_trans (Finset.card_insert_le _ _) (by omega)
  have hsI := bag_sz_num M k
  have hPD : ∀ r ∈ introPlans v (nbrs adj v c.bag) (t0.char c.bag),
      (E5Inst.ext5_e2 (LrI k) hΔ.e4.e2 hΔ.e4.e1).PD (sI M k) (CT.norm r.2.2) target := by
    intro r hr
    obtain ⟨path, plan, r2⟩ := r
    have hIR := introPlans_toIR v (nbrs adj v c.bag) (t0.char c.bag) r2 ⟨path, plan, hr⟩
    obtain ⟨lr, cr, -, -, -⟩ := ir_aux v c.bag hvB (nbrs adj v c.bag) hIR (loc_of_good _ hwf.good) hwf.conn
      (by rw [hwf.verts_eq]; exact hvB)
    have hgood : Good (insert v c.bag) (CT.norm r2) := good_norm r2 lr cr
    have hme : maxEntry r2 ≤ k + 3 :=
      introPlans_me v (nbrs adj v c.bag) (b := c.bag.card) (K := k + 3) (by omega) (t0.char c.bag)
        (LB.of_good hwf.good) (by have := hwf.bounded; omega) (path, plan, r2) hr
    have hme' : maxEntry (CT.norm r2) ≤ k + 3 := le_trans (maxEntry_norm_le r2) hme
    refine ⟨?_, ?_⟩
    · exact (RB.of_good hgood hme').mono (by omega) (by unfold LrI; omega)
    · exact (RB.of_good hwt.good hwt.bounded).mono (by omega) (by unfold LrI; omega)
  have hBsum := numRI_B M k _ hcip
  have hBd : sz c.bag ≤ sI M k := by rw [sz_finset]; omega
  have ht : sz t0 ≤ sI M k := le_trans hsz (t0_sz_num M k _ hcM)
  have htg' : sz target ≤ sI M k := le_trans (tables_sz_le hg0 hw target htg) (tg_sz_num M k)
  have hB2 : 20000 + 20000 * (sI M k + 1) + (E5Inst.ext5_e2 (LrI k) hΔ.e4.e2 hΔ.e4.e1).cKey (6 * sI M k) +
      (E5Inst.ext5_e2 (LrI k) hΔ.e4.e2 hΔ.e4.e1).cNorm (5 * sI M k) +
      (E5Inst.ext5_e2 (LrI k) hΔ.e4.e2 hΔ.e4.e1).cNorm (sI M k) +
      (E5Inst.ext5_e2 (LrI k) hΔ.e4.e2 hΔ.e4.e1).cDom (sI M k) +
      (ipInst hΔ3 c.bag (k + 1) (UI M k)).cIP v (nbrs adj v c.bag) (t0.char c.bag) < B := by
    have : Zc M k ^ pRI < B := by nlinarith [Nat.zero_le (Zc M k ^ pRI)]
    exact lt_of_le_of_lt hBsum this
  have h := E5R.realIntro_runs (Ext.trans E5W.extR hΔ.e5) B (E5Inst.ext5_e2 (LrI k) hΔ.e4.e2 hΔ.e4.e1)
    (ipInst hΔ3 c.bag (k + 1) (UI M k)) (k + 1) v (nbrs adj v c.bag) c.bag t0 target (sI M k) (LenI k)
    hBd ht htg' hPIP hLen hplans hPD hB2
  rw [ipInst_ip] at h
  exact h.mono (numRI_cost M k _ hcip)

end E6b
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6bRealJ` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# WP E6b (8): `realJoin` on the trees built by `extract`

`realJoin_at`: `E5D.fRealJoin` computes `realJoin (k+1) a.bag ta tb target` within `Zc^pRJ` steps, where `ta`, `tb` are
real decompositions returned by the extractions of the two children (`PTD`), by `E5D.realJoin_runs'` (the version of
`E5D.realJoin_runs` with the target-sequence length `Ly` as a separate parameter, `E6bMerge`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT E5D

theorem cJ_le (Bs : Finset ℕ) (k : ℕ) (ca cb : CT) (hb : Bs.card ≤ k + 2) (M : ℕ) (ha : ca.Wf Bs (k + 1))
    (hbb : cb.Wf Bs (k + 1)) :
    28000 * (sz ca + sz cb + 1) * 2 ^ (48 * (ca.verts.card + (k + 1) + 2) ^ 3) + 2000 * (sz ca + sz cb + 1) + 2000 +
      E2.R0k (k + 1) + 1000 ≤ cJb M k := by
  have hsa := wf_sz_le hb ha
  have hsb := wf_sz_le hb hbb
  have hv : ca.verts = Bs := ha.verts_eq
  have hR := E2.join_R0_bound Bs.card (k + 1)
  have hpos : 0 < (2 * Bs.card + 2) ^ 2 := pow_pos (by omega) 2
  have hR1 : E2.R0k (k + 1) ≤ 6000 * 2 ^ (48 * (Bs.card + (k + 1) + 2) ^ 3) :=
    le_trans (Nat.le_mul_of_pos_left (E2.R0k (k + 1)) hpos) hR
  have hE : 48 * (Bs.card + (k + 1) + 2) ^ 3 ≤ 1296 * Yk k := by
    unfold Yk
    have h1 : Bs.card + (k + 1) + 2 ≤ 3 * (k + 2) := by omega
    have h2 : (Bs.card + (k + 1) + 2) ^ 3 ≤ (3 * (k + 2)) ^ 3 := Nat.pow_le_pow_left h1 3
    calc 48 * (Bs.card + (k + 1) + 2) ^ 3 ≤ 48 * (3 * (k + 2)) ^ 3 := Nat.mul_le_mul_left _ h2
      _ = 1296 * (k + 2) ^ 3 := by ring
  have hP : 2 ^ (48 * (Bs.card + (k + 1) + 2) ^ 3) ≤ 2 ^ (1296 * Yk k) := Nat.pow_le_pow_right (by norm_num) hE
  rw [hv]
  unfold cJb
  have h3 : sz ca + sz cb + 1 ≤ 256 * Yk k + 1 := by unfold Yk; omega
  have h4 : 28000 * (sz ca + sz cb + 1) * 2 ^ (48 * (Bs.card + (k + 1) + 2) ^ 3) ≤
      28000 * (256 * Yk k + 1) * 2 ^ (1296 * Yk k) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) hP
  have h5 : 2000 * (sz ca + sz cb + 1) ≤ 2000 * (256 * Yk k + 1) := Nat.mul_le_mul_left _ h3
  have h6 : 6000 * 2 ^ (48 * (Bs.card + (k + 1) + 2) ^ 3) ≤ 6000 * 2 ^ (1296 * Yk k) := Nat.mul_le_mul_left _ hP
  omega

theorem realJoin_at {Δ' : ℕ → Option Tm} (hΔ : Ext6 Δ') (B : ℕ) {adj : Adj} {k M : ℕ} {a b : NT}
    (hg : (NT.join a b).Good adj) (hw : (NT.join a b).toRT.Width (k + 1))
    {ta tb : RT} (hta : PTD adj a k ta) (htb : PTD adj b k tb) {target : CT}
    (htg : target ∈ tables adj k (NT.join a b))
    (hsza : sz ta ≤ (2 * k + 8) * (2 * k + 6) * a.size) (hszb : sz tb ≤ (2 * k + 8) * (2 * k + 6) * b.size)
    (haM : a.size ≤ M) (hbM : b.size ≤ M) (hB : (Zc M k ^ pRJ + 2) ^ 2 < B) :
    Runs Δ' B E5D.fRealJoin [toVal (k + 1), toVal a.bag, toVal ta, toVal tb, toVal target]
      (toVal (realJoin (k + 1) a.bag ta tb target)) (Zc M k ^ pRJ) := by
  have hg0 := hg
  have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
  obtain ⟨hab, -, hga, hgb, -⟩ := hg'
  have hwa : a.toRT.Width (k + 1) := NT.width_join_left hw
  have hb : a.bag.card ≤ k + 2 := bag_card_le_of_width hwa
  have hcova : a.bag ⊆ ta.verts := by
    rw [hta.1.verts_eq]; intro x hx; exact NT.bag_subset_under a hx
  have hcovb : a.bag ⊆ tb.verts := by
    rw [htb.1.verts_eq, hab]; intro x hx; exact NT.bag_subset_under b hx
  have wfa : (ta.char a.bag).Wf a.bag (k + 1) := char_wf hta.1.conn hcova hta.2
  have wfb : (tb.char a.bag).Wf a.bag (k + 1) := char_wf htb.1.conn hcovb htb.2
  have wft : target.Wf a.bag (k + 1) := tables_wf hg0 target htg
  have hsI := bag_sz_num M k
  have hRBd : ∀ d ∈ CT.joinC (k + 1) (ta.char a.bag) (tb.char a.bag), d.Wf a.bag (k + 1) :=
    fun d hd => CT.joinC_wf wfa wfb hd
  have hcj : (E5Inst.extJ_e2 hΔ.e4.e2 hΔ.e4.e1).cJ (k + 1) (ta.char a.bag) (tb.char a.bag) ≤ cJb M k :=
    cJ_le a.bag k _ _ hb M wfa wfb
  have hBsum := numRJ_B M k _ hcj
  have hB2 : 200000 + 100000 * (sI M k + 1) ^ 2 +
      (E5Inst.ext5_e2 (LrJ k) hΔ.e4.e2 hΔ.e4.e1).cKey (6 * sI M k) +
      (E5Inst.ext5_e2 (LrJ k) hΔ.e4.e2 hΔ.e4.e1).cNorm (5 * sI M k) +
      (E5Inst.ext5_e2 (LrJ k) hΔ.e4.e2 hΔ.e4.e1).cDom (sI M k) +
      (E5Inst.extJ_e2 hΔ.e4.e2 hΔ.e4.e1).cJ (k + 1) (ta.char a.bag) (tb.char a.bag) < B := by
    have : Zc M k ^ pRJ < B := by nlinarith [Nat.zero_le (Zc M k ^ pRJ)]
    exact lt_of_le_of_lt hBsum this
  have hPD : ∀ d ∈ CT.joinC (k + 1) (ta.char a.bag) (tb.char a.bag),
      (E5Inst.ext5_e2 (LrJ k) hΔ.e4.e2 hΔ.e4.e1).PD (sI M k) d target := by
    intro d hd
    have hwd := hRBd d hd
    refine ⟨?_, ?_⟩
    · exact (RB.of_good hwd.good hwd.bounded).mono (by omega) (by unfold LrJ; omega)
    · exact (RB.of_good wft.good wft.bounded).mono (by omega) (by unfold LrJ; omega)
  have hRB : ∀ d ∈ CT.joinC (k + 1) (ta.char a.bag) (tb.char a.bag), CT.RB (5 * sI M k) (LrJ k) d := by
    intro d hd
    have hwd := hRBd d hd
    exact (RB.of_good hwd.good hwd.bounded).mono (by omega) (by unfold LrJ; omega)
  have h := E5D.realJoin_runs' (Ext.trans E5W.extD hΔ.e5) B (E5Inst.ext5_e2 (LrJ k) hΔ.e4.e2 hΔ.e4.e1)
    (E5Inst.extJ_e2 hΔ.e4.e2 hΔ.e4.e1) (k + 1) a.bag ta tb target (sI M k) (k + 1) (LrJ k) (LenJ k)
    (by rw [sz_finset]; omega) (le_trans hsza (t0_sz_num M k _ haM))
    (le_trans hszb (t0_sz_num M k _ hbM))
    (le_trans (tables_sz_le hg0 hw target htg) (tg_sz_num M k)) (by omega)
    hta.2 htb.2 ⟨a.bag, wfa, wfb⟩
    (joinC_length_le_k hb wfa wfb)
    (fun d hd => le_trans (wf_sz_le hb (hRBd d hd)) (tg_sz_num M k)) hPD hRB hB2
  exact h.mono (numRJ_cost M k _ hcj)

end E6b
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6bCand` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# WP E6b (9): the candidate functions of the searches

Each candidate function (`fFgCand`, `fInCand`, `fJnInner`) is run on one table entry.  *Miss*: the branch condition fails
(cost independent of the recursion, value `none`).  *Hit*: the condition holds; the recursive extraction(s) run (their cost is
a hypothesis) and, for introduce/join, the `realIntro`/`realJoin` call (`E6bRealI`, `E6bRealJ`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lib1 Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT
open E4 (adjOfWord nOfWord)

/-- cost of a forget candidate (without the recursion) -/
def cFgC (k : ℕ) : ℕ := 7000 * (128 * Yk k + 1) ^ 5 + 30 * (128 * Yk k) + 200

section fg
variable {Δ' : ℕ → Option Tm} (hΔ : Ext6 Δ') (B : ℕ)
include hΔ

theorem fgCand_miss (x : List ℕ) (k y : ℕ) (c : NT) (target cq : CT) (hcq : sz cq ≤ 128 * Yk k)
    (htg : sz target ≤ 128 * Yk k) (hne : CT.forgetC y cq ≠ target) (hB : (cFgC k + 2) ^ 2 < B) :
    Runs Δ' B fFgCand [toVal (x, k, y, c, target), toVal cq] (toVal (none : Option RT)) (cFgC k) := by
  have hpos : 1 ≤ (128 * Yk k + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hB500 : 500 < B := by
    have : 200 ≤ cFgC k := by unfold cFgC; omega
    nlinarith
  have h1 := E2.forgetC_runs_fits hΔ.e4.e2 hΔ.e4.e1 B y cq (128 * Yk k) hcq
    (lt_of_le_of_lt (Nat.pow_le_pow_left (by unfold cFgC; omega) 2) hB)
  have hd : decide (CT.forgetC y cq = target) = false := by simp [hne]
  have h2 := eqV_runs_typed hΔ.e4.l1 B (by omega) (CT.forgetC y cq) target (decide (CT.forgetC y cq = target))
    (by simp)
  rw [hd] at h2
  have hm : 30 * min (sz (CT.forgetC y cq)) (sz target) ≤ 30 * (128 * Yk k) := by
    have := Nat.min_le_right (sz (CT.forgetC y cq)) (sz target); omega
  have hE2 : E2.fForgetC < B := by show 169 < B; omega
  refine Runs.mk (hΔ.e6 _ _ Δ_fgCand) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · unfold cFgC; omega

theorem fgCand_hit (x : List ℕ) (k y : ℕ) (c : NT) (cq : CT) (hcq : sz cq ≤ 128 * Yk k)
    (E : ℕ) (hE : Runs Δ' B fExtract [toVal x, toVal k, toVal c, toVal cq]
      (toVal (extract (adjOfWord x) k c cq)) E) (hB : (cFgC k + E + 2) ^ 2 < B) :
    Runs Δ' B fFgCand [toVal (x, k, y, c, CT.forgetC y cq), toVal cq]
      (toVal (extract (adjOfWord x) k c cq)) (cFgC k + E) := by
  have hpos : 1 ≤ (128 * Yk k + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hB500 : 500 < B := by
    have : 200 ≤ cFgC k := by unfold cFgC; omega
    have h2 : (200 + 2) ^ 2 ≤ (cFgC k + E + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have htg : sz (CT.forgetC y cq) ≤ 128 * Yk k := le_trans (E4.sz_forgetC_le y cq) hcq
  have h1 := E2.forgetC_runs_fits hΔ.e4.e2 hΔ.e4.e1 B y cq (128 * Yk k) hcq
    (lt_of_le_of_lt (Nat.pow_le_pow_left (by unfold cFgC; omega) 2) hB)
  have hd : decide (CT.forgetC y cq = CT.forgetC y cq) = true := by simp
  have h2 := eqV_runs_typed hΔ.e4.l1 B (by omega) (CT.forgetC y cq) (CT.forgetC y cq)
    (decide (CT.forgetC y cq = CT.forgetC y cq)) (by simp)
  rw [hd] at h2
  have hm : 30 * min (sz (CT.forgetC y cq)) (sz (CT.forgetC y cq)) ≤ 30 * (128 * Yk k) := by
    have := Nat.min_le_right (sz (CT.forgetC y cq)) (sz (CT.forgetC y cq)); omega
  have hE2 : E2.fForgetC < B := by show 169 < B; omega
  refine Runs.mk (hΔ.e6 _ _ Δ_fgCand) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · unfold cFgC; omega

theorem fgCand_hit' (x : List ℕ) (k y : ℕ) (c : NT) (cq target : CT) (hcq : sz cq ≤ 128 * Yk k)
    (heq : CT.forgetC y cq = target)
    (E : ℕ) (hE : Runs Δ' B fExtract [toVal x, toVal k, toVal c, toVal cq]
      (toVal (extract (adjOfWord x) k c cq)) E) (hB : (cFgC k + E + 2) ^ 2 < B) :
    Runs Δ' B fFgCand [toVal (x, k, y, c, target), toVal cq]
      (toVal (extract (adjOfWord x) k c cq)) (cFgC k + E) := by
  subst heq
  exact fgCand_hit hΔ B x k y c cq hcq E hE hB

end fg

/-! ## introduce candidates -/

/-- the cost of the `introC` call of an introduce candidate -/
def cIntroCb (M k : ℕ) : ℕ := E3C.introCCost (UI M k + 1) (3 * (k + 2)) + 30
/-- the cost of the membership test of an introduce candidate -/
def cMemI (k : ℕ) : ℕ := (30 * (128 * Yk k) + 24) * (2 ^ (1728 * Yk k) + 1) + 8
/-- cost of an introduce candidate (without the recursion and `realIntro`) -/
def cInC (M k : ℕ) : ℕ := cIntroCb M k + cMemI k + 300

theorem cInC_ge (M k : ℕ) : 300 ≤ cInC M k := by unfold cInC; omega

section intro
variable {Δ' : ℕ → Option Tm} (hΔ : Ext6 Δ') (B : ℕ)
include hΔ

/-- the two subcalls of an introduce candidate -/
theorem inCand_calls (x : List ℕ) (k v M : ℕ) (c : NT) (target cq : CT)
    (hg : (NT.intro v c).Good (adjOfWord x)) (hw : (NT.intro v c).toRT.Width (k + 1))
    (hcq : cq ∈ tables (adjOfWord x) k c) (htg : target ∈ tables (adjOfWord x) k (NT.intro v c))
    (hvM : v ≤ M) (hbagM : ∀ u ∈ c.bag, u ≤ M) (hB : (cInC M k + 2) ^ 2 < B) :
    Runs Δ' B E4.fIntroCb [toVal (k + 1, v, nbrs (adjOfWord x) v c.bag), toVal cq]
      (toVal (introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq)) (cIntroCb M k) ∧
    Runs Δ' B fMem [toVal target, toVal (introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq)]
      (toVal (decide (target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq))) (cMemI k) := by
  have hg0 := hg
  obtain ⟨hvB, -, -, hgc⟩ := hg
  have hwc : c.toRT.Width (k + 1) := NT.width_intro hw
  have hb : c.bag.card ≤ k + 2 := bag_card_le_of_width hwc
  have hwq : cq.Wf c.bag (k + 1) := tables_wf hgc cq hcq
  have hwt : target.Wf (insert v c.bag) (k + 1) := tables_wf hg0 target htg
  have hNcard : (nbrs (adjOfWord x) v c.bag).card ≤ k + 2 :=
    le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hb
  have hsq : sz cq ≤ 128 * Yk k := tables_sz_le hgc hwc cq hcq
  have hst : sz target ≤ 128 * Yk k := tables_sz_le hg0 hw target htg
  have hY := Yk_ge k
  have hU1 : ∀ u ∈ c.bag, u ≤ UI M k := fun u hu => le_trans (hbagM u hu) (by unfold UI; omega)
  have hUY : 128 * Yk k ≤ UI M k := by unfold UI; omega
  have hmx : mx cq ≤ UI M k := mx_ct_le_of_wf hwq hU1 (by unfold UI; omega)
  have hC : cIntroCb M k + 40 < B := by
    have : cIntroCb M k + 40 ≤ cInC M k := by unfold cInC; omega
    have h2 : cInC M k ≤ (cInC M k + 2) ^ 2 := by nlinarith [cInC_ge M k]
    omega
  have hcb : Runs Δ' B E4.fIntroCb [toVal (k + 1, v, nbrs (adjOfWord x) v c.bag), toVal cq]
      (toVal (introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq)) (cIntroCb M k) := by
    have hBc : E3C.introCCost (UI M k + 1) (c.bag.card + (k + 1) + 2) + 40 < B := by
      have := introCCost_mono (W := UI M k + 1) (s := c.bag.card + (k + 1) + 2) (s' := 3 * (k + 2)) (by omega)
      unfold cIntroCb at hC; omega
    have := E4.introCb_runs hΔ.e4 B (k + 1) v (nbrs (adjOfWord x) v c.bag) c.bag cq hwq (UI M k)
      (le_trans hsq hUY) hmx (by unfold UI; omega) (by unfold UI; omega) (by unfold UI; omega) hBc
    refine this.mono ?_
    unfold cIntroCb
    have := introCCost_mono (W := UI M k + 1) (s := c.bag.card + (k + 1) + 2) (s' := 3 * (k + 2)) (by omega)
    omega
  refine ⟨hcb, ?_⟩
  have hlen : (introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq).length ≤ 2 ^ (1728 * Yk k) :=
    introC_length_le hb hwq
  have h := mem_runs hΔ.e4.l1 B (by nlinarith [cInC_ge M k]) target
    (introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq)
    (decide (target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq)) (by simp)
  refine h.mono ?_
  unfold cMemI
  have h1 : (30 * sz target + 24) * ((introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq).length + 1) ≤
      (30 * (128 * Yk k) + 24) * (2 ^ (1728 * Yk k) + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

theorem inCand_miss (x : List ℕ) (k v M : ℕ) (c : NT) (target cq : CT)
    (hg : (NT.intro v c).Good (adjOfWord x)) (hw : (NT.intro v c).toRT.Width (k + 1))
    (hcq : cq ∈ tables (adjOfWord x) k c) (htg : target ∈ tables (adjOfWord x) k (NT.intro v c))
    (hvM : v ≤ M) (hbagM : ∀ u ∈ c.bag, u ≤ M)
    (hmiss : target ∉ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq) (hB : (cInC M k + 2) ^ 2 < B) :
    Runs Δ' B fInCand [toVal ((k + 1, v, nbrs (adjOfWord x) v c.bag), x, k, c, c.bag, target), toVal cq]
      (toVal (none : Option RT)) (cInC M k) := by
  obtain ⟨h1, h2⟩ := inCand_calls hΔ B x k v M c target cq hg hw hcq htg hvM hbagM hB
  have hd : decide (target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq) = false := by simp [hmiss]
  rw [hd] at h2
  have hB500 : 500 < B := by
    have := cInC_ge M k
    have h2 : (300 + 2) ^ 2 ≤ (cInC M k + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hk1 : E4.fIntroCb < B := by show 389 < B; omega
  refine Runs.mk (hΔ.e6 _ _ Δ_inCand) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · unfold cInC; omega

theorem inCand_hit (x : List ℕ) (k v M : ℕ) (c : NT) (target cq : CT)
    (hg : (NT.intro v c).Good (adjOfWord x)) (hw : (NT.intro v c).toRT.Width (k + 1))
    (hcq : cq ∈ tables (adjOfWord x) k c) (htg : target ∈ tables (adjOfWord x) k (NT.intro v c))
    (hvM : v ≤ M) (hbagM : ∀ u ∈ c.bag, u ≤ M)
    (hhit : target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq) (t0 : RT)
    (hext : extract (adjOfWord x) k c cq = some t0) (E RI : ℕ)
    (hE : Runs Δ' B fExtract [toVal x, toVal k, toVal c, toVal cq] (toVal (extract (adjOfWord x) k c cq)) E)
    (hR : Runs Δ' B E5R.fRealIntro [Val.nat E3C.fIntroPlans, toVal (k + 1), toVal v,
      toVal (nbrs (adjOfWord x) v c.bag), toVal c.bag, toVal t0, toVal target]
      (toVal (realIntro (k + 1) v (nbrs (adjOfWord x) v c.bag) c.bag t0 target)) RI)
    (hB : (cInC M k + E + RI + 2) ^ 2 < B) :
    Runs Δ' B fInCand [toVal ((k + 1, v, nbrs (adjOfWord x) v c.bag), x, k, c, c.bag, target), toVal cq]
      (toVal (realIntro (k + 1) v (nbrs (adjOfWord x) v c.bag) c.bag t0 target)) (cInC M k + E + RI) := by
  have hB' : (cInC M k + 2) ^ 2 < B :=
    lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hB
  obtain ⟨h1, h2⟩ := inCand_calls hΔ B x k v M c target cq hg hw hcq htg hvM hbagM hB'
  have hd : decide (target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq) = true := by simp [hhit]
  rw [hd] at h2
  rw [hext] at hE
  have hB500 : 1000 < B := by
    have := cInC_ge M k
    have h2 : (300 + 2) ^ 2 ≤ (cInC M k + E + RI + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hk1 : E4.fIntroCb < B := by show 389 < B; omega
  have hk2 : E5R.fRealIntro < B := by show 504 < B; omega
  have hk3 : E3C.fIntroPlans < B := by show 325 < B; omega
  refine Runs.mk (hΔ.e6 _ _ Δ_inCand) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · unfold cInC at *; omega

end intro

/-! ## join candidates (inner) -/

/-- the cost of the `joinC` call of a join candidate -/
def cJoinInner (k : ℕ) : ℕ := 14000 * (128 * Yk k + 1) * 2 ^ (1296 * Yk k) + 30
/-- the cost of the membership test of a join candidate -/
def cMemJ (k : ℕ) : ℕ := (30 * (128 * Yk k) + 24) * (2 ^ (432 * Yk k) + 1) + 8
/-- cost of a join candidate (without the recursions and `realJoin`) -/
def cJnC (k : ℕ) : ℕ := cJoinInner k + cMemJ k + 400

theorem cJnC_ge (k : ℕ) : 400 ≤ cJnC k := by unfold cJnC; omega

theorem cJnC_ge_k (k : ℕ) : k + 2 ≤ cJnC k := by
  have hP : 1 ≤ 2 ^ (1296 * Yk k) := Nat.one_le_two_pow
  have h := Nat.mul_le_mul_left (14000 * (128 * Yk k + 1)) hP
  have := lin_Yk k
  unfold cJnC cJoinInner
  omega

section join
variable {Δ' : ℕ → Option Tm} (hΔ : Ext6 Δ') (B : ℕ)
include hΔ

theorem jnCand_calls (x : List ℕ) (k : ℕ) (a b : NT) (target ca cb : CT)
    (hg : (NT.join a b).Good (adjOfWord x)) (hw : (NT.join a b).toRT.Width (k + 1))
    (hca : ca ∈ tables (adjOfWord x) k a) (hcb : cb ∈ tables (adjOfWord x) k b)
    (htg : target ∈ tables (adjOfWord x) k (NT.join a b)) (hB : (cJnC k + 2) ^ 2 < B) :
    Runs Δ' B E4.fJoinInner [toVal (k + 1, ca), toVal cb] (toVal (joinC (k + 1) ca cb)) (cJoinInner k) ∧
    Runs Δ' B fMem [toVal target, toVal (joinC (k + 1) ca cb)]
      (toVal (decide (target ∈ joinC (k + 1) ca cb))) (cMemJ k) := by
  have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good (adjOfWord x) a ∧ NT.Good (adjOfWord x) b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adjOfWord x u v = true ∨ adjOfWord x v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
  obtain ⟨hab, -, hga, hgb, -⟩ := hg'
  have hwa : a.toRT.Width (k + 1) := NT.width_join_left hw
  have hwb : b.toRT.Width (k + 1) := NT.width_join_right hw
  have hb : a.bag.card ≤ k + 2 := bag_card_le_of_width hwa
  have wa : ca.Wf a.bag (k + 1) := tables_wf hga ca hca
  have wb : cb.Wf a.bag (k + 1) := by rw [hab]; exact tables_wf hgb cb hcb
  have hsa : sz ca ≤ 128 * Yk k := tables_sz_le hga hwa ca hca
  have hsb : sz cb ≤ 128 * Yk k := tables_sz_le hgb hwb cb hcb
  have hst : sz target ≤ 128 * Yk k := tables_sz_le hg hw target htg
  have hY := Yk_ge k
  have hCj : 14000 * (128 * Yk k + 1) * 2 ^ (48 * (a.bag.card + (k + 1) + 2) ^ 3) ≤
      14000 * (128 * Yk k + 1) * 2 ^ (1296 * Yk k) := by
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) ?_)
    unfold Yk
    have h1 : a.bag.card + (k + 1) + 2 ≤ 3 * (k + 2) := by omega
    have h2 : (a.bag.card + (k + 1) + 2) ^ 3 ≤ (3 * (k + 2)) ^ 3 := Nat.pow_le_pow_left h1 3
    calc 48 * (a.bag.card + (k + 1) + 2) ^ 3 ≤ 48 * (3 * (k + 2)) ^ 3 := Nat.mul_le_mul_left _ h2
      _ = 1296 * (k + 2) ^ 3 := by ring
  have hC : (cJoinInner k + 10) ^ 2 < B := by
    have : cJoinInner k + 10 ≤ cJnC k + 2 := by unfold cJnC; omega
    exact lt_of_le_of_lt (Nat.pow_le_pow_left this 2) hB
  refine ⟨?_, ?_⟩
  · have := E4.joinInner_runs hΔ.e4 B (k + 1) a.bag ca cb wa wb (128 * Yk k) (14000 * (128 * Yk k + 1) * 2 ^ (1296 * Yk k))
      hsa hsb hCj (by unfold cJoinInner at hC; nlinarith)
    exact this
  · have hlen : (joinC (k + 1) ca cb).length ≤ 2 ^ (432 * Yk k) := joinC_length_le_k hb wa wb
    have h := mem_runs hΔ.e4.l1 B (by nlinarith [cJnC_ge k]) target (joinC (k + 1) ca cb)
      (decide (target ∈ joinC (k + 1) ca cb)) (by simp)
    refine h.mono ?_
    unfold cMemJ
    have h1 : (30 * sz target + 24) * ((joinC (k + 1) ca cb).length + 1) ≤
        (30 * (128 * Yk k) + 24) * (2 ^ (432 * Yk k) + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega

theorem jnCand_miss (x : List ℕ) (k : ℕ) (a b : NT) (target ca cb : CT)
    (hg : (NT.join a b).Good (adjOfWord x)) (hw : (NT.join a b).toRT.Width (k + 1))
    (hca : ca ∈ tables (adjOfWord x) k a) (hcb : cb ∈ tables (adjOfWord x) k b)
    (htg : target ∈ tables (adjOfWord x) k (NT.join a b)) (hmiss : target ∉ joinC (k + 1) ca cb)
    (hB : (cJnC k + 2) ^ 2 < B) :
    Runs Δ' B fJnInner [toVal (ca, x, k, a, b, a.bag, target), toVal cb] (toVal (none : Option RT)) (cJnC k) := by
  obtain ⟨h1, h2⟩ := jnCand_calls hΔ B x k a b target ca cb hg hw hca hcb htg hB
  have hd : decide (target ∈ joinC (k + 1) ca cb) = false := by simp [hmiss]
  rw [hd] at h2
  have hB500 : 1000 < B := by
    have := cJnC_ge k
    have h2 : (400 + 2) ^ 2 ≤ (cJnC k + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hk1 : E4.fJoinInner < B := by show 391 < B; omega
  have hk2 : k + 1 < B := by
    have := cJnC_ge k
    have h3 : k + 2 ≤ cJnC k := cJnC_ge_k k
    have h2 : (cJnC k + 2) ^ 2 ≥ cJnC k + 2 := Nat.le_self_pow (by norm_num) _
    omega
  refine Runs.mk (hΔ.e6 _ _ Δ_jnInner) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · unfold cJnC; omega

theorem jnCand_hit (x : List ℕ) (k : ℕ) (a b : NT) (target ca cb : CT)
    (hg : (NT.join a b).Good (adjOfWord x)) (hw : (NT.join a b).toRT.Width (k + 1))
    (hca : ca ∈ tables (adjOfWord x) k a) (hcb : cb ∈ tables (adjOfWord x) k b)
    (htg : target ∈ tables (adjOfWord x) k (NT.join a b)) (hhit : target ∈ joinC (k + 1) ca cb)
    (ta tb : RT) (hea : extract (adjOfWord x) k a ca = some ta) (heb : extract (adjOfWord x) k b cb = some tb)
    (Ea Eb RJ : ℕ)
    (hEa : Runs Δ' B fExtract [toVal x, toVal k, toVal a, toVal ca] (toVal (extract (adjOfWord x) k a ca)) Ea)
    (hEb : Runs Δ' B fExtract [toVal x, toVal k, toVal b, toVal cb] (toVal (extract (adjOfWord x) k b cb)) Eb)
    (hR : Runs Δ' B E5D.fRealJoin [toVal (k + 1), toVal a.bag, toVal ta, toVal tb, toVal target]
      (toVal (realJoin (k + 1) a.bag ta tb target)) RJ)
    (hB : (cJnC k + Ea + Eb + RJ + 2) ^ 2 < B) :
    Runs Δ' B fJnInner [toVal (ca, x, k, a, b, a.bag, target), toVal cb]
      (toVal (realJoin (k + 1) a.bag ta tb target)) (cJnC k + Ea + Eb + RJ) := by
  have hB' : (cJnC k + 2) ^ 2 < B := lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hB
  obtain ⟨h1, h2⟩ := jnCand_calls hΔ B x k a b target ca cb hg hw hca hcb htg hB'
  have hd : decide (target ∈ joinC (k + 1) ca cb) = true := by simp [hhit]
  rw [hd] at h2
  rw [hea] at hEa
  rw [heb] at hEb
  have hB500 : 1000 < B := by
    have := cJnC_ge k
    have h2 : (400 + 2) ^ 2 ≤ (cJnC k + Ea + Eb + RJ + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hk1 : E4.fJoinInner < B := by show 391 < B; omega
  have hk2 : k + 1 < B := by
    have := cJnC_ge k
    have h3 : k + 2 ≤ cJnC k := cJnC_ge_k k
    have h2 : (cJnC k + 2) ^ 2 ≥ cJnC k + 2 := Nat.le_self_pow (by norm_num) _
    omega
  refine Runs.mk (hΔ.e6 _ _ Δ_jnInner) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · unfold cJnC at *; omega

end join

end E6b
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6bAsm` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# WP E6b (10): the assembly lemmas of `fExtract` (callee facts as hypotheses, small contexts)
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lib1 Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT
open E4 (adjOfWord nOfWord)

section asm
variable {Δ' : ℕ → Option Tm} (hΔ : Ext6 Δ') (B : ℕ)
include hΔ

theorem leaf_asm (x : List ℕ) (k : ℕ) (target : CT) (hB : 500 < B) :
    Runs Δ' B fExtract [toVal x, toVal k, toVal NT.leaf, toVal target]
      (toVal (some (RT.node ∅ []) : Option RT)) 10 := by
  refine Runs.mk (hΔ.e6 _ _ Δ_extract) ?_
  simp only [toVal_nt_leaf]
  ev_start
  · ev_run
  · omega

theorem forget_ext_asm (x : List ℕ) (k y : ℕ) (c : NT) (target : CT) (T : List CT) (r : Option RT) (Ct Cs C : ℕ)
    (hB : 1000 < B) (hk : k + 1 < B)
    (hT : Runs Δ' B E4.fTables [toVal x, toVal k, toVal c] (toVal T) Ct)
    (hS : Runs Δ' B Lib4.fFindSome [Val.nat fFgCand, toVal (x, k, y, c, target), toVal T] (toVal r) Cs)
    (hC : 60 + Ct + Cs ≤ C) :
    Runs Δ' B fExtract [toVal x, toVal k, toVal (NT.forget y c), toVal target] (toVal r) C := by
  have h1 : fFgCand < B := by show 705 < B; omega
  refine Runs.mk (hΔ.e6 _ _ Δ_extract) ?_
  simp only [toVal_nt_forget, toVal_pair] at *
  ev_start
  · ev_run
  · omega

theorem intro_ext_asm (x : List ℕ) (k v : ℕ) (c : NT) (target : CT) (T : List CT) (N : Finset ℕ) (r : Option RT)
    (Ct Cbag Cnb Cs C : ℕ) (hB : 1000 < B) (hk : k + 1 < B)
    (hT : Runs Δ' B E4.fTables [toVal x, toVal k, toVal c] (toVal T) Ct)
    (hbag : Runs Δ' B E4.fNtBag [toVal c] (toVal c.bag) Cbag)
    (hnb : Runs Δ' B E4.fNbrs [toVal x, toVal v, toVal c.bag] (toVal N) Cnb)
    (hS : Runs Δ' B Lib4.fFindSome [Val.nat fInCand, toVal ((k + 1, v, N), x, k, c, c.bag, target), toVal T]
      (toVal r) Cs)
    (hC : 100 + Ct + Cbag + Cnb + Cs ≤ C) :
    Runs Δ' B fExtract [toVal x, toVal k, toVal (NT.intro v c), toVal target] (toVal r) C := by
  have h1 : fInCand < B := by show 706 < B; omega
  refine Runs.mk (hΔ.e6 _ _ Δ_extract) ?_
  simp only [toVal_nt_intro, toVal_pair] at *
  ev_start
  · ev_run
  · omega

theorem join_ext_asm (x : List ℕ) (k : ℕ) (a b : NT) (target : CT) (Ta Tb : List CT) (r : Option RT)
    (Cta Ctb Cbag Cs C : ℕ) (hB : 1000 < B)
    (hTa : Runs Δ' B E4.fTables [toVal x, toVal k, toVal a] (toVal Ta) Cta)
    (hTb : Runs Δ' B E4.fTables [toVal x, toVal k, toVal b] (toVal Tb) Ctb)
    (hbag : Runs Δ' B E4.fNtBag [toVal a] (toVal a.bag) Cbag)
    (hS : Runs Δ' B Lib4.fFindSome [Val.nat fJnOuter, toVal ((x, k, a, b, a.bag, target), Tb), toVal Ta]
      (toVal r) Cs)
    (hC : 100 + Cta + Ctb + Cbag + Cs ≤ C) :
    Runs Δ' B fExtract [toVal x, toVal k, toVal (NT.join a b), toVal target] (toVal r) C := by
  have h1 : fJnOuter < B := by show 707 < B; omega
  refine Runs.mk (hΔ.e6 _ _ Δ_extract) ?_
  simp only [toVal_nt_join, toVal_pair] at *
  ev_start
  · ev_run
  · omega

theorem jnOuter_asm (x : List ℕ) (k : ℕ) (a b : NT) (target ca : CT) (Tb : List CT) (r : Option RT) (Cs C : ℕ)
    (hB : 1000 < B)
    (hS : Runs Δ' B Lib4.fFindSome [Val.nat fJnInner, toVal (ca, x, k, a, b, a.bag, target), toVal Tb]
      (toVal r) Cs) (hC : 20 + Cs ≤ C) :
    Runs Δ' B fJnOuter [toVal ((x, k, a, b, a.bag, target), Tb), toVal ca] (toVal r) C := by
  have h1 : fJnInner < B := by show 708 < B; omega
  refine Runs.mk (hΔ.e6 _ _ Δ_jnOuter) ?_
  simp only [toVal_pair] at *
  ev_start
  · ev_run
  · omega

end asm

end E6b
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6bNum2` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6b (12): the node costs of `extract`

`Wx M k = Zc M k ^ pX` is the cost bound *per unit of `size²`*: `extract` on a nice tree with `s` nodes costs `≤ s² · Wx M k`.
The non-recursive work of a node is `≤ (its tables) + G`, with `G` from the table lengths (`Nt k = 2^(96 (k+2)^3)`),
the candidate costs (`cFgC`, `cInC`, `cJnC`) and the costs of `realIntro`/`realJoin` (`Zc^pRI`, `Zc^pRJ`).
The three numerical facts `cnode + G ≤ Wx` are the only arithmetic the induction needs.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

/-- the exponent of the per-node cost bound -/
def pX : ℕ := 60

/-- the per-node cost bound: `extract` on a nice tree with `s` nodes costs `s² · Wx M k` -/
def Wx (M k : ℕ) : ℕ := Zc M k ^ pX

/-- the number of table entries: `≤ 2^(96 Yk)` -/
def Nt (k : ℕ) : ℕ := 2 ^ (96 * Yk k)

/-- non-recursive overhead of a forget node (besides `tables` and the recursion) -/
def Gf (k : ℕ) : ℕ := 60 + 24 * Nt k + 6 + Nt k * cFgC k + cFgC k

/-- of an introduce node -/
def Gi (M k : ℕ) : ℕ :=
  100 + 60 * M ^ 2 + ((k + 2) * (28 * M + 120) + 60) + 24 * Nt k + 6 + Nt k * cInC M k + cInC M k + Zc M k ^ pRI

/-- of a join node -/
def Gj (M k : ℕ) : ℕ :=
  100 + 60 * M ^ 2 + 24 * Nt k + 6 + Nt k * (20 + 24 * Nt k + 6 + Nt k * cJnC k) +
    (20 + 24 * Nt k + 6 + Nt k * cJnC k + cJnC k + Zc M k ^ pRJ)

/-! ### the numerical facts -/

theorem Nt_z (M k : ℕ) : Nt k ≤ Zc M k ^ 1 := by
  unfold Nt; exact b_pow M k _ 1 (by omega)

theorem cnode_z (M k : ℕ) : E4.cnode M k ≤ Zc M k ^ 18 := by
  unfold E4.cnode
  have hZ := Zc_big M k
  have h1 := zb_pow (b_M M k) 15
  have h2 : 2 ^ (4000 * (k + 2) ^ 3) ≤ Zc M k ^ 3 := b_pow M k _ 3 (by unfold Yk; omega)
  have := zb_mul h1 h2
  exact zb_mono this (by omega) (hZ1 hZ)

theorem cFgC_z (M k : ℕ) : cFgC k ≤ Zc M k ^ 18 := by
  unfold cFgC
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have h1 := zb_succ (zb_cmul (cnum (by norm_num : 128 ≤ 2 ^ 200) hZ) (b_Y M k)) hZ2'
  have h2 := zb_cmul (cnum (by norm_num : 7000 ≤ 2 ^ 200) hZ) (zb_pow h1 5)
  have h3 := zb_cmul (cnum (by norm_num : 30 ≤ 2 ^ 200) hZ) (zb_cmul (cnum (by norm_num : 128 ≤ 2 ^ 200) hZ) (b_Y M k))
  have h4 := zb_add' h2 h3 hZ2' (r := 16) (by omega) (by omega)
  have h5 := zb_add' h4 (zb_num (cnum (by norm_num : 200 ≤ 2 ^ 200) hZ)) hZ2' (r := 17) (by omega) (by omega)
  exact zb_mono h5 (by omega) (hZ1 hZ)

theorem cMem_z (M k e : ℕ) (he : e ≤ 1728 * Yk k) :
    (30 * (128 * Yk k) + 24) * (2 ^ e + 1) + 8 ≤ Zc M k ^ 9 := by
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have h1 := zb_add' (zb_cmul (cnum (by norm_num : 30 ≤ 2 ^ 200) hZ)
    (zb_cmul (cnum (by norm_num : 128 ≤ 2 ^ 200) hZ) (b_Y M k))) (zb_num (cnum (by norm_num : 24 ≤ 2 ^ 200) hZ)) hZ2'
    (r := 3) (by omega) (by omega)
  have h2 := zb_succ (b_pow M k e 1 (by omega)) hZ2'
  have h3 := zb_mul h1 h2
  have h4 := zb_add' h3 (zb_num (cnum (by norm_num : 8 ≤ 2 ^ 200) hZ)) hZ2' (r := 6) (by omega) (by omega)
  exact zb_mono h4 (by omega) (hZ1 hZ)

theorem cInC_z (M k : ℕ) : cInC M k ≤ Zc M k ^ 21 := by
  unfold cInC cIntroCb cMemI
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have h1 := zb_add' (introCCost_z M k) (zb_num (cnum (by norm_num : 30 ≤ 2 ^ 200) hZ)) hZ2' (r := 18) (by omega)
    (by omega)
  have h2 := cMem_z M k (1728 * Yk k) le_rfl
  have h3 := zb_add' h1 h2 hZ2' (r := 19) (by omega) (by omega)
  have h4 := zb_add' h3 (zb_num (cnum (by norm_num : 300 ≤ 2 ^ 200) hZ)) hZ2' (r := 20) (by omega) (by omega)
  exact zb_mono h4 (by omega) (hZ1 hZ)

theorem cJnC_z (M k : ℕ) : cJnC k ≤ Zc M k ^ 12 := by
  unfold cJnC cJoinInner cMemJ
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have h1 := zb_succ (zb_cmul (cnum (by norm_num : 128 ≤ 2 ^ 200) hZ) (b_Y M k)) hZ2'
  have hP : 2 ^ (1296 * Yk k) ≤ Zc M k ^ 1 := b_pow M k _ 1 (by omega)
  have h2 := zb_mul (zb_cmul (cnum (by norm_num : 14000 ≤ 2 ^ 200) hZ) h1) hP
  have h3 := zb_add' h2 (zb_num (cnum (by norm_num : 30 ≤ 2 ^ 200) hZ)) hZ2' (r := 8) (by omega) (by omega)
  have h4 := cMem_z M k (432 * Yk k) (by omega)
  have h5 := zb_add' h3 h4 hZ2' (r := 9) (by omega) (by omega)
  have h6 := zb_add' h5 (zb_num (cnum (by norm_num : 400 ≤ 2 ^ 200) hZ)) hZ2' (r := 10) (by omega) (by omega)
  exact zb_mono h6 (by omega) (hZ1 hZ)

theorem numX_forget (M k : ℕ) : E4.cnode M k + Gf k ≤ Wx M k := by
  unfold Gf Wx pX
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have hN := Nt_z M k
  have hc := zb_mono (cFgC_z M k) le_rfl (hZ1 hZ)
  have a := zb_add' (zb_num (cnum (by norm_num : 60 ≤ 2 ^ 200) hZ)) (zb_cmul (cnum (by norm_num : 24 ≤ 2 ^ 200) hZ) hN)
    hZ2' (r := 2) (by omega) (by omega)
  have b := zb_add' a (zb_num (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ)) hZ2' (r := 3) (by omega) (by omega)
  have c := zb_add' b (zb_mul hN hc) hZ2' (r := 19) (by omega) (by omega)
  have d := zb_add' c hc hZ2' (r := 20) (by omega) (by omega)
  have e := zb_add' (cnode_z M k) d hZ2' (r := 21) (by omega) (by omega)
  exact zb_mono e (by omega) (hZ1 hZ)

theorem numX_intro (M k : ℕ) : E4.cnode M k + Gi M k ≤ Wx M k := by
  unfold Gi Wx pX
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have hN := Nt_z M k
  have hM := b_M M k
  have hM' : M ≤ Zc M k ^ 1 := by omega
  have a1 := zb_cmul (cnum (by norm_num : 60 ≤ 2 ^ 200) hZ) (zb_pow hM' 2)
  have a2 := zb_addm (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) a1 hZ2'
  have b1 := zb_addm (zb_cmul (cnum (by norm_num : 28 ≤ 2 ^ 200) hZ) hM') (zb_num (cnum (by norm_num : 120 ≤ 2 ^ 200) hZ)) hZ2'
  have b2 := zb_addm (zb_mul (b_k M k) b1) (zb_num (cnum (by norm_num : 60 ≤ 2 ^ 200) hZ)) hZ2'
  have a3 := zb_addm a2 b2 hZ2'
  have a4 := zb_addm a3 (zb_cmul (cnum (by norm_num : 24 ≤ 2 ^ 200) hZ) hN) hZ2'
  have a5 := zb_addm a4 (zb_num (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ)) hZ2'
  have a6 := zb_addm a5 (zb_mul hN (cInC_z M k)) hZ2'
  have a7 := zb_addm a6 (cInC_z M k) hZ2'
  have hp : Zc M k ^ pRI ≤ Zc M k ^ 40 := by unfold pRI; exact le_refl _
  have a8 := zb_addm a7 hp hZ2'
  have a9 := zb_addm (cnode_z M k) a8 hZ2'
  exact zb_mono a9 (by norm_num) (hZ1 hZ)

theorem numX_join (M k : ℕ) : E4.cnode M k + Gj M k ≤ Wx M k := by
  unfold Gj Wx pX
  have hZ := Zc_big M k
  have hZ2' := hZ2 hZ
  have hN := Nt_z M k
  have hM := b_M M k
  have hM' : M ≤ Zc M k ^ 1 := by omega
  have hj := cJnC_z M k
  have a1 := zb_cmul (cnum (by norm_num : 60 ≤ 2 ^ 200) hZ) (zb_pow hM' 2)
  have a2 := zb_addm (zb_num (cnum (by norm_num : 100 ≤ 2 ^ 200) hZ)) a1 hZ2'
  have a3 := zb_addm a2 (zb_cmul (cnum (by norm_num : 24 ≤ 2 ^ 200) hZ) hN) hZ2'
  have a4 := zb_addm a3 (zb_num (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ)) hZ2'
  -- inner bracket `20 + 24 Nt + 6 + Nt * cJnC`
  have c1 := zb_addm (zb_num (cnum (by norm_num : 20 ≤ 2 ^ 200) hZ)) (zb_cmul (cnum (by norm_num : 24 ≤ 2 ^ 200) hZ) hN) hZ2'
  have c2 := zb_addm c1 (zb_num (cnum (by norm_num : 6 ≤ 2 ^ 200) hZ)) hZ2'
  have c3 := zb_addm c2 (zb_mul hN hj) hZ2'
  have c4 := zb_mul hN c3
  have a5 := zb_addm a4 c4 hZ2'
  -- last bracket
  have d1 := zb_addm c2 (zb_mul hN hj) hZ2'
  have d2 := zb_addm d1 hj hZ2'
  have hp : Zc M k ^ pRJ ≤ Zc M k ^ 50 := by unfold pRJ; exact le_refl _
  have d3 := zb_addm d2 hp hZ2'
  have a6 := zb_addm a5 d3 hZ2'
  have a7 := zb_addm (cnode_z M k) a6 hZ2'
  exact zb_mono a7 (by norm_num) (hZ1 hZ)

/-! ## the algebra of the recursion `s ↦ s²` -/

theorem alg_one (s cn G X : ℕ) (hs : 1 ≤ s) (hX : cn + G ≤ X) :
    s * cn + G + s ^ 2 * X ≤ (s + 1) ^ 2 * X := by
  have h1 : s * cn + G ≤ s * X := by nlinarith
  have h2 : (s + 1) ^ 2 * X = s ^ 2 * X + (2 * s + 1) * X := by ring
  nlinarith

theorem alg_two (a b cn G X : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hX : cn + G ≤ X) :
    (a + b) * cn + G + a ^ 2 * X + b ^ 2 * X ≤ (a + b + 1) ^ 2 * X := by
  have h1 : (a + b) * cn + G ≤ (a + b) * X := by nlinarith
  have h2 : (a + b + 1) ^ 2 * X = a ^ 2 * X + b ^ 2 * X + (2 * a * b + 2 * a + 2 * b + 1) * X := by ring
  have h3 : (a + b) * X ≤ (2 * a * b + 2 * a + 2 * b + 1) * X := Nat.mul_le_mul_right _ (by nlinarith)
  omega

-- from now on `Wx` is opaque (its closed form is `E6bFinal.cost_closed`)
attribute [irreducible] Wx

end E6b
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6bMath3` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6b (11): the first-hit facts of the extraction (from `extract_all`, `realIntro_spec`, `realJoin_spec`)

The Lean `findSome?` stops at the first candidate for which the branch condition holds *and* the recursive extraction succeeds.
These lemmas say that the second requirement is automatic: whenever the condition holds, the candidate returns `some`.  Hence
in the cost analysis the recursive calls happen for one candidate only (per side).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT

/-- extraction of a table entry succeeds -/
theorem extract_some {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) {nt : NT} (hg : nt.Good adj)
    (hW : nt.under ⊆ W) {c : CT} (hc : c ∈ tables adj k nt) :
    ∃ t, extract adj k nt c = some t ∧ PTD adj nt k t := by
  obtain ⟨⟨t, ht⟩, hsp⟩ := extract_all hs hg hW c hc
  exact ⟨t, ht, (hsp t ht).1⟩

theorem intro_hit_facts {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) {v : ℕ} {c : NT}
    (hg : (NT.intro v c).Good adj) (hW : (NT.intro v c).under ⊆ W) {cq target : CT} (hcq : cq ∈ tables adj k c)
    (hhit : target ∈ introC (k + 1) v (nbrs adj v c.bag) cq) :
    ∃ t0, extract adj k c cq = some t0 ∧ PTD adj c k t0 ∧
      (realIntro (k + 1) v (nbrs adj v c.bag) c.bag t0 target).isSome = true := by
  have hgc := hg.2.2.2
  have hWc : c.under ⊆ W := fun x hx => hW (Finset.mem_insert_of_mem hx)
  have hvW : v ∈ W := hW (Finset.mem_insert_self _ _)
  have hsym : ∀ u ∈ c.under, adj u v = true → adj v u = true := by
    intro u hu h
    rw [← hs u (hWc hu) v hvW]; exact h
  obtain ⟨⟨t0, ht0⟩, hsp⟩ := extract_all hs hgc hWc cq hcq
  obtain ⟨p0, d0⟩ := hsp t0 ht0
  obtain ⟨t', ht', -⟩ := realIntro_spec hg hsym p0 d0 hhit
  exact ⟨t0, ht0, p0, by simp [ht']⟩

theorem join_hit_facts {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) {a b : NT}
    (hg : (NT.join a b).Good adj) (hW : (NT.join a b).under ⊆ W) {ca cb target : CT}
    (hca : ca ∈ tables adj k a) (hcb : cb ∈ tables adj k b) (hhit : target ∈ CT.joinC (k + 1) ca cb) :
    ∃ ta tb, extract adj k a ca = some ta ∧ extract adj k b cb = some tb ∧ PTD adj a k ta ∧ PTD adj b k tb ∧
      (realJoin (k + 1) a.bag ta tb target).isSome = true := by
  have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
    (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
  obtain ⟨hab, -, hga, hgb, -⟩ := hg'
  have hWa : a.under ⊆ W := fun x hx => hW (Finset.mem_union_left _ hx)
  have hWb : b.under ⊆ W := fun x hx => hW (Finset.mem_union_right _ hx)
  obtain ⟨⟨ta, hta⟩, hspa⟩ := extract_all hs hga hWa ca hca
  obtain ⟨⟨tb, htb⟩, hspb⟩ := extract_all hs hgb hWb cb hcb
  obtain ⟨pa, da⟩ := hspa ta hta
  obtain ⟨pb, db⟩ := hspb tb htb
  rw [← hab] at db
  obtain ⟨t, ht, -⟩ := realJoin_spec hg pa pb da db hhit
  exact ⟨ta, tb, hta, htb, pa, pb, by simp [ht]⟩

end E6b
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6bRun` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-!
# WP E6b (13): `fExtract` computes `extract` — the induction over the nice tree

`extract_runs`: for a good nice tree of width `≤ k+1` (labels and size `≤ M`, `adjOfWord x` symmetric on a set `W` containing
the vertices below `nt`), and every table entry `target`, `fExtract` computes `extract (adjOfWord x) k nt target` within
`nt.size² · Wx M k` steps.

The recursion of the Lean function: one recursive extraction per node (forget/introduce) or per side (join), *for the
first candidate whose branch condition holds*: this candidate always succeeds (`E6bMath3`), so the `findSome?` stops there.
Every other candidate costs `Cn` (condition test only).  Recurrence: `ε(s) ≤ s·cnode + G + ε(s-1)` gives `ε(s) ≤ s²·Wx`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lib1 Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT
open E4 (adjOfWord nOfWord)

theorem size_pos (nt : NT) : 1 ≤ nt.size := by
  cases nt <;> simp [NT.size] <;> omega

theorem Wx_ge (M k : ℕ) : 1000 ≤ Wx M k :=
  le_trans (E4.cnode_ge M k) (le_trans (Nat.le_add_right _ _) (numX_forget M k))

theorem sq_Wx_ge (M k s : ℕ) (hs : 1 ≤ s) : 1000 ≤ s ^ 2 * Wx M k := by
  have := Wx_ge M k
  have h : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ hs
  nlinarith

theorem hB_of_sq {B : ℕ} (M k s : ℕ) (hs : 1 ≤ s) (hB : (s ^ 2 * Wx M k + 2) ^ 2 < B) : 1000 < B := by
  have := sq_Wx_ge M k s hs
  have h2 : (1000 + 2) ^ 2 ≤ (s ^ 2 * Wx M k + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem hBm_of {B : ℕ} {C : ℕ} (hB : (C + 2) ^ 2 < B) : ∀ y, y ≤ C → (y + 2) ^ 2 < B :=
  fun y hy => lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hB

theorem k1_of_hk {B k : ℕ} (hk : k + 2 < B) : k + 1 < B := by omega

theorem extract_runs {Δ' : ℕ → Option Tm} (hΔ : Ext6 Δ') (B : ℕ) (x : List ℕ) (k M : ℕ) {W : Finset ℕ}
    (hs : (adjOfWord x).SymmOn W) (hxM : x.length ≤ M) (hn : (nOfWord x) ^ 2 < B) (hk : k + 2 < B) :
    ∀ nt : NT, nt.Good (adjOfWord x) → nt.under ⊆ W → nt.toRT.Width (k + 1) → sz nt ≤ M → mx nt ≤ M →
      (nt.size ^ 2 * Wx M k + 2) ^ 2 < B → ∀ target ∈ tables (adjOfWord x) k nt,
      Runs Δ' B fExtract [toVal x, toVal k, toVal nt, toVal target]
        (toVal (extract (adjOfWord x) k nt target)) (nt.size ^ 2 * Wx M k) := by
  intro nt
  induction nt with
  | leaf =>
    intro hg hW hw hsM hmM hB target htg
    have hB1000 := hB_of_sq M k _ (size_pos NT.leaf) hB
    have e : extract (adjOfWord x) k NT.leaf target = some (RT.node ∅ []) := rfl
    rw [e]
    refine (leaf_asm hΔ B x k target (by omega)).mono ?_
    have := sq_Wx_ge M k _ (size_pos NT.leaf)
    omega
  | forget y c ih =>
    intro hg hW hw hsM hmM hB target htg
    have hsize : (NT.forget y c).size = c.size + 1 := rfl
    have hcpos := size_pos c
    have hB1000 := hB_of_sq M k _ (size_pos (NT.forget y c)) hB
    have hgc : c.Good (adjOfWord x) := hg.2
    have hWc : c.under ⊆ W := hW
    have hwc : c.toRT.Width (k + 1) := NT.width_forget hw
    have hsc : sz c ≤ M := by have := sz_nt_forget y c; omega
    have hmc : mx c ≤ M := le_trans (E4.mx_forget_le y c) hmM
    have hBm := hBm_of hB
    have hcn := E4.cnode_ge M k
    have hX := Wx_ge M k
    have hsqc : c.size ^ 2 * Wx M k ≤ (c.size + 1) ^ 2 * Wx M k :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 2)
    have hnum := numX_forget M k
    have hBc : (c.size ^ 2 * Wx M k + 2) ^ 2 < B := by
      have := hBm (c.size ^ 2 * Wx M k) (by rw [hsize]; exact hsqc); exact this
    have hcs : c.size * E4.cnode M k ≤ (c.size + 1) ^ 2 * Wx M k := by
      have : c.size * E4.cnode M k ≤ c.size * Wx M k := Nat.mul_le_mul_left _ (by omega)
      have h2 : c.size * Wx M k ≤ c.size ^ 2 * Wx M k := by
        have : c.size ≤ c.size ^ 2 := Nat.le_self_pow (by norm_num) _
        exact Nat.mul_le_mul_right _ this
      omega
    have hBt : (c.size * E4.cnode M k + 2) ^ 2 < B := by
      have := hBm (c.size * E4.cnode M k) (by rw [hsize]; exact hcs); exact this
    have hT := E4.tables_runs hΔ.e4 B x k M hxM hn hk c hgc hwc hsc hmc hBt
    have hIH : ∀ cq ∈ tables (adjOfWord x) k c, Runs Δ' B fExtract [toVal x, toVal k, toVal c, toVal cq]
        (toVal (extract (adjOfWord x) k c cq)) (c.size ^ 2 * Wx M k) :=
      fun cq hcq => ih hgc hWc hwc hsc hmc hBc cq hcq
    have hszq : ∀ cq ∈ tables (adjOfWord x) k c, sz cq ≤ 128 * Yk k := fun cq hcq => tables_sz_le hgc hwc cq hcq
    have hsz_t : sz target ≤ 128 * Yk k := tables_sz_le hg hw target htg
    have hTlen : (tables (adjOfWord x) k c).length ≤ Nt k := tables_length_le_pow hgc hwc
    have hcF : cFgC k + c.size ^ 2 * Wx M k + 2 ≤ (c.size + 1) ^ 2 * Wx M k + 2 := by
      have : cFgC k ≤ Gf k := by unfold Gf; omega
      have h2 : cFgC k + c.size ^ 2 * Wx M k ≤ (c.size + 1) ^ 2 * Wx M k := by
        have := alg_one c.size (E4.cnode M k) (Gf k) (Wx M k) hcpos hnum
        omega
      omega
    have hf : ∀ cq ∈ tables (adjOfWord x) k c, Runs Δ' B fFgCand [toVal (x, k, y, c, target), toVal cq]
        (toVal (if CT.forgetC y cq = target then extract (adjOfWord x) k c cq else none))
        (if CT.forgetC y cq = target then cFgC k + c.size ^ 2 * Wx M k else cFgC k) := by
      intro cq hcq
      by_cases hc : CT.forgetC y cq = target
      · simp only [hc, if_true]
        exact fgCand_hit' hΔ B x k y c cq target (hszq cq hcq) hc _ (hIH cq hcq)
          (by have := hBm (cFgC k + c.size ^ 2 * Wx M k) (by rw [hsize]; omega); exact this)
      · simp only [hc, if_false]
        exact fgCand_miss hΔ B x k y c target cq (hszq cq hcq) hsz_t hc
          (by have := hBm (cFgC k) (by rw [hsize]; have : cFgC k ≤ Gf k := by unfold Gf; omega
                                       have := alg_one c.size (E4.cnode M k) (Gf k) (Wx M k) hcpos hnum
                                       omega); exact this)
    have hnone : ∀ cq ∈ tables (adjOfWord x) k c,
        (if CT.forgetC y cq = target then extract (adjOfWord x) k c cq else none) = none →
        (if CT.forgetC y cq = target then cFgC k + c.size ^ 2 * Wx M k else cFgC k) ≤ cFgC k := by
      intro cq hcq hnn
      by_cases hc : CT.forgetC y cq = target
      · exfalso
        obtain ⟨t, ht, -⟩ := extract_some hs hgc hWc hcq
        simp only [hc, if_true, ht] at hnn
        cases hnn
      · simp [hc]
    have hsome : ∀ cq ∈ tables (adjOfWord x) k c,
        ((if CT.forgetC y cq = target then extract (adjOfWord x) k c cq else none)).isSome = true →
        (if CT.forgetC y cq = target then cFgC k + c.size ^ 2 * Wx M k else cFgC k) ≤
          cFgC k + c.size ^ 2 * Wx M k := by
      intro cq hcq _
      by_cases hc : CT.forgetC y cq = target <;> simp [hc]
    have hfind := findSome_first_runs hΔ.e4.l4 B fFgCand (toVal (x, k, y, c, target))
      (fun cq => if CT.forgetC y cq = target then extract (adjOfWord x) k c cq else none)
      (fun cq => if CT.forgetC y cq = target then cFgC k + c.size ^ 2 * Wx M k else cFgC k)
      (tables (adjOfWord x) k c) (cFgC k) (cFgC k + c.size ^ 2 * Wx M k) hf hnone hsome (by omega)
    have e : extract (adjOfWord x) k (NT.forget y c) target = (tables (adjOfWord x) k c).findSome?
        (fun cq => if CT.forgetC y cq = target then extract (adjOfWord x) k c cq else none) := rfl
    rw [e]
    refine forget_ext_asm hΔ B x k y c target _ _ _ _ _ hB1000 (k1_of_hk hk) hT hfind ?_
    have h1 : 24 * (tables (adjOfWord x) k c).length ≤ 24 * Nt k := by omega
    have h2 : (tables (adjOfWord x) k c).length * cFgC k ≤ Nt k * cFgC k := Nat.mul_le_mul_right _ hTlen
    have h3 := alg_one c.size (E4.cnode M k) (Gf k) (Wx M k) hcpos hnum
    unfold Gf at h3
    rw [hsize]
    omega
  | join a b iha ihb =>
    intro hg hW hw hsM hmM hB target htg
    have hsize : (NT.join a b).size = a.size + b.size + 1 := rfl
    have hapos := size_pos a
    have hbpos := size_pos b
    have hB1000 := hB_of_sq M k _ (size_pos (NT.join a b)) hB
    have hg0 := hg
    have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good (adjOfWord x) a ∧ NT.Good (adjOfWord x) b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adjOfWord x u v = true ∨ adjOfWord x v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
    obtain ⟨hab, -, hga, hgb, -⟩ := hg'
    have hWa : a.under ⊆ W := fun z hz => hW (Finset.mem_union_left _ hz)
    have hWb : b.under ⊆ W := fun z hz => hW (Finset.mem_union_right _ hz)
    have hwa : a.toRT.Width (k + 1) := NT.width_join_left hw
    have hwb : b.toRT.Width (k + 1) := NT.width_join_right hw
    have hsab := sz_nt_join a b
    have hsa : sz a ≤ M := by omega
    have hsb : sz b ≤ M := by omega
    have hma : mx a ≤ M := le_trans (E4.mx_join_left_le a b) hmM
    have hmb : mx b ≤ M := le_trans (E4.mx_join_right_le a b) hmM
    have haM : a.size ≤ M := E4.size_le_M hsa
    have hbM : b.size ≤ M := E4.size_le_M hsb
    have hBm := hBm_of hB
    have hcn := E4.cnode_ge M k
    have hX := Wx_ge M k
    have hnum := numX_join M k
    have hAlg := alg_two a.size b.size (E4.cnode M k) (Gj M k) (Wx M k) hapos hbpos hnum
    have hEa : a.size ^ 2 * Wx M k ≤ (a.size + b.size + 1) ^ 2 * Wx M k :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 2)
    have hEb : b.size ^ 2 * Wx M k ≤ (a.size + b.size + 1) ^ 2 * Wx M k :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 2)
    have hBa : (a.size ^ 2 * Wx M k + 2) ^ 2 < B := by
      have := hBm (a.size ^ 2 * Wx M k) (by rw [hsize]; exact hEa); exact this
    have hBb : (b.size ^ 2 * Wx M k + 2) ^ 2 < B := by
      have := hBm (b.size ^ 2 * Wx M k) (by rw [hsize]; exact hEb); exact this
    have hcsa : a.size * E4.cnode M k ≤ (a.size + b.size + 1) ^ 2 * Wx M k := by
      have h1 : a.size * E4.cnode M k ≤ a.size * Wx M k := Nat.mul_le_mul_left _ (by omega)
      have h2 : a.size * Wx M k ≤ (a.size + b.size + 1) ^ 2 * Wx M k := Nat.mul_le_mul_right _ (by nlinarith)
      omega
    have hcsb : b.size * E4.cnode M k ≤ (a.size + b.size + 1) ^ 2 * Wx M k := by
      have h1 : b.size * E4.cnode M k ≤ b.size * Wx M k := Nat.mul_le_mul_left _ (by omega)
      have h2 : b.size * Wx M k ≤ (a.size + b.size + 1) ^ 2 * Wx M k := Nat.mul_le_mul_right _ (by nlinarith)
      omega
    have hTa := E4.tables_runs hΔ.e4 B x k M hxM hn hk a hga hwa hsa hma
      (by have := hBm (a.size * E4.cnode M k) (by rw [hsize]; exact hcsa); exact this)
    have hTb := E4.tables_runs hΔ.e4 B x k M hxM hn hk b hgb hwb hsb hmb
      (by have := hBm (b.size * E4.cnode M k) (by rw [hsize]; exact hcsb); exact this)
    have hbag := E4.ntBag_runs hΔ.e4 B (by omega) a
    have hTalen : (tables (adjOfWord x) k a).length ≤ Nt k := tables_length_le_pow hga hwa
    have hTblen : (tables (adjOfWord x) k b).length ≤ Nt k := tables_length_le_pow hgb hwb
    -- the pieces of the cost
    have hGj : cJnC k + Zc M k ^ pRJ ≤ Gj M k := by unfold Gj; omega
    have hEh : cJnC k + a.size ^ 2 * Wx M k + b.size ^ 2 * Wx M k + Zc M k ^ pRJ ≤
        (a.size + b.size + 1) ^ 2 * Wx M k := by omega
    have hEh' : ∀ y, y ≤ cJnC k + a.size ^ 2 * Wx M k + b.size ^ 2 * Wx M k + Zc M k ^ pRJ →
        (y + 2) ^ 2 < B := fun y hy => hBm y (by rw [hsize]; omega)
    -- the candidates
    obtain ⟨fin, hfin⟩ : ∃ fin : CT → CT → Option RT, fin = fun ca cb =>
        if target ∈ joinC (k + 1) ca cb then
          (extract (adjOfWord x) k a ca).bind (fun ta => (extract (adjOfWord x) k b cb).bind
            (fun tb => realJoin (k + 1) a.bag ta tb target)) else none := ⟨_, rfl⟩
    obtain ⟨cfin, hcfin⟩ : ∃ cfin : CT → CT → ℕ, cfin = fun ca cb =>
        if target ∈ joinC (k + 1) ca cb then
          cJnC k + a.size ^ 2 * Wx M k + b.size ^ 2 * Wx M k + Zc M k ^ pRJ else cJnC k := ⟨_, rfl⟩
    have hfin_run : ∀ ca ∈ tables (adjOfWord x) k a, ∀ cb ∈ tables (adjOfWord x) k b,
        Runs Δ' B fJnInner [toVal (ca, x, k, a, b, a.bag, target), toVal cb] (toVal (fin ca cb)) (cfin ca cb) := by
      intro ca hca cb hcb
      subst hfin hcfin
      by_cases hm : target ∈ joinC (k + 1) ca cb
      · simp only [hm, if_true]
        obtain ⟨ta, tb, hea, heb, hpa, hpb, -⟩ := join_hit_facts hs hg0 hW hca hcb hm
        have hsza := extract_sz_le hs hga hWa hwa ca hca ta hea
        have hszb := extract_sz_le hs hgb hWb hwb cb hcb tb heb
        have hR := realJoin_at hΔ B hg0 hw hpa hpb htg hsza hszb haM hbM
          (by have := hEh' (Zc M k ^ pRJ) (by omega); exact this)
        have := jnCand_hit hΔ B x k a b target ca cb hg0 hw hca hcb htg hm ta tb hea heb
          (a.size ^ 2 * Wx M k) (b.size ^ 2 * Wx M k) (Zc M k ^ pRJ)
          (iha hga hWa hwa hsa hma hBa ca hca) (ihb hgb hWb hwb hsb hmb hBb cb hcb) hR
          (by have := hEh' (cJnC k + a.size ^ 2 * Wx M k + b.size ^ 2 * Wx M k + Zc M k ^ pRJ) le_rfl; exact this)
        rw [hea, heb, Option.bind_some, Option.bind_some]
        exact this
      · simp only [hm, if_false]
        exact jnCand_miss hΔ B x k a b target ca cb hg0 hw hca hcb htg hm
          (by have := hEh' (cJnC k) (by omega); exact this)
    -- classification of the candidates by value
    have hfin_none : ∀ ca ∈ tables (adjOfWord x) k a, ∀ cb ∈ tables (adjOfWord x) k b,
        fin ca cb = none → cfin ca cb ≤ cJnC k := by
      intro ca hca cb hcb hnn
      subst hfin hcfin
      by_cases hm : target ∈ joinC (k + 1) ca cb
      · exfalso
        obtain ⟨ta, tb, hea, heb, -, -, hsome⟩ := join_hit_facts hs hg0 hW hca hcb hm
        simp only [hm, if_true, hea, heb, Option.bind_some] at hnn
        simp [hnn] at hsome
      · simp [hm]
    have hfin_cond : ∀ ca ∈ tables (adjOfWord x) k a, ∀ cb ∈ tables (adjOfWord x) k b,
        (fin ca cb).isSome = true → target ∈ joinC (k + 1) ca cb := by
      intro ca hca cb hcb hsm
      subst hfin
      by_contra hm
      simp [hm] at hsm
    have hfin_some : ∀ ca ∈ tables (adjOfWord x) k a, ∀ cb ∈ tables (adjOfWord x) k b,
        target ∈ joinC (k + 1) ca cb → (fin ca cb).isSome = true := by
      intro ca hca cb hcb hm
      subst hfin
      obtain ⟨ta, tb, hea, heb, -, -, hsome⟩ := join_hit_facts hs hg0 hW hca hcb hm
      simp only [hm, if_true, hea, heb, Option.bind_some]
      exact hsome
    have hcfin_le : ∀ ca cb, cfin ca cb ≤ cJnC k + a.size ^ 2 * Wx M k + b.size ^ 2 * Wx M k + Zc M k ^ pRJ := by
      intro ca cb; subst hcfin
      by_cases hm : target ∈ joinC (k + 1) ca cb
      · simp only [hm, if_true, le_refl]
      · simp only [hm, if_false]; omega
    -- the inner search (per `ca`)
    have hinner : ∀ ca ∈ tables (adjOfWord x) k a,
        Runs Δ' B Lib4.fFindSome
          [Val.nat fJnInner, toVal (ca, x, k, a, b, a.bag, target), toVal (tables (adjOfWord x) k b)]
          (toVal ((tables (adjOfWord x) k b).findSome? (fin ca)))
          (24 * (tables (adjOfWord x) k b).length + 6 + (tables (adjOfWord x) k b).length * cJnC k +
            (if ((tables (adjOfWord x) k b).findSome? (fin ca)).isSome then
              cJnC k + a.size ^ 2 * Wx M k + b.size ^ 2 * Wx M k + Zc M k ^ pRJ else 0)) := by
      intro ca hca
      by_cases hA : ((tables (adjOfWord x) k b).findSome? (fin ca)).isSome = true
      · rw [if_pos hA]
        exact findSome_first_runs hΔ.e4.l4 B fJnInner (toVal (ca, x, k, a, b, a.bag, target)) (fin ca) (cfin ca)
          (tables (adjOfWord x) k b) (cJnC k)
          (cJnC k + a.size ^ 2 * Wx M k + b.size ^ 2 * Wx M k + Zc M k ^ pRJ) (hfin_run ca hca)
          (fun cb hcb hnn => hfin_none ca hca cb hcb hnn) (fun cb hcb _ => hcfin_le ca cb) (by omega)
      · rw [if_neg hA]
        have := findSome_first_runs hΔ.e4.l4 B fJnInner (toVal (ca, x, k, a, b, a.bag, target)) (fin ca) (cfin ca)
          (tables (adjOfWord x) k b) (cJnC k) 0 (hfin_run ca hca)
          (fun cb hcb hnn => hfin_none ca hca cb hcb hnn)
          (fun cb hcb hsm => by
            exfalso
            apply hA
            rw [List.findSome?_isSome_iff]
            exact ⟨cb, hcb, hsm⟩) (by omega)
        simpa using this
    -- the outer candidate and the outer search
    obtain ⟨fout, hfout⟩ : ∃ fout : CT → Option RT, fout = fun ca => (tables (adjOfWord x) k b).findSome? (fin ca) :=
      ⟨_, rfl⟩
    have hout : ∀ ca ∈ tables (adjOfWord x) k a,
        Runs Δ' B fJnOuter [toVal ((x, k, a, b, a.bag, target), tables (adjOfWord x) k b), toVal ca]
          (toVal (fout ca))
          (20 + (24 * (tables (adjOfWord x) k b).length + 6 + (tables (adjOfWord x) k b).length * cJnC k +
            (if (fout ca).isSome then
              cJnC k + a.size ^ 2 * Wx M k + b.size ^ 2 * Wx M k + Zc M k ^ pRJ else 0))) := by
      intro ca hca
      subst hfout
      exact jnOuter_asm hΔ B x k a b target ca _ _ _ _ hB1000 (hinner ca hca) le_rfl
    have hout_none : ∀ ca ∈ tables (adjOfWord x) k a, fout ca = none →
        20 + (24 * (tables (adjOfWord x) k b).length + 6 + (tables (adjOfWord x) k b).length * cJnC k +
            (if (fout ca).isSome then
              cJnC k + a.size ^ 2 * Wx M k + b.size ^ 2 * Wx M k + Zc M k ^ pRJ else 0)) ≤
        20 + (24 * (tables (adjOfWord x) k b).length + 6 + (tables (adjOfWord x) k b).length * cJnC k) := by
      intro ca hca hnn
      rw [hnn]; simp
    have hout_some : ∀ ca ∈ tables (adjOfWord x) k a, (fout ca).isSome = true →
        20 + (24 * (tables (adjOfWord x) k b).length + 6 + (tables (adjOfWord x) k b).length * cJnC k +
            (if (fout ca).isSome then
              cJnC k + a.size ^ 2 * Wx M k + b.size ^ 2 * Wx M k + Zc M k ^ pRJ else 0)) ≤
        20 + (24 * (tables (adjOfWord x) k b).length + 6 + (tables (adjOfWord x) k b).length * cJnC k) +
          (cJnC k + a.size ^ 2 * Wx M k + b.size ^ 2 * Wx M k + Zc M k ^ pRJ) := by
      intro ca hca hsm
      rw [if_pos hsm]; omega
    have hfind := findSome_first_runs hΔ.e4.l4 B fJnOuter
      (toVal ((x, k, a, b, a.bag, target), tables (adjOfWord x) k b)) fout
      (fun ca => 20 + (24 * (tables (adjOfWord x) k b).length + 6 + (tables (adjOfWord x) k b).length * cJnC k +
            (if (fout ca).isSome then
              cJnC k + a.size ^ 2 * Wx M k + b.size ^ 2 * Wx M k + Zc M k ^ pRJ else 0)))
      (tables (adjOfWord x) k a)
      (20 + (24 * (tables (adjOfWord x) k b).length + 6 + (tables (adjOfWord x) k b).length * cJnC k))
      (20 + (24 * (tables (adjOfWord x) k b).length + 6 + (tables (adjOfWord x) k b).length * cJnC k) +
          (cJnC k + a.size ^ 2 * Wx M k + b.size ^ 2 * Wx M k + Zc M k ^ pRJ))
      hout hout_none hout_some (by omega)
    have e : extract (adjOfWord x) k (NT.join a b) target =
        (tables (adjOfWord x) k a).findSome? fout := by
      subst hfout hfin; rfl
    rw [e]
    refine join_ext_asm hΔ B x k a b target _ _ _ _ _ _ _ _ hB1000 hTa hTb hbag hfind ?_
    have h1 : 24 * (tables (adjOfWord x) k a).length ≤ 24 * Nt k := by omega
    have h2 : 24 * (tables (adjOfWord x) k b).length ≤ 24 * Nt k := by omega
    have h3 : (tables (adjOfWord x) k b).length * cJnC k ≤ Nt k * cJnC k := Nat.mul_le_mul_right _ hTblen
    have h4 : (tables (adjOfWord x) k a).length *
        (20 + (24 * (tables (adjOfWord x) k b).length + 6 + (tables (adjOfWord x) k b).length * cJnC k)) ≤
        Nt k * (20 + 24 * Nt k + 6 + Nt k * cJnC k) := Nat.mul_le_mul hTalen (by omega)
    have h5 : 60 * sz a ^ 2 ≤ 60 * M ^ 2 := E4.sz_sq_le hsa
    have h6 : (a.size + b.size) * E4.cnode M k = a.size * E4.cnode M k + b.size * E4.cnode M k := by ring
    unfold Gj at hAlg
    rw [hsize]
    omega
  | intro v c ih =>
    intro hg hW hw hsM hmM hB target htg
    have hsize : (NT.intro v c).size = c.size + 1 := rfl
    have hcpos := size_pos c
    have hB1000 := hB_of_sq M k _ (size_pos (NT.intro v c)) hB
    have hg0 := hg
    obtain ⟨hvB, -, -, hgc⟩ := hg
    have hWc : c.under ⊆ W := fun z hz => hW (Finset.mem_insert_of_mem hz)
    have hwc : c.toRT.Width (k + 1) := NT.width_intro hw
    have hsc : sz c ≤ M := by have := sz_nt_intro v c; omega
    have hmc : mx c ≤ M := le_trans (E4.mx_intro_le v c) hmM
    have hcM : c.size ≤ M := E4.size_le_M hsc
    have hvM : v ≤ M := le_trans (le_mx_nt (NT.intro v c) (by simp [NT.mentioned])) hmM
    have hbagM : ∀ u ∈ c.bag, u ≤ M := fun u hu => le_trans (le_mx_nt c (E4.bag_subset_mentioned c hu)) hmc
    have hBm := hBm_of hB
    have hcn := E4.cnode_ge M k
    have hX := Wx_ge M k
    have hnum := numX_intro M k
    have hsqc : c.size ^ 2 * Wx M k ≤ (c.size + 1) ^ 2 * Wx M k :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 2)
    have hBc : (c.size ^ 2 * Wx M k + 2) ^ 2 < B := by
      have := hBm (c.size ^ 2 * Wx M k) (by rw [hsize]; exact hsqc); exact this
    have hcs : c.size * E4.cnode M k ≤ (c.size + 1) ^ 2 * Wx M k := by
      have : c.size * E4.cnode M k ≤ c.size * Wx M k := Nat.mul_le_mul_left _ (by omega)
      have h2 : c.size * Wx M k ≤ c.size ^ 2 * Wx M k := by
        have : c.size ≤ c.size ^ 2 := Nat.le_self_pow (by norm_num) _
        exact Nat.mul_le_mul_right _ this
      omega
    have hBt : (c.size * E4.cnode M k + 2) ^ 2 < B := by
      have := hBm (c.size * E4.cnode M k) (by rw [hsize]; exact hcs); exact this
    have hT := E4.tables_runs hΔ.e4 B x k M hxM hn hk c hgc hwc hsc hmc hBt
    have hbag := E4.ntBag_runs hΔ.e4 B (by omega) c
    have hnb := E4.nbrs_runs hΔ.e4 B x v c.bag (by omega) hn
    have hcard : c.bag.card ≤ k + 2 := bag_card_le_of_width hwc
    have hIH : ∀ cq ∈ tables (adjOfWord x) k c, Runs Δ' B fExtract [toVal x, toVal k, toVal c, toVal cq]
        (toVal (extract (adjOfWord x) k c cq)) (c.size ^ 2 * Wx M k) :=
      fun cq hcq => ih hgc hWc hwc hsc hmc hBc cq hcq
    have hTlen : (tables (adjOfWord x) k c).length ≤ Nt k := tables_length_le_pow hgc hwc
    have hG : cInC M k + Zc M k ^ pRI ≤ Gi M k := by unfold Gi; omega
    have hAlg := alg_one c.size (E4.cnode M k) (Gi M k) (Wx M k) hcpos hnum
    have hEh : cInC M k + c.size ^ 2 * Wx M k + Zc M k ^ pRI ≤ (c.size + 1) ^ 2 * Wx M k := by omega
    have hRI : Zc M k ^ pRI + 2 ≤ (c.size + 1) ^ 2 * Wx M k + 2 := by omega
    have hcI : cInC M k + 2 ≤ (c.size + 1) ^ 2 * Wx M k + 2 := by omega
    have hf : ∀ cq ∈ tables (adjOfWord x) k c, Runs Δ' B fInCand
        [toVal ((k + 1, v, nbrs (adjOfWord x) v c.bag), x, k, c, c.bag, target), toVal cq]
        (toVal (if target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq then
          (extract (adjOfWord x) k c cq).bind
            (fun t => realIntro (k + 1) v (nbrs (adjOfWord x) v c.bag) c.bag t target) else none))
        (if target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq then
          cInC M k + c.size ^ 2 * Wx M k + Zc M k ^ pRI else cInC M k) := by
      intro cq hcq
      by_cases hm : target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq
      · simp only [hm, if_true]
        obtain ⟨t0, hext, hpt, -⟩ := intro_hit_facts hs hg0 hW hcq hm
        have hsz := extract_sz_le hs hgc hWc hwc cq hcq t0 hext
        have hR := realIntro_at hΔ B hg0 hw hpt htg hsz hcM hvM hbagM
          (by have := hBm (Zc M k ^ pRI) (by rw [hsize]; omega); exact this)
        have := inCand_hit hΔ B x k v M c target cq hg0 hw hcq htg hvM hbagM hm t0 hext
          (c.size ^ 2 * Wx M k) (Zc M k ^ pRI) (hIH cq hcq) hR
          (by have := hBm (cInC M k + c.size ^ 2 * Wx M k + Zc M k ^ pRI) (by rw [hsize]; omega); exact this)
        rw [hext, Option.bind_some]
        exact this
      · simp only [hm, if_false]
        exact inCand_miss hΔ B x k v M c target cq hg0 hw hcq htg hvM hbagM hm
          (by have := hBm (cInC M k) (by rw [hsize]; omega); exact this)
    have hnone : ∀ cq ∈ tables (adjOfWord x) k c,
        (if target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq then
          (extract (adjOfWord x) k c cq).bind
            (fun t => realIntro (k + 1) v (nbrs (adjOfWord x) v c.bag) c.bag t target) else none) = none →
        (if target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq then
          cInC M k + c.size ^ 2 * Wx M k + Zc M k ^ pRI else cInC M k) ≤ cInC M k := by
      intro cq hcq hnn
      by_cases hm : target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq
      · exfalso
        obtain ⟨t0, hext, -, hsome⟩ := intro_hit_facts hs hg0 hW hcq hm
        simp only [hm, if_true, hext, Option.bind_some] at hnn
        simp [hnn] at hsome
      · simp [hm]
    have hsome : ∀ cq ∈ tables (adjOfWord x) k c,
        ((if target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq then
          (extract (adjOfWord x) k c cq).bind
            (fun t => realIntro (k + 1) v (nbrs (adjOfWord x) v c.bag) c.bag t target) else none)).isSome = true →
        (if target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq then
          cInC M k + c.size ^ 2 * Wx M k + Zc M k ^ pRI else cInC M k) ≤
          cInC M k + c.size ^ 2 * Wx M k + Zc M k ^ pRI := by
      intro cq hcq _
      by_cases hm : target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq
      · simp only [hm, if_true, le_refl]
      · simp only [hm, if_false]; omega
    have hfind := findSome_first_runs hΔ.e4.l4 B fInCand
      (toVal ((k + 1, v, nbrs (adjOfWord x) v c.bag), x, k, c, c.bag, target))
      (fun cq => if target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq then
          (extract (adjOfWord x) k c cq).bind
            (fun t => realIntro (k + 1) v (nbrs (adjOfWord x) v c.bag) c.bag t target) else none)
      (fun cq => if target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq then
          cInC M k + c.size ^ 2 * Wx M k + Zc M k ^ pRI else cInC M k)
      (tables (adjOfWord x) k c) (cInC M k) (cInC M k + c.size ^ 2 * Wx M k + Zc M k ^ pRI) hf hnone hsome
      (by omega)
    have e : extract (adjOfWord x) k (NT.intro v c) target = (tables (adjOfWord x) k c).findSome?
        (fun cq => if target ∈ introC (k + 1) v (nbrs (adjOfWord x) v c.bag) cq then
          (extract (adjOfWord x) k c cq).bind
            (fun t => realIntro (k + 1) v (nbrs (adjOfWord x) v c.bag) c.bag t target) else none) := rfl
    rw [e]
    refine intro_ext_asm hΔ B x k v c target _ _ _ _ _ _ _ _ hB1000 (k1_of_hk hk) hT hbag hnb hfind ?_
    have h1 : 24 * (tables (adjOfWord x) k c).length ≤ 24 * Nt k := by omega
    have h2 : (tables (adjOfWord x) k c).length * cInC M k ≤ Nt k * cInC M k := Nat.mul_le_mul_right _ hTlen
    have h3 : 60 * sz c ^ 2 ≤ 60 * M ^ 2 := E4.sz_sq_le hsc
    have h4 := E4.nbrs_cost_le (c := c.bag.card) (X := k + 2) (L := x.length) (M := M) hcard hxM
    unfold Gi at hAlg
    rw [hsize]
    omega

end E6b
end Lax117284Proofs.Treewidth.Fun

end
