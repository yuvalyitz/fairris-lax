import Lax117284Proofs.Treewidth.Fun.E4Base

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
