import Lax117284Proofs.Treewidth.Fun.E6bRealJ

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
