import Lax117284Proofs.Treewidth.Fun.E6bNum2
import Lax117284Proofs.Treewidth.Fun.E6bMath3

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
