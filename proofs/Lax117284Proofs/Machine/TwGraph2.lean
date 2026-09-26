import Lax117284Proofs.Machine.TwGraph
import Lax117284.Bodlaender
import Lax117284.InstanceEncoding

/-!
The word of the graph: the fill of the matrix, the whole array, and the fact that it presents the
overall conflict graph.
-/

namespace Lax117284Proofs.Machine.TwGraph

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit
open Lax117284.Scheduling Lax117284.InstanceEncoding

variable {B : ℕ}

theorem graphFill_run (X : List ℕ) (n m : ℕ) (σ : Env) (hX : σ.arrs "X" = X)
    (hn : σ.vars "n" = n) (hm : σ.vars "m" = m) (hmn : σ.vars "mn" = m * n)
    (hmask : σ.vars "mask" = 2 ^ m - 1) (hbs : σ.vars "bs" = 1) (hfn : σ.vars "fn" = n * n)
    (hY : 1 + n * n ≤ (σ.arrs "Y").length)
    (hlen : 2 + 2 * (m * n) + 1 ≤ X.length) (hXB : ∀ v ∈ X, v < B) (hB : X.length + 8 < B)
    (hmB : m + 3 < B) (hnB : n < B) (hmk : 2 ^ m < B) (hnn : n * n + 8 < B) :
    ∃ σ', Run B (fillLoop "Y" adjCell) σ σ' ((214 * m + 90 + 20 + 4) * (n * n) + 6) ∧
      (σ'.arrs "Y").length = (σ.arrs "Y").length ∧
      (∀ k, (σ'.arrs "Y").getD k 0 =
        if 1 ≤ k ∧ k < 1 + n * n then adjBit X n m (k - 1) else (σ.arrs "Y").getD k 0) ∧
      AgrA ("fc" :: SG) "Y" σ σ' ∧ σ'.out = σ.out := by
  have hres := fillLoop_run (B := B) "Y" adjCell (adjBit X n m) ("fc" :: SG) (214 * m + 90) (n * n)
    σ hfn (by omega) (by rw [hbs]; omega)
    (fun k => by
      have : adjBit X n m k ≤ 1 := by unfold adjBit; split_ifs <;> omega
      omega) (by simp [SG, SD]) (by rw [hbs]; omega) (by
      intro τ hF hA hlt
      have hfr : ∀ y, y ∉ "fc" :: SG → τ.vars y = σ.vars y := hA.1
      have e1 : τ.vars "n" = n := by rw [hfr "n" (by simp [SG, SD])]; exact hn
      have e2 : τ.vars "m" = m := by rw [hfr "m" (by simp [SG, SD])]; exact hm
      have e3 : τ.vars "mn" = m * n := by rw [hfr "mn" (by simp [SG, SD])]; exact hmn
      have e4 : τ.vars "mask" = 2 ^ m - 1 := by rw [hfr "mask" (by simp [SG, SD])]; exact hmask
      have e5 : τ.arrs "X" = X := by rw [hA.2 "X" (by decide)]; exact hX
      obtain ⟨τ', r, hv, ha, hf, ho⟩ := adjCell_run (B := B) X n m τ e5 e1 e2 e3 e4 hlt hlen hXB hB
        hmB hnB hmk (by omega)
      exact ⟨τ', r, hv, by rw [ha], fun y hy => hf y (fun h => hy (List.mem_cons_of_mem _ h)),
        hf "fc" (by simp [SG, SD]), ho⟩)
  obtain ⟨σ', r, hl, hg, hA, ho⟩ := hres
  refine ⟨σ', r, hl, fun k => ?_, hA, ho⟩
  rw [hg k, hbs]

/-- The word of the graph: the number of clients, then the matrix. -/
def gwList (X : List ℕ) (n m : ℕ) : List ℕ := n :: (List.range (n * n)).map (adjBit X n m)

lemma gwList_length (X : List ℕ) (n m : ℕ) : (gwList X n m).length = 1 + n * n := by
  simp [gwList]; try omega

lemma gwList_getD_zero (X : List ℕ) (n m : ℕ) : (gwList X n m).getD 0 0 = n := by
  simp [gwList]

lemma gwList_getD_succ (X : List ℕ) (n m : ℕ) {k : ℕ} (hk : k < n * n) :
    (gwList X n m).getD (1 + k) 0 = adjBit X n m k := by
  simp [gwList, List.getD_eq_getElem?_getD, hk, Nat.add_comm 1 k]

/-- **The matrix is the adjacency of the overall conflict graph.** -/
theorem encodesGraph_gwList {I : Instance} {y X : List ℕ} (hy : EncodesInstance y I)
    (hXy : ∀ j < y.length, X.getD j 0 = y.getD j 0) :
    Lax117284.Bodlaender.EncodesGraph (gwList X I.clients I.days) I := by
  classical
  refine ⟨by rw [gwList_length], by rw [gwList_getD_zero], fun u v => ?_⟩
  have hnpos : 0 < I.clients := by have := u.isLt; omega
  have hk : u.val * I.clients + v.val < I.clients * I.clients := by
    calc u.val * I.clients + v.val < u.val * I.clients + I.clients := by have := v.isLt; omega
      _ = (u.val + 1) * I.clients := by ring
      _ ≤ I.clients * I.clients := Nat.mul_le_mul_right _ u.isLt
  have e : 1 + u.val * I.clients + v.val = 1 + (u.val * I.clients + v.val) := by ring
  rw [e, gwList_getD_succ _ _ _ hk]
  unfold adjBit
  have hdiv : (u.val * I.clients + v.val) / I.clients = u.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hnpos, Nat.div_eq_of_lt v.isLt, Nat.zero_add]
  have hmod : (u.val * I.clients + v.val) % I.clients = v.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt v.isLt]
  rw [hdiv, hmod]
  refine if_congr ?_ rfl rfl
  unfold Lax117284.ConflictGraph.overallGraph
  simp only
  constructor
  · rintro ⟨hne, d, hd, hc⟩
    refine ⟨fun h => hne (by simp [h]), ⟨d, hd⟩, ?_⟩
    exact (Instance.conflictAt_iff I ⟨d, hd⟩ u v).1
      ((Lax117284Proofs.Machine.TwCf.cfN_iff hy hXy hd u.isLt v.isLt).1 hc)
  · rintro ⟨hne, d, hc⟩
    refine ⟨fun h => hne (Fin.ext h), d.val, d.isLt, ?_⟩
    exact (Lax117284Proofs.Machine.TwCf.cfN_iff hy hXy d.isLt u.isLt v.isLt).2
      ((Instance.conflictAt_iff I d u v).2 hc)

end Lax117284Proofs.Machine.TwGraph
