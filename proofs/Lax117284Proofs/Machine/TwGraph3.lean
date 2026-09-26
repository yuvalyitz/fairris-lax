import Lax117284Proofs.Machine.TwGraph2

/-!
The array `Y`: the word of the graph followed by the width.
-/

namespace Lax117284Proofs.Machine.TwGraph

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {B : ℕ}

lemma list_ext_getD {a b : List ℕ} (hl : a.length = b.length)
    (h : ∀ k, a.getD k 0 = b.getD k 0) : a = b := by
  apply List.ext_getElem hl
  intro k h1 h2
  have := h k
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

lemma getD_append_singleton (l : List ℕ) (w k : ℕ) :
    (l ++ [w]).getD k 0 = if k < l.length then l.getD k 0 else if k = l.length then w else 0 := by
  by_cases h : k < l.length
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [if_neg h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : l.length ≤ k)]
    by_cases h2 : k = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : k - l.length ≥ 1 := by omega
      rw [List.getElem?_eq_none (by simp; omega)]; simp

/-- The count, and the range of the fill. -/
def gwPre : Com := seqs
  [ .store "Y" (Expr.lit 0) (V "n"),
    .assign "bs" (Expr.lit 1),
    .assign "fn" (mul (V "n") (V "n")) ]

/-- The width. -/
def gwPost : Com := .store "Y" (add (mul (V "n") (V "n")) (Expr.lit 1)) (V "w")

/-- **The word handed to the decomposition step**: the count, the matrix, the width. -/
def gwCom : Com := .seq gwPre (.seq (fillLoop "Y" adjCell) gwPost)

/-- The scalars the word writes. -/
def SGW : List String := "fc" :: SG ++ ["bs", "fn"]

theorem gwPre_run (σ : Env) (n : ℕ) (hn : σ.vars "n" = n) (hnB : n < B) (hnn : n * n + 3 < B)
    (hY : 0 < (σ.arrs "Y").length) :
    ∃ σ1, Run B gwPre σ σ1 20 ∧
      σ1 = (((σ.setArr "Y" 0 n).setVar "bs" 1).setVar "fn" (n * n)) := by
  unfold gwPre seqs
  run_vcg
  all_goals (try nrmB)
  all_goals try (first | omega | (simp only [hn]; omega))
  all_goals (try simp only [hn])

theorem gwPost_run (σ : Env) (n : ℕ) (hn : σ.vars "n" = n) (hnB : n < B) (hnn : n * n + 3 < B)
    (hw : σ.vars "w" < B) (hlen : n * n + 1 < (σ.arrs "Y").length) :
    ∃ σ1, Run B gwPost σ σ1 20 ∧ σ1 = σ.setArr "Y" (n * n + 1) (σ.vars "w") := by
  unfold gwPost
  run_vcg
  all_goals (try nrmB)
  all_goals try (first | omega | (simp only [hn]; omega))
  all_goals (try simp only [hn])

theorem gwCom_run (X : List ℕ) (n m : ℕ) (σ : Env) (hX : σ.arrs "X" = X)
    (hn : σ.vars "n" = n) (hm : σ.vars "m" = m) (hmn : σ.vars "mn" = m * n)
    (hmask : σ.vars "mask" = 2 ^ m - 1) (hY : σ.arrs "Y" = List.replicate (n * n + 2) 0)
    (hlen : 2 + 2 * (m * n) + 1 ≤ X.length) (hXB : ∀ v ∈ X, v < B) (hB : X.length + 8 < B)
    (hmB : m + 3 < B) (hnB : n < B) (hmk : 2 ^ m < B) (hnn : n * n + 8 < B)
    (hw : σ.vars "w" < B) :
    ∃ σ', Run B gwCom σ σ' ((214 * m + 90 + 20 + 4) * (n * n) + 6 + 60) ∧
      σ'.arrs "Y" = gwList X n m ++ [σ.vars "w"] ∧
      (∀ a, a ≠ "Y" → σ'.arrs a = σ.arrs a) ∧ (∀ v, v ∉ SGW → σ'.vars v = σ.vars v) ∧
      σ'.out = σ.out := by
  obtain ⟨σ1, r1, e1⟩ := gwPre_run (B := B) σ n hn hnB (by omega) (by rw [hY]; simp)
  have hY1 : σ1.arrs "Y" = (List.replicate (n * n + 2) 0).set 0 n := by rw [e1]; simp [hY]
  have hY1l : (σ1.arrs "Y").length = n * n + 2 := by rw [hY1]; simp
  have hoth1 : ∀ a, a ≠ "Y" → σ1.arrs a = σ.arrs a := by intro a ha; rw [e1]; simp [ha]
  have hv1 : ∀ v, v ≠ "bs" → v ≠ "fn" → σ1.vars v = σ.vars v := by
    intro v h1 h2; rw [e1]; simp [Env.setVar, h1, h2]
  obtain ⟨σ4, r4, hl4, hg4, hA4, ho4⟩ := graphFill_run (B := B) X n m σ1
    (by rw [hoth1 "X" (by decide), hX])
    (by rw [hv1 "n" (by decide) (by decide), hn]) (by rw [hv1 "m" (by decide) (by decide), hm])
    (by rw [hv1 "mn" (by decide) (by decide), hmn])
    (by rw [hv1 "mask" (by decide) (by decide), hmask]) (by rw [e1]; simp) (by rw [e1]; simp)
    (by rw [hY1l]; omega) hlen hXB hB hmB hnB hmk hnn
  have hv4 : ∀ v, v ∉ SGW → σ4.vars v = σ.vars v := by
    intro v hv
    have h4 : σ4.vars v = σ1.vars v := hA4.1 v (fun h => hv (by
      simp only [SGW, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
      simp only [List.mem_cons] at h ⊢; tauto))
    rw [h4, hv1 v (fun h => hv (by simp [SGW, h])) (fun h => hv (by simp [SGW, h]))]
  have hw4 : σ4.vars "w" = σ.vars "w" := hv4 "w" (by simp [SGW, SG, SD])
  have hn4 : σ4.vars "n" = n := by rw [hv4 "n" (by simp [SGW, SG, SD]), hn]
  have hYl4 : (σ4.arrs "Y").length = n * n + 2 := by rw [hl4, hY1l]
  obtain ⟨σ5, r5, e5⟩ := gwPost_run (B := B) σ4 n hn4 hnB (by omega) (by rw [hw4]; exact hw)
    (by rw [hYl4]; omega)
  have hY5 : σ5.arrs "Y" = (σ4.arrs "Y").set (n * n + 1) (σ.vars "w") := by
    rw [e5, hw4]; simp
  refine ⟨σ5, ?_, ?_, ?_, ?_, ?_⟩
  · exact (r1.seq (r4.seq r5)).mono (by omega)
  · rw [hY5]
    refine list_ext_getD (by rw [List.length_set, hYl4]; simp [gwList_length]; omega) (fun k => ?_)
    rw [getD_set', getD_append_singleton, gwList_length, hYl4]
    by_cases hk : k = n * n + 1
    · subst hk
      rw [if_pos ⟨rfl, by omega⟩, if_neg (by omega), if_pos (by omega)]
    · by_cases hk0 : k = 0
      · subst hk0
        rw [if_neg (by omega), hg4 0, if_neg (by omega), if_pos (by omega)]
        rw [hY1, getD_set', if_pos ⟨rfl, by simp⟩, gwList_getD_zero]
      · by_cases hkr : k < 1 + n * n
        · rw [if_neg (by omega), if_pos hkr, hg4 k, if_pos ⟨by omega, hkr⟩]
          have : k = 1 + (k - 1) := by omega
          conv_rhs => rw [this]
          rw [gwList_getD_succ X n m (by omega)]
        · rw [if_neg (by omega), if_neg hkr, if_neg (by omega), hg4 k, if_neg (by omega)]
          rw [hY1, getD_set']
          rw [if_neg (by omega)]
          exact List.getD_eq_default _ _ (by simp; omega)
  · intro a ha
    rw [e5]; simp [ha, hA4.2 a ha, hoth1 a ha]
  · intro v hv
    rw [e5, hw4]; simp [hv4 v hv]
  · rw [e5]; simp [ho4, e1]

end Lax117284Proofs.Machine.TwGraph
