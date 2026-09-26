import Lax117284Proofs.Machine.FreeMain
import Lax117284Proofs.Machine.TokRun

/-!
The whole reduction as one program, and what it computes.
-/

namespace Lax117284Proofs.Machine.FreeRun

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan Lax117284Proofs.Machine.TokProg
open Lax117284Proofs.Machine.TokLoop Lax117284Proofs.Machine.TokBound Lax117284Proofs.Machine.TokRun
open Lax117284Proofs.Machine.InstSem Lax117284Proofs.Machine.UNk
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.FreeAccept
open Lax117284Proofs.Machine.FreeMain

/-- The reduction: read the word, tokenize it against the format, and then either write the
output or the rejected word. -/
def mainFree : Com :=
  .seq ReadAll.readAll (.seq (tokRun "a" "L" nkU)
    (.ite (.eq (.var "ph") (.lit 0))
      (.ite (.eq (.var "L") (.lit 0))
        (.ite (.eq (.var "kind") (.lit 2)) acceptFree rejectPrint) rejectPrint) rejectPrint))

/-- The cost of the whole program on an input of length `l` at word size `Sz`. -/
def Kmain (l Sz : ℕ) : ℕ :=
  (12 * l + 10) + (20 + 60 + ((100 + 60 + 4) * l + 6)) + 20 + Kacc Sz l + 3 * (48 * Sz + 50)

lemma warrs_readAll : ReadAll.readAll.warrs = ["a"] := by
  simp [ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, Com.warrs]

variable {B : ℕ} (y : List ℕ)

theorem mainFree_spec (hyB : ∀ v ∈ y, v < B)
    (hB : 2 ^ (2 * y.length + 4) + 8 * y.length + 64 ≤ B) :
    ∃ σ', Run B mainFree (initEnv (fun _ => y.length) (y.length :: y)) σ'
        (Kmain y.length B.size) ∧
      σ'.out = natBits (Lax117284.Corollary8.reduceFreeDay (bitsOf y)) := by
  have hpow : y.length < 2 ^ y.length := Nat.lt_two_pow_self
  have hpow1 : (2 : ℕ) ^ (y.length + 1) = 2 * 2 ^ y.length := by ring
  have hpow2 : (2 : ℕ) ^ (2 * y.length + 4) = 16 * (2 ^ y.length * 2 ^ y.length) := by ring
  have hPP : 2 ^ y.length ≤ 2 ^ y.length * 2 ^ y.length :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have hs : ∀ v, v + 4 < B → v.size ≤ B.size := fun v hv => Nat.size_le_size (by omega)
  set σ0 := initEnv (fun _ => y.length) (y.length :: y) with hσ0
  -- read the word
  obtain ⟨σ1, r1, ⟨hL1, ha1, ho1, -⟩, fv1, fa1, -, -⟩ :=
    (ReadAll.readAll_spec (B := B) (y := y) hyB (by omega)).frame σ0
      ⟨rfl, rfl, by simp [hσ0, initEnv]⟩
  have tk1 : σ1.arrs "TK" = List.replicate y.length 0 := by
    rw [fa1 "TK" (by simp [warrs_readAll])]; rfl
  -- tokenize
  have hnk : NkSpec B (2 ^ y.length) (EI eU) y.length nkU 60 :=
    nkU_spec (B := B) _ _ (by nlinarith)
  obtain ⟨σ2, r2, hR, ho2, hlen2⟩ := (tokRun_spec (B := B) "a" "L" nkU (by decide) y y.length
    (le_refl _) hnk (by omega) hyB) σ1 ⟨by rw [ha1, List.take_length], hL1, by rw [tk1]; simp, ho1⟩
  set st := run (EI eU) init (bitsOf y) with hst
  have hbd : Bd st y.length := by
    have h := bd_stAt (EI eU) y y.length (le_refl _)
    have e : stAt (EI eU) y y.length = st := by unfold stAt; rw [List.take_length]
    rwa [e] at h
  have hkB : σ2.vars "kind" < B := by
    rw [hR.kind]; cases (EI eU) st.toks <;> simp [kcode] <;> omega
  have hphB : σ2.vars "ph" < B := by rw [hR.ph]; have := hbd.ph; omega
  have hLB : σ2.vars "L" < B := by rw [hR.L]; have := hbd.L; omega
  have hmono : ∀ N, N ≤ y.length → Kacc B.size N ≤ Kacc B.size y.length := fun N hN => by
    unfold Kacc
    nlinarith [Nat.mul_le_mul_left (96 * B.size + 200) (Nat.mul_le_mul_left 3 hN)]
  by_cases hacc : Accepts (EI eU) st
  · obtain ⟨h0, hL0, hk⟩ := hacc
    have hph : σ2.vars "ph" = 0 := by rw [hR.ph]; exact h0
    have hLv : σ2.vars "L" = 0 := by rw [hR.L]; exact hL0
    have hkind : σ2.vars "kind" = 2 := by rw [hR.kind, hk]; rfl
    obtain ⟨ns, hw, hsh, hns⟩ := accepted_stream y ⟨h0, hL0, hk⟩
    rw [← hst] at hns
    have hlenT : ns.length ≤ y.length := by
      have := hbd.T; rw [hns] at this; simpa using this
    have hval : ∀ v ∈ ns, v < 2 ^ (y.length + 1) := fun v hv => by
      have := hbd.tok (.num v) (by rw [hns]; exact List.mem_map_of_mem hv)
      simpa [Tok.val] using this
    obtain ⟨hTv, hTK⟩ := hR.tok
    have harr : (σ2.arrs "TK").take ns.length = ns := by
      rw [hns] at hTK
      simpa [List.map_map, Function.comp_def, Tok.val] using hTK
    have hg : ∀ k < ns.length, (σ2.arrs "TK").getD k 0 = ns.getD k 0 := fun k hk => by
      conv_rhs => rw [← harr]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
    obtain ⟨hs2, hsl⟩ := hsh
    simp only [eU] at hsl
    have hm : (σ2.arrs "TK").getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
    have hn : (σ2.arrs "TK").getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
    set arr := σ2.arrs "TK" with harrdef
    have hN : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) = ns.length := by
      rw [hm, hn]; omega
    have hnsv : ∀ k < ns.length, ns.getD k 0 < 2 ^ (y.length + 1) := fun k hk => by
      rw [List.getD_eq_getElem _ _ hk]; exact hval _ (List.getElem_mem hk)
    have hE : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), arr.getD k 0 + 8 < B := fun k hk => by
      rw [hg k (by omega)]; have := hnsv k (by omega); omega
    have hnB : arr.getD 0 0 < 2 ^ (y.length + 1) := by rw [hn]; exact hnsv 0 (by omega)
    obtain ⟨σa, ra, oa⟩ := acceptFree_run (B := B) B.size arr σ2 hs hE (by omega)
      (by rw [hlen2]; omega) (by omega)
      (fun hmpos => by
        have hnN : arr.getD 0 0 ≤ arr.getD 1 0 * arr.getD 0 0 := Nat.le_mul_of_pos_left _ hmpos
        have hgap : gapOf arr ≤ 2 ^ (y.length + 1) := by
          unfold gapOf
          refine foldl_max_le _ _ _ 0 (Nat.zero_le _) fun j hj => ?_
          have := hnsv (2 + 2 * j) (by omega)
          rw [hg _ (by omega)]; omega
        nlinarith [Nat.mul_le_mul hnB.le hgap]) rfl
    have rite := Run.ite_true (d := rejectPrint)
      (cond_lit_true (B := B) hph (by omega))
      (Run.ite_true (d := rejectPrint) (cond_lit_true (B := B) hLv (by omega))
        (Run.ite_true (d := rejectPrint) (cond_lit_true (B := B) hkind (by omega)) ra))
    refine ⟨σa, (r1.seq (r2.seq rite)).mono ?_, ?_⟩
    · unfold Kmain
      simp only [Cond.size, Expr.size]
      have := hmono (arr.getD 1 0 * arr.getD 0 0) (by omega)
      omega
    · rw [oa, ho2]
      simp only [List.nil_append]
      exact (bits_accept y arr ⟨h0, hL0, hk⟩ hTK).symm
  · have hrej := bits_reject y hacc
    obtain ⟨σr, rr, orr, -, -⟩ := rejectPrint_run (B := B) B.size σ2 hs (by omega)
    have houtr : σr.out = natBits (Lax117284.Corollary8.reduceFreeDay (bitsOf y)) := by
      rw [orr, ho2, hrej]; simp
    have hKrej : 3 * (48 * B.size + 50) ≤ Kmain y.length B.size := by
      unfold Kmain; omega
    by_cases h0 : st.ph = 0
    · by_cases hL0 : st.L = 0
      · have hk : EI eU st.toks ≠ .done := fun hk => hacc ⟨h0, hL0, hk⟩
        have rite := Run.ite_true (d := rejectPrint)
          (cond_lit_true (B := B) (hR.ph.trans h0) (by omega))
          (Run.ite_true (d := rejectPrint) (cond_lit_true (B := B) (hR.L.trans hL0) (by omega))
            (Run.ite_false (c := acceptFree) (cond_lit_false (B := B)
              (by rw [hR.kind]; exact fun h => hk (kcode_done.mp h)) hkB (by omega)) rr))
        exact ⟨σr, (r1.seq (r2.seq rite)).mono (by
          unfold Kmain; simp only [Cond.size, Expr.size]; omega), houtr⟩
      · have rite := Run.ite_true (d := rejectPrint)
          (cond_lit_true (B := B) (hR.ph.trans h0) (by omega))
          (Run.ite_false (c := Com.ite (.eq (.var "kind") (.lit 2)) acceptFree rejectPrint)
            (cond_lit_false (B := B) (by rw [hR.L]; exact hL0) hLB (by omega)) rr)
        exact ⟨σr, (r1.seq (r2.seq rite)).mono (by
          unfold Kmain; simp only [Cond.size, Expr.size]; omega), houtr⟩
    · have rite := Run.ite_false
        (c := Com.ite (.eq (.var "L") (.lit 0))
          (.ite (.eq (.var "kind") (.lit 2)) acceptFree rejectPrint) rejectPrint)
        (cond_lit_false (B := B) (by rw [hR.ph]; exact h0) hphB (by omega)) rr
      exact ⟨σr, (r1.seq (r2.seq rite)).mono (by
        unfold Kmain; simp only [Cond.size, Expr.size]; omega), houtr⟩

end Lax117284Proofs.Machine.FreeRun
