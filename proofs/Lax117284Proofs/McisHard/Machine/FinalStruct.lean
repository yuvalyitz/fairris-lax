import Lax117284Proofs.McisHard.Machine.AcceptRun
import Lax117284Proofs.McisHard.MathFinal
import Lax117284Proofs.Machine.SatNk
import Lax117284Proofs.Machine.WrapTFinal

/-!
# The reduction to `H` as a `WrapT` (WP9, part 1)
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem Lax117284Proofs.Machine.SatCong
open Lax117284Proofs.Machine.WrapT Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.TokModel
open Lax117284Proofs.Machine.TokProg (Tok.val)
open Lax117284Proofs.McisHard Lax117284Proofs.McisHard.Acc

open scoped Classical

/-- The image is at most `2^(2L+4)`: `400 (S+1)² + 8 < 2^(2L+4) + 8L + 64` once `L ≥ 3 + 2S`. -/
theorem sq_le_pow (S : ℕ) : 400 * (S + 1) ^ 2 ≤ 1024 * 16 ^ S := by
  induction S with
  | zero => norm_num
  | succ n ih =>
    have e : 16 ^ (n + 1) = 16 * 16 ^ n := by ring
    rw [e]
    nlinarith [Nat.zero_le n]

theorem V_lt_B (S L B : ℕ) (hL : 3 + 2 * S ≤ L) (hB : 2 ^ (2 * L + 4) + 8 * L + 64 ≤ B) :
    400 * (S + 1) ^ 2 + 8 < B := by
  have h1 := sq_le_pow S
  have h2 : (1024 : ℕ) * 16 ^ S = 2 ^ (4 * S + 10) := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
    rw [show (1024 : ℕ) = 2 ^ 10 by norm_num, ← pow_add]; ring_nf
  have h3 : 2 ^ (4 * S + 10) ≤ 2 ^ (2 * L + 4) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- **The reduction as a reduction on tokens.** -/
noncomputable def W : WrapT where
  E := EF
  nk := Lax117284Proofs.Machine.SatNk.nkF
  Knk := 80
  hnk := fun B Bt cap hB => Lax117284Proofs.Machine.SatNk.nkF_spec (B := B) Bt cap hB
  red := reduceMcis
  cond := fun ts => CondN (ts.map Tok.val)
  outW := fun ts => Lax117284.MulticolouredIndepSet.encodeInstance (Hfin (ts.map Tok.val))
  sem_acc := fun ts hc hcond => Proved.reduceMcis_code ts hc hcond
  rejW := []
  sem_rej := fun w h => Proved.reduceMcis_rej w h
  rej := Com.skip
  Krej := fun _ => 1
  rejRun := fun B Sz σ hs hB => ⟨σ, Run.skip, by simp [natBits]⟩
  acc := accMcis
  Kacc := KaccM
  Kmono := KaccM_mono
  accRun := fun B Sz L ts arr σ hconf harr hA hlenL hvals hB hs => by
    obtain ⟨hshape, hts⟩ := shape_of_conforms hconf
    have hsh := hshape
    obtain ⟨h3, hl, hsg⟩ := hshape
    have hlenns : (ts.map Tok.val).length = ts.length := by simp
    have harr' : arr.take (ts.map Tok.val).length = ts.map Tok.val := by rw [hlenns]; exact harr
    obtain ⟨S, hS⟩ : ∃ S, SlotsN (ts.map Tok.val) = S := ⟨_, rfl⟩
    have hl' := hl
    rw [hS] at hl' hsg
    have hval : ∀ k < (ts.map Tok.val).length, (ts.map Tok.val).getD k 0 < 2 ^ (L + 1) := by
      intro k hk
      rw [List.getD_eq_getElem _ _ hk]
      obtain ⟨t, ht, e⟩ := List.mem_map.mp (List.getElem_mem hk)
      rw [← e]
      exact hvals t ht
    have hL3 : 3 ≤ L := by omega
    have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
    have hpow2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (2 ^ L * 2 ^ L) := by ring
    have hP8 : 8 ≤ 2 ^ L := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hL3
    have hPL : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self
    have hPP : 8 * 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul_right _ hP8
    have hE : ∀ k < 3 + 2 * S, (ts.map Tok.val).getD k 0 + 8 < B := by
      intro k hk
      have := hval k (by omega)
      omega
    have hn0 := hval 0 (by omega)
    have hSN : 2 * (ts.map Tok.val).getD 1 0 + 3 * (ts.map Tok.val).getD 2 0 = S := hS
    have hVl : 400 * (S + 1) ^ 2 + 8 < B := V_lt_B S L B (by omega) hB
    obtain ⟨σ', r, o⟩ := accMcis_run (B := B) Sz ts.length arr (ts.map Tok.val) σ hs hA hsh harr'
      (by rw [hS]; exact hE) (by rw [hS]; omega) (by rw [hS]; omega) (by omega) (by rw [hS]; exact hVl)
    refine ⟨σ', r, ?_⟩
    rw [o]
    show _ = σ.out ++ (if CondN (ts.map Tok.val) then
      natBits (Lax117284.MulticolouredIndepSet.encodeInstance (Hfin (ts.map Tok.val))) else natBits [])
    simp [natBits]

end Lax117284Proofs.McisHard.Final
