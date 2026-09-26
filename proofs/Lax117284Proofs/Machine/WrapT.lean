import Lax117284Proofs.Machine.FreeAccept
import Lax117284Proofs.Machine.TokRun
import Lax117284Proofs.Machine.FreeMain

/-!
A reduction on the numbers of its input, once and for all: the program reads the word, tokenizes it
against a format of numbers, and then either runs the phase that writes the image or writes the
rejected word. What differs from one reduction to the next is the format, the phase and the
semantics of the image, and they are the fields of the structure.
-/

namespace Lax117284Proofs.Machine.WrapT

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime Lax117284Proofs.Codes
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan Lax117284Proofs.Machine.TokProg
open Lax117284Proofs.Machine.TokLoop Lax117284Proofs.Machine.TokBound Lax117284Proofs.Machine.TokRun
open Lax117284Proofs.Machine.FreeAccept

open scoped Classical

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- **A reduction that reads tokens — numbers and bits — and writes a word.** -/
structure WrapT where
  /-- The format of the tokens the word is a stream of. -/
  E : Format
  /-- What the format expects next, as a command. -/
  nk : Com
  Knk : ℕ
  hnk : ∀ (B Bt cap : ℕ), 2 * (Bt * Bt) + 2 * Bt + cap + 16 < B → NkSpec B Bt E cap nk Knk
  /-- The reduction, as a map on words. -/
  red : Word → Word
  /-- The streams that are mapped to an image. -/
  cond : List Tok → Prop
  /-- The image, as a word. -/
  outW : List Tok → Word
  sem_acc : ∀ ts, Conforms E ts → cond ts → red (code ts) = outW ts
  /-- The word every other word is sent to. -/
  rejW : Word
  sem_rej : ∀ w, ¬ (∃ ts, w = code ts ∧ Conforms E ts ∧ cond ts) → red w = rejW
  /-- The command that writes it. -/
  rej : Com
  Krej : ℕ → ℕ
  rejRun : ∀ (B Sz : ℕ) (σ : Env), (∀ v, v + 4 < B → v.size ≤ Sz) → 6 < B →
    ∃ σ', Run B rej σ σ' (Krej Sz) ∧ σ'.out = σ.out ++ natBits rejW
  /-- The phase that runs once the tokenizer has accepted. -/
  acc : Com
  Kacc : ℕ → ℕ → ℕ
  Kmono : ∀ Sz a b, a ≤ b → Kacc Sz a ≤ Kacc Sz b
  accRun : ∀ (B Sz L : ℕ) (ts : List Tok) (arr : List ℕ) (σ : Env), Conforms E ts →
    arr.take ts.length = ts.map Tok.val →
    σ.arrs "TK" = arr → ts.length ≤ L → (∀ t ∈ ts, Tok.val t < 2 ^ (L + 1)) →
    2 ^ (2 * L + 4) + 8 * L + 64 ≤ B → (∀ v, v + 4 < B → v.size ≤ Sz) →
    ∃ σ', Run B acc σ σ' (Kacc Sz ts.length) ∧
      σ'.out = σ.out ++ (if cond ts then natBits (outW ts) else natBits rejW)

variable (W : WrapT)

/-- The reduction: read the word, tokenize it against the format, and then either write the
output or the rejected word. -/
def WrapT.mainW : Com :=
  .seq ReadAll.readAll (.seq (tokRun "a" "L" W.nk)
    (.ite (.eq (.var "ph") (.lit 0))
      (.ite (.eq (.var "L") (.lit 0))
        (.ite (.eq (.var "kind") (.lit 2)) W.acc W.rej) W.rej) W.rej))

/-- The cost of the whole program on an input of length `l` at word size `Sz`. -/
def WrapT.Kmain (l Sz : ℕ) : ℕ :=
  (12 * l + 10) + (20 + W.Knk + ((100 + W.Knk + 4) * l + 6)) + 20 + W.Kacc Sz l + W.Krej Sz

/-- What the reduction computes, on the zeros and ones of its input. -/
noncomputable def WrapT.redBits (y : List ℕ) : List ℕ := natBits (W.red (bitsOf y))

/-- **A word the tokenizer accepts is the code of a stream of the format.** -/
theorem WrapT.accepted_stream (y : List ℕ) (hacc : Accepts W.E (run W.E init (bitsOf y))) :
    ∃ ts : List Tok, bitsOf y = code ts ∧ Conforms W.E ts ∧
      (run W.E init (bitsOf y)).toks = ts :=
  ⟨_, (accept_sound W.E hacc).1.symm, (accept_sound W.E hacc).2, rfl⟩

theorem WrapT.bits_accept (y : List ℕ) (ts : List Tok) (hw : bitsOf y = code ts)
    (hsh : Conforms W.E ts) :
    W.redBits y = if W.cond ts then natBits (W.outW ts) else natBits W.rejW := by
  unfold WrapT.redBits
  rw [hw]
  by_cases hc : W.cond ts
  · rw [if_pos hc, W.sem_acc ts hsh hc]
  · rw [if_neg hc, W.sem_rej]
    rintro ⟨ts', hw', hs', hc'⟩
    have hnn : ts' = ts := by
      rw [← (accept_complete W.E ts' hs').2, ← hw']; exact (accept_complete W.E ts hsh).2
    subst hnn
    exact hc hc'

theorem WrapT.bits_reject (y : List ℕ) (hn : ¬ Accepts W.E (run W.E init (bitsOf y))) :
    W.redBits y = natBits W.rejW := by
  unfold WrapT.redBits
  rw [W.sem_rej]
  rintro ⟨ts', hw', hs', -⟩
  apply hn
  have := (accept_complete W.E ts' hs').1
  rwa [← hw'] at this

lemma warrs_readAll : ReadAll.readAll.warrs = ["a"] := by
  simp [ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, Com.warrs]

variable {W} {B : ℕ} (y : List ℕ)

theorem mainW_spec (hyB : ∀ v ∈ y, v < B)
    (hB : 2 ^ (2 * y.length + 4) + 8 * y.length + 64 ≤ B) :
    ∃ σ', Run B W.mainW (initEnv (fun _ => y.length) (y.length :: y)) σ'
        (W.Kmain y.length B.size) ∧ σ'.out = W.redBits y := by
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
  have hnk : NkSpec B (2 ^ y.length) W.E y.length W.nk W.Knk :=
    W.hnk B _ _ (by nlinarith)
  obtain ⟨σ2, r2, hR, ho2, hlen2⟩ := (tokRun_spec (B := B) "a" "L" W.nk (by decide) y y.length
    (le_refl _) hnk (by omega) hyB) σ1 ⟨by rw [ha1, List.take_length], hL1, by rw [tk1]; simp, ho1⟩
  set st := run W.E init (bitsOf y) with hst
  have hbd : Bd st y.length := by
    have h := bd_stAt W.E y y.length (le_refl _)
    have e : stAt W.E y y.length = st := by unfold stAt; rw [List.take_length]
    rwa [e] at h
  have hkB : σ2.vars "kind" < B := by
    rw [hR.kind]; cases W.E st.toks <;> simp [kcode] <;> omega
  have hphB : σ2.vars "ph" < B := by rw [hR.ph]; have := hbd.ph; omega
  have hLB : σ2.vars "L" < B := by rw [hR.L]; have := hbd.L; omega
  by_cases hacc : Accepts W.E st
  · obtain ⟨h0, hL0, hk⟩ := hacc
    have hph : σ2.vars "ph" = 0 := by rw [hR.ph]; exact h0
    have hLv : σ2.vars "L" = 0 := by rw [hR.L]; exact hL0
    have hkind : σ2.vars "kind" = 2 := by rw [hR.kind, hk]; rfl
    obtain ⟨ts, hw, hsh, hns⟩ := W.accepted_stream y ⟨h0, hL0, hk⟩
    rw [← hst] at hns
    have hlenT : ts.length ≤ y.length := by
      have := hbd.T; rw [hns] at this; exact this
    have hval : ∀ t ∈ ts, Tok.val t < 2 ^ (y.length + 1) := fun t ht => by
      have := hbd.tok t (by rw [hns]; exact ht)
      exact this
    obtain ⟨hTv, hTK⟩ := hR.tok
    have harr : (σ2.arrs "TK").take ts.length = ts.map Tok.val := by
      rw [hns] at hTK
      exact hTK
    obtain ⟨σa, ra, oa⟩ := W.accRun B B.size y.length ts (σ2.arrs "TK") σ2 hsh harr rfl hlenT hval hB hs
    have rite := Run.ite_true (d := W.rej)
      (cond_lit_true (B := B) hph (by omega))
      (Run.ite_true (d := W.rej) (cond_lit_true (B := B) hLv (by omega))
        (Run.ite_true (d := W.rej) (cond_lit_true (B := B) hkind (by omega)) ra))
    refine ⟨σa, (r1.seq (r2.seq rite)).mono ?_, ?_⟩
    · unfold WrapT.Kmain
      simp only [Cond.size, Expr.size]
      have := W.Kmono B.size ts.length y.length hlenT
      omega
    · rw [oa, ho2, W.bits_accept y ts hw hsh]
      simp only [List.nil_append]
  · have hrej := W.bits_reject y hacc
    obtain ⟨σr, rr, orr⟩ := W.rejRun B B.size σ2 hs (by omega)
    have houtr : σr.out = W.redBits y := by
      rw [orr, ho2, hrej]; simp
    have hKrej : W.Krej B.size ≤ W.Kmain y.length B.size := by
      unfold WrapT.Kmain; omega
    by_cases h0 : st.ph = 0
    · by_cases hL0 : st.L = 0
      · have hk : W.E st.toks ≠ .done := fun hk => hacc ⟨h0, hL0, hk⟩
        have rite := Run.ite_true (d := W.rej)
          (cond_lit_true (B := B) (hR.ph.trans h0) (by omega))
          (Run.ite_true (d := W.rej) (cond_lit_true (B := B) (hR.L.trans hL0) (by omega))
            (Run.ite_false (c := W.acc) (cond_lit_false (B := B)
              (by rw [hR.kind]; exact fun h => hk (kcode_done.mp h)) hkB (by omega)) rr))
        exact ⟨σr, (r1.seq (r2.seq rite)).mono (by
          unfold WrapT.Kmain; simp only [Cond.size, Expr.size]; omega), houtr⟩
      · have rite := Run.ite_true (d := W.rej)
          (cond_lit_true (B := B) (hR.ph.trans h0) (by omega))
          (Run.ite_false (c := Com.ite (.eq (.var "kind") (.lit 2)) W.acc W.rej)
            (cond_lit_false (B := B) (by rw [hR.L]; exact hL0) hLB (by omega)) rr)
        exact ⟨σr, (r1.seq (r2.seq rite)).mono (by
          unfold WrapT.Kmain; simp only [Cond.size, Expr.size]; omega), houtr⟩
    · have rite := Run.ite_false
        (c := Com.ite (.eq (.var "L") (.lit 0))
          (.ite (.eq (.var "kind") (.lit 2)) W.acc W.rej) W.rej)
        (cond_lit_false (B := B) (by rw [hR.ph]; exact h0) hphB (by omega)) rr
      exact ⟨σr, (r1.seq (r2.seq rite)).mono (by
        unfold WrapT.Kmain; simp only [Cond.size, Expr.size]; omega), houtr⟩

end Lax117284Proofs.Machine.WrapT
