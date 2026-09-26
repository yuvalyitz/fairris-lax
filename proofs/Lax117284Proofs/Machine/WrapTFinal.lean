import Lax117284Proofs.Machine.WrapT
import Lax117284Proofs.Machine.FreeFinal

/-!
A reduction of the shape of `WrapT` is polynomial-time computable: on the word RAM, and hence on a
Turing machine, once its program is laid out in memory and its accepting phase is linear in the
size of its input times the word size.
-/

namespace Lax117284Proofs.Machine.WrapTFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.WrapT Lax117284Proofs.Machine.FreeFinal
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax759944Proofs.Encoding

variable (W : WrapT) (layout : Layout)

theorem solves (hok : Com.Ok layout W.mainW) :
    Solves layout W.mainW FreeFinal.Shape (fun x => W.redBits x.tail) (fun x => Bd x.tail)
      (fun x => W.Kmain x.tail.length (Bd x.tail).size) where
  ok := hok
  inp := by
    intro x hx v hv
    rw [shape_eq hx] at hv
    have hpow : x.tail.length < 2 ^ (2 * x.tail.length + 4) := by
      have := Nat.lt_two_pow_self (n := x.tail.length)
      have h2 : 2 ^ x.tail.length ≤ 2 ^ (2 * x.tail.length + 4) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    rcases List.mem_cons.mp hv with rfl | hv'
    · unfold Bd; omega
    · have := le_Mx hv'; unfold Bd; omega
  run := by
    intro x hx
    obtain ⟨σ', hrun, hout⟩ := WrapT.mainW_spec (W := W) (B := Bd x.tail) x.tail
      (fun v hv => by
        have := le_Mx hv
        have h2 : 2 ^ (2 * x.tail.length + 4) ≥ 1 := Nat.one_le_two_pow
        unfold Bd; omega)
      (by unfold Bd; omega)
    rw [← shape_eq hx] at hrun
    exact ⟨_, σ', hrun, hout⟩

theorem prog_runs (hok : Com.Ok layout W.mainW) (harr : layout.arrays.length = 2)
    (hsc : layout.temps + layout.scalars.length ≤ 200) (w : ℕ) (x : List ℕ)
    (hfit : 202 + 2 * Bd x ≤ 2 ^ w) :
    ∃ t ≤ 10 * W.Kmain x.length (Bd x).size + 1,
      RunsTo w (compileProgram layout W.mainW) (x.length :: x) (W.redBits x) t := by
  have hs : Solves layout W.mainW {z | z = x.length :: x} (fun z => W.redBits z.tail)
      (fun z => Bd z.tail) (fun z => W.Kmain z.tail.length (Bd z.tail).size) :=
    ⟨(solves W layout hok).ok, fun z hz => (solves W layout hok).inp z
      (by rw [hz]; exact ⟨by simp, by simp⟩),
      fun z hz => (solves W layout hok).run z (by rw [hz]; exact ⟨by simp, by simp⟩)⟩
  have h := computesInTime_of_solves (w := w)
    (T := fun z => 10 * W.Kmain z.tail.length (Bd z.tail).size + 1) hs
    (fun z hz => by
      rw [hz]; simp only [List.tail_cons]
      have hB : 64 ≤ Bd x := by
        have := Nat.zero_le (2 ^ (2 * x.length + 4))
        unfold Bd; omega
      refine fitsWords_of_max_le (by omega) ?_
      simp only [Layout.span, harr, max_le_iff]
      omega)
    (fun z hz => by simp [Layout.const])
  obtain ⟨t, ht, hrun⟩ := h (x.length :: x) rfl
  exact ⟨t, by simpa using ht, by simpa using hrun⟩

/-- **The reduction is a polynomial-time word RAM computation on the zeros and ones of its
input**, when its accepting phase costs at most `C · (Sz + 1) · (l + 1) ^ e`. -/
theorem ramPolytimeE (hok : Com.Ok layout W.mainW) (harr : layout.arrays.length = 2)
    (hsc : layout.temps + layout.scalars.length ≤ 200) (C e : ℕ) (he : 1 ≤ e)
    (hK : ∀ Sz l, W.Kacc Sz l ≤ C * (Sz + 1) * (l + 1) ^ e)
    (hKr : ∀ Sz, W.Krej Sz ≤ C * (Sz + 1)) :
    RamPolytime W.redBits := by
  refine Lax117284Proofs.Machine.RamBridge2.ramPolytime_of_wordlen (d := 2) (K := 10)
    (prog := compileProgram layout W.mainW)
    (Polynomial.C (100 * (2 * C + W.Knk + 1000)) * (Polynomial.X + Polynomial.C 1) ^ (e + 1))
    (by omega) ?_ ?_
  · intro x v hv
    unfold WrapT.redBits at hv
    simp only [natBits, List.mem_map] at hv
    obtain ⟨b, -, rfl⟩ := hv
    have : (2 : ℕ) ^ 10 ≤ 2 ^ (2 * bitSize x + 10) := Nat.pow_le_pow_right (by omega) (by omega)
    split <;> omega
  · intro w x hw
    have hB := Bd_lt x
    have hlen := length_le_bitSize x
    have hfit : 202 + 2 * Bd x ≤ 2 ^ w := by
      have h1 : (2 : ℕ) ^ (2 * bitSize x + 11) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
      have e : (2 : ℕ) ^ (2 * bitSize x + 11) = 16 * 2 ^ (2 * bitSize x + 7) := by ring
      have h5 : 128 ≤ 2 ^ (2 * bitSize x + 7) := by
        calc (128 : ℕ) = 2 ^ 7 := by norm_num
          _ ≤ 2 ^ (2 * bitSize x + 7) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    obtain ⟨t, ht, hrun⟩ := prog_runs W layout hok harr hsc w x hfit
    refine ⟨t, ?_, hrun⟩
    have hsz : (Bd x).size ≤ 2 * bitSize x + 7 := Nat.size_le.mpr hB
    unfold WrapT.Kmain at ht
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
    obtain ⟨u, hu⟩ : ∃ u, u = bitSize x + 1 := ⟨_, rfl⟩
    rw [← hu]
    have hu1 : 1 ≤ u := by omega
    have hT1 : u ≤ u ^ (e + 1) := Nat.le_self_pow (by omega) u
    have hT0 : 1 ≤ u ^ (e + 1) := le_trans hu1 hT1
    have hpe : (x.length + 1) ^ e ≤ u ^ e := Nat.pow_le_pow_left (by omega) e
    have h8 : (Bd x).size + 1 ≤ 8 * u := by omega
    have hTe : u * u ^ e = u ^ (e + 1) := by rw [pow_succ']
    have hKa : W.Kacc (Bd x).size x.length ≤ 8 * C * u ^ (e + 1) := by
      calc W.Kacc (Bd x).size x.length ≤ C * ((Bd x).size + 1) * (x.length + 1) ^ e := hK _ _
        _ ≤ C * (8 * u) * u ^ e := Nat.mul_le_mul (Nat.mul_le_mul_left _ h8) hpe
        _ = 8 * C * (u * u ^ e) := by ring
        _ = 8 * C * u ^ (e + 1) := by rw [hTe]
    have hKb : W.Krej (Bd x).size ≤ 8 * C * u ^ (e + 1) := by
      calc W.Krej (Bd x).size ≤ C * ((Bd x).size + 1) := hKr _
        _ ≤ C * (8 * u) := Nat.mul_le_mul_left _ h8
        _ = 8 * C * u := by ring
        _ ≤ 8 * C * u ^ (e + 1) := Nat.mul_le_mul_left _ hT1
    have hL1 : (W.Knk + 116) * x.length ≤ (W.Knk + 116) * u ^ (e + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hL2 : W.Knk + 56 ≤ (W.Knk + 56) * u ^ (e + 1) := Nat.le_mul_of_pos_right _ hT0
    have hmain : 12 * x.length + 10 + (20 + W.Knk + ((100 + W.Knk + 4) * x.length + 6)) + 20 +
        W.Kacc (Bd x).size x.length + W.Krej (Bd x).size ≤
        (2 * W.Knk + 172 + 16 * C) * u ^ (e + 1) := by nlinarith
    nlinarith [hmain, hT0, Nat.zero_le C, Nat.zero_le W.Knk]

/-- **The reduction is polynomial-time computable.** -/
theorem polyTimeE (hok : Com.Ok layout W.mainW) (harr : layout.arrays.length = 2)
    (hsc : layout.temps + layout.scalars.length ≤ 200) (C e : ℕ) (he : 1 ≤ e)
    (hK : ∀ Sz l, W.Kacc Sz l ≤ C * (Sz + 1) * (l + 1) ^ e)
    (hKr : ∀ Sz, W.Krej Sz ≤ C * (Sz + 1)) :
    Nonempty (Turing.TM2ComputableInPolyTime id id W.red) := by
  refine Lax117284Proofs.Machine.RamToTuring.polyTime_of_ram
    (ramPolytimeE W layout hok harr hsc C e he hK hKr) ?_
  intro w
  unfold WrapT.redBits
  rw [bitsOf_natBits]

end Lax117284Proofs.Machine.WrapTFinal
