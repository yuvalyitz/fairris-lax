import Lax117284Proofs.Machine.MisRun
import Lax117284Proofs.Machine.MisCong

/-!
The word of the machine is large enough for everything the accepting phase of Lemma 14 computes,
and the phase costs at most a cubic in the number of tokens.
-/

namespace Lax117284Proofs.Machine.MisBound

open Lax117284Proofs.Machine.MisSem Lax117284Proofs.Machine.MisPrint Lax117284Proofs.Machine.MisChk
open Lax117284Proofs.Machine.MisRun
open Lax117284Proofs.Machine.MisJob (Mag)
open Lax117284Proofs.Machine.MisFormat (VM)

/-- **The cost of the accepting phase is a polynomial.** -/
theorem Kreal_le (Sz l Vn VVn DC CC : ℕ) (hV : Vn ≤ l) (hVV : VVn = Vn * Vn) (hVl : VVn ≤ l)
    (hDC : DC ≤ 12 * ((l + 1) * (l + 1))) (hCC : CC ≤ 4 * (l + 1)) :
    Kreal Sz Vn VVn DC CC ≤ 30000 * (Sz + 1) * (l + 1) ^ 3 := by
  unfold Kreal Kprint Kcell Kkv MisJob.Kjob Kchk
  have hA : 100 + (300 + (84 * VVn + 20) + 2 * (44 * Vn + 20)) + 2 * (48 * Sz + 50) + 10 + 4 ≤
      574 * ((l + 1) * (Sz + 1)) := by nlinarith [Nat.zero_le (l * Sz)]
  have hB := Nat.mul_le_mul hA hDC
  have hC : (100 + (48 * Sz + 50) + 10 + 4) * CC ≤ (164 + 48 * Sz) * (4 * (l + 1)) :=
    Nat.mul_le_mul (by omega) hCC
  have hD : ((40 + 4) * Vn + 100 + 4) * Vn = 44 * VVn + 104 * Vn := by rw [hVV]; ring
  obtain ⟨x, hx⟩ : ∃ x, x = l + 1 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = Sz + 1 := ⟨_, rfl⟩
  have hx1 : 1 ≤ x := by omega
  have hy1 : 1 ≤ y := by omega
  have hxx : x ≤ x * x := Nat.le_mul_of_pos_left _ (by omega)
  have hxxx : x * x ≤ x * x * x := Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = x * x * x * y := ⟨_, rfl⟩
  have hZx : x ≤ Z := by
    rw [hZ]; calc x ≤ x * x := hxx
      _ ≤ x * x * x := hxxx
      _ ≤ x * x * x * y := Nat.le_mul_of_pos_right _ (by omega)
  have hZy : y ≤ Z := by
    rw [hZ]; calc y ≤ 1 * y := by omega
      _ ≤ x * x * x * y := Nat.mul_le_mul_right _ (by have := Nat.mul_le_mul hxx hx1; nlinarith)
  have hZxy : x * y ≤ Z := by
    rw [hZ]; exact Nat.mul_le_mul_right _ (le_trans hxx hxxx)
  have hZ2 : 12 * (x * x) * (574 * (x * y)) ≤ 6888 * Z := by
    rw [hZ]; nlinarith [Nat.zero_le (x * x * x * y)]
  have hxy : (l + 1) * (Sz + 1) = x * y := by rw [hx, hy]
  have hxx' : (l + 1) * (l + 1) = x * x := by rw [hx]
  rw [hxy, hxx'] at hB
  have hcube : 30000 * (Sz + 1) * (l + 1) ^ 3 = 30000 * Z := by rw [hZ, ← hx, ← hy]; ring
  rw [hcube]
  have hC' : (164 + 48 * Sz) * (4 * (l + 1)) ≤ 656 * Z := by
    have : (164 + 48 * Sz) * (4 * (l + 1)) ≤ 656 * (x * y) := by
      rw [hx, hy]; nlinarith [Nat.zero_le (l * Sz)]
    omega
  have hB' : (100 + (300 + (84 * VVn + 20) + 2 * (44 * Vn + 20)) + 2 * (48 * Sz + 50) + 10 + 4) * DC ≤
      6888 * Z := by
    calc _ ≤ 574 * (x * y) * (12 * (x * x)) := hB
      _ = 12 * (x * x) * (574 * (x * y)) := by ring
      _ ≤ 6888 * Z := hZ2
  omega

lemma Mag_cong {arr ns : List ℕ} (h : MisCong.AgrM arr ns) : Mag arr = Mag ns := by
  unfold Mag
  rw [MisCong.spanN_cong h, MisCong.degN_cong h, MisCong.nN_cong h]

section Shape

variable {ns : List ℕ}

lemma VM_le_len (hsh : MisFormat.ShapeM ns) : VM ns ≤ ns.length := by
  obtain ⟨-, hl, -⟩ := hsh
  rcases Nat.eq_zero_or_pos (VM ns) with h | h
  · omega
  · have := Nat.le_mul_of_pos_left (VM ns) h; omega

lemma VV_le_len (hsh : MisFormat.ShapeM ns) : VM ns * VM ns ≤ ns.length := by
  obtain ⟨-, hl, -⟩ := hsh; omega

lemma edgeN_le (ns : List ℕ) : edgeN ns ≤ VM ns * VM ns := by
  unfold edgeN
  have := List.countP_le_length (p := qualE ns) (l := List.range (VM ns * VM ns))
  simpa using this

lemma rowSum_le (ns : List ℕ) : rowSum ns 0 ≤ VM ns := by
  unfold rowSum
  have := List.countP_le_length (p := fun w' => decide (mat ns 0 w' = 1)) (l := List.range (VM ns))
  simpa using this

lemma degN_le (ns : List ℕ) : degN ns ≤ VM ns + 1 := by
  have := rowSum_le ns
  unfold degN; omega

lemma lN_le_VM (h : 4 ≤ nN ns) : lN ns ≤ VM ns := by
  rw [MisSem.VM_eq]; exact Nat.le_mul_of_pos_right _ (by omega)

lemma daysN_le (hsh : MisFormat.ShapeM ns) (h : 4 ≤ nN ns) : daysN ns ≤ 3 * ns.length := by
  have h1 := VM_le_len hsh
  have h2 := VV_le_len hsh
  have h3 := edgeN_le ns
  have h4 := lN_le_VM h
  have h5 : lN ns * (nN ns + 1) = VM ns + lN ns := by rw [Nat.mul_add, Nat.mul_one, MisSem.VM_eq]
  unfold daysN; omega

lemma clN_le (hsh : MisFormat.ShapeM ns) (h : 4 ≤ nN ns) : clN ns ≤ 4 * ns.length + 3 := by
  have h1 := VM_le_len hsh
  have h2 := VV_le_len hsh
  have h4 := lN_le_VM h
  have h5 : VM ns * degN ns ≤ VM ns * (VM ns + 1) := Nat.mul_le_mul_left _ (degN_le ns)
  have h6 : VM ns * (VM ns + 1) = VM ns * VM ns + VM ns := by rw [Nat.mul_add, Nat.mul_one]
  unfold clN; omega

end Shape

/-- **The numbers of the accepting phase fit in the word.** -/
theorem accept_bounds (ns : List ℕ) (B L : ℕ) (hsh : MisFormat.ShapeM ns)
    (hlL : ns.length ≤ L) (hv : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1))
    (hB : 2 ^ (2 * L + 4) + 8 * L + 64 ≤ B) :
    (∀ k < VM ns * VM ns, ns.getD (2 + k) 0 + 8 < B) ∧ lN ns + 8 < B ∧ nN ns + 8 < B ∧
    VM ns * VM ns + 2 * VM ns + nN ns + 40 < B ∧
    2 * (VM ns * VM ns) + 2 * VM ns + 2 * lN ns + 60 < B ∧
    (CondM ns → Mag ns + 4 < B) ∧
    (CondM ns → daysN ns * clN ns + clN ns + daysN ns + 100 < B) := by
  have hsh0 := hsh
  obtain ⟨h2, hl, -⟩ := hsh
  have h1 := VM_le_len hsh0
  have h3 := VV_le_len hsh0
  obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ L := ⟨_, rfl⟩
  have hPL : L + 1 ≤ P := by rw [hP]; exact Nat.lt_two_pow_self
  have hP4 : 4 ≤ P := by
    rw [hP]; calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * P := by rw [hP]; ring
  have hpow2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (P * P) := by rw [hP]; ring
  rw [hpow2] at hB
  rw [hpow1] at hv
  have hPP : 4 * P ≤ P * P := Nat.mul_le_mul_right P hP4
  have hLL : L * L + 2 * L + 1 ≤ P * P := by nlinarith [Nat.mul_le_mul hPL hPL]
  have hl0 : lN ns < 2 * P := hv 0 (by omega)
  have hn0 : nN ns < 2 * P := hv 1 (by omega)
  refine ⟨fun k hk => ?_, by omega, by omega, by omega, by omega, fun hc => ?_, fun hc => ?_⟩
  · have := hv (2 + k) (by omega); omega
  · have h4 : 4 ≤ nN ns := hc.1
    have hdg := degN_le ns
    have hsp : spanN ns ≤ 2 + 4 * L := by
      have h5 : VM ns * degN ns ≤ VM ns * (VM ns + 1) := Nat.mul_le_mul_left _ hdg
      have h6 : VM ns * (VM ns + 1) = VM ns * VM ns + VM ns := by rw [Nat.mul_add, Nat.mul_one]
      have := lN_le_VM h4
      unfold spanN; omega
    have hdn : degN ns * nN ns ≤ 2 * (P * P) := by
      calc degN ns * nN ns ≤ P * (2 * P) := Nat.mul_le_mul (by omega) (by omega)
        _ = 2 * (P * P) := by ring
    unfold Mag; omega
  · have h4 : 4 ≤ nN ns := hc.1
    have hd := daysN_le hsh0 h4
    have hcl := clN_le hsh0 h4
    have hDC : daysN ns * clN ns ≤ (3 * L) * (4 * L + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hDC' : (3 * L) * (4 * L + 3) = 12 * (L * L) + 9 * L := by ring
    omega

end Lax117284Proofs.Machine.MisBound
