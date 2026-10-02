import Lax117284Proofs.Treewidth.Fun.VMSolve

/-!
# WP V3 (12): `fits_of_guard` — the word-length guard of the concept implies `Layout.FitsWords`

The concept's guard is `∀ v ∈ x, c · 2^(c e³) · (|x| + v + 1)^c ≤ 2^W`.  For the layout `Ly` (its span is
`temps + 2 + #scalars + #arrays · B`) and `Bfun c' e x = c' · 2^(c' e³) · (|x| + maxEntry x + 1)^c'` the fitting condition
`1 < B`, `B ≤ 2^W`, `span B ≤ 2^W` follows once `c ≥ (temps + 2 + #scalars + #arrays) · c'`.
-/

namespace Lax117284Proofs.Treewidth.Fun.Load

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax117284Proofs.Treewidth.Fun.VM Lax117284Proofs.Treewidth.Fun.VM.Ram

/-- The IMP+ value bound of the concept-level statements (`c'`, exponent parameter `e`). -/
def Bfun (c' e : ℕ) (x : List ℕ) : ℕ := c' * 2 ^ (c' * e ^ 3) * (x.length + maxEntry x + 1) ^ c'

theorem maxEntry_mem : ∀ {x : List ℕ}, x ≠ [] → maxEntry x ∈ x := by
  intro x
  induction x with
  | nil => intro h; exact absurd rfl h
  | cons a l ih =>
    intro _
    by_cases hl : l = []
    · subst hl; simp [maxEntry]
    · have := ih hl
      simp only [maxEntry, List.foldr_cons] at this ⊢
      rcases max_choice a (l.foldr max 0) with h | h
      · rw [h]; simp
      · rw [h]; exact List.mem_cons_of_mem _ this

theorem fits_of_guard {Ly : Layout} {c' c W e : ℕ} {x : List ℕ} (hx : x ≠ []) (hc' : 1 ≤ c')
    (hc : (Ly.temps + 2 + Ly.scalars.length + Ly.arrays.length) * c' ≤ c)
    (hg : ∀ v ∈ x, c * 2 ^ (c * e ^ 3) * (x.length + v + 1) ^ c ≤ 2 ^ W) :
    Ly.FitsWords (Bfun c' e x) W := by
  have hg' := hg _ (maxEntry_mem hx)
  set m := Ly.temps + 2 + Ly.scalars.length + Ly.arrays.length with hm
  set X := x.length + maxEntry x + 1 with hX
  have hxl : 1 ≤ x.length := List.length_pos_iff.mpr hx
  have hX2 : 2 ≤ X := by omega
  have hm1 : 1 ≤ m := by omega
  have hc'c : c' ≤ c := by nlinarith
  have hp1 : 2 ^ (c' * e ^ 3) ≤ 2 ^ (c * e ^ 3) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hc'c)
  have hp2 : X ^ c' ≤ X ^ c := Nat.pow_le_pow_right (by omega) hc'c
  have hB1 : 1 ≤ 2 ^ (c' * e ^ 3) := Nat.one_le_two_pow
  have hXB : X ≤ X ^ c' := Nat.le_self_pow (by omega) X
  set B := Bfun c' e x with hB
  have hBdef : B = c' * 2 ^ (c' * e ^ 3) * X ^ c' := rfl
  have hB2 : 2 ≤ B := by
    rw [hBdef]
    have : 1 * 1 * 2 ≤ c' * 2 ^ (c' * e ^ 3) * X ^ c' :=
      Nat.mul_le_mul (Nat.mul_le_mul hc' hB1) (le_trans hX2 hXB)
    omega
  have hmB : m * B ≤ 2 ^ W := by
    calc m * B = (m * c') * 2 ^ (c' * e ^ 3) * X ^ c' := by rw [hBdef]; ring
      _ ≤ c * 2 ^ (c * e ^ 3) * X ^ c :=
          Nat.mul_le_mul (Nat.mul_le_mul hc hp1) hp2
      _ ≤ 2 ^ W := hg'
  refine ⟨by omega, ?_, ?_⟩
  · calc B ≤ 1 * B := by omega
      _ ≤ m * B := Nat.mul_le_mul_right _ hm1
      _ ≤ 2 ^ W := hmB
  · have : Ly.span B ≤ m * B := by
      unfold Layout.span
      have : Ly.temps + 2 + Ly.scalars.length ≤ (Ly.temps + 2 + Ly.scalars.length) * B := by
        nlinarith
      have e : m * B = (Ly.temps + 2 + Ly.scalars.length) * B + Ly.arrays.length * B := by rw [hm]; ring
      omega
    omega

theorem fitsWords_mono {Ly : Layout} {B B' W : ℕ} (h : Ly.FitsWords B W) (hle : B' ≤ B) (h1 : 1 < B') :
    Ly.FitsWords B' W := by
  refine ⟨h1, le_trans hle h.bound, le_trans ?_ h.span⟩
  unfold Layout.span
  have := Nat.mul_le_mul_left Ly.arrays.length hle
  omega

theorem bimp_arith (S A1 A2 Z2 K n κ κZ : ℕ) (hS : S ≤ A1) (hK : K ≤ A2) (hn : n ≤ Z2) (h1 : 1 ≤ Z2)
    (hκ : κ ≤ κZ) : 2 * (S + 1) + 4 * (K + n + 8) + κ ≤ 2 * A1 + 4 * A2 + 38 * Z2 + κZ := by omega

/-- The constant `c'` for which the IMP+ value bound of `compile_solves` is below `Bfun c'`. -/
def cB (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) : ℕ :=
  2 * (1 + p.c0 * p.c2 ^ p.c3) ^ 2 + 4 * (p.c0 * p.c2 ^ p.c3) + 38 + kappa Δ N main p + 2 * p.c1 + 2 * p.c3 + 2

theorem cB_pos (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) : 1 ≤ cB Δ N main p := by unfold cB; omega

/-- **The IMP+ value bound of `compile_solves` is dominated by the concept's `Bfun`** (with `e = kw`). -/
theorem Bimp_le_Bfun (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) (fmt : Fmt) (x : List ℕ) (h0 : 1 ≤ p.c0)
    (h2 : 1 ≤ p.c2) (hn : 1 ≤ x.length) :
    Bimp Δ N main p fmt x ≤ Bfun (cB Δ N main p) (fmt.kw x) x := by
  set n := x.length with hn'
  set M := maxEntry x with hM
  set X := n + M + 1 with hX
  set e := fmt.kw x with he
  set u := p.c0 * p.c2 ^ p.c3 with hu
  set Q := 2 ^ (p.c1 * e ^ 3) with hQ
  set Z := Q * X ^ (p.c3 + 1) with hZ
  set κ := kappa Δ N main p with hκ
  have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
  have hX1 : 1 ≤ X := by omega
  have hXM : M + 2 ≤ X := by omega
  have hZX : X ≤ Z := by
    calc X ≤ X ^ (p.c3 + 1) := Nat.le_self_pow (by omega) X
      _ = 1 * X ^ (p.c3 + 1) := by ring
      _ ≤ Q * X ^ (p.c3 + 1) := Nat.mul_le_mul_right _ hQ1
  have hR : (n + p.c2) ^ p.c3 ≤ p.c2 ^ p.c3 * X ^ p.c3 := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by nlinarith [Nat.zero_le M]) _
  have hK : Kx p fmt x = p.c0 * Q * (n + p.c2) ^ p.c3 := rfl
  have hKu : Kx p fmt x ≤ u * Z := by
    rw [hK]
    calc p.c0 * Q * (n + p.c2) ^ p.c3 ≤ p.c0 * Q * (p.c2 ^ p.c3 * X ^ p.c3) := Nat.mul_le_mul_left _ hR
      _ = u * (Q * X ^ p.c3) := by rw [hu]; ring
      _ ≤ u * (Q * X ^ (p.c3 + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
  have hMK : M + Kx p fmt x + 2 ≤ (1 + u) * Z := by
    have : (1 + u) * Z = Z + u * Z := by ring
    omega
  have hsq : (M + Kx p fmt x + 2) ^ 2 ≤ (1 + u) ^ 2 * Z ^ 2 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hMK 2
  have hZ1 : 1 ≤ Z := le_trans hX1 hZX
  have hZ2 : Z ≤ Z ^ 2 := by
    calc Z = Z * 1 := by ring
      _ ≤ Z * Z := Nat.mul_le_mul_left _ hZ1
      _ = Z ^ 2 := by ring
  have h3 : n ≤ Z ^ 2 := by omega
  have h4 : 1 ≤ Z ^ 2 := le_trans hZ1 hZ2
  have h5 : Kx p fmt x ≤ u * Z ^ 2 := le_trans hKu (Nat.mul_le_mul_left _ hZ2)
  have h6 : κ ≤ κ * Z ^ 2 := by
    calc κ = κ * 1 := by ring
      _ ≤ κ * Z ^ 2 := Nat.mul_le_mul_left _ h4
  have h7 : Bimp Δ N main p fmt x ≤ (2 * (1 + u) ^ 2 + 4 * u + 38 + κ) * Z ^ 2 := by
    unfold Bimp Bx bexp
    rw [← hM]
    have e : (2 * (1 + u) ^ 2 + 4 * u + 38 + κ) * Z ^ 2 =
        2 * ((1 + u) ^ 2 * Z ^ 2) + 4 * (u * Z ^ 2) + 38 * Z ^ 2 + κ * Z ^ 2 := by ring
    rw [e]
    exact bimp_arith _ _ _ _ _ _ _ _ hsq h5 h3 h4 h6
  have h8 : (2 * (1 + u) ^ 2 + 4 * u + 38 + κ) * Z ^ 2 ≤ Bfun (cB Δ N main p) e x := by
    unfold Bfun
    have hcBe : cB Δ N main p = 2 * (1 + u) ^ 2 + 4 * u + 38 + κ + 2 * p.c1 + 2 * p.c3 + 2 := rfl
    have hcB : 2 * (1 + u) ^ 2 + 4 * u + 38 + κ ≤ cB Δ N main p := by omega
    have hZe : Z ^ 2 = 2 ^ (2 * p.c1 * e ^ 3) * X ^ (2 * p.c3 + 2) := by
      rw [hZ, hQ, mul_pow, ← pow_mul, ← pow_mul]; ring_nf
    have hp1 : 2 ^ (2 * p.c1 * e ^ 3) ≤ 2 ^ (cB Δ N main p * e ^ 3) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
    have hp2 : X ^ (2 * p.c3 + 2) ≤ X ^ (cB Δ N main p) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [hZe]
    calc (2 * (1 + u) ^ 2 + 4 * u + 38 + κ) * (2 ^ (2 * p.c1 * e ^ 3) * X ^ (2 * p.c3 + 2))
        ≤ cB Δ N main p * (2 ^ (cB Δ N main p * e ^ 3) * X ^ (cB Δ N main p)) :=
          Nat.mul_le_mul hcB (Nat.mul_le_mul hp1 hp2)
      _ = cB Δ N main p * 2 ^ (cB Δ N main p * e ^ 3) * X ^ (cB Δ N main p) := by ring
  exact le_trans h7 h8

open Lax808846.Ram Lax808846.RamComputes Lax117284Proofs.Treewidth.Fun.ToVal in
/-- **End-to-end (WP V3 + the guard).**  One machine program `prog` (chosen before `D`, `f`, `w`) computes `f` on `D` in time
`10 κ (Kx + |x| + 1) + 1`, at every word length `w` satisfying the guard
`∀ x ∈ D, ∀ v ∈ x, c · 2^(c · kw³) · (|x| + v + 1)^c ≤ 2^w`, provided the table computes `f` functionally
(`Runs Δ (Bx x) main [toVal x] (toVal (f x)) (Kx x)`, `|f x| ≤ Kx x`). -/
theorem compile_computes (Δ : ℕ → Option Tm) {N : ℕ} (hN : ∀ f, N ≤ f → Δ f = none) (main : ℕ) (fmt : Fmt)
    (p : KP) (h0 : 1 ≤ p.c0) (h1 : 1 ≤ p.c1) (h2 : 1 ≤ p.c2) :
    ∃ (prog : Program) (c : ℕ), ∀ (D : Set (List ℕ)) (f : List ℕ → List ℕ),
      (∀ x ∈ D, fmtLen fmt x = x.length) →
      (∀ x ∈ D, Runs Δ (Bx p fmt x) main [Lax117284Proofs.Treewidth.Fun.ToVal.toVal x] (Lax117284Proofs.Treewidth.Fun.ToVal.toVal (f x)) (Kx p fmt x)) →
      (∀ x ∈ D, (f x).length ≤ Kx p fmt x) →
      ∀ w, (∀ x ∈ D, ∀ v ∈ x, c * 2 ^ (c * (fmt.kw x) ^ 3) * (x.length + v + 1) ^ c ≤ 2 ^ w) →
        ComputesInTime w prog D f (fun x => 10 * kappa Δ N main p * (Kx p fmt x + x.length + 1) + 1) := by
  refine ⟨compileProgram solveLayout (solveCom Δ N main fmt p),
    (solveLayout.temps + 2 + solveLayout.scalars.length + solveLayout.arrays.length) * cB Δ N main p,
    fun D f hfmt hruns hlen w hg => ?_⟩
  have hS := solve_solves Δ hN main fmt p h0 h1 h2 hfmt hruns hlen
  refine Lax808846Proofs.Transfer.computesInTime_of_solves hS (fun x hx => ?_) (fun x hx => ?_)
  · have hx0 : x ≠ [] := by
      intro h; have := two_le_len fmt x (hfmt x hx); rw [h] at this; simp at this
    have hfit := fits_of_guard (Ly := solveLayout) (c' := cB Δ N main p) (e := fmt.kw x) (W := w) hx0
      (cB_pos Δ N main p) le_rfl (hg x hx)
    refine fitsWords_mono hfit (Bimp_le_Bfun Δ N main p fmt x h0 h2 (List.length_pos_iff.mpr hx0)) ?_
    have : 2 ≤ Bx p fmt x := bexp_ge_two _ _
    unfold Bimp; omega
  · have : solveLayout.const = 10 := rfl
    rw [this]; unfold Cimp; rw [Nat.mul_assoc]

end Lax117284Proofs.Treewidth.Fun.Load
