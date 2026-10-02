import Lax117284Proofs.Treewidth.Fun.A2Stmt
import Lax117284.BodlaenderGeneral

/-!
# WP A2 (1): correctness and arithmetic for `niceDecomposition_computable`

* `outWord_correct`  : the output word of the exact algorithm (`decomposeC`) on `g ++ [k]` is `[0]` when the graph has no tree
  decomposition of width `k` and `1 :: D` with `NiceDecomposition G k D` otherwise (`Wrap/ImproveC.decomposeC_words_final`);
* `kw_graphK`, `fmtLen_graphK` : the format facts about `x = g ++ [k]`;
* `guard_mono`, `time_arith` : the constant chase between the compiler's guard/time (`c₀`, `κ`) and the concept's (`c`).
-/

namespace Lax117284Proofs.Treewidth.Fun.A2

open Lax117284Proofs.Treewidth.Fun Lax117284Proofs.Treewidth.Fun.Load Lax117284.GraphWords ToVal

section format

variable {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ}

theorem head_getD (henc : EncodesGraph g G) (k : ℕ) : (g ++ [k]).getD 0 0 = n := by
  have h0 : 0 < g.length := by rw [henc.length_eq]; omega
  rw [List.getD_append _ _ _ _ h0]
  exact henc.head_eq

theorem getD_g (henc : EncodesGraph g G) (k i : ℕ) (hi : i < 1 + n * n) : (g ++ [k]).getD i 0 = g.getD i 0 := by
  apply List.getD_append
  rw [henc.length_eq]; exact hi

theorem kw_graphK (henc : EncodesGraph g G) (k : ℕ) : Fmt.graphK.kw (g ++ [k]) = k := by
  unfold Fmt.kw
  rw [head_getD henc k]
  have : (g ++ [k]).getD (n * n + Fmt.graphK.off) 0 = k := by
    show (g ++ [k]).getD (n * n + 1) 0 = k
    rw [List.getD_append_right _ _ _ _ (by rw [henc.length_eq]; omega)]
    rw [henc.length_eq]
    have : n * n + 1 - (1 + n * n) = 0 := by omega
    rw [this]; rfl
  exact this

theorem fmtLen_graphK (henc : EncodesGraph g G) (k : ℕ) : fmtLen Fmt.graphK (g ++ [k]) = (g ++ [k]).length := by
  show nOfWord (g ++ [k]) * nOfWord (g ++ [k]) + 2 = _
  have : nOfWord (g ++ [k]) = n := head_getD henc k
  rw [this, List.length_append, henc.length_eq]
  simp; omega

theorem mem_D2 (henc : EncodesGraph g G) (k : ℕ) : g ++ [k] ∈ D2 := ⟨n, G, g, k, rfl, henc⟩

open Classical in
theorem hadj_of_encodes (henc : EncodesGraph g G) (k : ℕ) :
    ∀ u v : Fin n, E4.adjOfWord (g ++ [k]) u.val v.val = true ↔ G.Adj u v ∨ G.Adj v u := by
  intro u v
  have hu := u.isLt
  have hv := v.isLt
  have hlt : 1 + u.val * n + v.val < 1 + n * n := by
    have : u.val * n + v.val < n * n := by
      have h1 : u.val * n + n ≤ n * n := by nlinarith
      omega
    omega
  have hn : E4.nOfWord (g ++ [k]) = n := head_getD henc k
  have e := henc.adj_eq u v
  have e2 : (g ++ [k]).getD (1 + u.val * n + v.val) 0 = if G.Adj u v then 1 else 0 := by
    rw [getD_g henc k _ hlt]; exact e
  simp only [E4.adjOfWord, hn, decide_eq_true_eq]
  rw [e2]
  constructor
  · rintro ⟨-, -, h⟩
    by_cases hA : G.Adj u v
    · exact Or.inl hA
    · simp [hA] at h
  · rintro (h | h)
    · exact ⟨hu, hv, by simp [h]⟩
    · exact ⟨hu, hv, by simp [h.symm]⟩

/-- **Correctness of the output word.** -/
theorem outWord_correct (henc : EncodesGraph g G) (k : ℕ) :
    (outWord (g ++ [k]) = [0] ∧ ¬ Lax228581.Treewidth.HasTreewidthAtMost G k) ∨
      ∃ D, outWord (g ++ [k]) = 1 :: D ∧ NiceDecomposition G k D := by
  have hadj := hadj_of_encodes henc k
  obtain ⟨h1, h2⟩ := Lax117284Proofs.Treewidth.Chars.decomposeC_words_final G (E4.adjOfWord (g ++ [k])) hadj k
  unfold outWord
  rw [kw_graphK henc k, head_getD henc k]
  cases hd : Lax117284Proofs.Treewidth.Chars.decomposeC (E4.adjOfWord (g ++ [k])) k n with
  | none =>
    left
    exact ⟨rfl, h1.1 hd⟩
  | some t =>
    right
    exact ⟨t.encode, rfl, h2 t hd⟩

end format

section arith

/-- the compiler's guard follows from the concept's when `c₀ ≤ c`. -/
theorem guard_mono {c₀ c e Y W : ℕ} (hc : c₀ ≤ c) (hY : 1 ≤ Y)
    (h : c * 2 ^ (c * e ^ 3) * Y ^ c ≤ 2 ^ W) : c₀ * 2 ^ (c₀ * e ^ 3) * Y ^ c₀ ≤ 2 ^ W := by
  refine le_trans ?_ h
  exact Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hc)))
    (Nat.pow_le_pow_right hY hc)

/-- the compiler's time bound `10 κ (K + |x| + 1) + 1` is below the concept's, `K = C₀ · 2^(C₁ e³) · X^C₃`. -/
theorem time_arith {κ C₀ C₁ C₃ e X X' c : ℕ} (hX : 1 ≤ X) (hXX : X ≤ X') (h3 : 1 ≤ C₃) (h1 : C₁ ≤ c) (h3c : C₃ ≤ c)
    (hc : 10 * κ * (C₀ + 1) + 1 ≤ c) :
    10 * κ * (C₀ * 2 ^ (C₁ * e ^ 3) * X ^ C₃ + X) + 1 ≤ c * 2 ^ (c * e ^ 3) * X' ^ c := by
  set S := 2 ^ (C₁ * e ^ 3) * X ^ C₃ with hS
  have hXS : X ≤ S := by
    have h1' : 1 ≤ 2 ^ (C₁ * e ^ 3) := Nat.one_le_two_pow
    calc X ≤ X ^ C₃ := Nat.le_self_pow (by omega) X
      _ = 1 * X ^ C₃ := by ring
      _ ≤ S := Nat.mul_le_mul_right _ h1'
  have hS1 : 1 ≤ S := le_trans hX hXS
  have e1 : C₀ * 2 ^ (C₁ * e ^ 3) * X ^ C₃ = C₀ * S := by rw [hS]; ring
  rw [e1]
  have e2 : 10 * κ * (C₀ * S + X) + 1 ≤ (10 * κ * (C₀ + 1) + 1) * S := by
    have : 10 * κ * (C₀ * S + X) ≤ 10 * κ * ((C₀ + 1) * S) := Nat.mul_le_mul_left _ (by nlinarith)
    nlinarith
  have e3 : S ≤ 2 ^ (c * e ^ 3) * X' ^ c :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h1))
      (le_trans (Nat.pow_le_pow_left hXX _) (Nat.pow_le_pow_right (by omega) h3c))
  calc 10 * κ * (C₀ * S + X) + 1 ≤ (10 * κ * (C₀ + 1) + 1) * S := e2
    _ ≤ c * S := Nat.mul_le_mul_right _ hc
    _ ≤ c * (2 ^ (c * e ^ 3) * X' ^ c) := Nat.mul_le_mul_left _ e3
    _ = c * 2 ^ (c * e ^ 3) * X' ^ c := by ring

end arith

end Lax117284Proofs.Treewidth.Fun.A2
