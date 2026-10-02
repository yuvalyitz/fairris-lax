import Lax117284Proofs.Treewidth.Fun.A3Disp

/-!
# WP A3 (3): the words `x = g ++ [k, l] ++ D`, the output word, and the numeric facts

`facts_*` read `n, k, l, D, g ++ [k]` off `x`; `outWord1_eq` evaluates `outWord1`; `maxEntry_*` and the `Kx`-monotonicity lemmas
compare the two runs (`Bx (pC C) graphK y` of the exact algorithm against `Bx (pC1 C) graphKLD x` of the dispatcher).
-/

namespace Lax117284Proofs.Treewidth.Fun.A3

open Lax117284Proofs.Treewidth.Fun Lax117284Proofs.Treewidth.Fun.Load Lax117284Proofs.Treewidth.Fun.VM.Ram Lax117284.GraphWords ToVal

section words

variable {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ}

theorem facts_head (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) : (g ++ [k, l] ++ D).getD 0 0 = n := by
  have h0 : 0 < g.length := by rw [henc.length_eq]; omega
  rw [List.append_assoc, List.getD_append _ _ _ _ h0]
  exact henc.head_eq

theorem facts_k (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) : (g ++ [k, l] ++ D).getD (n * n + 1) 0 = k := by
  have hg := henc.length_eq
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), hg]
  have : n * n + 1 - (1 + n * n) = 0 := by omega
  rw [this]; rfl

theorem facts_l (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) : (g ++ [k, l] ++ D).getD (n * n + 2) 0 = l := by
  have hg := henc.length_eq
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), hg]
  have : n * n + 2 - (1 + n * n) = 1 := by omega
  rw [this]; rfl

theorem facts_drop (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) : (g ++ [k, l] ++ D).drop (n * n + 3) = D := by
  have hg := henc.length_eq
  apply List.drop_left'
  simp [hg]; omega

theorem facts_take (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) : (g ++ [k, l] ++ D).take (n * n + 2) = g ++ [k] := by
  have hg := henc.length_eq
  have : g ++ [k, l] ++ D = (g ++ [k]) ++ ([l] ++ D) := by simp
  rw [this]
  apply List.take_left'
  simp [hg]; omega

theorem facts_length (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) :
    (g ++ [k, l] ++ D).length = n * n + 3 + D.length := by
  have hg := henc.length_eq
  simp [hg]; omega

theorem outWord1_eq (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) :
    outWord1 (g ++ [k, l] ++ D) = if l ≤ k then 1 :: D else A2.outWord (g ++ [k]) := by
  unfold outWord1
  rw [facts_head henc, facts_k henc, facts_l henc, facts_drop henc, facts_take henc]

theorem facts_kw (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) : Fmt.graphKLD.kw (g ++ [k, l] ++ D) = l := by
  unfold Fmt.kw
  rw [facts_head henc]
  exact facts_l henc k l D

theorem facts_fmtLen (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) (hD : D.length = 1 + 3 * D.getD 0 0) :
    fmtLen Fmt.graphKLD (g ++ [k, l] ++ D) = (g ++ [k, l] ++ D).length := by
  have hg := henc.length_eq
  have h1 : nOfWord (g ++ [k, l] ++ D) = n := facts_head henc k l D
  have h2 : (g ++ [k, l] ++ D).getD (1 + n * n + 2) 0 = D.getD 0 0 := by
    rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), hg]
    have : 1 + n * n + 2 - (1 + n * n) = 2 := by omega
    rw [this]
    simp [List.getD_cons_succ]
  show 1 + nOfWord (g ++ [k, l] ++ D) * nOfWord (g ++ [k, l] ++ D) + 2 + 1
      + 3 * (g ++ [k, l] ++ D).getD (1 + nOfWord (g ++ [k, l] ++ D) * nOfWord (g ++ [k, l] ++ D) + 2) 0 = _
  rw [h1, h2, facts_length henc k l D]
  omega

end words

/-! ### maximal entries -/

theorem le_maxEntry {x : List ℕ} {v : ℕ} (h : v ∈ x) : v ≤ maxEntry x := by
  induction x with
  | nil => simp at h
  | cons a l ih =>
    simp only [maxEntry, List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem maxEntry_le {y : List ℕ} {M : ℕ} (h : ∀ v ∈ y, v ≤ M) : maxEntry y ≤ M := by
  induction y with
  | nil => simp [maxEntry]
  | cons a l ih =>
    simp only [maxEntry, List.foldr_cons]
    exact max_le (h a (List.mem_cons_self ..)) (ih (fun v hv => h v (List.mem_cons_of_mem _ hv)))

theorem Bx_le {p p' : KP} {fmt fmt' : Fmt} {y x : List ℕ} (hM : ∀ v ∈ y, v ≤ maxEntry x)
    (hK : Kx p fmt y ≤ Kx p' fmt' x) : Bx p fmt y ≤ Bx p' fmt' x := by
  unfold Bx bexp
  have := maxEntry_le hM
  have h2 : maxEntry y + Kx p fmt y + 2 ≤ maxEntry x + Kx p' fmt' x + 2 := by omega
  have := Nat.pow_le_pow_left h2 2
  omega

/-- `Kx` of the dispatcher: `(C + 100) · 2^(C·l³) · (|x| + 1)^C`. -/
theorem Kx_eq {x : List ℕ} {l C : ℕ} (hkw : Fmt.graphKLD.kw x = l) :
    Kx (pC1 C) Fmt.graphKLD x = (C + 100) * 2 ^ (C * l ^ 3) * (x.length + 1) ^ C := by
  unfold Kx pC1 KP.k
  rw [hkw]

theorem S_ge {C l m : ℕ} (hC : 1 ≤ C) : m + 1 ≤ 2 ^ (C * l ^ 3) * (m + 1) ^ C := by
  have h1 : 1 ≤ 2 ^ (C * l ^ 3) := Nat.one_le_two_pow
  calc m + 1 ≤ (m + 1) ^ C := Nat.le_self_pow (by omega) _
    _ = 1 * (m + 1) ^ C := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ h1

/-- the exact algorithm's cost bound on the prefix `g ++ [k]` is below the dispatcher's, plus `100 (|x| + 1)`. -/
theorem Ky_add {C k l ly lx : ℕ} (hkl : k ≤ l) (hl : ly ≤ lx) (hC : 1 ≤ C) :
    C * 2 ^ (C * k ^ 3) * (ly + 1) ^ C + 100 * (lx + 1) ≤ (C + 100) * 2 ^ (C * l ^ 3) * (lx + 1) ^ C := by
  set S := 2 ^ (C * l ^ 3) * (lx + 1) ^ C with hS
  have h1 : C * 2 ^ (C * k ^ 3) * (ly + 1) ^ C ≤ C * S := by
    rw [hS, ← mul_assoc]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hkl 3))))
      (Nat.pow_le_pow_left (by omega) _)
  have h2 : lx + 1 ≤ S := S_ge hC
  have : (C + 100) * 2 ^ (C * l ^ 3) * (lx + 1) ^ C = (C + 100) * S := by rw [hS]; ring
  rw [this]
  nlinarith

end Lax117284Proofs.Treewidth.Fun.A3
