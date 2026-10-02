import Lax117284Proofs.Treewidth.Fun.A1Arith

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# WP A1 (6): `decompose_run : A2.DecompRun`

The table `finalΔ` (ids `< 800`, `A1Defs`), the entry `fMain = 770` and `C = 2^E` (`E` an abstract natural `≥ 829723`).
For `x = g ++ [k]` with `g` the word of a graph on `Fin n`: `|x| = n² + 2`, `x[0] = n`, `x[n²+1] = k`, the adjacency read
off the word is the graph's (symmetric on `range n`), and `main_runs` (A1Main) with `M = 8 (|x|+1)²`, `Mv = maxEntry x + 3`
gives the run within `cMain`, which `cMain_le` (A1Arith) bounds by `K x - 3`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace A1

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees Lax117284.GraphWords
open Lax117284Proofs.Treewidth.Fun.Load (Fmt Kx Bx maxEntry)
open Lax117284Proofs.Treewidth.Fun.VM.Ram (KP)
open E4 (adjOfWord nOfWord)

/-! ## the admissible inputs -/

theorem d2_len {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ} {k : ℕ} (h : EncodesGraph g G) :
    (g ++ [k]).length = n * n + 2 := by
  simp [h.length_eq]; ring

theorem d2_n {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ} {k : ℕ} (h : EncodesGraph g G) :
    nOfWord (g ++ [k]) = n := by
  have h1 := h.head_eq
  have hl : 0 < g.length := by rw [h.length_eq]; omega
  unfold nOfWord
  rw [List.getD_append _ _ _ _ hl]
  exact h1

theorem d2_k {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ} {k : ℕ} (h : EncodesGraph g G) :
    Fmt.graphK.kw (g ++ [k]) = k := by
  have hn := d2_n (k := k) h
  have h1 : (g ++ [k]).getD 0 0 = n := hn
  unfold Fmt.kw Fmt.off
  rw [h1]
  simp only
  rw [List.getD_eq_getElem?_getD]
  have : (n * n + 1) = g.length := by rw [h.length_eq]; ring
  rw [this]
  simp

theorem d2_adj {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ} {k : ℕ} (h : EncodesGraph g G) :
    ∀ u v : Fin n, adjOfWord (g ++ [k]) u.val v.val = true ↔ G.Adj u v ∨ G.Adj v u := by
  intro u v
  have hn := d2_n (k := k) h
  have hidx : 1 + u.val * n + v.val < g.length := by
    rw [h.length_eq]
    have hu := u.2
    have hv := v.2
    have : (u.val + 1) * n ≤ n * n := Nat.mul_le_mul_right _ hu
    nlinarith
  have hget : (g ++ [k]).getD (1 + u.val * n + v.val) 0 = g.getD (1 + u.val * n + v.val) 0 :=
    List.getD_append _ _ _ _ hidx
  have hadj := h.adj_eq u v
  unfold adjOfWord
  rw [hn, hget, hadj]
  by_cases hA : G.Adj u v
  · simp [hA, u.2, v.2]
  · have : G.Adj u v ↔ G.Adj v u := ⟨fun h => h.symm, fun h => h.symm⟩
    simp [hA, u.2, v.2]
    exact fun hh => hA (this.2 hh)

theorem le_maxEntry {x : List ℕ} {a : ℕ} (h : a ∈ x) : a ≤ maxEntry x :=
  (mx_foldr_max_le (y := x) (M := maxEntry x)).1 le_rfl a h

/-! ## the theorem -/

theorem decompose_run_E (E : ℕ) (hE : 829723 ≤ E) :
    ∃ (Δ : ℕ → Option Tm) (N main C : ℕ), 1 ≤ C ∧ (∀ f, N ≤ f → Δ f = none) ∧
      ∀ x ∈ A2.D2, Runs Δ (Bx (A2.pC C) Fmt.graphK x) main [toVal x] (toVal (A2.outWord x))
          (Kx (A2.pC C) Fmt.graphK x) ∧
        (A2.outWord x).length ≤ Kx (A2.pC C) Fmt.graphK x := by
  refine ⟨finalΔ, 800, fMain, 2 ^ E, Nat.one_le_two_pow, fun f hf => finalΔ_none hf, ?_⟩
  rintro x ⟨n, G, g, k, rfl, henc⟩
  have hxl := d2_len (k := k) henc
  have hnw := d2_n (k := k) henc
  have hkw := d2_k (k := k) henc
  have hadj := d2_adj (k := k) henc
  have hs : (adjOfWord (g ++ [k])).SymmOn (Finset.range (nOfWord (g ++ [k]))) := by
    rw [hnw]; exact symmOn_of_encodes hadj
  set x := g ++ [k] with hx
  have hnn : n ≤ x.length := by rw [hxl]; nlinarith
  -- the numbers
  have hK : Kx (A2.pC (2 ^ E)) Fmt.graphK x = 2 ^ E * 2 ^ (2 ^ E * k ^ 3) * (x.length + 1) ^ (2 ^ E) := by
    unfold Kx A2.pC KP.k
    rw [hkw]
  have hBx : Bx (A2.pC (2 ^ E)) Fmt.graphK x =
      (maxEntry x + Kx (A2.pC (2 ^ E)) Fmt.graphK x + 2) ^ 2 + 1 := rfl
  set K := Kx (A2.pC (2 ^ E)) Fmt.graphK x with hKdef
  set M := 8 * ((x.length + 1) * (x.length + 1)) with hM
  set Cm := cMain n x.length M k with hCm
  have hCmK : Cm + 3 ≤ K := by rw [hK]; exact cMain_le E n x.length k hE hnn
  have hCm28 : 28 * x.length ≤ Cm := by rw [hCm]; unfold cMain; omega
  have hmem_n : n ≤ maxEntry x := by
    have : n ∈ x := by
      have h0 : x.getD 0 0 = n := hnw
      have : 0 < x.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this] at h0
      simp only [Option.getD_some] at h0
      rw [← h0]; exact List.getElem_mem _
    exact le_maxEntry this
  have hmem_k : k ≤ maxEntry x := le_maxEntry (by simp [hx])
  have hxM : x.length ≤ M := by rw [hM]; nlinarith
  have hMs : 8 * ((nOfWord x + 1) * (nOfWord x + 1)) ≤ M := by
    rw [hnw, hM]
    have : (n + 1) * (n + 1) ≤ (x.length + 1) * (x.length + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hnM : nOfWord x + 3 ≤ M := by
    rw [hnw, hM]; nlinarith
  have hkB : k + 2 < (maxEntry x + K + 2) ^ 2 + 1 := by
    have : maxEntry x + K + 2 ≤ (maxEntry x + K + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hnnB : nOfWord x * nOfWord x + 1 < (maxEntry x + K + 2) ^ 2 + 1 := by
    have : maxEntry x + K + 2 ≤ (maxEntry x + K + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    rw [hnw]; nlinarith
  have hBfit : (maxEntry x + 3 + Cm + 2) ^ 2 < (maxEntry x + K + 2) ^ 2 + 1 := by
    have : (maxEntry x + 3 + Cm + 2) ^ 2 ≤ (maxEntry x + K + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hCm' : cMain (nOfWord x) x.length M k ≤ Cm := by rw [hnw]
  have hmain := main_runs ext6_final ext6a_final ext_a1_final ((maxEntry x + K + 2) ^ 2 + 1) x k M
    (maxEntry x + 3) Cm hkw.symm hs hxM hMs hnM (by rw [hnw]; omega) hkB hnnB hCm' hBfit
  refine ⟨?_, ?_⟩
  · rw [hBx]
    exact hmain.mono (by omega)
  · -- the length of the output
    unfold A2.outWord
    rw [hkw]
    have hd := (decomposeC_correct_final (adjOfWord x) (Finset.range n) (by rw [hnw] at hs; exact hs) k n
      (Finset.Subset.refl _)).2
    have hnx : x.getD 0 0 = n := hnw
    rw [hnx]
    have hsq : 200 * ((n + 2) * (n + 2)) ^ 2 + 2000 ≤ Cm := by rw [hCm]; unfold cMain; omega
    rcases hr : decomposeC (adjOfWord x) k n with _ | t
    · simp only [List.length_cons, List.length_nil]; omega
    · have hsize := (hd t hr).2
      simp only [List.length_cons, encode_length]
      have h1 : t.size * t.size ≤ (n + 2) * (n + 2) * ((n + 2) * (n + 2)) := Nat.mul_le_mul hsize hsize
      have h2 : ((n + 2) * (n + 2)) ^ 2 = (n + 2) * (n + 2) * ((n + 2) * (n + 2)) := by ring
      have h3 : t.size ≤ t.size * t.size := Nat.le_mul_self t.size
      omega

/-- **`decompose_run`**: the top-level functional program computes `outWord` within `K x` steps at the tag bound `Bx`. -/
theorem decompose_run : A2.DecompRun := by
  obtain ⟨E, hE⟩ : ∃ E, 829723 ≤ E := ⟨_, le_refl _⟩
  exact decompose_run_E E hE

end A1
end Lax117284Proofs.Treewidth.Fun
