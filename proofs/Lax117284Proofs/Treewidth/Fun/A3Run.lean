import Lax117284Proofs.Treewidth.Fun.A3Facts

/-!
# WP A3 (4): `improveRun_of` — the dispatcher over the exact algorithm's table

`extΔ Δ N main` adds three functions at the fresh ids `N` (dispatcher), `N + 1` (take), `N + 2` (drop) to the table of `DecompRun`
(ids `< N`), and `improveRun_of h : ImproveRun` runs the dispatcher: for `l ≤ k` it answers `1 :: D`, otherwise it calls the
old `main` on the prefix `g ++ [k]` (`take (n² + 2) x`), weakened to the larger tag bound `Bx (pC1 C) graphKLD x`.
-/

namespace Lax117284Proofs.Treewidth.Fun.A3

open Lax117284Proofs.Treewidth.Fun Lax117284Proofs.Treewidth.Fun.Load Lax117284Proofs.Treewidth.Fun.VM.Ram Lax117284.GraphWords ToVal

/-- The extended table. -/
def extΔ (Δ : ℕ → Option Tm) (N main : ℕ) : ℕ → Option Tm := fun f =>
  if f = N then some (dispTm (N + 1) (N + 2) main)
  else if f = N + 1 then some (takeTmAt (N + 1))
  else if f = N + 2 then some (dropTmAt (N + 2))
  else Δ f

theorem extΔ_ext {Δ : ℕ → Option Tm} {N : ℕ} (main : ℕ) (hN : ∀ f, N ≤ f → Δ f = none) : Ext Δ (extΔ Δ N main) := by
  intro f b hf
  have hf' : f < N := by
    by_contra hc
    rw [hN f (by omega)] at hf
    cases hf
  unfold extΔ
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact hf

theorem extΔ_none {Δ : ℕ → Option Tm} {N : ℕ} (main : ℕ) (hN : ∀ f, N ≤ f → Δ f = none) :
    ∀ f, N + 3 ≤ f → extΔ Δ N main f = none := by
  intro f hf
  unfold extΔ
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact hN f (by omega)

theorem extΔ_d (Δ : ℕ → Option Tm) (N main : ℕ) : extΔ Δ N main N = some (dispTm (N + 1) (N + 2) main) := by
  simp [extΔ]

theorem extΔ_tk (Δ : ℕ → Option Tm) (N main : ℕ) : extΔ Δ N main (N + 1) = some (takeTmAt (N + 1)) := by
  simp [extΔ]

theorem extΔ_dr (Δ : ℕ → Option Tm) (N main : ℕ) : extΔ Δ N main (N + 2) = some (dropTmAt (N + 2)) := by
  simp [extΔ]

section wrappers
variable {Δ' : ℕ → Option Tm} {B tk dr mn d : ℕ}

theorem disp_true_x (hd : Δ' d = some (dispTm tk dr mn)) (hdr : Δ' dr = some (dropTmAt dr)) {x : List ℕ} {n : ℕ}
    {xs : List ℕ} (hx : x = n :: xs) (hlen : n * n + 3 ≤ x.length) (hB : n * n + 2 < B)
    (hle : x.getD (n * n + 2) 0 ≤ x.getD (n * n + 1) 0) :
    Runs Δ' B d [toVal x] (toVal (1 :: x.drop (n * n + 3))) (20 * x.length + 60) := by
  subst hx
  exact disp_runs_true hd hdr n xs hlen hB hle

theorem disp_false_x (hd : Δ' d = some (dispTm tk dr mn)) (hdr : Δ' dr = some (dropTmAt dr))
    (htk : Δ' tk = some (takeTmAt tk)) {x : List ℕ} {n : ℕ} {xs : List ℕ} (hx : x = n :: xs)
    (hlen : n * n + 3 ≤ x.length) (hB : n * n + 2 < B)
    (hlt : x.getD (n * n + 1) 0 < x.getD (n * n + 2) 0) {v : Val} {cm : ℕ}
    (hmain : Runs Δ' B mn [toVal (x.take (n * n + 2))] v cm) :
    Runs Δ' B d [toVal x] v (cm + 40 * x.length + 100) := by
  subst hx
  exact disp_runs_false hd hdr htk n xs hlen hB hlt hmain

end wrappers

theorem improveRun_of (h : A2.DecompRun) : ImproveRun := by
  obtain ⟨Δ, N, main, C, hC, hN, hrun⟩ := h
  refine ⟨extΔ Δ N main, N + 3, N, C, hC, extΔ_none main hN, ?_⟩
  rintro x ⟨n, G, g, k, l, D, rfl, henc, hD⟩
  have hd := extΔ_d Δ N main
  have htk := extΔ_tk Δ N main
  have hdr := extΔ_dr Δ N main
  set x := g ++ [k, l] ++ D with hx
  have hlenx : x.length = n * n + 3 + D.length := facts_length henc k l D
  have hkw := facts_kw henc k l D
  have hK : Kx (pC1 C) Fmt.graphKLD x = (C + 100) * 2 ^ (C * l ^ 3) * (x.length + 1) ^ C := Kx_eq hkw
  have hS := S_ge (C := C) (l := l) (m := x.length) hC
  have hS' : (C + 100) * 2 ^ (C * l ^ 3) * (x.length + 1) ^ C
      = (C + 100) * (2 ^ (C * l ^ 3) * (x.length + 1) ^ C) := by ring
  obtain ⟨xs, hxs⟩ : ∃ xs, x = n :: xs := by
    have h0 : 0 < g.length := by rw [henc.length_eq]; omega
    obtain ⟨a, gs, hg⟩ : ∃ a gs, g = a :: gs := by
      cases g with
      | nil => simp at h0
      | cons a gs => exact ⟨a, gs, rfl⟩
    refine ⟨gs ++ [k, l] ++ D, ?_⟩
    have := henc.head_eq
    rw [hg] at this
    simp only [List.getD_cons_zero] at this
    rw [hx, hg, this]
    simp
  have hhead : x.getD 0 0 = n := facts_head henc k l D
  set K := Kx (pC1 C) Fmt.graphKLD x with hKdef
  set B := Bx (pC1 C) Fmt.graphKLD x with hBdef
  have hnM : n ≤ maxEntry x := by
    apply le_maxEntry
    rw [hxs]; simp
  have hB2 : n * n + 2 < B := by
    rw [hBdef]; unfold Bx bexp
    have h1 : n * n ≤ maxEntry x * maxEntry x := Nat.mul_le_mul hnM hnM
    nlinarith [Nat.zero_le K, Nat.zero_le (maxEntry x)]
  have hlen3 : n * n + 3 ≤ x.length := by omega
  have hxK : x.length + 1 ≤ K := by rw [hK, hS']; nlinarith
  rw [outWord1_eq henc k l D]
  by_cases hle : l ≤ k
  · rw [if_pos hle]
    have hle' : x.getD (n * n + 2) 0 ≤ x.getD (n * n + 1) 0 := by
      rw [facts_l henc, facts_k henc]; exact hle
    have hr := disp_true_x hd hdr hxs hlen3 hB2 hle'
    rw [facts_drop henc] at hr
    have hcost : 20 * x.length + 60 ≤ K := by rw [hK, hS']; nlinarith
    refine ⟨Runs.mono hr hcost, ?_⟩
    simp only [List.length_cons]
    omega
  · rw [if_neg hle]
    have hlt : x.getD (n * n + 1) 0 < x.getD (n * n + 2) 0 := by
      rw [facts_l henc, facts_k henc]; omega
    have hD2 : g ++ [k] ∈ A2.D2 := A2.mem_D2 henc k
    obtain ⟨hr0, hl0⟩ := hrun (g ++ [k]) hD2
    have hKy : Kx (A2.pC C) Fmt.graphK (g ++ [k]) = C * 2 ^ (C * k ^ 3) * ((g ++ [k]).length + 1) ^ C := by
      unfold Kx A2.pC KP.k
      rw [A2.kw_graphK henc k]
    have hkl : k ≤ l := by omega
    have hly : (g ++ [k]).length ≤ x.length := by
      rw [hlenx, List.length_append, henc.length_eq]; simp; omega
    have hKyle := Ky_add (C := C) hkl hly hC
    rw [← hKy, ← hK] at hKyle
    have hKB : Kx (A2.pC C) Fmt.graphK (g ++ [k]) ≤ K := by omega
    have hBB : Bx (A2.pC C) Fmt.graphK (g ++ [k]) ≤ B :=
      Bx_le (fun v hv => le_maxEntry (by rw [hx]; simp at hv ⊢; tauto)) hKB
    have hmain : Runs (extΔ Δ N main) B main [toVal (x.take (n * n + 2))]
        (toVal (A2.outWord (g ++ [k]))) (Kx (A2.pC C) Fmt.graphK (g ++ [k])) := by
      rw [hx, facts_take henc]
      exact Runs.weaken (extΔ_ext main hN) hBB hr0
    have hr := disp_false_x hd hdr htk hxs hlen3 hB2 hlt hmain
    have hcost : Kx (A2.pC C) Fmt.graphK (g ++ [k]) + 40 * x.length + 100 ≤ K := by omega
    exact ⟨Runs.mono hr hcost, le_trans hl0 hKB⟩

end Lax117284Proofs.Treewidth.Fun.A3
