import Lax117284Proofs.Machine.ClMainCost
import Lax117284Proofs.Injectivity
import Lax808846Proofs.Transfer

/-!
The main program solves the problem of the clients: its values stay below `Bx`, and it costs at
most `Kx`.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax808846Proofs.Transfer
open Lax808846.Ram
open Lax117284Proofs.Machine.ClBuild
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Lax117284.InstanceEncoding

/-- What the program answers: `1` for a word whose instance block has a `k`-fair schedule. -/
noncomputable def fAns (x : List ℕ) : List ℕ :=
  open Classical in if (decode x.dropLast).HasKFairSchedule (parameter x) then [1] else [0]

theorem fAns_eq {x : List ℕ} {I : Instance} {k : ℕ} (h : EncodesUniform x I k) :
    fAns x = open Classical in if I.HasKFairSchedule k then [1] else [0] := by
  obtain ⟨y, rfl, hy⟩ := h
  have h1 : (y ++ [k]).dropLast = y := by simp
  have h2 : parameter (y ++ [k]) = k := by simp [parameter]
  unfold fAns
  rw [h1, h2, Lax117284Proofs.Injectivity.decode_eq hy]

variable {P : Program} {c' c1 : ℕ} {g' : ℕ → ℕ}

open Classical Lax117284.ParameterizedComplexity in
open Lax117284.IlpClients (decodeILP ilpClients) in
theorem solves (hc1 : c1 = c' + 1)
    (hOr : ∀ w z, z ∈ ilpClients.Domain → Fits c' w z → ∃ t ≤ c' * g' (z.getD 0 0) * (z.length + 1) ^ c' * (w + 1) ^ c',
      RunsTo w P z [if (decodeILP z).Feasible then 1 else 0] t) :
    Solves (layoutF P c1) (mainCom P c1) UniformInstances fAns (Bx P c1) (Kx P c' g' c1) where
  ok := layout_ok P c1
  inp := by
    rintro x ⟨I, k, hdec⟩ v hv
    exact (bxFacts (P := P) (c1 := c1) hdec (by omega)).hX v hv
  run := by
    rintro x ⟨I, k, hdec⟩
    have hF := bxFacts (P := P) (c1 := c1) hdec (by omega)
    have hn : x.getD 0 0 = I.clients := ClientsWord.x0 hdec
    have hm : x.getD 1 0 = I.days := ClientsWord.x1 hdec
    have hl := ClientsWord.len_eq hdec
    refine ⟨extF P c1 x, ?_⟩
    have hmain := main_core (P := P) (c1 := c1) hdec hF.hL hF.hX hF.hnB hF.h3
      (Kfit P c' g' c1 I + 30) (ClBrute.bruteCost I.days I.clients + 3)
      (fun hc => fitBranch_spec P c' g' c1 hc1 hOr ⟨hdec, hF.hL, hF.hX, by have := zLen_le I.clients; have := hF.hL; omega⟩ hc hF.hbB hF.hw hF.hP hF.hLits)
      (fun _ => bruteBranch_spec hdec hF.h4 hF.hX)
    obtain ⟨σ', hrun, hout⟩ := hmain (initEnv (extF P c1 x) x) ⟨rfl, rfl, fun a => rfl⟩
    refine ⟨σ', hrun.mono (le_of_eq ?_), ?_⟩
    · unfold Kx
      rw [hn, hm]
      rfl
    · rw [hout, fAns_eq hdec]
      by_cases hK : I.HasKFairSchedule k <;> simp [hK]

end Lax117284Proofs.Machine.ClMain
