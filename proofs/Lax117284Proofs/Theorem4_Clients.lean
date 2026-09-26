import Lax117284.Theorem4
import Lax117284.IlpClients
import Lax117284Proofs.Machine.ClMainTime
import Lax117284Proofs.Machine.IlpFinal

/-!
Theorem 4, third bullet: the problem is fixed-parameter tractable in the number of clients.
-/

namespace Lax117284Proofs.Theorem4Clients

open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes Lax808846Proofs.Compile
open Lax117284.InstanceEncoding Lax117284.ParameterizedComplexity Lax117284.Scheduling
open Lax117284Proofs.Machine.ClMain

theorem param_eq {x : List ℕ} (hx : x ∈ UniformInstances) :
    Lax117284.Theorem4.byClients.param x = x.getD 0 0 := by
  obtain ⟨I, k, hdec⟩ := hx
  have hx0 := ClientsWord.x0 hdec
  obtain ⟨y, rfl, hy⟩ := hdec
  have h1 : (y ++ [k]).dropLast = y := by simp
  show (decode (y ++ [k]).dropLast).clients = _
  rw [h1, Lax117284Proofs.Injectivity.decode_eq hy]
  exact hx0.symm

open Classical in
open Lax117284.IlpClients (decodeILP ilpClients) in
/--
---
conclusion: Lax117284.Theorem4.fpt_byClients
---
The problem is decided by a word RAM program that reads the word, with `n` clients and `m` days,
and tests whether it is at least `2 ^ (2 n² + n + 3) + 2` long, by doubling a counter held at the
length. If it is, and the fairness parameter is at most `m`, the program writes the word of an
integer program with `2 ^ (n² + n) + n` variables: one per pair of a type of day (its conflict
relation) and a set of clients, which the pair says run together on the days of that type, and one
slack per client; one constraint fixes, for each type, the number of days of that type, and one
says, for each client, that the days it is not served on are at most `m - k`. It then chooses a
word length `w'` for which that word fits, and runs the program that solves the integer programs of
the family (`IlpClients.ilpClients_fpt`, proved) on it at
that word length, by an interpreter of word RAM programs written in the IMP+ language, the memory
of the interpreted machine being an array of `2 ^ w'` cells. The program is read as data, so it is
the same for every word length. If the word is too short, the number of schedules is at most a
function of `n` alone, and the program enumerates them. A parameter above `m` is answered `no`
at once when there is a client. No result is cited.
-/
theorem fpt_byClients : FPT Lax117284.Theorem4.byClients := by
  obtain ⟨P, c', g', hD⟩ := Lax117284Proofs.Machine.Ilp.ilpClients_fpt_proved
  set c1 := c' + 1 with hc1def
  have hc1 : c1 = c' + 1 := rfl
  have hc1' : 1 ≤ c1 := by omega
  have hOr : ∀ w z, z ∈ ilpClients.Domain → Fits c' w z → ∃ t ≤ c' * g' (z.getD 0 0) * (z.length + 1) ^ c' * (w + 1) ^ c',
      RunsTo w P z [if (decodeILP z).Feasible then 1 else 0] t := by
    intro w z hd hz
    obtain ⟨t, ht, hr⟩ := hD w z ⟨hd, hz⟩
    have ht' : t ≤ c' * g' (z.getD 0 0) * (z.length + 1) ^ c' := ht
    have hle : c' * g' (z.getD 0 0) * (z.length + 1) ^ c' ≤
        c' * g' (z.getD 0 0) * (z.length + 1) ^ c' * (w + 1) ^ c' :=
      Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos _) _)
    refine ⟨t, ht'.trans hle, ?_⟩
    by_cases hF : (decodeILP z).Feasible
    · have : ilpClients.Yes z := hF
      simp only [this, if_true] at hr
      simpa [hF] using hr
    · have : ¬ ilpClients.Yes z := hF
      simp only [this, if_false] at hr
      simpa [hF] using hr
  have hsol := solves (P := P) (c' := c') (c1 := c1) (g' := g') hc1 hOr
  set S := (layoutF P c1).scalars.length with hS
  set c := 2 + c' + c' * c' + (10 * C0 P c1 + S + 14) with hcdef
  refine ⟨compileProgram (layoutF P c1) (mainCom P c1), c, Gt P c' g' c1, fun w => ?_⟩
  have hs : Solves (layoutF P c1) (mainCom P c1)
      {x | x ∈ Lax117284.Theorem4.byClients.Domain ∧ Fits c w x} fAns (Bx P c1) (Kx P c' g' c1) :=
    ⟨hsol.ok, fun x hx => hsol.inp x hx.1, fun x hx => hsol.run x hx.1⟩
  refine computesInTime_of_solves hs ?_ ?_
  · rintro x ⟨hx, hf⟩
    exact fitsWords_of hc1' hx hf (by omega) (by omega) (by omega)
  · rintro x ⟨hx, hf⟩
    rw [param_eq hx]
    have := time_le (P := P) (c' := c') (c1 := c1) (g' := g') hc1 hx (c := c) (by omega) (by omega) (by omega)
    show 10 * Kx P c' g' c1 x + 1 ≤ _
    exact this

end Lax117284Proofs.Theorem4Clients
