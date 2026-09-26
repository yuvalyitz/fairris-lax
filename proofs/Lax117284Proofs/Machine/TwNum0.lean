import Lax117284Proofs.Machine.TwSetup1

/-!
A run of a machine program writes at most one number per step, so the output is no longer than the
running time.
-/

namespace Lax117284Proofs.Machine.TwSetup

open Lax808846.Ram

lemma step_out_len {w : ℕ} {p : Program} {s s' : State} (h : step w p s = some s') :
    s'.out.length ≤ s.out.length + 1 := by
  unfold step at h
  cases hi : p[s.pc]? with
  | none => rw [hi] at h; simp at h
  | some i =>
    rw [hi] at h
    simp only [Option.bind_some] at h
    cases i <;> simp only [Instr.effect, Option.some.injEq] at h <;>
      first
      | (simp at h; done)
      | (subst h; omega)
      | (subst h; simp)
      | (cases hh : s.inp.head? <;> simp only [hh, Option.map] at h
         · exact absurd h (by simp)
         · rename_i v
           simp only [Option.some.injEq] at h
           subst h; simp)
      | skip

lemma run_out_len {w : ℕ} {p : Program} : ∀ (n : ℕ) (s s' : State),
    run w p n s = some s' → s'.out.length ≤ s.out.length + n
  | 0, s, s', h => by
    simp only [run, Option.some.injEq] at h; subst h; omega
  | n + 1, s, s', h => by
    simp only [run] at h
    cases hs : step w p s with
    | none => rw [hs] at h; simp at h
    | some s1 =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      have := run_out_len n s1 s' h
      have := step_out_len hs
      omega

/-- **The output is no longer than the time.** -/
theorem RunsTo.out_length_le {w : ℕ} {p : Program} {x y : List ℕ} {t : ℕ} (h : RunsTo w p x y t) :
    y.length ≤ t := by
  obtain ⟨k, s, hrun, -, hout, ht⟩ := h
  subst hout
  have := run_out_len k _ s hrun
  simp [initState] at this
  omega

end Lax117284Proofs.Machine.TwSetup
