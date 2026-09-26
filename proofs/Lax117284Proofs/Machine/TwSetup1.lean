import Lax117284Proofs.Machine.TwRamLoop

/-!
Facts about a run of a machine program that the setup of the decomposition step needs: every
number it writes is a word.
-/

namespace Lax117284Proofs.Machine.TwSetup

open Lax808846.Ram

lemma step_out_lt {w : ℕ} {p : Program} {s s' : State} (h : step w p s = some s')
    (ho : ∀ v ∈ s.out, v < 2 ^ w) : ∀ v ∈ s'.out, v < 2 ^ w := by
  unfold step at h
  cases hi : p[s.pc]? with
  | none => rw [hi] at h; simp at h
  | some i =>
    rw [hi] at h
    simp only [Option.bind_some] at h
    have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
    cases i <;> simp only [Instr.effect, Option.some.injEq] at h <;>
      first
      | (simp at h; done)
      | (subst h; exact ho)
      | (subst h; intro v hv
         simp only [List.mem_append, List.mem_singleton] at hv
         rcases hv with hv | rfl
         · exact ho v hv
         · exact Nat.mod_lt _ hpos)
      | (cases hh : s.inp.head? <;> simp only [hh, Option.map] at h
         · exact absurd h (by simp)
         · rename_i v
           simp only [Option.some.injEq] at h
           subst h; exact ho)
      | skip

lemma run_out_lt {w : ℕ} {p : Program} : ∀ (n : ℕ) (s s' : State),
    run w p n s = some s' → (∀ v ∈ s.out, v < 2 ^ w) → ∀ v ∈ s'.out, v < 2 ^ w
  | 0, s, s', h, ho => by
    simp only [run, Option.some.injEq] at h; subst h; exact ho
  | n + 1, s, s', h, ho => by
    simp only [run] at h
    cases hs : step w p s with
    | none => rw [hs] at h; simp at h
    | some s1 =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      exact run_out_lt n s1 s' h (step_out_lt hs ho)

/-- **Every number a run writes is a word.** -/
theorem RunsTo.out_lt {w : ℕ} {p : Program} {x y : List ℕ} {t : ℕ} (h : RunsTo w p x y t) :
    ∀ v ∈ y, v < 2 ^ w := by
  obtain ⟨k, s, hrun, -, hout, -⟩ := h
  rw [← hout]
  exact run_out_lt k _ s hrun (by simp [initState])

end Lax117284Proofs.Machine.TwSetup
