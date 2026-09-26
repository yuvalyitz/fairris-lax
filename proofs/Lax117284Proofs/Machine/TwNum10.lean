import Lax117284Proofs.Machine.TwNum9

/-!
The time bound: `10 * Kx + 1` is at most a function of the parameter times a power of the length.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding Lax117284.ConflictGraph

/-- The function of the parameter in the time bound. -/
def Gp (cc Cp : ℕ) (p : ℕ) : ℕ := 10 * Cp + 10 * HB cc p + 1

theorem time_le {prog : Program} {ca cc : ℕ} (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    ∃ Cp Ep : ℕ, ∀ x, Dm x →
      10 * Kx prog ca cc x + 1 ≤
        Gp cc Cp ((Ix x).days + treewidth (Ix x)) * (x.length + 1) ^ Ep := by
  obtain ⟨Cp, Ep, h⟩ := plon_KP (prog := prog) hca hcc
  refine ⟨Cp, Ep, fun x hx => ?_⟩
  have h1 := h x hx
  have h2 := KB_le (cc := cc) (by omega) hx
  have h3 := Kx_le (prog := prog) (ca := ca) (cc := cc) (x := x)
  have h4 : 1 ≤ (x.length + 1) ^ Ep := Nat.one_le_pow _ _ (by omega)
  unfold Lp at h1
  unfold Gp
  generalize (x.length + 1) ^ Ep = a at *
  generalize HB cc ((Ix x).days + treewidth (Ix x)) = hb at *
  nlinarith

end Lax117284Proofs.Machine.TwNum
