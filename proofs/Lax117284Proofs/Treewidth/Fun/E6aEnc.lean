import Lax117284Proofs.Treewidth.Fun.E6aDefs

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E6a

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees Lib1

theorem NT.size_pos_aux (t : NT) : 1 ≤ t.size := by cases t <;> simp [NT.size] <;> omega

section addEv
variable {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ') (B : ℕ)
include hΔ

theorem addEv_runs (v : ℕ) (hB : 4 < B) : ∀ nt : NT,
    Runs Δ' B fAddEv [toVal v, toVal nt] (toVal (NT.addEverywhere v nt)) (30 * nt.size) := by
  intro nt
  induction nt with
  | leaf =>
    refine Runs.mk (hΔ _ _ Δ_addEv) ?_
    ev_start
    · ev_run
    · simp [NT.size]
  | intro u c ih =>
    refine Runs.mk (hΔ _ _ Δ_addEv) ?_
    ev_start
    · ev_run
    · simp [NT.size]; omega
  | forget u c ih =>
    refine Runs.mk (hΔ _ _ Δ_addEv) ?_
    ev_start
    · ev_run
    · simp [NT.size]; omega
  | join a b iha ihb =>
    refine Runs.mk (hΔ _ _ Δ_addEv) ?_
    ev_start
    · ev_run
    · simp [NT.size]; omega

end addEv

theorem recs_length : ∀ (nt : NT) (b : ℕ), (NT.recs b nt).length = nt.size
  | .leaf, b => by simp [NT.recs, NT.size]
  | .intro v c, b => by simp [NT.recs, NT.size, recs_length c b]
  | .forget v c, b => by simp [NT.recs, NT.size, recs_length c b]
  | .join x y, b => by
    simp [NT.recs, NT.size, recs_length x, recs_length y]; omega

section recs
variable {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ') (B : ℕ)
include hΔ

theorem recs_runs : ∀ (nt : NT) (b : ℕ), 8 * (b + nt.size) + 40 < B →
    Runs Δ' B fRecs [toVal b, toVal nt] (toVal (NT.recs b nt)) (60 * nt.size ^ 2) := by
  intro nt
  induction nt with
  | leaf =>
    intro b hB
    refine Runs.mk (hΔ _ _ Δ_recs) ?_
    ev_start
    · ev_run
    · simp [NT.size]
  | intro u c ih =>
    intro b hB
    simp only [NT.size] at hB
    have h1 := ih b (by omega)
    have h2 := append_runs (ext1 hΔ) B (NT.recs b c) [((1 : ℕ), (u, (0 : ℕ)))]
    rw [recs_length] at h2
    refine Runs.mk (hΔ _ _ Δ_recs) ?_
    simp only [NT.recs]
    ev_start
    · ev_run
    · simp [NT.size]; nlinarith
  | forget u c ih =>
    intro b hB
    simp only [NT.size] at hB
    have h1 := ih b (by omega)
    have h2 := append_runs (ext1 hΔ) B (NT.recs b c) [((2 : ℕ), (u, (0 : ℕ)))]
    rw [recs_length] at h2
    refine Runs.mk (hΔ _ _ Δ_recs) ?_
    simp only [NT.recs]
    ev_start
    · ev_run
    · simp [NT.size]; nlinarith
  | join x y ihx ihy =>
    intro b hB
    simp only [NT.size] at hB
    have hx1 := NT.size_pos_aux x
    have h1 := ihy b (by omega)
    have h2 := ihx (b + y.size) (by omega)
    have hl := length_runs (ext1 hΔ) B (NT.recs b y) (by rw [recs_length]; omega)
    rw [recs_length] at hl
    have h3 := append_runs (ext1 hΔ) B (NT.recs (b + y.size) x) [((3 : ℕ), ((0 : ℕ), b + y.size - 1))]
    rw [recs_length] at h3
    have h4 := append_runs (ext1 hΔ) B (NT.recs b y)
      (NT.recs (b + y.size) x ++ [((3 : ℕ), ((0 : ℕ), b + y.size - 1))])
    rw [recs_length] at h4
    refine Runs.mk (hΔ _ _ Δ_recs) ?_
    simp only [NT.recs, recs_length, List.append_assoc]
    ev_start
    · ev_run
    · simp [NT.size]; nlinarith

theorem triple_runs (ctx : Val) (r : ℕ × ℕ × ℕ) (hB : 0 < B) :
    Runs Δ' B fTriple [ctx, toVal r] (toVal [r.1, r.2.1, r.2.2]) 20 := by
  obtain ⟨a, b, c⟩ := r
  refine Runs.mk (hΔ _ _ Δ_triple) ?_
  ev_start
  · ev_run
  · omega

theorem encode_runs (nt : NT) (hB : 8 * nt.size + 1000 < B) :
    Runs Δ' B fEncode [toVal nt] (toVal nt.encode) (200 * nt.size ^ 2) := by
  have hp := NT.size_pos_aux nt
  have hT : fTriple < B := by show 653 < B; omega
  have h1 := recs_runs hΔ B nt 0 (by omega)
  have hl : Runs Δ' B fLength [toVal (NT.recs 0 nt)] (toVal (NT.recs 0 nt).length) (8 * nt.size + 5) :=
    (length_runs (ext1 hΔ) B (NT.recs 0 nt) (by rw [recs_length]; omega)).mono (by rw [recs_length])
  have hf := flatMap_runs (ext1 hΔ) B fTriple (.nat 0) (fun r : ℕ × ℕ × ℕ => [r.1, r.2.1, r.2.2]) (fun _ => 20)
    (NT.recs 0 nt) (fun r _ => triple_runs hΔ B _ r (by omega))
  have hsum : ((NT.recs 0 nt).map (fun a : ℕ × ℕ × ℕ => 20 + 10 * [a.1, a.2.1, a.2.2].length + 20)).sum
      = nt.size * 70 := by
    have : ∀ l : List (ℕ × ℕ × ℕ), (l.map (fun a : ℕ × ℕ × ℕ => 20 + 10 * [a.1, a.2.1, a.2.2].length + 20)).sum
        = l.length * 70 := by
      intro l; induction l with
      | nil => simp
      | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; simp; ring
    rw [this, recs_length]
  rw [hsum] at hf
  have hv : toVal nt.encode = Val.cons (Val.nat (NT.recs 0 nt).length)
      (toVal ((NT.recs 0 nt).flatMap (fun r : ℕ × ℕ × ℕ => [r.1, r.2.1, r.2.2]))) := rfl
  refine Runs.mk (hΔ _ _ Δ_encode) ?_
  rw [hv]
  ev_start
  · ev_run
  · nlinarith

end recs

section embeds
variable {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ')
include hΔ

end embeds

end E6a
end Lax117284Proofs.Treewidth.Fun
