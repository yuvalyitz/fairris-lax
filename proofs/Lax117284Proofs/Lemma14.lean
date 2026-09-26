import Lax117284Proofs.Lemma14Match
import Lax117284Proofs.Transport
import Lax117284.Lemma14

/-!
Lemma 14's correctness. The development's construction takes the graph presented through a
numbering of each vertex's neighbours; the construction of the concepts reads that numbering
off the graph, so it is that construction at that choice, and the two layouts differ on each
day only by a shift of the gadget.
-/

namespace Lax117284Proofs.Lemma14

open Lax117284.Scheduling Lax117284.MulticolouredIndepSet Lax117284.Lemma14
open Lax117284Proofs.Lemma14Graph Lax117284Proofs.Lemma14Build
open Lax117284Proofs.Lemma14Match

variable (G : Lax117284.MulticolouredIndepSet.Instance)

/-- On an instance in normal form the degree read off the graph is the common degree. -/
theorem regular_deg (hG : G.Normal) : G.Regular (deg G) := by
  obtain ⟨⟨r, hr, hreg⟩, -, -⟩ := hG
  rcases Nat.eq_zero_or_pos G.vertices with h0 | h0
  · intro w hw
    exact absurd hw (by omega)
  · have h1 : G.degree = r := hreg 0 h0
    have h2 : deg G = r := by
      simp only [deg, h1]
      omega
    rw [h2]
    exact hreg

/-- The instance of the development is the numbered one. -/
noncomputable def numbering (hreg : G.Regular (deg G)) :
    Transport.Numbering ((mis G hreg).inst) (inst G) where
  client := clientEquiv G hreg
  day := dayEquiv G hreg
  conflict_iff := fun i j j' =>
    (conflict_iff G hreg i j j').trans ((inst G).conflictAt_iff (dayEquiv G hreg i)
      (clientEquiv G hreg j) (clientEquiv G hreg j'))

/-- The fairness parameters agree: every day for the dummy, half the edges for each
interaction client, one for everybody else. -/
theorem kvec_eq (hreg : G.Regular (deg G)) (j : (mis G hreg).Client) :
    kvec G ((numbering G hreg).client j) = (mis G hreg).kvec (G.edgeCount / 2) j := by
  have hval : (((numbering G hreg).client j : Fin (inst G).clients) : ℕ)
      = clientNum G hreg j := rfl
  unfold Lax117284.Lemma14.kvec
  rw [hval]
  rcases j with v | i | x | b | u
  · have h := (cv_range G hreg v).1
    rw [if_neg (by omega), if_neg (by omega)]
    rfl
  · have h := (cs_range G hreg i).1
    rw [if_neg (by omega), if_neg (by omega)]
    rfl
  · have h := (ce_range G hreg x).1
    rw [if_neg (by omega), if_neg (by omega)]
    rfl
  · have h : clientNum G hreg (Sum.inr (Sum.inr (Sum.inr (Sum.inl b))))
        = (if b then 1 else 2) := rfl
    rw [h]
    cases b
    · rw [if_neg (by simp), if_pos (by simp)]
      rfl
    · rw [if_neg (by simp), if_pos (by simp)]
      rfl
  · have h : clientNum G hreg (Sum.inr (Sum.inr (Sum.inr (Sum.inr u)))) = 0 := rfl
    rw [h, if_pos rfl]
    exact (card_day G hreg).symm

/--
---
conclusion: Lax117284.Lemma14.correct
---
The vertex-selection gadget of a colour compels one vertex client of that colour, the
validation day pushes its incidence clients onto their edge days, and the two interaction
clients, needing half the edge days each, leave one of the two incidence clients of every
edge unserved. The dummy client blocks exactly the clients parked on a day, so each day
reduces to its gadget.
-/
theorem correct (hG : G.Normal) :
    G.HasIndepSet ↔ (inst G).HasFairSchedule (kvec G) := by
  have hreg := regular_deg G hG
  obtain ⟨-, hsize, hdvd⟩ := hG
  have hhalf : 2 * (G.edgeCount / 2) = Fintype.card (mis G hreg).Edge := by
    rw [card_edge G hreg]
    omega
  have hbal : (mis G hreg).ℓ * (mis G hreg).r ≤ G.edgeCount / 2 := balance G hreg hsize
  have h1 := (mis G hreg).hasFairSchedule_iff_hasIndepSet hhalf hbal
  rw [mis_hasIndepSet_iff G hreg] at h1
  have hk : (mis G hreg).kvec (G.edgeCount / 2)
      = fun j => kvec G ((numbering G hreg).client j) :=
    funext fun j => (kvec_eq G hreg j).symm
  calc G.HasIndepSet
      ↔ (mis G hreg).inst.HasFairSchedule ((mis G hreg).kvec (G.edgeCount / 2)) := h1.symm
    _ ↔ (mis G hreg).inst.HasFairSchedule
          (fun j => kvec G ((numbering G hreg).client j)) := by rw [hk]
    _ ↔ (inst G).HasFairSchedule (kvec G) :=
        (numbering G hreg).hasFairSchedule_iff (kvec G)

end Lax117284Proofs.Lemma14
