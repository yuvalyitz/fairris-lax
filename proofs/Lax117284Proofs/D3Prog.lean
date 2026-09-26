import Lax117284Proofs.D3DP
import Lax117284Proofs.D3Rank
import Lax117284Proofs.Tractable
import Lax117284Proofs.WordCorrect
import Lax117284Proofs.ExtremeFairness
import Lax117284.Theorem12

/-!
Day-independent due dates: a fair schedule exists exactly when the dynamic program on numbers
reaches some state after the last client.
-/

namespace Lax117284Proofs.D3Prog

open Lax117284.Scheduling Lax117284Proofs.D3DP Lax117284Proofs.D3Rank

variable (I : Instance)

/-- The due date of a client, on the first day. -/
def ddI (j : ℕ) : ℕ := I.dAt 0 j

/-- The client at a position of the order. -/
noncomputable def ordI (c : ℕ) : ℕ := ordOf (ddI I) I.clients c

/-- The processing time, on a day, of the client at a position. -/
noncomputable def qI (i c : ℕ) : ℕ := I.pAt i (ordI I c)

/-- The due date of the client at a position. -/
noncomputable def eI (c : ℕ) : ℕ := ddI I (ordI I c)

lemma ordI_lt {c : ℕ} (hc : c < I.clients) : ordI I c < I.clients := (ordOf_spec hc).1

/-- The clients in the order. -/
noncomputable def lst : List (Fin I.clients) :=
  (List.finRange I.clients).map fun c => ⟨ordI I c.val, ordI_lt I c.isLt⟩

lemma lst_length : (lst I).length = I.clients := by simp [lst]

lemma lst_nodup : (lst I).Nodup := by
  unfold lst
  refine List.Nodup.map (fun a b h => ?_) (List.nodup_finRange _)
  have := congrArg Fin.val h
  exact Fin.ext (ordOf_inj a.isLt b.isLt this)

lemma lst_all (j : Fin I.clients) : j ∈ lst I := by
  unfold lst
  rw [List.mem_map]
  refine ⟨⟨rk (ddI I) I.clients j, rk_lt j.isLt⟩, List.mem_finRange _, ?_⟩
  apply Fin.ext
  exact ordOf_rk j.isLt

lemma lst_sorted (hm : 0 < I.days) :
    (lst I).Pairwise fun a b => I.d ⟨0, hm⟩ a ≤ I.d ⟨0, hm⟩ b := by
  unfold lst
  rw [List.pairwise_map]
  refine (List.pairwise_lt_finRange I.clients).imp (fun {a b} (hab : a < b) => ?_)
  have := ordOf_mono (dd := ddI I) a.isLt b.isLt (le_of_lt hab)
  have e1 := Instance.dAt_coe I ⟨0, hm⟩ ⟨ordI I a.val, ordI_lt I a.isLt⟩
  have e2 := Instance.dAt_coe I ⟨0, hm⟩ ⟨ordI I b.val, ordI_lt I b.isLt⟩
  simp only [Fin.val_mk] at e1 e2
  rw [← e1, ← e2]
  exact this

variable {I}

/-- The dynamic program of the concept, from a state and a position. -/
noncomputable def Good (hm : 0 < I.days) (k c : ℕ) (v : Vec I.days) : Prop :=
  Lax117284.Theorem12.Program (I := I) (I.d ⟨0, hm⟩) k ((lst I).drop c) (fun i => fv (eI I) (v i))

lemma fv_succ (c : ℕ) : fv (eI I) (c + 1) = eI I c := by simp [fv]

/-- **One client of the program.** -/
theorem good_step (hm : 0 < I.days) (k : ℕ) {c : ℕ} (hc : c < I.clients) (v : Vec I.days) :
    Good hm k c v ↔ ∃ S : Finset (Fin I.days), S.card = k ∧
      (∀ i ∈ S, feas I.days (qI I) (eI I) c v i) ∧ Good hm k (c + 1) (stepV I.days c S v) := by
  have hlen : c < (lst I).length := by rw [lst_length]; exact hc
  have hd : (lst I).drop c = (lst I)[c] :: (lst I).drop (c + 1) := List.drop_eq_getElem_cons hlen
  have hget : (lst I)[c] = ⟨ordI I c, ordI_lt I hc⟩ := by simp [lst]
  unfold Good
  rw [hd, hget]
  simp only [Lax117284.Theorem12.Program]
  have hp : ∀ i : Fin I.days, I.p i ⟨ordI I c, ordI_lt I hc⟩ = qI I i c := fun i => by
    unfold qI; exact (Instance.pAt_coe I i ⟨ordI I c, ordI_lt I hc⟩).symm
  have he : I.d ⟨0, hm⟩ ⟨ordI I c, ordI_lt I hc⟩ = eI I c := by
    unfold eI ddI; exact (Instance.dAt_coe I ⟨0, hm⟩ ⟨ordI I c, ordI_lt I hc⟩).symm
  refine exists_congr fun S => and_congr Iff.rfl (and_congr ?_ ?_)
  · refine forall₂_congr fun i hi => ?_
    unfold feas
    rw [hp, he]
  · have : (fun i => if i ∈ S then I.d ⟨0, hm⟩ ⟨ordI I c, ordI_lt I hc⟩ else fv (eI I) (v i)) =
        fun i => fv (eI I) (stepV I.days c S v i) := by
      funext i
      unfold stepV
      split_ifs
      · rw [he, fv_succ]
      · rfl
    rw [this]

/-- Nothing is left to serve after the last client. -/
theorem good_end (hm : 0 < I.days) (k : ℕ) (v : Vec I.days) : Good hm k I.clients v := by
  unfold Good
  rw [List.drop_of_length_le (by rw [lst_length])]
  trivial

/-- **The program reaches a state after the last client.** -/
theorem good_zero_iff_reach (hm : 0 < I.days) (k : ℕ) :
    Good hm k 0 (fun _ => 0) ↔ (Reach I.days k (qI I) (eI I) I.clients).Nonempty := by
  have key : ∀ c, c ≤ I.clients → ((∃ v ∈ Reach I.days k (qI I) (eI I) c, Good hm k c v) ↔
      Good hm k 0 (fun _ => 0)) := by
    intro c
    induction c with
    | zero =>
      intro _
      constructor
      · rintro ⟨v, hv, hg⟩
        have : v = fun _ => 0 := hv
        rwa [this] at hg
      · intro h
        exact ⟨fun _ => 0, rfl, h⟩
    | succ c ih =>
      intro hc
      rw [← ih (by omega)]
      constructor
      · rintro ⟨v', ⟨v, hv, S, hS, hfs, rfl⟩, hg⟩
        exact ⟨v, hv, (good_step hm k (by omega) v).2 ⟨S, hS, hfs, hg⟩⟩
      · rintro ⟨v, hv, hg⟩
        obtain ⟨S, hS, hfs, hg'⟩ := (good_step hm k (by omega) v).1 hg
        exact ⟨stepV I.days c S v, ⟨v, hv, S, hS, hfs, rfl⟩, hg'⟩
  rw [← key I.clients le_rfl]
  constructor
  · rintro ⟨v, hv, -⟩; exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩; exact ⟨v, hv, good_end hm k v⟩

/-- **A fair schedule exists exactly when a state is reachable.** -/
theorem hasKFair_iff_reach {I : Instance} (hd : I.DayIndepD) (hm : 0 < I.days) (k : ℕ) :
    I.HasKFairSchedule k ↔ (Reach I.days k (qI I) (eI I) I.clients).Nonempty := by
  rw [Tractable.hasKFairSchedule_iff_program hd ⟨0, hm⟩ k (lst_nodup I) (lst_all I)
    (lst_sorted I hm), ← good_zero_iff_reach hm k]
  rfl

end Lax117284Proofs.D3Prog
