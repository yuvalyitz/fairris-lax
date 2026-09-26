import Lax117284Proofs.Machine.SatSem

/-!
The image and the check depend only on the first entries of the array: an array that agrees with a
stream on its numbers gives the same image.
-/

namespace Lax117284Proofs.Machine.SatCong

open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem

variable {arr ns : List ℕ}

/-- The two lists agree on the numbers of a stream with `S` positions. -/
def Agree (arr ns : List ℕ) (S : ℕ) : Prop := ∀ k < 3 + 2 * S, arr.getD k 0 = ns.getD k 0

lemma Agree.n {S : ℕ} (h : Agree arr ns S) : arr.getD 0 0 = ns.getD 0 0 := h 0 (by omega)
lemma Agree.na {S : ℕ} (h : Agree arr ns S) : arr.getD 1 0 = ns.getD 1 0 := h 1 (by omega)
lemma Agree.nb {S : ℕ} (h : Agree arr ns S) : arr.getD 2 0 = ns.getD 2 0 := h 2 (by omega)

lemma Agree.slots {S : ℕ} (h : Agree arr ns S) : SlotsN arr = SlotsN ns := by
  unfold SlotsN; rw [h.na, h.nb]

lemma Agree.rank {S : ℕ} (h : Agree arr ns S) {o : ℕ} (ho : o < S) :
    rankN arr o = rankN ns o := by
  unfold rankN
  refine List.countP_congr fun o' ho' => ?_
  have h' : o' < o := List.mem_range.mp ho'
  rw [h (3 + 2 * o') (by omega), h (3 + 2 * o) (by omega), h (4 + 2 * o') (by omega),
    h (4 + 2 * o) (by omega)]

lemma Agree.pass {S : ℕ} (h : Agree arr ns S) {o : ℕ} (ho : o < S) :
    PassS arr o ↔ PassS ns o := by
  unfold PassS
  rw [h (3 + 2 * o) (by omega), h.n, h.rank ho]

lemma Agree.cond {S : ℕ} (h : Agree arr ns S) (hS : SlotsN ns = S) : CondN arr ↔ CondN ns := by
  unfold CondN
  rw [h.slots, h.n, hS]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun o ho => (h.pass ho).1 (h2 o ho)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun o ho => (h.pass ho).2 (h2 o ho)⟩

lemma Agree.due {S : ℕ} (h : Agree arr ns S) (hS : SlotsN ns = S) (d c : ℕ)
    (hc : c < 3 + 2 * ns.getD 0 0 + S) : dueN arr d c = dueN ns d c := by
  unfold dueN
  rw [h.n, h.na]
  by_cases h1 : c < 3
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : c < 3 + 2 * ns.getD 0 0
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2]
      have ho : c - 3 - 2 * ns.getD 0 0 < S := by omega
      rw [h (4 + 2 * (c - 3 - 2 * ns.getD 0 0)) (by omega),
        h (3 + 2 * (c - 3 - 2 * ns.getD 0 0)) (by omega), h.rank ho]

theorem Agree.out {S : ℕ} (h : Agree arr ns S) (hS : SlotsN ns = S) :
    outNums arr = outNums ns := by
  unfold outNums clientsN
  rw [h.n, h.slots]
  congr 2
  refine List.flatMap_congr fun i _ => List.flatMap_congr fun c hc => ?_
  have hc' := List.mem_range.mp hc
  rw [h.due hS i c (by omega)]

end Lax117284Proofs.Machine.SatCong
