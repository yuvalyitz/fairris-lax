import Mathlib

/-!
# Sorted bags

The dynamic program keeps each bag as the increasing list of its clients, so that two bags that
are equal as sets are equal as lists and the tables of two children of a join node are indexed
alike. Introducing a client inserts it at the number of smaller entries, forgetting removes it
from there.
-/

namespace Lax117284Proofs.TwBags

/-- The number of entries below `v`. -/
def pos (l : List ℕ) (v : ℕ) : ℕ := l.countP (fun x => decide (x < v))

/-- Insertion into an increasing list, by recursion. -/
def ordIns (v : ℕ) : List ℕ → List ℕ
  | [] => [v]
  | a :: l => if a < v then a :: ordIns v l else v :: a :: l

variable {l : List ℕ} {v : ℕ}

lemma mem_ordIns {x : ℕ} : ∀ {l : List ℕ}, x ∈ ordIns v l ↔ x = v ∨ x ∈ l
  | [] => by simp [ordIns]
  | a :: l => by
    unfold ordIns
    split_ifs with h
    · simp only [List.mem_cons, mem_ordIns]; try tauto
    · simp; try tauto

lemma ordIns_pairwise : ∀ {l : List ℕ}, l.Pairwise (· < ·) → v ∉ l →
    (ordIns v l).Pairwise (· < ·)
  | [], _, _ => by simp [ordIns]
  | a :: l, h, hv => by
    obtain ⟨ha, hl⟩ := List.pairwise_cons.1 h
    have hva : v ≠ a := fun e => hv (by simp [e])
    unfold ordIns
    split_ifs with hlt
    · refine List.pairwise_cons.2 ⟨fun x hx => ?_, ordIns_pairwise hl (fun e => hv (by simp [e]))⟩
      rcases mem_ordIns.1 hx with rfl | hx
      · exact hlt
      · exact ha x hx
    · refine List.pairwise_cons.2 ⟨fun x hx => ?_, h⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · have := ha x hx; omega

lemma pos_cons_lt {a : ℕ} (h : a < v) : pos (a :: l) v = pos l v + 1 := by
  simp [pos, List.countP_cons, h]

lemma pos_cons_ge {a : ℕ} (h : ¬ a < v) : pos (a :: l) v = pos l v := by
  simp [pos, List.countP_cons, h]

lemma pos_eq_zero_of_ge (h : ∀ x ∈ l, ¬ x < v) : pos l v = 0 := by
  unfold pos
  rw [List.countP_eq_zero]
  intro x hx; simpa using h x hx

/-- **The position is where insertion into the increasing list goes.** -/
lemma insertIdx_pos : ∀ {l : List ℕ}, l.Pairwise (· < ·) → v ∉ l →
    l.insertIdx (pos l v) v = ordIns v l
  | [], _, _ => by simp [pos, ordIns]
  | a :: l, h, hv => by
    obtain ⟨ha, hl⟩ := List.pairwise_cons.1 h
    have hva : v ≠ a := fun e => hv (by simp [e])
    unfold ordIns
    by_cases hlt : a < v
    · rw [if_pos hlt, pos_cons_lt hlt, List.insertIdx_succ_cons,
        insertIdx_pos hl (fun e => hv (by simp [e]))]
    · rw [if_neg hlt]
      have : pos (a :: l) v = 0 := by
        rw [pos_cons_ge hlt]
        exact pos_eq_zero_of_ge fun x hx => by have := ha x hx; omega
      rw [this]; simp

lemma pos_le_length : ∀ {l : List ℕ}, pos l v ≤ l.length := fun {l} => List.countP_le_length

/-- **The position of a member is its index.** -/
lemma getElem_pos : ∀ {l : List ℕ}, l.Pairwise (· < ·) → v ∈ l →
    ∃ h : pos l v < l.length, l[pos l v] = v ∧ l.eraseIdx (pos l v) = l.erase v
  | [], _, hv => by simp at hv
  | a :: l, h, hv => by
    obtain ⟨ha, hl⟩ := List.pairwise_cons.1 h
    by_cases hlt : a < v
    · have hvl : v ∈ l := by
        rcases List.mem_cons.1 hv with rfl | hv
        · omega
        · exact hv
      obtain ⟨h1, h2, h3⟩ := getElem_pos hl hvl
      refine ⟨by rw [pos_cons_lt hlt]; simp; omega, ?_, ?_⟩
      · simp [pos_cons_lt hlt, h2]
      · rw [pos_cons_lt hlt, List.eraseIdx_cons_succ, h3, List.erase_cons_tail]
        simpa using (show a ≠ v by omega)
    · have hva : v = a := by
        rcases List.mem_cons.1 hv with e | hv
        · exact e
        · exfalso; have := ha v hv; omega
      subst hva
      have : pos (v :: l) v = 0 := by
        rw [pos_cons_ge hlt]
        exact pos_eq_zero_of_ge fun x hx => by have := ha x hx; omega
      refine ⟨by rw [this]; simp, by simp [this], by simp [this]⟩

lemma erase_pairwise (h : l.Pairwise (· < ·)) : (l.erase v).Pairwise (· < ·) :=
  h.sublist (List.erase_sublist ..)

lemma mem_erase_pairwise {x : ℕ} (h : l.Pairwise (· < ·)) :
    x ∈ l.erase v ↔ x ∈ l ∧ x ≠ v := by
  have hnd : l.Nodup := h.imp (fun {a b} h => h.ne)
  rw [List.Nodup.mem_erase_iff hnd]; tauto

/-- Two increasing lists with the same entries are equal. -/
lemma eq_of_mem_iff {l l' : List ℕ} (h : l.Pairwise (· < ·)) (h' : l'.Pairwise (· < ·))
    (hm : ∀ x, x ∈ l ↔ x ∈ l') : l = l' := by
  have hp : l.Perm l' := List.perm_of_nodup_nodup_toFinset_eq
    (h.imp (fun {a b} h => h.ne)) (h'.imp (fun {a b} h => h.ne)) (by ext x; simpa using hm x)
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => by omega |> fun _ => by
    have := hab; have := hba; omega) h h' hp

end Lax117284Proofs.TwBags
