import Lax117284Proofs.Theorem7_FromSat
import Lax117284Proofs.Theorem7Slots
import Lax117284Proofs.Transport
import Lax117284.Theorem7

/-!
The formula the development of Theorem 7 consumes, read off a numbered [2,3]-bounded 3-SAT
formula: a literal is a variable together with a sign either way, and the rank of a position
— which of the at most two occurrences of its literal it is — is the number of earlier slots
carrying that literal.
-/

namespace Lax117284Proofs.Theorem7Bridge

open Lax117284.BoundedSat Lax117284.Theorem7 Lax117284Proofs.Theorem7Slots

variable (φ : Formula)

/-- A literal of a clause of two literals, as the development writes it. -/
def aL (c : Fin φ.twoClauses) (α : Fin 2) : Model.TwoSat.Lit (Fin φ.vars) :=
  ⟨(φ.aLit c α).1, (φ.aLit c α).2⟩

/-- A literal of a clause of three literals, as the development writes it. -/
def bL (c : Fin φ.threeClauses) (α : Fin 3) : Model.TwoSat.Lit (Fin φ.vars) :=
  ⟨(φ.bLit c α).1, (φ.bLit c α).2⟩

theorem elim_lit (o : φ.Occ) :
    Sum.elim (fun q : Fin φ.twoClauses × Fin 2 => aL φ q.1 q.2)
        (fun q : Fin φ.threeClauses × Fin 3 => bL φ q.1 q.2) o
      = ⟨(φ.litAt o).1, (φ.litAt o).2⟩ := by
  rcases o with q | q <;> rfl

/-- **The formula of the development**, read off the numbered one. -/
@[reducible] noncomputable def bnd : Model.Theorem7.Bounded23 where
  nv := φ.vars
  nA := φ.twoClauses
  nB := φ.threeClauses
  aLit := aL φ
  bLit := bL φ
  rank := rankOf φ
  rank_inj := by
    intro o o' hl hr
    refine occ_eq_of_lit_rank φ ?_ hr
    rw [elim_lit, elim_lit] at hl
    refine Prod.ext ?_ ?_
    · exact congrArg Model.TwoSat.Lit.var hl
    · exact congrArg Model.TwoSat.Lit.pos hl

@[simp] theorem bnd_nv : (bnd φ).nv = φ.vars := rfl
@[simp] theorem bnd_nA : (bnd φ).nA = φ.twoClauses := rfl
@[simp] theorem bnd_nB : (bnd φ).nB = φ.threeClauses := rfl

theorem lit_bnd (o : φ.Occ) : (bnd φ).lit o = ⟨(φ.litAt o).1, (φ.litAt o).2⟩ := by
  rcases o with q | q <;> rfl

theorem rank_bnd (o : φ.Occ) : (bnd φ).rank o = rankOf φ o := rfl

/-- **The two questions agree.** -/
theorem satisfiable_iff : (bnd φ).Satisfiable ↔ φ.Satisfiable := Iff.rfl

/-! ### The clients, numbered

The three dummies first, then the two clients of every variable, then one client per
occurrence slot in the order the slots are numbered. -/

/-- Which of the two clients of a variable this is. -/
def bit (s : Bool) : ℕ := if s then 0 else 1

theorem bit_lt (s : Bool) : bit s < 2 := by cases s <;> decide

theorem bit_inj {s s' : Bool} (h : bit s = bit s') : s = s' := by
  cases s <;> cases s' <;> first | rfl | exact absurd h (by decide)

/-- The number of a client. -/
noncomputable def clientNum : (bnd φ).Client → ℕ
  | Sum.inl t => (t : ℕ)
  | Sum.inr (Sum.inl (v, s)) => 3 + 2 * (v : ℕ) + bit s
  | Sum.inr (Sum.inr o) => 3 + 2 * φ.vars + slotNum φ o

theorem clientNum_lt (c : (bnd φ).Client) : clientNum φ c < clients φ := by
  have hc : clients φ = 3 + 2 * φ.vars + slots φ := rfl
  rcases c with t | ⟨v, s⟩ | o
  · have := t.isLt
    have := Nat.zero_le (slots φ)
    simp only [clientNum]
    omega
  · have hv : (v : ℕ) < φ.vars := v.isLt
    have := Nat.zero_le (slots φ)
    have hb := bit_lt s
    simp only [clientNum]
    omega
  · have := slotNum_lt φ o
    simp only [clientNum]
    omega

theorem clientNum_injective : Function.Injective (clientNum φ) := by
  rintro (t | ⟨v, s⟩ | o) (t' | ⟨v', s'⟩ | o') h <;>
    simp only [clientNum] at h
  · exact congrArg Sum.inl (Fin.ext h)
  · exact absurd h (by have := t.isLt; have := bit_lt s'; omega)
  · exact absurd h (by have := t.isLt; have := Nat.zero_le (slotNum φ o'); omega)
  · exact absurd h (by have := t'.isLt; have := bit_lt s; omega)
  · have hb1 := bit_lt s
    have hb2 := bit_lt s'
    have hss : s = s' := bit_inj (by omega)
    have hvv : (v : ℕ) = (v' : ℕ) := by rw [hss] at h; omega
    exact congrArg (fun a => Sum.inr (Sum.inl a)) (Prod.ext (Fin.ext hvv) hss)
  · exact absurd h (by
      have hv : (v : ℕ) < φ.vars := v.isLt
      have := bit_lt s
      have := Nat.zero_le (slotNum φ o')
      omega)
  · exact absurd h (by have := t'.isLt; have := Nat.zero_le (slotNum φ o); omega)
  · exact absurd h (by
      have hv : (v' : ℕ) < φ.vars := v'.isLt
      have := bit_lt s'
      have := Nat.zero_le (slotNum φ o)
      omega)
  · exact congrArg (fun a => Sum.inr (Sum.inr a)) (slotNum_injective φ (by omega))

theorem card_client : Fintype.card (bnd φ).Client = clients φ := by
  have h1 : Fintype.card (bnd φ).Client
      = Fintype.card (Fin 3) + (Fintype.card (Fin (bnd φ).nv × Bool)
        + Fintype.card (bnd φ).Occ) := by
    rw [Fintype.card_sum, Fintype.card_sum]
  have h2 : Fintype.card (Fin (bnd φ).nv × Bool) = φ.vars * 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, bnd_nv]
  have h3 : Fintype.card (bnd φ).Occ = φ.twoClauses * 2 + φ.threeClauses * 3 := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, bnd_nA, bnd_nB]
  have h4 : clients φ = 3 + 2 * φ.vars + (2 * φ.twoClauses + 3 * φ.threeClauses) := rfl
  rw [h1, h2, h3, Fintype.card_fin]
  omega

/-- **The clients of the development are the numbered clients.** -/
noncomputable def clientEquiv : (bnd φ).Client ≃ Fin (clients φ) :=
  Equiv.ofBijective (fun c => ⟨clientNum φ c, clientNum_lt φ c⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun a b h => clientNum_injective φ (congrArg Fin.val h),
        by rw [card_client φ, Fintype.card_fin]⟩)

/-! ### The due dates agree -/

theorem due_dummy (i : ℕ) (t : Fin 3) : due φ i (t : ℕ) = 2 := by
  have := t.isLt
  simp only [due]
  rw [if_pos (by omega)]

theorem dueDate_dummy (i : Fin 3) (t : Fin 3) :
    (bnd φ).dueDate i (Sum.inl t) = 2 := by
  simp only [Model.Theorem7.Bounded23.dueDate]
  split_ifs <;> rfl

theorem due_xcl (i : ℕ) (v : ℕ) (hv : v < φ.vars) (b : ℕ) (hb : b < 2) :
    due φ i (3 + 2 * v + b)
      = if i = 0 then 2 * v + 5 else if i = 1 then 2
        else if b = 0 then 10 * v + 6 else 10 * v + 11 := by
  have e1 : (3 + 2 * v + b - 3) / 2 = v := by omega
  have e2 : (3 + 2 * v + b - 3) % 2 = b := by omega
  simp only [due]
  rw [if_neg (by omega), if_pos (by omega), e1, e2]

theorem dueDate_xcl (i : Fin 3) (v : Fin (bnd φ).nv) (s : Bool) :
    (bnd φ).dueDate i (Sum.inr (Sum.inl (v, s)))
      = if (i : ℕ) = 0 then 2 * (v : ℕ) + 5 else if (i : ℕ) = 1 then 2
        else if bit s = 0 then 10 * (v : ℕ) + 6 else 10 * (v : ℕ) + 11 := by
  cases s <;> rfl

theorem due_ocl (i : ℕ) (n : ℕ) :
    due φ i (3 + 2 * φ.vars + n)
      = if i = 2 then
          (if (litOfSlot φ n).2 then 10 * (litOfSlot φ n).1 + 5 + 2 * slotRank φ n
            else 10 * (litOfSlot φ n).1 + 10 + 2 * slotRank φ n)
        else if n < 2 * φ.twoClauses then
          (if i = 0 then 2 * φ.vars + 2 * (n / 2) + 7 else 2)
        else
          (if i = 0 then
            2 * φ.vars + 2 * φ.twoClauses + 2 * ((n - 2 * φ.twoClauses) / 3) + 9
          else 3 * ((n - 2 * φ.twoClauses) / 3) + 6) := by
  have e : 3 + 2 * φ.vars + n - 3 - 2 * φ.vars = n := by omega
  simp only [due]
  rw [if_neg (by omega), if_neg (by omega), e]

theorem d2_ocl (o : (bnd φ).Occ) :
    (bnd φ).d2 (Sum.inr (Sum.inr o))
      = (if (litOfSlot φ (slotNum φ o)).2
          then 10 * (litOfSlot φ (slotNum φ o)).1 + 5 + 2 * slotRank φ (slotNum φ o)
          else 10 * (litOfSlot φ (slotNum φ o)).1 + 10 + 2 * slotRank φ (slotNum φ o)) := by
  rw [litOfSlot_slotNum]
  show (if ((bnd φ).lit o).pos
      then 10 * (((bnd φ).lit o).var : ℕ) + 5 + 2 * (((bnd φ).rank o) : ℕ)
      else 10 * (((bnd φ).lit o).var : ℕ) + 10 + 2 * (((bnd φ).rank o) : ℕ)) = _
  rw [lit_bnd, rank_bnd]
  rfl

theorem d_eq (i : Fin 3) (c : (bnd φ).Client) :
    (bnd φ).dueDate i c = due φ (i : ℕ) (clientNum φ c) := by
  have hi : (i : ℕ) < 3 := i.isLt
  rcases c with t | ⟨v, s⟩ | o
  · rw [show clientNum φ (Sum.inl t) = (t : ℕ) from rfl, due_dummy, dueDate_dummy]
  · rw [show clientNum φ (Sum.inr (Sum.inl (v, s))) = 3 + 2 * (v : ℕ) + bit s from rfl,
      due_xcl φ _ (v : ℕ) v.isLt (bit s) (bit_lt s), dueDate_xcl]
  · rw [show clientNum φ (Sum.inr (Sum.inr o)) = 3 + 2 * φ.vars + slotNum φ o from rfl,
      due_ocl]
    show (if (i : ℕ) = 0 then (bnd φ).d0 (Sum.inr (Sum.inr o))
      else if (i : ℕ) = 1 then (bnd φ).d1 (Sum.inr (Sum.inr o))
      else (bnd φ).d2 (Sum.inr (Sum.inr o))) = _
    rw [d2_ocl]
    rcases o with ⟨j, α⟩ | ⟨j, α⟩
    · have hα : (α : ℕ) < 2 := α.isLt
      have hj : (j : ℕ) < φ.twoClauses := j.isLt
      have hn : slotNum φ (Sum.inl (j, α)) = 2 * (j : ℕ) + (α : ℕ) := rfl
      have e1 : (2 * (j : ℕ) + (α : ℕ)) / 2 = (j : ℕ) := by omega
      have hd0 : (bnd φ).d0 (Sum.inr (Sum.inr (Sum.inl (j, α))))
          = 2 * φ.vars + 2 * (j : ℕ) + 7 := rfl
      have hd1 : (bnd φ).d1 (Sum.inr (Sum.inr (Sum.inl (j, α)))) = 2 := rfl
      rw [hn, if_pos (show 2 * (j : ℕ) + (α : ℕ) < 2 * φ.twoClauses by omega), e1, hd0, hd1]
      split_ifs <;> first | rfl | omega
    · have hα : (α : ℕ) < 3 := α.isLt
      have hn : slotNum φ (Sum.inr (j, α))
          = 2 * φ.twoClauses + 3 * (j : ℕ) + (α : ℕ) := rfl
      have e1 : (2 * φ.twoClauses + 3 * (j : ℕ) + (α : ℕ) - 2 * φ.twoClauses) / 3
          = (j : ℕ) := by omega
      have hd0 : (bnd φ).d0 (Sum.inr (Sum.inr (Sum.inr (j, α))))
          = 2 * φ.vars + 2 * φ.twoClauses + 2 * (j : ℕ) + 9 := rfl
      have hd1 : (bnd φ).d1 (Sum.inr (Sum.inr (Sum.inr (j, α)))) = 3 * (j : ℕ) + 6 := rfl
      rw [hn, if_neg (show ¬ (2 * φ.twoClauses + 3 * (j : ℕ) + (α : ℕ)
        < 2 * φ.twoClauses) by omega), e1, hd0, hd1]
      split_ifs <;> first | rfl | omega

/-- The instance of the development is the numbered one: the same three days, the same
processing time everywhere, and the same due dates. -/
noncomputable def numbering : Transport.Numbering ((bnd φ).inst) (inst φ) :=
  Transport.Numbering.ofJobs (clientEquiv φ) (Equiv.refl (Fin 3))
    (fun _ _ => rfl) (fun i c => d_eq φ i c)

end Lax117284Proofs.Theorem7Bridge
