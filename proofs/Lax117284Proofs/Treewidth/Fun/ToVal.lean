import Lax117284Proofs.Treewidth.Fun.Defs
import Mathlib.Data.Finset.Sort

/-!
# WP F0 (2): typed views of values (`ToVal`), sizes `sz`, and maximal naturals `mx`

`toVal : α → Val` is injective.  Conventions: lists end in `nat 0`; `Bool` is `nat 0/1`; `Option`: `none = nat 0`,
`some a = cons (nat 1) (toVal a)`; products are `cons`; `Finset ℕ` is the strictly sorted list of its elements.
-/

namespace Lax117284Proofs.Treewidth.Fun

/-- Typed views of values (`[] = nat 0`; `Finset ℕ` = strictly sorted list). -/
class ToVal (α : Type) where
  toVal : α → Val
  inj : Function.Injective toVal

open ToVal

instance : ToVal ℕ := ⟨Val.nat, fun _ _ h => by simpa using h⟩

instance : ToVal Val := ⟨id, fun _ _ h => h⟩

instance : ToVal Bool := ⟨fun b => .nat (if b then 1 else 0), by
  intro a b h
  cases a <;> cases b <;> simp_all⟩

instance : ToVal Unit := ⟨fun _ => .nat 0, fun _ _ _ => rfl⟩

/-- the list view. -/
def listVal {α : Type} [ToVal α] : List α → Val
  | [] => .nat 0
  | a :: l => .cons (toVal a) (listVal l)

theorem listVal_injective {α : Type} [ToVal α] : Function.Injective (listVal (α := α)) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ h; cases l₂ with
    | nil => rfl
    | cons b l₂ => simp [listVal] at h
  | cons a l₁ ih => intro l₂ h; cases l₂ with
    | nil => simp [listVal] at h
    | cons b l₂ =>
      simp only [listVal, Val.cons.injEq] at h
      rw [ToVal.inj h.1, ih h.2]

instance {α : Type} [ToVal α] : ToVal (List α) := ⟨listVal, listVal_injective⟩

instance {α β : Type} [ToVal α] [ToVal β] : ToVal (α × β) :=
  ⟨fun p => .cons (toVal p.1) (toVal p.2), by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [Val.cons.injEq] at h
    rw [ToVal.inj h.1, ToVal.inj h.2]⟩

instance {α : Type} [ToVal α] : ToVal (Option α) :=
  ⟨fun o => match o with | none => .nat 0 | some a => .cons (.nat 1) (toVal a), by
    intro a b h
    cases a <;> cases b <;> simp at h ⊢
    exact ToVal.inj h⟩

/-- A finite set of naturals as the strictly sorted list of its elements. -/
def finVal (S : Finset ℕ) : Val := toVal (S.sort (· ≤ ·))

instance : ToVal (Finset ℕ) := ⟨finVal, by
  intro S T h
  have h1 : S.sort (· ≤ ·) = T.sort (· ≤ ·) := ToVal.inj h
  rw [← Finset.sort_toFinset (· ≤ ·) (s := S), h1, Finset.sort_toFinset]⟩

/-! ### the `simp` set for `toVal` -/

section simps
variable {α β : Type} [ToVal α] [ToVal β]

@[simp] theorem toVal_nat (n : ℕ) : toVal n = Val.nat n := by rfl
@[simp] theorem toVal_bool (b : Bool) : toVal b = Val.nat (if b then 1 else 0) := by rfl
@[simp] theorem toVal_true : toVal true = Val.nat 1 := by rfl
@[simp] theorem toVal_false : toVal false = Val.nat 0 := by rfl
@[simp] theorem toVal_nil : toVal ([] : List α) = Val.nat 0 := by rfl
@[simp] theorem toVal_cons (a : α) (l : List α) : toVal (a :: l) = Val.cons (toVal a) (toVal l) := by rfl
@[simp] theorem toVal_pair (a : α) (b : β) : toVal (a, b) = Val.cons (toVal a) (toVal b) := by rfl
@[simp] theorem toVal_none : toVal (none : Option α) = Val.nat 0 := by rfl
@[simp] theorem toVal_some (a : α) : toVal (some a) = Val.cons (Val.nat 1) (toVal a) := by rfl
theorem toVal_finset (S : Finset ℕ) : toVal S = toVal (S.sort (· ≤ ·)) := rfl

@[simp] theorem toVal_empty_finset : toVal (∅ : Finset ℕ) = Val.nat 0 := by
  rw [toVal_finset]; simp

theorem toVal_list (l : List α) : toVal l = listVal l := rfl

end simps

/-! ### sizes and maximal naturals -/

/-- Size (number of cells) of the value view. -/
def sz {α : Type} [ToVal α] (a : α) : ℕ := (toVal a).size

/-- Largest natural occurring in the value view. -/
def mx {α : Type} [ToVal α] (a : α) : ℕ := (toVal a).maxNat

theorem Val.size_pos (v : Val) : 0 < v.size := by cases v <;> simp [Val.size]

section sizes
variable {α β : Type} [ToVal α] [ToVal β]

theorem sz_pos (a : α) : 0 < sz a := Val.size_pos _

@[simp] theorem sz_nat (n : ℕ) : sz n = 1 := by rfl
@[simp] theorem sz_nil : sz ([] : List α) = 1 := by rfl
theorem sz_cons (a : α) (l : List α) : sz (a :: l) = sz a + sz l + 1 := rfl
theorem sz_pair (a : α) (b : β) : sz (a, b) = sz a + sz b + 1 := by rfl
@[simp] theorem sz_none : sz (none : Option α) = 1 := by rfl
theorem sz_some (a : α) : sz (some a) = sz a + 2 := by
  simp only [sz, toVal_some, Val.size]; omega

/-- size of a list: one terminal cell, plus one cons cell and the element size per element. -/
theorem sz_list (l : List α) : sz l = 1 + l.length + (l.map sz).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [sz_cons, ih, List.length_cons, List.map_cons, List.sum_cons]; omega

theorem sz_list_nat (l : List ℕ) : sz l = 2 * l.length + 1 := by
  rw [sz_list]
  have : (l.map sz).sum = l.length := by
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]; omega
  omega

theorem length_le_sz (l : List α) : l.length ≤ sz l := by rw [sz_list]; omega

theorem sz_le_of_mem {a : α} {l : List α} (h : a ∈ l) : sz a ≤ sz l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [sz_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem sz_tail_lt (a : α) (l : List α) : sz l < sz (a :: l) := by rw [sz_cons]; omega
theorem sz_head_lt (a : α) (l : List α) : sz a < sz (a :: l) := by rw [sz_cons]; have := sz_pos l; omega

theorem sz_append (l₁ l₂ : List α) : sz (l₁ ++ l₂) + 1 = sz l₁ + sz l₂ := by
  induction l₁ with
  | nil => simp; omega
  | cons a l ih => simp only [List.cons_append, sz_cons]; omega

theorem sz_finset (S : Finset ℕ) : sz S = 2 * S.card + 1 := by
  have : sz S = sz (S.sort (· ≤ ·)) := rfl
  rw [this, sz_list_nat, Finset.length_sort]

theorem sz_pair_le {a : α} {b : β} : sz a ≤ sz (a, b) ∧ sz b ≤ sz (a, b) := by
  simp only [sz_pair]; omega

@[simp] theorem mx_nat (n : ℕ) : mx n = n := by rfl
@[simp] theorem mx_nil : mx ([] : List α) = 0 := by rfl
theorem mx_cons (a : α) (l : List α) : mx (a :: l) = max (mx a) (mx l) := rfl

theorem mx_le_of_mem {a : α} {l : List α} (h : a ∈ l) : mx a ≤ mx l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [mx_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem mx_list_le {l : List α} {M : ℕ} : mx l ≤ M ↔ ∀ a ∈ l, mx a ≤ M := by
  induction l with
  | nil => simp
  | cons b l ih => simp [mx_cons, ih]

theorem mx_finset_le {S : Finset ℕ} {M : ℕ} : mx S ≤ M ↔ ∀ a ∈ S, a ≤ M := by
  have : mx S = mx (S.sort (· ≤ ·)) := rfl
  rw [this, mx_list_le]; simp

end sizes

end Lax117284Proofs.Treewidth.Fun
