import Lax117284Proofs.Treewidth.Fun.ToValAlgSize
import Lax117284Proofs.Treewidth.Fun.Lib1
import Lax117284Proofs.Treewidth.Fun.Lib2

/-!
# WP E3: small utilities (size / `mx` facts about the data the enumerations manipulate)
-/

namespace Lax117284Proofs.Treewidth.Fun

open ToVal Lax117284Proofs.Treewidth.Chars

theorem mx_le_of_sublist {l l' : List ℕ} (h : l.Sublist l') : mx l ≤ mx l' := by
  rw [mx_list_le]
  intro a ha
  exact mx_le_of_mem (h.subset ha)

theorem mx_take_le (n : ℕ) (l : List ℕ) : mx (l.take n) ≤ mx l := mx_le_of_sublist (List.take_sublist _ _)
theorem mx_drop_le (n : ℕ) (l : List ℕ) : mx (l.drop n) ≤ mx l := mx_le_of_sublist (List.drop_sublist _ _)

/-- the pieces of a well-bounded characteristic node -/
theorem ct_node_facts {U : ℕ} {S : Finset ℕ} {y : List ℕ} {ks : List CT}
    (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) :
    S.card ≤ U ∧ y.length ≤ U ∧ sz ks + 1 ≤ U ∧ mx S ≤ U ∧ mx y ≤ U ∧ mx ks ≤ U ∧ sz S ≤ U ∧ sz y ≤ U := by
  rw [sz_ct_node] at hU
  rw [mx_ct_node] at hM
  have h1 := sz_finset S
  have h2 := sz_list_nat y
  have h3 := sz_pos ks
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem foldCost_le {α β : Type} (g : β → α → β) (cf : β → α → ℕ) (P : β → Prop) (c : ℕ) :
    ∀ (l : List α) (b : β), P b → (∀ b' a, P b' → a ∈ l → P (g b' a)) →
      (∀ b' a, P b' → a ∈ l → cf b' a ≤ c) → Lib1.foldCost g cf b l ≤ l.length * c := by
  intro l
  induction l with
  | nil => intro b _ _ _; simp [Lib1.foldCost]
  | cons a l ih =>
    intro b hb hstep hcf
    have h1 := hcf b a hb (List.mem_cons_self ..)
    have h2 := ih (g b a) (hstep b a hb (List.mem_cons_self ..))
      (fun b' x hb' hx => hstep b' x hb' (List.mem_cons_of_mem _ hx))
      (fun b' x hb' hx => hcf b' x hb' (List.mem_cons_of_mem _ hx))
    simp only [Lib1.foldCost, List.length_cons]
    nlinarith

theorem sum_map_le {α : Type} (f : α → ℕ) (c : ℕ) (l : List α) (h : ∀ a ∈ l, f a ≤ c) :
    (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- the arithmetic of one step of `kidChoices` -/
theorem kc_arith (m n a K Q : ℕ) (hK : 1 ≤ K) (hQ : 1000 ≤ Q) :
    60 + Q * m * (a + 1) + 32 * a + Q * n * (K + 1) + (a + 1) * (33 * K + 32) + 20 ≤
      Q * (m + n + 1) * ((a + 1) * K + 1) := by
  have hAK : a + 1 ≤ (a + 1) * K := Nat.le_mul_of_pos_right _ hK
  have s1 : Q * m * (a + 1) ≤ Q * m * ((a + 1) * K + 1) := Nat.mul_le_mul_left _ (by omega)
  have s2 : Q * n * (K + 1) ≤ Q * n * ((a + 1) * K + 1) := Nat.mul_le_mul_left _ (by nlinarith)
  have s3 : 32 * a + (a + 1) * (33 * K + 32) + 80 ≤ Q * ((a + 1) * K + 1) := by
    have : (a + 1) * (33 * K + 32) ≤ 65 * ((a + 1) * K) := by nlinarith
    nlinarith
  have e : Q * (m + n + 1) * ((a + 1) * K + 1) =
      Q * m * ((a + 1) * K + 1) + Q * n * ((a + 1) * K + 1) + Q * ((a + 1) * K + 1) := by ring
  omega

theorem flatMap_sum_le {α β : Type} (g : α → List β) (cf : α → ℕ) (C : ℕ) :
    ∀ (l : List α), (∀ a ∈ l, cf a + 10 * (g a).length + 20 ≤ C * (g a).length) →
      (l.map (fun a => cf a + 10 * (g a).length + 20)).sum ≤ C * (l.flatMap g).length
  | [], _ => by simp
  | a :: l, h => by
    have h1 := h a (List.mem_cons_self ..)
    have h2 := flatMap_sum_le g cf C l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
    nlinarith

theorem foldrCost_le {α β : Type} (g : α → β → β) (cf : α → β → ℕ) (P : β → Prop) (z : β) (c : ℕ) (hz : P z) :
    ∀ (l : List α), (∀ a b, a ∈ l → P b → P (g a b)) → (∀ a b, a ∈ l → P b → cf a b ≤ c) →
      Lib2.foldrCost g cf z l ≤ l.length * c
  | [], _, _ => by simp [Lib2.foldrCost]
  | a :: l, hs, hc => by
    have hP : P (l.foldr g z) :=
      Lib2.foldr_inv g P z hz l (fun a' b ha' hb => hs a' b (List.mem_cons_of_mem _ ha') hb)
    have h1 := hc a _ (List.mem_cons_self ..) hP
    have h2 := foldrCost_le g cf P z c hz l (fun a' b ha' hb => hs a' b (List.mem_cons_of_mem _ ha') hb)
      (fun a' b ha' hb => hc a' b (List.mem_cons_of_mem _ ha') hb)
    simp only [Lib2.foldrCost, List.length_cons]
    nlinarith

theorem sum_affine_le {α β : Type} (g : α → List β) (cf : α → ℕ) (a b : ℕ) :
    ∀ (l : List α), (∀ x ∈ l, cf x + 10 * (g x).length + 20 ≤ a * (g x).length + b) →
      (l.map (fun x => cf x + 10 * (g x).length + 20)).sum ≤ a * (l.flatMap g).length + b * l.length
  | [], _ => by simp
  | x :: l, h => by
    have h1 := h x (List.mem_cons_self ..)
    have h2 := sum_affine_le g cf a b l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

theorem filter_len_le_of_imp {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = true → q a = true) → (l.filter p).length ≤ (l.filter q).length
  | [], _ => by simp
  | a :: l, h => by
    have ih := filter_len_le_of_imp p q l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a (List.mem_cons_self ..)
    by_cases hp : p a = true
    · have hq := ha hp
      simp [List.filter_cons, hp, hq]; omega
    · by_cases hq : q a = true
      · simp [List.filter_cons, hp, hq]; omega
      · simp [List.filter_cons, hp, hq]; omega

end Lax117284Proofs.Treewidth.Fun
