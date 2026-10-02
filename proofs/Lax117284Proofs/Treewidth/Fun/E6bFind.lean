import Lax117284Proofs.Treewidth.Fun.Lib4

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6b (1): `findSome?` with the cost of the *examined prefix* only

`Lib4.findSome_runs` charges every element of the list.  `extract` searches the tables with `findSome?` and each
successful candidate performs a *recursive extraction*, so charging all successful candidates would multiply the
cost by the table length at every level.  Here: `prefixSome f l` is the list of examined elements (up to and including the
first `some`), and `findSome_first_runs` charges `Cn` per non-hit and `Ch` once, for the hit only.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lib1 Lib4

/-- the elements `findSome?` examines: up to and including the first `some` -/
def prefixSome {α β : Type} (f : α → Option β) : List α → List α
  | [] => []
  | a :: l => a :: (match f a with | none => prefixSome f l | some _ => [])

theorem prefixSome_length_le {α β : Type} (f : α → Option β) : ∀ l : List α, (prefixSome f l).length ≤ l.length
  | [] => by simp [prefixSome]
  | a :: l => by
    have := prefixSome_length_le f l
    cases h : f a <;> simp [prefixSome, h] <;> omega

theorem mem_prefixSome {α β : Type} (f : α → Option β) : ∀ {l : List α} {a : α}, a ∈ prefixSome f l → a ∈ l
  | [], a, h => by simp [prefixSome] at h
  | b :: l, a, h => by
    simp only [prefixSome] at h
    cases hb : f b with
    | none =>
      simp only [hb, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (mem_prefixSome f h)
    | some c =>
      simp only [hb, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h; simp

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Lib4.Δ ⊑ Δ') (B : ℕ) {α β : Type} [ToVal α] [ToVal β]
include hΔ

/-- the prefix form of `findSome_runs` -/
theorem findSome_pre_runs (fid : ℕ) (ctx : Val) (f : α → Option β) (cf : α → ℕ) (l : List α)
    (hf : ∀ a ∈ prefixSome f l, Runs Δ' B fid [ctx, toVal a] (toVal (f a)) (cf a)) (hB : 1 < B) :
    Runs Δ' B fFindSome [.nat fid, ctx, toVal l] (toVal (l.findSome? f))
      (24 * (prefixSome f l).length + 6 + ((prefixSome f l).map cf).sum) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_findSome) ?_
    ev_start
    · ev_run
    · simp [prefixSome]
  | cons a l ih =>
    have h1 := hf a (by simp [prefixSome])
    refine Runs.mk (hΔ _ _ Δ_findSome) ?_
    cases hp : f a with
    | none =>
      have ih := ih (fun x hx => hf x (by simp only [prefixSome, hp]; exact List.mem_cons_of_mem _ hx))
      simp only [hp] at h1
      simp only [List.findSome?_cons, hp]
      ev_start
      · ev_run
      · simp only [prefixSome, hp, List.length_cons, List.map_cons, List.sum_cons]; omega
    | some b =>
      simp only [hp] at h1
      simp only [List.findSome?_cons, hp]
      ev_start
      · ev_run
      · simp only [prefixSome, hp, List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil]
        omega

end proofs

theorem sum_prefix_le {α β : Type} (f : α → Option β) (cf : α → ℕ) (Cn Ch : ℕ) :
    ∀ l : List α, (∀ a ∈ l, f a = none → cf a ≤ Cn) → (∀ a ∈ l, (f a).isSome → cf a ≤ Ch) →
      ((prefixSome f l).map cf).sum ≤ (prefixSome f l).length * Cn + Ch
  | [], _, _ => by simp [prefixSome]
  | a :: l, hn, hs => by
    have ih := sum_prefix_le f cf Cn Ch l (fun x hx => hn x (List.mem_cons_of_mem _ hx))
      (fun x hx => hs x (List.mem_cons_of_mem _ hx))
    cases hp : f a with
    | none =>
      have h1 := hn a (List.mem_cons_self ..) hp
      simp only [prefixSome, hp, List.length_cons, List.map_cons, List.sum_cons]
      nlinarith
    | some b =>
      have h1 := hs a (List.mem_cons_self ..) (by simp [hp])
      simp only [prefixSome, hp, List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      omega

section proofs2
variable {Δ' : ℕ → Option Tm} (hΔ : Lib4.Δ ⊑ Δ') (B : ℕ) {α β : Type} [ToVal α] [ToVal β]
include hΔ

/-- **`findSome?` with a per-hit cost**: non-hits cost `≤ Cn`, hits `≤ Ch`; only the first hit is charged. -/
theorem findSome_first_runs (fid : ℕ) (ctx : Val) (f : α → Option β) (cf : α → ℕ) (l : List α) (Cn Ch : ℕ)
    (hf : ∀ a ∈ l, Runs Δ' B fid [ctx, toVal a] (toVal (f a)) (cf a))
    (hn : ∀ a ∈ l, f a = none → cf a ≤ Cn) (hs : ∀ a ∈ l, (f a).isSome → cf a ≤ Ch) (hB : 1 < B) :
    Runs Δ' B fFindSome [.nat fid, ctx, toVal l] (toVal (l.findSome? f)) (24 * l.length + 6 + l.length * Cn + Ch) := by
  have h := findSome_pre_runs hΔ B fid ctx f cf l (fun a ha => hf a (mem_prefixSome f ha)) hB
  have hsum := sum_prefix_le f cf Cn Ch l hn hs
  have hl := prefixSome_length_le f l
  refine h.mono ?_
  have : (prefixSome f l).length * Cn ≤ l.length * Cn := Nat.mul_le_mul_right _ hl
  omega

end proofs2

end E6b
end Lax117284Proofs.Treewidth.Fun
