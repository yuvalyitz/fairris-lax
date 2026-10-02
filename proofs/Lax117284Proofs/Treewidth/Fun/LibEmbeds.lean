import Lax117284Proofs.Treewidth.Fun.Lib

/-!
# `Embeds` instances of the library (unary, typed) — the shape the algorithm embeddings E1–E6 use

`Embeds Δ fid P f cost`: for every `B` with `Fits B (toVal a) (cost a)` the function `fid` computes `f a` in `cost a`.
The needed size hypotheses of the `Runs` lemmas (`1 < B`, `8·len+8 < B`, …) follow from `Fits` (`Fits.cost_lt`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace Lib

open ToVal

variable {Δ' : ℕ → Option Tm} (hΔ : Lib.Δ ⊑ Δ') {α : Type} [ToVal α]
include hΔ

theorem embeds_length : Embeds Δ' Lib1.fLength (fun _ : List α => True) List.length (fun l => 8 * l.length + 5) := by
  intro B l _ hfit
  have := hfit.cost_lt
  exact Lib1.length_runs (Ext.trans ext1 hΔ) B l (by omega)

theorem embeds_reverse : Embeds Δ' Lib2.fReverse (fun _ : List α => True) List.reverse (fun l => 12 * l.length + 10) := by
  intro B l _ hfit
  have := hfit.cost_lt
  exact Lib2.reverse_runs (Ext.trans ext2 hΔ) B l (by omega)

theorem embeds_dedup [DecidableEq α] : Embeds Δ' Lib2.fDedup (fun _ : List α => True) List.dedup
    (fun l => 60 * (sz l + 1) * (l.length + 1) ^ 2) := by
  intro B l _ hfit
  have h1 : 1 < B := by
    have := hfit.cost_lt
    have : 60 ≤ 60 * (sz l + 1) * (l.length + 1) ^ 2 := by
      have := Nat.one_le_pow 2 (l.length + 1) (by omega)
      nlinarith [Nat.zero_le (sz l)]
    omega
  exact Lib2.dedup_runs (Ext.trans ext2 hΔ) B h1 (sz l) l (fun a ha => sz_le_of_mem ha)

theorem embeds_card : Embeds Δ' Lib1.fLength (fun _ : Finset ℕ => True) Finset.card (fun S => 8 * S.card + 5) := by
  intro B S _ hfit
  have := hfit.cost_lt
  exact Lib4.card_runs (Ext.trans ext4 hΔ) B S (by omega)

theorem embeds_toFinset : Embeds Δ' Lib4.fToFinset (fun _ : List ℕ => True) List.toFinset
    (fun l => 60 * (l.length + 1) ^ 2) := by
  intro B l _ hfit
  exact Lib4.toFinset_runs (Ext.trans ext4 hΔ) B l

end Lib

/-! ### a toy composition through the closure lemmas: `l ↦ (reverse l).length` -/

section toy
open ToVal Lib

def toyTm : Tm := .call Lib1.fLength [.call Lib2.fReverse [.var 0]]
def toyΔ : ℕ → Option Tm := Lib.extend (fun f => if f = 128 then some toyTm else none)

theorem toy_inner : EmbedsE toyΔ (.call Lib2.fReverse [.var 0]) (fun _ : List ℕ => True)
    (fun l : List ℕ => [toVal l]) (fun l => l.reverse) (fun l => 1 + (12 * l.length + 10) + 1) := by
  have hrev := embeds_reverse (α := ℕ) (ext_extend _ : Lib.Δ ⊑ toyΔ)
  refine EmbedsE.call1 (P := fun _ : List ℕ => True) (hf := hrev)
      (hg := EmbedsE.var (f := fun l : List ℕ => l) 0 (fun a _ => by simp)) (hQ := fun _ _ => trivial) ?_
  intro B a _ h
  exact (fitsL_single B _ _).mp (h.mono_cost (by omega))

theorem toy_embeds : Embeds toyΔ 128 (fun _ : List ℕ => True) (fun l => l.reverse.length)
    (fun l => (1 + (12 * l.length + 10) + 1) + (8 * l.reverse.length + 5) + 1) := by
  have hbody : toyΔ 128 = some toyTm := by
    simp [toyΔ, Lib.extend, layerΔ_ge _ (show Lib.reserved ≤ 128 by decide)]
  refine Embeds.of_body hbody ?_
  have hlen := embeds_length (α := ℕ) (ext_extend _ : Lib.Δ ⊑ toyΔ)
  refine EmbedsE.call1 (P := fun _ : List ℕ => True) (hf := hlen) (hg := toy_inner) (hQ := fun _ _ => trivial) ?_
  intro B a _ h
  have h' := (fitsL_single B _ _).mp (h.mono_cost (le_refl _))
  refine (h'.mono_val (by have := mx_reverse a; simp only [mx] at this; omega)).mono_cost ?_
  simp only [List.length_reverse]; omega
end toy

end Lax117284Proofs.Treewidth.Fun
