import Lax117284Proofs.Machine.TwNode

/-!
What a node program keeps: everything but its scratch scalars and the rows it fills.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

/-- The scalars the node programs write. -/
def SN : List String :=
  ["c", "vx", "ot", "s", "cw", "p", "pt", "s1", "iw", "bs", "fn", "fc", "val", "Pp", "shp1",
    "cbase", "off", "vs", "e", "lo", "hi", "rm", "so", "ac", "ix", "kd", "ov", "ob", "tbs"] ++ SV

/-- **Nothing but the scratch scalars changed, the input arrays are as they were, and the arrays
that are filled kept their length.** -/
structure Keep (σ0 σ : Env) : Prop where
  vars : ∀ y, y ∉ SN → σ.vars y = σ0.vars y
  X : σ.arrs "X" = σ0.arrs "X"
  O : σ.arrs "O" = σ0.arrs "O"
  szl : (σ.arrs "SZ").length = (σ0.arrs "SZ").length
  bgl : (σ.arrs "BG").length = (σ0.arrs "BG").length
  tbl : (σ.arrs "TB").length = (σ0.arrs "TB").length
  out : σ.out = σ0.out

lemma Keep.refl (σ : Env) : Keep σ σ := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma Keep.trans {σ0 σ1 σ2 : Env} (h1 : Keep σ0 σ1) (h2 : Keep σ1 σ2) : Keep σ0 σ2 :=
  ⟨fun y hy => (h2.vars y hy).trans (h1.vars y hy), h2.X.trans h1.X, h2.O.trans h1.O,
    h2.szl.trans h1.szl, h2.bgl.trans h1.bgl, h2.tbl.trans h1.tbl, h2.out.trans h1.out⟩

lemma Keep.of_agr {S : List String} {σ0 σ : Env} (h : Agr S σ0 σ) (hS : ∀ y ∈ S, y ∈ SN)
    (ho : σ.out = σ0.out) : Keep σ0 σ := by
  refine ⟨fun y hy => h.2 y (fun hyS => hy (hS y hyS)), ?_, ?_, ?_, ?_, ?_, ho⟩ <;>
    simp [h.1]

lemma Keep.of_agrA {S : List String} {arr : String} {σ0 σ : Env} (h : AgrA S arr σ0 σ)
    (hl : (σ.arrs arr).length = (σ0.arrs arr).length) (hS : ∀ y ∈ S, y ∈ SN)
    (harr : arr = "SZ" ∨ arr = "BG" ∨ arr = "TB") (ho : σ.out = σ0.out) : Keep σ0 σ := by
  have hx : ∀ a, a ≠ arr → σ.arrs a = σ0.arrs a := h.2
  rcases harr with rfl | rfl | rfl
  · exact ⟨fun y hy => h.1 y (fun hyS => hy (hS y hyS)), hx _ (by decide), hx _ (by decide), hl,
      by rw [hx _ (by decide)], by rw [hx _ (by decide)], ho⟩
  · exact ⟨fun y hy => h.1 y (fun hyS => hy (hS y hyS)), hx _ (by decide), hx _ (by decide),
      by rw [hx _ (by decide)], hl, by rw [hx _ (by decide)], ho⟩
  · exact ⟨fun y hy => h.1 y (fun hyS => hy (hS y hyS)), hx _ (by decide), hx _ (by decide),
      by rw [hx _ (by decide)], by rw [hx _ (by decide)], hl, ho⟩

lemma Keep.setVar {σ0 σ : Env} (h : Keep σ0 σ) {x : String} (hx : x ∈ SN) (v : ℕ) :
    Keep σ0 (σ.setVar x v) := by
  refine ⟨fun y hy => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : y ≠ x := fun e => hy (e ▸ hx)
    simp only [vars_setVar, this, if_false]; exact h.vars y hy
  · simpa using h.X
  · simpa using h.O
  · simpa using h.szl
  · simpa using h.bgl
  · simpa using h.tbl
  · simpa using h.out

lemma Keep.setArr {σ0 σ : Env} (h : Keep σ0 σ) {a : String} (ha : a = "SZ" ∨ a = "BG" ∨ a = "TB")
    (i v : ℕ) : Keep σ0 (σ.setArr a i v) := by
  rcases ha with rfl | rfl | rfl
  · exact ⟨fun y hy => by simpa using h.vars y hy, by simpa using h.X, by simpa using h.O,
      by simpa using h.szl, by simpa using h.bgl, by simpa using h.tbl, by simpa using h.out⟩
  · exact ⟨fun y hy => by simpa using h.vars y hy, by simpa using h.X, by simpa using h.O,
      by simpa using h.szl, by simpa using h.bgl, by simpa using h.tbl, by simpa using h.out⟩
  · exact ⟨fun y hy => by simpa using h.vars y hy, by simpa using h.X, by simpa using h.O,
      by simpa using h.szl, by simpa using h.bgl, by simpa using h.tbl, by simpa using h.out⟩

variable {P : Params} {B : ℕ}

lemma Keep.nc {σ0 σ : Env} (h : NC P B σ0) (k : Keep σ0 σ) : NC P B σ :=
  h.transfer (fun y hy => k.vars y (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [SN, SV, Stt, St2, SD])) k.X k.O k.szl k.bgl k.tbl

end Lax117284Proofs.Machine.TwNode
