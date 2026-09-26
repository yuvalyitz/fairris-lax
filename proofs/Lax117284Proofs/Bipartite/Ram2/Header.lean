import Lax117284Proofs.Bipartite.Ram2.Word

/-!
Reading the word into the array `"a"`, and the header scalars.

The program starts with the scalar `len` already holding the length of the word (`Wrap.lean`).
`readAll` reads exactly `len` entries into `a`, so it never reads from an exhausted tape; `hdrCom`
then sets `V := a[0]`, `n := a[len - 1]`, `m := V - n`.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile

variable {B : ℕ}

/-- One entry: read it, store it, advance. -/
def readBody : Com :=
  .seq (.read "v")
    (.seq (.store "a" (.var "rt") (.var "v")) (.assign "rt" (.add (.var "rt") (.lit 1))))

/-- Read the whole word into `a`: `rt := 0; while rt < len do readBody`. -/
def readAll : Com :=
  .seq (.assign "rt" (.lit 0)) (.while (.lt (.var "rt") (.var "len")) readBody)

/-- Invariant of the read: `rt` entries consumed and stored. -/
def ReadInv (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "len" = x.length ∧ σ.vars "rt" ≤ x.length ∧ σ.inp = x.drop (σ.vars "rt") ∧
    σ.arrs "a" = arrOf x.length (fun t => if t < σ.vars "rt" then x.getD t 0 else 0)

theorem readBody_spec {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hlB : x.length < B) :
    Spec B (fun σ => ReadInv x σ ∧ σ.vars "rt" < x.length) readBody
      (fun σ σ' => ReadInv x σ' ∧ σ'.vars "rt" = σ.vars "rt" + 1) 10 := by
  rintro σ ⟨⟨hl, hrt, hinp, ha⟩, hlt⟩
  have hlen : (σ.arrs "a").length = x.length := by rw [ha]; simp
  have hdrop : σ.inp = x[σ.vars "rt"]'hlt :: x.drop (σ.vars "rt" + 1) := by
    rw [hinp, List.drop_eq_getElem_cons hlt]
  have hgetE : x[σ.vars "rt"]?.getD 0 = x[σ.vars "rt"]'hlt := by
    rw [List.getElem?_eq_getElem hlt]; rfl
  have htail : σ.inp.tail = x.drop (σ.vars "rt" + 1) := by rw [hdrop]; rfl
  have hne : σ.inp ≠ [] := by rw [hdrop]; exact List.cons_ne_nil _ _
  have hhead' : σ.inp.head?.getD 0 = x[σ.vars "rt"]'hlt := by rw [hdrop]; rfl
  have hv' : σ.inp.head?.getD 0 < B := by rw [hhead']; exact hx _ (List.getElem_mem hlt)
  have hhead : σ.inp.headD 0 = x[σ.vars "rt"]'hlt := by rw [hdrop]; rfl
  have hv : σ.inp.headD 0 < B := by rw [hhead]; exact hx _ (List.getElem_mem hlt)
  unfold readBody
  run_vcg
  all_goals (simp [ReadInv, hl, htail]; try omega)
  refine ⟨hlt, ?_⟩
  rw [ha, set_arrOf]
  refine arrOf_congr (fun k _ => ?_)
  by_cases hk : k = σ.vars "rt"
  · subst hk; simp [hhead', hgetE]
  · simp only [hk, if_false]
    split_ifs <;> first | rfl | omega

/-- **The read leaves the word in `a`.** -/
theorem readAll_spec {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hlB : x.length < B) :
    Spec B (fun σ => σ.vars "len" = x.length ∧ σ.inp = x ∧
        σ.arrs "a" = arrOf x.length (fun _ => 0))
      readAll (fun _ σ' => σ'.inp = [] ∧ ArrOK x σ' ∧ σ'.vars "len" = x.length)
      ((10 + 4) * x.length + 6) := by
  have hloop := Spec.forRangeZero (B := B) (c := readBody) "rt" "len" (ReadInv x) x.length 10
    hlB (fun σ hσ => hσ.2.1) (fun σ hσ => hσ.1) (readBody_spec hx hlB)
  refine hloop.conseq ?_ ?_ le_rfl
  · rintro σ ⟨hl, hinp, ha⟩
    refine ⟨by simpa using hl, by simp, by simpa using hinp, ?_⟩
    simpa using ha
  · rintro σ σ' _ ⟨⟨hl, -, hinp, ha⟩, hrt⟩
    rw [hrt] at hinp ha
    refine ⟨?_, ?_, hl⟩
    · rw [hinp]; exact List.drop_eq_nil_of_le le_rfl
    · unfold ArrOK
      rw [ha]
      exact arrOf_congr (fun k hk => by simp [hk])

/-- The header: `V := a[0]; n := a[len - 1]; m := V - n`. -/
def hdrCom : Com :=
  .seq (.assign "V" (.get "a" (.lit 0)))
    (.seq (.assign "n" (.get "a" (.sub (.var "len") (.lit 1))))
      (.assign "m" (.sub (.var "V") (.var "n"))))

theorem hdr_spec {x : List ℕ} (hg : Good x) (hB : x.length + 8 ≤ B) :
    Spec B (fun σ => ArrOK x σ ∧ σ.vars "len" = x.length) hdrCom
      (fun σ σ' => σ' = ((σ.setVar "V" (Vw x)).setVar "n" (nw x)).setVar "m" (mw x)) 12 := by
  rintro σ ⟨ha, hl⟩
  have h4 := hg.four_le
  have hlen := ha.length
  have hV : (σ.arrs "a").getD 0 0 = Vw x := ha.getD (by omega)
  have hn : (σ.arrs "a").getD (x.length - 1) 0 = nw x := ha.getD (by omega)
  have hVB : Vw x < B := by have := hg.V_lt; omega
  have hnB : nw x < B := by have := hg.n_lt; omega
  rw [List.getD_eq_getElem?_getD] at hV hn
  unfold hdrCom
  run_vcg
  all_goals (simp [hl, hV, hn, mw]; try omega)

end Lax117284Proofs.Bipartite.Ram2
