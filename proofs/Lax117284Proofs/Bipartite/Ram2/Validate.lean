import Lax117284Proofs.Bipartite.Ram2.SymmWord

/-!
The validator: the word is read into `t`, its header into `V`, `E`, `n`, and the syntactic
conditions of `WellFormed` other than `crosses` are checked in linear time, a flag `ok` (`1` or
`0`) recording the verdict: `n ≤ V`, the length `4 + V + 2E`, the first offset `0`, the last
offset `2E`, nondecreasing offsets, every target a vertex. The checks are ordered so that every
array read of a later check is in range once the earlier ones passed; a failed check clears the
flag and the later checks are skipped. `WF3 x` names what the flag certifies.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteDecision
open scoped Classical

variable {B : ℕ}

/-! ### The word in `t` -/

/-- The word is in the array `t`. -/
def TabOK (x : List ℕ) (σ : Env) : Prop := σ.arrs "t" = arrOf x.length (fun i => x.getD i 0)

theorem TabOK.length {x : List ℕ} {σ : Env} (h : TabOK x σ) : (σ.arrs "t").length = x.length := by
  rw [h]; simp

theorem TabOK.getD {x : List ℕ} {σ : Env} (h : TabOK x σ) {i : ℕ} (hi : i < x.length) :
    (σ.arrs "t").getD i 0 = x.getD i 0 := by rw [h]; exact getD_arrOf _ hi

theorem TabOK.congr {x : List ℕ} {σ σ' : Env} (h : TabOK x σ) (ha : σ'.arrs "t" = σ.arrs "t") :
    TabOK x σ' := by unfold TabOK; rw [ha]; exact h

theorem getD_lt_of_mem {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hB : 0 < B) (i : ℕ) :
    x.getD i 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : x[i]? with _ | v
  · exact hB
  · exact hx v (List.mem_of_getElem? h)

/-- One entry: read it, store it, advance. -/
def readTBody : Com :=
  .seq (.read "v")
    (.seq (.store "t" (.var "rt") (.var "v")) (.assign "rt" (.add (.var "rt") (.lit 1))))

/-- Read the whole word into `t`. -/
def readT : Com :=
  .seq (.assign "rt" (.lit 0)) (.while (.lt (.var "rt") (.var "len")) readTBody)

/-- Invariant of the read: `rt` entries consumed and stored. -/
def ReadTInv (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "len" = x.length ∧ σ.vars "rt" ≤ x.length ∧ σ.inp = x.drop (σ.vars "rt") ∧
    σ.arrs "t" = arrOf x.length (fun i => if i < σ.vars "rt" then x.getD i 0 else 0)

theorem readTBody_spec {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hlB : x.length < B) :
    Spec B (fun σ => ReadTInv x σ ∧ σ.vars "rt" < x.length) readTBody
      (fun σ σ' => ReadTInv x σ' ∧ σ'.vars "rt" = σ.vars "rt" + 1) 10 := by
  rintro σ ⟨⟨hl, hrt, hinp, ha⟩, hlt⟩
  have hlen : (σ.arrs "t").length = x.length := by rw [ha]; simp
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
  unfold readTBody
  run_vcg
  all_goals (simp [ReadTInv, hl, htail]; try omega)
  refine ⟨hlt, ?_⟩
  rw [ha, set_arrOf]
  refine arrOf_congr (fun k _ => ?_)
  by_cases hk : k = σ.vars "rt"
  · subst hk; simp [hhead', hgetE]
  · simp only [hk, if_false]
    split_ifs <;> first | rfl | omega

/-- **The read leaves the word in `t`.** -/
theorem readT_spec {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hlB : x.length < B) :
    Spec B (fun σ => σ.vars "len" = x.length ∧ σ.inp = x ∧
        σ.arrs "t" = arrOf x.length (fun _ => 0))
      readT (fun _ σ' => σ'.inp = [] ∧ TabOK x σ' ∧ σ'.vars "len" = x.length)
      ((10 + 4) * x.length + 6) := by
  have hloop := Spec.forRangeZero (B := B) (c := readTBody) "rt" "len" (ReadTInv x) x.length 10
    hlB (fun σ hσ => hσ.2.1) (fun σ hσ => hσ.1) (readTBody_spec hx hlB)
  refine hloop.conseq ?_ ?_ le_rfl
  · rintro σ ⟨hl, hinp, ha⟩
    refine ⟨by simpa using hl, by simp, by simpa using hinp, ?_⟩
    simpa using ha
  · rintro σ σ' _ ⟨⟨hl, -, hinp, ha⟩, hrt⟩
    rw [hrt] at hinp ha
    refine ⟨?_, ?_, hl⟩
    · rw [hinp]; exact List.drop_eq_nil_of_le le_rfl
    · unfold TabOK
      rw [ha]
      exact arrOf_congr (fun k hk => by simp [hk])

/-! ### The header and the facts the validator establishes -/

/-- The scalars of the header, in place, and the word in `t`. -/
structure Base (x : List ℕ) (σ : Env) : Prop where
  tab : TabOK x σ
  len : σ.vars "len" = x.length
  V : σ.vars "V" = Vw x
  E : σ.vars "E" = x.getD 1 0
  n : σ.vars "n" = nw x

theorem Base.setVar {x : List ℕ} {σ : Env} (h : Base x σ) (y : String)
    (hy : y ∉ ["len", "V", "E", "n"]) (v : ℕ) : Base x (σ.setVar y v) := by
  refine ⟨h.tab.congr rfl, ?_, ?_, ?_, ?_⟩
  · simp only [vars_setVar]; rw [if_neg (by rintro rfl; simp at hy)]; exact h.len
  · simp only [vars_setVar]; rw [if_neg (by rintro rfl; simp at hy)]; exact h.V
  · simp only [vars_setVar]; rw [if_neg (by rintro rfl; simp at hy)]; exact h.E
  · simp only [vars_setVar]; rw [if_neg (by rintro rfl; simp at hy)]; exact h.n

theorem Base.setArr {x : List ℕ} {σ : Env} (h : Base x σ) {a : String} (ha : a ≠ "t") (i v : ℕ) :
    Base x (σ.setArr a i v) :=
  ⟨h.tab.congr (by simp only [arrs_setArr]; rw [if_neg (Ne.symm ha)]), h.len, h.V, h.E, h.n⟩

/-- **What the validator certifies**: `WellFormed` without `crosses`. -/
structure WF3 (x : List ℕ) : Prop where
  nV : nw x ≤ Vw x
  len : x.length = 4 + Vw x + 2 * x.getD 1 0
  off0 : offw x 0 = 0
  offV : offw x (Vw x) = 2 * x.getD 1 0
  mono : ∀ i < Vw x, offw x i ≤ offw x (i + 1)
  tgt_lt : ∀ s < 2 * x.getD 1 0, tgtw x s < Vw x

theorem WF3.off_le {x : List ℕ} (h : WF3 x) {i : ℕ} (hi : i ≤ Vw x) :
    offw x i ≤ 2 * x.getD 1 0 := by
  rw [← h.offV]; exact mono_chain (offw x) (Vw x) h.mono i hi

/-- Well-formedness is `WF3` and `crosses`. -/
theorem wellFormed_iff {x : List ℕ} :
    WellFormed x ↔ WF3 x ∧ ∀ u < Vw x, ∀ j, offw x u ≤ j → j < offw x (u + 1) →
      (u < nw x ↔ nw x ≤ tgtw x j) := by
  constructor
  · intro hw
    exact ⟨⟨wf_nV hw, wf_len hw, wf_off0 hw, wf_offV hw, wf_mono hw, wf_tgt_lt hw⟩,
      fun u hu j h1 h2 => wf_cross hw hu h1 h2⟩
  · rintro ⟨h3, hc⟩
    refine ⟨?_, h3.len, h3.off0, h3.offV, h3.mono, h3.tgt_lt, ?_⟩
    · rw [← nw_eq_leftCount]; exact h3.nV
    · intro u hu j h1 h2
      rw [← nw_eq_leftCount]
      exact hc u hu j h1 h2

/-- The header: `V := t[0]; E := t[1]; n := t[len - 1]`. -/
def hdrT : Com :=
  .seq (.assign "V" (.get "t" (.lit 0)))
    (.seq (.assign "E" (.get "t" (.lit 1)))
      (.assign "n" (.get "t" (.sub (.var "len") (.lit 1)))))

theorem hdrT_spec {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hlB : x.length < B) (h4 : 4 ≤ x.length) :
    Spec B (fun σ => TabOK x σ ∧ σ.vars "len" = x.length) hdrT
      (fun σ σ' => σ' = ((σ.setVar "V" (Vw x)).setVar "E" (x.getD 1 0)).setVar "n" (nw x)) 14 := by
  rintro σ ⟨htab, hl⟩
  have hlen := htab.length
  have hB : 4 < B := by omega
  have hg0 : (σ.arrs "t").getD 0 0 = Vw x := htab.getD (by omega)
  have hg1 : (σ.arrs "t").getD 1 0 = x.getD 1 0 := htab.getD (by omega)
  have hgn : (σ.arrs "t").getD (x.length - 1) 0 = nw x := htab.getD (by omega)
  have hVB : Vw x < B := getD_lt_of_mem hx (by omega) 0
  have hEB : x.getD 1 0 < B := getD_lt_of_mem hx (by omega) 1
  have hnB : nw x < B := getD_lt_of_mem hx (by omega) _
  rw [List.getD_eq_getElem?_getD] at hg0 hg1 hgn
  unfold hdrT
  run_vcg
  all_goals (try simp [hl, hg0, hg1, hgn])
  all_goals (try omega)

end Lax117284Proofs.Bipartite.Ram2
