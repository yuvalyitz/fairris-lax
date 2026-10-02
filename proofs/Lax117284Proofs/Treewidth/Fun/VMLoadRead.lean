import Lax117284Proofs.Treewidth.Fun.VMLoadStore

/-!
# WP V3 (3): reading the input word into the heap array `HA`

The tape is the raw word `x` (no length prefix; IMP+ has no end-of-input test).  `rdOne` reads one entry `v`, stores it
at `HA[i]`, keeps the running maximum `M`, and bumps `i`; `rdLoop` repeats it while `i < tot`.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-- The largest entry of a word (`0` for the empty word). -/
def wordMax (l : List ℕ) : ℕ := l.foldr max 0

theorem wordMax_append_single (l : List ℕ) (a : ℕ) : wordMax (l ++ [a]) = max (wordMax l) a := by
  induction l with
  | nil => simp [wordMax]
  | cons b l ih => simp only [List.cons_append, wordMax, List.foldr_cons] at ih ⊢; rw [ih]; omega

theorem wordMax_take_succ (x : List ℕ) (i : ℕ) (h : i < x.length) :
    wordMax (x.take (i + 1)) = max (wordMax (x.take i)) (x.getD i 0) := by
  have : x.take (i + 1) = x.take i ++ [x[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl
  rw [this, wordMax_append_single]
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem wordMax_lt {l : List ℕ} {B : ℕ} (hB : 0 < B) (h : ∀ v ∈ l, v < B) : wordMax l < B := by
  induction l with
  | nil => simpa [wordMax] using hB
  | cons a l ih =>
    have := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    have := h a (by simp)
    simp only [wordMax, List.foldr_cons] at *
    omega

theorem wordMax_take_le (x : List ℕ) (i : ℕ) : wordMax (x.take i) ≤ wordMax x := by
  have : x = x.take i ++ x.drop i := (List.take_append_drop i x).symm
  conv_rhs => rw [this]
  clear this
  generalize x.take i = a
  generalize x.drop i = b
  induction a with
  | nil => simp [wordMax]
  | cons c a ih => simp only [List.cons_append, wordMax, List.foldr_cons] at *; omega

theorem wordMax_getD_le (x : List ℕ) (j : ℕ) : x.getD j 0 ≤ wordMax x := by
  induction x generalizing j with
  | nil => simp
  | cons a l ih =>
    cases j with
    | zero => simp [wordMax]
    | succ j =>
      have := ih j
      simp only [wordMax, List.foldr_cons, List.getD_cons_succ] at *
      omega

/-- `nrm` at all hypotheses and the goal. -/
macro "nrmAt" : tactic => `(tactic| simp only [vars_setVar, arrs_setVar, inp_setVar, out_setVar, vars_setArr,
  arrs_setArr, inp_setArr, out_setArr, ↓reduceIte, String.reduceEq, eq_self, if_true, if_false] at *)

theorem getD_lt {x : List ℕ} {B : ℕ} (hB : 0 < B) (hxB : ∀ v ∈ x, v < B) (j : ℕ) : x.getD j 0 < B :=
  lt_of_le_of_lt (wordMax_getD_le x j) (wordMax_lt hB hxB)

abbrev bump (s : String) : Com := .assign s (pl (V s) (L 1))

/-- read one entry, store it at `HA[i]`, update the maximum, bump `i` -/
def rdOne : Com :=
  .seq (.read "v") (.seq (.store "HA" (V "i") (V "v"))
    (.seq (.ite (.lt (V "M") (V "v")) (.assign "M" (V "v")) .skip) (bump "i")))

def rdLoop : Com := .while (.lt (V "i") (V "tot")) rdOne

/-- The reader's invariant: the first `i` entries of the word have been read into `HA`. -/
structure RCore (x : List ℕ) (A : ℕ) (σ : IEnv) : Prop where
  hi : σ.vars "i" ≤ x.length
  inp : σ.inp = x.drop (σ.vars "i")
  ha : σ.arrs "HA" = arrOf A (fun j => if j < σ.vars "i" then x.getD j 0 else 0)
  hM : σ.vars "M" = wordMax (x.take (σ.vars "i"))

theorem headD_drop_eq (x : List ℕ) (i : ℕ) : (x.drop i).headD 0 = x.getD i 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < x.length
  · rw [List.drop_eq_getElem_cons h, List.getElem?_eq_getElem h]; rfl
  · rw [List.drop_of_length_le (by omega), List.getElem?_eq_none (by omega)]; rfl

theorem rdOne_spec {x : List ℕ} {A Bi : ℕ} (hA : x.length ≤ A) (hxB : ∀ v ∈ x, v < Bi) (hL : x.length + 1 < Bi) :
    Spec Bi (fun σ => RCore x A σ ∧ σ.vars "i" < x.length) rdOne
      (fun σ σ' => RCore x A σ' ∧ σ'.vars "i" = σ.vars "i" + 1 ∧ σ'.vars "tot" = σ.vars "tot" ∧
        σ'.vars "v" = x.getD (σ.vars "i") 0) 22 := by
  refine Spec.pre (P := fun σ => RCore x A σ ∧ σ.vars "i" < x.length ∧ σ.inp ≠ [] ∧ σ.inp.headD 0 < Bi ∧
    σ.vars "i" < (σ.arrs "HA").length ∧ σ.vars "M" < Bi ∧ σ.vars "i" + 1 < Bi) ?_ ?_
  · unfold rdOne bump
    run_vcg
    all_goals dsimp only at *
    all_goals nrmAt
    all_goals try assumption
    all_goals have hI : RCore x A σ := ‹_›
    all_goals have hlt : σ.vars "i" < x.length := ‹_›
    all_goals have hhd : σ.inp.headD 0 = x.getD (σ.vars "i") 0 := by rw [hI.inp, headD_drop_eq]
    all_goals have hMt := wordMax_take_succ x (σ.vars "i") hlt
    all_goals refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals try nrmAt
    all_goals first
      | omega
      | exact hhd
      | trivial
      | rfl
      | (rw [hI.inp, List.tail_drop]; done)
      | (rw [hI.ha, set_arrOf]; congr 1; funext k; simp only [hhd]
         split_ifs with h1 h2 <;>
           first | rfl | (exfalso; omega) | (have : k = σ.vars "i" := by omega
                                             subst this; rfl))
      | (rw [hMt, ← hI.hM]; omega)
  · intro σ ⟨hI, hlt⟩
    have hMB : σ.vars "M" < Bi := by
      rw [hI.hM]; exact wordMax_lt (by omega) (fun v hv => hxB v (List.mem_of_mem_take hv))
    have hxi : x.getD (σ.vars "i") 0 < Bi := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      exact hxB _ (List.getElem_mem _)
    have hhd : σ.inp.headD 0 = x.getD (σ.vars "i") 0 := by rw [hI.inp, headD_drop_eq]
    have hne : σ.inp ≠ [] := by
      rw [hI.inp]; intro h
      have := congrArg List.length h
      simp at this; omega
    have hHA : (σ.arrs "HA").length = A := by rw [hI.ha]; simp
    exact ⟨hI, hlt, hne, by rw [hhd]; exact hxi, by omega, hMB, by omega⟩

/-- The counted reading loop's invariant. -/
def RInv (x : List ℕ) (A N : ℕ) (σ : IEnv) : Prop :=
  RCore x A σ ∧ σ.vars "tot" = N ∧ N ≤ x.length ∧ σ.vars "i" ≤ N

theorem rdLoop_spec {x : List ℕ} {A Bi : ℕ} (N : ℕ) (hA : x.length ≤ A) (hxB : ∀ v ∈ x, v < Bi)
    (hL : x.length + 1 < Bi) :
    Spec Bi (fun σ => RInv x A N σ) rdLoop (fun _ σ' => RInv x A N σ' ∧ σ'.vars "i" = N) (26 * N + 4) := by
  refine Spec.forRange "i" "tot" (RInv x A N) N 22 (26 * N + 4) ?_ ?_ ?_ ?_ ?_ (fun _ h => h) ?_
  · intro σ h; have := h.2.2.1; have := h.2.2.2; omega
  · intro σ h; have := h.2.2.1; have := h.2.1; omega
  · intro σ h; exact h.2.1
  · intro σ h; exact h.2.2.2
  · intro σ ⟨h, hlt⟩
    obtain ⟨hc, ht, hN, hi⟩ := h
    obtain ⟨σ', hr, hq⟩ := (rdOne_spec (A := A) hA hxB hL).run (σ := σ) ⟨hc, by omega⟩
    refine ⟨σ', hr, ⟨hq.1, by rw [hq.2.2.1]; exact ht, hN, by rw [hq.2.1]; omega⟩, hq.2.1⟩
  · intro σ h
    have : (22 + 4) * (N - σ.vars "i") ≤ 26 * N := by
      have := Nat.mul_le_mul_left 26 (Nat.sub_le N (σ.vars "i")); omega
    omega

/-! ## The header: `n` is the first entry; the reader then knows how many entries the graph part has -/

/-- Read `n` (entry 0), store it, start the maximum, `i := 1`, `tot := n * n + t0`. -/
def hdrCom (t0 : ℕ) : Com :=
  .seq (.read "v") (.seq (.store "HA" (L 0) (V "v")) (.seq (.assign "M" (V "v"))
    (.seq (.assign "i" (L 1)) (.assign "tot" (pl (ml (V "v") (V "v")) (L t0))))))

theorem hdrCom_spec {x : List ℕ} {A Bi t0 : ℕ} (ht : 1 ≤ t0) (hx : x ≠ []) (hA : x.length ≤ A)
    (hxB : ∀ v ∈ x, v < Bi) (hL : x.length + 1 < Bi) (hN : x.getD 0 0 * x.getD 0 0 + t0 ≤ x.length) :
    Spec Bi (fun σ => σ.inp = x ∧ σ.arrs "HA" = arrOf A (fun _ => 0)) (hdrCom t0)
      (fun _ σ' => RInv x A (x.getD 0 0 * x.getD 0 0 + t0) σ' ∧ σ'.vars "i" = 1) 20 := by
  have hpos : 0 < x.length := List.length_pos_iff.mpr hx
  have h0B : x.getD 0 0 < Bi := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpos]; exact hxB _ (List.getElem_mem _)
  have hM1 : wordMax (x.take 1) = x.getD 0 0 := by
    have := wordMax_take_succ x 0 hpos
    simp only [Nat.zero_add, List.take_zero] at this
    rw [this]; simp [wordMax]
  refine Spec.pre (P := fun σ => σ.inp = x ∧ σ.arrs "HA" = arrOf A (fun _ => 0) ∧ σ.inp ≠ [] ∧
    σ.inp.headD 0 < Bi ∧ σ.inp.headD 0 * σ.inp.headD 0 + t0 < Bi ∧ 0 < (σ.arrs "HA").length) ?_ ?_
  · unfold hdrCom
    run_vcg
    all_goals dsimp only at *
    all_goals nrmAt
    all_goals try (first | assumption | omega)
    all_goals have hinp : σ.inp = x := ‹_›
    all_goals have hha : σ.arrs "HA" = arrOf A (fun _ => 0) := ‹_›
    all_goals have hhd : σ.inp.headD 0 = x.getD 0 0 := by rw [hinp]; cases x <;> simp_all
    all_goals refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
    all_goals try nrmAt
    all_goals first
      | omega
      | trivial
      | rfl
      | (rw [hinp]; cases x <;> simp_all; done)
      | (rw [hha, set_arrOf]; congr 1; funext k; simp only [hhd]
         split_ifs with h1 h2 <;>
           first | rfl | (exfalso; omega) | (have : k = 0 := by omega
                                             subst this; rfl))
      | (rw [hM1, hhd])
      | (rw [hhd])
  · intro σ ⟨hinp, hha⟩
    have hhd : σ.inp.headD 0 = x.getD 0 0 := by rw [hinp]; cases x <;> simp_all
    refine ⟨hinp, hha, by rw [hinp]; exact hx, by rw [hhd]; exact h0B, by rw [hhd]; omega, by rw [hha]; simp; omega⟩

/-! ## The two input formats -/

/-- `Fmt.graphK`: `n :: n² entries ++ [k]`, of length `n² + 2`. -/
def loadK : Com := .seq (hdrCom 2) rdLoop

/-- `Fmt.graphKLD`: `n :: n² entries ++ [k, l] ++ D`, `D = d :: 3d entries`, of length `n² + 4 + 3d`. -/
def loadKLD : Com :=
  .seq (hdrCom 3) (.seq rdLoop (.seq rdOne (.seq (.assign "tot" (pl (V "i") (ml (L 3) (V "v")))) rdLoop)))

/-- The whole word has been read. -/
def Read (x : List ℕ) (A : ℕ) (σ : IEnv) : Prop :=
  RInv x A x.length σ ∧ σ.vars "i" = x.length

theorem loadK_spec {x : List ℕ} {A Bi : ℕ} (hx : x ≠ []) (hA : x.length ≤ A)
    (hxB : ∀ v ∈ x, v < Bi) (hL : x.length + 1 < Bi) (hlen : x.getD 0 0 * x.getD 0 0 + 2 = x.length) :
    Spec Bi (fun σ => σ.inp = x ∧ σ.arrs "HA" = arrOf A (fun _ => 0)) loadK
      (fun _ σ' => Read x A σ') (26 * x.length + 24) := by
  have h1 := hdrCom_spec (t0 := 2) (by omega) hx hA hxB hL (by omega)
  rw [hlen] at h1
  have h2 := rdLoop_spec (A := A) (Bi := Bi) x.length hA hxB hL
  refine Spec.mono (Spec.seq h1 h2 ?_ ?_) (by omega)
  · intro σ σ' _ hq; exact hq.1
  · intro σ σ' σ'' _ _ hq; exact hq

theorem loadKLD_spec {x : List ℕ} {A Bi : ℕ} (hx : x ≠ []) (hA : x.length ≤ A)
    (hxB : ∀ v ∈ x, v < Bi) (hL : x.length + 1 < Bi)
    (hlen : x.getD 0 0 * x.getD 0 0 + 4 + 3 * x.getD (x.getD 0 0 * x.getD 0 0 + 3) 0 = x.length) :
    Spec Bi (fun σ => σ.inp = x ∧ σ.arrs "HA" = arrOf A (fun _ => 0)) loadKLD
      (fun _ σ' => Read x A σ') (52 * x.length + 60) := by
  set n2 := x.getD 0 0 * x.getD 0 0 with hn2
  set d := x.getD (n2 + 3) 0 with hd
  have hlt3 : n2 + 3 < x.length := by omega
  have hdB : d < Bi := getD_lt (by omega) hxB _
  have h1 := hdrCom_spec (t0 := 3) (by omega) hx hA hxB hL (by omega)
  have h2 := rdLoop_spec (A := A) (Bi := Bi) (n2 + 3) hA hxB hL
  have h3 := rdOne_spec (A := A) (Bi := Bi) hA hxB hL
  have h5 := rdLoop_spec (A := A) (Bi := Bi) x.length hA hxB hL
  have h4 : Spec Bi (fun σ => RCore x A σ ∧ σ.vars "i" = n2 + 4 ∧ σ.vars "v" = d)
      (.assign "tot" (pl (V "i") (ml (L 3) (V "v"))))
      (fun σ σ' => σ' = σ.setVar "tot" (σ.vars "i" + 3 * σ.vars "v")) 6 := by
    have := Spec.assign (B := Bi) (P := fun σ : IEnv => RCore x A σ ∧ σ.vars "i" = n2 + 4 ∧ σ.vars "v" = d)
      (x := "tot") (e := pl (V "i") (ml (L 3) (V "v"))) (f := fun σ => σ.vars "i" + 3 * σ.vars "v") (by
        intro σ ⟨_, hi, hv⟩
        have e1 : σ.vars "i" + 3 * σ.vars "v" = x.length := by rw [hi, hv]; omega
        exact RunStep.eval_add Bi σ _ _ _ _ (RunStep.eval_var Bi σ "i" (by omega))
          (RunStep.eval_mul Bi σ _ _ 3 (σ.vars "v") (RunStep.eval_lit Bi 3 σ (by omega))
            (RunStep.eval_var Bi σ "v" (by rw [hv]; exact hdB)) (by omega)) (by omega))
    simpa using this
  have h3' : Spec Bi (fun σ => RCore x A σ ∧ σ.vars "i" = n2 + 3) rdOne
      (fun σ σ' => RCore x A σ' ∧ σ'.vars "i" = n2 + 4 ∧ σ'.vars "v" = d) 22 :=
    (h3.pre (fun σ h => ⟨h.1, by rw [h.2]; exact hlt3⟩)).post (fun σ σ' h hq => ⟨hq.1, by rw [hq.2.1, h.2], by
      rw [hq.2.2.2, h.2]⟩)
  have h45 : Spec Bi (fun σ => RCore x A σ ∧ σ.vars "i" = n2 + 4 ∧ σ.vars "v" = d)
      (.seq (.assign "tot" (pl (V "i") (ml (L 3) (V "v")))) rdLoop) (fun _ σ' => Read x A σ')
      (6 + (26 * x.length + 4)) := by
    refine Spec.seq h4 h5 ?_ (fun _ _ _ _ _ hq => hq)
    intro σ σ' ⟨hc, hi, hv⟩ hq
    subst hq
    have e1 : σ.vars "i" + 3 * σ.vars "v" = x.length := by rw [hi, hv]; omega
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, le_rfl, ?_⟩
    · simpa using hc.hi
    · simpa using hc.inp
    · simpa using hc.ha
    · simpa using hc.hM
    · simpa using e1
    · simpa using hc.hi
  have h345 : Spec Bi (fun σ => RCore x A σ ∧ σ.vars "i" = n2 + 3)
      (.seq rdOne (.seq (.assign "tot" (pl (V "i") (ml (L 3) (V "v")))) rdLoop)) (fun _ σ' => Read x A σ')
      (22 + (6 + (26 * x.length + 4))) :=
    Spec.seq h3' h45 (fun σ σ' _ hq => hq) (fun _ _ _ _ _ hq => hq)
  have h2345 : Spec Bi (fun σ => RInv x A (n2 + 3) σ)
      (.seq rdLoop (.seq rdOne (.seq (.assign "tot" (pl (V "i") (ml (L 3) (V "v")))) rdLoop)))
      (fun _ σ' => Read x A σ') ((26 * (n2 + 3) + 4) + (22 + (6 + (26 * x.length + 4)))) :=
    Spec.seq h2 h345 (fun σ σ' _ hq => ⟨hq.1.1, hq.2⟩) (fun _ _ _ _ _ hq => hq)
  refine Spec.mono (Spec.seq h1 h2345 (fun σ σ' _ hq => hq.1) (fun _ _ _ _ _ hq => hq)) (by omega)

end Lax117284Proofs.Treewidth.Fun.VM.Ram
