import Lax117284Proofs.Bipartite.Ram2.Word
import Lax117284Proofs.Bipartite.StackSearchCorrect
import Lax808846Proofs.Reasoning
import Lax808846Proofs.Tactic
import Lax117284Proofs.Bipartite.Maximum
import Lax117284Proofs.Bipartite.Ram2.Wrap

/-! ### `Lax117284Proofs.Bipartite.Ram2.Header` -/

section
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

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.SearchMath` -/

section
/-!
The mathematics of the array-based backtracking search, with no machine in sight.

The machine keeps the stack in three parallel arrays `stkL`, `stkR`, `stkX`; here they are three
functions `Ls Rs : ℕ → ℕ` (the third, the resume column, is pure machine bookkeeping and plays no
role in correctness). Frame `k` places left vertex `Ls k` by trying right vertex `Rs k`; frame
`k + 1` exists because `Rs k` was occupied by `Ls (k + 1)`.

`PathA` is the *flat* well-formedness of the first `t` frames: everything that
`StackSearchCorrect.StackWF` says, minus its lists of not-yet-tried candidates (this search finds
its candidates lazily, by scanning, so there are none to record). `success_good` then shows that
when one more frame finds a free right vertex, applying every frame's choice, bottom to top, is a
`GoodResult` — by *reusing* `StackSearchCorrect.collapse_free`, with each frame's `rest` left
empty.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching Lax117284Proofs.Bipartite.StackSearch Lax117284Proofs.Bipartite.StackSearchCorrect

/-- The frames `Ls 0, Rs 0` up to `Ls (k-1), Rs (k-1)` as a `StackSearch` stack: head = top. -/
def framesOf (Ls Rs : ℕ → ℕ) : ℕ → List (Frame ℕ ℕ)
  | 0 => []
  | k + 1 => ⟨Ls k, Rs k, []⟩ :: framesOf Ls Rs k

/-- Apply the first `k` frames' choices to `μ`, bottom to top (frame `0` first). -/
def applyN (μ : ℕ → Option ℕ) (Ls Rs : ℕ → ℕ) : ℕ → ℕ → Option ℕ
  | 0 => μ
  | k + 1 => Function.update (applyN μ Ls Rs k) (Rs k) (some (Ls k))

/-- **The first `t` frames are a well-formed path**: the bottom frame places `l₀`, every frame
chose an edge of its own left vertex, each chosen right vertex (but the last frame's) is occupied
by the next frame's left vertex, and no right vertex is chosen twice. -/
structure PathA (adjB : ℕ → ℕ → Prop) (μ₀ : ℕ → Option ℕ) (l₀ : ℕ) (Ls Rs : ℕ → ℕ) (t : ℕ) :
    Prop where
  start : Ls 0 = l₀
  adj : ∀ k < t, adjB (Ls k) (Rs k)
  link : ∀ k, k + 1 < t → μ₀ (Rs k) = some (Ls (k + 1))
  distinct : ∀ i k, i < k → k < t → Rs i ≠ Rs k

theorem mem_framesOf {Ls Rs : ℕ → ℕ} {f : Frame ℕ ℕ} :
    ∀ {k : ℕ}, f ∈ framesOf Ls Rs k → ∃ i < k, f.r = Rs i
  | 0, h => by simp [framesOf] at h
  | k + 1, h => by
      rw [framesOf, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨k, Nat.lt_succ_self k, rfl⟩
      · obtain ⟨i, hi, hr⟩ := mem_framesOf h
        exact ⟨i, by omega, hr⟩

theorem mem_belowVisited_framesOf {Ls Rs : ℕ → ℕ} {x : ℕ} :
    ∀ {k : ℕ}, x ∈ belowVisited (∅ : Finset ℕ) (framesOf Ls Rs k) ↔ ∃ i < k, Rs i = x
  | 0 => by simp [framesOf, belowVisited]
  | k + 1 => by
      rw [framesOf, belowVisited, Finset.mem_insert, mem_belowVisited_framesOf]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨k, Nat.lt_succ_self k, rfl⟩
        · exact ⟨i, by omega, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
        · exact Or.inr ⟨i, h, rfl⟩
        · exact Or.inl rfl

/-- **A flat path is a `StackWF` stack** (with every `rest` empty). -/
theorem stackWF_of_pathA {adjB : ℕ → ℕ → Prop} [DecidableRel adjB] {μ₀ : ℕ → Option ℕ}
    {l₀ : ℕ} {Ls Rs : ℕ → ℕ} :
    ∀ t, PathA adjB μ₀ l₀ Ls Rs (t + 1) → StackWF adjB μ₀ ∅ l₀ (framesOf Ls Rs (t + 1))
  | 0, h => by
      show StackWF adjB μ₀ ∅ l₀ [⟨Ls 0, Rs 0, []⟩]
      refine ⟨h.start, fun x hx => ?_⟩
      have : x = Rs 0 := by simpa using hx
      subst this
      exact ⟨h.adj 0 (by omega), by simp⟩
  | t + 1, h => by
      have h' : PathA adjB μ₀ l₀ Ls Rs (t + 1) :=
        ⟨h.start, fun k hk => h.adj k (by omega), fun k hk => h.link k (by omega),
          fun i k hik hk => h.distinct i k hik (by omega)⟩
      have hne : ∀ f' ∈ framesOf Ls Rs t, f'.r ≠ Rs t := fun f' hf' => by
        obtain ⟨i, hi, hr⟩ := mem_framesOf hf'
        rw [hr]; exact h.distinct i t hi (by omega)
      show StackWF adjB μ₀ ∅ l₀
        (⟨Ls (t + 1), Rs (t + 1), []⟩ :: ⟨Ls t, Rs t, []⟩ :: framesOf Ls Rs t)
      refine ⟨stackWF_of_pathA t h', ?_, fun x hx => ?_⟩
      · show belowMatching μ₀ (framesOf Ls Rs t) (Rs t) = some (Ls (t + 1))
        rw [belowMatching_eq_of_notMem μ₀ (Rs t) (framesOf Ls Rs t) hne]
        exact h.link t (by omega)
      · have hx' : x = Rs (t + 1) := by simpa using hx
        subst hx'
        refine ⟨h.adj (t + 1) (by omega), fun hmem => ?_⟩
        rcases Finset.mem_insert.mp hmem with h1 | h1
        · exact h.distinct t (t + 1) (by omega) (by omega) h1.symm
        · obtain ⟨i, hi, hr⟩ := mem_belowVisited_framesOf.mp h1
          exact h.distinct i (t + 1) (by omega) (by omega) hr

theorem applyN_update_comm (Ls Rs : ℕ → ℕ) (r : ℕ) (v : Option ℕ) :
    ∀ (k : ℕ) (μ : ℕ → Option ℕ), (∀ i < k, Rs i ≠ r) →
      applyN (Function.update μ r v) Ls Rs k = Function.update (applyN μ Ls Rs k) r v
  | 0, _, _ => rfl
  | k + 1, μ, h => by
      show Function.update (applyN (Function.update μ r v) Ls Rs k) (Rs k) (some (Ls k)) =
        Function.update (Function.update (applyN μ Ls Rs k) (Rs k) (some (Ls k))) r v
      rw [applyN_update_comm Ls Rs r v k μ (fun i hi => h i (by omega)),
        Function.update_comm (h k (by omega)).symm]

/-- **The stack's own fold is the bottom-to-top application**, since the keys are distinct. -/
theorem fold_framesOf (Ls Rs : ℕ → ℕ) :
    ∀ (k : ℕ) (μ : ℕ → Option ℕ), (∀ i j, i < j → j < k → Rs i ≠ Rs j) →
      fold μ (framesOf Ls Rs k) = applyN μ Ls Rs k
  | 0, _, _ => rfl
  | k + 1, μ, h => by
      show fold (Function.update μ (Rs k) (some (Ls k))) (framesOf Ls Rs k) =
        Function.update (applyN μ Ls Rs k) (Rs k) (some (Ls k))
      rw [fold_framesOf Ls Rs k _ (fun i j hij hj => h i j hij (by omega)),
        applyN_update_comm Ls Rs (Rs k) _ k μ (fun i hi => h i k hi (by omega))]

/-- **Extending a path by one frame** that chose a fresh edge. -/
theorem PathA.extend {adjB : ℕ → ℕ → Prop} {μ₀ : ℕ → Option ℕ} {l₀ : ℕ} {Ls Rs : ℕ → ℕ} {t j : ℕ}
    (hP : PathA adjB μ₀ l₀ Ls Rs t) (hlink : ∀ k < t, μ₀ (Rs k) = some (Ls (k + 1)))
    (hadj : adjB (Ls t) j) (hd : ∀ i < t, Rs i ≠ j) :
    PathA adjB μ₀ l₀ Ls (Function.update Rs t j) (t + 1) := by
  refine ⟨hP.start, fun k hk => ?_, fun k hk => ?_, fun i k hik hk => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
    · rw [Function.update_of_ne (by omega)]; exact hP.adj k h
    · rw [Function.update_self]; exact hadj
  · have : k < t := by omega
    rw [Function.update_of_ne (by omega)]; exact hlink k this
  · have hit : i ≠ t := by omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
    · rw [Function.update_of_ne hit, Function.update_of_ne (by omega)]
      exact hP.distinct i k hik h
    · rw [Function.update_of_ne hit, Function.update_self]
      exact hd i hik

/-- **Soundness of a successful search.** `t` frames form a path, the next frame (left vertex
`Ls t`) found an unmatched neighbour `j` not chosen by any of them: applying all `t + 1`
choices, bottom to top, is a `GoodResult` for `l₀`. -/
theorem success_good {adjB : ℕ → ℕ → Prop} [DecidableRel adjB] {μ₀ : ℕ → Option ℕ} {l₀ : ℕ}
    {Ls Rs : ℕ → ℕ} {t j : ℕ} (hRes : Respects adjB μ₀) (hInj : InjOnSupport μ₀)
    (hUnm : ¬ Matched μ₀ l₀) (hP : PathA adjB μ₀ l₀ Ls Rs t)
    (hlink : ∀ k < t, μ₀ (Rs k) = some (Ls (k + 1))) (hadj : adjB (Ls t) j)
    (hd : ∀ i < t, Rs i ≠ j) (hfree : μ₀ j = none) :
    GoodResult adjB μ₀ ∅ l₀ (applyN μ₀ Ls (Function.update Rs t j) (t + 1)) := by
  have hP' := hP.extend hlink hadj hd
  have hwf := stackWF_of_pathA t hP'
  have hfree' : belowMatching μ₀ (framesOf Ls (Function.update Rs t j) t) j = none := by
    rw [belowMatching_eq_of_notMem μ₀ j (framesOf Ls (Function.update Rs t j) t)]
    · exact hfree
    · intro f' hf'
      obtain ⟨i, hi, hr⟩ := mem_framesOf hf'
      rw [hr, Function.update_of_ne (by omega)]
      exact hd i hi
  have hcf := collapse_free adjB hRes hInj hUnm
    (⟨Ls t, Function.update Rs t j t, []⟩ : Frame ℕ ℕ)
    (framesOf Ls (Function.update Rs t j) t) hwf
    (by rw [Function.update_self]; exact hfree')
  have hfold := fold_framesOf Ls (Function.update Rs t j) (t + 1) μ₀ hP'.distinct
  exact hfold ▸ hcf

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.SearchAbs` -/

section
/-!
The abstract state of the array-based backtracking search over compressed sparse rows, and how
one turn transforms it — with no machine in sight (`Ram2/SearchReal.lean` ties it to an `Env`).

`AS` records what the arrays and the visited table *mean*: left vertices `Ls`, chosen right
vertices `Rs`, resume **slots** `Xs` (absolute positions in the target array), the stack height
`top`, and the set `visB` of right vertices visited so far. Frame `k` scans the row of `Ls k`,
the slots `off (Ls k) .. off (Ls k + 1) - 1`, and `Xs k` is where it resumes; frames
`0 .. top - 2` have chosen their right vertex, frame `top - 1` is *pending*.

`AbsInv` is what one turn needs and what it re-establishes: the `PathA`/`link` correctness that
`success_good` uses, the closure bookkeeping that a failed search hands to the completeness
argument (`Cl`, `occ`), and the counting facts (`top_le`) that bound the stack. The graph is
`adjOff off tgt n` throughout: left `l` is adjacent to right index `j` when some slot of its row
holds the vertex `n + j`.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The abstract state of the search. -/
structure AS where
  Ls : ℕ → ℕ
  Rs : ℕ → ℕ
  Xs : ℕ → ℕ
  top : ℕ
  visB : ℕ → Prop

open Classical in
/-- How many right vertices below `m` are visited. -/
noncomputable def AS.nvis (a : AS) (m : ℕ) : ℕ := ((Finset.range m).filter a.visB).card

/-- `l` is *closed*: every neighbour of `l` below `m` is visited. -/
def Cl (adjB : ℕ → ℕ → Prop) (visB : ℕ → Prop) (m l : ℕ) : Prop :=
  ∀ j < m, adjB l j → visB j

theorem Cl.mono {adjB : ℕ → ℕ → Prop} {v v' : ℕ → Prop} {m l : ℕ} (h : Cl adjB v m l)
    (hv : ∀ r, v r → v' r) : Cl adjB v' m l :=
  fun j hj ha => hv j (h j hj ha)

/-- **What a failed search certifies**: the visited set is closed under the search. Every
neighbour of `l₀` is visited, and every visited right vertex is occupied by a closed left
vertex. -/
def FailCert (adjB : ℕ → ℕ → Prop) (μ₀ : ℕ → Option ℕ) (m l₀ : ℕ) (visB : ℕ → Prop) : Prop :=
  Cl adjB visB m l₀ ∧ ∀ r < m, visB r → ∃ l', μ₀ r = some l' ∧ Cl adjB visB m l'

/-- **The invariant at the start of a turn.** -/
structure AbsInv (off tgt : ℕ → ℕ) (μ₀ : ℕ → Option ℕ) (n m l₀ : ℕ) (a : AS) : Prop where
  top_pos : 1 ≤ a.top
  top_le : a.top ≤ a.nvis m + 1
  Lbd : ∀ k < a.top, a.Ls k < n
  Xlo : ∀ k < a.top, off (a.Ls k) ≤ a.Xs k
  Xhi : ∀ k < a.top, a.Xs k ≤ off (a.Ls k + 1)
  Xcl : ∀ k < a.top, ∀ s, off (a.Ls k) ≤ s → s < a.Xs k → ∀ j, tgt s = n + j → a.visB j
  path : PathA (adjOff off tgt n) μ₀ l₀ a.Ls a.Rs (a.top - 1)
  link : ∀ k, k + 1 < a.top → μ₀ (a.Rs k) = some (a.Ls (k + 1))
  Rvis : ∀ k, k + 1 < a.top → a.Rs k < m ∧ a.visB (a.Rs k)
  occ : ∀ r < m, a.visB r → ∃ l', μ₀ r = some l' ∧
    ((∃ k < a.top, a.Ls k = l') ∨ Cl (adjOff off tgt n) a.visB m l')

/-- Frame `top - 1` chose right vertex `j` at slot `s`: record it, resume after the slot, mark
`j` visited. -/
def AS.choose (a : AS) (s j : ℕ) : AS :=
  { a with Rs := Function.update a.Rs (a.top - 1) j,
           Xs := Function.update a.Xs (a.top - 1) (s + 1),
           visB := fun r => r = j ∨ a.visB r }

/-- Push a frame for `l'`, scanning its row from its first slot. -/
def AS.push (off : ℕ → ℕ) (a : AS) (l' : ℕ) : AS :=
  { a with Ls := Function.update a.Ls a.top l', Xs := Function.update a.Xs a.top (off l'),
           top := a.top + 1 }

/-- Pop the exhausted top frame. -/
def AS.pop (a : AS) : AS := { a with top := a.top - 1 }

/-- A zero-potential dummy state, the ghost of a finished search. -/
def AS.done : AS := ⟨fun _ => 0, fun _ => 0, fun _ => 0, 0, fun _ => True⟩

/-- What one scan found: slot `s` of the pending frame's row is the first slot at or after its
resume point whose target `n + j` is unvisited. -/
structure Found (off tgt : ℕ → ℕ) (n m : ℕ) (a : AS) (s j : ℕ) : Prop where
  lo : off (a.Ls (a.top - 1)) ≤ s
  hi : s < off (a.Ls (a.top - 1) + 1)
  tgtEq : tgt s = n + j
  lt : j < m
  fresh : ¬ a.visB j
  first : ∀ s', off (a.Ls (a.top - 1)) ≤ s' → s' < s → ∀ j', tgt s' = n + j' → a.visB j'

section Basic

variable {off tgt : ℕ → ℕ} {μ₀ : ℕ → Option ℕ} {n m l₀ : ℕ} {a : AS} {s j : ℕ}

theorem Found.adj (hF : Found off tgt n m a s j) : adjOff off tgt n (a.Ls (a.top - 1)) j :=
  ⟨s, hF.lo, hF.hi, hF.tgtEq⟩

theorem PathA.congr_Ls {adjB : ℕ → ℕ → Prop} {Ls Ls' Rs : ℕ → ℕ}
    {t : ℕ} (h : PathA adjB μ₀ l₀ Ls Rs t) (hL : ∀ k, k < t → Ls' k = Ls k)
    (h0 : Ls' 0 = Ls 0) : PathA adjB μ₀ l₀ Ls' Rs t := by
  refine ⟨by rw [h0]; exact h.start, fun k hk => ?_, fun k hk => ?_, h.distinct⟩
  · rw [hL k hk]; exact h.adj k hk
  · rw [hL (k + 1) hk]; exact h.link k hk

theorem PathA.mono {adjB : ℕ → ℕ → Prop} {Ls Rs : ℕ → ℕ}
    {t t' : ℕ} (h : PathA adjB μ₀ l₀ Ls Rs t) (ht : t' ≤ t) : PathA adjB μ₀ l₀ Ls Rs t' :=
  ⟨h.start, fun k hk => h.adj k (by omega), fun k hk => h.link k (by omega),
    fun i k hik hk => h.distinct i k hik (by omega)⟩

open Classical in
/-- Marking a fresh in-range vertex visited raises the count by exactly one. -/
theorem nvis_choose (a : AS) (s : ℕ) {m j : ℕ} (hj : j < m) (hfresh : ¬ a.visB j) :
    (a.choose s j).nvis m = a.nvis m + 1 := by
  unfold AS.nvis
  have hn : j ∉ (Finset.range m).filter a.visB := by simp [hfresh]
  rw [← Finset.card_insert_of_notMem hn]
  refine congrArg Finset.card ?_
  ext r
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
  show r < m ∧ (r = j ∨ a.visB r) ↔ r = j ∨ r < m ∧ a.visB r
  constructor
  · rintro ⟨hr, rfl | h⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hr, h⟩
  · rintro (rfl | ⟨hr, h⟩)
    · exact ⟨hj, Or.inl rfl⟩
    · exact ⟨hr, Or.inr h⟩

open Classical in
theorem nvis_le (a : AS) (m : ℕ) : a.nvis m ≤ m := by
  unfold AS.nvis
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem top_le_succ (hI : AbsInv off tgt μ₀ n m l₀ a) : a.top ≤ m + 1 := by
  have := hI.top_le; have := nvis_le a m; omega

/-- A found slot is at or after the resume point (everything before it is visited). -/
theorem Found.ge (hI : AbsInv off tgt μ₀ n m l₀ a) (hF : Found off tgt n m a s j) :
    a.Xs (a.top - 1) ≤ s := by
  by_contra h
  push Not at h
  exact hF.fresh (hI.Xcl (a.top - 1) (by have := hI.top_pos; omega) s hF.lo h j hF.tgtEq)

end Basic

section Transitions

variable {off tgt : ℕ → ℕ} {μ₀ : ℕ → Option ℕ} {n m l₀ : ℕ} {a : AS} {s j l' : ℕ}

/-- **A pushed frame keeps the invariant.** -/
theorem AbsInv.push (hI : AbsInv off tgt μ₀ n m l₀ a) (hF : Found off tgt n m a s j)
    (hocc : μ₀ j = some l') (hl'n : l' < n) (hmono : off l' ≤ off (l' + 1)) :
    AbsInv off tgt μ₀ n m l₀ ((a.choose s j).push off l') := by
  have hpos := hI.top_pos
  have hd : ∀ i < a.top - 1, a.Rs i ≠ j := fun i hi he =>
    hF.fresh (he ▸ (hI.Rvis i (by omega)).2)
  have hpath := (hI.path.extend (fun k hk => hI.link k (by omega)) hF.adj hd)
  have hlo := hF.lo
  have hhi := hF.hi
  refine ⟨by show 1 ≤ a.top + 1; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show a.top + 1 ≤ (a.choose s j).nvis m + 1
    rw [nvis_choose a s hF.lt hF.fresh]; have := hI.top_le; omega
  · intro k hk
    have hk' : k < a.top + 1 := hk
    show Function.update a.Ls a.top l' k < n
    by_cases hkt : k = a.top
    · rw [hkt, Function.update_self]; exact hl'n
    · rw [Function.update_of_ne hkt]; exact hI.Lbd k (by omega)
  · intro k hk
    have hk' : k < a.top + 1 := hk
    show off (Function.update a.Ls a.top l' k) ≤
      Function.update (Function.update a.Xs (a.top - 1) (s + 1)) a.top (off l') k
    by_cases hkt : k = a.top
    · rw [hkt, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hkt, Function.update_of_ne hkt]
      by_cases hk1 : k = a.top - 1
      · rw [hk1, Function.update_self]; omega
      · rw [Function.update_of_ne hk1]; exact hI.Xlo k (by omega)
  · intro k hk
    have hk' : k < a.top + 1 := hk
    show Function.update (Function.update a.Xs (a.top - 1) (s + 1)) a.top (off l') k ≤
      off (Function.update a.Ls a.top l' k + 1)
    by_cases hkt : k = a.top
    · rw [hkt, Function.update_self, Function.update_self]; exact hmono
    · rw [Function.update_of_ne hkt, Function.update_of_ne hkt]
      by_cases hk1 : k = a.top - 1
      · rw [hk1, Function.update_self]; omega
      · rw [Function.update_of_ne hk1]; exact hI.Xhi k (by omega)
  · intro k hk s' hs'lo hs'hi j' hj'
    have hk' : k < a.top + 1 := hk
    have hlo' : off (Function.update a.Ls a.top l' k) ≤ s' := hs'lo
    have hhi' : s' < Function.update (Function.update a.Xs (a.top - 1) (s + 1)) a.top (off l') k :=
      hs'hi
    show j' = j ∨ a.visB j'
    by_cases hkt : k = a.top
    · rw [hkt, Function.update_self] at hlo' hhi'; omega
    · rw [Function.update_of_ne hkt] at hlo' hhi'
      by_cases hk1 : k = a.top - 1
      · rw [hk1, Function.update_self] at hhi'
        rw [hk1] at hlo'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hhi' with h | h
        · exact Or.inr (hF.first s' hlo' h j' hj')
        · subst h
          left
          rw [hF.tgtEq] at hj'
          omega
      · rw [Function.update_of_ne hk1] at hhi'
        exact Or.inr (hI.Xcl k (by omega) s' hlo' hhi' j' hj')
  · have e : ((a.choose s j).push off l').top - 1 = a.top - 1 + 1 := by
      show a.top + 1 - 1 = a.top - 1 + 1
      omega
    rw [e]
    refine PathA.congr_Ls hpath (fun k hk => ?_) (by
      show Function.update a.Ls a.top l' 0 = a.Ls 0
      rw [Function.update_of_ne (by omega)])
    show Function.update a.Ls a.top l' k = a.Ls k
    rw [Function.update_of_ne (by omega)]
  · intro k hk
    have hk' : k < a.top := by have : k + 1 < a.top + 1 := hk; omega
    show μ₀ (Function.update a.Rs (a.top - 1) j k) = some (Function.update a.Ls a.top l' (k + 1))
    by_cases hk1 : k = a.top - 1
    · have : k + 1 = a.top := by omega
      rw [hk1, Function.update_self, ← hk1, this, Function.update_self]; exact hocc
    · rw [Function.update_of_ne hk1, Function.update_of_ne (by omega)]
      exact hI.link k (by omega)
  · intro k hk
    have hk' : k < a.top := by have : k + 1 < a.top + 1 := hk; omega
    show Function.update a.Rs (a.top - 1) j k < m ∧ (Function.update a.Rs (a.top - 1) j k = j ∨
      a.visB (Function.update a.Rs (a.top - 1) j k))
    by_cases hk1 : k = a.top - 1
    · rw [hk1, Function.update_self]; exact ⟨hF.lt, Or.inl rfl⟩
    · rw [Function.update_of_ne hk1]
      obtain ⟨h1, h2⟩ := hI.Rvis k (by omega)
      exact ⟨h1, Or.inr h2⟩
  · intro r hr hv
    have hv' : r = j ∨ a.visB r := hv
    rcases hv' with rfl | hv0
    · refine ⟨l', hocc, Or.inl ⟨a.top, by show a.top < a.top + 1; omega, ?_⟩⟩
      show Function.update a.Ls a.top l' a.top = l'
      rw [Function.update_self]
    · obtain ⟨l'', h1, h2⟩ := hI.occ r hr hv0
      refine ⟨l'', h1, ?_⟩
      rcases h2 with ⟨k, hk, hkl⟩ | hcl
      · left
        refine ⟨k, by show k < a.top + 1; omega, ?_⟩
        show Function.update a.Ls a.top l' k = l''
        rw [Function.update_of_ne (by omega)]; exact hkl
      · right
        exact hcl.mono (fun r' h => Or.inr h)

/-- **A popped frame keeps the invariant** (when frames remain). -/
theorem AbsInv.pop (hI : AbsInv off tgt μ₀ n m l₀ a)
    (hcl : Cl (adjOff off tgt n) a.visB m (a.Ls (a.top - 1))) (h2 : 2 ≤ a.top) :
    AbsInv off tgt μ₀ n m l₀ a.pop := by
  refine ⟨by show 1 ≤ a.top - 1; omega, ?_,
    fun k hk => hI.Lbd k (by have : k < a.top - 1 := hk; omega),
    fun k hk => hI.Xlo k (by have : k < a.top - 1 := hk; omega),
    fun k hk => hI.Xhi k (by have : k < a.top - 1 := hk; omega),
    fun k hk => hI.Xcl k (by have : k < a.top - 1 := hk; omega),
    hI.path.mono (by show a.top - 1 - 1 ≤ a.top - 1; omega),
    fun k hk => hI.link k (by have : k + 1 < a.top - 1 := hk; omega),
    fun k hk => hI.Rvis k (by have : k + 1 < a.top - 1 := hk; omega), ?_⟩
  · show a.top - 1 ≤ a.nvis m + 1
    have := hI.top_le; omega
  · intro r hr hv
    obtain ⟨l', h1, h3⟩ := hI.occ r hr hv
    refine ⟨l', h1, ?_⟩
    rcases h3 with ⟨k, hk, hkl⟩ | hc
    · by_cases hk1 : k = a.top - 1
      · right; rw [← hkl, hk1]; exact hcl
      · left; exact ⟨k, by show k < a.top - 1; omega, hkl⟩
    · exact Or.inr hc

/-- **An exhausted bottom frame is a failure certificate.** -/
theorem AbsInv.failCert (hI : AbsInv off tgt μ₀ n m l₀ a)
    (hcl : Cl (adjOff off tgt n) a.visB m (a.Ls (a.top - 1))) (h1 : a.top = 1) :
    FailCert (adjOff off tgt n) μ₀ m l₀ a.visB := by
  have h0 : a.Ls 0 = l₀ := hI.path.start
  have hcl0 : Cl (adjOff off tgt n) a.visB m (a.Ls 0) := by
    have : a.top - 1 = 0 := by omega
    rwa [this] at hcl
  refine ⟨h0 ▸ hcl0, fun r hr hv => ?_⟩
  obtain ⟨l', h2, h3⟩ := hI.occ r hr hv
  refine ⟨l', h2, ?_⟩
  rcases h3 with ⟨k, hk, hkl⟩ | hc
  · have : k = 0 := by omega
    rw [← hkl, this]; exact hcl0
  · exact hc

open Classical in
/-- **Soundness of a successful turn**: applying every frame's choice is a `GoodResult`. -/
theorem AbsInv.success (hRes : Respects (adjOff off tgt n) μ₀) (hInj : InjOnSupport μ₀)
    (hUnm : ¬ Matched μ₀ l₀) (hI : AbsInv off tgt μ₀ n m l₀ a) (hF : Found off tgt n m a s j)
    (hfree : μ₀ j = none) :
    GoodResult (adjOff off tgt n) μ₀ ∅ l₀
      (applyN μ₀ a.Ls (Function.update a.Rs (a.top - 1) j) a.top) := by
  have hpos := hI.top_pos
  have hd : ∀ i < a.top - 1, a.Rs i ≠ j := fun i hi he =>
    hF.fresh (he ▸ (hI.Rvis i (by omega)).2)
  have := success_good hRes hInj hUnm hI.path (fun k hk => hI.link k (by omega)) hF.adj hd hfree
  rwa [Nat.sub_add_cancel hpos] at this

end Transitions

/-! ### A restarted search -/

/-- The abstract state of a *restarted* search from `l₀`, reusing whatever the stack arrays held
before: only frame `0` (left vertex `l₀`, at the first slot of its row) and an empty visited set
matter. -/
def AS.restart (off : ℕ → ℕ) (b : AS) (l₀ : ℕ) : AS :=
  { b with Ls := Function.update b.Ls 0 l₀, Xs := Function.update b.Xs 0 (off l₀), top := 1,
           visB := fun _ => False }

theorem AbsInv.restart {off tgt : ℕ → ℕ} {μ₀ : ℕ → Option ℕ} {n m l₀ : ℕ} (b : AS)
    (hl₀ : l₀ < n) (hmono : off l₀ ≤ off (l₀ + 1)) :
    AbsInv off tgt μ₀ n m l₀ (AS.restart off b l₀) := by
  have h0 : (AS.restart off b l₀).Ls 0 = l₀ := by simp [AS.restart]
  have hX0 : (AS.restart off b l₀).Xs 0 = off l₀ := by simp [AS.restart]
  have hk0 : ∀ k, k < (AS.restart off b l₀).top → k = 0 := fun k hk => by
    have : k < 1 := hk
    omega
  refine ⟨le_rfl, by simp [AS.restart], fun k hk => ?_, fun k hk => ?_, fun k hk => ?_,
    fun k hk s hs1 hs2 => ?_, ⟨h0, ?_, ?_, ?_⟩,
    fun k hk => absurd hk (by simp [AS.restart]),
    fun k hk => absurd hk (by simp [AS.restart]), fun r _ hr => absurd hr (by simp [AS.restart])⟩
  · rw [hk0 k hk, h0]; exact hl₀
  · rw [hk0 k hk, hX0, h0]
  · rw [hk0 k hk, hX0, h0]; exact hmono
  · rw [hk0 k hk] at hs1 hs2; rw [h0] at hs1; rw [hX0] at hs2; intro j _; exfalso; omega
  · intro k hk; exact absurd hk (by simp [AS.restart])
  · intro k hk; exact absurd hk (by simp [AS.restart])
  · intro i k _ hk; exact absurd hk (by simp [AS.restart])

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.Scan` -/

section
/-!
The row scan over compressed sparse rows: find the first slot `s` at or after the resume point of
the row of left vertex `i` whose target `a[3 + V + s]` names a right vertex `cand = target - n`
not yet visited — the machine-level version of the head of a vertex's candidate list.

The scan stops the instant it finds one (or reaches the end of the row, `xe = off (i + 1)`), so
that a frame resumed after its candidate's sub-search failed pays only for the *new* segment it
sweeps; resume points strictly increase, so a row is swept at most once per search.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open scoped Classical

variable {B : ℕ}

/-- The `vis` array agrees with `visB`, for every right index below `m`. -/
def VisOK (visB : ℕ → Prop) (m : ℕ) (σ : Env) : Prop :=
  σ.arrs "vis" = arrOf m (fun j => if visB j then 1 else 0)

theorem VisOK.length {visB : ℕ → Prop} {m : ℕ} {σ : Env} (h : VisOK visB m σ) :
    (σ.arrs "vis").length = m := by rw [h]; simp

theorem VisOK.getD {visB : ℕ → Prop} {m : ℕ} {σ : Env} (h : VisOK visB m σ) {j : ℕ} (hj : j < m) :
    (σ.arrs "vis").getD j 0 = if visB j then 1 else 0 := by rw [h]; exact getD_arrOf _ hj

theorem VisOK.getD_lt {visB : ℕ → Prop} {m : ℕ} {σ : Env} (h : VisOK visB m σ) {j : ℕ}
    (hj : j < m) (hB : 1 < B) : (σ.arrs "vis").getD j 0 < B := by
  rw [h.getD hj]; split <;> omega

theorem VisOK.congr {visB : ℕ → Prop} {m : ℕ} {σ σ' : Env} (h : VisOK visB m σ)
    (ha : σ'.arrs "vis" = σ.arrs "vis") : VisOK visB m σ' := by unfold VisOK; rw [ha]; exact h

/-- Slots `[off l, p)` of row `l` all name visited right vertices. -/
def SlotsVis (x : List ℕ) (visB : ℕ → Prop) (l p : ℕ) : Prop :=
  ∀ s, offw x l ≤ s → s < p → ∀ j, tgtw x s = nw x + j → visB j

/-- **The scan invariant**: `x` has swept the slots `[off i, x)` of the row of `i`, and
`found`/`foundJ` summarize what that sweep saw — either every swept slot names a visited vertex,
or the last swept slot names the unvisited `foundJ` and every earlier one a visited vertex. -/
structure ScanInv (x : List ℕ) (visB : ℕ → Prop) (l : ℕ) (σ : Env) : Prop where
  i : σ.vars "i" = l
  xe : σ.vars "xe" = offw x (l + 1)
  V : σ.vars "V" = Vw x
  n : σ.vars "n" = nw x
  m : σ.vars "m" = mw x
  arr : ArrOK x σ
  vis : VisOK visB (mw x) σ
  xlo : offw x l ≤ σ.vars "x"
  xhi : σ.vars "x" ≤ offw x (l + 1)
  fle : σ.vars "found" ≤ 1
  fJ : σ.vars "foundJ" ≤ mw x
  cases : (σ.vars "found" = 0 ∧ SlotsVis x visB l (σ.vars "x")) ∨
    (σ.vars "found" = 1 ∧ offw x l < σ.vars "x" ∧
      tgtw x (σ.vars "x" - 1) = nw x + σ.vars "foundJ" ∧ ¬ visB (σ.vars "foundJ") ∧
      SlotsVis x visB l (σ.vars "x" - 1))

/-- The scalars the scan invariant reads. -/
def scanReads : List String := ["i", "xe", "V", "n", "m", "x", "found", "foundJ"]

theorem ScanInv.congr {x : List ℕ} {visB : ℕ → Prop} {l : ℕ} {σ σ' : Env}
    (h : ScanInv x visB l σ) (hv : ∀ y ∈ scanReads, σ'.vars y = σ.vars y)
    (ha : σ'.arrs "a" = σ.arrs "a") (hvis : σ'.arrs "vis" = σ.arrs "vis") :
    ScanInv x visB l σ' := by
  have hi := hv "i" (by simp [scanReads])
  have hxe := hv "xe" (by simp [scanReads])
  have hV := hv "V" (by simp [scanReads])
  have hn := hv "n" (by simp [scanReads])
  have hm := hv "m" (by simp [scanReads])
  have hx := hv "x" (by simp [scanReads])
  have hf := hv "found" (by simp [scanReads])
  have hfJ := hv "foundJ" (by simp [scanReads])
  refine ⟨by rw [hi]; exact h.i, by rw [hxe]; exact h.xe, by rw [hV]; exact h.V,
    by rw [hn]; exact h.n, by rw [hm]; exact h.m, h.arr.congr ha, h.vis.congr hvis,
    by rw [hx]; exact h.xlo, by rw [hx]; exact h.xhi, by rw [hf]; exact h.fle,
    by rw [hfJ]; exact h.fJ, by rw [hx, hf, hfJ]; exact h.cases⟩

/-- Setting a scalar the invariant does not read keeps it. -/
theorem ScanInv.setVar {x : List ℕ} {visB : ℕ → Prop} {l : ℕ} {σ : Env}
    (h : ScanInv x visB l σ) (y : String) (hy : y ∉ scanReads) (v : ℕ) :
    ScanInv x visB l (σ.setVar y v) :=
  h.congr (fun z hz => by
    simp only [vars_setVar]
    rw [if_neg]
    rintro rfl
    exact hy hz) rfl rfl

/-! ### One slot -/

/-- The candidate of the current slot: `a[3 + V + x] - n`. -/
def candExpr : Expr :=
  .sub (.get "a" (.add (.add (.lit 3) (.var "V")) (.var "x"))) (.var "n")

/-- One slot of the row: compute its candidate; if unvisited, record it; move on. -/
def scanBody : Com :=
  .seq (.assign "cand" candExpr)
    (.seq (.ite (.eq (.get "vis" (.var "cand")) (.lit 0))
        (.seq (.assign "foundJ" (.var "cand")) (.assign "found" (.lit 1)))
        .skip)
      (.assign "x" (.add (.var "x") (.lit 1))))

theorem candExpr_size : candExpr.size = 8 := by simp [candExpr]

/-- **One slot of the row, examined.** Only run with nothing found yet. -/
theorem scanBody_run {x : List ℕ} {visB : ℕ → Prop} {l : ℕ} (hg : Good x)
    (hB : x.length + 8 ≤ B) (hl : l < nw x) {σ : Env} (hI : ScanInv x visB l σ)
    (hx : σ.vars "x" < offw x (l + 1)) (hf : σ.vars "found" = 0) :
    ∃ σ' K, Run B scanBody σ σ' K ∧ K ≤ 26 ∧ ScanInv x visB l σ' ∧
      σ'.vars "x" = σ.vars "x" + 1 := by
  have hV := hI.V
  have hn := hI.n
  have hxlo := hI.xlo
  have hsV : σ.vars "x" < offw x (Vw x) := hg.slot_lt hl hx
  have hpos : 3 + Vw x + σ.vars "x" < x.length := hg.tgtPos_lt hsV
  have hread : (σ.arrs "a").getD (3 + Vw x + σ.vars "x") 0 = tgtw x (σ.vars "x") :=
    hI.arr.getD_tgtw hg hsV
  have htB : tgtw x (σ.vars "x") < x.length := by unfold tgtw; exact hg.getD_lt _ hpos
  have hlenA : (σ.arrs "a").length = x.length := hI.arr.length
  have hcm : tgtw x (σ.vars "x") - nw x < mw x := hg.cand_lt hl hxlo hx
  have hce : tgtw x (σ.vars "x") = nw x + (tgtw x (σ.vars "x") - nw x) := hg.cand_eq hl hxlo hx
  set c := tgtw x (σ.vars "x") - nw x with hc
  have hVB : Vw x < B := by have := hg.V_lt; omega
  have hmB : mw x < B := by have := hg.m_lt; omega
  have hnB : nw x < B := by have := hg.n_lt; omega
  have hxB : σ.vars "x" < B := by have := hg.off_lt_len (i := Vw x) le_rfl; omega
  -- evaluate `cand`
  have e1 : candExpr.evalB B σ = some c := by
    have h3 := RunStep.eval_lit B 3 σ (by omega)
    have hVe : (Expr.var "V").evalB B σ = some (Vw x) := by
      rw [← hV]; exact RunStep.eval_var B σ "V" (by omega)
    have hxe : (Expr.var "x").evalB B σ = some (σ.vars "x") := RunStep.eval_var B σ "x" hxB
    have hne : (Expr.var "n").evalB B σ = some (nw x) := by
      rw [← hn]; exact RunStep.eval_var B σ "n" (by omega)
    have h4 := RunStep.eval_add B σ _ _ _ _ h3 hVe (by omega)
    have h5 := RunStep.eval_add B σ _ _ _ _ h4 hxe (by omega)
    have h6 := RunStep.eval_get B σ "a" _ _ h5 (by omega) (by rw [hread]; omega)
    rw [hread] at h6
    exact RunStep.eval_sub B σ _ _ _ _ h6 hne (by omega)
  have r1 := RunStep.assign B σ "cand" candExpr c e1
  set σ₁ := σ.setVar "cand" c with hσ₁
  have hI₁ : ScanInv x visB l σ₁ := hI.setVar "cand" (by simp [scanReads]) c
  have hvisv : (σ₁.arrs "vis").getD c 0 = if visB c then 1 else 0 := hI₁.vis.getD hcm
  have hvislen : (σ₁.arrs "vis").length = mw x := hI₁.vis.length
  have hcand1 : σ₁.vars "cand" = c := by simp [hσ₁]
  have ecand : (Expr.var "cand").evalB B σ₁ = some c := by
    rw [← hcand1]; exact RunStep.eval_var B σ₁ "cand" (by rw [hcand1]; omega)
  have eget : (Expr.get "vis" (.var "cand")).evalB B σ₁ = some ((σ₁.arrs "vis").getD c 0) :=
    RunStep.eval_get B σ₁ "vis" _ c ecand (by omega) (hI₁.vis.getD_lt hcm (by omega))
  have e0 := RunStep.eval_lit B 0 σ₁ (by omega)
  have hx₁ : σ₁.vars "x" = σ.vars "x" := by simp [hσ₁]
  -- the increment of `x`, from any state agreeing with `σ` on `x`
  have einc : ∀ τ : Env, τ.vars "x" = σ.vars "x" →
      (Expr.add (.var "x") (.lit 1)).evalB B τ = some (σ.vars "x" + 1) := by
    intro τ hτ
    have := RunStep.eval_add B τ (.var "x") (.lit 1) (σ.vars "x") 1
      (by rw [← hτ]; exact RunStep.eval_var B τ "x" (by omega)) (RunStep.eval_lit B 1 τ (by omega))
      (by omega)
    exact this
  have hcases := hI.cases
  have hslots : SlotsVis x visB l (σ.vars "x") := by
    rcases hcases with ⟨-, h⟩ | ⟨h1, -⟩
    · exact h
    · omega
  by_cases hvc : visB c
  · -- the candidate is visited: nothing found, move on
    have hcond : (Cond.eq (.get "vis" (.var "cand")) (.lit 0)).evalB B σ₁ = some false :=
      RunStep.cond_eq_false B σ₁ _ _ _ 0 eget e0 (by rw [hvisv, if_pos hvc]; omega)
    have r2 := RunStep.ite_false B _
      (.seq (.assign "foundJ" (.var "cand")) (.assign "found" (.lit 1))) .skip σ₁ σ₁ 1 hcond
      (RunStep.skip B σ₁)
    have r4 := RunStep.assign B σ₁ "x" (.add (.var "x") (.lit 1)) (σ.vars "x" + 1) (einc σ₁ hx₁)
    refine ⟨σ₁.setVar "x" (σ.vars "x" + 1), _, r1.seq (r2.seq r4), ?_, ?_, by simp⟩
    · simp only [candExpr_size, size_condEq, size_get, size_var, size_lit, size_add]; omega
    · refine ⟨by simp [hσ₁]; exact hI.i, by simp [hσ₁]; exact hI.xe, by simp [hσ₁]; exact hI.V,
        by simp [hσ₁]; exact hI.n, by simp [hσ₁]; exact hI.m, hI.arr.congr (by simp [hσ₁]),
        hI.vis.congr (by simp [hσ₁]), by simp; omega, by simp; omega, by simp [hσ₁]; omega,
        by simp [hσ₁]; exact hI.fJ, ?_⟩
      left
      refine ⟨by simp [hσ₁]; exact hf, ?_⟩
      show SlotsVis x visB l (σ.vars "x" + 1)
      intro s hs1 hs2 j hj
      rcases Nat.lt_or_ge s (σ.vars "x") with h | h
      · exact hslots s hs1 h j hj
      · have : s = σ.vars "x" := by omega
        subst this
        have : j = c := by omega
        rw [this]; exact hvc
  · -- the candidate is fresh: record it
    have hcond : (Cond.eq (.get "vis" (.var "cand")) (.lit 0)).evalB B σ₁ = some true :=
      RunStep.cond_eq_true B σ₁ _ _ _ 0 eget e0 (by rw [hvisv, if_neg hvc])
    have r2 := RunStep.assign B σ₁ "foundJ" (.var "cand") c ecand
    set σ₂ := σ₁.setVar "foundJ" c with hσ₂
    have r3 := RunStep.assign B σ₂ "found" (.lit 1) 1 (RunStep.eval_lit B 1 σ₂ (by omega))
    set σ₃ := σ₂.setVar "found" 1 with hσ₃
    have rite := RunStep.ite_true B _ _ .skip σ₁ σ₃ _ hcond (r2.seq r3)
    have hx₃ : σ₃.vars "x" = σ.vars "x" := by simp [hσ₃, hσ₂, hσ₁]
    have r4 := RunStep.assign B σ₃ "x" (.add (.var "x") (.lit 1)) (σ.vars "x" + 1) (einc σ₃ hx₃)
    refine ⟨σ₃.setVar "x" (σ.vars "x" + 1), _, r1.seq (rite.seq r4), ?_, ?_, by simp⟩
    · simp only [candExpr_size, size_condEq, size_get, size_var, size_lit, size_add]; omega
    · refine ⟨by simp [hσ₃, hσ₂, hσ₁]; exact hI.i, by simp [hσ₃, hσ₂, hσ₁]; exact hI.xe,
        by simp [hσ₃, hσ₂, hσ₁]; exact hI.V, by simp [hσ₃, hσ₂, hσ₁]; exact hI.n,
        by simp [hσ₃, hσ₂, hσ₁]; exact hI.m, hI.arr.congr (by simp [hσ₃, hσ₂, hσ₁]),
        hI.vis.congr (by simp [hσ₃, hσ₂, hσ₁]), by simp; omega, by simp; omega,
        by simp [hσ₃, hσ₂, hσ₁], by simp [hσ₃, hσ₂, hσ₁]; omega, ?_⟩
      right
      refine ⟨by simp [hσ₃, hσ₂, hσ₁], by simp; omega, ?_, ?_, ?_⟩
      · simp [hσ₃, hσ₂, hσ₁]; exact hce
      · simp [hσ₃, hσ₂, hσ₁]; exact hvc
      · simp only [vars_setVar, ↓reduceIte, Nat.add_sub_cancel]
        exact hslots

/-! ### Early exit -/

/-- Whether the scan should keep going: `x` has not yet reached the end of the row, and nothing
has been found yet. `Cond` has no conjunction, so this is computed into a scalar. -/
def computeCont : Com :=
  .ite (.lt (.var "x") (.var "xe"))
    (.ite (.eq (.var "found") (.lit 0)) (.assign "cont" (.lit 1)) (.assign "cont" (.lit 0)))
    (.assign "cont" (.lit 0))

/-- **What `computeCont` computes**, walked by `run_vcg`. -/
theorem computeCont_run {σ : Env} (h1B : 1 < B) (hxB : σ.vars "x" < B)
    (hxeB : σ.vars "xe" < B) (hfB : σ.vars "found" < B) :
    ∃ σ' K, Run B computeCont σ σ' K ∧ K ≤ 10 ∧
      σ' = σ.setVar "cont" (if σ.vars "x" < σ.vars "xe" ∧ σ.vars "found" = 0 then 1 else 0) := by
  unfold computeCont
  run_vcg <;> (split_ifs with h <;> simp_all)

/-- **The row scan with early exit**: `cont := (x < xe ∧ found = 0); while cont = 1 do
(scanBody; cont := ...)`. -/
def scanRowEarly : Com :=
  .seq computeCont (.while (.eq (.var "cont") (.lit 1)) (.seq scanBody computeCont))

/-- The loop invariant of the early-exit scan. -/
def ScanLoopInv (x : List ℕ) (visB : ℕ → Prop) (l x₀ : ℕ) (σ : Env) : Prop :=
  ScanInv x visB l σ ∧
    σ.vars "cont" = (if σ.vars "x" < offw x (l + 1) ∧ σ.vars "found" = 0 then 1 else 0) ∧
    x₀ ≤ σ.vars "x"

/-- One turn of the early-exit loop moves `x` up by exactly one. -/
theorem scanLoop_step {x : List ℕ} {visB : ℕ → Prop} {l x₀ : ℕ} (hg : Good x)
    (hB : x.length + 8 ≤ B) (hl : l < nw x) {σ : Env} (hJ : ScanLoopInv x visB l x₀ σ)
    (hcont : σ.vars "cont" = 1) :
    ∃ σ' K, Run B (.seq scanBody computeCont) σ σ' K ∧ K ≤ 36 ∧
      ScanLoopInv x visB l x₀ σ' ∧ σ'.vars "x" = σ.vars "x" + 1 := by
  obtain ⟨hI, hc, hx0⟩ := hJ
  have hxlt : σ.vars "x" < offw x (l + 1) ∧ σ.vars "found" = 0 := by
    by_contra h; simp [h] at hc; omega
  obtain ⟨σ₁, K₁, hrun1, hK1, hI1, hx1⟩ := scanBody_run hg hB hl hI hxlt.1 hxlt.2
  have hoffB : offw x (l + 1) < B := by
    have := hg.off_lt_len (i := l + 1) (by have := hg.nV; omega); omega
  have hxB1 : σ₁.vars "x" < B := by have := hI1.xhi; omega
  have hxeB1 : σ₁.vars "xe" < B := by rw [hI1.xe]; exact hoffB
  have hfB1 : σ₁.vars "found" < B := by have := hI1.fle; omega
  obtain ⟨σ₂, K₂, hrun2, hK2, hσ₂⟩ := computeCont_run (σ := σ₁) (by omega) hxB1 hxeB1 hfB1
  have hxe1 := hI1.xe
  refine ⟨σ₂, K₁ + K₂, hrun1.seq hrun2, by omega, ⟨?_, ?_, ?_⟩, ?_⟩
  · subst hσ₂; exact hI1.setVar "cont" (by simp [scanReads]) _
  · subst hσ₂; simp [hxe1]
  · subst hσ₂; simp; omega
  · subst hσ₂; simp; omega

/-- **The early-exit row scan, with segment-sensitive cost.** Started with `found = 0`, it stops
at the first fresh candidate at or after `x`, or at the end of the row; it costs `40` per slot
swept plus `14`; it changes only `cont`, `x`, `found`, `foundJ`, `cand`. -/
theorem scanRowEarly_run {x : List ℕ} {visB : ℕ → Prop} {l : ℕ} (hg : Good x)
    (hB : x.length + 8 ≤ B) (hl : l < nw x) {σ : Env} (hI : ScanInv x visB l σ)
    (hf : σ.vars "found" = 0) :
    ∃ σ' K, Run B scanRowEarly σ σ' K ∧ ScanInv x visB l σ' ∧
      (σ'.vars "x" = offw x (l + 1) ∨ σ'.vars "found" = 1) ∧
      σ.vars "x" ≤ σ'.vars "x" ∧ K + 40 * σ.vars "x" ≤ 40 * σ'.vars "x" + 14 ∧
      (∀ y, y ∉ ["cont", "x", "found", "foundJ", "cand"] → σ'.vars y = σ.vars y) ∧
      (∀ b, σ'.arrs b = σ.arrs b) := by
  have h1B : 1 < B := by omega
  have hoffB : offw x (l + 1) < B := by
    have := hg.off_lt_len (i := l + 1) (by have := hg.nV; omega); omega
  have hxB : σ.vars "x" < B := by have := hI.xhi; omega
  have hxeB : σ.vars "xe" < B := by rw [hI.xe]; exact hoffB
  have hfB : σ.vars "found" < B := by have := hI.fle; omega
  obtain ⟨σ₁, K₁, hrun1, hK1, hσ₁⟩ := computeCont_run (σ := σ) h1B hxB hxeB hfB
  have hxe := hI.xe
  have hJ₁ : ScanLoopInv x visB l (σ.vars "x") σ₁ := by
    subst hσ₁
    refine ⟨hI.setVar "cont" (by simp [scanReads]) _, ?_, ?_⟩
    · simp [hxe]
    · simp
  have hloop := Run.while_potential (B := B) (b := .eq (.var "cont") (.lit 1))
    (c := .seq scanBody computeCont) (ScanLoopInv x visB l (σ.vars "x"))
    (fun τ => 40 * (offw x (l + 1) - τ.vars "x"))
    (fun τ hτ => by
      have hcB : τ.vars "cont" < B := by rw [hτ.2.1]; split <;> omega
      exact ⟨_, evalB_condEq (evalB_var hcB) (evalB_lit (n := 1) h1B)⟩)
    (fun τ hτ hb => by
      have hcB : τ.vars "cont" < B := by rw [hτ.2.1]; split <;> omega
      have hbtrue : τ.vars "cont" = 1 := by
        have heq := evalB_condEq (evalB_var hcB) (evalB_lit (n := 1) h1B)
        rw [hb] at heq
        simpa using heq.symm
      obtain ⟨τ', K, hrun, hK, hJ', hx'⟩ := scanLoop_step hg hB hl hτ hbtrue
      have hxle : τ'.vars "x" ≤ offw x (l + 1) := hJ'.1.xhi
      refine ⟨τ', K, hrun, hJ', ?_⟩
      simp only [size_condEq, size_var, size_lit]
      omega) hJ₁
  obtain ⟨σ', K₂, hrun2, hJ', hfalse, hpay⟩ := hloop
  have hxle₀ : σ.vars "x" ≤ offw x (l + 1) := hI.xhi
  have hx₁ : σ₁.vars "x" = σ.vars "x" := by subst hσ₁; simp
  have hxle' : σ'.vars "x" ≤ offw x (l + 1) := hJ'.1.xhi
  refine ⟨σ', K₁ + K₂, hrun1.seq hrun2, hJ'.1, ?_, hJ'.2.2, ?_, ?_, ?_⟩
  · have hcB'' : σ'.vars "cont" < B := by rw [hJ'.2.1]; split <;> omega
    have hbfalse : σ'.vars "cont" ≠ 1 := by
      have heq := evalB_condEq (evalB_var hcB'') (evalB_lit (n := 1) h1B)
      rw [hfalse] at heq
      intro hc; rw [hc] at heq; simp at heq
    by_contra hcon
    push Not at hcon
    have hxlt : σ'.vars "x" < offw x (l + 1) := by omega
    have hfle : σ'.vars "found" ≤ 1 := hJ'.1.fle
    have hf0 : σ'.vars "found" = 0 := by omega
    exact hbfalse (by rw [hJ'.2.1]; simp [hxlt, hf0])
  · simp only [size_condEq, size_var, size_lit] at hpay
    rw [hx₁] at hpay
    omega
  · intro y hy
    have h1 := hrun1.frame_var y (fun h => hy (by
      simp [computeCont, Com.wvars] at h; simp; tauto))
    have h2 := hrun2.frame_var y (fun h => hy (by
      simp [Com.wvars, scanBody, computeCont] at h; simp; tauto))
    rw [h2, h1]
  · intro b
    have h1 := hrun1.frame_arr b (by simp [computeCont, Com.warrs])
    have h2 := hrun2.frame_arr b (by simp [Com.warrs, scanBody, computeCont])
    rw [h2, h1]

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.Mu` -/

section
/-!
The matching array: the machine-level version of `Matching.μ : R → Option L`.

Right vertex `j`'s cell holds `0` if `j` is unmatched, or `l + 1` if `j` is matched to left
vertex `l` — shifting by one so `0` is free to mean "nothing here", the usual encoding for an
optional value in a word.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile

variable {B : ℕ}

/-- The `"mu"` array agrees with `μ`, encoding `none` as `0` and `some l` as `l + 1`, for every
right vertex below `m`. -/
def MuOK (μ : ℕ → Option ℕ) (m : ℕ) (σ : Env) : Prop :=
  (σ.arrs "mu").length = m ∧
    ∀ j < m, (σ.arrs "mu").getD j 0 = match μ j with | none => 0 | some l => l + 1

/-- Read `mu[j]` into `occ`, as the shifted encoding: `0` for unmatched, `l + 1` for `some l`. -/
def readMu (j occ : String) : Com := .assign occ (.get "mu" (.var j))

/-- Write `mu[j] := l + 1`, recording that right vertex `j` is now matched to left vertex `l`. -/
def writeMu (j l : String) : Com := .store "mu" (.var j) (.add (.var l) (.lit 1))

@[simp] theorem warrs_writeMu (j l : String) : (writeMu j l).warrs = ["mu"] := by
  simp [writeMu, Com.warrs]

/-- **Recording that `j` is now matched to `l`.** -/
theorem writeMu_spec {μ : ℕ → Option ℕ} {m j lv nB : ℕ} (h1B : 1 < B) (hmB : m < B)
    (hlB : lv + 1 < nB) (hnB : nB ≤ B) (hjm : j < m) (jn ln : String) :
    Spec B (fun σ => MuOK μ m σ ∧ σ.vars jn = j ∧ σ.vars ln = lv) (writeMu jn ln)
      (fun _ σ' => MuOK (Function.update μ j (some lv)) m σ') 5 := by
  intro σ ⟨⟨hlen, hval⟩, hjv, hlv⟩
  have hidxlt : j < (σ.arrs "mu").length := by omega
  have hjB : σ.vars jn < B := by omega
  have hlnB : σ.vars ln < B := by omega
  have hi : (Expr.var jn).evalB B σ = some j := by rw [evalB_var hjB, hjv]
  have hbop : Bop.add.apply (σ.vars ln) 1 = σ.vars ln + 1 := rfl
  have hget : (Expr.add (.var ln) (.lit 1)).evalB B σ = some (lv + 1) := by
    rw [show Expr.add (.var ln) (Expr.lit 1) = Expr.bin Bop.add (.var ln) (.lit 1) from rfl]
    rw [evalB_bin (evalB_var hlnB) (evalB_lit (n := 1) (by omega)) (by rw [hbop]; omega), hbop, hlv]
  have hst : Run B (writeMu jn ln) σ (σ.setArr "mu" j (lv + 1)) 5 :=
    Run.store hi hget hidxlt
  refine ⟨σ.setArr "mu" j (lv + 1), hst, ?_⟩
  constructor
  · simpa using hlen
  · intro k hk
    by_cases hkj : k = j
    · subst hkj
      simp [Function.update_self, List.getD_eq_getElem?_getD, hidxlt]
    · have := hval k hk
      simp [Function.update_of_ne hkj, List.getD_eq_getElem?_getD, Ne.symm hkj]
      rwa [← List.getD_eq_getElem?_getD]

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.SearchReal` -/

section
/-!
Tying the abstract search state `AS` to an IMP+ environment, and the straight-line phases of one
turn of the backtracking search.

Layout. Scalars: `top` (stack height), `result` (`2` = still searching, `1` = augmented, `0` = no
augmenting path), `t1 = top - 1`, `occ` (encoded occupant of the candidate), `k`/`rr`/`ll` (the
apply loop), the word's `V n m`, and the scan's `i x xe found foundJ cand cont`. Arrays: `a` (the
word), `vis`, `mu` (`0` = free, `l + 1` = matched to `l`), and the three parallel stacks `stkL`
(left vertex), `stkR` (chosen right vertex), `stkX` (resume slot), all of length `m + 1`.

`Real a σ` says the environment's arrays are exactly the abstract state's functions. Everything
about *correctness* lives in `SearchAbs`; this file only shows that the machine's stores realize
the abstract transitions `AS.choose`, `AS.push`, `AS.pop`.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching
open scoped Classical

variable {B : ℕ}

/-- **The environment realizes the abstract state.** -/
structure Real (x : List ℕ) (μ₀ : ℕ → Option ℕ) (a : AS) (σ : Env) : Prop where
  top : σ.vars "top" = a.top
  V : σ.vars "V" = Vw x
  n : σ.vars "n" = nw x
  m : σ.vars "m" = mw x
  arr : ArrOK x σ
  vis : VisOK a.visB (mw x) σ
  mu : MuOK μ₀ (mw x) σ
  stkL : σ.arrs "stkL" = arrOf (mw x + 1) a.Ls
  stkR : σ.arrs "stkR" = arrOf (mw x + 1) a.Rs
  stkX : σ.arrs "stkX" = arrOf (mw x + 1) a.Xs

/-- Everything fixed about a search: the word, the bound, the matching, the start vertex. -/
structure Ctx (B : ℕ) (x : List ℕ) (μ₀ : ℕ → Option ℕ) (l₀ : ℕ) : Prop where
  good : Good x
  hB : x.length + 8 ≤ B
  hl₀ : l₀ < nw x
  res : Respects (adjw x) μ₀
  inj : InjOnSupport μ₀
  unm : ¬ Matched μ₀ l₀
  hμn : ∀ j l, μ₀ j = some l → l < nw x
  supp : ∀ j l, μ₀ j = some l → j < mw x

theorem set_arrOf_update (n i v : ℕ) (f : ℕ → ℕ) :
    (arrOf n f).set i v = arrOf n (Function.update f i v) := by
  rw [set_arrOf]
  exact arrOf_congr (fun k _ => by simp [Function.update_apply])

section Access

variable {x : List ℕ} {μ₀ : ℕ → Option ℕ} {a : AS} {σ : Env}

theorem Real.getL (hR : Real x μ₀ a σ) {k : ℕ} (hk : k < mw x + 1) :
    (σ.arrs "stkL").getD k 0 = a.Ls k := by rw [hR.stkL]; exact getD_arrOf _ hk

theorem Real.getR (hR : Real x μ₀ a σ) {k : ℕ} (hk : k < mw x + 1) :
    (σ.arrs "stkR").getD k 0 = a.Rs k := by rw [hR.stkR]; exact getD_arrOf _ hk

theorem Real.getX (hR : Real x μ₀ a σ) {k : ℕ} (hk : k < mw x + 1) :
    (σ.arrs "stkX").getD k 0 = a.Xs k := by rw [hR.stkX]; exact getD_arrOf _ hk

theorem Real.lenL (hR : Real x μ₀ a σ) : (σ.arrs "stkL").length = mw x + 1 := by
  rw [hR.stkL]; simp

theorem Real.lenR (hR : Real x μ₀ a σ) : (σ.arrs "stkR").length = mw x + 1 := by
  rw [hR.stkR]; simp

theorem Real.lenX (hR : Real x μ₀ a σ) : (σ.arrs "stkX").length = mw x + 1 := by
  rw [hR.stkX]; simp

theorem Real.congr {σ' : Env} (hR : Real x μ₀ a σ)
    (ht : σ'.vars "top" = σ.vars "top") (hV : σ'.vars "V" = σ.vars "V")
    (hn : σ'.vars "n" = σ.vars "n") (hm : σ'.vars "m" = σ.vars "m")
    (ha : ∀ b, σ'.arrs b = σ.arrs b) : Real x μ₀ a σ' := by
  refine ⟨by rw [ht]; exact hR.top, by rw [hV]; exact hR.V, by rw [hn]; exact hR.n,
    by rw [hm]; exact hR.m, hR.arr.congr (ha _), hR.vis.congr (ha _), ?_, ?_, ?_, ?_⟩
  · unfold MuOK; rw [ha]; exact hR.mu
  · rw [ha]; exact hR.stkL
  · rw [ha]; exact hR.stkR
  · rw [ha]; exact hR.stkX

/-- Setting a scalar other than the four the realization reads keeps it. -/
theorem Real.setVar (hR : Real x μ₀ a σ) (y : String) (hy : y ∉ ["top", "V", "n", "m"]) (v : ℕ) :
    Real x μ₀ a (σ.setVar y v) :=
  hR.congr (by simp; rintro rfl; simp at hy) (by simp; rintro rfl; simp at hy)
    (by simp; rintro rfl; simp at hy) (by simp; rintro rfl; simp at hy) (fun _ => rfl)

theorem Real.pop {σ' : Env} (hR : Real x μ₀ a σ) (ht : σ'.vars "top" = a.top - 1)
    (hV : σ'.vars "V" = σ.vars "V") (hn : σ'.vars "n" = σ.vars "n")
    (hm : σ'.vars "m" = σ.vars "m") (ha : ∀ b, σ'.arrs b = σ.arrs b) :
    Real x μ₀ a.pop σ' := by
  refine ⟨ht, by rw [hV]; exact hR.V, by rw [hn]; exact hR.n, by rw [hm]; exact hR.m,
    hR.arr.congr (ha _), hR.vis.congr (ha _), ?_, ?_, ?_, ?_⟩
  · unfold MuOK; rw [ha]; exact hR.mu
  · rw [ha]; exact hR.stkL
  · rw [ha]; exact hR.stkR
  · rw [ha]; exact hR.stkX

theorem Real.withMu {μ' : ℕ → Option ℕ} {σ' : Env} (hR : Real x μ₀ a σ)
    (ht : σ'.vars "top" = σ.vars "top") (hV : σ'.vars "V" = σ.vars "V")
    (hn : σ'.vars "n" = σ.vars "n") (hm : σ'.vars "m" = σ.vars "m")
    (ha : ∀ b, b ≠ "mu" → σ'.arrs b = σ.arrs b) (hmu : MuOK μ' (mw x) σ') :
    Real x μ' a σ' := by
  refine ⟨by rw [ht]; exact hR.top, by rw [hV]; exact hR.V, by rw [hn]; exact hR.n,
    by rw [hm]; exact hR.m, hR.arr.congr (ha _ (by decide)), hR.vis.congr (ha _ (by decide)), hmu,
    ?_, ?_, ?_⟩
  · rw [ha _ (by decide)]; exact hR.stkL
  · rw [ha _ (by decide)]; exact hR.stkR
  · rw [ha _ (by decide)]; exact hR.stkX

end Access

/-! ### The phases of a turn -/

/-- Load the pending frame: `t1 := top - 1; i := stkL[t1]; x := stkX[t1]; xe := a[3 + i];
found := 0; foundJ := 0`. -/
def preludeCom : Com :=
  .seq (.assign "t1" (.sub (.var "top") (.lit 1)))
    (.seq (.assign "i" (.get "stkL" (.var "t1")))
      (.seq (.assign "x" (.get "stkX" (.var "t1")))
        (.seq (.assign "xe" (.get "a" (.add (.lit 3) (.var "i"))))
          (.seq (.assign "found" (.lit 0)) (.assign "foundJ" (.lit 0))))))

/-- The scan found nothing: pop the frame, and if it was the last, the search has failed. -/
def popCom : Com :=
  .seq (.assign "top" (.var "t1"))
    (.ite (.eq (.var "top") (.lit 0)) (.assign "result" (.lit 0)) .skip)

/-- The scan found `foundJ` at the slot before `x`: remember it, resume at `x`, mark it visited,
read its occupant. -/
def foundCom : Com :=
  .seq (.store "stkR" (.var "t1") (.var "foundJ"))
    (.seq (.store "stkX" (.var "t1") (.var "x"))
      (.seq (.store "vis" (.var "foundJ") (.lit 1)) (readMu "foundJ" "occ")))

/-- The candidate is occupied by `occ - 1`: push a frame for it, at the start of its row. -/
def pushCom : Com :=
  .seq (.store "stkL" (.var "top") (.sub (.var "occ") (.lit 1)))
    (.seq (.store "stkX" (.var "top") (.get "a" (.add (.lit 2) (.sub (.var "occ") (.lit 1)))))
      (.assign "top" (.add (.var "top") (.lit 1))))

/-- One iteration of the apply loop: `mu[stkR[k]] := stkL[k] + 1; k := k + 1`. -/
def applyBodyCom : Com :=
  .seq (.assign "rr" (.get "stkR" (.var "k")))
    (.seq (.assign "ll" (.get "stkL" (.var "k")))
      (.seq (writeMu "rr" "ll") (.assign "k" (.add (.var "k") (.lit 1)))))

/-- The candidate is free: write every frame's choice into `mu`, bottom to top. -/
def applyCom : Com :=
  .seq (.assign "k" (.lit 0)) (.while (.lt (.var "k") (.var "top")) applyBodyCom)

/-- The apply loop's invariant: the first `k` frames' choices are in `mu`. -/
def ApplyInv (x : List ℕ) (μ₀ : ℕ → Option ℕ) (b : AS) (σ : Env) : Prop :=
  Real x (applyN μ₀ b.Ls b.Rs (σ.vars "k")) b σ ∧ σ.vars "k" ≤ b.top

/-- What a turn does once the scan is done: pop if nothing was found, otherwise record the
candidate and either succeed (free) or push (occupied). -/
def afterScanCom : Com :=
  .ite (.eq (.var "found") (.lit 0)) popCom
    (.seq foundCom
      (.ite (.eq (.var "occ") (.lit 0)) (.seq applyCom (.assign "result" (.lit 1))) pushCom))

/-- **One turn of the search.** -/
def turnCom : Com := .seq preludeCom (.seq scanRowEarly afterScanCom)

/-- **The search**: turn until `result` leaves `2`. -/
def searchCom : Com := .while (.eq (.var "result") (.lit 2)) turnCom

/-! ### The phases, proved -/

section Phases

variable {x : List ℕ} {μ₀ : ℕ → Option ℕ} {l₀ : ℕ}

theorem offw_succ (x : List ℕ) (l : ℕ) : offw x (l + 1) = x.getD (3 + l) 0 := by
  unfold offw; congr 1; omega

theorem prelude_spec (ctx : Ctx B x μ₀ l₀) {a : AS} :
    Spec B (fun σ => Real x μ₀ a σ ∧ AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a) preludeCom
      (fun σ σ' => σ' = (((((σ.setVar "t1" (a.top - 1)).setVar "i" (a.Ls (a.top - 1))).setVar "x"
        (a.Xs (a.top - 1))).setVar "xe" (offw x (a.Ls (a.top - 1) + 1))).setVar "found" 0).setVar
        "foundJ" 0) 20 := by
  rintro σ ⟨hR, hI⟩
  have hg := ctx.good
  have hB := ctx.hB
  have hpos := hI.top_pos
  have hle : a.top ≤ mw x + 1 := top_le_succ hI
  have hk : a.top - 1 < mw x + 1 := by omega
  have hL := hR.getL hk
  have hX := hR.getX hk
  have hLn := hI.Lbd (a.top - 1) (by omega)
  have hXhi := hI.Xhi (a.top - 1) (by omega)
  have htop := hR.top
  have hlenL := hR.lenL
  have hlenX := hR.lenX
  have hlenA := hR.arr.length
  have hmB : mw x + 1 < B := by have := hg.m_lt; omega
  have htopB : a.top < B := by omega
  have hnB : nw x < B := by have := hg.n_lt; omega
  have hoffB : offw x (a.Ls (a.top - 1) + 1) < B := by
    have := hg.off_lt_len (i := a.Ls (a.top - 1) + 1) (by have := hg.nV; omega); omega
  have h3pos : 3 + a.Ls (a.top - 1) < x.length := by have := hg.len; have := hg.nV; omega
  have hXE : (σ.arrs "a").getD (3 + a.Ls (a.top - 1)) 0 = offw x (a.Ls (a.top - 1) + 1) := by
    rw [hR.arr.getD h3pos, offw_succ]
  rw [List.getD_eq_getElem?_getD] at hL hX hXE
  unfold preludeCom
  run_vcg
  all_goals (simp [htop, hL, hX, hXE]; try omega)

theorem pop_spec {a : AS} (h1B : 3 < B) (hbt : a.top ≤ mw x + 1) (hpos : 1 ≤ a.top)
    (hmB : mw x + 1 < B) :
    Spec B (fun σ => Real x μ₀ a σ ∧ σ.vars "result" = 2 ∧ σ.vars "t1" + 1 = a.top) popCom
      (fun _ σ' => Real x μ₀ a.pop σ' ∧ (a.top = 1 → σ'.vars "result" = 0) ∧
        (2 ≤ a.top → σ'.vars "result" = 2)) 8 := by
  rintro σ ⟨hR, hres, ht1⟩
  unfold popCom
  run_vcg
  · rename_i hc
    simp at hc
    refine ⟨hR.pop (by simp; omega) (by simp) (by simp) (by simp) (by simp), fun _ => by simp,
      fun h => by omega⟩
  · rename_i hc
    simp at hc
    refine ⟨hR.pop (by simp; omega) (by simp) (by simp) (by simp) (by simp), fun h => by omega,
      fun _ => by simp [hres]⟩

theorem found_spec {a : AS} {j xv : ℕ} (h1B : 3 < B) (hbt : a.top ≤ mw x + 1) (hpos : 1 ≤ a.top)
    (hmB : mw x + 1 < B) (hjm : j < mw x) (hμB : ∀ l, μ₀ j = some l → l + 1 < nw x + 1)
    (hnB : nw x + 1 ≤ B) (hxB : xv < B) :
    Spec B (fun σ => Real x μ₀ a σ ∧ σ.vars "t1" + 1 = a.top ∧ σ.vars "foundJ" = j ∧
        σ.vars "x" = xv)
      foundCom
      (fun σ σ' => σ' = (((σ.setArr "stkR" (a.top - 1) j).setArr "stkX" (a.top - 1) xv).setArr
        "vis" j 1).setVar "occ" (match μ₀ j with | none => 0 | some l => l + 1)) 14 := by
  rintro σ ⟨hR, ht1, hjv, hxv⟩
  have hlenR := hR.lenR
  have hlenX := hR.lenX
  have hmu := hR.mu
  have hvis := hR.vis
  have hvislen : (σ.arrs "vis").length = mw x := hvis.length
  have hmuv : (σ.arrs "mu").getD j 0 = (match μ₀ j with | none => 0 | some l => l + 1) :=
    hmu.2 j hjm
  have hmulen : (σ.arrs "mu").length = mw x := hmu.1
  have hoccB : (match μ₀ j with | none => 0 | some l => l + 1) < B := by
    rcases hμ : μ₀ j with _ | l
    · show 0 < B; omega
    · show l + 1 < B; have := hμB l hμ; omega
  rw [List.getD_eq_getElem?_getD] at hmuv
  have ht1' : σ.vars "t1" = a.top - 1 := by omega
  unfold foundCom readMu
  run_vcg
  all_goals (simp [ht1', hjv, hxv, hmuv]; try omega)

theorem Real.found {a : AS} {σ : Env} {s j : ℕ} (hR : Real x μ₀ a σ) (occv : ℕ) :
    Real x μ₀ (a.choose s j)
      ((((σ.setArr "stkR" (a.top - 1) j).setArr "stkX" (a.top - 1) (s + 1)).setArr "vis" j 1).setVar
        "occ" occv) := by
  refine ⟨by simpa [AS.choose] using hR.top, by simpa using hR.V, by simpa using hR.n,
    by simpa using hR.m, hR.arr.congr (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · unfold VisOK
    simp only [arrs_setVar, arrs_setArr]
    simp
    rw [hR.vis, set_arrOf_update]
    exact arrOf_congr (fun k hk => by
      simp [Function.update_apply, AS.choose]; try split_ifs <;> simp_all)
  · simpa [MuOK] using hR.mu
  · simpa [AS.choose] using hR.stkL
  · simp [hR.stkR, set_arrOf_update, AS.choose]
  · simp [hR.stkX, set_arrOf_update, AS.choose]

theorem push_spec (hg : Good x) (hB : x.length + 8 ≤ B) {b : AS} {l' : ℕ} (h1B : 3 < B)
    (hbt : b.top ≤ mw x) (hmB : mw x + 1 < B) (hnB : nw x + 2 ≤ B) (hl' : l' < nw x) :
    Spec B (fun σ => Real x μ₀ b σ ∧ σ.vars "occ" = l' + 1) pushCom
      (fun σ σ' => σ' = ((σ.setArr "stkL" b.top l').setArr "stkX" b.top (offw x l')).setVar "top"
        (b.top + 1)) 18 := by
  rintro σ ⟨hR, hocc⟩
  have hlenL := hR.lenL
  have hlenX := hR.lenX
  have hlenA := hR.arr.length
  have htop := hR.top
  have h2pos : 2 + l' < x.length := hg.offPos_lt (by have := hg.nV; omega)
  have hoff : (σ.arrs "a").getD (2 + l') 0 = offw x l' := hR.arr.getD h2pos
  have hoffB : offw x l' < B := by
    have := hg.off_lt_len (i := l') (by have := hg.nV; omega); omega
  rw [List.getD_eq_getElem?_getD] at hoff
  unfold pushCom
  run_vcg
  all_goals (simp [htop, hocc, hoff]; try omega)

theorem Real.push {b : AS} {σ : Env} {l' : ℕ} (hR : Real x μ₀ b σ) :
    Real x μ₀ (b.push (offw x) l')
      (((σ.setArr "stkL" b.top l').setArr "stkX" b.top (offw x l')).setVar "top" (b.top + 1)) := by
  refine ⟨by simp [AS.push], by simpa using hR.V, by simpa using hR.n, by simpa using hR.m,
    hR.arr.congr (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · unfold VisOK
    simp only [arrs_setVar, arrs_setArr]
    simp
    exact hR.vis
  · simpa [MuOK] using hR.mu
  · simp [hR.stkL, set_arrOf_update, AS.push]
  · simpa [AS.push] using hR.stkR
  · simp [hR.stkX, set_arrOf_update, AS.push]

theorem applyBody_spec {b : AS} (h1B : 3 < B) (hbt : b.top ≤ mw x + 1) (hmB : mw x + 1 < B)
    (hnB : nw x + 2 ≤ B) (hRb : ∀ k < b.top, b.Rs k < mw x) (hLb : ∀ k < b.top, b.Ls k < nw x) :
    Spec B (fun σ => ApplyInv x μ₀ b σ ∧ σ.vars "k" < b.top) applyBodyCom
      (fun σ σ' => ApplyInv x μ₀ b σ' ∧ σ'.vars "k" = σ.vars "k" + 1) 15 := by
  rintro σ ⟨⟨hR, hkt⟩, hk⟩
  have hk' : σ.vars "k" < mw x + 1 := by omega
  have hRk := hR.getR hk'
  have hLk := hR.getL hk'
  have hRkm := hRb _ hk
  have hLkn := hLb _ hk
  have hlenR := hR.lenR
  have hlenL := hR.lenL
  rw [List.getD_eq_getElem?_getD] at hRk hLk
  unfold applyBodyCom
  run_vcg [(writeMu_spec (B := B) (μ := applyN μ₀ b.Ls b.Rs (σ.vars "k")) (m := mw x)
    (j := b.Rs (σ.vars "k")) (lv := b.Ls (σ.vars "k")) (nB := nw x + 1) (by omega) (by omega)
    (by omega) (by omega) hRkm "rr" "ll").frame]
  · rename_i w hw
    obtain ⟨hmu, hv, ha, -, -⟩ := hw
    have hv' : ∀ y, w.vars y = ((σ.setVar "rr" ((σ.arrs "stkR").getD (σ.vars "k") 0)).setVar "ll"
        (((σ.setVar "rr" ((σ.arrs "stkR").getD (σ.vars "k") 0)).arrs "stkL").getD
          ((σ.setVar "rr" ((σ.arrs "stkR").getD (σ.vars "k") 0)).vars "k") 0)).vars y :=
      fun y => hv y (by simp [writeMu, Com.wvars])
    have ha' : ∀ c, c ≠ "mu" → w.arrs c = σ.arrs c := fun c hc => by
      have := ha c (by simp [warrs_writeMu, hc]); simpa using this
    refine ⟨⟨hR.withMu (σ' := w.setVar "k" (w.vars "k" + 1)) ?_ ?_ ?_ ?_
      (fun c hc => by simpa using ha' c hc) ?_, ?_⟩, ?_⟩
    · simp [hv']
    · simp [hv']
    · simp [hv']
    · simp [hv']
    · have hk1 : (w.setVar "k" (w.vars "k" + 1)).vars "k" = σ.vars "k" + 1 := by simp [hv']
      rw [hk1]
      show MuOK (Function.update (applyN μ₀ b.Ls b.Rs (σ.vars "k")) (b.Rs (σ.vars "k"))
        (some (b.Ls (σ.vars "k")))) (mw x) _
      simpa [MuOK] using hmu
    · simp [hv']; omega
    · simp [hv']
  · refine ⟨by simpa [MuOK] using hR.mu, by simp [hRk], by simp [hLk]⟩
  all_goals
    rename_i w hw
    have hwk := hw.2.1 "k" (by simp [writeMu, Com.wvars])
    simp at hwk
    omega

/-- **The apply loop writes every frame's choice into `mu`.** -/
theorem apply_spec {b : AS} (h1B : 3 < B) (hbt : b.top ≤ mw x + 1) (hmB : mw x + 1 < B)
    (hnB : nw x + 2 ≤ B) (hRb : ∀ k < b.top, b.Rs k < mw x) (hLb : ∀ k < b.top, b.Ls k < nw x) :
    Spec B (fun σ => Real x μ₀ b σ) applyCom
      (fun _ σ' => Real x (applyN μ₀ b.Ls b.Rs b.top) b σ') (19 * b.top + 6) := by
  have hloop := Spec.forRangeZero (B := B) (c := applyBodyCom) "k" "top"
    (ApplyInv x μ₀ b) b.top 15 (by omega) (fun σ hσ => hσ.2) (fun σ hσ => hσ.1.top)
    (applyBody_spec h1B hbt hmB hnB hRb hLb)
  refine (hloop.conseq ?_ ?_ (by omega))
  · intro σ hσ
    refine ⟨?_, by simp⟩
    have := hσ.setVar "k" (by simp) 0
    simpa [applyN] using this
  · intro σ σ' _ h
    obtain ⟨⟨hR, -⟩, hk⟩ := h
    rwa [hk] at hR

end Phases

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.Pot` -/

section
/-!
The potential of the search, and what each kind of turn does to it.

One turn's machine cost is paid out of `AS.pot`. It counts the scan work still to come on each
live frame (`off (Ls k + 1) - Xs k` slots, at 40 per slot), a flat charge `potD` per live frame,
and a charge per still-unvisited right vertex `j`: `40 * occLen j + potW`, where `occLen j` is
the length of the row of the left vertex currently holding `j` (zero if `j` is free). Visiting
`j` releases exactly what pushing a frame for its occupant costs — the scan of that occupant's
row — so the search's total cost is linear in `rowlen l₀ + Σ_j occLen j + m`, and the occupant
sum is at most the total row length of the left side, since the matching is injective.

The successful turn ends the loop, so its ghost successor state is the zero-potential `AS.done`;
its cost is paid out of the pending frame's scan share, the flat charges, and the released
vertex's charge, which is `pot_success`.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching

/-- Flat charge per live frame. -/
def potD : ℕ := 100

/-- Flat charge per unvisited right vertex. -/
def potW : ℕ := 300

/-- The row length of the occupant of a right vertex (zero if free). -/
def occLen (off : ℕ → ℕ) (μ₀ : ℕ → Option ℕ) (j : ℕ) : ℕ :=
  match μ₀ j with
  | none => 0
  | some l => rowlen off l

/-- The charge of an unvisited right vertex. -/
def potJ (off : ℕ → ℕ) (μ₀ : ℕ → Option ℕ) (j : ℕ) : ℕ := 40 * occLen off μ₀ j + potW

open Classical in
/-- **The potential.** -/
noncomputable def AS.pot (off : ℕ → ℕ) (μ₀ : ℕ → Option ℕ) (m : ℕ) (a : AS) : ℕ :=
  40 * (∑ k ∈ Finset.range a.top, (off (a.Ls k + 1) - a.Xs k)) + potD * a.top +
    ∑ j ∈ (Finset.range m).filter (fun j => ¬ a.visB j), potJ off μ₀ j

section Pot

variable {off tgt : ℕ → ℕ} {μ₀ : ℕ → Option ℕ} {n m l₀ : ℕ} {a : AS} {s j l' : ℕ}

open Classical in
theorem AS.done_pot : (AS.done).pot off μ₀ m = 0 := by
  unfold AS.pot AS.done
  simp

/-- **Popping a frame releases its share.** -/
theorem pot_pop (a : AS) (h : 1 ≤ a.top) :
    a.pot off μ₀ m = a.pop.pot off μ₀ m + (40 * (off (a.Ls (a.top - 1) + 1) - a.Xs (a.top - 1)) +
      potD) := by
  have e2 : a.pop.top = a.top - 1 := rfl
  have e3 : a.pop.Xs = a.Xs := rfl
  have e4 : a.pop.Ls = a.Ls := rfl
  have e5 : a.pop.visB = a.visB := rfl
  unfold AS.pot
  rw [e2, e3, e4, e5]
  obtain ⟨t, ht⟩ : ∃ t, a.top = t + 1 := ⟨a.top - 1, by omega⟩
  rw [ht, Nat.add_sub_cancel, Finset.sum_range_succ]
  have hD := mul_add_one potD t
  omega

open Classical in
/-- The unvisited set after choosing `j` is the old one without `j`. -/
theorem filter_choose (a : AS) (s j : ℕ) :
    (Finset.range m).filter (fun r => ¬ (a.choose s j).visB r) =
      ((Finset.range m).filter (fun r => ¬ a.visB r)).erase j := by
  ext r
  rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
  show r < m ∧ ¬ (r = j ∨ a.visB r) ↔ r ≠ j ∧ r < m ∧ ¬ a.visB r
  constructor
  · rintro ⟨hr, h⟩
    push Not at h
    exact ⟨h.1, hr, h.2⟩
  · rintro ⟨h1, hr, h2⟩
    exact ⟨hr, fun h => h.elim h1 h2⟩

open Classical in
theorem sum_choose (a : AS) (s : ℕ) (hj : j < m) (hfresh : ¬ a.visB j) :
    ∑ r ∈ (Finset.range m).filter (fun r => ¬ a.visB r), potJ off μ₀ r =
      potJ off μ₀ j + ∑ r ∈ (Finset.range m).filter (fun r => ¬ (a.choose s j).visB r),
        potJ off μ₀ r := by
  rw [filter_choose, Finset.add_sum_erase]
  simp [hj, hfresh]

open Classical in
/-- **The successful turn is paid for**: the pending frame's scan share up to the found slot, the
flat charges, and the released vertex's charge are all in the potential. -/
theorem pot_success (hI : AbsInv off tgt μ₀ n m l₀ a) (hF : Found off tgt n m a s j) :
    40 * (s + 1 - a.Xs (a.top - 1)) + potD * a.top + potW ≤ a.pot off μ₀ m := by
  have hpos := hI.top_pos
  have hhi := hF.hi
  unfold AS.pot
  have h1 : off (a.Ls (a.top - 1) + 1) - a.Xs (a.top - 1) ≤
      ∑ k ∈ Finset.range a.top, (off (a.Ls k + 1) - a.Xs k) :=
    Finset.single_le_sum (f := fun k => off (a.Ls k + 1) - a.Xs k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (by omega))
  have h2 : potJ off μ₀ j ≤ ∑ r ∈ (Finset.range m).filter (fun r => ¬ a.visB r), potJ off μ₀ r :=
    Finset.single_le_sum (f := potJ off μ₀) (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.2 ⟨Finset.mem_range.2 hF.lt, hF.fresh⟩)
  have h3 : potW ≤ potJ off μ₀ j := by unfold potJ; omega
  have h4 : s + 1 - a.Xs (a.top - 1) ≤ off (a.Ls (a.top - 1) + 1) - a.Xs (a.top - 1) := by omega
  have h5 := Nat.mul_le_mul_left 40 (h4.trans h1)
  omega

open Classical in
/-- **Choosing a candidate and pushing a frame for its occupant** is paid for by the pending
frame's scan share up to the found slot and the released vertex's flat charge, minus the new
frame's flat charge. -/
theorem pot_push (hI : AbsInv off tgt μ₀ n m l₀ a) (hF : Found off tgt n m a s j)
    (hocc : μ₀ j = some l') :
    a.pot off μ₀ m + potD =
      ((a.choose s j).push off l').pot off μ₀ m + 40 * (s + 1 - a.Xs (a.top - 1)) + potW := by
  have hpos := hI.top_pos
  have hge := hF.ge hI
  have hhi := hF.hi
  have hsum := sum_choose (off := off) (μ₀ := μ₀) a s hF.lt hF.fresh
  have e1 : ((a.choose s j).push off l').visB = (a.choose s j).visB := rfl
  have e2 : ((a.choose s j).push off l').top = a.top + 1 := rfl
  have hJ : potJ off μ₀ j = 40 * rowlen off l' + potW := by
    unfold potJ occLen; rw [hocc]
  unfold AS.pot
  rw [e1, e2, hsum, hJ]
  obtain ⟨t, ht⟩ : ∃ t, a.top = t + 1 := ⟨a.top - 1, by omega⟩
  have hXs : ((a.choose s j).push off l').Xs =
      Function.update (Function.update a.Xs t (s + 1)) (t + 1) (off l') := by
    show Function.update (Function.update a.Xs (a.top - 1) (s + 1)) a.top (off l') = _
    rw [ht, Nat.add_sub_cancel]
  have hLs : ((a.choose s j).push off l').Ls = Function.update a.Ls (t + 1) l' := by
    show Function.update a.Ls a.top l' = _
    rw [ht]
  rw [hXs, hLs, ht]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  have hcongr : ∑ k ∈ Finset.range t, (off (Function.update a.Ls (t + 1) l' k + 1) -
      Function.update (Function.update a.Xs t (s + 1)) (t + 1) (off l') k) =
      ∑ k ∈ Finset.range t, (off (a.Ls k + 1) - a.Xs k) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' := Finset.mem_range.mp hk
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  rw [hcongr]
  simp only [Function.update_self, Function.update_of_ne (show t ≠ t + 1 by omega),
    Nat.add_sub_cancel]
  rw [ht, Nat.add_sub_cancel] at hge hhi
  have hD := mul_add_one potD (t + 1)
  have hD' := mul_add_one potD t
  unfold rowlen
  have hX : a.Xs t ≤ s + 1 := by omega
  omega

end Pot

/-! ### The potential of a restarted search -/

section Restart

variable {off : ℕ → ℕ} {μ₀ : ℕ → Option ℕ} {n m : ℕ}

open Classical in
theorem AS.restart_pot (b : AS) (l₀ : ℕ) :
    (AS.restart off b l₀).pot off μ₀ m =
      40 * rowlen off l₀ + potD + ∑ j ∈ Finset.range m, potJ off μ₀ j := by
  unfold AS.pot
  have h1 : (AS.restart off b l₀).top = 1 := rfl
  have hf : (Finset.range m).filter (fun j => ¬ (AS.restart off b l₀).visB j) = Finset.range m := by
    ext r; simp [AS.restart]
  rw [h1, hf, Finset.sum_range_one]
  simp [AS.restart, rowlen]

theorem sum_potJ (off : ℕ → ℕ) (μ₀ : ℕ → Option ℕ) (m : ℕ) :
    ∑ j ∈ Finset.range m, potJ off μ₀ j =
      40 * ∑ j ∈ Finset.range m, occLen off μ₀ j + potW * m := by
  unfold potJ
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

/-- **The occupants' rows are distinct rows of the left side**, so their lengths sum to at most
the total row length of the left side. -/
theorem sum_occLen_le (hinj : InjOnSupport μ₀) (hbd : ∀ j l, μ₀ j = some l → l < n) :
    ∑ j ∈ Finset.range m, occLen off μ₀ j ≤ ∑ l ∈ Finset.range n, rowlen off l := by
  classical
  set s := (Finset.range m).filter (fun j => (μ₀ j).isSome) with hs
  set g : ℕ → ℕ := fun j => (μ₀ j).getD 0 with hg
  have h1 : ∑ j ∈ Finset.range m, occLen off μ₀ j = ∑ j ∈ s, rowlen off (g j) := by
    rw [hs, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold occLen
    rcases hμ : μ₀ j with _ | l <;> simp [hg, hμ]
  have h2 : ∑ j ∈ s, rowlen off (g j) = ∑ l ∈ s.image g, rowlen off l := by
    rw [Finset.sum_image]
    intro j hj j' hj' he
    have hj1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).2
    have hj2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hj')).2
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hj1
    obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.1 hj2
    simp only [hg, hl, hl', Option.getD_some] at he
    subst he
    exact hinj j j' l hl hl'
  have h3 : s.image g ⊆ Finset.range n := by
    intro l hl
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hl
    obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.1 (Finset.mem_filter.1 hj).2
    simp only [hg, hl', Option.getD_some]
    exact Finset.mem_range.2 (hbd j l' hl')
  rw [h1, h2]
  exact Finset.sum_le_sum_of_subset h3

/-- The rows of the left side, laid end to end, end at `off n`. -/
theorem sum_rowlen_le (off : ℕ → ℕ) (n : ℕ) (hmono : ∀ l < n, off l ≤ off (l + 1)) :
    ∑ l ∈ Finset.range n, rowlen off l ≤ off n := by
  have key : ∀ k ≤ n, ∑ l ∈ Finset.range k, rowlen off l + off 0 = off k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ]
      have h1 := ih (by omega)
      have h2 := hmono k (by omega)
      have h3 : rowlen off k = off (k + 1) - off k := rfl
      omega
  have := key n le_rfl
  omega

/-- **A restarted search's potential is linear in the row lengths and `m`.** -/
theorem restart_pot_le (b : AS) (l₀ : ℕ) (hinj : InjOnSupport μ₀)
    (hbd : ∀ j l, μ₀ j = some l → l < n) (hmono : ∀ l < n, off l ≤ off (l + 1)) {R : ℕ}
    (hR : off n ≤ R) (hl₀ : rowlen off l₀ ≤ R) :
    (AS.restart off b l₀).pot off μ₀ m ≤ 80 * R + potD + potW * m := by
  rw [AS.restart_pot, sum_potJ]
  have h1 := sum_occLen_le (off := off) (m := m) hinj hbd
  have h2 := sum_rowlen_le off n hmono
  have h3 := Nat.mul_le_mul_left 40 (h1.trans (h2.trans hR))
  have h4 := Nat.mul_le_mul_left 40 hl₀
  omega

end Restart

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.SearchTurn` -/

section
/-!
The three kinds of turn — **pop** (the scan found nothing), **success** (the scan found a free
right vertex) and **push** (it found an occupied one) — each proved to run `afterScanCom` from a
finished scan to a state satisfying the search's loop invariant `LoopInv`, at a cost paid by the
drop in the potential `AS.pot`.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching
open scoped Classical

variable {B : ℕ}

/-- Applying frames whose right vertices are below `m` keeps the support below `m`. -/
theorem applyN_supp {μ : ℕ → Option ℕ} {Ls Rs : ℕ → ℕ} {m : ℕ}
    (hμ : ∀ j l, μ j = some l → j < m) :
    ∀ t, (∀ k < t, Rs k < m) → ∀ j l, applyN μ Ls Rs t j = some l → j < m
  | 0, _, j, l, h => hμ j l h
  | t + 1, hR, j, l, h => by
      have h' : Function.update (applyN μ Ls Rs t) (Rs t) (some (Ls t)) j = some l := h
      by_cases hj : j = Rs t
      · subst hj; exact hR _ (by omega)
      · rw [Function.update_of_ne hj] at h'
        exact applyN_supp hμ t (fun k hk => hR k (by omega)) j l h'

/-- **The search has succeeded**: `mu` holds a `GoodResult` (with the stacks and the visited
table still standing in `b`), whose support is below `m`. -/
def Done1 (x : List ℕ) (μ₀ : ℕ → Option ℕ) (l₀ : ℕ) (σ : Env) : Prop :=
  σ.vars "result" = 1 ∧ ∃ (b : AS) (μ' : ℕ → Option ℕ), Real x μ' b σ ∧
    GoodResult (adjw x) μ₀ ∅ l₀ μ' ∧ ∀ j l, μ' j = some l → j < mw x

/-- **The search has failed**: the visited set certifies that no augmenting path exists. -/
def Done0 (x : List ℕ) (μ₀ : ℕ → Option ℕ) (l₀ : ℕ) (σ : Env) : Prop :=
  σ.vars "result" = 0 ∧ ∃ b : AS, Real x μ₀ b σ ∧ FailCert (adjw x) μ₀ (mw x) l₀ b.visB

/-- **The invariant of the search loop**: still searching from a well-formed state `a`, or done. -/
def LoopInv (x : List ℕ) (μ₀ : ℕ → Option ℕ) (l₀ : ℕ) (a : AS) (σ : Env) : Prop :=
  (σ.vars "result" = 2 ∧ Real x μ₀ a σ ∧ AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a) ∨
    Done1 x μ₀ l₀ σ ∨ Done0 x μ₀ l₀ σ

/-- **A finished scan.** -/
structure PostScan (x : List ℕ) (μ₀ : ℕ → Option ℕ) (a : AS) (σ : Env) : Prop where
  real : Real x μ₀ a σ
  res : σ.vars "result" = 2
  t1 : σ.vars "t1" + 1 = a.top
  scan : ScanInv x a.visB (a.Ls (a.top - 1)) σ
  stop : σ.vars "x" = offw x (a.Ls (a.top - 1) + 1) ∨ σ.vars "found" = 1

section Turns

variable {x : List ℕ} {μ₀ : ℕ → Option ℕ} {l₀ : ℕ} {a : AS} {σ : Env}

/-- A scan that found something names a `Found`, at the slot before `x`. -/
theorem PostScan.found (hg : Good x) (hI : AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a)
    (hP : PostScan x μ₀ a σ) (hf : σ.vars "found" = 1) :
    Found (offw x) (tgtw x) (nw x) (mw x) a (σ.vars "x" - 1) (σ.vars "foundJ") ∧
      1 ≤ σ.vars "x" := by
  have hpos := hI.top_pos
  have hLn := hI.Lbd (a.top - 1) (by omega)
  have hxhi := hP.scan.xhi
  rcases hP.scan.cases with ⟨h0, -⟩ | ⟨-, hlt, htg, hfresh, hslots⟩
  · omega
  · refine ⟨⟨by omega, by omega, htg, ?_, hfresh, hslots⟩, by omega⟩
    have hsV : σ.vars "x" - 1 < offw x (Vw x) := hg.slot_lt hLn (by omega)
    have := hg.tgt_lt _ hsV
    unfold mw; omega

/-- A scan that found nothing has closed the pending frame's row. -/
theorem PostScan.closed (hP : PostScan x μ₀ a σ) (hf : σ.vars "found" = 0) :
    Cl (adjOff (offw x) (tgtw x) (nw x)) a.visB (mw x) (a.Ls (a.top - 1)) := by
  have hx : σ.vars "x" = offw x (a.Ls (a.top - 1) + 1) := by
    rcases hP.stop with h | h
    · exact h
    · omega
  rcases hP.scan.cases with ⟨-, hslots⟩ | ⟨h1, -⟩
  · rintro j _ ⟨s, hlo, hhi, ht⟩
    exact hslots s hlo (by omega) j ht
  · omega

/-- **Pop**: the scan found nothing, so the frame is exhausted. -/
theorem turn_pop (ctx : Ctx B x μ₀ l₀) (hI : AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a)
    (hP : PostScan x μ₀ a σ) (hf : σ.vars "found" = 0) {K₀ : ℕ}
    (hK₀ : K₀ + 40 * a.Xs (a.top - 1) ≤ 40 * offw x (a.Ls (a.top - 1) + 1) + 34) :
    ∃ a' σ' K, Run B afterScanCom σ σ' K ∧ LoopInv x μ₀ l₀ a' σ' ∧
      K₀ + K + 4 + a'.pot (offw x) μ₀ (mw x) ≤ a.pot (offw x) μ₀ (mw x) := by
  have hg := ctx.good
  have hB := ctx.hB
  have hpos := hI.top_pos
  have hle := top_le_succ hI
  have hmB : mw x + 1 < B := by have := hg.m_lt; omega
  have hcl := hP.closed hf
  obtain ⟨σ', hrun, hQ⟩ := (pop_spec (x := x) (μ₀ := μ₀) (by omega) hle hpos hmB).run
    ⟨hP.real, hP.res, hP.t1⟩
  have hfB : σ.vars "found" < B := by have := hP.scan.fle; omega
  have hcond : (Cond.eq (.var "found") (.lit 0)).evalB B σ = some true := by
    rw [evalB_condEq (evalB_var hfB) (evalB_lit (by omega)), hf]; simp
  refine ⟨a.pop, σ', _, Run.ite_true hcond hrun, ?_, ?_⟩
  · by_cases h1 : a.top = 1
    · exact Or.inr (Or.inr ⟨hQ.2.1 h1, a.pop, hQ.1, hI.failCert hcl h1⟩)
    · exact Or.inl ⟨hQ.2.2 (by omega), hQ.1, hI.pop hcl (by omega)⟩
  · have hX := hI.Xhi (a.top - 1) (by omega)
    have := pot_pop (off := offw x) (μ₀ := μ₀) (m := mw x) a hpos
    simp only [size_condEq, size_var, size_lit, potD] at *
    omega

/-- **Success**: the scan found a free right vertex; every frame's choice goes into `mu`. -/
theorem turn_success (ctx : Ctx B x μ₀ l₀) (hI : AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a)
    (hP : PostScan x μ₀ a σ) (hf : σ.vars "found" = 1)
    (hfree : μ₀ (σ.vars "foundJ") = none) {K₀ : ℕ}
    (hK₀ : K₀ + 40 * a.Xs (a.top - 1) ≤ 40 * σ.vars "x" + 34) :
    ∃ a' σ' K, Run B afterScanCom σ σ' K ∧ LoopInv x μ₀ l₀ a' σ' ∧
      K₀ + K + 4 + a'.pot (offw x) μ₀ (mw x) ≤ a.pot (offw x) μ₀ (mw x) := by
  have hg := ctx.good
  have hB := ctx.hB
  obtain ⟨hF, hx1⟩ := hP.found hg hI hf
  set j := σ.vars "foundJ" with hj
  set s := σ.vars "x" - 1 with hs
  have hxs : σ.vars "x" = s + 1 := by omega
  have hpos := hI.top_pos
  have hle := top_le_succ hI
  have hmB : mw x + 1 < B := by have := hg.m_lt; omega
  have hnB : nw x + 2 ≤ B := by have := hg.n_lt; omega
  have hxB : σ.vars "x" < B := by
    have := hP.scan.xhi
    have := hg.off_lt_len (i := a.Ls (a.top - 1) + 1) (by have := hI.Lbd (a.top - 1) (by omega); have := hg.nV; omega)
    omega
  -- record the candidate
  obtain ⟨σ₃, hrun3, hQ3⟩ := (found_spec (x := x) (μ₀ := μ₀) (a := a) (j := j) (xv := σ.vars "x")
    (by omega) hle hpos hmB hF.lt (fun l hl => by have := ctx.hμn j l hl; omega)
    (by omega) hxB).run ⟨hP.real, hP.t1, rfl, rfl⟩
  rw [hxs] at hQ3
  subst hQ3
  have hR3 := hP.real.found (s := s) (j := j) (match μ₀ j with | none => 0 | some l => l + 1)
  have hocc : ((((σ.setArr "stkR" (a.top - 1) j).setArr "stkX" (a.top - 1) (s + 1)).setArr
      "vis" j 1).setVar "occ" (match μ₀ j with | none => 0 | some l => l + 1)).vars "occ" = 0 := by
    simp [hfree]
  set σ3 := ((((σ.setArr "stkR" (a.top - 1) j).setArr "stkX" (a.top - 1) (s + 1)).setArr
      "vis" j 1).setVar "occ" (match μ₀ j with | none => 0 | some l => l + 1)) with hσ3
  have hRb : ∀ k < (a.choose s j).top, (a.choose s j).Rs k < mw x := by
    intro k hk
    show Function.update a.Rs (a.top - 1) j k < mw x
    by_cases hk1 : k = a.top - 1
    · rw [hk1, Function.update_self]; exact hF.lt
    · rw [Function.update_of_ne hk1]
      exact (hI.Rvis k (by have : k < a.top := hk; omega)).1
  have hLb : ∀ k < (a.choose s j).top, (a.choose s j).Ls k < nw x := fun k hk => hI.Lbd k hk
  obtain ⟨σ₄, hrun4, hQ4⟩ := (apply_spec (x := x) (μ₀ := μ₀) (by omega)
    (b := a.choose s j) hle hmB hnB hRb hLb).run hR3
  have hres1 : (1 : ℕ) < B := by omega
  have hrun5 := Run.assign (B := B) (σ := σ₄) (x := "result") (e := .lit 1) (v := 1)
    (evalB_lit hres1)
  have hoccB : σ3.vars "occ" < B := by rw [hocc]; omega
  have hcond : (Cond.eq (.var "occ") (.lit 0)).evalB B σ3 = some true := by
    rw [evalB_condEq (evalB_var hoccB) (evalB_lit (by omega)), hocc]; simp
  have hfB : σ.vars "found" < B := by have := hP.scan.fle; omega
  have hcond0 : (Cond.eq (.var "found") (.lit 0)).evalB B σ = some false := by
    rw [evalB_condEq (evalB_var hfB) (evalB_lit (by omega)), hf]; simp
  refine ⟨AS.done, σ₄.setVar "result" 1, _,
    Run.ite_false hcond0 (hrun3.seq (Run.ite_true hcond (hrun4.seq hrun5))), ?_, ?_⟩
  · refine Or.inr (Or.inl ⟨by simp, a.choose s j, _,
      hQ4.congr (by simp) (by simp) (by simp) (by simp) (by simp), ?_, ?_⟩)
    · exact hI.success ctx.res ctx.inj ctx.unm hF hfree
    · exact applyN_supp ctx.supp _ hRb
  · have hpc := pot_success hI hF
    have hge := hF.ge hI
    have htopc : (a.choose s j).top = a.top := rfl
    rw [AS.done_pot]
    simp only [size_condEq, size_var, size_lit, potW, potD] at *
    omega

/-- **Push**: the scan found an occupied right vertex; a frame for its occupant goes on top. -/
theorem turn_push (ctx : Ctx B x μ₀ l₀) (hI : AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a)
    (hP : PostScan x μ₀ a σ) (hf : σ.vars "found" = 1) {l' : ℕ}
    (hocc : μ₀ (σ.vars "foundJ") = some l') {K₀ : ℕ}
    (hK₀ : K₀ + 40 * a.Xs (a.top - 1) ≤ 40 * σ.vars "x" + 34) :
    ∃ a' σ' K, Run B afterScanCom σ σ' K ∧ LoopInv x μ₀ l₀ a' σ' ∧
      K₀ + K + 4 + a'.pot (offw x) μ₀ (mw x) ≤ a.pot (offw x) μ₀ (mw x) := by
  have hg := ctx.good
  have hB := ctx.hB
  obtain ⟨hF, hx1⟩ := hP.found hg hI hf
  set j := σ.vars "foundJ" with hj
  set s := σ.vars "x" - 1 with hs
  have hxs : σ.vars "x" = s + 1 := by omega
  have hpos := hI.top_pos
  have hle := top_le_succ hI
  have hmB : mw x + 1 < B := by have := hg.m_lt; omega
  have hnB : nw x + 2 ≤ B := by have := hg.n_lt; omega
  have hl'n : l' < nw x := ctx.hμn j l' hocc
  have hxB : σ.vars "x" < B := by
    have := hP.scan.xhi
    have := hg.off_lt_len (i := a.Ls (a.top - 1) + 1) (by have := hI.Lbd (a.top - 1) (by omega); have := hg.nV; omega)
    omega
  obtain ⟨σ₃, hrun3, hQ3⟩ := (found_spec (x := x) (μ₀ := μ₀) (a := a) (j := j) (xv := σ.vars "x")
    (by omega) hle hpos hmB hF.lt (fun l hl => by have := ctx.hμn j l hl; omega)
    (by omega) hxB).run ⟨hP.real, hP.t1, rfl, rfl⟩
  rw [hxs] at hQ3
  subst hQ3
  have hR3 := hP.real.found (s := s) (j := j) (match μ₀ j with | none => 0 | some l => l + 1)
  have hocc' : ((((σ.setArr "stkR" (a.top - 1) j).setArr "stkX" (a.top - 1) (s + 1)).setArr
      "vis" j 1).setVar "occ" (match μ₀ j with | none => 0 | some l => l + 1)).vars "occ" =
      l' + 1 := by
    simp [hocc]
  set σ3 := ((((σ.setArr "stkR" (a.top - 1) j).setArr "stkX" (a.top - 1) (s + 1)).setArr
      "vis" j 1).setVar "occ" (match μ₀ j with | none => 0 | some l => l + 1)) with hσ3
  have hbt : (a.choose s j).top ≤ mw x := by
    have h1 := hI.top_le
    have h2 := nvis_choose a s hF.lt hF.fresh
    have h3 := nvis_le (a.choose s j) (mw x)
    show a.top ≤ mw x
    omega
  obtain ⟨σ₄, hrun4, hQ4⟩ := (push_spec (x := x) (μ₀ := μ₀) hg hB (l' := l')
    (by omega) (b := a.choose s j) hbt hmB hnB hl'n).run ⟨hR3, hocc'⟩
  have hoccB : σ3.vars "occ" < B := by rw [hocc']; omega
  have hcond : (Cond.eq (.var "occ") (.lit 0)).evalB B σ3 = some false := by
    rw [evalB_condEq (evalB_var hoccB) (evalB_lit (by omega)), hocc']; simp
  have hfB : σ.vars "found" < B := by have := hP.scan.fle; omega
  have hcond0 : (Cond.eq (.var "found") (.lit 0)).evalB B σ = some false := by
    rw [evalB_condEq (evalB_var hfB) (evalB_lit (by omega)), hf]; simp
  have hmono : offw x l' ≤ offw x (l' + 1) := hg.mono l' (by have := hg.nV; omega)
  refine ⟨(a.choose s j).push (offw x) l', σ₄, _,
    Run.ite_false hcond0 (hrun3.seq (Run.ite_false hcond hrun4)), ?_, ?_⟩
  · subst hQ4
    refine Or.inl ⟨?_, Real.push hR3, hI.push hF hocc hl'n hmono⟩
    have := hP.res
    simp [hσ3, this]
  · have hpc := pot_push hI hF hocc
    have hge := hF.ge hI
    simp only [size_condEq, size_var, size_lit, potW, potD] at *
    omega

end Turns

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.SearchLoop` -/

section
/-!
The whole search loop: one turn (`turn_run`), a while rule whose potential is a function of a
*ghost* abstract state (`while_ghost`), and `search_run`, the loop-level specification; then the
cost of a search restarted from a fresh left vertex, linear in the word.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching
open scoped Classical

variable {B : ℕ}

section Turn

variable {x : List ℕ} {μ₀ : ℕ → Option ℕ} {l₀ : ℕ} {a : AS} {σ : Env}

/-- The scan's precondition, for the pending frame, in the state the prelude leaves. -/
theorem scanInv_of_prelude (hR : Real x μ₀ a σ)
    (hI : AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a) {σ₁ : Env}
    (hσ₁ : σ₁ = (((((σ.setVar "t1" (a.top - 1)).setVar "i" (a.Ls (a.top - 1))).setVar "x"
        (a.Xs (a.top - 1))).setVar "xe" (offw x (a.Ls (a.top - 1) + 1))).setVar "found" 0).setVar
        "foundJ" 0) :
    ScanInv x a.visB (a.Ls (a.top - 1)) σ₁ := by
  have hpos := hI.top_pos
  have hXlo := hI.Xlo (a.top - 1) (by omega)
  have hXhi := hI.Xhi (a.top - 1) (by omega)
  subst hσ₁
  refine ⟨by simp, by simp, by simpa using hR.V, by simpa using hR.n, by simpa using hR.m,
    hR.arr.congr (by simp), hR.vis.congr (by simp), by simpa using hXlo, by simpa using hXhi,
    by simp, by simp, ?_⟩
  left
  refine ⟨by simp, ?_⟩
  simp only [vars_setVar, String.reduceEq, ↓reduceIte]
  intro s hs1 hs2 j hj
  exact hI.Xcl (a.top - 1) (by omega) s hs1 hs2 j hj

/-- **One turn of the search**: a step of the loop, paying for itself out of the potential. -/
theorem turn_run (ctx : Ctx B x μ₀ l₀) (hR : Real x μ₀ a σ)
    (hI : AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a) (hres : σ.vars "result" = 2) :
    ∃ a' σ' K, Run B turnCom σ σ' K ∧ LoopInv x μ₀ l₀ a' σ' ∧
      K + 4 + a'.pot (offw x) μ₀ (mw x) ≤ a.pot (offw x) μ₀ (mw x) := by
  have hg := ctx.good
  have hB := ctx.hB
  have hpos := hI.top_pos
  have hLn := hI.Lbd (a.top - 1) (by omega)
  obtain ⟨σ₁, hr1, hq1⟩ := (prelude_spec ctx (a := a)).run ⟨hR, hI⟩
  have hSI := scanInv_of_prelude hR hI hq1
  have hR₁ : Real x μ₀ a σ₁ := by
    subst hq1; exact hR.congr (by simp) (by simp) (by simp) (by simp) (by simp)
  have hf₁ : σ₁.vars "found" = 0 := by subst hq1; simp
  have hx₁ : σ₁.vars "x" = a.Xs (a.top - 1) := by subst hq1; simp
  obtain ⟨σ₂, K₂, hr2, hI₂, hstop, hxle, hK₂, hfv, hfa⟩ :=
    scanRowEarly_run (B := B) (visB := a.visB) hg hB hLn hSI hf₁
  have hres₁ : σ₁.vars "result" = 2 := by subst hq1; simpa using hres
  have ht1₁ : σ₁.vars "t1" + 1 = a.top := by subst hq1; simp; omega
  have hP : PostScan x μ₀ a σ₂ :=
    ⟨hR₁.congr (by rw [hfv "top" (by simp)]) (by rw [hfv "V" (by simp)])
      (by rw [hfv "n" (by simp)]) (by rw [hfv "m" (by simp)]) hfa,
      by rw [hfv "result" (by simp)]; exact hres₁,
      by rw [hfv "t1" (by simp)]; exact ht1₁, hI₂, hstop⟩
  have hfle : σ₂.vars "found" ≤ 1 := hI₂.fle
  rw [hx₁] at hK₂
  by_cases hf : σ₂.vars "found" = 0
  · have hx : σ₂.vars "x" = offw x (a.Ls (a.top - 1) + 1) := by rcases hstop with h | h <;> omega
    obtain ⟨a', σ', K, hrA, hL, hK⟩ := turn_pop ctx hI hP hf (K₀ := 20 + K₂) (by omega)
    exact ⟨a', σ', 20 + (K₂ + K), hr1.seq (hr2.seq hrA), hL, by omega⟩
  · have hf1 : σ₂.vars "found" = 1 := by omega
    have hK₀ : (20 + K₂) + 40 * a.Xs (a.top - 1) ≤ 40 * σ₂.vars "x" + 34 := by omega
    rcases hμ : μ₀ (σ₂.vars "foundJ") with _ | l'
    · obtain ⟨a', σ', K, hrA, hL, hK⟩ := turn_success ctx hI hP hf1 hμ hK₀
      exact ⟨a', σ', 20 + (K₂ + K), hr1.seq (hr2.seq hrA), hL, by omega⟩
    · obtain ⟨a', σ', K, hrA, hL, hK⟩ := turn_push ctx hI hP hf1 hμ hK₀
      exact ⟨a', σ', 20 + (K₂ + K), hr1.seq (hr2.seq hrA), hL, by omega⟩

end Turn

/-! ### The loop -/

/-- **The while rule, with a potential on a ghost state.** As `Run.while_potential`, but the
invariant and the potential range over an auxiliary ghost value carried along the run. -/
theorem while_ghost {G : Type*} {b : Cond} {c : Com} (I : G → Env → Prop) (Φ : G → ℕ)
    (hdef : ∀ g σ, I g σ → ∃ v, b.evalB B σ = some v)
    (hstep : ∀ g σ, I g σ → b.evalB B σ = some true →
      ∃ g' σ' K, Run B c σ σ' K ∧ I g' σ' ∧ 1 + b.size + K + Φ g' ≤ Φ g)
    {g : G} {σ : Env} (hI : I g σ) :
    ∃ g' σ' K, Run B (.while b c) σ σ' K ∧ I g' σ' ∧ b.evalB B σ' = some false ∧
      K + Φ g' ≤ Φ g + 1 + b.size := by
  suffices H : ∀ N (g : G) σ, I g σ → Φ g ≤ N →
      ∃ g' σ' K, Run B (.while b c) σ σ' K ∧ I g' σ' ∧ b.evalB B σ' = some false ∧
        K + Φ g' ≤ Φ g + 1 + b.size from H (Φ g) g σ hI le_rfl
  intro N
  induction N with
  | zero =>
      intro g σ hI hΦ
      obtain ⟨v, hv⟩ := hdef g σ hI
      cases v with
      | false => exact ⟨g, σ, _, Run.while_false hv, hI, hv, by omega⟩
      | true =>
          obtain ⟨g₁, σ₁, K, hrun, _, hpay⟩ := hstep g σ hI hv
          omega
  | succ N ih =>
      intro g σ hI hΦ
      obtain ⟨v, hv⟩ := hdef g σ hI
      cases v with
      | false => exact ⟨g, σ, _, Run.while_false hv, hI, hv, by omega⟩
      | true =>
          obtain ⟨g₁, σ₁, K, hrun, hI₁, hpay⟩ := hstep g σ hI hv
          obtain ⟨g', σ', K', hrun', hI', hfalse, hpay'⟩ := ih g₁ σ₁ hI₁ (by omega)
          obtain ⟨k, hk, hbs⟩ := hrun
          obtain ⟨k', hk', hbs'⟩ := hrun'
          exact ⟨g', σ', 1 + b.size + k + k', ⟨1 + b.size + k + k', le_rfl,
            .while_true hv hbs hbs'⟩, hI', hfalse, by omega⟩

section Loop

variable {x : List ℕ} {μ₀ : ℕ → Option ℕ} {l₀ : ℕ}

/-- **The search loop, run to completion.** From a well-formed state whose `result` is `2`, the
loop `while result = 2 do turn` halts within `pot a + 4` instructions in a state that has either
**succeeded** (`Done1`: `mu` holds a `GoodResult` for `l₀`) or **failed** (`Done0`: the visited
set is a `FailCert`). -/
theorem search_run (ctx : Ctx B x μ₀ l₀) {a : AS} {σ : Env}
    (hR : Real x μ₀ a σ) (hI : AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a)
    (hres : σ.vars "result" = 2) :
    ∃ σ' K, Run B searchCom σ σ' K ∧ K ≤ a.pot (offw x) μ₀ (mw x) + 4 ∧
      (Done1 x μ₀ l₀ σ' ∨ Done0 x μ₀ l₀ σ') := by
  have h3 : 3 < B := by have := ctx.hB; omega
  have hresB : ∀ (g : AS) (τ : Env), LoopInv x μ₀ l₀ g τ → τ.vars "result" < B := by
    intro g τ h
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  obtain ⟨g', σ', K, hrun, hL, hfalse, hpay⟩ := while_ghost (B := B)
    (b := .eq (.var "result") (.lit 2)) (c := turnCom) (LoopInv x μ₀ l₀)
    (fun g => g.pot (offw x) μ₀ (mw x))
    (fun g τ h => ⟨_, evalB_condEq (evalB_var (hresB g τ h)) (evalB_lit (n := 2) (by omega))⟩)
    (fun g τ h hb => by
      have hτ : τ.vars "result" = 2 := by
        have heq := evalB_condEq (evalB_var (hresB g τ h)) (evalB_lit (n := 2) (by omega))
        rw [hb] at heq
        simpa using heq.symm
      rcases h with ⟨-, hR', hI'⟩ | ⟨h1, -⟩ | ⟨h0, -⟩
      · obtain ⟨a', τ', K, hrun, hL, hK⟩ := turn_run ctx hR' hI' hτ
        refine ⟨a', τ', K, hrun, hL, ?_⟩
        simp only [size_condEq, size_var, size_lit]
        omega
      · omega
      · omega)
    (Or.inl ⟨hres, hR, hI⟩)
  refine ⟨σ', K, hrun, by simp only [size_condEq, size_var, size_lit] at hpay; omega, ?_⟩
  have hne : σ'.vars "result" ≠ 2 := by
    intro h2
    have heq := evalB_condEq (evalB_var (hresB g' σ' hL)) (evalB_lit (n := 2) (by omega))
    rw [hfalse, h2] at heq
    simp at heq
  rcases hL with ⟨h, -⟩ | h | h
  · omega
  · exact Or.inl h
  · exact Or.inr h

/-- The cost of one search, restarted from a fresh left vertex: linear in the word. -/
def searchCost (x : List ℕ) : ℕ := 80 * offw x (Vw x) + potD + potW * mw x + 4

/-- **A restarted search costs `O(|x|)`** — from any left-over stack arrays, with `top` reset
to `1`, `stkL[0] := l₀`, `stkX[0] := off l₀` and the visited table cleared. -/
theorem search_run_restart (ctx : Ctx B x μ₀ l₀) {b : AS} {σ : Env}
    (hR : Real x μ₀ (AS.restart (offw x) b l₀) σ) (hres : σ.vars "result" = 2) :
    ∃ σ' K, Run B searchCom σ σ' K ∧ K ≤ searchCost x ∧
      (Done1 x μ₀ l₀ σ' ∨ Done0 x μ₀ l₀ σ') := by
  have hg := ctx.good
  have hmono : offw x l₀ ≤ offw x (l₀ + 1) := hg.mono l₀ (by have := hg.nV; have := ctx.hl₀; omega)
  obtain ⟨σ', K, hrun, hK, hd⟩ := search_run ctx hR (AbsInv.restart b ctx.hl₀ hmono) hres
  have hpot := restart_pot_le (off := offw x) (μ₀ := μ₀) (n := nw x) (m := mw x) b l₀ ctx.inj
    ctx.hμn (fun l hl => hg.mono l (by have := hg.nV; omega)) (R := offw x (Vw x))
    (hg.off_le_last (nw x) hg.nV) (hg.rowlen_le ctx.hl₀)
  exact ⟨σ', K, hrun, by unfold searchCost; omega, hd⟩

end Loop

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.Restart` -/

section
/-!
Restarting the search for the next left vertex: `stkL[0] := l0; stkX[0] := a[2 + l0]; top := 1;
result := 2`, and clear the visited table (`m` stores). The postcondition is `Real` for the
abstract state `AS.restart (offw x) b l0`, exactly what `search_run_restart` asks for.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching
open scoped Classical

variable {B : ℕ}

/-- `vis[j] := 0; j := j + 1`. -/
def clearVisBody : Com :=
  .seq (.store "vis" (.var "j") (.lit 0)) (.assign "j" (.add (.var "j") (.lit 1)))

/-- Clear the visited table: `j := 0; while j < m do clearVisBody`. -/
def clearVis : Com := .seq (.assign "j" (.lit 0)) (.while (.lt (.var "j") (.var "m")) clearVisBody)

/-- The four writes of a restart: frame `0` is `l0` at the first slot of its row. -/
def restartHead : Com :=
  .seq (.store "stkL" (.lit 0) (.var "l0"))
    (.seq (.store "stkX" (.lit 0) (.get "a" (.add (.lit 2) (.var "l0"))))
      (.seq (.assign "top" (.lit 1)) (.assign "result" (.lit 2))))

/-- **Restart**: frame `0` is `l0` at its row's first slot, `top = 1`, `result = 2`, nothing
visited. -/
def restartCom : Com := .seq restartHead clearVis

/-- The invariant of the clearing loop: `m` is in place, `j ≤ m`, and the first `j` cells of
`vis` are zero, the rest as they were (`f`). -/
def ClearInv (m : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "m" = m ∧ σ.vars "j" ≤ m ∧
    σ.arrs "vis" = arrOf m (fun k => if k < σ.vars "j" then 0 else f k)

theorem clearVisBody_spec {m : ℕ} {f : ℕ → ℕ} (hmB : m + 1 < B) (h1B : 1 < B) :
    Spec B (fun σ => ClearInv m f σ ∧ σ.vars "j" < m) clearVisBody
      (fun σ σ' => ClearInv m f σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 9 := by
  rintro σ ⟨⟨hm, hjm, hvis⟩, hj⟩
  have hlen : (σ.arrs "vis").length = m := by rw [hvis]; simp
  unfold clearVisBody
  run_vcg
  all_goals (simp [ClearInv, hm, hvis]; try omega)
  refine ⟨hj, ?_⟩
  rw [set_arrOf_update]
  refine arrOf_congr (fun k _ => ?_)
  by_cases hk : k = σ.vars "j"
  · subst hk; simp
  · rw [Function.update_of_ne hk]
    split_ifs <;> first | rfl | omega

theorem clearVis_spec {m : ℕ} {f : ℕ → ℕ} (hmB : m + 1 < B) (h1B : 1 < B) :
    Spec B (fun σ => σ.vars "m" = m ∧ σ.arrs "vis" = arrOf m f) clearVis
      (fun _ σ' => σ'.arrs "vis" = arrOf m (fun _ => 0)) ((9 + 4) * m + 6) := by
  have hloop := Spec.forRangeZero (B := B) (c := clearVisBody) "j" "m" (ClearInv m f) m 9
    (by omega) (fun σ hσ => hσ.2.1) (fun σ hσ => hσ.1) (clearVisBody_spec hmB h1B)
  refine hloop.conseq ?_ ?_ le_rfl
  · rintro σ ⟨hm, hv⟩
    refine ⟨by simpa using hm, by simp, ?_⟩
    simpa using hv.trans (arrOf_congr (fun k _ => by simp))
  · rintro σ σ' _ ⟨⟨_, _, hv⟩, hj⟩
    rw [hv]
    exact arrOf_congr (fun k hk => by simp [hj, hk])

section Head

variable {x : List ℕ} {μ : ℕ → Option ℕ} {l0 : ℕ} {b : AS} {σ : Env}

/-- The abstract state after the head of a restart (visited table not yet cleared). -/
def AS.head (off : ℕ → ℕ) (b : AS) (l0 : ℕ) : AS :=
  { b with Ls := Function.update b.Ls 0 l0, Xs := Function.update b.Xs 0 (off l0), top := 1 }

theorem restartHead_spec (hg : Good x) (hB : x.length + 8 ≤ B) (hl : l0 < nw x) :
    Spec B (fun σ => Real x μ b σ ∧ σ.vars "l0" = l0) restartHead
      (fun σ σ' => σ' = (((σ.setArr "stkL" 0 l0).setArr "stkX" 0 (offw x l0)).setVar "top" 1).setVar
        "result" 2) 16 := by
  rintro σ ⟨hR, hl0⟩
  have hlenL := hR.lenL
  have hlenX := hR.lenX
  have hlenA := hR.arr.length
  have hnB : nw x < B := by have := hg.n_lt; omega
  have h2pos : 2 + l0 < x.length := hg.offPos_lt (by have := hg.nV; omega)
  have hoff : (σ.arrs "a").getD (2 + l0) 0 = offw x l0 := hR.arr.getD h2pos
  have hoffB : offw x l0 < B := by
    have := hg.off_lt_len (i := l0) (by have := hg.nV; omega); omega
  rw [List.getD_eq_getElem?_getD] at hoff
  unfold restartHead
  run_vcg
  all_goals (simp [hl0, hoff]; try omega)

theorem Real.head (hR : Real x μ b σ) (l0 : ℕ) :
    Real x μ (AS.head (offw x) b l0)
      ((((σ.setArr "stkL" 0 l0).setArr "stkX" 0 (offw x l0)).setVar "top" 1).setVar "result" 2) := by
  refine ⟨by simp [AS.head], by simpa using hR.V, by simpa using hR.n, by simpa using hR.m,
    hR.arr.congr (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · unfold VisOK
    have := hR.vis
    unfold VisOK at this
    simp only [arrs_setVar, arrs_setArr]
    simp
    exact this
  · simpa [MuOK] using hR.mu
  · simp [hR.stkL, set_arrOf_update, AS.head]
  · simpa [AS.head] using hR.stkR
  · simp [hR.stkX, set_arrOf_update, AS.head]

theorem Real.clear {a : AS} {σ' : Env} (hR : Real x μ a σ)
    (hv : σ'.arrs "vis" = arrOf (mw x) (fun _ => 0)) (ha : ∀ c, c ≠ "vis" → σ'.arrs c = σ.arrs c)
    (ht : σ'.vars "top" = σ.vars "top") (hV : σ'.vars "V" = σ.vars "V")
    (hn : σ'.vars "n" = σ.vars "n") (hm : σ'.vars "m" = σ.vars "m") :
    Real x μ { a with visB := fun _ => False } σ' := by
  refine ⟨by rw [ht]; exact hR.top, by rw [hV]; exact hR.V, by rw [hn]; exact hR.n,
    by rw [hm]; exact hR.m, hR.arr.congr (ha _ (by decide)), ?_, ?_, ?_, ?_, ?_⟩
  · unfold VisOK; rw [hv]; exact arrOf_congr (fun k _ => by simp)
  · unfold MuOK; rw [ha _ (by decide)]; exact hR.mu
  · rw [ha _ (by decide)]; exact hR.stkL
  · rw [ha _ (by decide)]; exact hR.stkR
  · rw [ha _ (by decide)]; exact hR.stkX

/-- The cost of a restart. -/
def restartCost (x : List ℕ) : ℕ := 16 + ((9 + 4) * mw x + 6)

/-- **Restart**: from any state realizing `b`, with `l0 < n` in the scalar `"l0"`, the search
state is that of `AS.restart (offw x) b l0`, `result` is `2`, and every scalar but `top`,
`result`, `j` is unchanged. -/
theorem restart_spec (hg : Good x) (hB : x.length + 8 ≤ B) (hl : l0 < nw x) :
    Spec B (fun σ => Real x μ b σ ∧ σ.vars "l0" = l0) restartCom
      (fun σ σ' => Real x μ (AS.restart (offw x) b l0) σ' ∧ σ'.vars "result" = 2 ∧
        ∀ y, y ≠ "top" → y ≠ "result" → y ≠ "j" → σ'.vars y = σ.vars y)
      (restartCost x) := by
  intro σ hσ
  have hmB : mw x + 1 < B := by have := hg.m_lt; omega
  obtain ⟨σ₁, hr1, hq1⟩ := (restartHead_spec (μ := μ) (b := b) hg hB hl).run hσ
  have hR₁ : Real x μ (AS.head (offw x) b l0) σ₁ := by rw [hq1]; exact hσ.1.head l0
  obtain ⟨σ₂, hr2, hq2, hfv, hfa, -, -⟩ :=
    (clearVis_spec (B := B) (m := mw x) (f := fun k => if b.visB k then 1 else 0) hmB
      (by omega)).frame.run ⟨hR₁.m, hR₁.vis⟩
  have hv2 : ∀ y, y ≠ "j" → σ₂.vars y = σ₁.vars y := fun y hy =>
    hfv y (by simp [clearVis, clearVisBody, Com.wvars, hy])
  have ha2 : ∀ c, c ≠ "vis" → σ₂.arrs c = σ₁.arrs c := fun c hc =>
    hfa c (by simp [clearVis, clearVisBody, Com.warrs, hc])
  refine ⟨σ₂, (hr1.seq hr2), ?_, ?_, fun y h1 h2 h3 => ?_⟩
  · exact (hR₁.clear hq2 ha2 (hv2 _ (by decide)) (hv2 _ (by decide)) (hv2 _ (by decide))
      (hv2 _ (by decide)) : _)
  · rw [hv2 _ (by decide), hq1]; simp
  · rw [hv2 y h3, hq1]; simp [h1, h2]

end Head

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.OuterMath` -/

section
/-!
The mathematics of the outer loop over left vertices: the machine keeps a matching
`μ : ℕ → Option ℕ`; here it is read on the `Fin` types (`muF`), where `Maximum.lean`'s
maximality argument lives.

`MatchInv adjB n m l μ` is what the loop keeps after processing the left vertices `0 .. l - 1`:
`μ` is a matching whose left endpoints are below `l` and whose support is below `m`, and every
processed left vertex is `Matched` or `Failed`. A successful search preserves it by
`failed_stable`, a failed one by turning the machine's `FailCert` into `Failed`. At the end
(`l = n`) the matching has the size of Kuhn's result (`MatchInv.size_eq_kuhn`), and the count
of matched right vertices is that size (`size_muF_eq`).
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching Lax117284Proofs.Bipartite.Maximum
open scoped Classical

/-- A relation on `ℕ`, restricted to the `Fin` types. -/
def adjF (adjB : ℕ → ℕ → Prop) (n m : ℕ) : Fin n → Fin m → Prop := fun i j => adjB i.val j.val

/-- The support of `μ` lies below `m`. -/
def SuppLt (μ : ℕ → Option ℕ) (m : ℕ) : Prop := ∀ j l, μ j = some l → j < m

section Transfer

variable {adjB : ℕ → ℕ → Prop} {n m : ℕ} {μ : ℕ → Option ℕ}

/-- The matching `μ`, restricted to the `Fin` types. -/
noncomputable def muF (n m : ℕ) (μ : ℕ → Option ℕ) : Fin m → Option (Fin n) := fun j =>
  match μ j.val with
  | none => none
  | some l => if h : l < n then some ⟨l, h⟩ else none

theorem muF_eq_some (hbd : ∀ j l, μ j = some l → l < n) {j : Fin m} {l : Fin n} :
    muF n m μ j = some l ↔ μ j.val = some l.val := by
  unfold muF
  rcases hμ : μ j.val with _ | l'
  · simp
  · have := hbd _ _ hμ
    simp only [dif_pos this, Option.some.injEq]
    constructor
    · intro h; rw [← h]
    · intro h; exact Fin.ext h

theorem matched_muF (hbd : ∀ j l, μ j = some l → l < n) (hsupp : SuppLt μ m) {l : Fin n} :
    Matched (muF n m μ) l ↔ Matched μ l.val := by
  constructor
  · rintro ⟨r, hr⟩; exact ⟨r.val, (muF_eq_some hbd).1 hr⟩
  · rintro ⟨r, hr⟩; exact ⟨⟨r, hsupp r _ hr⟩, (muF_eq_some hbd).2 hr⟩

theorem isMatching_muF (hres : Respects adjB μ) (hinj : InjOnSupport μ)
    (hbd : ∀ j l, μ j = some l → l < n) : IsMatching (adjF adjB n m) (muF n m μ) := by
  refine ⟨fun r l h => hres r.val l.val ((muF_eq_some hbd).1 h), fun r r' l h h' => ?_⟩
  exact Fin.ext (hinj r.val r'.val l.val ((muF_eq_some hbd).1 h) ((muF_eq_some hbd).1 h'))

/-- A good result on `ℕ` is a good result on the `Fin` types. -/
theorem goodResult_muF {μ' : ℕ → Option ℕ} (hbd : ∀ j l, μ j = some l → l < n)
    (hbd' : ∀ j l, μ' j = some l → l < n) (hsupp : SuppLt μ m) (hsupp' : SuppLt μ' m) {l₀ : ℕ}
    (hl₀ : l₀ < n) (hG : GoodResult adjB μ ∅ l₀ μ') :
    GoodResult (adjF adjB n m) (muF n m μ) ∅ ⟨l₀, hl₀⟩ (muF n m μ') := by
  obtain ⟨hres', hinj', hM', hIff, -⟩ := hG
  refine ⟨(isMatching_muF hres' hinj' hbd').1, (isMatching_muF hres' hinj' hbd').2, ?_, ?_, ?_⟩
  · exact (matched_muF hbd' hsupp').2 hM'
  · intro l hl
    rw [matched_muF hbd hsupp, matched_muF hbd' hsupp']
    exact hIff l.val (fun h => hl (Fin.ext h))
  · intro r hr; simp at hr

/-- **A failure certificate is a `Failed` on the `Fin` types**: every reached left vertex is
closed, so every reached right vertex is visited, hence occupied. -/
theorem failed_of_failCert (hbd : ∀ j l, μ j = some l → l < n) (hsupp : SuppLt μ m) {l₀ : ℕ}
    (hl₀ : l₀ < n) (hunm : ¬ Matched μ l₀) {visB : ℕ → Prop}
    (hF : FailCert adjB μ m l₀ visB) :
    Failed (adjF adjB n m) (muF n m μ) ⟨l₀, hl₀⟩ := by
  obtain ⟨hC, hO⟩ := hF
  refine ⟨fun h => hunm ((matched_muF hbd hsupp).1 h), ?_⟩
  have hReach : ∀ l', ReachL (adjF adjB n m) (muF n m μ) ⟨l₀, hl₀⟩ l' →
      ∀ j < m, adjB l'.val j → visB j := by
    intro l' hl'
    unfold ReachL at hl'
    induction hl' with
    | refl => exact hC
    | @tail l l'' hprev hstep ih =>
        obtain ⟨r, hadjr, hocc⟩ := hstep
        have hv : visB r.val := ih r.val r.2 hadjr
        obtain ⟨l3, hl3, hcl3⟩ := hO r.val r.2 hv
        rw [muF_eq_some hbd] at hocc
        rw [hocc] at hl3
        cases hl3
        exact hcl3
  rintro r ⟨l, hl, hlr⟩
  have hv : visB r.val := hReach l hl r.val r.2 hlr
  obtain ⟨l3, hl3, -⟩ := hO r.val r.2 hv
  exact ⟨⟨l3, hbd _ _ hl3⟩, (muF_eq_some hbd).2 hl3⟩

/-- The size of the `Fin` matching is the number of matched right indices below `m`. -/
theorem size_muF_eq (hbd : ∀ j l, μ j = some l → l < n) :
    size (muF n m μ) = ((Finset.range m).filter (fun j => (μ j).isSome)).card := by
  unfold size
  refine Finset.card_bij (fun (j : Fin m) _ => j.val) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨j.2, ?_⟩
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hj
    exact Option.isSome_iff_exists.2 ⟨l.val, (muF_eq_some hbd).1 hl⟩
  · intro j _ j' _ h; exact Fin.ext h
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hj.2
    refine ⟨⟨j, hj.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Option.isSome_iff_exists.2 ⟨⟨l, hbd _ _ hl⟩, (muF_eq_some hbd).2 hl⟩

end Transfer

/-! ### The invariant of the outer loop -/

/-- **What the outer loop maintains** after processing the left vertices below `l`. -/
structure MatchInv (adjB : ℕ → ℕ → Prop) (n m l : ℕ) (μ : ℕ → Option ℕ) : Prop where
  res : Respects adjB μ
  inj : InjOnSupport μ
  bd : ∀ j l', μ j = some l' → l' < l
  supp : SuppLt μ m
  done : ∀ l' : Fin n, l'.val < l →
    Matched (muF n m μ) l' ∨ Failed (adjF adjB n m) (muF n m μ) l'

section Inv

variable {adjB : ℕ → ℕ → Prop} {n m l : ℕ} {μ : ℕ → Option ℕ}

theorem MatchInv.zero (adjB : ℕ → ℕ → Prop) (n m : ℕ) : MatchInv adjB n m 0 (fun _ => none) :=
  ⟨fun _ _ h => by simp at h, fun _ _ _ h => by simp at h, fun _ _ h => by simp at h,
    fun _ _ h => by simp at h, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem MatchInv.unm (h : MatchInv adjB n m l μ) : ¬ Matched μ l := by
  rintro ⟨j, hj⟩
  exact absurd (h.bd j l hj) (lt_irrefl l)

theorem MatchInv.hμn (h : MatchInv adjB n m l μ) (hl : l ≤ n) :
    ∀ j l', μ j = some l' → l' < n :=
  fun j l' hj => lt_of_lt_of_le (h.bd j l' hj) hl

/-- **A successful search extends the invariant.** -/
theorem MatchInv.succ_good {μ' : ℕ → Option ℕ} (h : MatchInv adjB n m l μ) (hl : l < n)
    (hG : GoodResult adjB μ ∅ l μ') (hsupp' : SuppLt μ' m) : MatchInv adjB n m (l + 1) μ' := by
  obtain ⟨hRes, hInj, hM, hIff, -⟩ := hG
  have hbd' : ∀ j l', μ' j = some l' → l' < l + 1 := by
    intro j l' hj
    by_cases hll : l' = l
    · omega
    · have hm : Matched μ' l' := ⟨j, hj⟩
      obtain ⟨j', hj'⟩ := (hIff l' hll).2 hm
      have := h.bd j' l' hj'
      omega
  have hbdn := h.hμn (by omega)
  have hbdn' : ∀ j l', μ' j = some l' → l' < n := fun j l' hj =>
    lt_of_lt_of_le (hbd' j l' hj) hl
  have hGF := goodResult_muF hbdn hbdn' h.supp hsupp' hl ⟨hRes, hInj, hM, hIff, fun r hr => by
    simp at hr⟩
  refine ⟨hRes, hInj, hbd', hsupp', fun l' hl' => ?_⟩
  by_cases hll : l'.val = l
  · left
    have : l' = ⟨l, hl⟩ := Fin.ext hll
    rw [this]; exact hGF.2.2.1
  · have hne : l' ≠ ⟨l, hl⟩ := fun he => hll (congrArg Fin.val he)
    rcases h.done l' (by omega) with hM' | hF'
    · left; exact (hGF.2.2.2.1 l' hne).1 hM'
    · right
      exact failed_stable (isMatching_muF h.res h.inj hbdn) hF' hne.symm
        (fun hm => h.unm ((matched_muF hbdn h.supp).1 hm)) hGF

/-- **A failed search extends the invariant**, the matching unchanged. -/
theorem MatchInv.succ_fail (h : MatchInv adjB n m l μ) (hl : l < n) {visB : ℕ → Prop}
    (hF : FailCert adjB μ m l visB) : MatchInv adjB n m (l + 1) μ := by
  have hbdn := h.hμn (by omega)
  refine ⟨h.res, h.inj, fun j l' hj => by have := h.bd j l' hj; omega, h.supp,
    fun l' hl' => ?_⟩
  by_cases hll : l'.val = l
  · right
    have : l' = ⟨l, hl⟩ := Fin.ext hll
    rw [this]; exact failed_of_failCert hbdn h.supp hl h.unm hF
  · exact h.done l' (by omega)

/-- **At the end the matching is maximum**: it has the size of Kuhn's result. -/
theorem MatchInv.size_eq_kuhn (h : MatchInv adjB n m n μ) :
    size (muF n m μ) = size (kuhn (adjF adjB n m)) := by
  have hbdn := h.hμn le_rfl
  have hM := isMatching_muF (m := m) h.res h.inj hbdn
  have hall : ∀ l' : Fin n, Matched (muF n m μ) l' ∨ Failed (adjF adjB n m) (muF n m μ) l' :=
    fun l' => h.done l' l'.2
  have hK := kuhn_maximum (adjF adjB n m)
  exact le_antisymm (hK.2 _ hM) (size_le_of_saturating hM hall hK.1)

end Inv

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.Outer` -/

section
/-!
The outer loop of Kuhn's algorithm: for each left vertex `l0 = 0, 1, …, n-1`, restart the search
and run it, then move on to the next left vertex whether the search succeeded or not. The loop's
invariant is `OuterMath.MatchInv` for the vertices processed so far.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching
open scoped Classical

variable {B : ℕ}

/-- The scalars the search may assign. -/
def searchVars : List String :=
  ["top", "result", "t1", "i", "x", "xe", "found", "foundJ", "cand", "occ", "k", "rr", "ll", "cont"]

theorem searchCom_wvars : ∀ y ∈ searchCom.wvars, y ∈ searchVars := by
  intro y hy
  simp [searchCom, turnCom, preludeCom, scanRowEarly, afterScanCom, popCom, foundCom, pushCom,
    applyCom, applyBodyCom, readMu, writeMu, computeCont, scanBody, Com.wvars] at hy
  simp only [searchVars, List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem search_frame {σ σ' : Env} {K : ℕ} (h : Run B searchCom σ σ' K) {y : String}
    (hy : y ∉ searchVars) : σ'.vars y = σ.vars y :=
  h.frame_var y (fun hm => hy (searchCom_wvars y hm))

/-- One outer iteration: restart the search for `l0`, run it, advance. -/
def outerBody : Com :=
  .seq restartCom (.seq searchCom (.assign "l0" (.add (.var "l0") (.lit 1))))

/-- The outer loop over the left vertices. -/
def outerLoop : Com := .while (.lt (.var "l0") (.var "n")) outerBody

/-- The outer loop's invariant: the vertices below `l0` have been processed, and the realized
matching satisfies `MatchInv` for them. -/
def OuterInv (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "l0" ≤ nw x ∧ ∃ (μ : ℕ → Option ℕ) (b : AS), Real x μ b σ ∧
    MatchInv (adjw x) (nw x) (mw x) (σ.vars "l0") μ

theorem OuterInv.n {x : List ℕ} {σ : Env} (h : OuterInv x σ) : σ.vars "n" = nw x := by
  obtain ⟨-, μ, b, hR, -⟩ := h
  exact hR.n

/-- The cost of one outer iteration. -/
def iterCost (x : List ℕ) : ℕ := restartCost x + searchCost x + 8

section Iter

variable {x : List ℕ}

theorem Ctx.of_inv (hg : Good x) (hB : x.length + 8 ≤ B) {μ : ℕ → Option ℕ} {l : ℕ}
    (hl : l < nw x) (hM : MatchInv (adjw x) (nw x) (mw x) l μ) : Ctx B x μ l :=
  ⟨hg, hB, hl, hM.res, hM.inj, hM.unm, hM.hμn (by omega), hM.supp⟩

theorem outer_iter (hg : Good x) (hB : x.length + 8 ≤ B) {σ : Env} (hI : OuterInv x σ)
    (hlt : σ.vars "l0" < nw x) :
    ∃ σ' K, Run B outerBody σ σ' K ∧ OuterInv x σ' ∧ σ'.vars "l0" = σ.vars "l0" + 1 ∧
      K + 4 ≤ iterCost x := by
  obtain ⟨hl0le, μ, b, hR, hM⟩ := hI
  obtain ⟨σ₁, hr1, hR₁, hres₁, hfr₁⟩ := (restart_spec (μ := μ) (b := b) hg hB hlt).run ⟨hR, rfl⟩
  obtain ⟨σ₂, K₂, hr2, hK₂, hd⟩ := search_run_restart (Ctx.of_inv hg hB hlt hM) hR₁ hres₁
  have hfr₂ : ∀ y, y ∉ searchVars → y ≠ "top" → y ≠ "result" → y ≠ "j" →
      σ₂.vars y = σ.vars y := fun y h0 h1 h2 h3 => by rw [search_frame hr2 h0, hfr₁ y h1 h2 h3]
  have hl₂ : σ₂.vars "l0" = σ.vars "l0" := hfr₂ "l0" (by decide) (by decide) (by decide) (by decide)
  have hnB : nw x < B := by have := hg.n_lt; omega
  have hl0B : σ.vars "l0" + 1 < B := by omega
  have r3 : Run B (.assign "l0" (.add (.var "l0") (.lit 1))) σ₂
      (σ₂.setVar "l0" (σ.vars "l0" + 1)) (1 + 3) := by
    have := RunStep.eval_add B σ₂ (.var "l0") (.lit 1) (σ.vars "l0") 1
      (by rw [← hl₂]; exact RunStep.eval_var B σ₂ "l0" (by omega))
      (RunStep.eval_lit B 1 σ₂ (by omega)) hl0B
    exact RunStep.assign B σ₂ "l0" _ _ this
  have e : (σ₂.setVar "l0" (σ.vars "l0" + 1)).vars "l0" = σ.vars "l0" + 1 := by simp
  refine ⟨σ₂.setVar "l0" (σ.vars "l0" + 1), _, hr1.seq (hr2.seq r3), ?_, e, ?_⟩
  · refine ⟨by rw [e]; omega, ?_⟩
    rcases hd with ⟨-, b', μ', hR', hg', hsupp'⟩ | ⟨-, b', hR', hF⟩
    · refine ⟨μ', b', hR'.setVar "l0" (by simp) _, ?_⟩
      rw [e]
      exact hM.succ_good hlt hg' hsupp'
    · refine ⟨μ, b', hR'.setVar "l0" (by simp) _, ?_⟩
      rw [e]
      exact hM.succ_fail hlt hF
  · unfold iterCost; omega

/-- **The outer loop, run to completion.** -/
theorem outerLoop_run (hg : Good x) (hB : x.length + 8 ≤ B) {σ : Env} (hI : OuterInv x σ) :
    ∃ σ' K, Run B outerLoop σ σ' K ∧ OuterInv x σ' ∧ σ'.vars "l0" = nw x ∧
      K ≤ iterCost x * (nw x - σ.vars "l0") + 4 := by
  have hnB : nw x < B := by have := hg.n_lt; omega
  have hdef : ∀ τ, OuterInv x τ → ∃ v,
      (Cond.lt (.var "l0") (.var "n")).evalB B τ = some v := fun τ hτ =>
    evalB_condLt_vars (by have := hτ.1; omega) (by rw [hτ.n]; exact hnB)
  have hstep : ∀ τ, OuterInv x τ → (Cond.lt (.var "l0") (.var "n")).evalB B τ = some true →
      ∃ τ' K, Run B outerBody τ τ' K ∧ OuterInv x τ' ∧
        1 + (Cond.lt (.var "l0") (.var "n")).size + K + iterCost x * (nw x - τ'.vars "l0") ≤
          iterCost x * (nw x - τ.vars "l0") := by
    intro τ hτ hv
    have hlt : τ.vars "l0" < nw x := by
      have := lt_of_condLt_true hv
      rw [hτ.n] at this
      exact this
    obtain ⟨τ', K', hr, hI', hgt, hK⟩ := outer_iter hg hB hτ hlt
    refine ⟨τ', K', hr, hI', ?_⟩
    have hd : nw x - τ'.vars "l0" + 1 = nw x - τ.vars "l0" := by omega
    have := congrArg (iterCost x * ·) hd
    simp only [Nat.mul_add, Nat.mul_one] at this
    simp only [size_condLt, size_var]
    omega
  obtain ⟨σ', K, hrun, hI', hfalse, hpay⟩ := Run.while_potential (B := B)
    (b := .lt (.var "l0") (.var "n")) (c := outerBody) (OuterInv x)
    (fun τ => iterCost x * (nw x - τ.vars "l0")) hdef hstep hI
  refine ⟨σ', K, hrun, hI', ?_, by simp only [size_condLt, size_var] at hpay; omega⟩
  have := le_of_condLt_false (x := "l0") (y := "n") (by simpa using hfalse)
  have h2 := hI'.n
  have h3 := hI'.1
  omega

end Iter

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.Count` -/

section
/-!
Counting the matched right vertices at the end: `count := 0; j := 0; while j < m do (if mu[j] ≠ 0
then count := count + 1); j := j + 1`. The result is the number of right indices below `m` whose
`mu` entry is nonzero — the size of the matching.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open scoped Classical

variable {B : ℕ}

/-- One right vertex: count it if matched, move on. -/
def countBody : Com :=
  .seq (.ite (.eq (.get "mu" (.var "j")) (.lit 0)) .skip
      (.assign "count" (.add (.var "count") (.lit 1))))
    (.assign "j" (.add (.var "j") (.lit 1)))

/-- **Count the matched right vertices.** -/
def countCom : Com :=
  .seq (.assign "count" (.lit 0))
    (.seq (.assign "j" (.lit 0)) (.while (.lt (.var "j") (.var "m")) countBody))

/-- The number of matched right indices below `j`. -/
noncomputable def cnt (μ : ℕ → Option ℕ) (j : ℕ) : ℕ :=
  ((Finset.range j).filter (fun r => (μ r).isSome)).card

theorem cnt_succ (μ : ℕ → Option ℕ) (j : ℕ) :
    cnt μ (j + 1) = cnt μ j + if (μ j).isSome then 1 else 0 := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem cnt_le (μ : ℕ → Option ℕ) (j : ℕ) : cnt μ j ≤ j := by
  unfold cnt
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The invariant of the counting loop. -/
def CountInv (μ : ℕ → Option ℕ) (m : ℕ) (σ : Env) : Prop :=
  σ.vars "m" = m ∧ σ.vars "j" ≤ m ∧ MuOK μ m σ ∧ σ.vars "count" = cnt μ (σ.vars "j")

theorem countBody_spec {μ : ℕ → Option ℕ} {m : ℕ} (hmB : m + 1 < B)
    (hμB : ∀ j l, μ j = some l → l + 1 < B) :
    Spec B (fun σ => CountInv μ m σ ∧ σ.vars "j" < m) countBody
      (fun σ σ' => CountInv μ m σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 14 := by
  rintro σ ⟨⟨hm, hjm, hmu, hc⟩, hj⟩
  have hlen : (σ.arrs "mu").length = m := hmu.1
  have hval : (σ.arrs "mu").getD (σ.vars "j") 0 =
      (match μ (σ.vars "j") with | none => 0 | some l => l + 1) := hmu.2 _ hj
  have hvalB : (σ.arrs "mu").getD (σ.vars "j") 0 < B := by
    rw [hval]
    rcases hμ : μ (σ.vars "j") with _ | l
    · show 0 < B; omega
    · show l + 1 < B; exact hμB _ _ hμ
  have hcB : σ.vars "count" < B := by rw [hc]; have := cnt_le μ (σ.vars "j"); omega
  have hc1B : σ.vars "count" + 1 < B := by rw [hc]; have := cnt_le μ (σ.vars "j"); omega
  have hsucc := cnt_succ μ (σ.vars "j")
  unfold countBody
  run_vcg
  · rename_i hz
    have hnone : μ (σ.vars "j") = none := by
      rcases hμ : μ (σ.vars "j") with _ | l
      · rfl
      · rw [hval, hμ] at hz; simp at hz
    refine ⟨⟨by simp [hm], by simp; omega, by simpa [MuOK] using hmu, ?_⟩, by simp⟩
    simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hsucc, hnone, hc]; simp
  · rename_i hz
    have hsome : (μ (σ.vars "j")).isSome := by
      rcases hμ : μ (σ.vars "j") with _ | l
      · rw [hval, hμ] at hz; simp at hz
      · rfl
    refine ⟨⟨by simp [hm], by simp; omega, by simpa [MuOK] using hmu, ?_⟩, by simp⟩
    simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hsucc, if_pos hsome, hc]

/-- **The count.** -/
theorem countCom_spec {μ : ℕ → Option ℕ} {m : ℕ} (hmB : m + 1 < B)
    (hμB : ∀ j l, μ j = some l → l + 1 < B) :
    Spec B (fun σ => σ.vars "m" = m ∧ MuOK μ m σ) countCom
      (fun _ σ' => σ'.vars "count" = cnt μ m) ((14 + 4) * m + 6 + 2) := by
  have hloop := Spec.forRangeZero (B := B) (c := countBody) "j" "m" (CountInv μ m) m 14
    (by omega) (fun σ hσ => hσ.2.1) (fun σ hσ => hσ.1) (countBody_spec hmB hμB)
  intro σ ⟨hm, hmu⟩
  have r1 : Run B (.assign "count" (.lit 0)) σ (σ.setVar "count" 0) 2 :=
    RunStep.assign B σ "count" (.lit 0) 0 (RunStep.eval_lit B 0 σ (by omega))
  obtain ⟨σ', hr2, hI', hj⟩ := hloop.run (σ := σ.setVar "count" 0) (by
    refine ⟨by simpa using hm, by simp, by simpa [MuOK] using hmu, ?_⟩
    simp [cnt])
  refine ⟨σ', (r1.seq hr2).mono (by omega), ?_⟩
  show σ'.vars "count" = cnt μ m
  rw [hI'.2.2.2, hj]

end Lax117284Proofs.Bipartite.Ram2

end

/-! ### `Lax117284Proofs.Bipartite.Ram2.MainProg` -/

section
/-!
The IMP+ program up to its final output: read the word, the header, run one search per left
vertex, count the matched right vertices. `pre_run` runs it from the entry state of `Wrap.lean` on
any word satisfying `Good`, and leaves `count` holding the size of Kuhn's matching of the
adjacency across the split, `adjF (adjw x) n m`. The three concept programs append one output
command each (`Machine.lean`).
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching
open scoped Classical

variable {B : ℕ}

/-- The program without its final output. -/
def preCom : Com :=
  .seq readAll (.seq hdrCom (.seq (.assign "l0" (.lit 0)) (.seq outerLoop countCom)))

/-- The array lengths declared to the run. -/
def extOf (x : List ℕ) : String → ℕ := fun a =>
  if a = "a" then x.length
  else if a = "vis" ∨ a = "mu" then mw x
  else mw x + 1

/-- The initial abstract state: empty stacks, nothing visited. -/
def b0 : AS := ⟨fun _ => 0, fun _ => 0, fun _ => 0, 0, fun _ => False⟩

/-- The cost of the program without its final output. -/
def preCost (x : List ℕ) : ℕ :=
  ((10 + 4) * x.length + 6) + 12 + 2 + (iterCost x * nw x + 4) + ((14 + 4) * mw x + 6 + 2)

/-- The size of Kuhn's matching of the adjacency across the split of the word. -/
noncomputable def kuhnSize (x : List ℕ) : ℕ := size (kuhn (adjF (adjw x) (nw x) (mw x)))

theorem real_init {x : List ℕ} {σ : Env} (htop : σ.vars "top" = 0) (hV : σ.vars "V" = Vw x)
    (hn : σ.vars "n" = nw x) (hm : σ.vars "m" = mw x) (harr : ArrOK x σ)
    (hvis : σ.arrs "vis" = List.replicate (mw x) 0) (hmu : σ.arrs "mu" = List.replicate (mw x) 0)
    (hL : σ.arrs "stkL" = List.replicate (mw x + 1) 0)
    (hR : σ.arrs "stkR" = List.replicate (mw x + 1) 0)
    (hX : σ.arrs "stkX" = List.replicate (mw x + 1) 0) :
    Real x (fun _ => none) b0 σ := by
  refine ⟨htop, hV, hn, hm, harr, ?_, ⟨?_, fun j hj => ?_⟩, ?_, ?_, ?_⟩
  · unfold VisOK
    rw [hvis, replicate_eq_arrOf]
    exact arrOf_congr (fun _ _ => by simp [b0])
  · rw [hmu]; simp
  · rw [hmu, replicate_eq_arrOf, getD_arrOf _ hj]
  · rw [hL, replicate_eq_arrOf]; rfl
  · rw [hR, replicate_eq_arrOf]; rfl
  · rw [hX, replicate_eq_arrOf]; rfl

/-- **The program up to its output**, on a good word: `count` is the size of Kuhn's matching, the
header scalars hold `V` and `n`, nothing has been written. -/
theorem pre_run {x : List ℕ} (hg : Good x) (hB : x.length + 8 ≤ B) :
    ∃ σ' K, Run B preCom (lenEnv (extOf x) x) σ' K ∧ K ≤ preCost x ∧
      σ'.vars "count" = kuhnSize x ∧ σ'.vars "n" = nw x ∧ σ'.vars "V" = Vw x ∧
      σ'.out = [] := by
  set σ₀ := lenEnv (extOf x) x with hσ₀
  have h0len : σ₀.vars "len" = x.length := by simp [hσ₀, lenEnv]
  have h0top : σ₀.vars "top" = 0 := by simp [hσ₀, lenEnv, initEnv]
  have h0inp : σ₀.inp = x := rfl
  have h0out : σ₀.out = [] := rfl
  have h0arr : ∀ a, σ₀.arrs a = List.replicate (extOf x a) 0 := fun a => rfl
  have hx := hg.ent_lt
  have hlB : x.length < B := by omega
  have hxB : ∀ v ∈ x, v < B := fun v hv => lt_of_lt_of_le (hx v hv) (by omega)
  -- read
  obtain ⟨σ₁, hr1, ⟨hinp1, harr1, hlen1⟩, hfv1, hfa1, -, hfo1⟩ :=
    (readAll_spec (B := B) hxB hlB).frame.run
      ⟨h0len, h0inp, by rw [h0arr, replicate_eq_arrOf]; simp [extOf]⟩
  have hv1 : ∀ y, y ≠ "rt" → y ≠ "v" → σ₁.vars y = σ₀.vars y := fun y h1 h2 =>
    hfv1 y (by simp [readAll, readBody, Com.wvars, h1, h2])
  have ha1 : ∀ a, a ≠ "a" → σ₁.arrs a = σ₀.arrs a := fun a h1 =>
    hfa1 a (by simp [readAll, readBody, Com.warrs, h1])
  have hout1 : σ₁.out = [] := by
    rw [hfo1 (by simp [readAll, readBody, Com.NoWrite]), h0out]
  -- header
  obtain ⟨σ₂, hr2, hq2⟩ := (hdr_spec (B := B) hg hB).run (σ := σ₁) ⟨harr1, hlen1⟩
  -- l0 := 0
  have hr3 : Run B (.assign "l0" (.lit 0)) σ₂ (σ₂.setVar "l0" 0) 2 :=
    RunStep.assign B σ₂ "l0" (.lit 0) 0 (RunStep.eval_lit B 0 σ₂ (by omega))
  set σ₃ := σ₂.setVar "l0" 0 with hσ₃
  have hI₃ : OuterInv x σ₃ := by
    refine ⟨by simp [hσ₃], fun _ => none, b0, ?_, ?_⟩
    · refine real_init ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hσ₃, hq2]; simp; rw [hv1 _ (by decide) (by decide), h0top]
      · rw [hσ₃, hq2]; simp
      · rw [hσ₃, hq2]; simp
      · rw [hσ₃, hq2]; simp
      · refine harr1.congr ?_
        rw [hσ₃, hq2]; simp
      all_goals
        rw [hσ₃, hq2]; simp only [arrs_setVar]
        rw [ha1 _ (by decide), h0arr]; simp [extOf]
    · simp only [hσ₃, vars_setVar, ↓reduceIte]
      exact MatchInv.zero _ _ _
  -- the searches
  obtain ⟨σ₄, K₄, hr4, hI₄, hl4, hK₄⟩ := outerLoop_run hg hB hI₃
  have hl3 : σ₃.vars "l0" = 0 := by simp [hσ₃]
  rw [hl3, Nat.sub_zero] at hK₄
  obtain ⟨-, μ, b, hR₄, hM₄⟩ := hI₄
  rw [hl4] at hM₄
  have hout4 : σ₄.out = [] := by
    rw [hr4.out_eq (by decide), hσ₃, hq2]; simpa using hout1
  -- the count
  have hnB : nw x < B := by have := hg.n_lt; omega
  have hmB : mw x + 1 < B := by have := hg.m_lt; omega
  obtain ⟨σ₅, hr5, hq5, hfv5, -, -, hfo5⟩ :=
    (countCom_spec (B := B) (μ := μ) (m := mw x) hmB
      (fun j l hj => by have := hM₄.hμn le_rfl j l hj; omega)).frame.run
      (σ := σ₄) ⟨hR₄.m, hR₄.mu⟩
  have hv5 : ∀ y, y ≠ "count" → y ≠ "j" → σ₅.vars y = σ₄.vars y := fun y h1 h2 =>
    hfv5 y (by simp [countCom, countBody, Com.wvars, h1, h2])
  refine ⟨σ₅, _, hr1.seq (hr2.seq (hr3.seq (hr4.seq hr5))), ?_, ?_, ?_, ?_, ?_⟩
  · unfold preCost; omega
  · rw [hq5]
    unfold kuhnSize cnt
    rw [← size_muF_eq (hM₄.hμn le_rfl), hM₄.size_eq_kuhn]
  · rw [hv5 _ (by decide) (by decide)]; exact hR₄.n
  · rw [hv5 _ (by decide) (by decide)]; exact hR₄.V
  · rw [hfo5 (by decide)]; exact hout4

end Lax117284Proofs.Bipartite.Ram2

end
