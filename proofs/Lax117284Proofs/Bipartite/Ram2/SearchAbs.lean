import Lax117284Proofs.Bipartite.Ram2.SearchMath
import Lax117284Proofs.Bipartite.Ram2.Word

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
