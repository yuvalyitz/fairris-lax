import Lax808846Proofs.Tactic
import Lax808846Proofs.Lib.Csr
import Lax808846Proofs.Lib.Queue
import Lax808846Proofs.Lib.Fill

/-!
Breadth-first search over a directed graph in compressed-row form, as an IMP+ command with a
proved specification: the marks array ends up as the indicator of the nodes reachable from the
source, at a cost linear in the number of nodes and slots.

The program is the search loop of `Lax271696Proofs.CC` (the connected-components driver) over a
directed structure, marking reachability instead of labelling: the marks are cleared first, the
source is marked and enqueued, and the queue is drained, each dequeued node having its whole row
scanned and every unmarked target marked and enqueued.

The invariant of the drain (`Base`) is the one of that driver with the labels replaced by marks:
the queue holds exactly the marked nodes, without repetition, all reachable from the source; the
source is marked; and every node before `head` has had its whole row looked at, so its successors
are marked. At exit `head = tail`, so the marked set is closed under the successor relation,
contains the source, and consists of reachable nodes — hence it is the reachable set.

The cost is paid out of the potential `26 · (E − scanned) + 23 · (N − head)`, where `scanned`
is the total length of the rows of the nodes already dequeued — read off the queue itself, so no
counting scalar is needed. A turn of the drain dequeues a node of row length `r`, costs at most
`26 r + 19`, and drops the potential by exactly `26 r + 23`.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Bfs

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib

/-! ### Reachability, on the offset and target functions alone -/

/-- `b` is a successor of `a`: some slot of row `a` names it. -/
def Succ (off tgt : ℕ → ℕ) (a b : ℕ) : Prop := ∃ j, off a ≤ j ∧ j < off (a + 1) ∧ tgt j = b

/-- The nodes reachable from `s`. -/
def Reach (off tgt : ℕ → ℕ) (s : ℕ) : ℕ → Prop := Relation.ReflTransGen (Succ off tgt) s

/-- The pure content of the `Csr` relation: what the offsets and the targets satisfy,
independently of any state. -/
structure CsrOk (N E : ℕ) (off tgt : ℕ → ℕ) : Prop where
  mono : ∀ i, i < N → off i ≤ off (i + 1)
  last : off N = E
  tgt_lt : ∀ p, p < E → tgt p < N

variable {B N E s : ℕ} {off tgt Vf Q : ℕ → ℕ} {head tail : ℕ}

theorem CsrOk.of_csr {σ : Env} (h : Csr "off" "tgt" N E N off tgt σ) : CsrOk N E off tgt :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem CsrOk.csr (h : CsrOk N E off tgt) {σ : Env} (ho : σ.arrs "off" = arrOf (N + 1) off)
    (ht : σ.arrs "tgt" = arrOf E tgt) : Csr "off" "tgt" N E N off tgt σ :=
  ⟨ho, ht, h.mono, h.last, h.tgt_lt⟩

theorem CsrOk.off_mono (h : CsrOk N E off tgt) {i k : ℕ} (hik : i ≤ k) (hk : k ≤ N) :
    off i ≤ off k := by
  induction k with
  | zero =>
      have : i = 0 := by omega
      subst this; exact le_rfl
  | succ k ih =>
      by_cases hik' : i ≤ k
      · exact le_trans (ih hik' (by omega)) (h.mono k (by omega))
      · have : i = k + 1 := by omega
        subst this; exact le_rfl

/-- A row of a node ends inside the target array. -/
theorem CsrOk.row_le (h : CsrOk N E off tgt) {v : ℕ} (hv : v < N) : off (v + 1) ≤ E :=
  h.last ▸ h.off_mono (by omega) le_rfl

/-- The rows tile the target array. -/
theorem CsrOk.sum_rowLen (h : CsrOk N E off tgt) :
    ∑ i ∈ Finset.range N, Csr.rowLen off i ≤ E := by
  have key : ∀ k, k ≤ N → ∑ i ∈ Finset.range k, Csr.rowLen off i = off k - off 0 := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih (by omega)]
        have h₁ : off 0 ≤ off k := h.off_mono (by omega) (by omega)
        have h₂ : off k ≤ off (k + 1) := h.mono k (by omega)
        simp only [Csr.rowLen]; omega
  rw [key N le_rfl, h.last]; omega

/-- The rows of distinct nodes together fit in the target array. -/
theorem CsrOk.sum_le (h : CsrOk N E off tgt) {Q : ℕ → ℕ} {k : ℕ} (hQ : ∀ i, i < k → Q i < N)
    (hinj : ∀ i, i < k → ∀ j, j < k → Q i = Q j → i = j) :
    ∑ i ∈ Finset.range k, Csr.rowLen off (Q i) ≤ E := by
  have himg : ∑ v ∈ (Finset.range k).image Q, Csr.rowLen off v
      = ∑ i ∈ Finset.range k, Csr.rowLen off (Q i) :=
    Finset.sum_image
      (fun i hi j hj hij => hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hij)
  rw [← himg]
  refine le_trans (Finset.sum_le_sum_of_subset ?_) h.sum_rowLen
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
  exact Finset.mem_range.2 (hQ i (Finset.mem_range.1 hi))

/-! ### What holds throughout the search -/

/-- The state of the marks and the queue, at any point of the search. -/
structure Base (off tgt : ℕ → ℕ) (N s : ℕ) (Vf Q : ℕ → ℕ) (head tail : ℕ) : Prop where
  /-- Every mark is a bit. -/
  bit : ∀ w, w < N → Vf w ≤ 1
  /-- The queue is a segment. -/
  hd : head ≤ tail
  /-- The queue holds nodes. -/
  tl : tail ≤ N
  /-- Everything on the queue is a marked node. -/
  qmem : ∀ i, i < tail → Q i < N ∧ Vf (Q i) = 1
  /-- Every marked node is on the queue. -/
  qall : ∀ w, w < N → Vf w = 1 → ∃ i, i < tail ∧ Q i = w
  /-- Nothing is on the queue twice. -/
  qinj : ∀ i, i < tail → ∀ j, j < tail → Q i = Q j → i = j
  /-- Everything on the queue is reachable. -/
  reach : ∀ i, i < tail → Reach off tgt s (Q i)
  /-- The source is marked. -/
  src : Vf s = 1
  /-- The row of a node before `head` has been looked at: its successors are marked. -/
  exp : ∀ i, i < head → ∀ j, off (Q i) ≤ j → j < off (Q i + 1) → Vf (tgt j) = 1

/-- An unmarked node is not on the queue, so there is room for one more. -/
theorem Base.tail_lt (hB : Base off tgt N s Vf Q head tail) {w : ℕ} (hw : w < N)
    (hV : Vf w = 0) : tail < N := by
  have hsub : (Finset.range tail).image Q ⊆ (Finset.range N).erase w := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
    have hi' := Finset.mem_range.1 hi
    refine Finset.mem_erase.2 ⟨fun h => ?_, Finset.mem_range.2 (hB.qmem i hi').1⟩
    have := (hB.qmem i hi').2
    rw [h, hV] at this
    exact absurd this (by omega)
  have hcard : ((Finset.range tail).image Q).card = tail := by
    rw [Finset.card_image_of_injOn (fun i hi j hj h =>
      hB.qinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) h)]
    exact Finset.card_range tail
  have := Finset.card_le_card hsub
  rw [hcard, Finset.card_erase_of_mem (Finset.mem_range.2 hw), Finset.card_range] at this
  omega

/-- Marking an unmarked reachable node and enqueuing it. -/
theorem Base.enqueue (hB : Base off tgt N s Vf Q head tail) {w : ℕ} (hw : w < N)
    (hnew : Vf w = 0) (hr : Reach off tgt s w) :
    Base off tgt N s (upd Vf w 1) (upd Q tail w) head (tail + 1) := by
  have htail : tail < N := hB.tail_lt hw hnew
  have hhd := hB.hd
  have hQne : ∀ p, p < tail → Q p ≠ w := fun p hp hpw => by
    have := (hB.qmem p hp).2
    rw [hpw, hnew] at this
    omega
  refine ⟨fun z hz => upd_le (le_refl 1) (hB.bit z hz), by omega, by omega, fun i hi => ?_,
    fun z hz hz1 => ?_, fun i hi j hj hij => ?_, fun i hi => ?_, ?_, fun i hi j hj₁ hj₂ => ?_⟩
  · by_cases hit : i = tail
    · rw [hit, upd_self, upd_self]; exact ⟨hw, rfl⟩
    · have hi' : i < tail := by omega
      rw [upd_of_ne _ hit, upd_of_ne _ (hQne i hi')]
      exact hB.qmem i hi'
  · by_cases hzw : z = w
    · exact ⟨tail, by omega, by rw [upd_self, hzw]⟩
    · rw [upd_of_ne _ hzw] at hz1
      obtain ⟨i, hi, rfl⟩ := hB.qall z hz hz1
      exact ⟨i, by omega, upd_of_ne _ (by omega)⟩
  · by_cases hit : i = tail <;> by_cases hjt : j = tail
    · omega
    · rw [hit, upd_self, upd_of_ne _ hjt] at hij
      exact absurd hij.symm (hQne j (by omega))
    · rw [hjt, upd_self, upd_of_ne _ hit] at hij
      exact absurd hij (hQne i (by omega))
    · rw [upd_of_ne _ hit, upd_of_ne _ hjt] at hij
      exact hB.qinj i (by omega) j (by omega) hij
  · by_cases hit : i = tail
    · rw [hit, upd_self]; exact hr
    · rw [upd_of_ne _ hit]; exact hB.reach i (by omega)
  · by_cases hsw : s = w
    · rw [hsw, upd_self]
    · rw [upd_of_ne _ hsw]; exact hB.src
  · have hit : i ≠ tail := by omega
    rw [upd_of_ne _ hit] at hj₁ hj₂
    by_cases htw : tgt j = w
    · rw [htw, upd_self]
    · rw [upd_of_ne _ htw]; exact hB.exp i hi j hj₁ hj₂

/-- Moving the head on, once the row of the node at the head has been looked at. -/
theorem Base.advance (hB : Base off tgt N s Vf Q head tail) (hht : head < tail)
    (hrow : ∀ j, off (Q head) ≤ j → j < off (Q head + 1) → Vf (tgt j) = 1) :
    Base off tgt N s Vf Q (head + 1) tail := by
  refine ⟨hB.bit, hht, hB.tl, hB.qmem, hB.qall, hB.qinj, hB.reach, hB.src,
    fun i hi j hj₁ hj₂ => ?_⟩
  rcases Nat.lt_or_ge i head with h | h
  · exact hB.exp i h j hj₁ hj₂
  · have : i = head := by omega
    subst this; exact hrow j hj₁ hj₂

/-- **The exit argument, one direction.** When the queue is empty, every reachable node is a
marked node: the marked set is closed under the successor relation. -/
theorem Base.reach_marked (hc : CsrOk N E off tgt) (hs : s < N)
    (hB : Base off tgt N s Vf Q tail tail) {w : ℕ} (h : Reach off tgt s w) :
    w < N ∧ Vf w = 1 := by
  induction h with
  | refl => exact ⟨hs, hB.src⟩
  | tail _ hstep ih =>
      obtain ⟨j, hj₁, hj₂, rfl⟩ := hstep
      obtain ⟨i, hi, rfl⟩ := hB.qall _ ih.1 ih.2
      have hjE : j < E := lt_of_lt_of_le hj₂ (hc.row_le ih.1)
      exact ⟨hc.tgt_lt j hjE, hB.exp i hi j hj₁ hj₂⟩

/-- And the other: a marked node is on the queue, hence reachable. -/
theorem Base.marked_reach (hB : Base off tgt N s Vf Q head tail) {w : ℕ} (hw : w < N)
    (h : Vf w = 1) : Reach off tgt s w := by
  obtain ⟨i, hi, rfl⟩ := hB.qall w hw h
  exact hB.reach i hi

open scoped Classical in
/-- **At exit the marks are the indicator of reachability.** -/
theorem Base.exit (hc : CsrOk N E off tgt) (hs : s < N)
    (hB : Base off tgt N s Vf Q tail tail) :
    arrOf N Vf = arrOf N (fun v => if Reach off tgt s v then 1 else 0) := by
  refine arrOf_congr fun w hw => ?_
  have hbit := hB.bit w hw
  by_cases hr : Reach off tgt s w
  · rw [if_pos hr]; exact (hB.reach_marked hc hs hr).2
  · rw [if_neg hr]
    rcases Nat.eq_zero_or_pos (Vf w) with h0 | hpos
    · exact h0
    · exact absurd (hB.marked_reach hw (by omega)) hr

/-- A list of length `n` is the array of its own entries. -/
theorem eq_arrOf_getD (l : List ℕ) (n : ℕ) (h : l.length = n) :
    l = arrOf n (fun i => l.getD i 0) := by
  subst h
  refine List.ext_getElem (by simp) fun k h₁ _ => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁]

/-- The state after the source has been marked and enqueued: the search's starting point. -/
theorem Base.init (hs : s < N) (Q₀ : ℕ → ℕ) :
    Base off tgt N s (upd (fun _ => 0) s 1) (upd Q₀ 0 s) 0 1 := by
  refine ⟨fun z hz => upd_le (le_refl 1) (Nat.zero_le 1), by omega, by omega, fun i hi => ?_,
    fun w hw h1 => ⟨0, by omega, ?_⟩, fun i hi j hj _ => by omega, fun i hi => ?_,
    upd_self _ _ _, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  · have : i = 0 := by omega
    subst this; simp [hs]
  · by_cases hws : w = s
    · rw [upd_self, hws]
    · rw [upd_of_ne _ hws] at h1; simp at h1
  · have : i = 0 := by omega
    subst this; rw [upd_self]; exact Relation.ReflTransGen.refl

/-! ### The program -/

/-- Clear the marks: `i := 0; while i < N do (vis[i] := 0; i := i + 1)`. -/
def clear : Com :=
  .seq (.assign "i" (.lit 0))
    (.while (.lt (.var "i") (.var "N"))
      (.seq (.store "vis" (.var "i") (.lit 0)) (.assign "i" (.add (.var "i") (.lit 1)))))

/-- Look at the slot `j`: if the node it names is unmarked, mark it and enqueue it. -/
def scanBody : Com :=
  .seq (.assign "v" (.get "tgt" (.var "j")))
    (.seq (.ite (.eq (.get "vis" (.var "v")) (.lit 0))
            (.seq (.store "vis" (.var "v") (.lit 1))
              (.seq (.store "q" (.var "tail") (.var "v"))
                (.assign "tail" (.add (.var "tail") (.lit 1)))))
            .skip)
      (.assign "j" (.add (.var "j") (.lit 1))))

/-- Take the next node off the queue and scan its whole row. The head moves *after* the scan,
so that "the nodes before `head` have been expanded" is an invariant of the scan as well. -/
def expandBody : Com :=
  .seq (.assign "u" (.get "q" (.var "head")))
    (.seq (.assign "j" (.get "off" (.var "u")))
      (.seq (.assign "jend" (.get "off" (.add (.var "u") (.lit 1))))
        (.seq (.while (.lt (.var "j") (.var "jend")) scanBody)
          (.assign "head" (.add (.var "head") (.lit 1))))))

/-- Empty the queue: the search itself. -/
def drain : Com := .while (.lt (.var "head") (.var "tail")) expandBody

/-- Mark and enqueue the source, then drain the queue. -/
def initDrain : Com :=
  .seq (.assign "head" (.lit 0))
    (.seq (.assign "tail" (.lit 0))
      (.seq (.store "q" (.var "tail") (.var "s"))
        (.seq (.assign "tail" (.add (.var "tail") (.lit 1)))
          (.seq (.store "vis" (.var "s") (.lit 1)) drain))))

/-- The whole search: clear the marks, mark and enqueue the source, drain the queue. -/
def bfs : Com := .seq clear initDrain

/-- The constant of the running time: `bfs` costs at most `Kbfs · (N + E + 1)`. -/
def Kbfs : ℕ := 40

@[simp] theorem Kbfs_eq : Kbfs = 40 := rfl

/-! ### The state of the machine -/

/-- The arrays and the two scalars the search does not move. -/
def SearchEnv (N E s : ℕ) (off tgt Vf Q : ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars "N" = N ∧ τ.vars "s" = s ∧
  τ.arrs "off" = arrOf (N + 1) off ∧ τ.arrs "tgt" = arrOf E tgt ∧
  τ.arrs "vis" = arrOf N Vf ∧ τ.arrs "q" = arrOf N Q

/-- The total length of the rows of the nodes already dequeued, read off the queue. -/
def scanned (off : ℕ → ℕ) (τ : Env) : ℕ :=
  ∑ i ∈ Finset.range (τ.vars "head"), Csr.rowLen off ((τ.arrs "q").getD i 0)

/-- The potential the search is paid out of: twenty-six per slot not yet looked at,
twenty-three per node not yet dequeued. -/
def Pot (N E : ℕ) (off : ℕ → ℕ) (τ : Env) : ℕ :=
  26 * (E - scanned off τ) + 23 * (N - τ.vars "head")

/-! ### Scanning one row -/

/-- The invariant of the row scan of the node `u` at position `head`: the position reached in
the row, the slots already looked at marked, and the queue below `head` untouched. -/
def ScanInv (N E s : ℕ) (off tgt : ℕ → ℕ) (u head : ℕ) (Q₀ : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ Vf Q, SearchEnv N E s off tgt Vf Q τ ∧ Base off tgt N s Vf Q head (τ.vars "tail") ∧
    τ.vars "head" = head ∧ head < τ.vars "tail" ∧ Q head = u ∧
    τ.vars "jend" = off (u + 1) ∧
    off u ≤ τ.vars "j" ∧ τ.vars "j" ≤ off (u + 1) ∧
    (∀ j', off u ≤ j' → j' < τ.vars "j" → Vf (tgt j') = 1) ∧
    (∀ i, i < head + 1 → Q i = Q₀ i)

/-- One slot of the row of `u`: if it names an unmarked node, that node is marked and enqueued.
The block is walked by `run_vcg`; what is left is what the two paths did. -/
theorem scanBody_run (hc : CsrOk N E off tgt) {u head : ℕ} (hu : u < N)
    (hB : N + E + 16 < B) {Q₀ : ℕ → ℕ} {τ : Env}
    (hI : ScanInv N E s off tgt u head Q₀ τ) (hjlt : τ.vars "j" < off (u + 1)) :
    ∃ τ' K, Run B scanBody τ τ' K ∧ K ≤ 22 ∧
      ScanInv N E s off tgt u head Q₀ τ' ∧ τ'.vars "j" = τ.vars "j" + 1 := by
  obtain ⟨Vf, Q, ⟨hn, hsv, hoff, htgt, hvis, hq⟩, hL, hhead, hht, hqu, hje, hj₁, hj₂, hscan,
    hq₀⟩ := hI
  have htl := hL.tl
  have hhd := hL.hd
  have hE : off (u + 1) ≤ E := hc.row_le hu
  have hjE : τ.vars "j" < E := by omega
  obtain ⟨w, hw⟩ : ∃ w, tgt (τ.vars "j") = w := ⟨_, rfl⟩
  have hwn : w < N := hw ▸ hc.tgt_lt _ hjE
  have hru : Reach off tgt s u := hqu ▸ hL.reach head hht
  have hrw : Reach off tgt s w := hru.tail ⟨τ.vars "j", hj₁, hjlt, hw⟩
  -- what the walk owes: the slot read, the mark read at what it names, and the bounds
  have hrj : (τ.arrs "tgt").getD (τ.vars "j") 0 = w := by
    rw [htgt, getD_arrOf tgt hjE, hw]
  have hrj' : (τ.arrs "tgt")[τ.vars "j"]?.getD 0 = w := by
    rw [← List.getD_eq_getElem?_getD]; exact hrj
  have hvw : (τ.setVar "v" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "v"
      = (τ.arrs "tgt").getD (τ.vars "j") 0 := by simp
  have hbr : ((τ.setVar "v" ((τ.arrs "tgt").getD (τ.vars "j") 0)).arrs "vis").getD
      ((τ.setVar "v" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "v") 0 = Vf w := by
    rw [arrs_setVar, hvw, hrj, hvis, getD_arrOf Vf hwn]
  have hjlen : τ.vars "j" < (τ.arrs "tgt").length := by rw [htgt, length_arrOf]; omega
  have hwB : (τ.arrs "tgt").getD (τ.vars "j") 0 < B := by rw [hrj]; omega
  have hwlen : (τ.arrs "tgt").getD (τ.vars "j") 0 < (τ.arrs "vis").length := by
    rw [hrj, hvis, length_arrOf]; exact hwn
  have hVwB : Vf w < B := by have := hL.bit w hwn; omega
  have hjB : τ.vars "j" + 1 < B := by omega
  have htB : τ.vars "tail" + 1 < B := by omega
  run_vcg
  · -- the node found is unmarked: it is marked and enqueued
    have hnew : Vf w = 0 := by omega
    have htail : τ.vars "tail" < N := hL.tail_lt hwn hnew
    refine ⟨⟨upd Vf w 1, upd Q (τ.vars "tail") w,
      ⟨by simp [hn], by simp [hsv], by simp [hoff], by simp [htgt],
        by simp [hvis, hrj', set_arrOf_eq_upd], by simp [hq, hrj', set_arrOf_eq_upd]⟩,
      by simpa using hL.enqueue hwn hnew hrw, by simp [hhead], by simp; omega,
      by rw [upd_of_ne _ (by omega : head ≠ τ.vars "tail")]; exact hqu,
      by simp [hje], by simp; omega, by simp; omega, ?_,
      fun i hi => by rw [upd_of_ne _ (by omega : i ≠ τ.vars "tail")]; exact hq₀ i hi⟩,
      by simp⟩
    intro j' hj₁' hj₂'
    simp at hj₂'
    by_cases hyw : tgt j' = w
    · rw [hyw, upd_self]
    · rw [upd_of_ne _ hyw]
      rcases Nat.lt_or_ge j' (τ.vars "j") with h | h
      · exact hscan j' hj₁' h
      · exact absurd (show j' = τ.vars "j" by omega) (by rintro rfl; exact hyw hw)
  · -- already marked: nothing is written
    have hVw : Vf w = 1 := by have := hL.bit w hwn; omega
    refine ⟨⟨Vf, Q, by simp [SearchEnv, hn, hsv, hoff, htgt, hvis, hq],
      by simpa using hL, by simp [hhead], by simp [hht], hqu, by simp [hje],
      by simp; omega, by simp; omega, ?_, hq₀⟩, by simp⟩
    intro j' hj₁' hj₂'
    simp at hj₂'
    rcases Nat.lt_or_ge j' (τ.vars "j") with h | h
    · exact hscan j' hj₁' h
    · rw [show j' = τ.vars "j" by omega, hw]; exact hVw
  -- what the walk deferred: the queue has room, because the node just found is unmarked
  all_goals
    (have hnew : Vf w = 0 := by omega
     have := hL.tail_lt hwn hnew
     simp [hq]
     omega)

/-- **The whole row of `u`, scanned.** The loop is the kit's row scan: twenty-six per slot. -/
theorem scan_spec (hc : CsrOk N E off tgt) {u head : ℕ} (hu : u < N)
    (hB : N + E + 16 < B) {Q₀ : ℕ → ℕ} :
    Spec B (fun τ => ScanInv N E s off tgt u head Q₀ τ ∧ τ.vars "j" = off u)
      (.while (.lt (.var "j") (.var "jend")) scanBody)
      (fun _ τ' => ScanInv N E s off tgt u head Q₀ τ' ∧ τ'.vars "j" = off (u + 1))
      (26 * Csr.rowLen off u + 4) := by
  have hE : off (u + 1) ≤ E := hc.row_le hu
  refine Csr.rowScan_spec B (26 * Csr.rowLen off u + 4) (off (u + 1)) 22 "j" "jend" scanBody
    (ScanInv N E s off tgt u head Q₀) (by omega)
    (fun σ hσ => by
      obtain ⟨-, -, -, -, -, -, -, hje, -, hjle, -, -⟩ := hσ
      exact ⟨hje, hjle⟩)
    (fun σ hσ hlt => by
      obtain ⟨σ', K', hr, hK, hI', hj'⟩ := scanBody_run hc hu hB hσ hlt
      exact ⟨σ', K', hr, hI', hj', hK⟩) (fun _ hσ => hσ.1)
    (fun σ hσ => by rw [hσ.2]; simp only [Csr.rowLen]; omega)

/-! ### Emptying the queue -/

/-- The invariant of the drain loop. -/
def DrainInv (N E s : ℕ) (off tgt : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ Vf Q, SearchEnv N E s off tgt Vf Q τ ∧
    Base off tgt N s Vf Q (τ.vars "head") (τ.vars "tail")

/-- Taking one node off the queue and scanning its row: the cost is twenty-six per slot of the
row and nineteen besides, and the scanned total grows by the row's length. -/
theorem expandBody_run (hc : CsrOk N E off tgt) (hB : N + E + 16 < B) {τ : Env}
    (hSE : SearchEnv N E s off tgt Vf Q τ)
    (hL : Base off tgt N s Vf Q (τ.vars "head") (τ.vars "tail"))
    (hht : τ.vars "head" < τ.vars "tail") :
    ∃ (τ' : Env) (K : ℕ), Run B expandBody τ τ' K ∧
      K ≤ 26 * Csr.rowLen off (Q (τ.vars "head")) + 19 ∧ DrainInv N E s off tgt τ' ∧
      τ'.vars "head" = τ.vars "head" + 1 ∧
      scanned off τ' = scanned off τ + Csr.rowLen off (Q (τ.vars "head")) := by
  obtain ⟨hn, hsv, hoff, htgt, hvis, hq⟩ := id hSE
  have htln := hL.tl
  have hheadn : τ.vars "head" < N := by omega
  obtain ⟨u, hudef⟩ : ∃ u, Q (τ.vars "head") = u := ⟨_, rfl⟩
  rw [hudef]
  have hun : u < N := hudef ▸ (hL.qmem _ hht).1
  have hcsr : Csr "off" "tgt" N E N off tgt τ := hc.csr hoff htgt
  -- what the read at the head of the queue owes
  have hru : (τ.arrs "q").getD (τ.vars "head") 0 = u := by
    rw [hq, getD_arrOf Q hheadn, hudef]
  have hru' : (τ.arrs "q")[τ.vars "head"]?.getD 0 = u := by
    rw [← List.getD_eq_getElem?_getD]; exact hru
  have hqlen : τ.vars "head" < (τ.arrs "q").length := by rw [hq, length_arrOf]; omega
  have huB : (τ.arrs "q").getD (τ.vars "head") 0 < B := by rw [hru]; omega
  -- the scan, saying what the turn owes: the invariant one node on
  have hscan : Spec B
      (fun σ => ScanInv N E s off tgt u (τ.vars "head") Q σ ∧ σ.vars "j" = off u)
      (.while (.lt (.var "j") (.var "jend")) scanBody)
      (fun _ σ' => DrainInv N E s off tgt (σ'.setVar "head" (τ.vars "head" + 1)) ∧
        σ'.vars "head" = τ.vars "head" ∧
        scanned off (σ'.setVar "head" (τ.vars "head" + 1))
          = scanned off τ + Csr.rowLen off u ∧
        σ'.vars "head" + 1 < B) (26 * Csr.rowLen off u + 4) :=
    (scan_spec hc hun hB (Q₀ := Q)).post fun _ σ' _ hQ => by
      obtain ⟨⟨Vf', Q', hSE', hL', hhead', hht', hqu', hje', hjge', hjle', hscanned, hq₀'⟩,
        hj₄⟩ := hQ
      obtain ⟨hn', hsv', hoff', htgt', hvis', hq'⟩ := id hSE'
      have htl' := hL'.tl
      refine ⟨⟨Vf', Q', by simpa [SearchEnv] using hSE', ?_⟩, hhead', ?_, by omega⟩
      · -- the search is one node further along
        have hrow : ∀ j, off (Q' (τ.vars "head")) ≤ j → j < off (Q' (τ.vars "head") + 1) →
            Vf' (tgt j) = 1 := by
          rw [hqu']
          intro j hj₁ hj₂
          exact hscanned j hj₁ (by rw [hj₄]; exact hj₂)
        simpa using hL'.advance hht' hrow
      · -- the scanned total is the sum over the dequeued nodes
        simp only [scanned, vars_setVar, arrs_setVar, if_true]
        rw [Finset.sum_range_succ]
        congr 1
        · refine Finset.sum_congr rfl fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          rw [hq', getD_arrOf Q' (by omega), hq₀' i (by omega), hq, getD_arrOf Q (by omega)]
        · rw [hq', getD_arrOf Q' (by omega), hq₀' _ (by omega), hudef]
  run_vcg [Csr.loadRow_spec B N E N "off" "tgt" "u" "j" "jend" off tgt (by decide) (by decide),
    hscan]
  · -- what the block did is what the scan handed back
    simp_all
  · -- the two offset reads: a row of the structure, and its number a word
    exact ⟨⟨by simpa using hcsr, by omega, by omega⟩, by simp [hru']; omega,
      by simp [hru']; omega⟩
  · -- the scan starts at the top of the row, in the state the reads left
    obtain ⟨-, -, -, rfl⟩ := ‹Csr.LoadRowPost "off" "tgt" "u" "j" "jend" N E N off tgt _ _›
    exact ⟨⟨Vf, Q, by simpa [SearchEnv] using hSE, by simpa using hL, by simp,
      by simpa using hht, hudef, by simp [hru'], by simp [hru'],
      (by simpa [hru'] using hc.mono u hun),
      by intro j' h₁ h₂; simp [hru'] at h₂; omega, fun i _ => rfl⟩,
      by simp [hru']⟩

open scoped Classical in
/-- **The search.** The queue is emptied, and the whole cost is paid out of the potential. The
loop is the kit's `Queue.drain_spec`; what is left here is that a turn pays for itself, and the
exit argument. -/
theorem drain_spec (hc : CsrOk N E off tgt) (hs : s < N) (hB : N + E + 16 < B) :
    Spec B (fun τ => DrainInv N E s off tgt τ ∧ τ.vars "head" = 0) drain
      (fun _ τ' => τ'.arrs "vis" = arrOf N (fun v => if Reach off tgt s v then 1 else 0) ∧
        Csr "off" "tgt" N E N off tgt τ' ∧ τ'.vars "N" = N ∧ τ'.vars "s" = s ∧
        (τ'.arrs "q").length = N)
      (26 * E + 23 * N + 4) := by
  refine (Queue.drain_spec B N N (26 * E + 23 * N + 4) "q" "head" "tail" expandBody
    (DrainInv N E s off tgt) (Pot N E off) (fun σ hσ => ?_) (by omega) (fun σ hσ hlt => ?_)
    (fun σ hσ => hσ.1) (fun σ hσ => ?_)).post (fun _ σ' _ hQ => ?_)
  · -- the invariant carries a queue: the marked nodes, in arrival order
    obtain ⟨Vf, Q, ⟨-, -, -, -, -, hq⟩, hL⟩ := hσ
    exact ⟨Q, σ.vars "head", σ.vars "tail", hq, rfl, rfl, hL.hd, hL.tl,
      fun i hi => (hL.qmem i hi).1⟩
  · -- a turn pays for itself out of the potential
    obtain ⟨Vf, Q, hSE, hL⟩ := hσ
    obtain ⟨σ', K, hrun, hK, hI', hhead', hsc'⟩ := expandBody_run hc hB hSE hL hlt
    refine ⟨σ', K, hrun, hI', ?_⟩
    obtain ⟨Vf', Q', hSE', hL'⟩ := hI'
    have hhd := hL'.hd
    have htl := hL'.tl
    have hE : scanned off σ' ≤ E := by
      have hq' := hSE'.2.2.2.2.2
      have : scanned off σ' = ∑ i ∈ Finset.range (σ'.vars "head"), Csr.rowLen off (Q' i) := by
        simp only [scanned]
        refine Finset.sum_congr rfl fun i hi => ?_
        have := Finset.mem_range.1 hi
        rw [hq', getD_arrOf Q' (by omega)]
      rw [this]
      exact hc.sum_le (fun i hi => (hL'.qmem i (by omega)).1)
        (fun i hi j hj h => hL'.qinj i (by omega) j (by omega) h)
    have hhd0 := hL.hd
    have htl0 := hL.tl
    simp only [Pot]
    omega
  · -- the potential at entry
    obtain ⟨-, h0⟩ := hσ
    simp only [Pot, scanned, h0, Finset.range_zero, Finset.sum_empty]
    omega
  · -- the exit: every node on the queue has been expanded
    obtain ⟨⟨Vf, Q, ⟨hn, hsv, hoff, htgt, hvis, hq⟩, hL⟩, hht⟩ := hQ
    rw [hht] at hL
    exact ⟨by rw [hvis]; exact hL.exit hc hs, hc.csr hoff htgt, hn, hsv,
      by rw [hq, length_arrOf]⟩

/-! ### The whole search -/

open scoped Classical in
/-- From cleared marks: the source is marked and enqueued, and the queue drained. -/
theorem initDrain_spec (hs : s < N) (hB : N + E + 16 < B) :
    Spec B
      (fun τ => Csr "off" "tgt" N E N off tgt τ ∧ τ.vars "N" = N ∧ τ.vars "s" = s ∧
        τ.arrs "vis" = arrOf N (fun _ => 0) ∧ (τ.arrs "q").length = N)
      initDrain
      (fun _ τ' => τ'.arrs "vis" = arrOf N (fun v => if Reach off tgt s v then 1 else 0) ∧
        Csr "off" "tgt" N E N off tgt τ' ∧
        τ'.vars "N" = N ∧ τ'.vars "s" = s ∧ (τ'.arrs "q").length = N)
      (26 * E + 23 * N + 18) := by
  intro τ hτ
  obtain ⟨hcsr, hn, hsv, hvis, hql⟩ := hτ
  obtain ⟨hoff, htgt, -, -, -⟩ := id hcsr
  have hc := CsrOk.of_csr hcsr
  have hdrain := drain_spec (B := B) hc hs hB
  obtain ⟨Q₀, hq⟩ : ∃ Q₀, τ.arrs "q" = arrOf N Q₀ := ⟨_, eq_arrOf_getD _ N hql⟩
  have hvl : (τ.arrs "vis").length = N := by rw [hvis, length_arrOf]
  run_vcg [hdrain]
  · exact ‹_›
  · -- the search starts with the source marked and on the queue
    refine ⟨⟨upd (fun _ => 0) s 1, upd Q₀ 0 s,
      ⟨by simp [hn], by simp [hsv], by simp [hoff], by simp [htgt],
        by simp [hvis, hsv, set_arrOf_eq_upd], by simp [hq, hsv, set_arrOf_eq_upd]⟩, ?_⟩,
      by simp⟩
    simpa using Base.init (off := off) (tgt := tgt) hs Q₀

open scoped Classical in
/-- **Breadth-first search.** From a CSR structure of `N` nodes and `E` slots and a source
`s < N`, with a marks array and a queue of length `N`, `bfs` leaves the marks array as the
indicator of the nodes reachable from `s`, at a cost of at most `Kbfs · (N + E + 1)`. -/
theorem bfs_spec {B : ℕ} (N E s : ℕ) (off tgt : ℕ → ℕ) (hs : s < N) (hB : N + E + 16 < B) :
    Spec B
      (fun σ => Csr "off" "tgt" N E N off tgt σ ∧
        σ.vars "N" = N ∧ σ.vars "s" = s ∧ (σ.arrs "vis").length = N ∧ (σ.arrs "q").length = N)
      bfs
      (fun _ σ' => σ'.arrs "vis" = arrOf N (fun v => if Reach off tgt s v then 1 else 0) ∧
        Csr "off" "tgt" N E N off tgt σ' ∧
        σ'.vars "N" = N ∧ σ'.vars "s" = s ∧ (σ'.arrs "q").length = N)
      (Kbfs * (N + E + 1)) := by
  have hclear : Spec B (fun σ => (∃ g, σ.arrs "vis" = arrOf N g) ∧ σ.vars "N" = N) clear
      (fun _ σ' => (∃ g, σ'.arrs "vis" = arrOf N g ∧ ∀ j, j < N → g j = 0) ∧ σ'.vars "i" = N)
      (11 * N + 6) :=
    Fill.loop_spec B N "vis" "i" "N" (.lit 0) (fun _ => 0) (by decide) (by omega)
      (fun _ _ _ _ => evalB_lit (by omega))
  refine ((hclear.frame.pre (P' := fun σ => Csr "off" "tgt" N E N off tgt σ ∧
      σ.vars "N" = N ∧ σ.vars "s" = s ∧ (σ.arrs "vis").length = N ∧ (σ.arrs "q").length = N)
      (fun σ hσ => ⟨⟨_, eq_arrOf_getD _ N hσ.2.2.2.1⟩, hσ.2.1⟩)).seq
    (initDrain_spec (off := off) (tgt := tgt) hs hB) ?_ ?_).mono ?_
  · -- the clearing lands in the search's precondition
    rintro σ σ' ⟨hcsr, hn, hsv, hvl, hql⟩ ⟨⟨⟨g, hg, hg0⟩, -⟩, hvars, harrs, -, -⟩
    have hoff : σ'.arrs "off" = σ.arrs "off" := harrs "off" (by decide)
    have htgt : σ'.arrs "tgt" = σ.arrs "tgt" := harrs "tgt" (by decide)
    refine ⟨hcsr.of_eq hoff htgt, by rw [hvars "N" (by decide), hn],
      by rw [hvars "s" (by decide), hsv], ?_, by rw [harrs "q" (by decide), hql]⟩
    rw [hg]
    exact arrOf_congr fun i hi => hg0 i hi
  · exact fun _ _ _ _ _ hq => hq
  · rw [Kbfs_eq]; omega

end Lax117284Proofs.TwoSAT.Machine.Bfs
