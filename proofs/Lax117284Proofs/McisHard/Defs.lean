import Lax117284.MulticolouredIndepSet
import Lax117284Proofs.Machine.SatSem
import Lax117284Proofs.Machine.SatNk
import Lax117284Proofs.SourceInjectivity
import Lax117284Proofs.Compose
import Lax117284Proofs.Lemma14Graph
import Lax117284Proofs.Machine.WrapTFinal
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# NP-hardness of Multicoloured Independent Set in normal form: the definitions and statements (WP0)

The reduction (see `mcis-notes/DESIGN.md`, `mcis-notes/check_ports.py`): a [2,3]-bounded 3-SAT formula becomes its occurrence
graph `G₀` on the positions; every position gets 5 *ports*, each port a 7-vertex gadget slot `K₇ − {ab, ac, de, fg}` (`a = 0`);
an unmatched port hangs `a` off the position, a matched port pair of positions `(o,j) ↔ (o',j')` joins the two slots' `a`
vertices (a dead pair) and makes `o ~ o'`.  The graph `G'` on `36·S` vertices is 5-regular with `α(G') = α(G₀) + 10·S`.
Then `H = copyInst (p + 10 S) G'` is in normal form and has an independent transversal iff the formula is satisfiable.

The theorems that were work-package goals are proved in the `Proved` namespace (files `*Proofs.lean`, `Ports*.lean`, `FormulaPorts.lean`).
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard

open Lax117284.MulticolouredIndepSet Lax434930.PolynomialTime
open Lax117284.Problems (encodeNat)
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284.BoundedSat

/-! ## M1. The copy reduction (generic in the graph) -/

def copyGraph (k : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : SimpleGraph (Fin k × Fin n) where
  Adj x y := x.1 ≠ y.1 ∧ (x.2 = y.2 ∨ G.Adj x.2 y.2)
  symm := ⟨fun _ _ h => ⟨fun e => h.1 e.symm, h.2.elim (fun e => Or.inl e.symm)
    (fun e => Or.inr (G.adj_comm _ _ |>.1 e))⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def copyInst (k : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Instance where
  colours := k
  size := n
  graph := copyGraph k G
  adj_colour_ne := fun _ _ h => h.1

theorem copyInst_hasIndepSet_iff (k : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    (copyInst k G).HasIndepSet ↔
      ∃ s : Finset (Fin n), G.IsIndepSet (s : Set (Fin n)) ∧ k ≤ s.card := by
  classical
  change (∃ f : Fin k → Fin n, ∀ i i', ¬ (copyGraph k G).Adj (i, f i) (i', f i')) ↔ _
  constructor
  · rintro ⟨f, hf⟩
    have hinj : Function.Injective f := by
      intro i i' h
      by_contra hne
      exact hf i i' ⟨hne, Or.inl h⟩
    refine ⟨Finset.univ.image f, ?_, ?_⟩
    · intro a ha b hb hab
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at ha hb
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨i', rfl⟩ := hb
      intro hadj
      have : i ≠ i' := fun e => hab (by rw [e])
      exact hf i i' ⟨this, Or.inr hadj⟩
    · rw [Finset.card_image_of_injective _ hinj]; simp
  · rintro ⟨s, hs, hk⟩
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hk
    let e : t ≃ Fin k := Finset.equivFinOfCardEq htc
    refine ⟨fun i => (e.symm i).1, fun i i' hadj => ?_⟩
    obtain ⟨hne, h⟩ := hadj
    have hne' : (e.symm i).1 ≠ (e.symm i').1 := by
      intro h'
      exact hne (e.symm.injective (Subtype.ext h'))
    have hi := hts (e.symm i).2
    have hi' := hts (e.symm i').2
    rcases h with h | h
    · exact hne' h
    · exact hs hi hi' hne' h



/-! ## M2. Port graphs -/

def gadAdj (t t' : ℕ) : Prop :=
  t < 7 ∧ t' < 7 ∧ t ≠ t' ∧ ¬ (t = 0 ∧ (t' = 1 ∨ t' = 2)) ∧ ¬ (t' = 0 ∧ (t = 1 ∨ t = 2)) ∧
    ¬ (t = 3 ∧ t' = 4) ∧ ¬ (t = 4 ∧ t' = 3) ∧ ¬ (t = 5 ∧ t' = 6) ∧ ¬ (t = 6 ∧ t' = 5)

instance : DecidableRel gadAdj := fun t t' => by unfold gadAdj; infer_instance

theorem gadAdj_symm {t t' : ℕ} (h : gadAdj t t') : gadAdj t' t := by unfold gadAdj at *; omega


structure IsPortRel (S : ℕ) (R : ℕ → ℕ → ℕ → ℕ → Prop) : Prop where
  lt : ∀ {o j o' j'}, R o j o' j' → o < S ∧ o' < S ∧ j < 5 ∧ j' < 5
  symm : ∀ {o j o' j'}, R o j o' j' → R o' j' o j
  func : ∀ {o j o' j' o'' j''}, R o j o' j' → R o j o'' j'' → o' = o'' ∧ j' = j''
  ne : ∀ {o j o' j'}, R o j o' j' → o ≠ o'
  simple : ∀ {o j o' j' j₂ j₂'}, R o j o' j' → R o j₂ o' j₂' → j = j₂

def portAdjN (R : ℕ → ℕ → ℕ → ℕ → Prop) (u v : ℕ) : Prop :=
  (u % 36 = 0 ∧ v % 36 = 0 ∧ ∃ j j', R (u / 36) j (v / 36) j') ∨
  (u % 36 = 0 ∧ v % 36 ≠ 0 ∧ u / 36 = v / 36 ∧ (v % 36 - 1) % 7 = 0 ∧
      ¬ ∃ o' j', R (u / 36) ((v % 36 - 1) / 7) o' j') ∨
  (u % 36 ≠ 0 ∧ v % 36 = 0 ∧ u / 36 = v / 36 ∧ (u % 36 - 1) % 7 = 0 ∧
      ¬ ∃ o' j', R (v / 36) ((u % 36 - 1) / 7) o' j') ∨
  (u % 36 ≠ 0 ∧ v % 36 ≠ 0 ∧
    ((u / 36 = v / 36 ∧ (u % 36 - 1) / 7 = (v % 36 - 1) / 7 ∧
        gadAdj ((u % 36 - 1) % 7) ((v % 36 - 1) % 7)) ∨
     ((u % 36 - 1) % 7 = 0 ∧ (v % 36 - 1) % 7 = 0 ∧
        R (u / 36) ((u % 36 - 1) / 7) (v / 36) ((v % 36 - 1) / 7))))

def portGraph (R : ℕ → ℕ → ℕ → ℕ → Prop) (S : ℕ) : SimpleGraph (Fin (S * 36)) :=
  SimpleGraph.fromRel fun u v => portAdjN R u.val v.val

def posGraph (R : ℕ → ℕ → ℕ → ℕ → Prop) (S : ℕ) : SimpleGraph (Fin S) :=
  SimpleGraph.fromRel fun o o' => ∃ j j', R o.val j o'.val j'




/-! ## M3. The port relation of a formula, on the numbers of its stream -/

section Sat
variable (ns : List ℕ)

def litV (o : ℕ) : ℕ := ns.getD (3 + 2 * o) 0
def litS (o : ℕ) : ℕ := ns.getD (4 + 2 * o) 0
def compN (o o' : ℕ) : Prop := litV ns o = litV ns o' ∧ litS ns o ≠ litS ns o'
def clSz (o : ℕ) : ℕ := if o < 2 * ns.getD 1 0 then 2 else 3
def clIx (o : ℕ) : ℕ := if o < 2 * ns.getD 1 0 then o % 2 else (o - 2 * ns.getD 1 0) % 3
def clId (o : ℕ) : ℕ :=
  if o < 2 * ns.getD 1 0 then o / 2 else ns.getD 1 0 + (o - 2 * ns.getD 1 0) / 3
def mateN (o j : ℕ) : ℕ := o - clIx ns o + (clIx ns o + j + 1) % clSz ns o

def RN (o j o' j' : ℕ) : Prop :=
  o < SlotsN ns ∧ o' < SlotsN ns ∧
  ((j < 2 ∧ j' < 2 ∧ j + j' + 2 = clSz ns o ∧ o' = mateN ns o j ∧ ¬ compN ns o o') ∨
   (2 ≤ j ∧ j < 4 ∧ 2 ≤ j' ∧ j' < 4 ∧ compN ns o o' ∧ rankN ns o' = j - 2 ∧
      rankN ns o = j' - 2))


def coCountN (o : ℕ) : ℕ :=
  ((List.range (SlotsN ns)).filter fun o' =>
    decide (litV ns o' = litV ns o ∧ litS ns o' ≠ litS ns o)).length

def unmatchedN (o j : ℕ) : Prop :=
  j = 4 ∨ (j < 2 ∧ (clSz ns o ≤ j + 1 ∨ compN ns o (mateN ns o j))) ∨
    (2 ≤ j ∧ j < 4 ∧ coCountN ns o ≤ j - 2)


def occGraphN : SimpleGraph (Fin (SlotsN ns)) :=
  SimpleGraph.fromRel fun o o' => clId ns o.val = clId ns o'.val ∨ compN ns o.val o'.val



def Hinst : Instance :=
  copyInst (ns.getD 1 0 + ns.getD 2 0 + 10 * SlotsN ns) (portGraph (RN ns) (SlotsN ns))

def H0 : Instance := copyInst 2 (⊥ : SimpleGraph (Fin 4))

open Classical in
noncomputable def Hfin : Instance := if SlotsN ns = 0 then H0 else Hinst ns

end Sat



/-! ## M4. From the graph to the bits the machine writes -/

def kOf (ns : List ℕ) : ℕ :=
  if SlotsN ns = 0 then 2 else ns.getD 1 0 + ns.getD 2 0 + 10 * SlotsN ns
def nOf (ns : List ℕ) : ℕ := if SlotsN ns = 0 then 4 else SlotsN ns * 36

def adjF (ns : List ℕ) (w w' : ℕ) : Prop :=
  w / nOf ns ≠ w' / nOf ns ∧
    (w % nOf ns = w' % nOf ns ∨
      (SlotsN ns ≠ 0 ∧ portAdjN (RN ns) (w % nOf ns) (w' % nOf ns)))


/-! ## M5. The reduction on words -/

open Classical in
noncomputable def reduceMcis (w : Word) : Word :=
  if h : ∃ φ : Formula, encodeFormula φ = w ∧ φ.vars ≤ slots φ then
    encodeInstance (Hfin (valsOf h.choose))
  else []

theorem sat_of_slots_zero (φ : Formula) (h : slots φ = 0) : φ.Satisfiable := by
  have h1 : φ.twoClauses = 0 := by unfold slots at h; omega
  have h2 : φ.threeClauses = 0 := by unfold slots at h; omega
  refine ⟨fun _ => true, fun c => ?_, fun c => ?_⟩
  · exact absurd c.isLt (by omega)
  · exact absurd c.isLt (by omega)


end Lax117284Proofs.McisHard
