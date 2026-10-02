import Lax117284Proofs.Theorem4TwTree
import Lax117284Proofs.Theorem4TwDigits
import Lax117284Proofs.Theorem4TwBags
import Lax117284Proofs.Theorem4TwMask
import Lax117284Proofs.Theorem4TreewidthDP

/-!
# The Dynamic Program over a Decomposition Word, as a Function on Numbers

`TB D i e` says that the table of node `i` holds the restriction `e`, a number whose digits are
the sets of days of the clients of the bag, in increasing order. It is defined by the four
recurrences of the table of `Theorem4TreewidthDP.lean`, and `tab_TB` says it is that table.
-/

namespace Lax117284Proofs.TwDP

open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwMask
open Lax117284Proofs.Model Lax117284Proofs.TwTree

/-- The sorted bag of node `i`, as a list of client numbers. -/
def bagL (D : List ℕ) : ℕ → List ℕ
  | 0 => []
  | i + 1 =>
      if kind D (i + 1) = 1 then
        (bagL D i).insertIdx (pos (bagL D i) (vertex D (i + 1))) (vertex D (i + 1))
      else if kind D (i + 1) = 2 then
        (bagL D i).eraseIdx (pos (bagL D i) (vertex D (i + 1)))
      else if kind D (i + 1) = 3 then bagL D i
      else []

variable (I : Lax117284.Scheduling.Instance) (kk : ℕ) (D : List ℕ)

/-- The clients `bl[t]` and `bl[t']` do not conflict on day `d` when both are served. -/
def feasE (bl : List ℕ) (e : ℕ) : Prop :=
  ∀ d < I.days, ∀ t < bl.length, ∀ t' < t,
    (dg (2 ^ I.days) e t).testBit d = true → (dg (2 ^ I.days) e t').testBit d = true →
      ¬ I.ConflictAt d bl[t]! bl[t']!

/-- Every client of the bag is served on at least `kk` days. -/
def fairE (bl : List ℕ) (e : ℕ) : Prop :=
  ∀ t < bl.length, kk ≤ popc I.days (dg (2 ^ I.days) e t)

/-- **The table of node `i`**, as a predicate on the restriction `e`. -/
def TB : ℕ → ℕ → Prop
  | 0, e => e = 0
  | i + 1, e =>
      if kind D (i + 1) = 1 then
        feasE I (bagL D (i + 1)) e ∧ fairE I kk (bagL D (i + 1)) e ∧
          TB i (rmN (2 ^ I.days) (pos (bagL D i) (vertex D (i + 1))) e)
      else if kind D (i + 1) = 2 then
        ∃ S < 2 ^ I.days, TB i (insN (2 ^ I.days) (pos (bagL D i) (vertex D (i + 1))) S e)
      else if kind D (i + 1) = 3 then
        TB i e ∧ (if h : other D (i + 1) < i + 1 then TB (other D (i + 1)) e else False)
      else e = 0
termination_by i => i
decreasing_by all_goals (try simp_wf) <;> omega


/-! ### The sorted bags -/

section Bags

variable {I} {w : ℕ} {D}

/-- The sorted bag of a node is increasing and lists exactly the clients of the bag. -/
lemma bagL_spec (hD : NiceDecomposition I w D) : ∀ i, i < nodeCount D →
    (bagL D i).Pairwise (· < ·) ∧ ∀ x, x ∈ bagL D i ↔
      ∃ h : x < I.clients, (⟨x, h⟩ : Fin I.clients) ∈ bagAt I.clients D i := by
  intro i
  induction i with
  | zero => intro _; simp [bagL, bagAt]
  | succ i ih =>
    intro hi
    obtain ⟨hp, hm⟩ := ih (by omega)
    have hshape := hD.shape (i + 1) hi
    rcases hshape with h0 | ⟨_, hk, hv', hnot⟩ | ⟨_, hk, hv', hin⟩ | ⟨_, hk, ho, hb⟩
    · simp [bagL, bagAt, h0]
    · have hvn : vertex D (i + 1) ∉ bagL D i := by
        intro h
        obtain ⟨h1, h2⟩ := (hm _).1 h
        exact hnot hv' (by simpa using h2)
      have hbl : bagL D (i + 1) = ordIns (vertex D (i + 1)) (bagL D i) := by
        rw [bagL, if_pos hk]; exact insertIdx_pos hp hvn
      refine ⟨by rw [hbl]; exact ordIns_pairwise hp hvn, fun x => ?_⟩
      rw [hbl, mem_ordIns, bagAt_succ_intro hk hv', hm]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨hv', by simp⟩
        · exact ⟨h1, Finset.mem_insert_of_mem h2⟩
      · rintro ⟨h1, h2⟩
        rcases Finset.mem_insert.1 h2 with h | h
        · left; simpa using congrArg Fin.val h
        · right; exact ⟨h1, h⟩
    · have hvl : vertex D (i + 1) ∈ bagL D i := (hm _).2 ⟨hv', by simpa using hin hv'⟩
      obtain ⟨-, -, hea⟩ := getElem_pos hp hvl
      have hbl : bagL D (i + 1) = (bagL D i).erase (vertex D (i + 1)) := by
        rw [bagL, if_neg (by omega), if_pos hk]; exact hea
      refine ⟨by rw [hbl]; exact erase_pairwise hp, fun x => ?_⟩
      rw [hbl, mem_erase_pairwise hp, bagAt_succ_forget hk hv', hm]
      constructor
      · rintro ⟨⟨h1, h2⟩, hne⟩
        refine ⟨h1, Finset.mem_erase.2 ⟨fun h => hne (by simpa using congrArg Fin.val h), h2⟩⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨hne, h3⟩ := Finset.mem_erase.1 h2
        exact ⟨⟨h1, h3⟩, fun h => hne (Fin.ext h)⟩
    · have hbl : bagL D (i + 1) = bagL D i := by
        rw [bagL, if_neg (by omega), if_neg (by omega), if_pos hk]
      rw [hbl, bagAt_succ_join hk]
      exact ⟨hp, hm⟩

end Bags


/-! ### Restrictions of schedules as numbers -/

section Enc

variable (I : Lax117284.Scheduling.Instance)

/-- Client `j` is served on day `d` by `σ`, for numbers `j`, `d` (false outside the instance). -/
def memb (σ : Fin I.days → Finset (Fin I.clients)) (j d : ℕ) : Bool :=
  if h : j < I.clients then
    (if h' : d < I.days then decide ((⟨j, h⟩ : Fin I.clients) ∈ σ ⟨d, h'⟩) else false)
  else false

/-- The set of days on which client `j` is served, as a number. -/
def maskOf (σ : Fin I.days → Finset (Fin I.clients)) (j : ℕ) : ℕ := bitsOf (memb I σ j) I.days

/-- The restriction of `σ` to the clients of the list `bl`, as a number. -/
def encS (σ : Fin I.days → Finset (Fin I.clients)) (bl : List ℕ) : ℕ :=
  enc (2 ^ I.days) (bl.map (maskOf I σ))

/-- `σ` serves only clients of the list. -/
def DefOn (σ : Fin I.days → Finset (Fin I.clients)) (bl : List ℕ) : Prop :=
  ∀ d, ∀ j ∈ σ d, j.val ∈ bl

variable {I}
variable {σ τ : Fin I.days → Finset (Fin I.clients)} {bl : List ℕ}

lemma maskOf_lt (σ) (j : ℕ) : maskOf I σ j < 2 ^ I.days := bitsOf_lt _ _

lemma testBit_maskOf (σ) (j : ℕ) {d : ℕ} (hd : d < I.days) :
    (maskOf I σ j).testBit d = memb I σ j d := by
  simp [maskOf, testBit_bitsOf, hd]

lemma memb_fin (σ) (j : Fin I.clients) (d : Fin I.days) : memb I σ j d = true ↔ j ∈ σ d := by
  simp [memb, j.isLt, d.isLt]

lemma memb_fin' (σ) {j d : ℕ} (hj : j < I.clients) (hd : d < I.days) :
    memb I σ j d = true ↔ (⟨j, hj⟩ : Fin I.clients) ∈ σ ⟨d, hd⟩ := by
  simp [memb, hj, hd]

lemma encS_lt (σ) (bl : List ℕ) : encS I σ bl < (2 ^ I.days) ^ bl.length := by
  have := enc_lt (b := 2 ^ I.days) (Nat.two_pow_pos _) (bl.map (maskOf I σ))
    (fun a ha => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha; exact maskOf_lt σ x)
  simpa [encS] using this

lemma dg_encS (σ) {bl : List ℕ} {t : ℕ} (ht : t < bl.length) :
    dg (2 ^ I.days) (encS I σ bl) t = maskOf I σ bl[t]! := by
  have := dg_enc (b := 2 ^ I.days) (Nat.two_pow_pos _) (bl.map (maskOf I σ))
    (fun a ha => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha; exact maskOf_lt σ x) t (by simpa using ht)
  rw [encS, this]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ht]

/-- **A schedule serving only the clients of a list is determined by its number.** -/
lemma encS_inj (hσ : DefOn I σ bl) (hτ : DefOn I τ bl) (h : encS I σ bl = encS I τ bl) : σ = τ := by
  have key : ∀ (σ τ : Fin I.days → Finset (Fin I.clients)), DefOn I σ bl →
      encS I σ bl = encS I τ bl → ∀ d j, j ∈ σ d → j ∈ τ d := by
    intro σ τ hσ h d j hj
    obtain ⟨t, ht, hbt⟩ := List.mem_iff_getElem.1 (hσ d j hj)
    have h1 := dg_encS σ ht
    have h2 := dg_encS τ ht
    rw [h] at h1
    have h3 : maskOf I σ bl[t]! = maskOf I τ bl[t]! := by rw [← h1, h2]
    have h4 : memb I σ j d = memb I τ j d := by
      have := congrArg (fun x => x.testBit d) h3
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ht] at this
      simp only [Option.getD_some, hbt] at this
      rwa [testBit_maskOf σ _ d.isLt, testBit_maskOf τ _ d.isLt] at this
    have := (memb_fin σ j d).2 hj
    rw [h4] at this
    exact (memb_fin τ j d).1 this
  funext d; ext j
  exact ⟨key σ τ hσ h d j, key τ σ hτ h.symm d j⟩

/-- **Every number below the bound is the number of a schedule.** -/
lemma exists_sched (hnd : bl.Nodup) (hlt : ∀ x ∈ bl, x < I.clients) {e : ℕ}
    (he : e < (2 ^ I.days) ^ bl.length) :
    ∃ σ : Fin I.days → Finset (Fin I.clients), DefOn I σ bl ∧ encS I σ bl = e := by
  classical
  let σ : Fin I.days → Finset (Fin I.clients) := fun d =>
    Finset.univ.filter (fun j => ∃ t, ∃ ht : t < bl.length, bl[t] = j.val ∧
      (dg (2 ^ I.days) e t).testBit d = true)
  refine ⟨σ, ?_, ?_⟩
  · intro d j hj
    simp only [σ, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨t, ht, h, -⟩ := hj
    rw [← h]; exact List.getElem_mem ht
  · have hmap : bl.map (maskOf I σ) = (List.range bl.length).map (dg (2 ^ I.days) e) := by
      apply List.ext_getElem (by simp)
      intro t h1' h2
      have h1 : t < bl.length := by simpa using h1'
      simp only [List.getElem_map, List.getElem_range]
      apply eq_of_bits (maskOf_lt σ _) (Nat.mod_lt _ (Nat.two_pow_pos _))
      intro d hd
      rw [testBit_maskOf σ _ hd]
      have hjt := hlt _ (List.getElem_mem h1)
      rw [Bool.eq_iff_iff, memb_fin' σ hjt hd]
      simp only [σ, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨t', ht', h, hb⟩
        have : t' = t := by
          have := (List.Nodup.getElem_inj_iff hnd).1 h
          exact this
        subst this; exact hb
      · intro hb; exact ⟨t, h1, rfl, hb⟩
    unfold encS
    rw [hmap]
    exact enc_map_dg (Nat.two_pow_pos _) _ e he

/-- The restriction of a schedule to a set of clients, on the numbered clients. -/
def restrF (X : Finset (Fin I.clients)) (σ : Fin I.days → Finset (Fin I.clients)) :
    Fin I.days → Finset (Fin I.clients) := fun d => σ d ∩ X

lemma restr_eq (X : Finset (Fin I.clients)) (σ : Fin I.days → Finset (Fin I.clients)) :
    Instance.restr (I := Bridge.model I) X σ = restrF X σ := rfl

/-- The number of days on which client `j` is served. -/
def servedF (σ : Fin I.days → Finset (Fin I.clients)) (j : Fin I.clients) : ℕ :=
  (Finset.univ.filter fun d : Fin I.days => j ∈ σ d).card

/-- The number of days on which client `j` is served is the number of set bits of its number. -/
lemma servedF_popc (σ : Fin I.days → Finset (Fin I.clients)) (j : Fin I.clients) :
    servedF σ j = popc I.days (maskOf I σ j) := by
  rw [servedF, Finset.card_filter, popc,
    ← Fin.sum_univ_eq_sum_range (fun d => if (maskOf I σ j).testBit d then 1 else 0)]
  refine Finset.sum_congr rfl fun (d : Fin I.days) _ => ?_
  rw [testBit_maskOf σ _ d.isLt]
  by_cases h : j ∈ σ d
  · have := (memb_fin σ j d).2 h
    rw [if_pos h, if_pos this]
  · have : ¬ memb I σ j d = true := fun h' => h ((memb_fin σ j d).1 h')
    rw [if_neg h, if_neg this]

lemma maskOf_restr (σ : Fin I.days → Finset (Fin I.clients)) (X : Finset (Fin I.clients)) {j : ℕ}
    (hj : ∃ h : j < I.clients, (⟨j, h⟩ : Fin I.clients) ∈ X) :
    maskOf I (restrF X σ) j = maskOf I σ j := by
  obtain ⟨h, hX⟩ := hj
  unfold maskOf
  congr 1
  funext d
  unfold memb
  by_cases hd : d < I.days
  · simp only [h, hd, dite_true, restrF]
    by_cases hm : (⟨j, h⟩ : Fin I.clients) ∈ σ ⟨d, hd⟩
    · simp [hm, hX]
    · simp [hm]
  · simp [hd]

lemma encS_restr (σ : Fin I.days → Finset (Fin I.clients)) (X : Finset (Fin I.clients))
    (hbl : ∀ x ∈ bl, ∃ h : x < I.clients, (⟨x, h⟩ : Fin I.clients) ∈ X) :
    encS I (restrF X σ) bl = encS I σ bl := by
  unfold encS
  congr 1
  exact List.map_congr_left fun x hx => maskOf_restr σ X (hbl x hx)

lemma encS_insertIdx (σ : Fin I.days → Finset (Fin I.clients)) (bl : List ℕ) {p : ℕ}
    (hp : p ≤ bl.length) (v : ℕ) :
    encS I σ (bl.insertIdx p v) = insN (2 ^ I.days) p (maskOf I σ v) (encS I σ bl) := by
  unfold encS
  rw [List.map_insertIdx]
  exact enc_insertIdx (Nat.two_pow_pos _) _ p _ (by simpa using hp) (fun a ha => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha; exact maskOf_lt σ x)

lemma encS_eraseIdx (σ : Fin I.days → Finset (Fin I.clients)) (bl : List ℕ) {p : ℕ}
    (hp : p < bl.length) :
    encS I σ (bl.eraseIdx p) = rmN (2 ^ I.days) p (encS I σ bl) := by
  unfold encS
  rw [← List.eraseIdx_map]
  exact enc_eraseIdx (Nat.two_pow_pos _) p _ (by simpa using hp) (fun a ha => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha; exact maskOf_lt σ x)

lemma getElem!_eq' {bl : List ℕ} {t : ℕ} (ht : t < bl.length) : bl[t]! = bl[t] := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ht]

/-- The bit of a digit says whether the client is served. -/
lemma bit_iff (σ : Fin I.days → Finset (Fin I.clients)) {bl : List ℕ} {t d : ℕ}
    (ht : t < bl.length) (hlt : bl[t] < I.clients) (hd : d < I.days) :
    (dg (2 ^ I.days) (encS I σ bl) t).testBit d = true ↔
      (⟨bl[t], hlt⟩ : Fin I.clients) ∈ σ ⟨d, hd⟩ := by
  rw [dg_encS σ ht, testBit_maskOf σ _ hd, getElem!_eq' ht, memb_fin' σ hlt hd]

/-- Conflict in the development, as the arithmetic conflict of the numbers. -/
lemma conflict_iff' (d : Fin I.days) (j j' : Fin I.clients) :
    Instance.Conflict (I := Bridge.model I) d j j' ↔ I.ConflictAt d j j' :=
  (Bridge.conflict_iff I d j j').symm.trans (Lax117284.Scheduling.Instance.conflictAt_iff I d j j').symm

/-- A member of a bag has a position. -/
lemma pos_of_mem {bl : List ℕ} {X : Finset (Fin I.clients)}
    (hX : ∀ j : Fin I.clients, j ∈ X ↔ j.val ∈ bl) {j : Fin I.clients} (hj : j ∈ X) :
    ∃ t, ∃ ht : t < bl.length, bl[t] = j.val := by
  obtain ⟨t, ht, h⟩ := List.mem_iff_getElem.1 ((hX j).1 hj)
  exact ⟨t, ht, h⟩

/-- **Feasibility is what `feasE` checks.** -/
lemma feasible_iff {bl : List ℕ} {X : Finset (Fin I.clients)} (hnd : bl.Nodup)
    (hlt : ∀ x ∈ bl, x < I.clients) (hX : ∀ j : Fin I.clients, j ∈ X ↔ j.val ∈ bl)
    {σ : Fin I.days → Finset (Fin I.clients)} (hσ : ∀ d, σ d ⊆ X) :
    Instance.Feasible (I := Bridge.model I) σ ↔ feasE I bl (encS I σ bl) := by
  constructor
  · intro hF d hd t ht t' ht' hb hb' hc
    have h1 : bl[t] < I.clients := hlt _ (List.getElem_mem ht)
    have h2 : bl[t'] < I.clients := hlt _ (List.getElem_mem (by omega))
    have hne : t ≠ t' := by omega
    have hj : (⟨bl[t], h1⟩ : Fin I.clients) ∈ σ ⟨d, hd⟩ := (bit_iff σ ht h1 hd).1 hb
    have hj' : (⟨bl[t'], h2⟩ : Fin I.clients) ∈ σ ⟨d, hd⟩ := (bit_iff σ (by omega) h2 hd).1 hb'
    have hne' : (⟨bl[t], h1⟩ : Fin I.clients) ≠ ⟨bl[t'], h2⟩ := by
      intro h
      exact hne ((List.Nodup.getElem_inj_iff hnd).1 (by simpa using congrArg Fin.val h))
    refine hF ⟨d, hd⟩ _ hj _ hj' hne' ((conflict_iff' ⟨d, hd⟩ _ _).2 ?_)
    rw [getElem!_eq' ht, getElem!_eq' (by omega : t' < bl.length)] at hc
    simpa using hc
  · intro hF d j hj j' hj' hne hcf
    have key : ∀ (a b : Fin I.clients) (ta tb : ℕ) (hta : ta < bl.length) (htb : tb < bl.length),
        bl[ta] = a.val → bl[tb] = b.val → tb < ta → a ∈ σ d → b ∈ σ d →
        Instance.Conflict (I := Bridge.model I) d a b → False := by
      intro a b ta tb hta htb ha hb hlt' ha' hb' hc
      have h1 : bl[ta] < I.clients := by rw [ha]; exact a.isLt
      have h2 : bl[tb] < I.clients := by rw [hb]; exact b.isLt
      have ea : (⟨bl[ta], h1⟩ : Fin I.clients) = a := Fin.ext ha
      have eb : (⟨bl[tb], h2⟩ : Fin I.clients) = b := Fin.ext hb
      refine hF d.val d.isLt ta hta tb hlt' ((bit_iff σ hta h1 d.isLt).2 (ea ▸ ha'))
        ((bit_iff σ htb h2 d.isLt).2 (eb ▸ hb')) ?_
      rw [getElem!_eq' hta, getElem!_eq' htb]
      have := (conflict_iff' d a b).1 hc
      simpa [← ha, ← hb] using this
    obtain ⟨t, ht, hj1⟩ := pos_of_mem hX (hσ d hj)
    obtain ⟨t', ht', hj2⟩ := pos_of_mem hX (hσ d hj')
    have hne' : t ≠ t' := by
      intro h; subst h; exact hne (Fin.ext (hj1.symm.trans hj2))
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact key j' j t' t ht' ht hj2 hj1 h hj' hj (Instance.conflict_symm hcf)
    · exact key j j' t t' ht ht' hj1 hj2 h hj hj' hcf

/-- **Fairness is what `fairE` checks.** -/
lemma fair_iff {bl : List ℕ} {X : Finset (Fin I.clients)} (kk : ℕ)
    (hlt : ∀ x ∈ bl, x < I.clients) (hX : ∀ j : Fin I.clients, j ∈ X ↔ j.val ∈ bl)
    {σ : Fin I.days → Finset (Fin I.clients)} :
    (∀ j ∈ X, kk ≤ servedF σ j) ↔ fairE I kk bl (encS I σ bl) := by
  constructor
  · intro h t ht
    have h1 : bl[t] < I.clients := hlt _ (List.getElem_mem ht)
    have := h ⟨bl[t], h1⟩ ((hX _).2 (List.getElem_mem ht))
    rw [servedF_popc] at this
    rwa [dg_encS σ ht, getElem!_eq' ht]
  · intro h j hj
    obtain ⟨t, ht, hjt⟩ := pos_of_mem hX hj
    have := h t ht
    rw [dg_encS σ ht, getElem!_eq' ht, hjt] at this
    rwa [servedF_popc]

/-- **`Σ(X)` is what `feasE` and `fairE` check.** -/
lemma sigma_iff {bl : List ℕ} {X : Finset (Fin I.clients)} (kk : ℕ) (hnd : bl.Nodup)
    (hlt : ∀ x ∈ bl, x < I.clients) (hX : ∀ j : Fin I.clients, j ∈ X ↔ j.val ∈ bl)
    {σ : Fin I.days → Finset (Fin I.clients)} (hσ : ∀ d, σ d ⊆ X) :
    Instance.Sigma (I := Bridge.model I) (fun _ => kk) X σ ↔
      feasE I bl (encS I σ bl) ∧ fairE I kk bl (encS I σ bl) := by
  unfold Instance.Sigma
  rw [feasible_iff hnd hlt hX hσ, ← fair_iff kk hlt hX]
  exact ⟨fun ⟨_, a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨hσ, a, b⟩⟩

end Enc

/-! ### The recurrences of the table, as equations -/

section Recurrences

variable {I} {kk : ℕ} {D : List ℕ} {i e : ℕ}

lemma TB_intro (hk : kind D (i + 1) = 1) :
    TB I kk D (i + 1) e ↔ feasE I (bagL D (i + 1)) e ∧ fairE I kk (bagL D (i + 1)) e ∧
      TB I kk D i (rmN (2 ^ I.days) (pos (bagL D i) (vertex D (i + 1))) e) := by
  rw [TB, if_pos hk]

lemma TB_forget (hk : kind D (i + 1) = 2) :
    TB I kk D (i + 1) e ↔ ∃ S < 2 ^ I.days,
      TB I kk D i (insN (2 ^ I.days) (pos (bagL D i) (vertex D (i + 1))) S e) := by
  rw [TB, if_neg (by omega), if_pos hk]

lemma TB_join (hk : kind D (i + 1) = 3) (ho : other D (i + 1) < i + 1) :
    TB I kk D (i + 1) e ↔ TB I kk D i e ∧ TB I kk D (other D (i + 1)) e := by
  rw [TB, if_neg (by omega), if_neg (by omega), if_pos hk, dif_pos ho]

lemma TB_leaf (hk : kind D (i + 1) = 0) : TB I kk D (i + 1) e ↔ e = 0 := by
  rw [TB, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma bagL_intro (hk : kind D (i + 1) = 1) :
    bagL D (i + 1) = (bagL D i).insertIdx (pos (bagL D i) (vertex D (i + 1))) (vertex D (i + 1)) := by
  rw [bagL, if_pos hk]

lemma bagL_forget (hk : kind D (i + 1) = 2) :
    bagL D (i + 1) = (bagL D i).eraseIdx (pos (bagL D i) (vertex D (i + 1))) := by
  rw [bagL, if_neg (by omega), if_pos hk]

lemma bagL_join (hk : kind D (i + 1) = 3) : bagL D (i + 1) = bagL D i := by
  rw [bagL, if_neg (by omega), if_neg (by omega), if_pos hk]

lemma bagL_leaf (hk : kind D (i + 1) = 0) : bagL D (i + 1) = [] := by
  rw [bagL, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end Recurrences

/-- A schedule in the table serves only the clients of the bag. -/
lemma tab_defined {kk : ℕ} : ∀ (T : NiceTree (Fin I.clients)) (σ : Fin I.days → Finset (Fin I.clients)),
    Instance.Tab (I := Bridge.model I) (fun _ => kk) T σ → ∀ d, σ d ⊆ T.bag
  | .leaf b, σ, h => fun d => h.1 d
  | .intro j c, σ, h => fun d => h.1.1 d
  | .forget j c, σ, ⟨σ', hσ', hres⟩ => fun d => by
      rw [← hres]
      intro x hx
      exact (Finset.mem_inter.1 hx).2
  | .join l r, σ, h => fun d => tab_defined l σ h.1 d

/-! ### The table is the table of the paper -/

section Main

variable {I} {w : ℕ} {D : List ℕ} {i : ℕ}

/-- The membership in a sorted bag, for `Fin` clients. -/
lemma bagL_mem_fin (hD : NiceDecomposition I w D) {i : ℕ} (hi : i < nodeCount D)
    (j : Fin I.clients) : j ∈ bagAt I.clients D i ↔ j.val ∈ bagL D i := by
  rw [(bagL_spec hD i hi).2 j.val]
  constructor
  · intro h; exact ⟨j.isLt, h⟩
  · rintro ⟨h1, h2⟩; exact h2

/-- **A sorted bag has at most `w + 1` entries.** -/
lemma bagL_length_le (hD : NiceDecomposition I w D) {i : ℕ} (hi : i < nodeCount D) :
    (bagL D i).length ≤ w + 1 := by
  obtain ⟨hp, hm⟩ := bagL_spec hD i hi
  have hnd : (bagL D i).Nodup := hp.imp (fun {a b} h => h.ne)
  have h1 : (bagL D i).toFinset = (bagAt I.clients D i).image Fin.val := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_image, hm]
    constructor
    · rintro ⟨h, hx⟩; exact ⟨_, hx, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a.isLt, ha⟩
  have h2 : (bagL D i).length = (bagAt I.clients D i).card := by
    rw [← List.toFinset_card_of_nodup hnd, h1, Finset.card_image_of_injective _ Fin.val_injective]
  rw [h2]
  exact hD.width i hi

/-- **The leaves.** -/
lemma tab_leaf (kk : ℕ) (σ : Fin I.days → Finset (Fin I.clients))
    (hσ : ∀ d, σ d ⊆ (∅ : Finset (Fin I.clients))) :
    Instance.Tab (I := Bridge.model I) (fun _ => kk) (NiceTree.leaf (∅ : Finset (Fin I.clients))) σ := by
  refine (sigma_iff (I := I) (X := (∅ : Finset (Fin I.clients))) (bl := []) kk (by simp)
    (by simp) (by simp) hσ).2 ⟨?_, ?_⟩
  · intro d hd t ht; simp at ht
  · intro t ht; simp at ht

lemma toTree_intro (hk : kind D (i + 1) = 1) (hv' : vertex D (i + 1) < I.clients) :
    toTree I.clients D (i + 1) =
      NiceTree.intro ⟨vertex D (i + 1), hv'⟩ (toTree I.clients D i) := by
  rw [toTree]; simp [hk, hv']

lemma toTree_forget (hk : kind D (i + 1) = 2) (hv' : vertex D (i + 1) < I.clients) :
    toTree I.clients D (i + 1) =
      NiceTree.forget ⟨vertex D (i + 1), hv'⟩ (toTree I.clients D i) := by
  rw [toTree]; simp [hk, hv']

lemma toTree_join (hk : kind D (i + 1) = 3) (ho : other D (i + 1) < i + 1) :
    toTree I.clients D (i + 1) =
      NiceTree.join (toTree I.clients D (other D (i + 1))) (toTree I.clients D i) := by
  rw [toTree]; simp [hk, ho]

/-- **The introduce step.** -/
lemma tab_intro_step (hD : NiceDecomposition I w D) (kk : ℕ)
    (hi : i + 1 < nodeCount D) (hk : kind D (i + 1) = 1) (hv' : vertex D (i + 1) < I.clients)
    (ihc : ∀ σ : Fin I.days → Finset (Fin I.clients), (∀ d, σ d ⊆ bagAt I.clients D i) →
      (Instance.Tab (I := Bridge.model I) (fun _ => kk) (toTree I.clients D i) σ ↔
        TB I kk D i (encS I σ (bagL D i))))
    {σ : Fin I.days → Finset (Fin I.clients)} (hσ : ∀ d, σ d ⊆ bagAt I.clients D (i + 1)) :
    Instance.Tab (I := Bridge.model I) (fun _ => kk) (toTree I.clients D (i + 1)) σ ↔
      TB I kk D (i + 1) (encS I σ (bagL D (i + 1))) := by
  obtain ⟨hp1, hm1⟩ := bagL_spec hD (i + 1) hi
  have hnd1 : (bagL D (i + 1)).Nodup := hp1.imp (fun {a b} h => h.ne)
  have hlt1 : ∀ x ∈ bagL D (i + 1), x < I.clients := fun x hx => ((hm1 x).1 hx).1
  obtain ⟨hp0, hm0⟩ := bagL_spec hD i (by omega)
  have hlt0 : ∀ x ∈ bagL D i, x < I.clients := fun x hx => ((hm0 x).1 hx).1
  have hX1 := bagL_mem_fin hD hi
  have hX0 := bagL_mem_fin hD (i := i) (by omega)
  rw [toTree_intro hk hv', TB_intro hk]
  show (Instance.Sigma (I := Bridge.model I) (fun _ => kk)
      (insert ⟨vertex D (i + 1), hv'⟩ (toTree I.clients D i).bag) σ ∧
    Instance.Tab (I := Bridge.model I) (fun _ => kk) (toTree I.clients D i)
      (Instance.restr (toTree I.clients D i).bag σ)) ↔ _
  have hbag : (insert ⟨vertex D (i + 1), hv'⟩ (toTree I.clients D i).bag : Finset (Fin I.clients)) =
      bagAt I.clients D (i + 1) := by
    rw [bag_toTree hD i (by omega), bagAt_succ_intro hk hv']
  have hX1' : ∀ j : Fin I.clients,
      j ∈ (insert ⟨vertex D (i + 1), hv'⟩ (toTree I.clients D i).bag : Finset (Fin I.clients)) ↔
        j.val ∈ bagL D (i + 1) := by
    intro j; rw [hbag]; exact hX1 j
  have hσ' : ∀ d, σ d ⊆
      (insert ⟨vertex D (i + 1), hv'⟩ (toTree I.clients D i).bag : Finset (Fin I.clients)) := by
    intro d; rw [hbag]; exact hσ d
  have h1 := sigma_iff (I := I) kk hnd1 hlt1 hX1' hσ'
  have hres : ∀ d, restrF (bagAt I.clients D i) σ d ⊆ bagAt I.clients D i :=
    fun d => Finset.inter_subset_right
  have hb0 : (toTree I.clients D i).bag = bagAt I.clients D i := bag_toTree hD i (by omega)
  have := ihc (restrF (bagAt I.clients D i) σ) hres
  have hen : encS I (restrF (bagAt I.clients D i) σ) (bagL D i) =
      rmN (2 ^ I.days) (pos (bagL D i) (vertex D (i + 1))) (encS I σ (bagL D (i + 1))) := by
    rw [encS_restr σ _ (fun x hx => ⟨hlt0 x hx, (hX0 ⟨x, hlt0 x hx⟩).2 hx⟩), bagL_intro hk,
      encS_insertIdx σ _ pos_le_length, rmN_insN (Nat.two_pow_pos _) (maskOf_lt σ _)]
  rw [← hen]
  have h2 : Instance.Tab (I := Bridge.model I) (fun _ => kk) (toTree I.clients D i)
      (Instance.restr (toTree I.clients D i).bag σ) ↔
      TB I kk D i (encS I (restrF (bagAt I.clients D i) σ) (bagL D i)) := by
    rw [hb0, restr_eq]; exact this
  exact (and_congr h1 h2).trans and_assoc

/-- **The forget step.** -/
lemma tab_forget_step (hD : NiceDecomposition I w D) (kk : ℕ)
    (hi : i + 1 < nodeCount D) (hk : kind D (i + 1) = 2) (hv' : vertex D (i + 1) < I.clients)
    (hin : (⟨vertex D (i + 1), hv'⟩ : Fin I.clients) ∈ bagAt I.clients D (i + 1 - 1))
    (ihc : ∀ σ : Fin I.days → Finset (Fin I.clients), (∀ d, σ d ⊆ bagAt I.clients D i) →
      (Instance.Tab (I := Bridge.model I) (fun _ => kk) (toTree I.clients D i) σ ↔
        TB I kk D i (encS I σ (bagL D i))))
    {σ : Fin I.days → Finset (Fin I.clients)} (hσ : ∀ d, σ d ⊆ bagAt I.clients D (i + 1)) :
    Instance.Tab (I := Bridge.model I) (fun _ => kk) (toTree I.clients D (i + 1)) σ ↔
      TB I kk D (i + 1) (encS I σ (bagL D (i + 1))) := by
  obtain ⟨hp1, hm1⟩ := bagL_spec hD (i + 1) hi
  have hnd1 : (bagL D (i + 1)).Nodup := hp1.imp (fun {a b} h => h.ne)
  have hlt1 : ∀ x ∈ bagL D (i + 1), x < I.clients := fun x hx => ((hm1 x).1 hx).1
  obtain ⟨hp0, hm0⟩ := bagL_spec hD i (by omega)
  have hnd0 : (bagL D i).Nodup := hp0.imp (fun {a b} h => h.ne)
  have hlt0 : ∀ x ∈ bagL D i, x < I.clients := fun x hx => ((hm0 x).1 hx).1
  have hX1 := bagL_mem_fin hD hi
  have hX0 := bagL_mem_fin hD (i := i) (by omega)
  have hvl : vertex D (i + 1) ∈ bagL D i :=
    (hX0 ⟨vertex D (i + 1), hv'⟩).1 (by simpa using hin)
  obtain ⟨hpos, -, -⟩ := getElem_pos hp0 hvl
  set p := pos (bagL D i) (vertex D (i + 1)) with hpdef
  have hbl : bagL D (i + 1) = (bagL D i).eraseIdx p := bagL_forget hk
  have hb0 : (toTree I.clients D i).bag = bagAt I.clients D i := bag_toTree hD i (by omega)
  have hbag : (toTree I.clients D i).bag.erase ⟨vertex D (i + 1), hv'⟩ =
      bagAt I.clients D (i + 1) := by
    rw [hb0, bagAt_succ_forget hk hv']
  rw [toTree_forget hk hv', TB_forget hk]
  show (∃ σ' : Fin I.days → Finset (Fin I.clients),
      Instance.Tab (I := Bridge.model I) (fun _ => kk) (toTree I.clients D i) σ' ∧
        Instance.restr (I := Bridge.model I)
          ((toTree I.clients D i).bag.erase ⟨vertex D (i + 1), hv'⟩) σ' = σ) ↔ _
  have hlen : (bagL D (i + 1)).length + 1 = (bagL D i).length := by
    rw [hbl, List.length_eraseIdx]; simp [hpos]; omega
  constructor
  · rintro ⟨σ', hT, hres⟩
    have hres' : restrF (bagAt I.clients D (i + 1)) σ' = σ := by rw [← hbag]; exact hres
    have hdef : ∀ d, σ' d ⊆ bagAt I.clients D i := by
      intro d; have := tab_defined I _ σ' hT d; rwa [hb0] at this
    have hT' := (ihc σ' hdef).1 hT
    have he : encS I σ (bagL D (i + 1)) = rmN (2 ^ I.days) p (encS I σ' (bagL D i)) := by
      rw [← hres', encS_restr σ' _ (fun x hx => ⟨hlt1 x hx, (hX1 ⟨x, hlt1 x hx⟩).2 hx⟩), hbl,
        encS_eraseIdx σ' _ hpos]
    refine ⟨dg (2 ^ I.days) (encS I σ' (bagL D i)) p, Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
    rw [he, insN_rmN (Nat.two_pow_pos _)]
    exact hT'
  · rintro ⟨S, hS, hTB⟩
    set e := encS I σ (bagL D (i + 1)) with hedef
    have he_lt : e < (2 ^ I.days) ^ (bagL D (i + 1)).length := encS_lt σ _
    have hp_le : p ≤ (bagL D (i + 1)).length := by omega
    have he'_lt : insN (2 ^ I.days) p S e < (2 ^ I.days) ^ (bagL D i).length := by
      rw [← hlen, pow_succ]
      have := insN_lt (Nat.two_pow_pos _) he_lt hS hp_le
      rwa [pow_succ] at this
    obtain ⟨σ', hdefσ', hencσ'⟩ := exists_sched hnd0 hlt0 he'_lt
    have hdef : ∀ d, σ' d ⊆ bagAt I.clients D i := by
      intro d j hj
      exact (hX0 j).2 (hdefσ' d j hj)
    refine ⟨σ', (ihc σ' hdef).2 (by rw [hencσ']; exact hTB), ?_⟩
    have hdefr : DefOn I (restrF (bagAt I.clients D (i + 1)) σ') (bagL D (i + 1)) := by
      intro d j hj
      exact (hX1 j).1 (Finset.mem_inter.1 hj).2
    have hdefσ : DefOn I σ (bagL D (i + 1)) := by
      intro d j hj; exact (hX1 j).1 (hσ d hj)
    have : restrF (bagAt I.clients D (i + 1)) σ' = σ := by
      refine encS_inj hdefr hdefσ ?_
      rw [encS_restr σ' _ (fun x hx => ⟨hlt1 x hx, (hX1 ⟨x, hlt1 x hx⟩).2 hx⟩), hbl,
        encS_eraseIdx σ' _ hpos, hencσ', rmN_insN (Nat.two_pow_pos _) hS, hedef, hbl]
    rw [← hbag] at this
    exact this

/-- **The join step.** -/
lemma tab_join_step (hD : NiceDecomposition I w D) (kk : ℕ)
    (hi : i + 1 < nodeCount D) (hk : kind D (i + 1) = 3) (ho : other D (i + 1) < i + 1)
    (hb : bagAt I.clients D (other D (i + 1)) = bagAt I.clients D i)
    (ihl : ∀ σ : Fin I.days → Finset (Fin I.clients),
      (∀ d, σ d ⊆ bagAt I.clients D (other D (i + 1))) →
      (Instance.Tab (I := Bridge.model I) (fun _ => kk) (toTree I.clients D (other D (i + 1))) σ ↔
        TB I kk D (other D (i + 1)) (encS I σ (bagL D (other D (i + 1))))))
    (ihr : ∀ σ : Fin I.days → Finset (Fin I.clients), (∀ d, σ d ⊆ bagAt I.clients D i) →
      (Instance.Tab (I := Bridge.model I) (fun _ => kk) (toTree I.clients D i) σ ↔
        TB I kk D i (encS I σ (bagL D i))))
    {σ : Fin I.days → Finset (Fin I.clients)} (hσ : ∀ d, σ d ⊆ bagAt I.clients D (i + 1)) :
    Instance.Tab (I := Bridge.model I) (fun _ => kk) (toTree I.clients D (i + 1)) σ ↔
      TB I kk D (i + 1) (encS I σ (bagL D (i + 1))) := by
  obtain ⟨hp0, hm0⟩ := bagL_spec hD i (by omega)
  obtain ⟨hpo, hmo⟩ := bagL_spec hD (other D (i + 1)) (by omega)
  have hbo : bagL D (other D (i + 1)) = bagL D i := by
    refine eq_of_mem_iff hpo hp0 fun x => ?_
    rw [hmo, hm0, hb]
  have hbj : bagAt I.clients D (i + 1) = bagAt I.clients D i := bagAt_succ_join hk
  have h1 := ihl σ (fun d => (hσ d).trans (by rw [hbj, hb]))
  have h2 := ihr σ (fun d => (hσ d).trans (by rw [hbj]))
  rw [hbo] at h1
  rw [toTree_join hk ho, TB_join hk ho, bagL_join hk]
  show (Instance.Tab (I := Bridge.model I) (fun _ => kk) (toTree I.clients D (other D (i + 1))) σ ∧
    Instance.Tab (I := Bridge.model I) (fun _ => kk) (toTree I.clients D i) σ) ↔ _
  exact (and_congr h1 h2).trans and_comm

/-- **The table of every node is the table of the paper.** -/
theorem tab_TB (hD : NiceDecomposition I w D) (kk : ℕ) : ∀ i, i < nodeCount D →
    ∀ σ : Fin I.days → Finset (Fin I.clients), (∀ d, σ d ⊆ bagAt I.clients D i) →
      (Instance.Tab (I := Bridge.model I) (fun _ => kk) (toTree I.clients D i) σ ↔
        TB I kk D i (encS I σ (bagL D i))) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi σ hσ
    cases i with
    | zero =>
      have h0 : toTree I.clients D 0 = NiceTree.leaf ∅ := by rw [toTree]
      have hs : ∀ d, σ d ⊆ (∅ : Finset (Fin I.clients)) := by simpa [bagAt] using hσ
      rw [h0]
      exact iff_of_true (tab_leaf kk σ hs) (by simp [TB, bagL, encS])
    | succ i =>
      have hshape := hD.shape (i + 1) hi
      have ihc : ∀ σ : Fin I.days → Finset (Fin I.clients), (∀ d, σ d ⊆ bagAt I.clients D i) →
          (Instance.Tab (I := Bridge.model I) (fun _ => kk) (toTree I.clients D i) σ ↔
            TB I kk D i (encS I σ (bagL D i))) := fun σ hσ => ih i (by omega) (by omega) σ hσ
      rcases hshape with h0 | ⟨_, hk, hv', hnot⟩ | ⟨_, hk, hv', hin⟩ | ⟨_, hk, ho, hb⟩
      · have ht : toTree I.clients D (i + 1) = NiceTree.leaf ∅ := by rw [toTree]; simp [h0]
        have hs : ∀ d, σ d ⊆ (∅ : Finset (Fin I.clients)) := by
          simpa [bagAt_succ_leaf h0] using hσ
        rw [ht]
        exact iff_of_true (tab_leaf kk σ hs) ((TB_leaf h0).2 (by simp [bagL_leaf h0, encS]))
      · exact tab_intro_step hD kk hi hk hv' ihc hσ
      · exact tab_forget_step hD kk hi hk hv' (hin hv') ihc hσ
      · have hoi : other D (i + 1) < i + 1 := by omega
        exact tab_join_step hD kk hi hk hoi (by simpa using hb)
          (fun σ hσ' => ih _ hoi (by omega) σ hσ') ihc hσ

/-- **The dynamic program answers the question.** Some restriction is in the table of the last
node exactly when the instance has a schedule serving every client `kk` times. -/
theorem dp_correct (hD : NiceDecomposition I w D) (kk : ℕ) :
    (∃ e < (2 ^ I.days) ^ (bagL D (nodeCount D - 1)).length,
        TB I kk D (nodeCount D - 1) e) ↔ I.HasKFairSchedule kk := by
  have hN := hD.nonempty
  have hroot : nodeCount D - 1 < nodeCount D := by omega
  obtain ⟨hp, hm⟩ := bagL_spec hD _ hroot
  have hnd : (bagL D (nodeCount D - 1)).Nodup := hp.imp (fun {a b} h => h.ne)
  have hlt : ∀ x ∈ bagL D (nodeCount D - 1), x < I.clients := fun x hx => ((hm x).1 hx).1
  have hX := bagL_mem_fin hD hroot
  have hnice : NiceTree.IsNice (Bridge.model I).overallGraph (toTree I.clients D (nodeCount D - 1)) := by
    rw [← Bridge.overallGraph_eq]; exact isNice_toTree hD
  rw [Bridge.hasKFairSchedule_iff]
  have key := Instance.exists_tab_iff_hasFairSchedule (I := Bridge.model I) (k := fun _ => kk) hnice
  show _ ↔ (Bridge.model I).HasFairSchedule (fun _ => kk)
  rw [← key]
  constructor
  · rintro ⟨e, he, hTB⟩
    obtain ⟨σ, hdef, henc⟩ := exists_sched hnd hlt he
    refine ⟨σ, (tab_TB hD kk _ hroot σ (fun d j hj => (hX j).2 (hdef d j hj))).2 ?_⟩
    rw [henc]; exact hTB
  · rintro ⟨σ, hσ⟩
    have hdef : ∀ d, σ d ⊆ bagAt I.clients D (nodeCount D - 1) := by
      intro d; have := tab_defined I _ σ hσ d
      rwa [bag_toTree hD _ hroot] at this
    exact ⟨encS I σ _, encS_lt σ _, (tab_TB hD kk _ hroot σ hdef).1 hσ⟩

end Main

end Lax117284Proofs.TwDP
