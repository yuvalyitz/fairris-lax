import Lax117284Proofs.Machine.FoldLoop
import Lax117284Proofs.Theorem4TwViol

/-!
The count of the violations of a restriction, as three nested loops over IMP+ scalars: a fold over
the days of a fold over the earlier clients of a fold over the clients of the bag.
-/

namespace Lax117284Proofs.Machine.TwViol

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.FoldLoop
open Lax117284Proofs.TwDigits Lax117284Proofs.TwMask

abbrev V (s : String) : Expr := .var s
abbrev L (n : ℕ) : Expr := .lit n
abbrev G (a : String) (e : Expr) : Expr := .get a e
abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f

/-- The conflict of clients `u`, `u'` on day `d` read off the instance word. -/
def cfN (X : List ℕ) (n m d u u' : ℕ) : Prop :=
  X.getD (2 + m * n + d * n + u') 0 - X.getD (2 + d * n + u') 0 <
      X.getD (2 + m * n + d * n + u) 0 ∧
    X.getD (2 + m * n + d * n + u) 0 - X.getD (2 + d * n + u) 0 <
      X.getD (2 + m * n + d * n + u') 0

instance (X : List ℕ) (n m d u u' : ℕ) : Decidable (cfN X n m d u u') := by
  unfold cfN; infer_instance

/-- Normalize the reads of an updated environment. -/
macro "nrm" : tactic => `(tactic| simp only [vars_setVar, arrs_setVar, inp_setVar, out_setVar,
  vars_setArr, ↓reduceIte, String.reduceEq, eq_self])

/-- A block of commands, run one after the other. -/
def seqs : List Com → Com
  | [] => .skip
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- The reads of the innermost loop. -/
def cfPre : Com := seqs
  [ .assign "b1" (.bin .and (.bin .shiftr (V "dt") (V "d")) (L 1)),
    .assign "b2" (.bin .and (.bin .shiftr (V "dq") (V "d")) (L 1)),
    .assign "dn" (mul (V "d") (V "n")),
    .assign "pa" (G "X" (add (add (L 2) (V "dn")) (V "du"))),
    .assign "da" (G "X" (add (add (add (L 2) (V "mn")) (V "dn")) (V "du"))),
    .assign "pb" (G "X" (add (add (L 2) (V "dn")) (V "dv"))),
    .assign "db" (G "X" (add (add (add (L 2) (V "mn")) (V "dn")) (V "dv"))),
    .assign "cf" (L 0) ]

/-- The test of the innermost loop. -/
def cfIte : Com :=
  .ite (.lt (sub (V "da") (V "pa")) (V "db"))
    (.ite (.lt (sub (V "db") (V "pb")) (V "da")) (.assign "cf" (L 1)) .skip) .skip

/-- The body of the innermost loop: does day `d` add a violation for the two clients? -/
def cfBody : Com := .seq cfPre (.seq cfIte
  (.assign "vi" (add (V "vi") (mul (mul (V "b1") (V "b2")) (V "cf")))))

variable {B : ℕ}

lemma agr_set {S : List String} {σ : Env} {x : String} (hx : x ∈ S) (v : ℕ) :
    Agr S σ (σ.setVar x v) :=
  ⟨rfl, fun y hy => by
    have : y ≠ x := fun h => hy (h ▸ hx)
    simp [Env.setVar, this]⟩

set_option maxHeartbeats 1600000 in
theorem cfPre_run (X : List ℕ) (n m : ℕ) (σ : Env) (hX : σ.arrs "X" = X)
    (hn : σ.vars "n" = n) (hmn : σ.vars "mn" = m * n) (hd : σ.vars "d" < m)
    (hdu : σ.vars "du" < n) (hdv : σ.vars "dv" < n) (hlen : 2 + 2 * (m * n) + 1 ≤ X.length)
    (hXB : ∀ v ∈ X, v < B) (hB : X.length + 8 < B) (hdt : σ.vars "dt" < B)
    (hdq : σ.vars "dq" < B) (hmB : m < B) (hnB : n < B) :
    ∃ σ', Run B cfPre σ σ' 100 ∧
      σ'.vars "b1" = Nat.land (σ.vars "dt" / 2 ^ σ.vars "d") 1 ∧
      σ'.vars "b2" = Nat.land (σ.vars "dq" / 2 ^ σ.vars "d") 1 ∧
      σ'.vars "pa" = X.getD (2 + σ.vars "d" * σ.vars "n" + σ.vars "du") 0 ∧
      σ'.vars "da" = X.getD (2 + σ.vars "mn" + σ.vars "d" * σ.vars "n" + σ.vars "du") 0 ∧
      σ'.vars "pb" = X.getD (2 + σ.vars "d" * σ.vars "n" + σ.vars "dv") 0 ∧
      σ'.vars "db" = X.getD (2 + σ.vars "mn" + σ.vars "d" * σ.vars "n" + σ.vars "dv") 0 ∧
      σ'.vars "cf" = 0 ∧
      Agr ["b1", "b2", "dn", "pa", "da", "pb", "db", "cf"] σ σ' ∧ σ'.out = σ.out := by
  have hXl : (σ.arrs "X").length = X.length := by rw [hX]
  have hXg : ∀ k, (σ.arrs "X").getD k 0 < B := by
    intro k; rw [hX]
    by_cases hk : k < X.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact hXB _ (List.getElem_mem hk)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp; omega
  have hdn : σ.vars "d" * σ.vars "n" + σ.vars "n" ≤ σ.vars "mn" := by
    rw [hn, hmn, ← Nat.succ_mul]; exact Nat.mul_le_mul_right n hd
  have hband : ∀ x : ℕ, Nat.land x 1 ≤ 1 := fun x => Nat.and_le_right
  unfold cfPre seqs
  run_vcg
  all_goals try (nrm; first
    | exact lt_of_le_of_lt (Nat.div_le_self _ _) hdt
    | exact lt_of_le_of_lt (Nat.div_le_self _ _) hdq)
  all_goals try exact lt_of_le_of_lt (Nat.div_le_self _ _) hdt
  all_goals (try nrm)
  all_goals try exact hXg _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [vars_setVar, ↓reduceIte, String.reduceEq]
  · simp only [vars_setVar, ↓reduceIte, String.reduceEq]
  · simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq, hX]
  · simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq, hX]
  · simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq, hX]
  · simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq, hX]
  · simp only [vars_setVar, ↓reduceIte, String.reduceEq]
  · refine ⟨?_, ?_⟩
    · simp only [arrs_setVar]
    · intro y hy
      simp only [vars_setVar]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.1,
        hy.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2]
  · simp only [out_setVar]

theorem cfIte_run (σ : Env) (hda : σ.vars "da" < B) (hpa : σ.vars "pa" < B)
    (hdb : σ.vars "db" < B) (hpb : σ.vars "pb" < B) (hcf : σ.vars "cf" = 0) (hB : 2 < B) :
    ∃ σ', Run B cfIte σ σ' 30 ∧
      σ'.vars "cf" = (if σ.vars "da" - σ.vars "pa" < σ.vars "db" ∧
        σ.vars "db" - σ.vars "pb" < σ.vars "da" then 1 else 0) ∧
      Agr ["cf"] σ σ' ∧ σ'.out = σ.out := by
  unfold cfIte
  run_vcg
  · refine ⟨?_, agr_set (by simp) _, rfl⟩
    rw [if_pos (by omega)]; nrm
  · refine ⟨?_, Agr.refl _ _, rfl⟩
    rw [hcf, if_neg (by omega)]
  · refine ⟨?_, Agr.refl _ _, rfl⟩
    rw [hcf, if_neg (by omega)]

theorem cfEnd_run (σ : Env) (hb1 : σ.vars "b1" ≤ 1) (hb2 : σ.vars "b2" ≤ 1)
    (hcf : σ.vars "cf" ≤ 1) (hvi : σ.vars "vi" + 2 < B) :
    ∃ σ', Run B (.assign "vi" (add (V "vi") (mul (mul (V "b1") (V "b2")) (V "cf")))) σ σ' 20 ∧
      σ'.vars "vi" = σ.vars "vi" + σ.vars "b1" * σ.vars "b2" * σ.vars "cf" ∧
      Agr ["vi"] σ σ' ∧ σ'.out = σ.out := by
  have h1 : σ.vars "b1" * σ.vars "b2" ≤ 1 := by
    calc σ.vars "b1" * σ.vars "b2" ≤ 1 * 1 := Nat.mul_le_mul hb1 hb2
      _ = 1 := rfl
  have h2 : σ.vars "b1" * σ.vars "b2" * σ.vars "cf" ≤ 1 := by
    calc σ.vars "b1" * σ.vars "b2" * σ.vars "cf" ≤ 1 * 1 := Nat.mul_le_mul h1 hcf
      _ = 1 := rfl
  run_vcg
  exact ⟨by nrm, agr_set (by simp) _, rfl⟩

lemma agr_comp {S S1 S2 : List String} {σ σ1 σ2 : Env} (h1 : Agr S1 σ σ1) (h2 : Agr S2 σ1 σ2)
    (hs1 : ∀ x ∈ S1, x ∈ S) (hs2 : ∀ x ∈ S2, x ∈ S) : Agr S σ σ2 :=
  ⟨h2.1.trans h1.1, fun y hy => (h2.2 y (fun h => hy (hs2 y h))).trans
    (h1.2 y (fun h => hy (hs1 y h)))⟩

lemma land_one (x : ℕ) : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x

lemma testBit_iff_land (x d : ℕ) : x.testBit d = true ↔ Nat.land (x / 2 ^ d) 1 = 1 := by
  rw [land_one, Nat.testBit_eq_decide_div_mod_eq]; simp

lemma val_eq (vi b1 b2 : ℕ) (Q bt1 bt2 : Prop) [Decidable Q] [Decidable bt1] [Decidable bt2]
    (h1 : b1 ≤ 1) (h2 : b2 ≤ 1) (e1 : bt1 ↔ b1 = 1) (e2 : bt2 ↔ b2 = 1) :
    vi + b1 * b2 * (if Q then 1 else 0) = vi + (if bt1 ∧ bt2 ∧ Q then 1 else 0) := by
  have g1 : ¬ bt1 → b1 = 0 := fun h => by
    by_contra hb; exact h (e1.2 (by omega))
  have g2 : ¬ bt2 → b2 = 0 := fun h => by
    by_contra hb; exact h (e2.2 (by omega))
  by_cases q : Q <;> by_cases c1 : bt1 <;> by_cases c2 : bt2
  · simp [q, c1, c2, e1.1 c1, e2.1 c2]
  · simp [q, c1, c2, g2 c2]
  · simp [q, c1, c2, g1 c1]
  · simp [q, c1, c2, g1 c1]
  · simp [q, c1, c2, e1.1 c1, e2.1 c2]
  · simp [q, c1, c2, g2 c2]
  · simp [q, c1, c2, g1 c1]
  · simp [q, c1, c2, g1 c1]

/-- **One day of the innermost loop.** -/
theorem cfBody_run (X : List ℕ) (n m : ℕ) (σ : Env) (hX : σ.arrs "X" = X)
    (hn : σ.vars "n" = n) (hmn : σ.vars "mn" = m * n) (hd : σ.vars "d" < m)
    (hdu : σ.vars "du" < n) (hdv : σ.vars "dv" < n) (hlen : 2 + 2 * (m * n) + 1 ≤ X.length)
    (hXB : ∀ v ∈ X, v < B) (hB : X.length + 8 < B) (hdt : σ.vars "dt" < B)
    (hdq : σ.vars "dq" < B) (hmB : m < B) (hnB : n < B) (hvi : σ.vars "vi" + 2 < B) :
    ∃ σ', Run B cfBody σ σ' 200 ∧
      σ'.vars "vi" = σ.vars "vi" +
        (if (σ.vars "dt").testBit (σ.vars "d") = true ∧ (σ.vars "dq").testBit (σ.vars "d") = true ∧
          cfN X n m (σ.vars "d") (σ.vars "du") (σ.vars "dv") then 1 else 0) ∧
      Agr ["b1", "b2", "dn", "pa", "da", "pb", "db", "cf", "vi"] σ σ' ∧
      σ'.vars "d" = σ.vars "d" ∧ σ'.out = σ.out := by
  have hXg : ∀ k, X.getD k 0 < B := by
    intro k
    by_cases hk : k < X.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact hXB _ (List.getElem_mem hk)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp; omega
  obtain ⟨σ1, r1, e1, e2, ep, ed, epb, edb, ecf, a1, o1⟩ := cfPre_run X n m σ hX hn hmn hd hdu hdv
    hlen hXB hB hdt hdq hmB hnB
  have hb1 : σ1.vars "b1" ≤ 1 := by rw [e1]; exact Nat.and_le_right
  have hb2 : σ1.vars "b2" ≤ 1 := by rw [e2]; exact Nat.and_le_right
  have hpa : σ1.vars "pa" < B := by rw [ep]; exact hXg _
  have hda : σ1.vars "da" < B := by rw [ed]; exact hXg _
  have hpb : σ1.vars "pb" < B := by rw [epb]; exact hXg _
  have hdb : σ1.vars "db" < B := by rw [edb]; exact hXg _
  obtain ⟨σ2, r2, e3, a2, o2⟩ := cfIte_run σ1 hda hpa hdb hpb ecf (by omega)
  have hcf : σ2.vars "cf" ≤ 1 := by rw [e3]; split_ifs <;> omega
  have hb1' : σ2.vars "b1" ≤ 1 := by rw [a2.2 "b1" (by simp)]; exact hb1
  have hb2' : σ2.vars "b2" ≤ 1 := by rw [a2.2 "b2" (by simp)]; exact hb2
  have hvi2 : σ2.vars "vi" + 2 < B := by
    rw [a2.2 "vi" (by simp), a1.2 "vi" (by simp)]; exact hvi
  obtain ⟨σ3, r3, e4, a3, o3⟩ := cfEnd_run σ2 hb1' hb2' hcf hvi2
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), ?_, ?_, ?_, ?_⟩
  · rw [e4, a2.2 "b1" (by simp), a2.2 "b2" (by simp), e3, e1, e2, a2.2 "vi" (by simp),
      a1.2 "vi" (by simp)]
    rw [ep, ed, epb, edb, hn, hmn]
    have hcfN : (X.getD (2 + m * n + σ.vars "d" * n + σ.vars "du") 0 -
          X.getD (2 + σ.vars "d" * n + σ.vars "du") 0 <
          X.getD (2 + m * n + σ.vars "d" * n + σ.vars "dv") 0 ∧
        X.getD (2 + m * n + σ.vars "d" * n + σ.vars "dv") 0 -
          X.getD (2 + σ.vars "d" * n + σ.vars "dv") 0 <
          X.getD (2 + m * n + σ.vars "d" * n + σ.vars "du") 0) ↔
        cfN X n m (σ.vars "d") (σ.vars "du") (σ.vars "dv") := by
      unfold cfN; exact and_comm
    have hbit1 := testBit_iff_land (σ.vars "dt") (σ.vars "d")
    have hbit2 := testBit_iff_land (σ.vars "dq") (σ.vars "d")
    have hl1 : Nat.land (σ.vars "dt" / 2 ^ σ.vars "d") 1 ≤ 1 := Nat.and_le_right
    have hl2 : Nat.land (σ.vars "dq" / 2 ^ σ.vars "d") 1 ≤ 1 := Nat.and_le_right
    rw [if_congr hcfN rfl rfl]
    exact val_eq _ _ _ _ _ _ hl1 hl2 hbit1 hbit2
  · exact agr_comp (S := ["b1", "b2", "dn", "pa", "da", "pb", "db", "cf", "vi"]) a1
      (agr_comp (S := ["cf", "vi"]) a2 a3 (by simp) (by simp)) (by simp) (by simp)
  · rw [a3.2 "d" (by simp), a2.2 "d" (by simp), a1.2 "d" (by simp)]
  · rw [o3, o2, o1]

/-- The number of days on which two digits both contain the day and the clients conflict. -/
def cfDayN (X : List ℕ) (n m u v a a' : ℕ) : ℕ :=
  ∑ d ∈ Finset.range m, if a.testBit d = true ∧ a'.testBit d = true ∧ cfN X n m d u v then 1 else 0

/-- The loop over the days. -/
def dLoop : Com := fLoop "d" "m" cfBody

/-- The scalars the loop over the days writes. -/
def SD : List String := ["d", "b1", "b2", "dn", "pa", "da", "pb", "db", "cf", "vi"]

/-- **The loop over the days**: it adds the number of days that violate. -/
theorem dLoop_run (X : List ℕ) (n m : ℕ) (σ0 : Env) (hX : σ0.arrs "X" = X)
    (hn : σ0.vars "n" = n) (hm : σ0.vars "m" = m) (hmn : σ0.vars "mn" = m * n)
    (hdu : σ0.vars "du" < n) (hdv : σ0.vars "dv" < n) (hlen : 2 + 2 * (m * n) + 1 ≤ X.length)
    (hXB : ∀ v ∈ X, v < B) (hB : X.length + 8 < B) (hdt : σ0.vars "dt" < B)
    (hdq : σ0.vars "dq" < B) (hmB : m + 1 < B) (hnB : n < B) (hvi : σ0.vars "vi" + m + 2 < B) :
    ∃ σ', Run B dLoop σ0 σ' ((200 + 10 + 4) * m + 6) ∧
      σ'.vars "vi" = σ0.vars "vi" + cfDayN X n m (σ0.vars "du") (σ0.vars "dv") (σ0.vars "dt")
        (σ0.vars "dq") ∧
      Agr SD σ0 σ' ∧ σ'.out = σ0.out := by
  have hf := fLoop_spec (B := B) "d" "m" "vi" cfBody SD
    (fun d a => a + (if (σ0.vars "dt").testBit d = true ∧ (σ0.vars "dq").testBit d = true ∧
      cfN X n m d (σ0.vars "du") (σ0.vars "dv") then 1 else 0))
    (fun j a => a ≤ σ0.vars "vi" + j) 200 m σ0 (by simp [SD]) (by simp [SD]) (by decide) hm
    (by omega) le_rfl (fun j a h => by split_ifs <;> omega) (by
      intro σ hA hlt hQ
      have hfr : ∀ y, y ∉ SD → σ.vars y = σ0.vars y := hA.2
      have e1 : σ.vars "n" = n := by rw [hfr "n" (by simp [SD])]; exact hn
      have e2 : σ.vars "mn" = m * n := by rw [hfr "mn" (by simp [SD])]; exact hmn
      have e3 : σ.vars "du" = σ0.vars "du" := hfr "du" (by simp [SD])
      have e4 : σ.vars "dv" = σ0.vars "dv" := hfr "dv" (by simp [SD])
      have e5 : σ.vars "dt" = σ0.vars "dt" := hfr "dt" (by simp [SD])
      have e6 : σ.vars "dq" = σ0.vars "dq" := hfr "dq" (by simp [SD])
      have hlt'' : σ.vars "d" < m := by simpa using hlt
      obtain ⟨σ', r, hv, hA', hd', ho'⟩ := cfBody_run (B := B) X n m σ (by rw [hA.1]; exact hX) e1 e2
        hlt'' (by rw [e3]; exact hdu) (by rw [e4]; exact hdv) hlen hXB hB (by rw [e5]; exact hdt)
        (by rw [e6]; exact hdq) (by omega) hnB (by have := hQ; omega)
      refine ⟨σ', r, ?_, agr_comp hA hA' (by intro x hx; exact hx) (by intro x hx; simp [SD] at hx ⊢; tauto), hd', ho'⟩
      rw [hv, e3, e4, e5, e6])
  obtain ⟨σ', r, hv, hA, ho⟩ := hf
  refine ⟨σ', r, ?_, hA, ho⟩
  rw [hv, Lax117284Proofs.TwViol.foldl_add_range]
  rfl

/-! ### The popcount of a digit -/

/-- The body of the popcount loop. -/
def pcBody : Com := .assign "pcn" (add (V "pcn") (.bin .and (.bin .shiftr (V "dt") (V "d")) (L 1)))

/-- The popcount of `dt`, over the days. -/
def pcLoop : Com := .seq (.assign "pcn" (L 0)) (fLoop "d" "m" pcBody)

def SP : List String := ["d", "pcn"]

lemma popc_foldl (m x : ℕ) :
    (List.range m).foldl (fun a d => a + Nat.land (x / 2 ^ d) 1) 0 = popc m x := by
  rw [Lax117284Proofs.TwViol.foldl_add_range, popc, Nat.zero_add]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [land_one]
  by_cases h : x.testBit d = true
  · rw [if_pos h]; have := (testBit_iff_land x d).1 h; rwa [land_one] at this
  · rw [if_neg h]
    have : ¬ x / 2 ^ d % 2 = 1 := fun h' => h ((testBit_iff_land x d).2 (by rwa [land_one]))
    omega

theorem pcBody_run (σ : Env) (hdt : σ.vars "dt" < B) (hpc : σ.vars "pcn" + 2 < B)
    (hd : σ.vars "d" < B) :
    ∃ σ', Run B pcBody σ σ' 10 ∧
      σ'.vars "pcn" = σ.vars "pcn" + Nat.land (σ.vars "dt" / 2 ^ σ.vars "d") 1 ∧
      Agr ["pcn"] σ σ' ∧ σ'.out = σ.out ∧ σ'.vars "d" = σ.vars "d" := by
  have hdb : Nat.land (σ.vars "dt" / 2 ^ σ.vars "d") 1 ≤ 1 := Nat.and_le_right
  unfold pcBody
  run_vcg
  all_goals try exact lt_of_le_of_lt (Nat.div_le_self _ _) hdt
  refine ⟨?_, agr_set (by simp) _, ?_, ?_⟩
  · nrm
  · rfl
  · nrm

theorem pcLoop_run (m : ℕ) (σ0 : Env) (hm : σ0.vars "m" = m) (hmB : m + 1 < B)
    (hdt : σ0.vars "dt" < B) :
    ∃ σ', Run B pcLoop σ0 σ' ((10 + 10 + 4) * m + 6 + 2) ∧
      σ'.vars "pcn" = popc m (σ0.vars "dt") ∧ Agr SP σ0 σ' ∧ σ'.out = σ0.out := by
  have hz : Run B (.assign "pcn" (L 0)) σ0 (σ0.setVar "pcn" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have hf := fLoop_spec (B := B) "d" "m" "pcn" pcBody SP
    (fun d a => a + Nat.land (σ0.vars "dt" / 2 ^ d) 1) (fun j a => a ≤ j) 10 m
    (σ0.setVar "pcn" 0) (by simp [SP]) (by simp [SP]) (by decide) (by simpa using hm) (by omega)
    (by simp [Env.setVar])
    (fun j a h => by have : Nat.land (σ0.vars "dt" / 2 ^ j) 1 ≤ 1 := Nat.and_le_right; omega) (by
      intro σ hA hlt hQ
      have hfr : ∀ y, y ∉ SP → σ.vars y = (σ0.setVar "pcn" 0).vars y := hA.2
      have e1 : σ.vars "dt" = σ0.vars "dt" := by
        rw [hfr "dt" (by simp [SP])]; simp [Env.setVar]
      have e2 : σ.vars "m" = m := by
        rw [hfr "m" (by simp [SP])]; simpa [Env.setVar] using hm
      have hlt' : σ.vars "d" < m := by simpa using hlt
      have hq : σ.vars "pcn" ≤ σ.vars "d" := hQ
      obtain ⟨σ', r, hv, hA', ho', hd'⟩ := pcBody_run σ (by rw [e1]; exact hdt) (by omega)
        (by omega)
      refine ⟨σ', r, ?_, agr_comp hA hA' (by intro x hx; exact hx)
        (by intro x hx; simp [SP] at hx ⊢; tauto), hd', ho'⟩
      rw [hv, e1])
  obtain ⟨σ', r, hv, hA, ho⟩ := hf
  refine ⟨σ', (hz.seq r).mono (by omega), ?_, ?_, ?_⟩
  · have h0 : (σ0.setVar "pcn" 0).vars "pcn" = 0 := by simp [Env.setVar]
    rw [hv, h0, popc_foldl]
  · exact ⟨hA.1.trans (by simp [Env.setVar]), fun y hy => by
      rw [hA.2 y hy]; simp only [SP, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [Env.setVar, hy.2]⟩
  · rw [ho]; simp [Env.setVar]

/-! ### The loop over the earlier clients -/

/-- The digit of `e` at position `t`, computed from the scalars. -/
lemma dg_land (m e t : ℕ) : Nat.land (e / 2 ^ (m * t)) (2 ^ m - 1) = dg (2 ^ m) e t := by
  unfold dg
  rw [← pow_mul]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

/-- The constants of the count: the instance word, the bag of the node in `BG`, and the bounds. -/
structure VC (X : List ℕ) (n m kk : ℕ) (bl : List ℕ) (B : ℕ) (σ : Env) : Prop where
  X_ : σ.arrs "X" = X
  n_ : σ.vars "n" = n
  m_ : σ.vars "m" = m
  kk_ : σ.vars "kk" = kk
  mn_ : σ.vars "mn" = m * n
  mask_ : σ.vars "mask" = 2 ^ m - 1
  lenX : 2 + 2 * (m * n) + 1 ≤ X.length
  XB : ∀ v ∈ X, v < B
  bnd : X.length + 8 < B
  mB : m + 1 < B
  nB : n < B
  vB : bl.length * (bl.length * m + 1) + bl.length * m + m + 16 < B
  BG_ : ∀ t < bl.length, (σ.arrs "BG").getD (σ.vars "off" + t) 0 = bl[t]!
  BGlen : σ.vars "off" + bl.length ≤ (σ.arrs "BG").length
  BGB : ∀ t < bl.length, bl[t]! < n
  offB : σ.vars "off" + bl.length < B
  vs_ : σ.vars "vs" = bl.length
  mask2 : 2 ^ m < B
  lenB : bl.length + 2 < B
  kkB : kk < B

/-- The two reads of the loop over the earlier clients. -/
def t2Pre : Com :=
  .seq (.assign "dq" (.bin .and (.bin .shiftr (V "e") (mul (V "m") (V "t2"))) (V "mask")))
    (.assign "dv" (G "BG" (add (V "off") (V "t2"))))

/-- The body of the loop over the earlier clients. -/
def t2Body : Com := .seq t2Pre dLoop

def St2 : List String := "t2" :: "dq" :: "dv" :: SD

lemma cfDayN_le (X : List ℕ) (n m u v a a' : ℕ) : cfDayN X n m u v a a' ≤ m := by
  unfold cfDayN
  calc ∑ d ∈ Finset.range m, (if a.testBit d = true ∧ a'.testBit d = true ∧ cfN X n m d u v
        then 1 else 0) ≤ ∑ d ∈ Finset.range m, 1 :=
      Finset.sum_le_sum fun d _ => by split_ifs <;> omega
    _ = m := by simp

theorem t2Pre_run {X : List ℕ} {n m kk : ℕ} {bl : List ℕ} {σ : Env}
    (hV : VC X n m kk bl B σ) (ht2 : σ.vars "t2" < bl.length) (he : σ.vars "e" < B) :
    ∃ σ', Run B t2Pre σ σ' 30 ∧
      σ'.vars "dq" = dg (2 ^ m) (σ.vars "e") (σ.vars "t2") ∧
      σ'.vars "dv" = bl[σ.vars "t2"]! ∧
      Agr ["dq", "dv"] σ σ' ∧ σ'.out = σ.out := by
  have hbg := hV.BG_ (σ.vars "t2") ht2
  have hbgB := hV.BGB (σ.vars "t2") ht2
  have hlt2 : σ.vars "off" + σ.vars "t2" < (σ.arrs "BG").length := by
    have := hV.BGlen; omega
  have hmt : m * σ.vars "t2" ≤ m * bl.length := Nat.mul_le_mul_left _ (by omega)
  have hvB := hV.vB
  have hmB := hV.mB
  have hnB := hV.nB
  have hmask := hV.mask_
  have hmask2 := hV.mask2
  have hoB := hV.offB
  have hband : Nat.land (σ.vars "e" / 2 ^ (m * σ.vars "t2")) (2 ^ m - 1) ≤ 2 ^ m - 1 :=
    Nat.and_le_right
  have hm' : σ.vars "m" = m := hV.m_
  have hmm : σ.vars "m" * σ.vars "t2" ≤ m * bl.length := by rw [hm']; exact hmt
  have hcom : m * bl.length = bl.length * m := Nat.mul_comm _ _
  unfold t2Pre
  run_vcg
  all_goals try (first
    | exact lt_of_le_of_lt (Nat.div_le_self _ _) he
    | exact lt_of_le_of_lt Nat.and_le_right (by rw [hmask]; omega)
    | (nrm; rw [hbg]; omega)
    | omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm; rw [hmask, hm', dg_land]
  · nrm; exact hbg
  · refine ⟨?_, ?_⟩
    · simp only [arrs_setVar]
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [Env.setVar, hy.1, hy.2]
  · rfl

theorem t2Body_run {X : List ℕ} {n m kk : ℕ} {bl : List ℕ} {σ : Env}
    (hV : VC X n m kk bl B σ) (ht2 : σ.vars "t2" < bl.length)
    (hdt : σ.vars "dt" < B) (hdu : σ.vars "du" < n) (he : σ.vars "e" < B)
    (hvi : σ.vars "vi" + m + 2 < B) :
    ∃ σ', Run B t2Body σ σ' (30 + (200 + 10 + 4) * m + 6) ∧
      σ'.vars "vi" = σ.vars "vi" + cfDayN X n m (σ.vars "du") bl[σ.vars "t2"]! (σ.vars "dt")
        (dg (2 ^ m) (σ.vars "e") (σ.vars "t2")) ∧
      Agr St2 σ σ' ∧ σ'.vars "t2" = σ.vars "t2" ∧ σ'.out = σ.out := by
  obtain ⟨σ1, r1, hdq, hdv, a1, o1⟩ := t2Pre_run hV ht2 he
  have fr : ∀ y, y ≠ "dq" → y ≠ "dv" → σ1.vars y = σ.vars y := fun y h1 h2 =>
    a1.2 y (by simp [h1, h2])
  have hbgB := hV.BGB (σ.vars "t2") ht2
  have hdq' : σ1.vars "dq" < B := by
    rw [hdq]; unfold dg
    exact lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _)) hV.mask2
  have hmn := hV.mn_
  have hoB := hV.vB
  obtain ⟨σ2, r2, hv, a2, o2⟩ := dLoop_run (B := B) X n m σ1 (by rw [a1.1]; exact hV.X_)
    (by rw [fr "n" (by decide) (by decide)]; exact hV.n_)
    (by rw [fr "m" (by decide) (by decide)]; exact hV.m_)
    (by rw [fr "mn" (by decide) (by decide)]; exact hmn)
    (by rw [fr "du" (by decide) (by decide)]; exact hdu)
    (by rw [hdv]; exact hbgB) hV.lenX hV.XB hV.bnd (by rw [fr "dt" (by decide) (by decide)]; exact hdt)
    hdq' hV.mB hV.nB (by rw [fr "vi" (by decide) (by decide)]; exact hvi)
  refine ⟨σ2, (r1.seq r2).mono (by omega), ?_, ?_, ?_, ?_⟩
  · rw [hv, fr "vi" (by decide) (by decide), fr "du" (by decide) (by decide), hdv,
      fr "dt" (by decide) (by decide), hdq]
  · refine agr_comp (S := St2) a1 a2 (by intro x hx; simp [St2] at hx ⊢; tauto)
      (by intro x hx; simp [St2, SD] at hx ⊢; tauto)
  · have h1 := a2.2 "t2" (by simp [SD])
    rw [h1, fr "t2" (by decide) (by decide)]
  · rw [o2, o1]

/-- The constants of the count survive a run that only changes other scalars. -/
lemma VC.of_agr {X : List ℕ} {n m kk : ℕ} {bl : List ℕ} {σ0 σ : Env} {S : List String}
    (hV : VC X n m kk bl B σ0) (h : Agr S σ0 σ)
    (hS : ∀ y ∈ ["n", "m", "kk", "mn", "mask", "off", "vs"], y ∉ S) : VC X n m kk bl B σ := by
  have fr : ∀ y, y ∉ S → σ.vars y = σ0.vars y := h.2
  have hs : ∀ y ∈ ["n", "m", "kk", "mn", "mask", "off", "vs"], σ.vars y = σ0.vars y :=
    fun y hy => fr y (hS y hy)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hV.lenX, hV.XB, hV.bnd, hV.mB, hV.nB, hV.vB, ?_, ?_, hV.BGB, ?_,
    ?_, hV.mask2, hV.lenB, hV.kkB⟩
  · rw [h.1]; exact hV.X_
  · rw [hs "n" (by simp)]; exact hV.n_
  · rw [hs "m" (by simp)]; exact hV.m_
  · rw [hs "kk" (by simp)]; exact hV.kk_
  · rw [hs "mn" (by simp)]; exact hV.mn_
  · rw [hs "mask" (by simp)]; exact hV.mask_
  · intro t ht; rw [h.1, hs "off" (by simp)]; exact hV.BG_ t ht
  · rw [h.1, hs "off" (by simp)]; exact hV.BGlen
  · rw [hs "off" (by simp)]; exact hV.offB
  · rw [hs "vs" (by simp)]; exact hV.vs_

/-- The loop over the earlier clients. -/
def t2Loop : Com := fLoop "t2" "t" t2Body

/-- **The loop over the earlier clients**: it adds the conflicts of the client `t` with each
earlier client. -/
theorem t2Loop_run {X : List ℕ} {n m kk : ℕ} {bl : List ℕ} {σ0 : Env}
    (hV : VC X n m kk bl B σ0) (ht : σ0.vars "t" < bl.length)
    (hdt : σ0.vars "dt" < B) (hdu : σ0.vars "du" < n) (he : σ0.vars "e" < B)
    (hvi : σ0.vars "vi" + σ0.vars "t" * m + m + 2 < B) :
    ∃ σ', Run B t2Loop σ0 σ' ((30 + (200 + 10 + 4) * m + 6 + 10 + 4) * σ0.vars "t" + 6) ∧
      σ'.vars "vi" = σ0.vars "vi" + ∑ t2 ∈ Finset.range (σ0.vars "t"),
        cfDayN X n m (σ0.vars "du") bl[t2]! (σ0.vars "dt") (dg (2 ^ m) (σ0.vars "e") t2) ∧
      Agr St2 σ0 σ' ∧ σ'.out = σ0.out := by
  have hf := fLoop_spec (B := B) "t2" "t" "vi" t2Body St2
    (fun t2 a => a + cfDayN X n m (σ0.vars "du") bl[t2]! (σ0.vars "dt")
      (dg (2 ^ m) (σ0.vars "e") t2))
    (fun j a => a ≤ σ0.vars "vi" + j * m) (30 + (200 + 10 + 4) * m + 6) (σ0.vars "t") σ0
    (by simp [St2]) (by simp [St2, SD]) (by decide) rfl (by have := hV.lenB; omega) (by simp)
    (fun j a h => by
      have := cfDayN_le X n m (σ0.vars "du") bl[j]! (σ0.vars "dt") (dg (2 ^ m) (σ0.vars "e") j)
      rw [Nat.succ_mul]; omega) (by
      intro σ hA hlt hQ
      have hV' := hV.of_agr hA (by
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [St2, SD])
      have hfr : ∀ y, y ∉ St2 → σ.vars y = σ0.vars y := hA.2
      have e1 : σ.vars "t" = σ0.vars "t" := hfr "t" (by simp [St2, SD])
      have e2 : σ.vars "dt" = σ0.vars "dt" := hfr "dt" (by simp [St2, SD])
      have e3 : σ.vars "du" = σ0.vars "du" := hfr "du" (by simp [St2, SD])
      have e4 : σ.vars "e" = σ0.vars "e" := hfr "e" (by simp [St2, SD])
      have hq : σ.vars "vi" ≤ σ0.vars "vi" + σ.vars "t2" * m := hQ
      have hmul : σ.vars "t2" * m ≤ σ0.vars "t" * m := Nat.mul_le_mul_right _ (by omega)
      obtain ⟨σ', r, hv, hA', h2', ho'⟩ := t2Body_run hV' (by omega) (by rw [e2]; exact hdt)
        (by rw [e3]; exact hdu) (by rw [e4]; exact he) (by omega)
      refine ⟨σ', r, ?_, agr_comp (S := St2) hA hA' (by intro x hx; exact hx) (by intro x hx; exact hx),
        h2', ho'⟩
      rw [hv, e2, e3, e4])
  obtain ⟨σ', r, hv, hA, ho⟩ := hf
  refine ⟨σ', r, ?_, hA, ho⟩
  rw [hv, Lax117284Proofs.TwViol.foldl_add_range]

/-! ### The loop over the clients of the bag -/

/-- The digit of the client `t` and the client itself. -/
def tPre : Com :=
  .seq (.assign "dt" (.bin .and (.bin .shiftr (V "e") (mul (V "m") (V "t"))) (V "mask")))
    (.assign "du" (G "BG" (add (V "off") (V "t"))))

/-- The check of fairness: one violation if the client is served fewer than `kk` times. -/
def fairChk : Com :=
  .ite (.lt (V "pcn") (V "kk")) (.assign "vi" (add (V "vi") (L 1))) .skip

/-- The body of the loop over the clients of the bag. -/
def tBody : Com := .seq tPre (.seq t2Loop (.seq pcLoop fairChk))

/-- The scalars the loop over the clients writes. -/
def Stt : List String := "t" :: "dt" :: "du" :: "pcn" :: St2

theorem tPre_run {X : List ℕ} {n m kk : ℕ} {bl : List ℕ} {σ : Env}
    (hV : VC X n m kk bl B σ) (ht : σ.vars "t" < bl.length) (he : σ.vars "e" < B) :
    ∃ σ', Run B tPre σ σ' 30 ∧ σ'.vars "dt" = dg (2 ^ m) (σ.vars "e") (σ.vars "t") ∧
      σ'.vars "du" = bl[σ.vars "t"]! ∧ Agr ["dt", "du"] σ σ' ∧ σ'.out = σ.out := by
  have hbg := hV.BG_ (σ.vars "t") ht
  have hbgB := hV.BGB (σ.vars "t") ht
  have hlt2 : σ.vars "off" + σ.vars "t" < (σ.arrs "BG").length := by
    have := hV.BGlen; omega
  have hmt : m * σ.vars "t" ≤ m * bl.length := Nat.mul_le_mul_left _ (by omega)
  have hvB := hV.vB
  have hmB := hV.mB
  have hnB := hV.nB
  have hmask := hV.mask_
  have hmask2 := hV.mask2
  have hoB := hV.offB
  have hm' : σ.vars "m" = m := hV.m_
  have hmm : σ.vars "m" * σ.vars "t" ≤ m * bl.length := by rw [hm']; exact hmt
  have hcom : m * bl.length = bl.length * m := Nat.mul_comm _ _
  unfold tPre
  run_vcg
  all_goals try (first
    | exact lt_of_le_of_lt (Nat.div_le_self _ _) he
    | exact lt_of_le_of_lt Nat.and_le_right (by rw [hmask]; omega)
    | (nrm; rw [hbg]; omega)
    | omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · nrm; rw [hmask, hm', dg_land]
  · nrm; exact hbg
  · refine ⟨?_, ?_⟩
    · simp only [arrs_setVar]
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [Env.setVar, hy.1, hy.2]
  · rfl

theorem fairChk_run (kk : ℕ) (σ : Env) (hkk : σ.vars "kk" = kk) (hp : σ.vars "pcn" < B)
    (hkB : kk < B) (hvi : σ.vars "vi" + 2 < B) :
    ∃ σ', Run B fairChk σ σ' 20 ∧
      σ'.vars "vi" = σ.vars "vi" + (if kk ≤ σ.vars "pcn" then 0 else 1) ∧
      Agr ["vi"] σ σ' ∧ σ'.out = σ.out := by
  unfold fairChk
  run_vcg
  · refine ⟨?_, agr_set (by simp) _, rfl⟩
    rw [if_neg (by omega)]; nrm
  · refine ⟨?_, Agr.refl _ _, rfl⟩
    rw [if_pos (by omega)]; rfl

lemma popc_le (m x : ℕ) : popc m x ≤ m := by
  unfold popc
  calc ∑ d ∈ Finset.range m, (if x.testBit d = true then 1 else 0) ≤ ∑ d ∈ Finset.range m, 1 :=
      Finset.sum_le_sum fun d _ => by split_ifs <;> omega
    _ = m := by simp

theorem tBody_run {X : List ℕ} {n m kk : ℕ} {bl : List ℕ} {σ : Env}
    (hV : VC X n m kk bl B σ) (ht : σ.vars "t" < bl.length) (he : σ.vars "e" < B)
    (hvi : σ.vars "vi" + σ.vars "t" * m + m + 3 < B) :
    ∃ σ', Run B tBody σ σ' (30 + ((30 + (200 + 10 + 4) * m + 6 + 10 + 4) * σ.vars "t" + 6) +
        ((10 + 10 + 4) * m + 6 + 2) + 20) ∧
      σ'.vars "vi" = σ.vars "vi" +
        ((if kk ≤ popc m (dg (2 ^ m) (σ.vars "e") (σ.vars "t")) then 0 else 1) +
          ∑ t2 ∈ Finset.range (σ.vars "t"),
            cfDayN X n m bl[σ.vars "t"]! bl[t2]! (dg (2 ^ m) (σ.vars "e") (σ.vars "t"))
              (dg (2 ^ m) (σ.vars "e") t2)) ∧
      Agr Stt σ σ' ∧ σ'.vars "t" = σ.vars "t" ∧ σ'.out = σ.out := by
  have hmB := hV.mB
  have hbgB := hV.BGB (σ.vars "t") ht
  obtain ⟨σ1, r1, hdt, hdu, a1, o1⟩ := tPre_run hV ht he
  have fr1 : ∀ y, y ≠ "dt" → y ≠ "du" → σ1.vars y = σ.vars y := fun y h1 h2 =>
    a1.2 y (by simp [h1, h2])
  have hV1 : VC X n m kk bl B σ1 := hV.of_agr a1 (by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  have hdtB : σ1.vars "dt" < B := by
    rw [hdt]; unfold dg
    exact lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _)) hV.mask2
  have e1t : σ1.vars "t" = σ.vars "t" := fr1 "t" (by decide) (by decide)
  have e1e : σ1.vars "e" = σ.vars "e" := fr1 "e" (by decide) (by decide)
  have e1v : σ1.vars "vi" = σ.vars "vi" := fr1 "vi" (by decide) (by decide)
  obtain ⟨σ2, r2, hv2, a2, o2⟩ := t2Loop_run hV1 (by rw [e1t]; exact ht) hdtB
    (by rw [hdu]; exact hbgB) (by rw [e1e]; exact he) (by rw [e1t, e1v]; omega)
  have fr2 : ∀ y, y ∉ St2 → σ2.vars y = σ1.vars y := a2.2
  have e2m : σ2.vars "m" = m := by rw [fr2 "m" (by simp [St2, SD])]; exact hV1.m_
  have e2dt : σ2.vars "dt" = σ1.vars "dt" := fr2 "dt" (by simp [St2, SD])
  obtain ⟨σ3, r3, hv3, a3, o3⟩ := pcLoop_run (B := B) m σ2 e2m (by omega) (by rw [e2dt]; exact hdtB)
  have fr3 : ∀ y, y ∉ SP → σ3.vars y = σ2.vars y := a3.2
  have hpcB : σ3.vars "pcn" < B := by rw [hv3]; have := popc_le m (σ2.vars "dt"); omega
  have e3kk : σ3.vars "kk" = kk := by
    rw [fr3 "kk" (by simp [SP]), fr2 "kk" (by simp [St2, SD])]; exact hV1.kk_
  have e3vi : σ3.vars "vi" = σ2.vars "vi" := fr3 "vi" (by simp [SP])
  have hsum : ∑ t2 ∈ Finset.range (σ1.vars "t"),
      cfDayN X n m (σ1.vars "du") bl[t2]! (σ1.vars "dt") (dg (2 ^ m) (σ1.vars "e") t2) ≤
        σ1.vars "t" * m := by
    calc _ ≤ ∑ t2 ∈ Finset.range (σ1.vars "t"), m :=
          Finset.sum_le_sum fun t2 _ => cfDayN_le _ _ _ _ _ _ _
      _ = σ1.vars "t" * m := by simp
  obtain ⟨σ4, r4, hv4, a4, o4⟩ := fairChk_run kk σ3 e3kk hpcB hV.kkB
    (by rw [e3vi, hv2, e1v]; have e1t' : σ1.vars "t" * m = σ.vars "t" * m := by rw [e1t]
        omega)
  have fr4 : ∀ y, y ∉ ["vi"] → σ4.vars y = σ3.vars y := a4.2
  refine ⟨σ4, ?_, ?_, ?_, ?_, ?_⟩
  · exact (r1.seq (r2.seq (r3.seq r4))).mono (by rw [e1t]; omega)
  · rw [hv4, e3vi, hv2, hv3, e2dt, hdt, e1t, hdu, e1e, e1v]
    ring
  · have hs1 : ∀ x ∈ ["dt", "du"], x ∈ Stt := by
      intro x hx; simp [Stt, St2, SD] at hx ⊢; tauto
    have hs2 : ∀ x ∈ St2, x ∈ Stt := by
      intro x hx; simp only [Stt, List.mem_cons]; right; right; right; right; exact hx
    have hs3 : ∀ x ∈ SP, x ∈ Stt := by
      intro x hx; simp [SP] at hx; rcases hx with rfl | rfl <;> simp [Stt, St2, SD]
    have hs4 : ∀ x ∈ ["vi"], x ∈ Stt := by
      intro x hx; simp at hx; subst hx; simp [Stt, St2, SD]
    exact agr_comp (S := Stt) a1 (agr_comp (S := Stt) a2 (agr_comp (S := Stt) a3 a4 hs3 hs4) hs2
      (by intro x hx; exact hx)) hs1 (by intro x hx; exact hx)
  · rw [fr4 "t" (by simp), fr3 "t" (by simp [SP]), fr2 "t" (by simp [St2, SD]), fr1 "t" (by decide) (by decide)]
  · rw [o4, o3, o2, o1]

/-- **The number of violations**, read off the instance word. -/
def violN (X : List ℕ) (n m kk : ℕ) (bl : List ℕ) (e : ℕ) : ℕ :=
  ∑ t ∈ Finset.range bl.length,
    ((if kk ≤ popc m (dg (2 ^ m) e t) then 0 else 1) +
      ∑ t2 ∈ Finset.range t, cfDayN X n m bl[t]! bl[t2]! (dg (2 ^ m) e t) (dg (2 ^ m) e t2))

/-- The loop over the clients of the bag. -/
def tLoop : Com := fLoop "t" "vs" tBody

/-- The whole count. -/
def violCom : Com := .seq (.assign "vi" (L 0)) tLoop

lemma quad_step (j m : ℕ) : j * (j * m + 1) + 1 + j * m ≤ (j + 1) * ((j + 1) * m + 1) := by
  nlinarith

theorem tLoop_run {X : List ℕ} {n m kk : ℕ} {bl : List ℕ} {σ0 : Env}
    (hV : VC X n m kk bl B σ0) (he : σ0.vars "e" < B) (hv0 : σ0.vars "vi" = 0) :
    ∃ σ', Run B tLoop σ0 σ'
        ((30 + ((30 + (200 + 10 + 4) * m + 6 + 10 + 4) * bl.length + 6) +
          ((10 + 10 + 4) * m + 6 + 2) + 20 + 10 + 4) * bl.length + 6) ∧
      σ'.vars "vi" = σ0.vars "vi" + violN X n m kk bl (σ0.vars "e") ∧
      Agr Stt σ0 σ' ∧ σ'.out = σ0.out := by
  have hf := fLoop_spec (B := B) "t" "vs" "vi" tBody Stt
    (fun t a => a + ((if kk ≤ popc m (dg (2 ^ m) (σ0.vars "e") t) then 0 else 1) +
      ∑ t2 ∈ Finset.range t, cfDayN X n m bl[t]! bl[t2]! (dg (2 ^ m) (σ0.vars "e") t)
        (dg (2 ^ m) (σ0.vars "e") t2)))
    (fun j a => a ≤ j * (j * m + 1))
    (30 + ((30 + (200 + 10 + 4) * m + 6 + 10 + 4) * bl.length + 6) +
          ((10 + 10 + 4) * m + 6 + 2) + 20) bl.length σ0
    (by simp [Stt]) (by simp [Stt, St2, SD]) (by decide) hV.vs_ (by have := hV.lenB; omega)
    (by rw [hv0]; exact Nat.zero_le _)
    (fun j a h => by
      have h1 : ∑ t2 ∈ Finset.range j, cfDayN X n m bl[j]! bl[t2]! (dg (2 ^ m) (σ0.vars "e") j)
          (dg (2 ^ m) (σ0.vars "e") t2) ≤ j * m := by
        calc _ ≤ ∑ t2 ∈ Finset.range j, m :=
              Finset.sum_le_sum fun t2 _ => cfDayN_le _ _ _ _ _ _ _
          _ = j * m := by simp
      have h2 := quad_step j m
      split_ifs <;> omega) (by
      intro σ hA hlt hQ
      have hV' := hV.of_agr hA (by
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Stt, St2, SD])
      have hfr : ∀ y, y ∉ Stt → σ.vars y = σ0.vars y := hA.2
      have e1 : σ.vars "e" = σ0.vars "e" := hfr "e" (by simp [Stt, St2, SD])
      have hlt' : σ.vars "t" < bl.length := hlt
      have hq : σ.vars "vi" ≤ σ.vars "t" * (σ.vars "t" * m + 1) := hQ
      have hm1 : σ.vars "t" * (σ.vars "t" * m + 1) ≤ bl.length * (bl.length * m + 1) :=
        Nat.mul_le_mul hlt'.le (by have := Nat.mul_le_mul_right m hlt'.le; omega)
      have hm2 : σ.vars "t" * m ≤ bl.length * m := Nat.mul_le_mul_right m hlt'.le
      have hvB := hV.vB
      have hcost : (30 + (200 + 10 + 4) * m + 6 + 10 + 4) * σ.vars "t" ≤
          (30 + (200 + 10 + 4) * m + 6 + 10 + 4) * bl.length := Nat.mul_le_mul_left _ hlt'.le
      obtain ⟨σ', r, hv, hA', ht', ho'⟩ := tBody_run hV' hlt' (by rw [e1]; exact he) (by omega)
      refine ⟨σ', r.mono (by omega), ?_, agr_comp (S := Stt) hA hA' (by intro x hx; exact hx)
        (by intro x hx; exact hx), ht', ho'⟩
      rw [hv, e1])
  obtain ⟨σ', r, hv, hA, ho⟩ := hf
  refine ⟨σ', r, ?_, hA, ho⟩
  rw [hv, Lax117284Proofs.TwViol.foldl_add_range]
  rfl

/-- The scalars the count writes. -/
def SV : List String := "vi" :: Stt

/-- **The count of the violations of a restriction**, as a single IMP+ command: `vi` is set to
`violN`. -/
theorem violCom_run {X : List ℕ} {n m kk : ℕ} {bl : List ℕ} {σ : Env}
    (hV : VC X n m kk bl B σ) (he : σ.vars "e" < B) :
    ∃ σ', Run B violCom σ σ'
        ((30 + ((30 + (200 + 10 + 4) * m + 6 + 10 + 4) * bl.length + 6) +
          ((10 + 10 + 4) * m + 6 + 2) + 20 + 10 + 4) * bl.length + 6 + 2) ∧
      σ'.vars "vi" = violN X n m kk bl (σ.vars "e") ∧ Agr SV σ σ' ∧ σ'.out = σ.out := by
  have hz : Run B (.assign "vi" (L 0)) σ (σ.setVar "vi" 0) 2 :=
    (Run.assign (evalB_lit (by have := hV.lenB; omega))).mono (by simp)
  have a0 : Agr ["vi"] σ (σ.setVar "vi" 0) := agr_set (by simp) _
  have hV0 : VC X n m kk bl B (σ.setVar "vi" 0) := hV.of_agr a0 (by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  obtain ⟨σ', r, hv, hA, ho⟩ := tLoop_run hV0 (by simpa using he) (by simp)
  refine ⟨σ', (hz.seq r).mono (by omega), ?_, ?_, ?_⟩
  · rw [hv]; simp [Env.setVar]
  · exact agr_comp (S := SV) a0 hA (by intro x hx; simp at hx; subst hx; simp [SV])
      (by intro x hx; simp [SV]; tauto)
  · rw [ho]; simp [Env.setVar]

end Lax117284Proofs.Machine.TwViol
