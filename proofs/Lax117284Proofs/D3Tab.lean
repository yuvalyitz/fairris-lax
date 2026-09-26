import Lax117284Proofs.D3DP
import Lax117284Proofs.D3Code
import Lax117284Proofs.D3List

/-!
The table of the dynamic program: a state with the number of days served so far is a number below
`P (k + 1)`, `P` being a power of one more than the number of clients, and the table holds a one at
the numbers of the reachable pairs.
-/

namespace Lax117284Proofs.D3Tab

open scoped Classical

open Lax117284Proofs.D3DP Lax117284Proofs.D3Code Lax117284Proofs.D3List

variable (m k n : ℕ) (q : ℕ → ℕ → ℕ) (e : ℕ → ℕ)

/-- The number of a state. -/
def TS (c i x : ℕ) : Prop :=
  ∃ v : Vec m, ∃ t, (v, t) ∈ Lay m k q e c i ∧ enc (n + 1) v + (n + 1) ^ m * t = x

/-- The target of a cell in the sweep that serves the client at position `c` on day `i`. -/
def tgt (c i x : ℕ) : Option ℕ :=
  if x / (n + 1) ^ m < k ∧ q i c + fv e (dig (n + 1) (x % (n + 1) ^ m) i) ≤ e c then
    some (x + (n + 1) ^ m + ((c + 1) - dig (n + 1) (x % (n + 1) ^ m) i) * (n + 1) ^ i)
  else none

lemma reach_le (c : ℕ) : ∀ v ∈ Reach m k q e c, ∀ x, v x ≤ c := by
  induction c with
  | zero =>
    intro v hv x
    have : v = fun _ => 0 := hv
    subst this; simp
  | succ c ih =>
    intro v' hv' x
    obtain ⟨v, hv, S, -, -, rfl⟩ := hv'
    have := ih v hv x
    unfold stepV; split <;> omega

lemma lay_le (c : ℕ) : ∀ i v t, (v, t) ∈ Lay m k q e c i → ∀ x, v x ≤ c + 1 := by
  intro i
  induction i with
  | zero =>
    intro v t h x
    have := reach_le m k q e c v h.1 x; omega
  | succ i ih =>
    intro v' t' h x
    obtain ⟨⟨v0, t0⟩, h0, h⟩ := h
    have ih' := ih v0 t0 h0
    rcases h with h | ⟨hh, hlt, hf, h⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ih' x
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      by_cases hx : x = ⟨i, hh⟩
      · subst hx; simp
      · simp [Function.update, hx]; exact ih' x

lemma lay_t_le (c : ℕ) : ∀ i, i ≤ m → ∀ v t, (v, t) ∈ Lay m k q e c i → t ≤ k := by
  intro i hi v t h
  obtain ⟨v0, -, S, -, hc, hk, -, -⟩ := (lay_iff m k q e c i hi v t).1 h
  exact hk

variable {m k n q e} {c : ℕ}

lemma enc_lt_P {c : ℕ} (hc : c < n) {i : ℕ} {v : Vec m} {t : ℕ}
    (h : (v, t) ∈ Lay m k q e c i) : enc (n + 1) v < (n + 1) ^ m :=
  enc_lt (by omega) v (fun x => by have := lay_le m k q e c i v t h x; omega)

/-- **A pair of the layer is determined by its number.** -/
lemma TS_split {c : ℕ} (hc : c < n) {i : ℕ} {v : Vec m} {t : ℕ}
    (h : (v, t) ∈ Lay m k q e c i) :
    (enc (n + 1) v + (n + 1) ^ m * t) / (n + 1) ^ m = t ∧
      (enc (n + 1) v + (n + 1) ^ m * t) % (n + 1) ^ m = enc (n + 1) v := by
  have hlt := enc_lt_P hc h
  have hP : 0 < (n + 1) ^ m := by positivity
  constructor
  · rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hlt]; simp
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

lemma TS_lt {c i x : ℕ} (hc : c < n) (hi : i ≤ m) (h : TS m k n q e c i x) : x < (n + 1) ^ m * (k + 1) := by
  obtain ⟨v, t, hv, rfl⟩ := h
  have h1 := enc_lt_P hc hv
  have h2 := lay_t_le m k q e c i hi v t hv
  have : (n + 1) ^ m * (t + 1) ≤ (n + 1) ^ m * (k + 1) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-- **The target of the number of a pair.** -/
lemma tgt_serve (hc : c < n) {i : ℕ} (hi : i < m) {v : Vec m} {t : ℕ}
    (h : (v, t) ∈ Lay m k q e c i) (hlt : t < k) (hf : feas m q e c v ⟨i, hi⟩) :
    tgt m k n q e c i (enc (n + 1) v + (n + 1) ^ m * t) =
      some (enc (n + 1) (Function.update v ⟨i, hi⟩ (c + 1)) + (n + 1) ^ m * (t + 1)) := by
  obtain ⟨h1, h2⟩ := TS_split hc h
  have hdig : dig (n + 1) (enc (n + 1) v) i = v ⟨i, hi⟩ :=
    dig_enc (by omega) v (fun x => by have := lay_le m k q e c i v t h x; omega) ⟨i, hi⟩
  have hle := lay_le m k q e c i v t h ⟨i, hi⟩
  have hup := enc_update (b := n + 1) v ⟨i, hi⟩ (c + 1)
  unfold tgt
  rw [h1, h2, hdig, if_pos ⟨hlt, hf⟩]
  simp only [Fin.val_mk] at hup
  have : (c + 1 - v ⟨i, hi⟩) * (n + 1) ^ i + v ⟨i, hi⟩ * (n + 1) ^ i = (c + 1) * (n + 1) ^ i := by
    rw [← Nat.add_mul]; congr 1; omega
  congr 1
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- **A cell with a target is a pair that can serve.** -/
lemma serve_tgt (hc : c < n) {i : ℕ} (hi : i < m) {v : Vec m} {t : ℕ}
    (h : (v, t) ∈ Lay m k q e c i) {y : ℕ}
    (hy : tgt m k n q e c i (enc (n + 1) v + (n + 1) ^ m * t) = some y) :
    t < k ∧ feas m q e c v ⟨i, hi⟩ ∧
      y = enc (n + 1) (Function.update v ⟨i, hi⟩ (c + 1)) + (n + 1) ^ m * (t + 1) := by
  obtain ⟨h1, h2⟩ := TS_split hc h
  have hdig : dig (n + 1) (enc (n + 1) v) i = v ⟨i, hi⟩ :=
    dig_enc (by omega) v (fun x => by have := lay_le m k q e c i v t h x; omega) ⟨i, hi⟩
  by_cases hcond : t < k ∧ feas m q e c v ⟨i, hi⟩
  · rw [tgt_serve hc hi h hcond.1 hcond.2] at hy
    exact ⟨hcond.1, hcond.2, (Option.some.inj hy).symm⟩
  · exfalso
    unfold tgt at hy
    rw [h1, h2, hdig] at hy
    have hcond' : ¬ (t < k ∧ q i c + fv e (v ⟨i, hi⟩) ≤ e c) := hcond
    rw [if_neg hcond'] at hy
    exact absurd hy (by simp)

/-- **One day of the client changes the set of numbers as the sweep does.** -/
theorem TS_succ_iff (hc : c < n) {i : ℕ} (hi : i < m) (y : ℕ) :
    TS m k n q e c (i + 1) y ↔ TS m k n q e c i y ∨
      ∃ x, TS m k n q e c i x ∧ tgt m k n q e c i x = some y := by
  constructor
  · rintro ⟨v', t', hv', hy⟩
    obtain ⟨⟨v0, t0⟩, h0, h⟩ := hv'
    rcases h with h | ⟨hh, hlt, hf, h⟩
    · obtain ⟨h1, h2⟩ := Prod.mk.inj h
      rw [h1, h2] at hy
      exact Or.inl ⟨v0, t0, h0, hy⟩
    · obtain ⟨h1, h2⟩ := Prod.mk.inj h
      rw [h1, h2] at hy
      refine Or.inr ⟨enc (n + 1) v0 + (n + 1) ^ m * t0, ⟨v0, t0, h0, rfl⟩, ?_⟩
      rw [tgt_serve hc hi h0 hlt hf, hy]
  · rintro (⟨v, t, hv, hy⟩ | ⟨x, ⟨v, t, hv, rfl⟩, hy⟩)
    · exact ⟨v, t, ⟨(v, t), hv, Or.inl rfl⟩, hy⟩
    · obtain ⟨hlt, hf, rfl⟩ := serve_tgt hc hi hv hy
      exact ⟨_, _, ⟨(v, t), hv, Or.inr ⟨hi, hlt, hf, rfl⟩⟩, rfl⟩

/-- The table after the days below `i` of the client at position `c`. -/
def RT (m k n : ℕ) (q : ℕ → ℕ → ℕ) (e : ℕ → ℕ) (c i : ℕ) (A : List ℕ) : Prop :=
  ∀ x < (n + 1) ^ m * (k + 1), A.getD x 0 = if TS m k n q e c i x then 1 else 0

/-- **The target of a state is a later cell of the table.** -/
theorem TS_tgt_lt (hc : c < n) {i : ℕ} (hi : i < m) {x y : ℕ} (hx : TS m k n q e c i x)
    (hy : tgt m k n q e c i x = some y) : x < y ∧ y < (n + 1) ^ m * (k + 1) := by
  have hP : 0 < (n + 1) ^ m := by positivity
  obtain ⟨v, t, hv, rfl⟩ := hx
  obtain ⟨hlt, hf', rfl⟩ := serve_tgt hc hi hv hy
  have hlt' := enc_lt_P hc hv
  have hlt2 : enc (n + 1) (Function.update v ⟨i, hi⟩ (c + 1)) < (n + 1) ^ m := by
    refine enc_lt (by omega) _ (fun x => ?_)
    have := lay_le m k q e c i v t hv x
    by_cases hx : x = ⟨i, hi⟩
    · subst hx; simp; omega
    · simp [Function.update, hx]; omega
  have : (n + 1) ^ m * (t + 1) ≤ (n + 1) ^ m * k := Nat.mul_le_mul_left _ (by omega)
  constructor
  · nlinarith
  · nlinarith

/-- **The sweep of a day.** -/
theorem RT_sweep (hc : c < n) {i : ℕ} (hi : i < m) (A : List ℕ)
    (hlen : (n + 1) ^ m * (k + 1) ≤ A.length) (hA : RT m k n q e c i A) :
    RT m k n q e c (i + 1) (swRun ((n + 1) ^ m * (k + 1)) (tgt m k n q e c i) A) ∧
      (swRun ((n + 1) ^ m * (k + 1)) (tgt m k n q e c i) A).length = A.length ∧
      ∀ y, (n + 1) ^ m * (k + 1) ≤ y →
        (swRun ((n + 1) ^ m * (k + 1)) (tgt m k n q e c i) A).getD y 0 = A.getD y 0 := by
  have hP : 0 < (n + 1) ^ m := by positivity
  have hf : ∀ x < (n + 1) ^ m * (k + 1), A.getD x 0 = 1 → ∀ y, tgt m k n q e c i x = some y →
      x < y ∧ y < (n + 1) ^ m * (k + 1) := by
    intro x hx h1 y hy
    have hts := hA x hx
    rw [h1] at hts
    have : TS m k n q e c i x := by
      by_contra hn'; rw [if_neg hn'] at hts; omega
    obtain ⟨v, t, hv, rfl⟩ := this
    obtain ⟨hlt, hf', rfl⟩ := serve_tgt hc hi hv hy
    have hlt' := enc_lt_P hc hv
    have hlt2 : enc (n + 1) (Function.update v ⟨i, hi⟩ (c + 1)) < (n + 1) ^ m := by
      refine enc_lt (by omega) _ (fun x => ?_)
      have := lay_le m k q e c i v t hv x
      by_cases hx : x = ⟨i, hi⟩
      · subst hx; simp; omega
      · simp [Function.update, hx]; omega
    have : (n + 1) ^ m * (t + 1) ≤ (n + 1) ^ m * k := Nat.mul_le_mul_left _ (by omega)
    constructor
    · nlinarith
    · nlinarith
  have hA01 : ∀ x < (n + 1) ^ m * (k + 1), A.getD x 0 ≤ 1 := by
    intro x hx; rw [hA x hx]; split <;> omega
  obtain ⟨hl, hout, hin⟩ := swRun_inv ((n + 1) ^ m * (k + 1)) (tgt m k n q e c i) A hf hA01 hlen
    ((n + 1) ^ m * (k + 1)) le_rfl
  refine ⟨fun y hy => ?_, hl, hout⟩
  unfold swRun
  rw [hin y hy, hA y hy]
  have hAx : ∀ x < (n + 1) ^ m * (k + 1), A.getD x 0 = 1 ↔ TS m k n q e c i x := by
    intro x hx
    rw [hA x hx]
    constructor
    · intro h; by_contra hn'; rw [if_neg hn'] at h; omega
    · intro h; rw [if_pos h]
  have hiff : (TS m k n q e c i y ∨ ∃ x, TS m k n q e c i x ∧ tgt m k n q e c i x = some y) ↔
      ((if TS m k n q e c i y then 1 else 0) = 1 ∨
        ∃ x, (n + 1) ^ m * (k + 1) - (n + 1) ^ m * (k + 1) ≤ x ∧ x < (n + 1) ^ m * (k + 1) ∧
          A.getD x 0 = 1 ∧ tgt m k n q e c i x = some y) := by
    constructor
    · rintro (h | ⟨x, hx, hxy⟩)
      · left; rw [if_pos h]
      · right
        have hxN := TS_lt hc hi.le hx
        exact ⟨x, by omega, hxN, (hAx x hxN).2 hx, hxy⟩
    · rintro (h | ⟨x, -, hxN, h1, hxy⟩)
      · left; by_contra hn'; rw [if_neg hn'] at h; omega
      · right
        exact ⟨x, (hAx x hxN).1 h1, hxy⟩
  rw [← TS_succ_iff hc hi] at hiff
  by_cases hT : TS m k n q e c (i + 1) y
  · rw [if_pos hT, if_pos (hiff.1 hT)]
  · rw [if_neg hT, if_neg (fun h => hT (hiff.2 h))]

/-- **The states after one more client are the states that served it on `k` days.** -/
theorem TS0_iff (hc : c < n) (x : ℕ) :
    TS m k n q e (c + 1) 0 x ↔ x < (n + 1) ^ m ∧ TS m k n q e c m (x + (n + 1) ^ m * k) := by
  have hP : 0 < (n + 1) ^ m := by positivity
  have hreach : ∀ v, v ∈ Reach m k q e (c + 1) ↔ (v, k) ∈ Lay m k q e c m := by
    intro v
    rw [lay_iff m k q e c m le_rfl v k]
    constructor
    · rintro ⟨v0, hv0, S, hS, hfs, rfl⟩
      exact ⟨v0, hv0, S, fun x _ => x.isLt, hS, le_rfl, hfs, rfl⟩
    · rintro ⟨v0, hv0, S, -, hS, -, hfs, rfl⟩
      exact ⟨v0, hv0, S, hS, hfs, rfl⟩
  constructor
  · rintro ⟨v, t, ⟨hv, ht⟩, rfl⟩
    have hd : ∀ y, v y ≤ n := fun y => by
      have := reach_le m k q e (c + 1) v hv y; omega
    have hlt : enc (n + 1) v < (n + 1) ^ m := enc_lt (by omega) v (fun y => by have := hd y; omega)
    subst ht
    refine ⟨by simpa using hlt, v, k, (hreach v).1 hv, by simp⟩
  · rintro ⟨hx, v, t, hv, heq⟩
    have hlt := enc_lt_P hc hv
    have h1 := TS_split hc hv
    have hk : t = k := by
      have := congrArg (fun z => z / (n + 1) ^ m) heq
      beta_reduce at this
      rw [h1.1, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hx] at this
      omega
    subst hk
    have hx' : enc (n + 1) v = x := by omega
    exact ⟨v, 0, ⟨(hreach v).2 hv, rfl⟩, by simpa using hx'⟩

/-- **The table at the start.** -/
theorem RT_init (A : List ℕ) (hA : ∀ x < (n + 1) ^ m * (k + 1), A.getD x 0 = if x = 0 then 1 else 0) :
    RT m k n q e 0 0 A := by
  intro x hx
  rw [hA x hx]
  have : TS m k n q e 0 0 x ↔ x = 0 := by
    constructor
    · rintro ⟨v, t, ⟨hv, ht⟩, rfl⟩
      have : v = fun _ => 0 := hv
      subst this; subst ht
      simp [enc]
    · rintro rfl
      exact ⟨fun _ => 0, 0, ⟨rfl, rfl⟩, by simp [enc]⟩
  by_cases h0 : x = 0
  · rw [if_pos h0, if_pos (this.2 h0)]
  · rw [if_neg h0, if_neg (fun h => h0 (this.1 h))]

/-- **A state is reachable after the last client exactly when the table has a one below `P`.** -/
theorem RT_final (A : List ℕ) (hA : RT m k n q e n 0 A) :
    (∃ s < (n + 1) ^ m, A.getD s 0 = 1) ↔ (Reach m k q e n).Nonempty := by
  constructor
  · rintro ⟨s, hs, h1⟩
    have hsK : s < (n + 1) ^ m * (k + 1) := by
      have : (n + 1) ^ m * 1 ≤ (n + 1) ^ m * (k + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    have := hA s hsK
    rw [h1] at this
    have hT : TS m k n q e n 0 s := by
      by_contra hn'; rw [if_neg hn'] at this; omega
    obtain ⟨v, t, ⟨hv, -⟩, -⟩ := hT
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    have hd : ∀ y, v y < n + 1 := fun y => by have := reach_le m k q e n v hv y; omega
    have hlt : enc (n + 1) v < (n + 1) ^ m := enc_lt (by omega) v hd
    have hsK : enc (n + 1) v < (n + 1) ^ m * (k + 1) := by
      have : (n + 1) ^ m * 1 ≤ (n + 1) ^ m * (k + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    refine ⟨enc (n + 1) v, hlt, ?_⟩
    rw [hA _ hsK, if_pos]
    exact ⟨v, 0, ⟨hv, rfl⟩, by simp⟩

open scoped Classical in
/-- **The collapse of the table.** -/
theorem RT_collapse (hc : c < n) (A : List ℕ) (hlen : (n + 1) ^ m * (k + 1) ≤ A.length)
    (hA : RT m k n q e c m A) :
    RT m k n q e (c + 1) 0 ((List.range ((n + 1) ^ m * (k + 1))).foldl
      (fun A x => clStep ((n + 1) ^ m) k x A) A) ∧
    ((List.range ((n + 1) ^ m * (k + 1))).foldl (fun A x => clStep ((n + 1) ^ m) k x A) A).length
      = A.length ∧
    ∀ y, (n + 1) ^ m * (k + 1) ≤ y →
      ((List.range ((n + 1) ^ m * (k + 1))).foldl (fun A x => clStep ((n + 1) ^ m) k x A) A).getD y 0
        = A.getD y 0 := by
  obtain ⟨hl, hout, hin⟩ := clRun_inv ((n + 1) ^ m) k A hlen ((n + 1) ^ m * (k + 1)) le_rfl
  refine ⟨fun x hx => ?_, hl, hout⟩
  rw [hin x hx, TS0_iff hc x]
  by_cases hx1 : x < (n + 1) ^ m
  · have hxk : x + (n + 1) ^ m * k < (n + 1) ^ m * (k + 1) := by nlinarith
    rw [if_pos hx1, hA _ hxk]
    by_cases hT : TS m k n q e c m (x + (n + 1) ^ m * k)
    · rw [if_pos hT, if_pos ⟨hx1, hT⟩]
    · rw [if_neg hT, if_neg (fun h => hT h.2)]
  · rw [if_neg hx1, if_neg (fun h => hx1 h.1)]

end Lax117284Proofs.D3Tab
