import Mathlib

/-!
# Numbers as Lists of Digits

A restriction of a schedule to a bag of `s` clients is a list of `s` masks, each a number below
`b = 2 ^ m`; the dynamic program indexes its table by the number whose base-`b` digits, least
significant first, are those masks. Introducing a client inserts a digit, forgetting one removes
it, and both are arithmetic on the number: `insN` and `rmN`.
-/

namespace Lax117284Proofs.TwDigits

/-- The list `ms` of digits as a number, least significant digit first. -/
def enc (b : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: ms => a + b * enc b ms

/-- The digit at position `t` of `e`. -/
def dg (b e t : ℕ) : ℕ := e / b ^ t % b

/-- The number `e` with digit `S` inserted at position `p`. -/
def insN (b p S e : ℕ) : ℕ := e % b ^ p + S * b ^ p + (e / b ^ p) * (b ^ p * b)

/-- The number `e` with the digit at position `p` removed. -/
def rmN (b p e : ℕ) : ℕ := e % b ^ p + (e / (b ^ p * b)) * b ^ p

variable {b : ℕ}

@[simp] lemma enc_nil : enc b [] = 0 := Eq.trans rfl rfl
@[simp] lemma enc_cons (a : ℕ) (ms : List ℕ) : enc b (a :: ms) = a + b * enc b ms := rfl

lemma enc_lt (hb : 0 < b) : ∀ ms : List ℕ, (∀ a ∈ ms, a < b) → enc b ms < b ^ ms.length
  | [], _ => by simp
  | a :: ms, h => by
    have ha := h a (by simp)
    have ih := enc_lt hb ms (fun x hx => h x (by simp [hx]))
    simp only [enc_cons, List.length_cons, pow_succ]
    calc a + b * enc b ms < b + b * enc b ms := by omega
      _ = b * (enc b ms + 1) := by ring
      _ ≤ b * b ^ ms.length := Nat.mul_le_mul_left _ ih
      _ = b ^ ms.length * b := by ring

lemma dg_zero (e : ℕ) : dg b e 0 = e % b := by simp [dg]

lemma dg_succ (hb : 0 < b) (e t : ℕ) : dg b e (t + 1) = dg b (e / b) t := by
  simp only [dg, pow_succ]
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm]

lemma dg_enc (hb : 0 < b) : ∀ (ms : List ℕ), (∀ a ∈ ms, a < b) → ∀ t, t < ms.length →
    dg b (enc b ms) t = ms[t]!
  | [], _, t, ht => by simp at ht
  | a :: ms, h, 0, _ => by
    have ha := h a (by simp)
    simp [dg_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  | a :: ms, h, t + 1, ht => by
    have ha := h a (by simp)
    have : (a + b * enc b ms) / b = enc b ms := by
      rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt ha, Nat.zero_add]
    simp only [enc_cons, dg_succ hb, this]
    exact dg_enc hb ms (fun x hx => h x (by simp [hx])) t (by simpa using ht)


lemma enc_map_dg (hb : 0 < b) : ∀ (s e : ℕ), e < b ^ s → enc b ((List.range s).map (dg b e)) = e
  | 0, e, h => by simp at h ⊢; omega
  | s + 1, e, h => by
    have h' : e / b < b ^ s := by
      rw [Nat.div_lt_iff_lt_mul hb]; simpa [pow_succ, Nat.mul_comm] using h
    have : (List.range (s + 1)).map (dg b e) = e % b :: (List.range s).map (dg b (e / b)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      · simp [dg_zero]
      · exact List.map_congr_left fun t _ => by simp [dg_succ hb]
    rw [this, enc_cons, enc_map_dg hb s (e / b) h']
    exact Nat.mod_add_div e b

lemma insN_zero (S e : ℕ) : insN b 0 S e = S + b * e := by
  simp [insN, Nat.mod_one, Nat.mul_comm]

lemma insN_cons (hb : 0 < b) {a : ℕ} (ha : a < b) (p S E : ℕ) :
    insN b (p + 1) S (a + b * E) = a + b * insN b p S E := by
  unfold insN
  have h1 : (a + b * E) % b ^ (p + 1) = a + b * (E % b ^ p) := by
    rw [pow_succ', Nat.mod_mul]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.add_mul_div_left _ _ hb,
      Nat.div_eq_of_lt ha, Nat.zero_add]
  have h2 : (a + b * E) / b ^ (p + 1) = E / b ^ p := by
    rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt ha,
      Nat.zero_add]
  rw [h1, h2, pow_succ']
  ring

lemma rmN_zero (e : ℕ) : rmN b 0 e = e / b := by simp [rmN, Nat.mod_one]

lemma rmN_cons (hb : 0 < b) {a : ℕ} (ha : a < b) (p E : ℕ) :
    rmN b (p + 1) (a + b * E) = a + b * rmN b p E := by
  unfold rmN
  have h1 : (a + b * E) % b ^ (p + 1) = a + b * (E % b ^ p) := by
    rw [pow_succ', Nat.mod_mul]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.add_mul_div_left _ _ hb,
      Nat.div_eq_of_lt ha, Nat.zero_add]
  have h2 : (a + b * E) / (b ^ (p + 1) * b) = E / (b ^ p * b) := by
    rw [pow_succ', mul_assoc, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt ha, Nat.zero_add]
  rw [h1, h2, pow_succ']
  ring


lemma enc_insertIdx (hb : 0 < b) (S : ℕ) : ∀ (p : ℕ) (ms : List ℕ), p ≤ ms.length →
    (∀ a ∈ ms, a < b) → enc b (ms.insertIdx p S) = insN b p S (enc b ms)
  | 0, ms, _, _ => by simp [insN_zero]
  | p + 1, [], h, _ => by simp at h
  | p + 1, a :: ms, h, hm => by
    have ha := hm a (by simp)
    rw [List.insertIdx_succ_cons, enc_cons, enc_cons, insN_cons hb ha,
      enc_insertIdx hb S p ms (by simpa using h) (fun x hx => hm x (by simp [hx]))]

lemma enc_eraseIdx (hb : 0 < b) : ∀ (p : ℕ) (ms : List ℕ), p < ms.length →
    (∀ a ∈ ms, a < b) → enc b (ms.eraseIdx p) = rmN b p (enc b ms)
  | _, [], h, _ => by simp at h
  | 0, a :: ms, _, hm => by
    have ha := hm a (by simp)
    simp only [List.eraseIdx_cons_zero, enc_cons, rmN_zero]
    rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt ha, Nat.zero_add]
  | p + 1, a :: ms, h, hm => by
    have ha := hm a (by simp)
    rw [List.eraseIdx_cons_succ, enc_cons, enc_cons, rmN_cons hb ha,
      enc_eraseIdx hb p ms (by simpa using h) (fun x hx => hm x (by simp [hx]))]

lemma rmN_insN (hb : 0 < b) {S : ℕ} (hS : S < b) (p e : ℕ) : rmN b p (insN b p S e) = e := by
  unfold rmN insN
  have hB : 0 < b ^ p := Nat.pow_pos hb
  have hx : e % b ^ p + S * b ^ p + e / b ^ p * (b ^ p * b) =
      e % b ^ p + b ^ p * (S + b * (e / b ^ p)) := by ring
  have h1 : (e % b ^ p + S * b ^ p + e / b ^ p * (b ^ p * b)) % b ^ p = e % b ^ p := by
    rw [hx, Nat.add_mul_mod_self_left, Nat.mod_mod]
  have h2 : (e % b ^ p + S * b ^ p + e / b ^ p * (b ^ p * b)) / (b ^ p * b) = e / b ^ p := by
    rw [hx, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (Nat.mod_lt _ hB),
      Nat.zero_add, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hS, Nat.zero_add]
  rw [h1, h2, Nat.mul_comm (e / b ^ p)]
  exact Nat.mod_add_div e (b ^ p)

lemma insN_rmN (hb : 0 < b) (p e : ℕ) : insN b p (dg b e p) (rmN b p e) = e := by
  unfold rmN insN dg
  have hB : 0 < b ^ p := Nat.pow_pos hb
  have h1 : (e % b ^ p + e / (b ^ p * b) * b ^ p) % b ^ p = e % b ^ p := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_mod]
  have h2 : (e % b ^ p + e / (b ^ p * b) * b ^ p) / b ^ p = e / (b ^ p * b) := by
    rw [Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt (Nat.mod_lt _ hB), Nat.zero_add]
  rw [h1, h2]
  have h3 : e / b ^ p = e / b ^ p % b + b * (e / (b ^ p * b)) := by
    rw [← Nat.div_div_eq_div_mul]; exact (Nat.mod_add_div _ _).symm
  calc e % b ^ p + e / b ^ p % b * b ^ p + e / (b ^ p * b) * (b ^ p * b)
      = e % b ^ p + (e / b ^ p % b + b * (e / (b ^ p * b))) * b ^ p := by ring
    _ = e % b ^ p + e / b ^ p * b ^ p := by rw [← h3]
    _ = e := by rw [Nat.mul_comm]; exact Nat.mod_add_div e (b ^ p)

lemma insN_lt (hb : 0 < b) {s p S e : ℕ} (he : e < b ^ s) (hS : S < b) (hp : p ≤ s) :
    insN b p S e < b ^ (s + 1) := by
  unfold insN
  have hB : 0 < b ^ p := Nat.pow_pos hb
  have hq : e / b ^ p < b ^ (s - p) := by
    rw [Nat.div_lt_iff_lt_mul hB, ← pow_add, Nat.sub_add_cancel hp]; exact he
  have hs : b ^ (s + 1) = b ^ p * (b * b ^ (s - p)) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  have hr := Nat.mod_lt e hB
  calc e % b ^ p + S * b ^ p + e / b ^ p * (b ^ p * b)
      < b ^ p + S * b ^ p + e / b ^ p * (b ^ p * b) := by omega
    _ = b ^ p * (1 + S + b * (e / b ^ p)) := by ring
    _ ≤ b ^ p * (b + b * (e / b ^ p)) := Nat.mul_le_mul_left _ (by omega)
    _ = b ^ p * (b * (e / b ^ p + 1)) := by ring
    _ ≤ b ^ p * (b * b ^ (s - p)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hq)
    _ = b ^ (s + 1) := hs.symm

lemma rmN_lt (hb : 0 < b) {s p e : ℕ} (he : e < b ^ (s + 1)) (hp : p ≤ s) :
    rmN b p e < b ^ s := by
  unfold rmN
  have hB : 0 < b ^ p := Nat.pow_pos hb
  have hq : e / (b ^ p * b) < b ^ (s - p) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos hB hb)]
    have : b ^ (s - p) * (b ^ p * b) = b ^ (s + 1) := by
      rw [← pow_succ, ← pow_add]; congr 1; omega
    rw [this]; exact he
  have hs : b ^ s = b ^ p * b ^ (s - p) := by rw [← pow_add]; congr 1; omega
  have hr := Nat.mod_lt e hB
  calc e % b ^ p + e / (b ^ p * b) * b ^ p < b ^ p + e / (b ^ p * b) * b ^ p := by omega
    _ = (e / (b ^ p * b) + 1) * b ^ p := by ring
    _ ≤ b ^ (s - p) * b ^ p := Nat.mul_le_mul_right _ hq
    _ = b ^ s := by rw [hs, Nat.mul_comm]

end Lax117284Proofs.TwDigits
