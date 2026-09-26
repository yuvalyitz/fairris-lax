import Lax117284Proofs.Machine.D3Coll
import Lax117284Proofs.D3Tab

/-!
A cell that holds a state is one the sweep can serve from safely: its digit is small, the times
add up to a word, and the state it leads to is a cell of the table.
-/

namespace Lax117284Proofs.Machine.D3Cell

open Lax117284Proofs.D3DP Lax117284Proofs.D3Code Lax117284Proofs.D3Tab Lax117284Proofs.Machine.D3Sweep

/-- **A state of the table is a cell the sweep can serve from safely.** -/
theorem cellOk_of_TS {m k n : ℕ} {q : ℕ → ℕ → ℕ} {e : ℕ → ℕ} {c i : ℕ} {arr Rl : List ℕ}
    {PK B : ℕ} (hc : c < n) (hi : i < m) {x : ℕ}
    (hx : TS m k n q e c i x) (hPK : PK = (n + 1) ^ m * (k + 1)) (hRe : eOrd arr Rl PK = e)
    (hsum : ∀ δ, δ ≤ n → q i c + fv e δ + 8 < B) :
    CellOk arr Rl n ((n + 1) ^ m) k (n + 1) ((n + 1) ^ i) c (q i c) (e c) PK B x := by
  have hx0 := hx
  obtain ⟨v, t, hv, rfl⟩ := hx
  obtain ⟨h1, h2⟩ := TS_split hc hv
  have hdig : (enc (n + 1) v + (n + 1) ^ m * t) % (n + 1) ^ m / (n + 1) ^ i % (n + 1) =
      v ⟨i, hi⟩ := by
    rw [h2]
    exact dig_enc (by omega) v (fun y => by have := lay_le m k q e c i v t hv y; omega) ⟨i, hi⟩
  have hle := lay_le m k q e c i v t hv ⟨i, hi⟩
  unfold CellOk
  rw [hRe, hdig]
  refine ⟨hle, by omega, hsum _ (by omega), fun hg => ?_⟩
  have htg : tgt m k n q e c i (enc (n + 1) v + (n + 1) ^ m * t) =
      some (enc (n + 1) v + (n + 1) ^ m * t + (n + 1) ^ m + ((c + 1) - v ⟨i, hi⟩) * (n + 1) ^ i) := by
    unfold tgt
    rw [h1, h2]
    have : dig (n + 1) (enc (n + 1) v) i = v ⟨i, hi⟩ :=
      dig_enc (by omega) v (fun y => by have := lay_le m k q e c i v t hv y; omega) ⟨i, hi⟩
    have hg1 : t < k := by rw [← h1]; exact hg.1
    have hg2 : q i c + fv e (v ⟨i, hi⟩) ≤ e c := hg.2
    rw [this, if_pos ⟨hg1, hg2⟩]
  rw [hPK]
  have := (TS_tgt_lt hc hi hx0 htg).2
  exact this

end Lax117284Proofs.Machine.D3Cell
