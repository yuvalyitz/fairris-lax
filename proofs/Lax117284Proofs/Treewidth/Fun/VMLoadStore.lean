import Lax117284Proofs.Treewidth.Fun.VMLoadCode

/-!
# WP V3 (2): straight-line stores — the loader of a *fixed* list of constants

`storeSeq a i l` is the command `a[i] := l₀; a[i+1] := l₁; …` (one `store` of two literals per element, a
right-nested `seq`; **never** simplified as a whole: every statement below is proved by induction on the list).
It loads the code arrays `OP`, `OA` and the function table `FT`.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-- `a[i] := l₀; a[i+1] := l₁; …`. -/
def storeSeq (a : String) : ℕ → List ℕ → Com
  | _, [] => .skip
  | i, v :: vs => .seq (.store a (.lit i) (.lit v)) (storeSeq a (i + 1) vs)

theorem storeSeq_ok {L : Layout} {a : String} (ha : a ∈ L.arrays) (h0 : 0 < L.temps) :
    ∀ (l : List ℕ) (i : ℕ), Com.Ok L (storeSeq a i l) := by
  intro l
  induction l with
  | nil => intro i; exact Com.ok_skip _
  | cons v vs ih =>
    intro i
    exact ⟨⟨ha, trivial, trivial, h0⟩, ih (i + 1)⟩

theorem storeSeq_wvars (a : String) : ∀ (l : List ℕ) (i : ℕ), (storeSeq a i l).wvars = [] := by
  intro l
  induction l with
  | nil => intro i; rfl
  | cons v vs ih => intro i; simp [storeSeq, Com.wvars, ih]

theorem storeSeq_warrs (a : String) : ∀ (l : List ℕ) (i : ℕ), ∀ b ∈ (storeSeq a i l).warrs, b = a := by
  intro l
  induction l with
  | nil => intro i b hb; simp [storeSeq, Com.warrs] at hb
  | cons v vs ih =>
    intro i b hb
    simp only [storeSeq, Com.warrs, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | hb
    · exact hb
    · exact ih _ b hb

theorem storeSeq_noWrite (a : String) : ∀ (l : List ℕ) (i : ℕ), (storeSeq a i l).NoWrite := by
  intro l
  induction l with
  | nil => intro i; exact Com.noWrite_skip
  | cons v vs ih => intro i; exact ⟨trivial, ih _⟩

theorem storeSeq_noReads (a : String) : ∀ (l : List ℕ) (i : ℕ), ¬ (storeSeq a i l).reads := by
  intro l
  induction l with
  | nil => intro i; simp [storeSeq, Com.reads]
  | cons v vs ih => intro i; simp [storeSeq, Com.reads, ih]

/-- The function an array becomes after `storeSeq`. -/
def stored (i : ℕ) (l : List ℕ) (f : ℕ → ℕ) : ℕ → ℕ :=
  fun k => if i ≤ k ∧ k < i + l.length then l.getD (k - i) 0 else f k

theorem stored_cons (i v : ℕ) (vs : List ℕ) (f : ℕ → ℕ) :
    stored (i + 1) vs (fun k => if k = i then v else f k) = stored i (v :: vs) f := by
  funext k
  unfold stored
  beta_reduce
  by_cases hk : k = i
  · subst hk
    rw [if_neg (by omega), if_pos rfl, if_pos (by simp)]
    simp
  · by_cases h1 : i + 1 ≤ k
    · by_cases h2 : k < i + 1 + vs.length
      · rw [if_pos ⟨h1, h2⟩, if_pos ⟨by omega, by simp; omega⟩]
        have e : k - i = (k - (i + 1)) + 1 := by omega
        rw [e, List.getD_cons_succ]
      · rw [if_neg (by omega), if_neg hk, if_neg (by simp; omega)]
    · have : k < i := by omega
      rw [if_neg (by omega), if_neg hk, if_neg (by omega)]

/-- **Running `storeSeq`.**  From an array `arrOf n f`, `l.length` cells (from `i`) are overwritten. -/
theorem storeSeq_run {Bi : ℕ} (a : String) :
    ∀ (l : List ℕ) (i : ℕ) (σ : IEnv) (n : ℕ) (f : ℕ → ℕ), σ.arrs a = arrOf n f → i + l.length ≤ n →
      (∀ v ∈ l, v < Bi) → i + l.length < Bi →
      ∃ σ', Run Bi (storeSeq a i l) σ σ' (3 * l.length + 1) ∧ σ'.arrs a = arrOf n (stored i l f) ∧
        σ'.vars = σ.vars ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧ ∀ b, b ≠ a → σ'.arrs b = σ.arrs b := by
  intro l
  induction l with
  | nil =>
    intro i σ n f h _ _ _
    refine ⟨σ, Run.skip.mono (by simp), ?_, rfl, rfl, rfl, fun _ _ => rfl⟩
    rw [h]; congr 1
    funext k; simp [stored]
  | cons v vs ih =>
    intro i σ n f h hn hv hb
    have hvB : v < Bi := hv v (by simp)
    have hlen : i < (σ.arrs a).length := by rw [h]; simp; simp at hn; omega
    have hr1 : Run Bi (.store a (.lit i) (.lit v)) σ (σ.setArr a i v) 3 :=
      (Run.store (i := .lit i) (e := .lit v) (idx := i) (v := v) (evalB_lit (by simp at hb; omega))
        (evalB_lit hvB) hlen).mono (by simp)
    have h1 : (σ.setArr a i v).arrs a = arrOf n (fun k => if k = i then v else f k) := by
      simp only [arrs_setArr, if_true]; rw [h, set_arrOf]
    obtain ⟨σ', hr, ha', hv', hi', ho', hb'⟩ := ih (i + 1) (σ.setArr a i v) n _ h1
      (by simp at hn; omega) (fun w hw => hv w (List.mem_cons_of_mem _ hw)) (by simp at hb; omega)
    refine ⟨σ', (hr1.seq hr).mono (by simp; omega), ?_, hv', hi', ho', ?_⟩
    · rw [ha', stored_cons]
    · intro b hb2
      rw [hb' b hb2]; simp [arrs_setArr, hb2]

/-- The cells of the array that are loaded read back: if the array was zero, `stored` is the list. -/
theorem storeSeq_run0 {Bi : ℕ} (a : String) (l : List ℕ) (σ : IEnv) (n : ℕ)
    (h : σ.arrs a = List.replicate n 0) (hn : l.length ≤ n) (hv : ∀ v ∈ l, v < Bi) (hb : l.length < Bi) :
    ∃ σ', Run Bi (storeSeq a 0 l) σ σ' (3 * l.length + 1) ∧ σ'.arrs a = arrOf n (fun k => l.getD k 0) ∧
        σ'.vars = σ.vars ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧ ∀ b, b ≠ a → σ'.arrs b = σ.arrs b := by
  obtain ⟨σ', hr, ha, h1, h2, h3, h4⟩ := storeSeq_run (Bi := Bi) a l 0 σ n (fun _ => 0)
    (by rw [h, replicate_eq_arrOf]) (by omega) hv (by omega)
  refine ⟨σ', hr, ?_, h1, h2, h3, h4⟩
  rw [ha]
  congr 1
  funext k
  unfold stored
  by_cases hk : k < l.length
  · simp [hk]
  · have : l.getD k 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    simp [hk, this]

end Lax117284Proofs.Treewidth.Fun.VM.Ram
