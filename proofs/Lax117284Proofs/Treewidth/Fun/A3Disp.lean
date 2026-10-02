import Lax117284Proofs.Treewidth.Fun.A3Defs
import Lax117284Proofs.Treewidth.Fun.Kit

/-!
# WP A3 (2): the dispatcher term

The table `Δ` delivered by `DecompRun` is abstract (it need not contain the library), so the dispatcher brings its own `take`, `drop`
at fresh ids (`tk`, `dr`), copies of `Lib1.takeTm/dropTm` with the recursive id replaced.

`dispTm tk dr mn` (environment `[x]`):

    n := x[0];  m := n·n + 1;  r := drop m x   (= k :: l :: D);
    if k < l then mn (take (m+1) x) else 1 :: D          (D = tail (tail r))
-/

namespace Lax117284Proofs.Treewidth.Fun.A3

open Lax117284Proofs.Treewidth.Fun ToVal

abbrev V (i : ℕ) : Tm := .var i

def takeTmAt (f : ℕ) : Tm :=
  .ite (.isNat (V 1)) (V 1)
    (.ite (.eq (V 0) (.lit 0)) (.lit 0) (.cons (.fst (V 1)) (.call f [.sub (V 0) (.lit 1), .snd (V 1)])))

def dropTmAt (f : ℕ) : Tm :=
  .ite (.isNat (V 1)) (V 1)
    (.ite (.eq (V 0) (.lit 0)) (V 1) (.call f [.sub (V 0) (.lit 1), .snd (V 1)]))

def dispTm (tk dr mn : ℕ) : Tm :=
  .letE (.fst (V 0))
    (.letE (.add (.mul (V 0) (V 0)) (.lit 1))
      (.letE (.call dr [V 0, V 2])
        (.ite (.lt (.fst (V 0)) (.fst (.snd (V 0))))
          (.call mn [.call tk [.add (V 1) (.lit 1), V 3]])
          (.cons (.lit 1) (.snd (.snd (V 0)))))))

section runs
variable {Δ' : ℕ → Option Tm} {B : ℕ}

theorem takeAt_runs {f : ℕ} (hf : Δ' f = some (takeTmAt f)) (n : ℕ) (xs : List ℕ) (hB : 1 < B) :
    Runs Δ' B f [toVal n, toVal xs] (toVal (xs.take n)) (20 * min n xs.length + 12) := by
  induction xs generalizing n with
  | nil =>
    refine Runs.mk hf ?_
    ev_start
    · ev_run
    · simp
  | cons a xs ih =>
    refine Runs.mk hf ?_
    cases n with
    | zero =>
      ev_start
      · ev_run
      · simp
    | succ n =>
      have ih := ih n
      ev_start
      · ev_run
      · simp; omega

theorem dropAt_runs {f : ℕ} (hf : Δ' f = some (dropTmAt f)) (n : ℕ) (xs : List ℕ) (hB : 1 < B) :
    Runs Δ' B f [toVal n, toVal xs] (toVal (xs.drop n)) (20 * min n xs.length + 12) := by
  induction xs generalizing n with
  | nil =>
    refine Runs.mk hf ?_
    ev_start
    · ev_run
    · simp
  | cons a xs ih =>
    refine Runs.mk hf ?_
    cases n with
    | zero =>
      ev_start
      · ev_run
      · simp
    | succ n =>
      have ih := ih n
      ev_start
      · ev_run
      · simp; omega

theorem drop_two (x : List ℕ) (m : ℕ) (h : m + 2 ≤ x.length) :
    x.drop m = x.getD m 0 :: x.getD (m + 1) 0 :: x.drop (m + 2) := by
  have h1 : m < x.length := by omega
  have h2 : m + 1 < x.length := by omega
  rw [List.drop_eq_getElem_cons h1, List.drop_eq_getElem_cons h2]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]

variable {tk dr mn d : ℕ}

/-- **The dispatcher, case `l ≤ k`.** -/
theorem disp_runs_true (hd : Δ' d = some (dispTm tk dr mn)) (hdr : Δ' dr = some (dropTmAt dr)) (n : ℕ) (xs : List ℕ)
    (hlen : n * n + 3 ≤ (n :: xs).length) (hB : n * n + 2 < B)
    (hle : (n :: xs).getD (n * n + 2) 0 ≤ (n :: xs).getD (n * n + 1) 0) :
    Runs Δ' B d [toVal (n :: xs)] (toVal (1 :: (n :: xs).drop (n * n + 3))) (20 * (n :: xs).length + 60) := by
  have hdrop := dropAt_runs (B := B) hdr (n * n + 1) (n :: xs) (by omega)
  rw [drop_two (n :: xs) (n * n + 1) (by omega)] at hdrop
  have hnot : ¬ (n :: xs).getD (n * n + 1) 0 < (n :: xs).getD (n * n + 1 + 1) 0 := by
    have : n * n + 1 + 1 = n * n + 2 := by ring
    rw [this]; omega
  have e3 : n * n + 1 + 2 = n * n + 3 := by ring
  rw [e3] at hdrop
  refine Runs.mk hd ?_
  ev_start
  · ev_run
    · ev_call hdrop
      ev_run
    apply EvLe.iteF
    case hc =>
      apply EvLe.lt
      case ha => ev_sub
      case hb => ev_sub
      case hv => rw [if_neg hnot]
    case hn => rfl
    case he => ev_run
  · omega

/-- **The dispatcher, case `k < l`.** -/
theorem disp_runs_false (hd : Δ' d = some (dispTm tk dr mn)) (hdr : Δ' dr = some (dropTmAt dr))
    (htk : Δ' tk = some (takeTmAt tk)) (n : ℕ) (xs : List ℕ)
    (hlen : n * n + 3 ≤ (n :: xs).length) (hB : n * n + 2 < B)
    (hlt : (n :: xs).getD (n * n + 1) 0 < (n :: xs).getD (n * n + 2) 0) {v : Val} {cm : ℕ}
    (hmain : Runs Δ' B mn [toVal ((n :: xs).take (n * n + 1 + 1))] v cm) :
    Runs Δ' B d [toVal (n :: xs)] v (cm + 40 * (n :: xs).length + 100) := by
  have hdrop := dropAt_runs (B := B) hdr (n * n + 1) (n :: xs) (by omega)
  rw [drop_two (n :: xs) (n * n + 1) (by omega)] at hdrop
  have htake := takeAt_runs (B := B) htk (n * n + 1 + 1) (n :: xs) (by omega)
  have hlt' : (n :: xs).getD (n * n + 1) 0 < (n :: xs).getD (n * n + 1 + 1) 0 := hlt
  refine Runs.mk hd ?_
  ev_start
  · ev_run
    · ev_call hdrop
      ev_run
    apply EvLe.iteT
    case hc =>
      apply EvLe.lt
      case ha => ev_sub
      case hb => ev_sub
      case hv => rw [if_pos hlt']
    case hn => simp
    case ht =>
      ev_run
  · have := min_le_right (n * n + 1) (n :: xs).length
    have := min_le_right (n * n + 1 + 1) (n :: xs).length
    omega

end runs

end Lax117284Proofs.Treewidth.Fun.A3
