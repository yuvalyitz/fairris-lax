import Lax808846Proofs.Transfer

/-!
A machine program that knows how long its input is.

IMP+ has no way to ask how long the input tape is: a `read` from an exhausted tape is stuck, and
the concept's words are *arbitrary* lists (a table shorter than the header claims reads as zeros).
The machine, though, has `inputLength`. So the machine program here is one instruction longer than
the compiled IMP+ one: `inputLength` into the cell of the scalar `"len"`, then the compiled code,
laid out at address `1`, then `halt`. The IMP+ program is proved against the environment in which
`"len"` already holds the input length; `wrap_runsTo` is the simulation theorem for that entry
state, obtained from `compile_correct` (which starts from *any* state representing the
environment, with the code laid out at the program counter).
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Simulation
open Lax808846Proofs.Machine

variable {x : List ℕ}

/-- The machine program: the input length into `"len"`, the compiled code, `halt`. -/
def wrapProgram (L : Layout) (c : Com) : Program :=
  Instr.inputLength (L.varAddr "len") :: (compile L c 1 ++ [Instr.halt])

/-- The environment the IMP+ program starts in: all zero, arrays as declared, and `"len"` holding
the length of the input. -/
def lenEnv (ext : String → ℕ) (x : List ℕ) : Env := (initEnv ext x).setVar "len" x.length

/-- The machine state after the first instruction. -/
def wrapState (L : Layout) (w : ℕ) (x : List ℕ) : State :=
  ⟨1, setCell w (initState x).mem (L.varAddr "len") x.length, x, x, []⟩

theorem wrap_step (L : Layout) (c : Com) (w : ℕ) (x : List ℕ) :
    run w (wrapProgram L c) 1 (initState x) = some (wrapState L w x) := by
  rw [run_one (ins := Instr.inputLength (L.varAddr "len")) (by simp [wrapProgram, initState]),
    effect_inputLength]
  rfl

theorem represents_wrapState {L : Layout} {B w : ℕ} (hfit : L.FitsWords B w)
    (hlen : "len" ∈ L.scalars) (hxB : x.length < B) (ext : String → ℕ) :
    Represents L (lenEnv ext x) (wrapState L w x) where
  vars y hy := by
    have hyw := L.varAddr_lt_two_pow hfit hy
    have hlw := L.varAddr_lt_two_pow hfit hlen
    have hxw : x.length < 2 ^ w := lt_of_lt_of_le hxB hfit.bound
    show setCell w (initState x).mem (L.varAddr "len") x.length (L.varAddr y) =
      (lenEnv ext x).vars y
    by_cases hyl : y = "len"
    · subst hyl
      rw [setCell_self _ hlw hxw]
      simp [lenEnv]
    · rw [setCell_of_ne _ _ hlw (fun h => hyl (varAddr_inj L hy hlen h))]
      simp [lenEnv, hyl, initState, initEnv]
  arrs a ha i hi := by
    have hlw := L.varAddr_lt_two_pow hfit hlen
    show setCell w (initState x).mem (L.varAddr "len") x.length (L.arrAddr a i) =
      ((lenEnv ext x).arrs a).getD i 0
    rw [setCell_of_ne _ _ hlw (fun h => varAddr_ne_arrAddr L hlen (a := a) i h.symm)]
    have : (lenEnv ext x).arrs a = List.replicate (ext a) 0 := rfl
    rw [this]
    show (0 : ℕ) = _
    rw [List.getD_eq_getElem?_getD]
    rcases h : (List.replicate (ext a) (0 : ℕ))[i]? with _ | u
    · rfl
    · have := List.mem_of_getElem? h
      simp only [List.mem_replicate] at this
      rw [this.2]; rfl
  inp := rfl
  out := rfl

theorem wrap_fits (L : Layout) (c : Com) :
    Fits (wrapProgram L c) 1 (compile L c 1) := by
  intro i hi
  show (Instr.inputLength (L.varAddr "len") :: (compile L c 1 ++ [Instr.halt]))[1 + i]? = _
  rw [Nat.add_comm, List.getElem?_cons_succ, List.getElem?_append_left hi]

/-- **The simulation theorem for the wrapped program.** -/
theorem wrap_runsTo {L : Layout} {B w : ℕ} {c : Com} {ext : String → ℕ} {x : List ℕ}
    {σ' : Env} {k : ℕ} (hfit : L.FitsWords B w) (hok : Com.Ok L c)
    (hlen : "len" ∈ L.scalars) (hx : ∀ v ∈ x, v < B) (hxl : x.length < B)
    (hbs : BigStepB B c (lenEnv ext x) σ' k) :
    ∃ t ≤ L.const * k + 2, RunsTo w (wrapProgram L c) x σ'.out t := by
  have hinp : (lenEnv ext x).InpBounded B := fun v hv => hx v hv
  obtain ⟨t, s', ht, hr, hpc, hrep⟩ :=
    compile_correct hfit hbs hok hinp 1 (wrapState L w x) rfl
      (represents_wrapState hfit hlen hxl ext) (wrap_fits L c)
  have hhalt : (wrapProgram L c)[s'.pc]? = some Instr.halt := by
    rw [hpc, wrapProgram, Nat.add_comm 1, List.getElem?_cons_succ, ← compile_length L c 1,
      List.getElem?_append_right (by omega)]
    simp
  refine ⟨1 + t + 1, by omega, 1 + t, s', run_trans (wrap_step L c w x) hr, ?_, ?_, ?_⟩
  · rw [step_eq, hhalt]; rfl
  · rw [← hrep.out]
  · rw [terminalCost_of_getElem? hhalt]

end Lax117284Proofs.Bipartite.Ram2
