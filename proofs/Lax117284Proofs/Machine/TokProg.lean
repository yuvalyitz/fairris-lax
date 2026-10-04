import Lax117284Proofs.Machine.TokModel
import Lax808846Proofs.Transfer
import Lax808846Proofs.Tactic
import Mathlib.Data.List.GetD

/-! ### `Lax117284Proofs.Machine.TokScan` -/

section
/-!
Tokenizing a bit stream against a format, as a one-pass scan.

Phase `0` stands at a token boundary or inside the unary length of a number; phase `1`
reads the digits of a number; phase `2` has rejected. The scan is the model a machine
program is proved against.
-/

namespace Lax117284Proofs.Machine.TokScan

open Lax117284.Problems Lax434930.PolynomialTime Lax117284Proofs.Codes
open Lax117284Proofs.Machine.TokModel

set_option genSizeOfSpec false in
set_option genInjectivity false in
structure St where
  ph : ℕ
  L : ℕ
  val : ℕ
  pw : ℕ
  dg : List Bool
  toks : List Tok

def init : St := ⟨0, 0, 0, 1, [], []⟩

def dead (s : St) : St := { s with ph := 2 }

variable (E : Format)

def step (s : St) (b : Bool) : St :=
  match s.ph with
  | 0 =>
    match E s.toks with
    | .done => dead s
    | .bit => if s.L = 0 then { s with toks := s.toks ++ [.bit b] } else dead s
    | .num =>
      if b then { s with L := s.L + 1 }
      else if s.L = 0 then { s with toks := s.toks ++ [.num 0] }
      else { s with ph := 1, val := 0, pw := 1, dg := [] }
  | 1 =>
    if s.dg.length + 1 = s.L then
      (if b then ⟨0, 0, 0, 1, [], s.toks ++ [.num (s.val + s.pw)]⟩ else dead s)
    else { s with val := s.val + (if b then s.pw else 0), pw := 2 * s.pw, dg := s.dg ++ [b] }
  | _ => dead s

def run (s : St) (w : Word) : St := w.foldl (step E) s

@[simp] lemma run_nil (s : St) : run E s [] = s := rfl
@[simp] lemma run_cons (s : St) (b : Bool) (w : Word) :
    run E s (b :: w) = run E (step E s b) w := rfl
lemma run_append (s : St) (u v : Word) : run E s (u ++ v) = run E (run E s u) v := by
  simp [run, List.foldl_append]

/-- The scan has read a whole stream that the format accepts. -/
def Accepts (s : St) : Prop := s.ph = 0 ∧ s.L = 0 ∧ E s.toks = .done

/-- The tokens so far follow the format. -/
def Follows (ts : List Tok) : Prop :=
  ∀ k < ts.length, (ts.getD k (.bit false)).kind = E (ts.take k)

lemma follows_snoc {ts : List Tok} {t : Tok} (h : Follows E ts) (ht : t.kind = E ts) :
    Follows E (ts ++ [t]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_or_ge k ts.length with h1 | h1
  · rw [List.getD_append _ _ _ _ h1, List.take_append_of_le_length (by omega)]
    exact h k h1
  · have : k = ts.length := by omega
    subst this
    simp [ht]

/-- The bits consumed so far, read back off the state. -/
def consumed (s : St) : Word :=
  match s.ph with
  | 0 => code s.toks ++ List.replicate s.L true
  | 1 => code s.toks ++ (List.replicate s.L true ++ [false] ++ s.dg)
  | _ => []

structure Good (s : St) : Prop where
  fol : Follows E s.toks
  num : s.ph = 1 ∨ 0 < s.L → E s.toks = .num
  dig : s.ph = 1 → s.dg.length < s.L ∧ s.val = ofBits s.dg ∧ s.pw = 2 ^ s.dg.length
  ph : s.ph ≤ 1

lemma encodeNat_zero : encodeNat 0 = [false] := by simp [encodeNat]

lemma step_inv {s : St} {b : Bool} (hg : Good E s) (h : (step E s b).ph ≤ 1) :
    Good E (step E s b) ∧ consumed (step E s b) = consumed s ++ [b] := by
  obtain ⟨ph, L, val, pw, dg, toks⟩ := s
  have hfol := hg.fol
  have hnum := hg.num
  have hdig := hg.dig
  have hph := hg.ph
  clear hg
  simp only at hfol hnum hdig hph
  have hcases : ph = 0 ∨ ph = 1 := by omega
  rcases hcases with rfl | rfl
  · -- boundary, or the unary length
    rcases hE : E toks with _ | _ | _
    · -- a number is expected
      cases b
      · by_cases hL : L = 0
        · subst hL
          refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hE, consumed]
          · exact follows_snoc E hfol (by simp [Tok.kind, hE])
          · simp [code_append, code, Tok.code, encodeNat_zero]
        · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hE, hL, consumed]
          all_goals first
            | exact hfol
            | exact hE
            | exact ⟨by omega, by simp [ofBits]⟩
            | (simp [ofBits]; omega)
      · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hE, consumed]
        all_goals first
          | exact hfol
          | exact hE
          | simp [List.replicate_succ']
    · -- a raw bit is expected
      by_cases hL : L = 0
      · subst hL
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hE, consumed]
        · exact follows_snoc E hfol (by simp [Tok.kind, hE])
        · simp [code_append, code, Tok.code]
      · simp [step, hE, hL, dead] at h
    · simp [step, hE, dead] at h
  · -- the digits
    obtain ⟨hlt, hval, hpw⟩ := hdig rfl
    have hE := hnum (Or.inl rfl)
    by_cases hlast : dg.length + 1 = L
    · cases b
      · simp [step, hlast, dead] at h
      · have hv : val + pw = ofBits (dg ++ [true]) := by
          rw [ofBits_append, hval, hpw]; simp
        have henc := encodeNat_ofBits (dg ++ [true]) (Or.inr (by simp))
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hlast, consumed]
        · exact follows_snoc E hfol (by simp [Tok.kind, hE])
        · rw [code_append, hv]
          simp only [code, List.flatMap_cons, List.flatMap_nil, List.append_nil, Tok.code, henc,
            List.length_append, List.length_singleton, hlast]
          simp [List.append_assoc]
    · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hlast, consumed]
      all_goals first
        | exact hfol
        | exact hE
        | (refine ⟨by omega, ?_, by rw [hpw]; ring⟩
           rw [ofBits_append, hval, hpw])
        | simp [List.append_assoc]

lemma step_alive {s : St} {b : Bool} (h : (step E s b).ph ≤ 1) : s.ph ≤ 1 := by
  by_contra hc
  obtain ⟨ph, L, val, pw, dg, toks⟩ := s
  simp only at hc
  match ph, hc with
  | k + 2, _ => simp [step, dead] at h

lemma good_init : Good E init :=
  ⟨fun k hk => by simp [init] at hk, by simp [init], by simp [init], by simp [init]⟩

lemma run_inv (w : Word) (h : (run E init w).ph ≤ 1) :
    Good E (run E init w) ∧ consumed (run E init w) = w := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨good_init E, by simp [consumed, init, code]⟩
  | append_singleton u b ih =>
      rw [run_append] at h ⊢
      simp only [run_cons, run_nil] at h ⊢
      have ih' := ih (step_alive E h)
      obtain ⟨hg, hc⟩ := step_inv E ih'.1 h
      exact ⟨hg, by rw [hc, ih'.2]⟩

/-- **Soundness**: an accepting scan has read the code of a conforming stream. -/
theorem accept_sound {w : Word} (h : Accepts E (run E init w)) :
    code (run E init w).toks = w ∧ Conforms E (run E init w).toks := by
  obtain ⟨h0, hL, hE⟩ := h
  obtain ⟨hg, hc⟩ := run_inv E w (by omega)
  refine ⟨?_, hg.fol, hE⟩
  have h1 : consumed (run E init w) = code (run E init w).toks := by
    simp [consumed, h0, hL]
  rw [← h1, hc]

/-! ### Completeness -/

lemma bits_last {n : ℕ} (h : n ≠ 0) : n.bits.getLast? = some true := by
  induction n using Nat.binaryRec' with
  | zero => exact absurd rfl h
  | bit b n hb ih =>
    rw [Nat.bits_append_bit n b hb]
    by_cases hn : n = 0
    · subst hn; simp [hb rfl]
    · have := ih hn
      rcases hbits : n.bits with _ | ⟨c, t⟩
      · rw [hbits] at this; simp at this
      · rw [hbits] at this; simpa [List.getLast?_cons_cons] using this

/-- The boundary state after the tokens `toks`. -/
def bd (toks : List Tok) : St := ⟨0, 0, 0, 1, [], toks⟩

lemma run_ones (toks : List Tok) (hE : E toks = .num) (L k : ℕ) (w : Word) :
    run E ⟨0, L, 0, 1, [], toks⟩ (List.replicate k true ++ w) =
      run E ⟨0, L + k, 0, 1, [], toks⟩ w := by
  induction k generalizing L with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, run_cons]
    have : step E ⟨0, L, 0, 1, [], toks⟩ true = ⟨0, L + 1, 0, 1, [], toks⟩ := by
      simp [step, hE]
    rw [this, ih]; congr 2; omega

lemma run_digits (toks : List Tok) (L : ℕ) (ds : List Bool) (hlast : ds.getLast? = some true)
    (dg : List Bool) (hlen : dg.length + ds.length = L) (w : Word) :
    run E ⟨1, L, ofBits dg, 2 ^ dg.length, dg, toks⟩ (ds ++ w) =
      run E (bd (toks ++ [.num (ofBits (dg ++ ds))])) w := by
  induction ds generalizing dg with
  | nil => simp at hlast
  | cons b t ih =>
    rw [List.cons_append, run_cons]
    rcases t with _ | ⟨c, u⟩
    · have hb : b = true := by simpa using hlast
      subst hb
      have hL : dg.length + 1 = L := by simpa using hlen
      have : step E ⟨1, L, ofBits dg, 2 ^ dg.length, dg, toks⟩ true =
          bd (toks ++ [.num (ofBits dg + 2 ^ dg.length)]) := by
        simp [step, hL, bd]
      rw [this, ofBits_append]; simp
    · have hne : dg.length + 1 ≠ L := by simp at hlen; omega
      have : step E ⟨1, L, ofBits dg, 2 ^ dg.length, dg, toks⟩ b =
          ⟨1, L, ofBits (dg ++ [b]), 2 ^ (dg ++ [b]).length, dg ++ [b], toks⟩ := by
        simp [step, hne, ofBits_append, pow_succ, Nat.mul_comm]
      rw [this, ih (by simpa [List.getLast?_cons_cons] using hlast) (dg ++ [b])
        (by simp at hlen ⊢; omega)]
      simp

lemma run_tok (toks : List Tok) (t : Tok) (ht : t.kind = E toks) (w : Word) :
    run E (bd toks) (t.code ++ w) = run E (bd (toks ++ [t])) w := by
  cases t with
  | bit b =>
    have hE : E toks = .bit := ht.symm
    simp [Tok.code, step, bd, hE]
  | num v =>
    have hE : E toks = .num := ht.symm
    by_cases hv : v = 0
    · subst hv
      simp [Tok.code, encodeNat_zero, step, bd, hE]
    · have hlast := bits_last hv
      have hsz : v.bits.length ≠ 0 := by
        intro h0
        have : v.bits = [] := List.length_eq_zero_iff.mp h0
        rw [this] at hlast; simp at hlast
      simp only [Tok.code, encodeNat, List.append_assoc, bd]
      rw [run_ones E toks hE 0 v.bits.length, List.singleton_append, run_cons]
      have hstep : step E ⟨0, 0 + v.bits.length, 0, 1, [], toks⟩ false =
          ⟨1, v.bits.length, ofBits [], 2 ^ ([] : List Bool).length, [], toks⟩ := by
        simp [step, hE, hsz, ofBits]
      rw [hstep, run_digits E toks v.bits.length v.bits hlast [] (by simp)]
      simp [ofBits_bits, bd]

lemma run_toks (ts : List Tok) (toks : List Tok)
    (hf : ∀ k < ts.length, (ts.getD k (.bit false)).kind = E (toks ++ ts.take k)) (w : Word) :
    run E (bd toks) (code ts ++ w) = run E (bd (toks ++ ts)) w := by
  induction ts generalizing toks with
  | nil => simp [code]
  | cons t rest ih =>
    have h0 := hf 0 (by simp)
    simp only [List.getD_cons_zero, List.take_zero, List.append_nil] at h0
    have : code (t :: rest) ++ w = t.code ++ (code rest ++ w) := by simp [code]
    rw [this, run_tok E toks t h0, ih (toks ++ [t]) (fun k hk => by
      have := hf (k + 1) (by simpa using hk)
      simpa [List.append_assoc] using this)]
    simp

/-- **Completeness**: the code of a conforming stream is accepted, the stream recovered. -/
theorem accept_complete (ts : List Tok) (hc : Conforms E ts) :
    Accepts E (run E init (code ts)) ∧ (run E init (code ts)).toks = ts := by
  have h := run_toks E ts [] (fun k hk => by simpa using hc.1 k hk) []
  simp only [List.append_nil, List.nil_append, run_nil] at h
  have hi : init = bd [] := rfl
  rw [hi, h]
  exact ⟨⟨rfl, rfl, hc.2⟩, rfl⟩

end Lax117284Proofs.Machine.TokScan

end

/-! ### `Lax117284Proofs.Machine.ReadAll` -/

section
/-!
Reading a length-prefixed word into an array, as an IMP+ command with its specification.

The polynomial-time predicate hands a program its input preceded by its length. Every
program written against it begins the same way: read the length, then copy that many
entries into an array so that they can be read again. This file is that beginning, stated
once for any bound on the values.
-/

namespace Lax117284Proofs.Machine.ReadAll

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

def readBody : Com :=
  .seq (.read "rv") (.seq (.store "a" (V "rt") (V "rv")) (bump "rt"))

def readLoop : Com := .seq (.assign "rt" (.lit 0)) (.while (.lt (V "rt") (V "L")) readBody)

/-- Read the length, then the word. -/
def readAll : Com := .seq (.read "L") readLoop

variable {B : ℕ} {y : List ℕ}

def RInv (y : List ℕ) (σ : Env) : Prop :=
  σ.vars "L" = y.length ∧ σ.vars "rt" ≤ y.length ∧ (σ.arrs "a").length = y.length ∧
    (∀ i < σ.vars "rt", (σ.arrs "a").getD i 0 = y.getD i 0) ∧
    σ.inp = y.drop (σ.vars "rt") ∧ σ.out = []

theorem readBody_spec (hy : ∀ v ∈ y, v < B) (hL : y.length + 1 < B) :
    Spec B (fun σ => RInv y σ ∧ σ.vars "rt" < y.length) readBody
      (fun σ σ' => RInv y σ' ∧ σ'.vars "rt" = σ.vars "rt" + 1) 8 := by
  refine Spec.pre (P := fun σ => RInv y σ ∧ σ.vars "rt" < y.length ∧ σ.inp ≠ [] ∧
      σ.inp.headD 0 < B ∧ σ.vars "rt" < (σ.arrs "a").length) ?_ ?_
  · run_vcg
    · obtain ⟨hLv, hle, hlen, hcell, hinp, hout⟩ := ‹RInv y σ›
      have htlt := ‹σ.vars "rt" < y.length›
      have hidx : σ.vars "rt" < (σ.arrs "a").length := by rw [hlen]; exact htlt
      simp only [RInv]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp
      · exact hLv
      · exact htlt
      · exact hlen
      · intro i hi
        rcases Nat.lt_or_ge i (σ.vars "rt") with h | h
        · rw [List.getElem?_set_ne (by omega)]
          simpa [List.getD_eq_getElem?_getD] using hcell i h
        · have hie : i = σ.vars "rt" := by omega
          subst hie
          rw [hinp]
          simp [hidx, List.head?_drop]
      · rw [hinp, List.tail_drop]
      · exact hout
    · simp only [Env.setVar]
      exact ‹σ.inp.headD 0 < B›
  · rintro σ ⟨hI, ht⟩
    have hinp : σ.inp = y.drop (σ.vars "rt") := hI.2.2.2.2.1
    have hne : σ.inp ≠ [] := by
      rw [hinp]; intro hc
      have : (y.drop (σ.vars "rt")).length = 0 := by rw [hc]; rfl
      simp only [List.length_drop] at this; omega
    refine ⟨hI, ht, hne, ?_, by rw [hI.2.2.1]; exact ht⟩
    rcases hh : σ.inp with _ | ⟨u, rest⟩
    · exact absurd hh hne
    · have : u ∈ y.drop (σ.vars "rt") := by rw [← hinp, hh]; exact List.mem_cons_self
      exact hy u (List.mem_of_mem_drop this)

theorem readLoop_spec (hy : ∀ v ∈ y, v < B) (hL : y.length + 1 < B) :
    Spec B (fun σ => RInv y (σ.setVar "rt" 0)) readLoop
      (fun _ σ' => RInv y σ' ∧ σ'.vars "rt" = y.length) (12 * y.length + 6) :=
  Spec.forRangeZero "rt" "L" (RInv y) y.length 8 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1) (readBody_spec hy hL)

/-- **The word has been read**: its length is in `L` and its entries are in `a`. -/
theorem readAll_spec (hy : ∀ v ∈ y, v < B) (hL : y.length + 1 < B) :
    Spec B (fun σ => σ.inp = y.length :: y ∧ σ.out = [] ∧ (σ.arrs "a").length = y.length)
      readAll
      (fun _ σ' => σ'.vars "L" = y.length ∧ σ'.arrs "a" = y ∧ σ'.out = [] ∧ σ'.inp = [])
      (12 * y.length + 10) := by
  run_vcg [readLoop_spec hy hL]
  · obtain ⟨⟨hLv, -, hlen, hcell, hinp, hout⟩, ht⟩ := ‹RInv y _ ∧ _›
    refine ⟨hLv, ?_, hout, by rw [hinp, ht]; simp⟩
    refine List.ext_getElem hlen fun i h1 h2 => ?_
    have := hcell i (by rw [ht]; exact h2)
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some,
      Option.getD_some] at this
  all_goals simp_all [RInv]

end Lax117284Proofs.Machine.ReadAll

end

/-! ### `Lax117284Proofs.Machine.TokProg` -/

section
/-!
The tokenizer as an IMP+ loop. The format enters through one command, `nk`, which sets the
scalar `kind` to the code of what the format expects after the tokens read so far.
-/

namespace Lax117284Proofs.Machine.TokProg

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan

abbrev V (s : String) : Expr := .var s
abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev bump (s : String) : Com := .assign s (add (V s) (.lit 1))
abbrev set (s : String) (n : ℕ) : Com := .assign s (.lit n)

/-- The number a token is stored as. -/
def Tok.val : Tok → ℕ
  | .num v => v
  | .bit b => if b then 1 else 0

/-- The code of a kind. -/
def kcode : Kind → ℕ
  | .num => 0
  | .bit => 1
  | .done => 2

/-- The token array reflects the tokens read. -/
def TokRefl (toks : List Tok) (σ : Env) : Prop :=
  σ.vars "T" = toks.length ∧ (σ.arrs "TK").take toks.length = toks.map Tok.val

/-- The scalars and arrays the scan owns; the format's command must leave them alone. -/
def scanVars : List String := ["ph", "L", "val", "pw", "i", "T", "p", "c", "Ln"]

/-- What is asked of the format's command. -/
def NkSpec (B Bt : ℕ) (E : Format) (cap : ℕ) (nk : Com) (Knk : ℕ) : Prop :=
  ∀ toks : List Tok, Follows E toks → toks.length ≤ cap →
    Spec B (fun σ => TokRefl toks σ ∧ ∀ t ∈ toks, Tok.val t < Bt) nk
      (fun σ σ' => σ'.vars "kind" = kcode (E toks) ∧
        (∀ y ∈ scanVars, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        σ'.inp = σ.inp) Knk

variable (nk : Com)

/-- Append the token whose value is in `tv`, and ask the format what comes next. -/
def put : Com := .seq (.store "TK" (V "T") (V "tv")) (.seq (bump "T") nk)

variable {B Bt : ℕ} {E : Format} {cap Knk : ℕ}

lemma take_set_succ (l : List ℕ) (k v : ℕ) (hk : k < l.length) :
    (l.set k v).take (k + 1) = l.take k ++ [v] := by
  rw [List.take_succ, List.take_set_of_le (le_refl k)]
  simp [hk]

/-- **Appending a token.** -/
theorem put_spec (hnk : NkSpec B Bt E cap nk Knk) (toks : List Tok) (t : Tok)
    (hfol : Follows E (toks ++ [t])) (hcap : toks.length + 1 ≤ cap)
    (hvals : ∀ u ∈ toks ++ [t], Tok.val u < Bt) (hBt : Bt ≤ B) (hTB : toks.length + 1 < B) :
    Spec B (fun σ => TokRefl toks σ ∧ σ.vars "tv" = Tok.val t ∧
        toks.length < (σ.arrs "TK").length) (put nk)
      (fun σ σ' => TokRefl (toks ++ [t]) σ' ∧ σ'.vars "kind" = kcode (E (toks ++ [t])) ∧
        (∀ y ∈ scanVars, y ≠ "T" → σ'.vars y = σ.vars y) ∧
        (∀ a, a ≠ "TK" → σ'.arrs a = σ.arrs a) ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
        (σ'.arrs "TK").length = (σ.arrs "TK").length)
      (20 + Knk) := by
  intro σ ⟨⟨hT, hTK⟩, htv, hlen⟩
  have hv : Tok.val t < B := lt_of_lt_of_le (hvals t (by simp)) hBt
  have r1 : Run B (.store "TK" (V "T") (V "tv")) σ (σ.setArr "TK" (σ.vars "T") (σ.vars "tv"))
      (1 + (V "T").size + (V "tv").size) :=
    Run.store (evalB_var (by rw [hT]; omega)) (evalB_var (by rw [htv]; exact hv))
      (by rw [hT]; exact hlen)
  set σ1 := σ.setArr "TK" (σ.vars "T") (σ.vars "tv") with h1
  have r2 : Run B (bump "T") σ1 (σ1.setVar "T" (σ1.vars "T" + 1)) (1 + (add (V "T") (.lit 1)).size) :=
    Run.assign (evalB_bin (evalB_var (by simp [h1, Env.setArr, hT]; omega))
      (evalB_lit (by omega)) (by simp [h1, Env.setArr, hT]; omega))
  set σ2 := σ1.setVar "T" (σ1.vars "T" + 1) with h2
  have hrefl2 : TokRefl (toks ++ [t]) σ2 := by
    refine ⟨by simp [h2, h1, Env.setVar, Env.setArr, hT], ?_⟩
    simp only [h2, h1, Env.setVar, Env.setArr, List.length_append, List.length_singleton,
      if_true, hT, htv]
    rw [take_set_succ _ _ _ hlen, hTK]; simp
  obtain ⟨σ3, r3, hk, hfv, hfa, hfo, hfi⟩ := hnk (toks ++ [t]) hfol (by simpa using hcap) σ2
    ⟨hrefl2, hvals⟩
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by simp [Expr.size]; omega), ?_, hk, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨q1, q2⟩ := hrefl2
    exact ⟨by rw [hfv "T" (by simp [scanVars])]; exact q1, by rw [hfa]; exact q2⟩
  · intro y hy hne
    rw [hfv y hy]; simp [h2, h1, Env.setVar, Env.setArr, hne]
  · intro a ha
    rw [hfa]; simp [h2, h1, Env.setVar, Env.setArr, ha]
  · rw [hfo]; rfl
  · rw [hfi]; rfl
  · rw [hfa]; simp [h2, h1, Env.setVar, Env.setArr]

/-! ### The state of the scan, reflected -/

variable (E)

structure Refl (s : St) (σ : Env) : Prop where
  ph : σ.vars "ph" = s.ph
  L : σ.vars "L" = s.L
  val : σ.vars "val" = s.val
  pw : σ.vars "pw" = s.pw
  i : σ.vars "i" = s.dg.length
  tok : TokRefl s.toks σ
  kind : σ.vars "kind" = kcode (E s.toks)

/-- What a step leaves alone. -/
def Frame (σ σ' : Env) : Prop :=
  σ'.vars "p" = σ.vars "p" ∧ σ'.vars "Ln" = σ.vars "Ln" ∧ σ'.vars "c" = σ.vars "c" ∧
    (∀ b, b ≠ "TK" → σ'.arrs b = σ.arrs b) ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
    (σ'.arrs "TK").length = (σ.arrs "TK").length

variable {E}

lemma kcode_done {k : Kind} : kcode k = 2 ↔ k = .done := by cases k <;> simp [kcode]

/-- The values of the tokens of a state are small. -/
def Small (Bt : ℕ) (s : St) : Prop := ∀ t ∈ s.toks, Tok.val t < Bt

/-- **Appending a token, as a step of the scan**: if the model's step appends `t` and
changes nothing else, `tv := e; put` realises it. -/
theorem putStep_spec (hnk : NkSpec B Bt E cap nk Knk) (s s' : St) (t : Tok) (e : Expr)
    (hs' : s' = { s with toks := s.toks ++ [t] })
    (hfol : Follows E (s.toks ++ [t])) (hcap : s.toks.length + 1 ≤ cap)
    (hsmall : Small Bt s) (htB : Tok.val t < Bt) (hBt : Bt ≤ B) (hTB : s.toks.length + 1 < B) :
    Spec B (fun σ => Refl E s σ ∧ e.evalB B σ = some (Tok.val t) ∧
        s.toks.length < (σ.arrs "TK").length)
      (.seq (.assign "tv" e) (put nk))
      (fun σ σ' => Refl E s' σ' ∧ Frame σ σ') (1 + e.size + (20 + Knk)) := by
  intro σ ⟨hR, hev, hlen⟩
  have r1 : Run B (.assign "tv" e) σ (σ.setVar "tv" (Tok.val t)) (1 + e.size) := Run.assign hev
  obtain ⟨σ2, r2, hrefl, hk, hfv, hfa, hfo, hfi, hfl⟩ :=
    put_spec nk hnk s.toks t hfol hcap (by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hsmall u h
      · simp at h; rw [h]; exact htB) hBt hTB (σ.setVar "tv" (Tok.val t))
      ⟨⟨by simpa [Env.setVar] using hR.tok.1, by simpa [Env.setVar] using hR.tok.2⟩,
        by simp [Env.setVar], by simpa [Env.setVar] using hlen⟩
  have hv : ∀ y ∈ scanVars, y ≠ "T" → σ2.vars y = σ.vars y := fun y hy hne => by
    rw [hfv y hy hne]
    have : y ≠ "tv" := by
      intro h; rw [h] at hy; simp [scanVars] at hy
    simp [Env.setVar, this]
  refine ⟨σ2, r1.seq r2, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hv "ph" (by simp [scanVars]) (by decide), hR.ph, hs']
  · rw [hv "L" (by simp [scanVars]) (by decide), hR.L, hs']
  · rw [hv "val" (by simp [scanVars]) (by decide), hR.val, hs']
  · rw [hv "pw" (by simp [scanVars]) (by decide), hR.pw, hs']
  · rw [hv "i" (by simp [scanVars]) (by decide), hR.i, hs']
  · rw [hs']; exact hrefl
  · rw [hs']; exact hk
  · exact ⟨hv "p" (by simp [scanVars]) (by decide), hv "Ln" (by simp [scanVars]) (by decide),
      hv "c" (by simp [scanVars]) (by decide), fun b hb => by rw [hfa b hb]; rfl,
      by rw [hfo]; rfl, by rw [hfi]; rfl, by rw [hfl]; rfl⟩

/-- Back to a token boundary. -/
def reset : Com :=
  .seq (set "ph" 0) (.seq (set "L" 0) (.seq (set "val" 0) (.seq (set "pw" 1) (set "i" 0))))

theorem reset_spec (hB : 2 < B) :
    Spec B (fun _ => True) reset
      (fun σ σ' => σ'.vars "ph" = 0 ∧ σ'.vars "L" = 0 ∧ σ'.vars "val" = 0 ∧ σ'.vars "pw" = 1 ∧
        σ'.vars "i" = 0 ∧ (∀ y ∉ ["ph", "L", "val", "pw", "i"], σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp) 12 := by
  run_vcg
  · refine ⟨by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar], by simp [Env.setVar], fun y hy => ?_, by simp [Env.setVar],
      by simp [Env.setVar], by simp [Env.setVar]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2]
  all_goals omega

/-- **Completing a number.** -/
theorem putNum_spec (hnk : NkSpec B Bt E cap nk Knk) (s : St) (hB : 2 < B)
    (hfol : Follows E (s.toks ++ [.num (s.val + s.pw)])) (hcap : s.toks.length + 1 ≤ cap)
    (hsmall : Small Bt s) (hvB : s.val + s.pw < Bt) (hBt : Bt ≤ B) (hTB : s.toks.length + 1 < B) :
    Spec B (fun σ => Refl E s σ ∧ s.toks.length < (σ.arrs "TK").length)
      (.seq (.assign "tv" (add (V "val") (V "pw"))) (.seq reset (put nk)))
      (fun σ σ' => Refl E ⟨0, 0, 0, 1, [], s.toks ++ [.num (s.val + s.pw)]⟩ σ' ∧ Frame σ σ')
      (4 + (12 + (20 + Knk))) := by
  intro σ ⟨hR, hlen⟩
  have r1 : Run B (.assign "tv" (add (V "val") (V "pw"))) σ (σ.setVar "tv" (s.val + s.pw))
      (1 + (add (V "val") (V "pw")).size) := by
    have := Run.assign (B := B) (σ := σ) (x := "tv") (e := add (V "val") (V "pw"))
      (v := s.val + s.pw) (by
        have h := evalB_bin (op := .add) (evalB_var (x := "val") (σ := σ) (B := B)
          (by rw [hR.val]; omega)) (evalB_var (x := "pw") (σ := σ) (B := B) (by rw [hR.pw]; omega))
          (by simp [hR.val, hR.pw]; omega)
        simpa [hR.val, hR.pw] using h)
    exact this
  set σ1 := σ.setVar "tv" (s.val + s.pw) with h1
  obtain ⟨σ2, r2, q1, q2, q3, q4, q5, qv, qa, qo, qi⟩ := reset_spec (B := B) hB σ1 trivial
  obtain ⟨σ3, r3, hrefl, hk, hfv, hfa, hfo, hfi, hfl⟩ :=
    put_spec nk hnk s.toks (.num (s.val + s.pw)) hfol hcap (by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hsmall u h
      · simp at h; rw [h]; exact hvB) hBt hTB σ2
      ⟨⟨by rw [qv "T" (by decide)]; simpa [h1, Env.setVar] using hR.tok.1,
        by rw [qa]; simpa [h1, Env.setVar] using hR.tok.2⟩,
        by rw [qv "tv" (by decide)]; simp [h1, Env.setVar, Tok.val],
        by rw [qa]; simpa [h1, Env.setVar] using hlen⟩
  have hv : ∀ y ∈ scanVars, y ≠ "T" → σ3.vars y = σ2.vars y := hfv
  have hv0 : ∀ y, y ∉ ["ph", "L", "val", "pw", "i"] → y ≠ "tv" → σ2.vars y = σ.vars y :=
    fun y h1' h2' => by rw [qv y h1']; simp [h1, Env.setVar, h2']
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by simp [Expr.size]), ⟨?_, ?_, ?_, ?_, ?_, hrefl, hk⟩, ?_⟩
  · rw [hv "ph" (by simp [scanVars]) (by decide), q1]
  · rw [hv "L" (by simp [scanVars]) (by decide), q2]
  · rw [hv "val" (by simp [scanVars]) (by decide), q3]
  · rw [hv "pw" (by simp [scanVars]) (by decide), q4]
  · rw [hv "i" (by simp [scanVars]) (by decide), q5]; rfl
  · exact ⟨by rw [hv "p" (by simp [scanVars]) (by decide), hv0 "p" (by decide) (by decide)],
      by rw [hv "Ln" (by simp [scanVars]) (by decide), hv0 "Ln" (by decide) (by decide)],
      by rw [hv "c" (by simp [scanVars]) (by decide), hv0 "c" (by decide) (by decide)],
      fun b hb => by rw [hfa b hb, qa]; rfl, by rw [hfo, qo]; rfl, by rw [hfi, qi]; rfl,
      by rw [hfl, qa]; rfl⟩

/-! ### Conditionals whose outcome is known -/

theorem ite_true_spec {P : Env → Prop} {Q : Env → Env → Prop} {b : Cond} {c d : Com} {K : ℕ}
    (hb : ∀ σ, P σ → b.evalB B σ = some true) (h : Spec B P c Q K) :
    Spec B P (.ite b c d) Q (1 + b.size + K) := by
  intro σ hσ
  obtain ⟨σ', r, q⟩ := h σ hσ
  exact ⟨σ', Run.ite_true (hb σ hσ) r, q⟩

theorem ite_false_spec {P : Env → Prop} {Q : Env → Env → Prop} {b : Cond} {c d : Com} {K : ℕ}
    (hb : ∀ σ, P σ → b.evalB B σ = some false) (h : Spec B P d Q K) :
    Spec B P (.ite b c d) Q (1 + b.size + K) := by
  intro σ hσ
  obtain ⟨σ', r, q⟩ := h σ hσ
  exact ⟨σ', Run.ite_false (hb σ hσ) r, q⟩

lemma eval_eq_lit {σ : Env} {x : String} {n : ℕ} (hx : σ.vars x < B) (hn : n < B) :
    (Cond.eq (V x) (.lit n)).evalB B σ = some (σ.vars x == n) :=
  evalB_condEq (evalB_var hx) (evalB_lit hn)

/-! ### The steps that only touch scalars -/

variable (E)

/-- What the scan knows at the start of a step on the bit `b`. -/
structure Pre (s : St) (b : Bool) (σ : Env) : Prop where
  refl : Refl E s σ
  cbit : σ.vars "c" = if b then 1 else 0
  room : s.toks.length < (σ.arrs "TK").length

variable {E}

theorem dead_spec (s : St) (b : Bool) (hB : 2 < B) :
    Spec B (Pre E s b) (set "ph" 2) (fun σ σ' => Refl E (dead s) σ' ∧ Frame σ σ') 2 := by
  run_vcg
  · obtain ⟨hR, -, -⟩ := ‹Pre E s b σ›
    obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7⟩, h8⟩ := hR
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [Env.setVar, dead]
  all_goals omega

theorem ones_spec (s : St) (b : Bool) (hLB : s.L + 1 < B) :
    Spec B (Pre E s b) (bump "L") (fun σ σ' => Refl E { s with L := s.L + 1 } σ' ∧ Frame σ σ')
      4 := by
  run_vcg
  all_goals obtain ⟨hR, -, -⟩ := ‹Pre E s b σ›
  all_goals obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7⟩, h8⟩ := hR
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [Env.setVar]
  all_goals first | omega | (simp; omega)

def startDigits : Com :=
  .seq (set "ph" 1) (.seq (set "val" 0) (.seq (set "pw" 1) (set "i" 0)))

theorem startDigits_spec (s : St) (b : Bool) (hB : 2 < B) :
    Spec B (Pre E s b) startDigits
      (fun σ σ' => Refl E { s with ph := 1, val := 0, pw := 1, dg := [] } σ' ∧ Frame σ σ') 8 := by
  run_vcg
  all_goals obtain ⟨hR, -, -⟩ := ‹Pre E s b σ›
  all_goals obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7⟩, h8⟩ := hR
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [Env.setVar]
  all_goals omega

/-- The model state after one more digit. -/
def digSt (s : St) (b : Bool) : St :=
  ⟨s.ph, s.L, s.val + (if b then s.pw else 0), 2 * s.pw, s.dg ++ [b], s.toks⟩

/-- One more digit, not the last. -/
def digit : Com :=
  .seq (.ite (.eq (V "c") (.lit 0)) .skip (.assign "val" (add (V "val") (V "pw"))))
    (.seq (.assign "pw" (.bin .mul (.lit 2) (V "pw"))) (bump "i"))

theorem digit_spec (s : St) (b : Bool) (hB : 2 < B) (hv : s.val + s.pw < B) (hp : 2 * s.pw < B)
    (hi : s.dg.length + 1 < B) :
    Spec B (Pre E s b) digit
      (fun σ σ' => Refl E (digSt s b) σ' ∧ Frame σ σ') 16 := by
  run_vcg
  all_goals obtain ⟨hR, hc, -⟩ := ‹Pre E s b σ›
  all_goals obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7⟩, h8⟩ := hR
  all_goals try simp only [Env.setVar] at *
  all_goals try (
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      cases b <;> simp_all [Env.setVar, digSt])
  all_goals try simp
  all_goals (rw [h3, h4, h5] at * <;> skip)
  all_goals first
    | omega
    | (cases b <;> simp_all <;> omega)

lemma cond_lit_true {σ : Env} {x : String} {n : ℕ} (hx : σ.vars x = n) (hn : n < B) :
    (Cond.eq (V x) (.lit n)).evalB B σ = some true := by
  rw [eval_eq_lit (by rw [hx]; exact hn) hn, hx]; simp

lemma cond_lit_false {σ : Env} {x : String} {n : ℕ} (hx : σ.vars x ≠ n) (hxB : σ.vars x < B)
    (hn : n < B) : (Cond.eq (V x) (.lit n)).evalB B σ = some false := by
  rw [eval_eq_lit hxB hn]; simp [hx]

/-! ### One step of the scan -/

def dispatch : Com :=
  .ite (.eq (V "ph") (.lit 0))
    (.ite (.eq (V "kind") (.lit 2)) (set "ph" 2)
      (.ite (.eq (V "kind") (.lit 1))
        (.ite (.eq (V "L") (.lit 0)) (.seq (.assign "tv" (V "c")) (put nk)) (set "ph" 2))
        (.ite (.eq (V "c") (.lit 0))
          (.ite (.eq (V "L") (.lit 0)) (.seq (.assign "tv" (.lit 0)) (put nk)) startDigits)
          (bump "L"))))
    (.ite (.eq (V "ph") (.lit 1))
      (.ite (.eq (add (V "i") (.lit 1)) (V "L"))
        (.ite (.eq (V "c") (.lit 0)) (set "ph" 2)
          (.seq (.assign "tv" (add (V "val") (V "pw"))) (.seq reset (put nk))))
        digit)
      (set "ph" 2))

/-- The numeric facts a step needs. -/
structure StepB (B Bt cap : ℕ) (s : St) : Prop where
  hB : 4 < B
  hBt : Bt ≤ B
  bt : 2 ≤ Bt
  vt : s.val + s.pw < Bt
  ph : s.ph < B
  L : s.L + 1 < B
  i : s.dg.length + 1 < B
  v : s.val + s.pw < B
  p : 2 * s.pw < B
  T : s.toks.length + 1 < B
  cap : s.toks.length + 1 ≤ cap
  small : Small Bt s

theorem dispatch_spec (hnk : NkSpec B Bt E cap nk Knk) (s : St) (b : Bool) (hb : StepB B Bt cap s)
    (hfol' : s.ph ≤ 1 → Follows E s.toks) (hnum : s.ph = 1 → E s.toks = .num) :
    Spec B (Pre E s b) (dispatch nk) (fun σ σ' => Refl E (step E s b) σ' ∧ Frame σ σ')
      (80 + Knk) := by
  have hB := hb.hB
  have kc : ∀ σ, Pre E s b σ → σ.vars "kind" = kcode (E s.toks) := fun σ h => h.refl.kind
  have kB : kcode (E s.toks) < B := by cases E s.toks <;> simp [kcode] <;> omega
  have cB : ∀ σ, Pre E s b σ → σ.vars "c" < B := fun σ h => by
    rw [h.cbit]; cases b <;> simp <;> omega
  by_cases h0 : s.ph = 0
  · have hfol := hfol' (by omega)
    rcases hE : E s.toks with _ | _ | _
    · -- a number is expected
      cases b
      · by_cases hL : s.L = 0
        · have hst : step E s false = { s with toks := s.toks ++ [.num 0] } := by
            simp [step, h0, hE, hL]
          refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
            (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
                (by rw [kc σ h]; exact kB) (by omega))
              (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
                  (by rw [kc σ h]; exact kB) (by omega))
                (ite_true_spec (fun σ h => cond_lit_true (by rw [h.cbit]; rfl) (by omega))
                  (ite_true_spec (fun σ h => cond_lit_true (h.refl.L.trans hL) (by omega))
                    ((putStep_spec nk hnk s (step E s false) (.num 0) (.lit 0) hst
                      (follows_snoc E hfol (by simp [Tok.kind, hE])) hb.cap hb.small
                      (by have := hb.bt; simp [Tok.val]; omega) hb.hBt hb.T).pre
                      (fun σ h => ⟨h.refl, evalB_lit (by omega), h.room⟩)))))))
            (by simp [Cond.size, Expr.size]; omega)
        · have hst : step E s false = { s with ph := 1, val := 0, pw := 1, dg := [] } := by
            simp [step, h0, hE, hL]
          refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
            (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
                (by rw [kc σ h]; exact kB) (by omega))
              (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
                  (by rw [kc σ h]; exact kB) (by omega))
                (ite_true_spec (fun σ h => cond_lit_true (by rw [h.cbit]; rfl) (by omega))
                  (ite_false_spec (fun σ h => cond_lit_false (by rw [h.refl.L]; exact hL)
                      (by rw [h.refl.L]; have := hb.L; omega) (by omega))
                    ((startDigits_spec s false (by omega)).post
                      (fun σ σ' _ h => by rw [hst]; exact h)))))))
            (by simp [Cond.size, Expr.size, startDigits]; omega)
      · have hst : step E s true = { s with L := s.L + 1 } := by simp [step, h0, hE]
        refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
          (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
              (by rw [kc σ h]; exact kB) (by omega))
            (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
                (by rw [kc σ h]; exact kB) (by omega))
              (ite_false_spec (fun σ h => cond_lit_false (by rw [h.cbit]; decide)
                  (cB σ h) (by omega))
                ((ones_spec s true hb.L).post (fun σ σ' _ h => by rw [hst]; exact h))))))
          (by simp [Cond.size, Expr.size]; omega)
    · -- a raw bit is expected
      by_cases hL : s.L = 0
      · have hst : step E s b = { s with toks := s.toks ++ [.bit b] } := by
          simp [step, h0, hE, hL]
        refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
          (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
              (by rw [kc σ h]; exact kB) (by omega))
            (ite_true_spec (fun σ h => cond_lit_true (by rw [kc σ h, hE]; rfl) (by omega))
              (ite_true_spec (fun σ h => cond_lit_true (h.refl.L.trans hL) (by omega))
                ((putStep_spec nk hnk s (step E s b) (.bit b) (V "c") hst
                  (follows_snoc E hfol (by simp [Tok.kind, hE])) hb.cap hb.small
                  (by have := hb.bt; cases b <;> simp [Tok.val] <;> omega) hb.hBt hb.T).pre
                  (fun σ h => ⟨h.refl, by
                    have := evalB_var (B := B) (x := "c") (σ := σ) (cB σ h)
                    rw [this, h.cbit]; rfl, h.room⟩))))))
          (by simp [Cond.size, Expr.size]; omega)
      · have hst : step E s b = dead s := by simp [step, h0, hE, hL]
        refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
          (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
              (by rw [kc σ h]; exact kB) (by omega))
            (ite_true_spec (fun σ h => cond_lit_true (by rw [kc σ h, hE]; rfl) (by omega))
              (ite_false_spec (fun σ h => cond_lit_false (by rw [h.refl.L]; exact hL)
                  (by rw [h.refl.L]; have := hb.L; omega) (by omega))
                ((dead_spec s b (by omega)).post (fun σ σ' _ h => by rw [hst]; exact h))))))
          (by simp [Cond.size, Expr.size]; omega)
    · -- nothing more is expected
      have hst : step E s b = dead s := by simp [step, h0, hE]
      refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
        (ite_true_spec (fun σ h => cond_lit_true (by rw [kc σ h, hE]; rfl) (by omega))
          ((dead_spec s b (by omega)).post (fun σ σ' _ h => by rw [hst]; exact h))))
        (by simp [Cond.size, Expr.size]; omega)
  · have hph0 : ∀ σ, Pre E s b σ → (Cond.eq (V "ph") (.lit 0)).evalB B σ = some false :=
      fun σ h => cond_lit_false (by rw [h.refl.ph]; exact h0) (by rw [h.refl.ph]; exact hb.ph)
        (by omega)
    by_cases h1 : s.ph = 1
    · have hfol := hfol' (by omega)
      have hE := hnum h1
      have hcond : ∀ σ, Pre E s b σ →
          (Cond.eq (add (V "i") (.lit 1)) (V "L")).evalB B σ =
            some (decide (s.dg.length + 1 = s.L)) := fun σ h => by
        have e1 := evalB_bin (op := .add) (evalB_var (x := "i") (σ := σ) (B := B)
          (by rw [h.refl.i]; have := hb.i; omega)) (evalB_lit (B := B) (σ := σ) (n := 1) (by omega))
          (by simp [h.refl.i]; exact hb.i)
        have e2 := evalB_var (B := B) (x := "L") (σ := σ) (by rw [h.refl.L]; have := hb.L; omega)
        rw [evalB_condEq e1 e2]
        simp only [Bop.apply_add, h.refl.i, h.refl.L]
        congr 1
      by_cases hlast : s.dg.length + 1 = s.L
      · cases b
        · have hst : step E s false = dead s := by simp [step, h1, hlast]
          refine Spec.mono (ite_false_spec hph0
            (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h1) (by omega))
              (ite_true_spec (fun σ h => by rw [hcond σ h]; simp [hlast])
                (ite_true_spec (fun σ h => cond_lit_true (by rw [h.cbit]; rfl) (by omega))
                  ((dead_spec s false (by omega)).post (fun σ σ' _ h => by rw [hst]; exact h))))))
            (by simp [Cond.size, Expr.size]; omega)
        · have hst : step E s true = ⟨0, 0, 0, 1, [], s.toks ++ [.num (s.val + s.pw)]⟩ := by
            simp [step, h1, hlast]
          refine Spec.mono (ite_false_spec hph0
            (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h1) (by omega))
              (ite_true_spec (fun σ h => by rw [hcond σ h]; simp [hlast])
                (ite_false_spec (fun σ h => cond_lit_false (by rw [h.cbit]; decide) (cB σ h)
                    (by omega))
                  (((putNum_spec nk hnk s (by omega)
                    (follows_snoc E hfol (by simp [Tok.kind, hE])) hb.cap hb.small hb.vt hb.hBt hb.T).pre
                    (fun σ h => ⟨h.refl, h.room⟩)).post
                    (fun σ σ' _ h => by rw [hst]; exact h))))))
            (by simp [Cond.size, Expr.size, reset]; omega)
      · have hst : step E s b = digSt s b := by simp [step, h1, hlast, digSt]
        refine Spec.mono (ite_false_spec hph0
          (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h1) (by omega))
            (ite_false_spec (fun σ h => by rw [hcond σ h]; simp [hlast])
              ((digit_spec s b (by omega) hb.v hb.p hb.i).post
                (fun σ σ' _ h => by rw [hst]; exact h)))))
          (by simp [Cond.size, Expr.size]; omega)
    · have hst : step E s b = dead s := by
        obtain ⟨ph, L, val, pw, dg, toks⟩ := s
        simp only at h0 h1
        match ph, h0, h1 with
        | k + 2, _, _ => simp [step]
      refine Spec.mono (ite_false_spec hph0
        (ite_false_spec (fun σ h => cond_lit_false (by rw [h.refl.ph]; exact h1)
            (by rw [h.refl.ph]; exact hb.ph) (by omega))
          ((dead_spec s b (by omega)).post (fun σ σ' _ h => by rw [hst]; exact h))))
        (by simp [Cond.size, Expr.size]; omega)

end Lax117284Proofs.Machine.TokProg

end
