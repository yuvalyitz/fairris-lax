import Lax117284Proofs.Treewidth.Fun.VMSimCases

/-!
# WP V1 (5): simulation of `ite`, `letE`, argument lists, calls; the main theorem `ev_sim`
-/

namespace Lax117284Proofs.Treewidth.Fun.VM

variable {P : Prog}

/-- `P` contains, for every function of the table, its code (followed by `ret`) at the address `ft f`; and
function ids are bounded by the code length (they are pushed as machine words). -/
def Prog.Real (P : Prog) (Δ : ℕ → Option Tm) : Prop :=
  ∀ f body, Δ f = some body → f ≤ P.len ∧ FitsAt P (P.ft f) (compile id body ++ [.ret])

theorem sim_iteT {ρ : List Val} {cnd t e : Tm} {n : ℕ} {v : Val} {c₁ c₂ : ℕ} (hn : n ≠ 0)
    (hc : SimEv P ρ cnd (.nat n) c₁) (ht : SimEv P ρ t v c₂) :
    SimEv P ρ (.ite cnd t e) v (c₁ + c₂ + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfc : FitsAt P s.pc (compile dep cnd) := hfit.append_left
  have hr1 := hfit.append_right
  have hjz := hr1.head
  have hr2 := hr1.tail
  have hft : FitsAt P (s.pc + (compile dep cnd).length + 1) (compile dep t) := hr2.append_left
  have hr3 := hr2.append_right
  have hjmp := hr3.head
  have hlen := hfit.1
  have e : s.pc + (compile dep cnd ++ (Instr.jz ((compile dep t).length + 1) ::
      (compile dep t ++ (Instr.jmp (compile dep e).length :: compile dep e)))).length =
      s.pc + (compile dep cnd).length + 1 + (compile dep t).length + 1 + (compile dep e).length := by
    simp; omega
  rw [e]
  simp only [List.length_append, List.length_cons] at hlen
  have hL := hcfg.len
  have hB := hcfg.heap
  have hstk := hcfg.stk
  have hret := hcfg.ret
  obtain ⟨n₁, hn₁, w₁, H₁, hs₁, hx₁, hr₁, hh₁⟩ := hc dep W s hfc henv (hcfg.sub (by omega))
  obtain ⟨rfl, hnB⟩ := hr₁.nat_inv
  have hbd := hs₁.bd_end
  have hstep := step_jz (P := P) (s := ⟨s.pc + (compile dep cnd).length, w₁ :: s.stk, s.ret, H₁⟩)
    hjz w₁ s.stk rfl
  simp only [if_neg hn] at hstep
  have hbd₂ : St.Bd W ⟨s.pc + (compile dep cnd).length + 1, s.stk, s.ret, H₁⟩ :=
    hbd.setStk (by omega) (fun x hx => hbd.stk x (List.mem_cons_of_mem _ hx)) (by omega)
  have hc₂ : Cfg P W ⟨s.pc + (compile dep cnd).length + 1, s.stk, s.ret, H₁⟩ c₂ :=
    ⟨hbd₂, hL, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
  obtain ⟨n₂, hn₂, w₂, H₂, hs₂, hx₂, hr₂, hh₂⟩ := ht dep W
    ⟨s.pc + (compile dep cnd).length + 1, s.stk, s.ret, H₁⟩ hft (henv.mono hx₁) hc₂
  dsimp only at hs₂ hh₂ hx₂
  have hstep2 := step_jmp (P := P) (s := ⟨s.pc + (compile dep cnd).length + 1 + (compile dep t).length,
    w₂ :: s.stk, s.ret, H₂⟩) hjmp
  have hbd₄ := hs₂.bd_end
  refine ⟨n₁ + (n₂ + 1 + 1), by omega, w₂, H₂,
    hs₁.trans (StepsB.step hbd hstep (hs₂.trans (StepsB.one hbd₄ hstep2 ?_))),
    hx₁.trans hx₂, hr₂, by omega⟩
  exact hbd₄.setPc (by omega)

theorem sim_iteF {ρ : List Val} {cnd t e : Tm} {v : Val} {c₁ c₂ : ℕ}
    (hc : SimEv P ρ cnd (.nat 0) c₁) (he : SimEv P ρ e v c₂) :
    SimEv P ρ (.ite cnd t e) v (c₁ + c₂ + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfc : FitsAt P s.pc (compile dep cnd) := hfit.append_left
  have hr1 := hfit.append_right
  have hjz := hr1.head
  have hr2 := hr1.tail
  have hr3 := hr2.append_right
  have hr4 := hr3.tail
  have hfe : FitsAt P (s.pc + (compile dep cnd).length + 1 + ((compile dep t).length + 1))
      (compile dep e) := by
    have := hr4
    rwa [show s.pc + (compile dep cnd).length + 1 + (compile dep t).length + 1 =
      s.pc + (compile dep cnd).length + 1 + ((compile dep t).length + 1) by omega] at this
  have hlen := hfit.1
  have e : s.pc + (compile dep cnd ++ (Instr.jz ((compile dep t).length + 1) ::
      (compile dep t ++ (Instr.jmp (compile dep e).length :: compile dep e)))).length =
      s.pc + (compile dep cnd).length + 1 + ((compile dep t).length + 1) + (compile dep e).length := by
    simp; omega
  rw [e]
  simp only [List.length_append, List.length_cons] at hlen
  have hL := hcfg.len
  have hB := hcfg.heap
  have hstk := hcfg.stk
  have hret := hcfg.ret
  obtain ⟨n₁, hn₁, w₁, H₁, hs₁, hx₁, hr₁, hh₁⟩ := hc dep W s hfc henv (hcfg.sub (by omega))
  obtain ⟨rfl, hnB⟩ := hr₁.nat_inv
  have hbd := hs₁.bd_end
  have hstep := step_jz (P := P) (s := ⟨s.pc + (compile dep cnd).length, 0 :: s.stk, s.ret, H₁⟩)
    hjz 0 s.stk rfl
  have hbd₂ : St.Bd W ⟨s.pc + (compile dep cnd).length + 1 + ((compile dep t).length + 1), s.stk, s.ret, H₁⟩ :=
    hbd.setStk (by omega) (fun x hx => hbd.stk x (List.mem_cons_of_mem _ hx)) (by omega)
  have hc₂ : Cfg P W ⟨s.pc + (compile dep cnd).length + 1 + ((compile dep t).length + 1), s.stk, s.ret, H₁⟩
      c₂ := ⟨hbd₂, hL, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
  obtain ⟨n₂, hn₂, w₂, H₂, hs₂, hx₂, hr₂, hh₂⟩ := he dep W
    ⟨s.pc + (compile dep cnd).length + 1 + ((compile dep t).length + 1), s.stk, s.ret, H₁⟩ hfe
    (henv.mono hx₁) hc₂
  dsimp only at hs₂ hh₂ hx₂
  refine ⟨n₁ + (n₂ + 1), by omega, w₂, H₂, hs₁.trans (StepsB.step hbd hstep hs₂), hx₁.trans hx₂, hr₂,
    by omega⟩

theorem sim_let {ρ : List Val} {a b : Tm} {u v : Val} {c₁ c₂ : ℕ} (ha : SimEv P ρ a u c₁)
    (hb : SimEv P (u :: ρ) b v c₂) : SimEv P ρ (.letE a b) v (c₁ + c₂ + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfa : FitsAt P s.pc (compile dep a) := hfit.append_left
  have hrest := hfit.append_right
  have hfb : FitsAt P (s.pc + (compile dep a).length) (compile (letDep dep) b) := hrest.append_left
  have hfi : FitsAt P (s.pc + (compile dep a).length + (compile (letDep dep) b).length) [Instr.slide] :=
    hrest.append_right
  have hlen := hfit.1
  have e : s.pc + (compile dep a ++ (compile (letDep dep) b ++ [Instr.slide])).length =
      s.pc + (compile dep a).length + (compile (letDep dep) b).length + 1 := by simp; omega
  rw [e]
  simp only [List.length_append, List.length_singleton] at hlen
  have hL := hcfg.len
  have hB := hcfg.heap
  have hstk := hcfg.stk
  obtain ⟨n₁, hn₁, w₁, H₁, hs₁, hx₁, hr₁, hh₁⟩ := ha dep W s hfa henv (hcfg.sub (by omega))
  have hc₂ : Cfg P W ⟨s.pc + (compile dep a).length, w₁ :: s.stk, s.ret, H₁⟩ c₂ :=
    hcfg.next (c₁ := c₁) (by omega) hs₁.bd_end hh₁ (by simp) (by simp)
  obtain ⟨n₂, hn₂, w₂, H₂, hs₂, hx₂, hr₂, hh₂⟩ := hb (letDep dep) W
    ⟨s.pc + (compile dep a).length, w₁ :: s.stk, s.ret, H₁⟩ hfb (Env.letE hr₁ (henv.mono hx₁)) hc₂
  dsimp only at hs₂ hh₂ hx₂
  have hstep := step_slide (P := P) (s := ⟨s.pc + (compile dep a).length + (compile (letDep dep) b).length,
    w₂ :: w₁ :: s.stk, s.ret, H₂⟩) hfi.head w₂ w₁ s.stk rfl
  have hbd := hs₂.bd_end
  refine ⟨n₁ + (n₂ + 1), by omega, w₂, H₂, hs₁.trans (hs₂.trans (StepsB.one hbd hstep ?_)),
    hx₁.trans hx₂, hr₂, by omega⟩
  refine hbd.setStk (by omega) ?_ (by simp; omega)
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hbd.stk x (by simp)
  · exact hbd.stk x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))

/-! ## argument lists -/

theorem sim_evl_nil {ρ : List Val} : SimEvL P ρ [] [] 0 := by
  intro dep W s hfit henv hcfg
  refine ⟨0, by omega, [], s.heap, ?_, HExt.refl _, .nil, by omega, rfl⟩
  simpa [compileArgs] using StepsB.refl hcfg.bd

theorem sim_evl_cons {ρ : List Val} {t : Tm} {ts : List Tm} {v : Val} {vs : List Val} {c₁ c₂ : ℕ}
    (hlen : ts.length ≤ c₂) (ht : SimEv P ρ t v c₁) (hts : SimEvL P ρ ts vs c₂) :
    SimEvL P ρ (t :: ts) (v :: vs) (c₁ + c₂) := by
  intro dep W s hfit henv hcfg
  simp only [compileArgs] at hfit ⊢
  have hfa : FitsAt P s.pc (compileArgs dep ts) := hfit.append_left
  have hfb : FitsAt P (s.pc + (compileArgs dep ts).length) (compile (shiftDep ts.length dep) t) :=
    hfit.append_right
  have hlen' := hfit.1
  have e : s.pc + (compileArgs dep ts ++ compile (shiftDep ts.length dep) t).length =
      s.pc + (compileArgs dep ts).length + (compile (shiftDep ts.length dep) t).length := by
    simp; omega
  rw [e]
  simp only [List.length_append] at hlen'
  have hL := hcfg.len
  have hB := hcfg.heap
  have hstk := hcfg.stk
  have hret := hcfg.ret
  obtain ⟨n₁, hn₁, ws, H₁, hs₁, hx₁, hr₁, hh₁, hwl⟩ := hts dep W s hfa henv (hcfg.sub (by omega))
  have hbd := hs₁.bd_end
  have hc₂ : Cfg P W ⟨s.pc + (compileArgs dep ts).length, ws ++ s.stk, s.ret, H₁⟩ c₁ :=
    ⟨hbd, hL, by dsimp only; omega, by simp; omega, by dsimp only; omega⟩
  have henv' : Env P.B H₁ (shiftDep ts.length dep) ρ (ws ++ s.stk) := by
    have := (henv.mono hx₁).shift ws
    rwa [hwl] at this
  obtain ⟨n₂, hn₂, w, H₂, hs₂, hx₂, hr₂, hh₂⟩ := ht (shiftDep ts.length dep) W
    ⟨s.pc + (compileArgs dep ts).length, ws ++ s.stk, s.ret, H₁⟩ hfb henv' hc₂
  dsimp only at hs₂ hh₂ hx₂
  refine ⟨n₁ + n₂, by omega, w :: ws, H₂, hs₁.trans hs₂, hx₁.trans hx₂,
    .cons hr₂ (hr₁.mono hx₂), by omega, by simp [hwl]⟩

/-! ## calls -/

/-- From the state right after the argument words and the function id were pushed, up to the return. -/
theorem callee_run {Δ : ℕ → Option Tm} (hreal : P.Real Δ) {f : ℕ} {body : Tm} {vs : List Val} {v : Val}
    {c₂ W : ℕ} (hΔ : Δ f = some body) (hbody : SimEv P vs body v c₂) {ws stk₀ : List ℕ}
    {ret₀ : List (ℕ × ℕ)} {H : List (ℕ × ℕ)} {pcc : ℕ}
    (hcode : P.code pcc = .call ws.length) (hrep : RepL P.B H ws vs)
    (hbd : St.Bd W ⟨pcc, f :: (ws ++ stk₀), ret₀, H⟩)
    (hL : P.len ≤ W) (hpc : pcc + 1 ≤ P.len) (hheap : P.B + H.length + c₂ ≤ W)
    (hstk : (ws ++ stk₀).length + 3 * c₂ ≤ W) (hret : ret₀.length + 1 + 3 * c₂ ≤ W) :
    ∃ n ≤ 3 * c₂ + 2, ∃ (w : ℕ) (H' : List (ℕ × ℕ)),
      StepsB P W n ⟨pcc, f :: (ws ++ stk₀), ret₀, H⟩ ⟨pcc + 1, w :: stk₀, ret₀, H'⟩ ∧ HExt H H' ∧
        Rep P.B H' w v ∧ H'.length ≤ H.length + c₂ := by
  obtain ⟨hfl, hfit⟩ := hreal f body hΔ
  have hfit' : FitsAt P (P.ft f) (compile id body) := hfit.append_left
  have hfret : FitsAt P (P.ft f + (compile id body).length) [Instr.ret] := hfit.append_right
  have hlen := hfit.1
  simp only [List.length_append, List.length_singleton] at hlen
  have hstep := step_call (P := P) (s := ⟨pcc, f :: (ws ++ stk₀), ret₀, H⟩) hcode f (ws ++ stk₀) rfl
  have hsub : (ws ++ stk₀).length - ws.length = stk₀.length := by simp
  simp only [hsub] at hstep
  have hws : ∀ x ∈ ws ++ stk₀, x ≤ W := fun x hx => hbd.stk x (List.mem_cons_of_mem _ hx)
  have hbd₃ : St.Bd W ⟨P.ft f, ws ++ stk₀, (pcc + 1, stk₀.length) :: ret₀, H⟩ := by
    refine ⟨by show P.ft f ≤ W; omega, by show (ws ++ stk₀).length ≤ W; omega, hws, by simp; omega, ?_, hbd.heapLen, hbd.heap⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨by omega, by simp at hstk; omega⟩
    · exact hbd.ret p hp
  have hc₃ : Cfg P W ⟨P.ft f, ws ++ stk₀, (pcc + 1, stk₀.length) :: ret₀, H⟩ c₂ :=
    ⟨hbd₃, hL, by dsimp only; omega, by dsimp only; omega, by simp; omega⟩
  obtain ⟨n₂, hn₂, w, H₂, hs₂, hx₂, hr₂, hh₂⟩ := hbody id W
    ⟨P.ft f, ws ++ stk₀, (pcc + 1, stk₀.length) :: ret₀, H⟩ hfit' (Env.of_repl hrep stk₀) hc₃
  dsimp only at hs₂ hh₂ hx₂
  have hbd₄ := hs₂.bd_end
  have hstep2 := step_ret (P := P) (s := ⟨P.ft f + (compile id body).length, w :: (ws ++ stk₀),
    (pcc + 1, stk₀.length) :: ret₀, H₂⟩) hfret.head w (ws ++ stk₀) (pcc + 1) stk₀.length ret₀ rfl rfl
  have hdrop : (ws ++ stk₀).drop ((ws ++ stk₀).length - stk₀.length) = stk₀ := by
    rw [List.length_append, Nat.add_sub_cancel]; exact List.drop_left ..
  simp only [hdrop] at hstep2
  refine ⟨(n₂ + 1) + 1, by omega, w, H₂, StepsB.step hbd hstep (hs₂.trans (StepsB.one hbd₄ hstep2 ?_)),
    hx₂, hr₂, by omega⟩
  refine ⟨by show pcc + 1 ≤ W; omega, ?_, ?_, ?_, ?_, hbd₄.heapLen, hbd₄.heap⟩
  · have := hbd₄.stkLen; simp at this ⊢; omega
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hbd₄.stk x (by simp)
    · exact hbd₄.stk x (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
  · have := hbd₄.retLen; simp at this ⊢; omega
  · intro p hp
    exact hbd₄.ret p (List.mem_cons_of_mem _ hp)

theorem sim_call {Δ : ℕ → Option Tm} (hreal : P.Real Δ) {ρ : List Val} {f : ℕ} {args : List Tm}
    {body : Tm} {vs : List Val} {v : Val} {c₁ c₂ : ℕ} (hlen : args.length ≤ c₁)
    (hargs : SimEvL P ρ args vs c₁) (hΔ : Δ f = some body) (hbody : SimEv P vs body v c₂) :
    SimEv P ρ (.call f args) v (c₁ + c₂ + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfa : FitsAt P s.pc (compileArgs dep args) := hfit.append_left
  have hr := hfit.append_right
  have hlit : P.code (s.pc + (compileArgs dep args).length) = .lit f := hr.head
  have hcall : P.code (s.pc + (compileArgs dep args).length + 1) = .call args.length := hr.tail.head
  have hlen' := hfit.1
  have e : s.pc + (compileArgs dep args ++ [Instr.lit f, Instr.call args.length]).length =
      s.pc + (compileArgs dep args).length + 1 + 1 := by simp; omega
  rw [e]
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen'
  have hL := hcfg.len
  have hB := hcfg.heap
  have hstk := hcfg.stk
  have hret := hcfg.ret
  have hfW : f ≤ W := Nat.le_trans (hreal f body hΔ).1 hL
  obtain ⟨n₁, hn₁, ws, H₁, hs₁, hx₁, hr₁, hh₁, hwl⟩ := hargs dep W s hfa henv (hcfg.sub (by omega))
  have hbd := hs₁.bd_end
  have hstep := step_lit (P := P) (s := ⟨s.pc + (compileArgs dep args).length, ws ++ s.stk, s.ret, H₁⟩) hlit
  have hbd₂ : St.Bd W ⟨s.pc + (compileArgs dep args).length + 1, f :: (ws ++ s.stk), s.ret, H₁⟩ :=
    hbd.setStk (by omega) (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hfW
      · exact hbd.stk x hx) (by simp; omega)
  obtain ⟨n₂, hn₂, w, H₂, hs₂, hx₂, hr₂, hh₂⟩ := callee_run hreal hΔ hbody
    (ws := ws) (stk₀ := s.stk) (ret₀ := s.ret) (H := H₁) (pcc := s.pc + (compileArgs dep args).length + 1)
    (by rw [hwl]; exact hcall) hr₁ hbd₂ hL (by omega) (by omega) (by simp; omega) (by omega)
  refine ⟨n₁ + (n₂ + 1), by omega, w, H₂, hs₁.trans (StepsB.step hbd hstep hs₂), hx₁.trans hx₂, hr₂,
    by omega⟩

theorem sim_callv {Δ : ℕ → Option Tm} (hreal : P.Real Δ) {ρ : List Val} {ft : Tm} {f : ℕ}
    {args : List Tm} {body : Tm} {vs : List Val} {v : Val} {c₀ c₁ c₂ : ℕ} (hlen : args.length ≤ c₁)
    (hf : SimEv P ρ ft (.nat f) c₀) (hargs : SimEvL P ρ args vs c₁) (hΔ : Δ f = some body)
    (hbody : SimEv P vs body v c₂) : SimEv P ρ (.callv ft args) v (c₀ + c₁ + c₂ + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfa : FitsAt P s.pc (compileArgs dep args) := hfit.append_left
  have hrest := hfit.append_right
  have hff : FitsAt P (s.pc + (compileArgs dep args).length) (compile (shiftDep args.length dep) ft) :=
    hrest.append_left
  have hcall : P.code (s.pc + (compileArgs dep args).length + (compile (shiftDep args.length dep) ft).length)
      = .call args.length := hrest.append_right.head
  have hlen' := hfit.1
  have e : s.pc + (compileArgs dep args ++ (compile (shiftDep args.length dep) ft ++
      [Instr.call args.length])).length =
      s.pc + (compileArgs dep args).length + (compile (shiftDep args.length dep) ft).length + 1 := by
    simp; omega
  rw [e]
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen'
  have hL := hcfg.len
  have hB := hcfg.heap
  have hstk := hcfg.stk
  have hret := hcfg.ret
  obtain ⟨n₁, hn₁, ws, H₁, hs₁, hx₁, hr₁, hh₁, hwl⟩ := hargs dep W s hfa henv (hcfg.sub (by omega))
  have hbd := hs₁.bd_end
  have hc₂ : Cfg P W ⟨s.pc + (compileArgs dep args).length, ws ++ s.stk, s.ret, H₁⟩ c₀ :=
    ⟨hbd, hL, by dsimp only; omega, by simp; omega, by dsimp only; omega⟩
  have henv' : Env P.B H₁ (shiftDep args.length dep) ρ (ws ++ s.stk) := by
    have := (henv.mono hx₁).shift ws
    rwa [hwl] at this
  obtain ⟨n₃, hn₃, wf, H₃, hs₃, hx₃, hr₃, hh₃⟩ := hf (shiftDep args.length dep) W
    ⟨s.pc + (compileArgs dep args).length, ws ++ s.stk, s.ret, H₁⟩ hff henv' hc₂
  dsimp only at hs₃ hh₃ hx₃
  obtain ⟨rfl, hfB⟩ := hr₃.nat_inv
  have hbd₃ := hs₃.bd_end
  obtain ⟨n₂, hn₂, w, H₂, hs₂, hx₂, hr₂, hh₂⟩ := callee_run hreal hΔ hbody
    (ws := ws) (stk₀ := s.stk) (ret₀ := s.ret) (H := H₃)
    (pcc := s.pc + (compileArgs dep args).length + (compile (shiftDep args.length dep) ft).length)
    (by rw [hwl]; exact hcall) (hr₁.mono hx₃) hbd₃ hL (by omega) (by omega) (by simp; omega)
    (by omega)
  refine ⟨n₁ + (n₃ + n₂), by omega, w, H₂, hs₁.trans (hs₃.trans hs₂), (hx₁.trans hx₃).trans hx₂, hr₂,
    by omega⟩

/-! ## the main theorem -/

theorem _root_.Lax117284Proofs.Treewidth.Fun.Ev.pos {Δ : ℕ → Option Tm} {B : ℕ} {ρ : List Val} {t : Tm} {v : Val} {c : ℕ}
    (h : Ev Δ B ρ t v c) : 1 ≤ c := by
  cases h <;> omega

theorem _root_.Lax117284Proofs.Treewidth.Fun.EvL.len_eq_le {Δ : ℕ → Option Tm} {B : ℕ} :
    ∀ (ts : List Tm) {ρ : List Val} {vs : List Val} {c : ℕ}, EvL Δ B ρ ts vs c →
      vs.length = ts.length ∧ ts.length ≤ c
  | [], _, _, _, h => by cases h; simp
  | t :: ts, _, _, _, h => by
    cases h with
    | cons h₁ h₂ =>
      have := h₁.pos
      have := EvL.len_eq_le ts h₂
      simp; omega

/-- **The simulation theorem**: every big-step derivation of the fragment is simulated by the machine. -/
theorem ev_sim {Δ : ℕ → Option Tm} (hB : 2 ≤ P.B) (hreal : P.Real Δ) {ρ : List Val} {t : Tm} {v : Val}
    {c : ℕ} (h : Ev Δ P.B ρ t v c) : SimEv P ρ t v c :=
  Ev.rec (motive_1 := fun ρ t v c _ => SimEv P ρ t v c)
    (motive_2 := fun ρ ts vs c _ => SimEvL P ρ ts vs c)
    (fun hn => sim_lit hn)
    (fun hi => sim_var hi)
    (fun _ _ hm iha ihb => bin_sim (op := (· + ·)) (fun dep => by simp [compile])
      (fun s x y r hc hs => step_add hc x y r hs) (fun _ _ => hm) iha ihb)
    (fun _ _ iha ihb => bin_sim (op := (· - ·)) (fun dep => by simp [compile])
      (fun s x y r hc hs => step_sub hc x y r hs) (fun h _ => by omega) iha ihb)
    (fun _ _ hm iha ihb => bin_sim (op := (· * ·)) (fun dep => by simp [compile])
      (fun s x y r hc hs => step_mul hc x y r hs) (fun _ _ => hm) iha ihb)
    (fun _ _ iha ihb => bin_sim (op := fun x y => if x < y then 1 else 0) (fun dep => by simp [compile])
      (fun s x y r hc hs => step_lt hc x y r hs) (fun _ _ => by split <;> omega) iha ihb)
    (fun _ _ iha ihb => bin_sim (op := fun x y => if x = y then 1 else 0) (fun dep => by simp [compile])
      (fun s x y r hc hs => step_eq hc x y r hs) (fun _ _ => by split <;> omega) iha ihb)
    (fun _ _ iha ihb => sim_cons iha ihb)
    (fun _ iha => sim_fst iha)
    (fun _ iha => sim_snd iha)
    (fun _ iha => sim_isNatT hB iha)
    (fun _ iha => sim_isNatF hB iha)
    (fun _ hn _ ihc iht => sim_iteT hn ihc iht)
    (fun _ _ ihc ihe => sim_iteF ihc ihe)
    (fun _ _ iha ihb => sim_let iha ihb)
    (fun hargs hΔ _ ihargs ihbody => sim_call hreal (hargs.len_eq_le).2 ihargs hΔ ihbody)
    (fun _ hargs hΔ _ ihf ihargs ihbody => sim_callv hreal (hargs.len_eq_le).2 ihf ihargs hΔ ihbody)
    sim_evl_nil
    (fun _ hts iht ihts => sim_evl_cons (hts.len_eq_le).2 iht ihts)
    h

end Lax117284Proofs.Treewidth.Fun.VM
