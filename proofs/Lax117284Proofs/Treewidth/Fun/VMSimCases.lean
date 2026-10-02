import Lax117284Proofs.Treewidth.Fun.VMSim

/-!
# WP V1 (4): simulation, the cases other than calls
-/

namespace Lax117284Proofs.Treewidth.Fun.VM

variable {P : Prog}

theorem Cfg.nextL {W : ℕ} {s s₁ : St} {c c₁ c₂ : ℕ} (h : Cfg P W s c) (hc : c₁ + c₂ ≤ c)
    (hb : s₁.Bd W) (hheap : s₁.heap.length ≤ s.heap.length + c₁)
    (hstk : s₁.stk.length ≤ s.stk.length + c₁) (hret : s₁.ret.length ≤ s.ret.length) :
    Cfg P W s₁ c₂ :=
  ⟨hb, h.len, by have := h.heap; omega, by have := h.stk; omega, by have := h.ret; omega⟩

theorem sim_lit {ρ : List Val} {n : ℕ} (hn : n < P.B) : SimEv P ρ (.lit n) (.nat n) 1 := by
  intro dep W s hfit henv hcfg
  have e : (compile dep (.lit n)).length = 1 := by simp [compile]
  have hfit' : FitsAt P s.pc [Instr.lit n] := by simpa [compile] using hfit
  have hlen : s.pc + 1 ≤ P.len := by simpa using hfit'.1
  have hB := hcfg.heap
  have hstk := hcfg.stk
  have hL := hcfg.len
  rw [e]
  refine ⟨1, by omega, n, s.heap, StepsB.one hcfg.bd (step_lit hfit'.head) ?_, HExt.refl _, .nat hn,
    by omega⟩
  exact hcfg.bd.cons (by omega) (by omega) (by omega)

theorem sim_var {ρ : List Val} {i : ℕ} {v : Val} (h : ρ[i]? = some v) : SimEv P ρ (.var i) v 1 := by
  intro dep W s hfit henv hcfg
  have e : (compile dep (.var i)).length = 1 := by simp [compile]
  have hfit' : FitsAt P s.pc [Instr.var (dep i)] := by simpa [compile] using hfit
  have hlen : s.pc + 1 ≤ P.len := by simpa using hfit'.1
  have hstk := hcfg.stk
  have hL := hcfg.len
  obtain ⟨w, hw, hr⟩ := henv i v h
  have hwW : w ≤ W := hcfg.bd.stk w (List.mem_of_getElem? hw)
  rw [e]
  refine ⟨1, by omega, w, s.heap, StepsB.one hcfg.bd (step_var hfit'.head hw) ?_, HExt.refl _, hr,
    by omega⟩
  exact hcfg.bd.cons (by omega) hwW (by omega)

theorem bin_sim {ρ : List Val} {a b t : Tm} {ins : Instr} {op : ℕ → ℕ → ℕ} {m n c₁ c₂ : ℕ}
    (hcode : ∀ dep, compile dep t = compile dep a ++ (compile (shiftDep 1 dep) b ++ [ins]))
    (hins : ∀ (s : St) (x y : ℕ) (r : List ℕ), P.code s.pc = ins → s.stk = y :: x :: r →
      P.step s = some ⟨s.pc + 1, op x y :: r, s.ret, s.heap⟩)
    (hres : m < P.B → n < P.B → op m n < P.B)
    (ha : SimEv P ρ a (.nat m) c₁) (hb : SimEv P ρ b (.nat n) c₂) :
    SimEv P ρ t (.nat (op m n)) (c₁ + c₂ + 1) := by
  intro dep W s hfit henv hcfg
  rw [hcode] at hfit ⊢
  have hfa : FitsAt P s.pc (compile dep a) := hfit.append_left
  have hrest := hfit.append_right
  have hfb : FitsAt P (s.pc + (compile dep a).length) (compile (shiftDep 1 dep) b) := hrest.append_left
  have hfi : FitsAt P (s.pc + (compile dep a).length + (compile (shiftDep 1 dep) b).length) [ins] :=
    hrest.append_right
  have hlen := hfit.1
  have e : s.pc + (compile dep a ++ (compile (shiftDep 1 dep) b ++ [ins])).length =
      s.pc + (compile dep a).length + (compile (shiftDep 1 dep) b).length + 1 := by simp; omega
  rw [e]
  simp only [List.length_append, List.length_singleton] at hlen
  have hL := hcfg.len
  have hB := hcfg.heap
  have hstk := hcfg.stk
  obtain ⟨n₁, hn₁, w₁, H₁, hs₁, hx₁, hr₁, hh₁⟩ := ha dep W s hfa henv (hcfg.sub (by omega))
  have hc₂ : Cfg P W ⟨s.pc + (compile dep a).length, w₁ :: s.stk, s.ret, H₁⟩ c₂ :=
    hcfg.next (c₁ := c₁) (by omega) hs₁.bd_end hh₁ (by simp) (by simp)
  obtain ⟨n₂, hn₂, w₂, H₂, hs₂, hx₂, hr₂, hh₂⟩ := hb (shiftDep 1 dep) W
    ⟨s.pc + (compile dep a).length, w₁ :: s.stk, s.ret, H₁⟩ hfb ((henv.mono hx₁).push w₁) hc₂
  dsimp only at hs₂ hh₂ hx₂
  obtain ⟨rfl, hm⟩ := hr₁.nat_inv
  obtain ⟨rfl, hn⟩ := hr₂.nat_inv
  have hstep := hins ⟨s.pc + (compile dep a).length + (compile (shiftDep 1 dep) b).length,
    w₂ :: w₁ :: s.stk, s.ret, H₂⟩ w₁ w₂ s.stk hfi.head rfl
  have hbd := hs₂.bd_end
  have hres' : op w₁ w₂ ≤ W := by have := hres hm hn; omega
  refine ⟨n₁ + (n₂ + 1), by omega, op w₁ w₂, H₂, hs₁.trans (hs₂.trans (StepsB.one hbd hstep ?_)),
    hx₁.trans hx₂, .nat (hres hm hn), by omega⟩
  refine hbd.setStk (by omega) ?_ (by simp; omega)
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hres'
  · exact hbd.stk x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))

theorem sim_cons {ρ : List Val} {a b : Tm} {u v : Val} {c₁ c₂ : ℕ}
    (ha : SimEv P ρ a u c₁) (hb : SimEv P ρ b v c₂) :
    SimEv P ρ (.cons a b) (.cons u v) (c₁ + c₂ + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfa : FitsAt P s.pc (compile dep a) := hfit.append_left
  have hrest := hfit.append_right
  have hfb : FitsAt P (s.pc + (compile dep a).length) (compile (shiftDep 1 dep) b) := hrest.append_left
  have hfi : FitsAt P (s.pc + (compile dep a).length + (compile (shiftDep 1 dep) b).length)
      [Instr.cons] := hrest.append_right
  have hlen := hfit.1
  have e : s.pc + (compile dep a ++ (compile (shiftDep 1 dep) b ++ [Instr.cons])).length =
      s.pc + (compile dep a).length + (compile (shiftDep 1 dep) b).length + 1 := by simp; omega
  rw [e]
  simp only [List.length_append, List.length_singleton] at hlen
  have hL := hcfg.len
  have hB := hcfg.heap
  have hstk := hcfg.stk
  obtain ⟨n₁, hn₁, w₁, H₁, hs₁, hx₁, hr₁, hh₁⟩ := ha dep W s hfa henv (hcfg.sub (by omega))
  have hc₂ : Cfg P W ⟨s.pc + (compile dep a).length, w₁ :: s.stk, s.ret, H₁⟩ c₂ :=
    hcfg.next (c₁ := c₁) (by omega) hs₁.bd_end hh₁ (by simp) (by simp)
  obtain ⟨n₂, hn₂, w₂, H₂, hs₂, hx₂, hr₂, hh₂⟩ := hb (shiftDep 1 dep) W
    ⟨s.pc + (compile dep a).length, w₁ :: s.stk, s.ret, H₁⟩ hfb ((henv.mono hx₁).push w₁) hc₂
  dsimp only at hs₂ hh₂ hx₂
  have hstep := step_cons (P := P) (s := ⟨s.pc + (compile dep a).length +
    (compile (shiftDep 1 dep) b).length, w₂ :: w₁ :: s.stk, s.ret, H₂⟩) hfi.head w₁ w₂ s.stk rfl
  have hbd := hs₂.bd_end
  have hw₁ : w₁ ≤ W := hbd.stk w₁ (by simp)
  have hw₂ : w₂ ≤ W := hbd.stk w₂ (by simp)
  refine ⟨n₁ + (n₂ + 1), by omega, P.B + H₂.length, H₂ ++ [(w₁, w₂)],
    hs₁.trans (hs₂.trans (StepsB.one hbd hstep ?_)), (hx₁.trans hx₂).trans (HExt.snoc _ _),
    .cons (p := H₂.length) (by simp) ((hr₁.mono hx₂).mono (HExt.snoc _ _)) (hr₂.mono (HExt.snoc _ _)),
    by simp; omega⟩
  refine ⟨by dsimp only; omega, by simp; omega, ?_, hbd.retLen, hbd.ret, by simp; omega, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · exact hbd.stk x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hbd.heap p hp
    · simp at hp; subst hp; exact ⟨hw₁, hw₂⟩

theorem sim_fst {ρ : List Val} {a : Tm} {u v : Val} {c : ℕ} (ha : SimEv P ρ a (.cons u v) c) :
    SimEv P ρ (.fst a) u (c + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfa : FitsAt P s.pc (compile dep a) := hfit.append_left
  have hfi : FitsAt P (s.pc + (compile dep a).length) [Instr.fst] := hfit.append_right
  have hlen := hfit.1
  simp only [List.length_append, List.length_singleton] at hlen ⊢
  have hL := hcfg.len
  have hstk := hcfg.stk
  obtain ⟨n₁, hn₁, w, H₁, hs₁, hx₁, hr₁, hh₁⟩ := ha dep W s hfa henv (hcfg.sub (by omega))
  obtain ⟨p, a', b', rfl, hp, hra, hrb⟩ := hr₁.cons_inv
  have hbd := hs₁.bd_end
  have hstep := step_fst (P := P) (s := ⟨s.pc + (compile dep a).length, (P.B + p) :: s.stk, s.ret, H₁⟩)
    hfi.head p a' b' s.stk rfl hp
  have ha'W : a' ≤ W := (hbd.heap (a', b') (List.mem_of_getElem? hp)).1
  refine ⟨n₁ + 1, by omega, a', H₁, hs₁.trans (StepsB.one hbd hstep ?_), hx₁, hra, by omega⟩
  refine hbd.setStk (by omega) ?_ (by simp; omega)
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ha'W
  · exact hbd.stk x (List.mem_cons_of_mem _ hx)

theorem sim_snd {ρ : List Val} {a : Tm} {u v : Val} {c : ℕ} (ha : SimEv P ρ a (.cons u v) c) :
    SimEv P ρ (.snd a) v (c + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfa : FitsAt P s.pc (compile dep a) := hfit.append_left
  have hfi : FitsAt P (s.pc + (compile dep a).length) [Instr.snd] := hfit.append_right
  have hlen := hfit.1
  simp only [List.length_append, List.length_singleton] at hlen ⊢
  have hL := hcfg.len
  have hstk := hcfg.stk
  obtain ⟨n₁, hn₁, w, H₁, hs₁, hx₁, hr₁, hh₁⟩ := ha dep W s hfa henv (hcfg.sub (by omega))
  obtain ⟨p, a', b', rfl, hp, hra, hrb⟩ := hr₁.cons_inv
  have hbd := hs₁.bd_end
  have hstep := step_snd (P := P) (s := ⟨s.pc + (compile dep a).length, (P.B + p) :: s.stk, s.ret, H₁⟩)
    hfi.head p a' b' s.stk rfl hp
  have hb'W : b' ≤ W := (hbd.heap (a', b') (List.mem_of_getElem? hp)).2
  refine ⟨n₁ + 1, by omega, b', H₁, hs₁.trans (StepsB.one hbd hstep ?_), hx₁, hrb, by omega⟩
  refine hbd.setStk (by omega) ?_ (by simp; omega)
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hb'W
  · exact hbd.stk x (List.mem_cons_of_mem _ hx)

theorem sim_isNatT (hB : 2 ≤ P.B) {ρ : List Val} {a : Tm} {n c : ℕ} (ha : SimEv P ρ a (.nat n) c) :
    SimEv P ρ (.isNat a) (.nat 1) (c + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfa : FitsAt P s.pc (compile dep a) := hfit.append_left
  have hfi : FitsAt P (s.pc + (compile dep a).length) [Instr.isNat] := hfit.append_right
  have hlen := hfit.1
  simp only [List.length_append, List.length_singleton] at hlen ⊢
  have hL := hcfg.len
  have hstk := hcfg.stk
  have hHB := hcfg.heap
  obtain ⟨n₁, hn₁, w, H₁, hs₁, hx₁, hr₁, hh₁⟩ := ha dep W s hfa henv (hcfg.sub (by omega))
  obtain ⟨rfl, hn⟩ := hr₁.nat_inv
  have hbd := hs₁.bd_end
  have hstep := step_isNat (P := P) (s := ⟨s.pc + (compile dep a).length, w :: s.stk, s.ret, H₁⟩)
    hfi.head w s.stk rfl
  simp only [if_pos hn] at hstep
  refine ⟨n₁ + 1, by omega, 1, H₁, hs₁.trans (StepsB.one hbd hstep ?_), hx₁, .nat (by omega), by omega⟩
  refine hbd.setStk (by omega) ?_ (by simp; omega)
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · omega
  · exact hbd.stk x (List.mem_cons_of_mem _ hx)

theorem sim_isNatF (hB : 2 ≤ P.B) {ρ : List Val} {a : Tm} {u v : Val} {c : ℕ}
    (ha : SimEv P ρ a (.cons u v) c) : SimEv P ρ (.isNat a) (.nat 0) (c + 1) := by
  intro dep W s hfit henv hcfg
  simp only [compile] at hfit ⊢
  have hfa : FitsAt P s.pc (compile dep a) := hfit.append_left
  have hfi : FitsAt P (s.pc + (compile dep a).length) [Instr.isNat] := hfit.append_right
  have hlen := hfit.1
  simp only [List.length_append, List.length_singleton] at hlen ⊢
  have hL := hcfg.len
  have hstk := hcfg.stk
  have hHB := hcfg.heap
  obtain ⟨n₁, hn₁, w, H₁, hs₁, hx₁, hr₁, hh₁⟩ := ha dep W s hfa henv (hcfg.sub (by omega))
  obtain ⟨p, a', b', rfl, hp, hra, hrb⟩ := hr₁.cons_inv
  have hbd := hs₁.bd_end
  have hstep := step_isNat (P := P) (s := ⟨s.pc + (compile dep a).length, (P.B + p) :: s.stk, s.ret, H₁⟩)
    hfi.head (P.B + p) s.stk rfl
  simp only [if_neg (show ¬ (P.B + p < P.B) by omega)] at hstep
  refine ⟨n₁ + 1, by omega, 0, H₁, hs₁.trans (StepsB.one hbd hstep ?_), hx₁, .nat (by omega), by omega⟩
  refine hbd.setStk (by omega) ?_ (by simp; omega)
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · omega
  · exact hbd.stk x (List.mem_cons_of_mem _ hx)

end Lax117284Proofs.Treewidth.Fun.VM
