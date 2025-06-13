import Projet.Syntaxe_eBPF

/--
  The function `update` takes a function `g` (mapping a register to an AbsRegisterValue),
  a register `α` and a value `v` of type `AbsRegisterValue`. It returns a new function that updates
  the value associated with the register `α`. If the register is `α`, it returns the value `v`,
  otherwise it returns the value from `g r`.
-/
def update(g : (Register → AbsRegisterValue)) (α : Register) (v : AbsRegisterValue) : Register → AbsRegisterValue :=
  fun r : Register => if r = α then v else g r

/-
/--
  The function `AbsRegisterValue_union` takes two `AbsRegisterValue` values (a₁ and a₂) and computes the union of
  them to produce a new `AbsRegisterValue`. It combines the initialization status, the interval,
  and the tristate number of both values.
-/
def AbsRegisterValue_union(a₁ a₂ : AbsRegisterValue) : AbsRegisterValue :=
  {is_init := a₁.is_init ∨ a₂.is_init , i := intrvl_union a₁.i a₂.i , t := tnum_union a₁.t a₂.t }

/--
  The function `AbsRegisterValue_is_in` checks if the union of `a₁` and `a₂` is equal to `a₂`.
  This is useful for checking if the first value is fully contained within the second.
-/
def AbsRegisterValue_is_in(a₁ a₂ : AbsRegisterValue) : Bool :=
  (AbsRegisterValue_union a₁ a₂ == a₂)

/--
  The function `add` simulates an addition operation. It takes a destination register `dst`,
  a source argument `src`, and the current state `s`.
  Depending on whether the source is an immediate value or a register, it performs the addition.
  It updates the state and returns the new state with the modified register `dst`.
-/
def add (dst : Register) (src : Argument) (s : AbsState) : AbsState :=
  match src with
  |Argument.imm v_src =>
    let a := s.reg dst
    let b : AbsRegisterValue := {is_init := true, i := intrvl_const v_src, t := tnum_const v_src}
    {pc := s.pc + 1, reg := update s.reg dst {is_init := true, i := intrvl_add a.i b.i, t:= tnum_add a.t b.t}, stack := s.stack}
  |Argument.reg r_src =>
    let a := s.reg dst -- AbsRegValue
    let b := s.reg r_src -- AbsRegValue, when src is a Reg
    {pc := s.pc + 1, reg := update s.reg dst {is_init := true, i := intrvl_add a.i b.i, t:= tnum_add a.t b.t}, stack := s.stack}


def r₁ (r : Register) : AbsRegisterValue :=
  {is_init := true, i := {min := 1 , max := 5}, t := { v := 1 , m := 6}}

def s₁ : AbsState :=
  {pc := 1, reg := r₁, stack := []}

/--
  The `mov` function performs a move operation. It takes a destination register `dst`,
  a source argument `src`, and the current state `s`.
  Depending on whether the source is an immediate value or a register, it moves the value to the destination register.
  It updates the state and returns the new state with the modified register `dst`.
-/
def mov(dst : Register)(src : Argument)(s : AbsState) : AbsState :=
  match src with
  |Argument.imm v_src =>
    {pc := s.pc + 1, reg := update s.reg dst {is_init := true, i := intrvl_const v_src, t:= tnum_const v_src}, stack := s.stack}
  |Argument.reg r_src =>
    {pc := s.pc + 1, reg := update s.reg dst (s.reg r_src), stack := s.stack}

/--
  The `ja` function performs a jump operation by adjusting the program counter (`pc`) by the provided `offset`.
  It returns the new state with the updated `pc` and the unchanged registers and stack.
-/
def ja(offset : Int)(s : AbsState) : AbsState :=
  {pc:= s.pc + offset, reg := s.reg, stack := s.stack}

/--
  The `call` function performs a call operation by pushing the current program counter (`pc`)
  onto the stack and updating the state with the new program counter.
-/
def call (offset : Int) (s : AbsState) : AbsState :=
  let new_stack := (s.pc + 1) :: s.stack
  {pc := s.pc + offset, reg := s.reg, stack := new_stack}

/--
  The `exit` function handles an exit operation by popping the top value from the stack and setting it as the new program counter (`pc`).
  If the stack is empty, it triggers an unreachable state, implying an invalid exit scenario.
-/
def exit(s : AbsState) : AbsState :=
  match s.stack with
  | new_pc :: new_stack => {pc := new_pc, reg := s.reg, stack := new_stack}
  | [] => unreachable!

-/
def add (dst : Register) (src : Argument) (s : AbsState) : AbsState :=
  let i₁ : I := (s.reg dst).i
  let t₁ : Tnum := (s.reg dst).t
  match src with
    | Argument.imm src_imm =>
      let i₂ : I := I.cst src_imm
      let t₂ : Tnum := Tnum.const src_imm
      {
        pc := s.pc + 1,
        reg := update s.reg dst {
          is_init := True, /- is_init = s.is_init ? Cas non initialisé ?-/
          i := i₁ + i₂,
          t := t₁ + t₂},
        stack := s.stack
      }
    | Argument.reg src_reg =>
      let i₂ : I := (s.reg src_reg).i
      let t₂ : Tnum := (s.reg src_reg).t
      {
        pc := s.pc + 1,
        reg := update s.reg dst {
          is_init := True, /- is_init = s.is_init ? Cas non initialisé ?-/
          i := i₁ + i₂,
          t := t₁ + t₂},
        stack := s.stack
      }

def mov (dst : Register) (src : Argument) (s : AbsState) : AbsState :=
  match src with
    | Argument.imm src_imm =>
      let i₁ : I := I.cst src_imm
      let t₁ : Tnum := Tnum.const src_imm
      {
        pc := s.pc + 1,
        reg := update s.reg dst {
          is_init := True, /- is_init = s.is_init ? Cas non initialisé ?-/
          i := i₁,
          t := t₁},
        stack := s.stack
      }
    | Argument.reg src_reg =>
      let i₁ : I := (s.reg src_reg).i
      let t₁ : Tnum := (s.reg src_reg).t
      {
        pc := s.pc + 1,
        reg := update s.reg dst {
          is_init := True, /- is_init = s.is_init ? Cas non initialisé ?-/
          i := i₁ ,
          t := t₁ },
        stack := s.stack
      }

def or (dst : Register) (src : Argument) (s : AbsState) : AbsState :=
  let i₁ : I := (s.reg dst).i
  let t₁ : Tnum := (s.reg dst).t
  match src with
    | Argument.imm src_imm =>
      let i₂ : I := I.cst src_imm
      let t₂ : Tnum := Tnum.const src_imm
      {
        pc := s.pc + 1,
        reg := update s.reg dst {
          is_init := True, /- is_init = s.is_init ? Cas non initialisé ?-/
          t := t₁ ||| t₂,
          i := I.or t i₁ i₂},
        stack := s.stack
      }
    | Argument.reg src_reg =>
      let i₂ : I := (s.reg src_reg).i
      let t₂ : Tnum := (s.reg src_reg).t
      {
        pc := s.pc + 1,
        reg := update s.reg dst {
          is_init := True, /- is_init = s.is_init ? Cas non initialisé ?-/
          t := t₁ ||| t₂,
          i := I.or t i₁ i₂},
        stack := s.stack
      }

def ja (offset : Int) (s : AbsState) :=
  {s with pc := s.pc+offset}

def jeq (dst : Register) (src : Argument) (offset : Int) (s : AbsState) : AbsState where
  pc := sorry
  reg := sorry
  stack := sorry

inductive AbstractSemantics (p : Program) : AbsState → AbsState → Prop
  | add (s : AbsState) (src : Argument) (dst : Register) :
    s.pc >= 0
    → s.pc <= p.length
    → p[(s.pc).toNat]! = Statement.add dst src
    -------------------------------------------------------------------------/
    → AbstractSemantics p s (add dst src s)

  | ja (s : AbsState) (k : Nat) (dst : Register):
    s.pc >= 0
    → s.pc <= p.length
    → p[(s.pc).toNat]! = Statement.ja k
    ---------------------------------------------------------------
    → AbstractSemantics p s (ja k s)

  | mov (s : AbsState) (src : Argument) (dst : Register) :
    s.pc >= 0
    → s.pc <= p.length
    → p[(s.pc).toNat]! = Statement.mov dst src
    ---------------------------------------------------------------
    → AbstractSemantics p s (mov dst src s)

  | jeq (s : AbsState) (src : Argument) (dst : Register) (offset : Int) :
    s.pc >= 0
    → s.pc <= p.length
    → p[(s.pc).toNat]! = Statement.jeq dst src offset
    → (s.pc+offset) >= 0
    → (s.pc+offset) <= p.length
    ---------------------------------------------------------------
    → AbstractSemantics p s (jeq dst src offset s)

  | or (s : AbsState) (src : Argument) (dst : Register) :
    s.pc >= 0
    → s.pc <= p.length
    → p[(s.pc).toNat]! = Statement.or dst src
    -------------------------------------------------------------
    → AbstractSemantics p s (or dst src s)

/-
def Edge (P : Program)(pc : Nat) : List Nat :=
  match P[pc]! with
  | Statement.add dst src => [pc + 1]
  | Statement.or dst src => [pc + 1]
  | Statement.mov dst src => [pc + 1]
  | Statement.ja (offset : Int) => if pc + offset >= 0 then [(pc + offset).toNat] else [0]
  | Statement.jeq dst src (offset : Int) => if pc + offset >=0 then [pc + 1, (pc + offset).toNat] else [pc+1 , 0]
  | Statement.call (offset : Int) => if pc + offset >= 0 then [(pc + offset).toNat] else [0]
  | Statement.exit => [pc]

def Graph (P : Program) : (Nat → List Nat) :=
  fun (α : Nat) => Edge P α

def Edge2 (P : Program) (s : AbsState) : List Nat :=
  let pc := (s.pc).toNat
  match P[pc]! with
  | Statement.add dst src => [pc + 1]
  | Statement.or dst src => [pc + 1]
  | Statement.mov dst src => [pc + 1]
  | Statement.ja (offset : Int) => if pc + offset >= 0 then [(pc + offset).toNat] else [0]
  | Statement.jeq dst src (offset : Int) => if pc + offset >=0 then [pc + 1, (pc + offset).toNat] else [pc+1 , 0]
  | Statement.call (offset : Int) => if pc + offset >= 0 then [(pc + offset).toNat] else [0]
  | Statement.exit => [(s.stack[0]!).toNat + 1]

def P1 : Program := [Statement.add Register.r1 (Argument.imm 1),Statement.add Register.r1 (Argument.imm 2),Statement.add Register.r1 (Argument.imm 3),Statement.add Register.r1 (Argument.imm 4),Statement.ja (-3)]

#eval Graph P1 0
#eval Graph P1 1
#eval Graph P1 2
#eval Graph P1 3
#eval Graph P1 4-/
-- P1 :
-- 1 : R1 + 1
-- 2 : R1 + 2
-- 3 : R1 + 3
-- 4 : R1 + 4
-- 5 : Jump offset -3 (goto 2)
