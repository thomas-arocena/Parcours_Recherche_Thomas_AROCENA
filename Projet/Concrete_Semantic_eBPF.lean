import Projet.Syntaxe_eBPF
/-import LeanSearchClient
import Mathlib-/


/--Function that takes a function g from Register to Val, a Register α and a Val v and return a function f so that f(α) = v and f(r!=α)=g(r)-/
def update(g : (Register → Val)) (α : Register) (v : Val) : Register → Val :=
  fun r : Register => if r = α then v else g r

/--Function that takes an Argument src, a Register dst and a State s and return a new State where pc+=1 and dst = dst + src-/
def add(dst : Register)(src : Argument)(s : State) : State :=
  match src with
  |Argument.imm v_src => {pc := s.pc + 1, reg := update s.reg dst (s.reg dst + v_src)}
  |Argument.reg r_src => {pc := s.pc + 1, reg := update s.reg dst (s.reg dst + s.reg r_src)}

/--Function that takes an Argument src, a Register dst ans a State s and return a new State where pc+=1 and dst = dst or src-/
def or_(dst : Register)(src : Argument)(s : State) : State :=
  match src with
  |Argument.imm v_src => {pc := s.pc + 1, reg := update s.reg dst (s.reg dst ||| v_src)}
  |Argument.reg r_src => {pc := s.pc + 1, reg := update s.reg dst (s.reg dst ||| s.reg r_src)}

/--Function that takes an Argument src, a Register dst ans a State s and return a new State with pc=s.pc+1 and dst = src-/
def mov (dst : Register)(src : Argument)(s : State) : State :=
  match src with
  |Argument.imm v_src => {pc := s.pc + 1, reg := update s.reg dst (v_src)}
  |Argument.reg r_src => {pc := s.pc + 1, reg := update s.reg dst (s.reg r_src)}

/--Function that takes an Nat offset and a State s and return the State with pc = pc + offset-/
def ja (offset: Int) (s : State) : State :=
  {s with pc := s.pc+offset}

/--Function that takes two Register src and dst and an offset and a State s and return the State with pc = pc + offset if dst = src and pc = pc + 1 otherwise-/
def jeq(dst : Register)(src : Argument)(offset: Int)(s : State) : State :=
  match src with
  |Argument.imm v_src =>
    if s.reg dst = v_src then {s with pc := s.pc + offset} else {s with pc := s.pc + 1}
  |Argument.reg r_src =>
    if s.reg dst = s.reg r_src then {s with pc := s.pc + offset} else {s with pc := s.pc + 1}

def exit (s : State) : State :=
  {s with pc := s.pc + 1}

def g : (Register → Val) := fun r : Register => 0
def s₀ : State := {pc := 0, reg := g}
def example_program : Program := [Statement.mov Register.r1 (Argument.imm 10), Statement.mov Register.r2 (Argument.imm 32), Statement.add Register.r0 (Argument.reg Register.r1), Statement.add Register.r0 (Argument.reg Register.r2), Statement.exit]
def printState (s : State) : IO Unit := do
  IO.println s!"pc = {s.pc}"
  IO.println s!"R0 = {s.reg Register.r0}"
  IO.println s!"R1 = {s.reg Register.r1}"
  IO.println s!"R2 = {s.reg Register.r2}"

#eval mov Register.r1 (Argument.imm 10) s₀
def s₁ : State := mov Register.r1 (Argument.imm 10) s₀
#eval printState s₁--
def s₂ : State := mov Register.r2 (Argument.imm 32) s₁
#eval printState s₂
def s₃ : State := add Register.r0 (Argument.reg Register.r1) s₂
#eval printState s₃
def s₄ : State := add Register.r0 (Argument.reg Register.r2) s₃
#eval printState s₄

/--Defining the relation from a State to another-/
inductive ConcreteSemantics (p : Program) : State → State → Prop

  | add (s : State) (src : Argument) (dst : Register) :
    s.pc >= 0
    → s.pc <= p.length
    → p[(s.pc).toNat]! = Statement.add dst src
    -------------------------------------------------------------------------/
    → ConcreteSemantics p s (add dst src s)

  | ja (s : State) (k : Nat) (dst : Register):
    s.pc >= 0
    → s.pc <= p.length
    → p[(s.pc).toNat]! = Statement.ja k
    ---------------------------------------------------------------
    → ConcreteSemantics p s (ja k s)

  | mov (s : State) (src : Argument) (dst : Register) :
    s.pc >= 0
    → s.pc <= p.length
    → p[(s.pc).toNat]! = Statement.mov dst src
    ---------------------------------------------------------------
    → ConcreteSemantics p s (mov dst src s)

  | jed (s : State) (src : Argument) (dst : Register) (offset : Int) :
    s.pc >= 0
    → s.pc <= p.length
    → p[(s.pc).toNat]! = Statement.jeq dst src offset
    → (s.pc+offset) >= 0
    → (s.pc+offset) <= p.length
    ---------------------------------------------------------------
    → ConcreteSemantics p s (jeq dst src offset s)

  | or (s : State) (src : Argument) (dst : Register) :
    s.pc >= 0
    → s.pc <= p.length
    → p[(s.pc).toNat]! = Statement.or dst src
    -------------------------------------------------------------
    → ConcreteSemantics p s (or_ dst src s)
