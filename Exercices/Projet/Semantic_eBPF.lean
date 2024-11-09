import Projet.Syntaxe_eBPF
import LeanSearchClient
import Mathlib

/--Function that takes a function g from Register to Val, a Register α and a Val v and return a function f so that f(α) = v and f(r!=α)=g(r)-/
def update(g : (Register → Val))(α : Register)(v : Val) : Register -> Val :=
  fun r : Register => if r = α then v else g r

/--Function that takes an Argument src, a Register dst and a State s and return a new State where pc+=1 and dst = dst + src-/
def add(src : Argument)(dst : Register)(s : State) : State :=
  match src with
  |Argument.imm v_src => {pc := s.pc + 1, reg := update s.reg dst ((s.reg dst)+v_src)}
  |Argument.reg r_src => {pc := s.pc + 1, reg := update s.reg dst ((s.reg dst) + (s.reg r_src))}

/--Function that takes an Argument src, a Register dst ans a State s and return a new State where pc+=1 and dst = dst or src-/
def or_(src : Argument)(dst : Register)(s : State) : State :=
  match src with
  |Argument.imm v_src => if v_src >= 0 then {pc := s.pc + 1, reg := update s.reg dst ((s.reg dst).toNat ||| v_src.toNat)} else {pc := s.pc + 1, reg := s.reg}
  |Argument.reg r_src => if (s.reg r_src) >= 0 then {pc := s.pc + 1, reg := update s.reg dst ((s.reg dst).toNat ||| (s.reg r_src).toNat)} else {pc := s.pc + 1, reg := s.reg}

def a₁ : Nat := 1
def b₁ : Nat := 1

def a₂ : Int := -1
def b₂ : Int := 1

#check a₁ ||| b₁

#eval a₂.toNat'

/--Function that takes an Argument src, a Register dst ans a State s and return a new State with pc=s.pc+1 and dst = src-/
def mov(src : Argument)(dst : Register)(s : State) : State :=
  match src with
  |Argument.imm v_src => {pc := s.pc + 1, reg := update s.reg dst v_src}
  |Argument.reg r_src => {pc := s.pc + 1, reg := update s.reg dst (s.reg r_src)}


/-
def bSwap(dst : Register)(s : State) : State :=
  {pc = s.pc + 1, reg = update s.reg dst }-/

/--Function that takes an Nat offset and a State s and return the State with pc = pc + offset-/
def ja(offset: Int)(s : State) : State :=
  {s with pc:= s.pc+offset}

/--Function that takes two Register src and dst and an offset and a State s and return the State with pc = pc + offset if dst = src and pc = pc + 1 otherwise-/
def jeq(src : Argument)(dst : Register)(offset: Int)(s : State) : State :=
  match src with
  |Argument.imm v_src => if v_src = s.reg dst then ja offset s else {s with pc := s.pc + 1}
  |Argument.reg r_src => if s.reg r_src = s.reg dst then ja offset s else {s with pc := s.pc + 1}

def setRange : ℕ → Set ℕ
| 0 => {0}
| n + 1 => setRange n ∪ {n + 1}

def a:=[1,3,24,3]
#eval (a[4]?)

/--Defining the relation from a State to another-/
inductive Semantics (p : Program) : State -> State -> Prop
  | ja_ (s0 s1 : State) :
      (∃ (k : Nat), (s0.pc>=0) ∧ ((s0.pc).toNat ∈ (setRange p.length)) ∧ (p[(s0.pc).toNat]! = Statement.ja k ) → (s1 = ja k s0))
      → Semantics p s0 s1
  | add (s0 s1 : State) :
      (∃ (src : Argument), ∃ (dst : Register),(s0.pc >=0)∧(s0.pc<=p.length) ∧ (p[(s0.pc).toNat]! = Statement.add src dst) → (s1 = add src dst s0))
      → Semantics p s0 s1
  | mov (s0 s1 : State) :
      (∃ (src : Argument), ∃ (dst : Register), (s0.pc >=0)∧(s0.pc<=p.length) ∧ (p[(s0.pc).toNat]? = Statement.mov src dst) → (s1 = mov src dst s0))
      → Semantics p s0 s1
  | jed (s0 s1 : State) :
      (∃ (src : Argument), ∃ (dst : Register), ∃ (offset : Int), (s0.pc >=0)∧(s0.pc<=p.length) ∧ (p[(s0.pc).toNat]? = Statement.jeq src dst offset) ∧ ((s0.pc+offset) >=0)∧((s0.pc+offset)<=p.length) → (s1 = jeq src dst offset s0))
      → Semantics p s0 s1
  | or (s0 s1 : State) :
      (∃ (src : Argument), ∃ (dst : Register),(s0.pc >=0)∧(s0.pc<=p.length) ∧ (p[(s0.pc).toNat]? = Statement.or src dst) → (s1 = or_ src dst s0))
      → Semantics p s0 s1
