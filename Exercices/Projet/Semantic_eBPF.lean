import Projet.Syntaxe_eBPF
import LeanSearchClient
import Mathlib

/--Function that takes a function g from Register to Val, a Register α and a Val v and return a function f so that f(α) = v and f(r!=α)=g(r)-/
def update(g : (Register → RegisterValue))(α : Register)(v : RegisterValue) : Register -> RegisterValue :=
  fun r : Register => if r = α then v else g r

/--Function that takes an Argument src, a Register dst and a State s and return a new State where pc+=1 and dst = dst + src-/
def add(src : Argument)(dst : Register)(s : State) : State :=
  match src with
  |Argument.imm v_src => match (s.reg dst) with
    |RegisterValue.not_init => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.scalar_value v_src)}
    |RegisterValue.pointer dst_ptr => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.pointer (v_src + dst_ptr))}
    |RegisterValue.scalar_value dst_val => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.scalar_value (v_src + dst_val))}
  |Argument.reg r_src => match (s.reg r_src) with
    |RegisterValue.not_init => match (s.reg dst) with
      |RegisterValue.not_init => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.not_init)}
      |RegisterValue.pointer dst_ptr => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.pointer dst_ptr)}
      |RegisterValue.scalar_value dst_val => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.scalar_value dst_val)}
    |RegisterValue.pointer ptr => match (s.reg dst) with
      |RegisterValue.not_init => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.scalar_value ptr)}
      |RegisterValue.pointer dst_ptr => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.scalar_value (ptr + dst_ptr))}
      |RegisterValue.scalar_value dst_val => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.pointer (ptr + dst_val))}
    |RegisterValue.scalar_value val => match (s.reg dst) with
      |RegisterValue.not_init => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.scalar_value val)}
      |RegisterValue.pointer dst_ptr => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.pointer (val + dst_ptr))}
      |RegisterValue.scalar_value dst_val => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.scalar_value (val + dst_val))}

  /-{pc := s.pc + 1, reg := update s.reg dst ((s.reg dst) + (s.reg r_src))}-/

/--Function that takes an Argument src, a Register dst ans a State s and return a new State where pc+=1 and dst = dst or src-/
def or_(src : Argument)(dst : Register)(s : State) : State :=
    match src with
  |Argument.imm v_src => match (s.reg dst) with
    |RegisterValue.not_init => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.not_init)}
    |RegisterValue.pointer dst_ptr => if v_src >= 0 then {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.scalar_value (dst_ptr.toNat ||| v_src.toNat))} else {pc := s.pc + 1, reg := s.reg}
    |RegisterValue.scalar_value dst_val => if v_src >= 0 then {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.scalar_value (dst_val.toNat ||| v_src.toNat))} else {pc := s.pc + 1, reg := s.reg}
  |Argument.reg r_src => match (s.reg r_src) with
    |RegisterValue.not_init => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.not_init)}
    |RegisterValue.pointer ptr => match (s.reg dst) with
      |RegisterValue.not_init => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.not_init)}
      |RegisterValue.pointer dst_ptr => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.scalar_value (dst_ptr.toNat ||| ptr.toNat))}
      |RegisterValue.scalar_value dst_val => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.scalar_value (dst_val.toNat ||| ptr.toNat))}
    |RegisterValue.scalar_value val => match (s.reg dst) with
      |RegisterValue.not_init => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.scalar_value val)}
      |RegisterValue.pointer dst_ptr => if val >= 0 then {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.scalar_value (dst_ptr.toNat ||| val.toNat))} else {pc := s.pc + 1, reg := s.reg}
      |RegisterValue.scalar_value dst_val => if val >= 0 then {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.scalar_value (dst_val.toNat ||| val.toNat))} else {pc := s.pc + 1, reg := s.reg}


def a₁ : Nat := 1
def b₁ : Nat := 1

def a₂ : Int := -1
def b₂ : Int := 1

#check a₁ ||| b₁

#eval a₂.toNat'

/--Function that takes an Argument src, a Register dst ans a State s and return a new State with pc=s.pc+1 and dst = src-/
def mov(src : Argument)(dst : Register)(s : State) : State :=
  match src with
  |Argument.imm v_src => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.scalar_value v_src)}
  |Argument.reg r_src => match (s.reg r_src) with
    |RegisterValue.not_init => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.not_init)}
    |RegisterValue.pointer ptr => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.pointer ptr)}
    |RegisterValue.scalar_value val => {pc := s.pc + 1, reg := update s.reg dst (RegisterValue.scalar_value val)}

/-
def bSwap(dst : Register)(s : State) : State :=
  {pc = s.pc + 1, reg = update s.reg dst }-/

/--Function that takes an Nat offset and a State s and return the State with pc = pc + offset-/
def ja(offset: Int)(s : State) : State :=
  {s with pc:= s.pc+offset}

/--Function that takes two Register src and dst and an offset and a State s and return the State with pc = pc + offset if dst = src and pc = pc + 1 otherwise-/
def jeq(src : Argument)(dst : Register)(offset: Int)(s : State) : State :=
  match src with
  |Argument.imm v_src => match (s.reg dst) with
    |RegisterValue.not_init => {s with pc := s.pc + 1}
    |RegisterValue.pointer dst_ptr => if v_src = dst_ptr then ja offset s else {s with pc := s.pc + 1}
    |RegisterValue.scalar_value dst_val => if v_src = dst_val then ja offset s else {s with pc := s.pc + 1}
  |Argument.reg r_src => match (s.reg r_src) with
    |RegisterValue.not_init => {s with pc := s.pc + 1}
    |RegisterValue.pointer ptr => match (s.reg dst) with
      |RegisterValue.not_init => {s with pc := s.pc + 1}
      |RegisterValue.pointer dst_ptr => if ptr = dst_ptr then ja offset s else {s with pc := s.pc + 1}
      |RegisterValue.scalar_value dst_val => if ptr = dst_val then ja offset s else {s with pc := s.pc + 1}
    |RegisterValue.scalar_value val => match (s.reg dst) with
      |RegisterValue.not_init => {s with pc := s.pc + 1}
      |RegisterValue.pointer dst_ptr => if val = dst_ptr then ja offset s else {s with pc := s.pc + 1}
      |RegisterValue.scalar_value dst_val => if val = dst_val then ja offset s else {s with pc := s.pc + 1}

def setRange : ℕ → Set ℕ
| 0 => {0}
| n + 1 => setRange n ∪ {n + 1}


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
