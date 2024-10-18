import Syntaxe_eBPF

/--Function that takes a function g from Register to Val, a Register α and a Val v and return a function f so that f(α) = v and f(r!=α)=g(r)-/
def update(g : (Register → Val))(α : Register)(v : Val) : Register -> Val :=
  fun r : Register => if r = α then v else g r

/--Function that takes an Argument src, a Register dst and a State s and return a new State where pc+=1 and dst = dst + src-/
def add(src : Argument)(dst : Register)(s : State) : State :=
  match src with
  |Argument.imm v_src => {pc := s.pc, reg := update s.reg dst ((s.reg dst)+v_src)}
  |Argument.reg r_src => {pc := s.pc, reg := update s.reg dst ((s.reg dst) + (s.reg r_src))}

/--Function that takes an Argument src, a Register dst ans a State s and return a new State where pc+=1 and dst = dst or src-/
def or(src : Argument)(dst : Register)(s : State) : State :=
  match src with
  |Argument.imm v_src => {pc := s.pc + 1, reg := update s.reg dst ((s.reg dst) ||| v_src)}
  |Argument.reg r_src => {pc := s.pc + 1, reg := update s.reg dst ((s.reg dst) ||| (s.reg r_src))}

/--Function that takes an Argument src, a Register dst ans a State s and return a new State with pc=s.pc+1 and dst = src-/
def mov(src : Argument)(dst : Register)(s : State) : State :=
  match src with
  |Argument.imm v_src => {pc := s.pc + 1, reg := update s.reg dst v_src}
  |Argument.reg r_src => {pc := s.pc + 1, reg := update s.reg dst (s.reg src)}

/-
def bSwap(dst : Register)(s : State) : State :=
  {pc = s.pc + 1, reg = update s.reg dst }-/






/--Function that takes an Nat offset and a State s and return the State with pc = pc + offset-/
def ja(offset: Int)(s : State) : State :=
  {s with pc:= s.pc+offset}

/--Function that takes two Register src and dst and an offset and a State s and return the State with pc = pc + offset if dst = src and pc = pc + 1 otherwise-/
def jed(src : Register)(dst : Register)(offset: Int)(s : State) : State :=
  if s.reg src = s.reg dst then
    ja offset s
  else {s with pc:= s.pc+1}

/--Defining the relation from a State to another-/
inductive Semantics(p : Program): State -> State -> Prop
  |(s0 : State) => (s1 : State) => (∃(k:Nat) , (s0.pc ∈ [0 . p.length]) ∧ (p[s0.pc]=ja k) → (s1 = ja k s0) ): Semantics p s0 s1
  |∃(src : Argument), ∃(dst: Register) , (s0.pc ∈ [0 . p.length]) ∧ (p[s0.pc]=add src dst) → (s1 add src dst s0) : Semantics p s0 s1
