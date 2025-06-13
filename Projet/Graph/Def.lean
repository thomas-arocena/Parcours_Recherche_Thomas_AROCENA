import Projet.Syntaxe_eBPF

/-structure Arc where
  dst : Bool
  src : Bool
  deriving BEq

abbrev Graph (n : Nat) := Fin n → Fin n → Arc

def is_target (G : Graph n) (src dst : Fin n) : Bool :=
  (G src dst).dst

def is_source (G : Graph n) (src dst : Fin n) : Bool :=
  (G src dst).src

def well_formed (G : Graph n) (src dst : Fin n) : Bool :=
  let c1 := is_target G src dst = is_source G dst src
  let c2 := is_source G src dst = is_target G dst src
  c1 ∧ c2
-/

def successors (prog : Program)(i : Fin prog.length) : List (Fin prog.length) :=
  match prog[i] with
  | Statement.exit => []
  | Statement.ja offset => sorry /- [(i + offset).toNat] -/
  | Statement.jeq r a n => sorry /- [i + 1, i + n] -/
  | Statement.call n => sorry
  | _ => sorry /-[i+1]-/

structure CFG (n : Nat) where
  successors : Fin n → List (Fin n)

def buildCFG (prog : Program) : CFG prog.length := {
  successors := λ i => successors prog i
}

def AbsRegisterValue.le (A₁ A₂ : AbsRegisterValue) : Bool :=
  if A₂.is_init = False ∨ (A₁.i ⊆ A₂.i ∧ A₁.t ⊆ A₂.t) then True else False

def AbsState.le (s₁ s₂ : AbsState) : Bool :=
  s₁.pc = s₂.pc ∧ ∀(r : Register), (s₁.reg r).le (s₂.reg r)
