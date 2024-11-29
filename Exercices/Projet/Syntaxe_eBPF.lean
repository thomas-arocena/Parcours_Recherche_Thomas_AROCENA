set_option autoImplicit false

/-- Register is the Type for eBPF register, there are 11 registers -/
inductive Register
  /-- reg0 should contain the return value from function calls-/
  |reg0
  /-- reg1 to reg5 contain arguments for function calls-/
  |reg1
  /-- reg1 to reg5 contain arguments for function calls-/
  |reg2
  /-- reg1 to reg5 contain arguments for function calls-/
  |reg3
  /-- reg1 to reg5 contain arguments for function calls-/
  |reg4
   /-- reg1 to reg5 contain arguments for function calls-/
  |reg5
  /-- reg6 to reg9 registers that function calls will preserve-/
  |reg6
  /-- reg6 to reg9 registers that function calls will preserve-/
  |reg7
  /-- reg6 to reg9 registers that function calls will preserve-/
  |reg8
  /-- reg6 to reg9 registers that function calls will preserve-/
  |reg9
  /-- reg10 contains the (read-only) frame pointer to access stack-/
  |reg10
  deriving DecidableEq

abbrev Val := Int

inductive RegisterValue
  /-- Register value is a pointer-/
  |pointer : Val -> RegisterValue
  /-- Register value is a scalar value-/
  |scalar_value : Val -> RegisterValue
  /-- Register has not been initialize -/
  |not_init
  deriving BEq

/-- Argument is the Type for eBPF expressions-/
inductive Argument
  /-- reg is an Argument from a register-/
  | reg : Register -> Argument
  /-- imm is an Argument from an immediate value-/
  | imm : Val -> Argument
  deriving BEq

/-- Statement is the type for eBPF instructions -/
inductive Statement
  /-- add take an Argument src and a Register dst and add src into dst (dst+=src)-/
  | add : Argument -> Register -> Statement
  /-- or takes an Argument src and a Register dst and return (src or dst) into dst (dst = dst or src)-/
  | or : Argument -> Register -> Statement
  /-- mov takes an Argument src and a Register dst and put src into dst (dst = src)-/
  | mov : Argument -> Register -> Statement
  /--bSwap takes a Register dst and return the byte swap of dst into dst-/
  | bSwap : Register -> Statement
  /--ja takes an Integer offset and add offset to pc-/
  | ja : Int -> Statement
  /--jeq takes an Argument src, a Register dst, an Integer offset add offset to pc if dst==src-/
  | jeq : Argument -> Register -> Int -> Statement
  /-- exit ends the program-/
  | exit : Statement
  deriving Inhabited, BEq

/--Program is the Type that represent eBPF program and is simply made of Statement-/
abbrev Program : Type := List Statement

/-structure State where
  pc : Int
  reg : Register -> Int
-/

/-- State is a structure that represent a state of a program with pc(program counter) representing the position in the program and data representing the values of each register-/
structure State where
  pc : Int
  reg : Register -> RegisterValue

#check State

def Stack_pointer := 1

def P0 (s : State) : Prop := (s.reg Register.reg0 == RegisterValue.not_init)
def P1 (s : State) : Prop := (s.reg Register.reg1 == RegisterValue.pointer Stack_pointer)
def P2 (s : State) : Prop := (s.reg Register.reg2 == RegisterValue.not_init)
def P3 (s : State) : Prop := (s.reg Register.reg3 == RegisterValue.not_init)
def P4 (s : State) : Prop := (s.reg Register.reg4 == RegisterValue.not_init)
def P5 (s : State) : Prop := (s.reg Register.reg5 == RegisterValue.not_init)

def P (s : State) : Prop :=  P1 s ∧ P2 s ∧ P3 s ∧ P4 s ∧ P5 s ∧ P0 s

def StateInit : Type := {s : State // P s}

def Pend (s : State) : Prop := (s.reg Register.reg0 == RegisterValue.scalar_value 1)

def StateEnd : Type := {s : State // P s}
