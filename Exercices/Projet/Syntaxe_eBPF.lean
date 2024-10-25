set_option autoImplicit false

/-- Register is the Type for eBPF register, there are 11 registers -/
inductive Register
  |reg0
  |reg1
  |reg2
  |reg3
  |reg4
  |reg5
  |reg6
  |reg7
  |reg8
  |reg9
  |reg10
  deriving DecidableEq

abbrev Val := Int
/-- Argument is the Type for eBPF expressions-/
inductive Argument
  /-- reg is an Argument from a register-/
  | reg : Register -> Argument
  /-- imm is an Argument from an immediate value-/
  | imm : Val -> Argument

/-- Statement is the type for eBPF instructions -/
inductive Statement
  /-- add take an Argument src and a Register dst and add src into dst (dst+=src)-/
  | add : Argument -> Register -> Statement
  /-- or take an Argument src and a Register dst and return (src or dst) into dst (dst = dst or src)-/
  | or : Argument -> Register -> Statement
  /-- mov take an Argument src and a Register dst and put src into dst (dst = src)-/
  | mov : Argument -> Register -> Statement
  /--bSwap take a Register dst and return the byte swap of dst into dst-/
  | bSwap : Register -> Statement
  /--ja take an Integer offset and add offset to pc-/
  | ja : Int -> Statement
  /--jeq take an Argument src, a Register dst, an Integer offset add offset to pc if dst==src-/
  | jeq : Argument -> Register -> Int -> Statement
  deriving Inhabited

/--Program is the Type that represent eBPF program and is simply made of Statement-/
abbrev Program : Type := List Statement

/-- State is a structure that represent a state of a program with pc(program counter) representing the position in the program and data representing the values of each register-/
structure State where
  pc : Int
  reg : Register -> Int
