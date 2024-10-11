set_option autoImplicit false

/-- Register is the Type for eBPF register, there are 11 registers -/
inductive Register
  |reg0 : Register
  |reg1 : Register
  |reg2 : Register
  |reg3 : Register
  |reg4 : Register
  |reg5 : Register
  |reg6 : Register
  |reg7 : Register
  |reg8 : Register
  |reg9 : Register
  |reg10 : Register

/-- Argument is the Type for eBPF expressions-/
inductive Argument
  /-- reg is an Argument from a register-/
  | reg : Register -> Argument
  /-- imm is an Argument from an immediate value-/
  | imm : Nat -> Argument

/-- Statement is the type for eBPF instructions -/
inductive Statement
  | add : Argument -> Argument -> Statement
  | or : Argument -> Argument -> Statement
  | mov : Argument -> Argument -> Statement
  | bSwap : Argument -> Statement
  | offset : Argument -> Argument -> Statement
