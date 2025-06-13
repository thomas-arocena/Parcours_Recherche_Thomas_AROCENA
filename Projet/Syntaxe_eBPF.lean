import Mathlib
import Projet.I
import Projet.Tnum

-- Option to disable automatic type inference.
set_option autoImplicit false

-- Abbreviation for the UInt64 type, named `Val`.
abbrev Val := UInt64

/--
  Inductive type `Register` represents the registers used in an eBPF processor.
-/
inductive Register
  /-- Register r0 holds the return value from function calls. -/
  | r0
  /-- Register r1 holds an argument for function calls. -/
  | r1
  /-- Register r2 holds an argument for function calls. -/
  | r2
  /-- Register r3 holds an argument for function calls. -/
  | r3
  /-- Register r4 holds an argument for function calls. -/
  | r4
  /-- Register r5 holds an argument for function calls. -/
  | r5
  /-- Registers r6 to r9 are preserved across function calls. -/
  | r6
  /-- Registers r6 to r9 are preserved across function calls. -/
  | r7
  /-- Registers r6 to r9 are preserved across function calls. -/
  | r8
  /-- Registers r6 to r9 are preserved across function calls. -/
  | r9
  /-- Register r10 contains the (read-only) frame pointer for stack access. -/
  | r10
  deriving DecidableEq, Repr

/--
  Definition of the `Argument` inductive type for eBPF expressions.
-/
inductive Argument
  /-- `reg` represents an argument taken from a `Register`. -/
  | reg : Register → Argument
  /-- `imm` represents an argument as an immediate value. -/
  | imm : Val → Argument
  deriving BEq

/--
  Inductive type `Statement` represents eBPF instructions.
-/
inductive Statement
  /-- `add` adds an `Argument` to the value of a `Register`. -/
  | add : Register → Argument → Statement
  /-- `or` performs a bitwise OR between two the value of a `Register` and an `Argument`. -/
  | or : Register → Argument → Statement
  /-- `mov` moves a value from an `Argument` to a `Register`. -/
  | mov : Register → Argument → Statement
  /-- `ja` jumps to a specific offset in the program. -/
  | ja : Int → Statement
  /-- `jeq` jumps if two values are equal. -/
  | jeq : Register → Argument → Int → Statement
  /-- `call` calls a function at a specific offset. -/
  | call : Int → Statement
  /-- `exit` terminates the program or the function call. -/
  | exit : Statement
  deriving Inhabited, BEq

#check Statement.add Register.r0 (Argument.imm 5)

/--
  `Program` is an abbreviation for a list of `Statement`, representing a complete eBPF program.
-/
abbrev Program : Type := List Statement

/--
  A structure `State` that represents the state of the program with registers and program counter.
-/
structure State where
  /-- The program counter (pc) that keeps track of the current position in the program. -/
  pc : Int
  /-- A mapping of `Register` to their values. -/
  reg : Register → Val
instance : Repr State where
  reprPrec s _ :=
    Std.Format.text s!"State.mk {s.pc} <function>"


/--
  A structure `AbsRegisterValue` that represents an abstract register value.
-/
structure AbsRegisterValue where
  /-- Indicates whether the register value is initialized. -/
  is_init : Bool
  /-- An `Intrvl` representing the value range. -/
  i : I
  /-- A `Tnum` representing the unkown bits. -/
  t : Tnum
  deriving Inhabited /- Repr, BEq -/

/--
  A structure `AbsState` that represents the abstract state of the program.
-/
structure AbsState where
  /-- The program counter (pc) that keeps track of the current position in the program. -/
  pc : Int
  /-- A mapping of `Register` to their `AbsRegisterValue`. -/
  reg : Register → AbsRegisterValue
  /-- The stack holding values (used for function calls, etc.). -/
  stack : List Int
  deriving Inhabited
