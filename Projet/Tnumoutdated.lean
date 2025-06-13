/--
  A `Tnum` (tristate number) represents a value with potential uncertainty.
  It consists of a value (`v`) and a mask (`m`), where the mask indicates bits that may vary.
  This structure is useful for modeling computations where some bits may be unknown or variable.
-/
structure Tnum where
  v : UInt64
  m : UInt64
  deriving Repr, Inhabited, BEq

/--
  Creates a constant `Tnum` with the given value `α` and a zero mask.
-/
def tnum_const (α : UInt64) : Tnum :=
  { v := α, m := 0 }

/--
  Left shifts the `Tnum` by `k` bits, shifting both the value and mask.
-/
def tnum_lshift (t : Tnum) (k : Nat) : Tnum :=
  { v := t.v <<< k.toUInt64, m := t.m <<< k.toUInt64 }

/--
  Right shifts the `Tnum` by `k` bits, shifting both the value and mask.
-/
def tnum_rshift (t : Tnum) (k : Nat) : Tnum :=
  { v := t.v >>> k.toUInt64, m := t.m >>> k.toUInt64 }

/--
  Performs a bitwise AND operation between two `Tnum` values,
  correctly handling uncertainty propagation.
-/
def tnum_and (t₁ t₂ : Tnum) : Tnum :=
  let α := t₁.v ||| t₁.m
  let β := t₂.v ||| t₂.m
  let val := t₁.v &&& t₂.v
  { v := val, m := α &&& β &&& (~~~val) }

/--
  Performs a bitwise OR operation between two `Tnum` values.
-/
def tnum_or (t₁ t₂ : Tnum) : Tnum :=
  let val := t₁.v ||| t₂.v
  let μ := t₁.m ||| t₂.m
  { v := val, m := μ &&& (~~~val) }

/--
  Performs a bitwise XOR operation between two `Tnum` values.
-/
def tnum_xor (t₁ t₂ : Tnum) : Tnum :=
  let val := t₁.v ^^^ t₂.v
  let μ := t₁.m ||| t₂.m
  { v := val &&& (~~~μ), m := μ }

/--
  Adds two `Tnum` values while correctly handling uncertainty propagation.
-/
def tnum_add (t₁ t₂ : Tnum) : Tnum :=
  let sᵥ := t₁.v + t₂.v
  let sₘ := t₁.m + t₂.m
  let S := sᵥ + sₘ
  let q := S ^^^ sᵥ
  let h := q ||| t₁.m ||| t₂.m
  { v := sᵥ &&& (~~~h), m := h }

/--
  Multiplies two `Tnum` values, ensuring uncertainty is properly accounted for.
--/
def tnum_mul (t₁ t₂ : Tnum) : Tnum :=
  let val := t₁.v * t₂.v
  let mask := { v := 0, m := 0 }
  let rec loop (t₁ t₂ mask : Tnum) : Tnum :=
    if t₁.v = 0 ∧ t₁.m = 0 then mask
    else
      let mask :=
        if t₁.v &&& 1 = 1 then tnum_add mask { v := 0, m := t₂.m }
        else if t₁.m &&& 1 = 1 then tnum_add mask { v := 0, m := t₂.v ||| t₂.m }
        else mask
      loop (tnum_rshift t₁ 1) (tnum_lshift t₂ 1) mask
  termination_by (t₁.v ||| t₁.m)
  decreasing_by
    all_goals simp_wf
    · dsimp [tnum_rshift, UInt64.toNat]
      admit

  tnum_add { v := val, m := 0 } (loop t₁ t₂ mask)

/--
  Computes the union of two `Tnum` values, merging value and mask appropriately.
-/
def tnum_union (t₁ t₂ : Tnum) : Tnum :=
  { v := t₁.v &&& t₂.v, m := t₁.m ||| t₂.m ||| (t₁.v ^^^ t₂.v) }

/--
  Checks if `t₁` is within the possible values of `t₂`.
-/
def tnum_is_in (t₁ t₂ : Tnum) : Bool :=
  (tnum_union t₁ t₂ == t₂)

/--
  Computes the intersection of two `Tnum` values, ensuring consistency.
-/
def tnum_intersect (t₁ t₂ : Tnum) : Tnum :=
  if ((t₁.v &&& t₂.m) ||| t₂.v) == ((t₂.v &&& t₁.m) ||| t₁.v) then
    { v := t₁.v ||| t₂.v, m := t₁.m &&& t₂.m }
  else
    sorry

/--
  Checks if a `Tnum` is a constant (i.e., has no uncertain bits).
-/
def tnum_is_const (t : Tnum) : Bool :=
  (t.m == 0)

/--
  Adjusts `t` to match the constant bounds defined by `tₐ`.
  `tₐ` is assumed to be a constant `Tnum`.
-/
def tnum_const_bord (t tₐ : Tnum) : Tnum :=
  if (t.v ||| t.m) == (tₐ.v ||| t.m) then
    { v := t.v ||| (t.m &&& (~~~tₐ.v)), m := 0 }
  else
    t


#eval tnum_const (5 : UInt64) /- Correct -/
#eval tnum_lshift (tnum_const (5 : UInt64)) 1 /- Correct -/
#eval tnum_rshift (tnum_const (5 : UInt64)) 1 /- Correct -/
def t₁ : Tnum := {v := 1 , m := 6}
def t₂ : Tnum := {v := 5 , m := 2}
#eval tnum_add t₁ t₂ /- Correct -/
#eval tnum_and t₁ t₂ /- Correct -/
#eval tnum_or t₁ t₂ /- Correct -/
#eval tnum_xor t₁ t₂ /- Correct -/
#eval! tnum_mul t₁ t₂ /- Correct -/
#eval tnum_const_bord ({v := 25 , m:= 36}) (tnum_const 57) /- Correct-/
#eval tnum_is_in ({v := 3 , m := 4}) ({v:= 1 , m:= 6}) /- Correct -/
