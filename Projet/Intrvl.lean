import Projet.Tnum

/--
  An `Intrvl` (interval) represents a range of possible values, defined by
  a minimum (`min`) and a maximum (`max`).
  This structure is useful for tracking possible value ranges in computations.
-/
structure Intrvl where
  min : UInt64
  max : UInt64
  deriving Repr, Inhabited, BEq

/--
  Creates a constant `Intrvl` where both `min` and `max` are set to `α`.
-/
def intrvl_const (α : UInt64) : Intrvl :=
  { min := α, max := α }

/--
  Adds two intervals, combining their respective min and max values.
-/
def intrvl_add (i₁ i₂ : Intrvl) : Intrvl :=
  { min := i₁.min + i₂.min, max := i₁.max + i₂.max }

/--
  Multiplies two intervals, multiplying their respective min and max values.
-/
def intrvl_mul (i₁ i₂ : Intrvl) : Intrvl :=
  { min := i₁.min * i₂.min, max := i₁.max * i₂.max }

/--
  Performs a bitwise AND operation between two intervals, using a `Tnum` result.
  `t` represents the computed `Tnum` from `tnum_and` applied to both intervals.
-/
def intrvl_and (i₁ i₂ : Intrvl) (t : Tnum) : Intrvl :=
  { min := t.v, max := min i₁.max i₂.max }

/--
  Performs a bitwise OR operation between two intervals, using a `Tnum` result.
  `t` represents the computed `Tnum` from `tnum_or` applied to both intervals.
-/
def intrvl_or (i₁ i₂ : Intrvl) (t : Tnum) : Intrvl :=
  { min := max i₁.min i₂.min, max := t.v }

/--
  Computes the union of two intervals by taking the min and max of both.
-/
def intrvl_union (i₁ i₂ : Intrvl) : Intrvl :=
  { min := min i₁.min i₂.min, max := max i₁.max i₂.max }

/--
  Checks if `i₁` is fully contained within `i₂`.
-/
def intrvl_is_in (i₁ i₂ : Intrvl) : Bool :=
  (intrvl_union i₁ i₂ == i₂)

/--
  Computes the intersection of two intervals. If they do not overlap, the behavior is undefined.
-/
def intrvl_intersec (i₁ i₂ : Intrvl) : Intrvl :=
{ min := max i₁.min i₂.min, max := min i₁.max i₂.max }

/--
  Checks if an interval is a constant (i.e., `min` and `max` are equal).
-/
def intrvl_is_const (i : Intrvl) : Bool :=
  (i.min == i.max)

/--
  Adjusts the bounds of `i` to exclude a constant `iₐ`, if possible.
  If `iₐ` is equal to the min or max of `i`, it adjusts the range accordingly.
-/
def intrvl_const_bord (i iₐ : Intrvl) : Intrvl :=
  let a := iₐ.min
  if i.min == a then
    (if a == i.max then sorry else { min := a + 1, max := i.max })
  else if i.max == a then
    { min := i.min, max := a - 1 }
  else
    i
