import Projet.Tnum
import Mathlib
import Projet.UInt64.Basic

abbrev I : Type := Interval UInt64

instance : Membership UInt64 I where
  mem i x :=
    match i with
    | none => False
    | some i => i.fst ≤ x ∧ x ≤ i.snd

abbrev VI (a b : UInt64) (p : a ≤ b) : I := some {fst := a , snd := b , fst_le_snd := p}

namespace I

  def is_empty (i : I) : Bool :=
    match i with
    | ⊥ => True
    | some i => False

  abbrev cst (a : UInt64) : I := Interval.pure a

  def is_const (i : I) : Bool := match i with
    | ⊥ => False
    | some i => i.fst = i.snd

  abbrev pure (a : UInt64) := Interval.pure a
  def i1 : I := pure 5

  def add (i₁ i₂ : I) : I :=
    match i₁ with
    | none => none
    | some i₁ =>
      match i₂ with
      | none => none
      | some i₂ =>
        let h := i₁.snd.toNat + i₂.snd.toNat ≤ UInt64.size - 1
        let j := i₁.fst.toNat + i₂.fst.toNat ≤ UInt64.size - 1
        if h && j then
          some
          { fst := i₁.fst + i₂.fst,
            snd := i₁.snd + i₂.snd,
            fst_le_snd := by
              apply UInt64.add_le_add;
              exact i₁.fst_le_snd;
              exact i₂.fst_le_snd
              admit}
        else
          some
          { fst := 0,
            snd := (UInt64.size - 1).toUInt64,
            fst_le_snd := by admit }

  instance : Add I := ⟨ add ⟩

  def mul (i₁ i₂ : I) : I :=
    match i₁ with
    | none => none
    | some i₁ =>
      match i₂ with
      | none => none
      | some i₂ =>
        let h := i₁.snd.toNat*i₂.snd.toNat ≤ UInt64.size - 1
        let j := i₁.fst.toNat*i₂.fst.toNat ≤ UInt64.size - 1
        if h && j then
          some
          { fst := i₁.fst*i₂.fst,
            snd := i₁.snd*i₂.snd,
            fst_le_snd := by admit }
        else
          some
          { fst := 0,
            snd := (UInt64.size - 1).toUInt64,
            fst_le_snd := by admit }

instance : Mul I := ⟨ mul ⟩

  def or (t : Tnum) (i₁ i₂ : I) : I :=
    match i₁ with
    | none => none
    | some i₁ =>
      match i₂ with
      | none => none
      | some i₂ =>
        some {
          fst := i₁.fst ||| i₂.fst,
          snd := t.v ||| t.m
          fst_le_snd := by admit
        }

  def and (t : Tnum) (i₁ i₂ : I) : I :=
    match i₁ with
    | none => none
    | some i₁ =>
      match i₂ with
      | none => none
      | some i₂ =>
        some {
          fst := t.v,
          snd := i₁.snd &&& i₂.snd,
          fst_le_snd := by admit
        }

  --instance (t : Tnum) : OrOp I := ⟨ or t ⟩

  def is_subset (i₁ i₂ : I) : Bool := match i₁ with
    | ⊥ => True
    | some i₁ => match i₂ with
      | ⊥ => False
      | some i₂ => (i₂.fst ≤ i₁.fst) ∧ (i₁.snd ≤ i₂.snd)

  instance : HasSubset I where
    Subset i₁ i₂ := is_subset i₁ i₂ = true /- NON DECIDABLE -/

  def i₁ : I := VI 2 6 (by trivial)
  def i₂ : I := VI 1 8 (by trivial)


end I
/-
  #check i1 + i1

end I

structure Intrvl where
  inf : UInt64
  sup : UInt64
  deriving BEq

namespace Intrvl


  --Creates a constant `Intrvl` where both `min` and `max` are set to `α`.

  def const (α : UInt64) : Intrvl :=
    { inf := α, sup := α }


    --Checks if an interval is a constant (i.e., `min` and `max` are equal).

  def is_const (i : Intrvl) : Bool :=
    (i.inf == i.sup)


    --Checks if a constant is within an interval i

  def const_is_in (i : Intrvl) (α : UInt64) : Bool :=
    (i.inf <= α) ∧ (α <= i.sup)

  instance : Membership UInt64 Intrvl where
    mem i a := const_is_in i a = true

    --Adds two intervals, combining their respective min and max values.

  def add (i₁ i₂ : Intrvl) : Intrvl :=
    { inf := i₁.inf + i₂.inf, sup := i₁.sup + i₂.sup }

  instance : Add Intrvl := ⟨ add ⟩

    --Multiplies two intervals, multiplying their respective min and max values.

  def mul (i₁ i₂ : Intrvl) : Intrvl :=
    { inf := i₁.inf * i₂.inf, sup := i₁.sup * i₂.sup }

  instance : Mul Intrvl := ⟨ mul ⟩

    --Performs a bitwise AND operation between two intervals, using a `Tnum` result.
    --`t` represents the computed `Tnum` from `tnum_and` applied to both intervals.

  def and (i₁ i₂ : Intrvl) (t : Tnum) : Intrvl :=
    { inf := t.v, sup := min i₁.sup i₂.sup }


    --Performs a bitwise OR operation between two intervals, using a `Tnum` result.
    --`t` represents the computed `Tnum` from `tnum_or` applied to both intervals.

  def or (i₁ i₂ : Intrvl) (t : Tnum) : Intrvl :=
    { inf := max i₁.inf i₂.inf, sup := t.v }


    --Computes the union of two intervals by taking the min and max of both.

  def union (i₁ i₂ : Intrvl) : Intrvl :=
    { inf := min i₁.inf i₂.inf, sup := max i₁.sup i₂.sup }

  instance : Union Intrvl := ⟨ union ⟩

    --Checks if `i₂` is fully contained within `i₁`.

  def is_in (i₁ i₂ : Intrvl) : Bool :=
    (union i₁ i₂ == i₁)

  instance : HasSubset Intrvl where
    Subset i₁ i₂ := is_in i₁ i₂ = true


   -- Computes the intersection of two intervals.

  def intersect (i₁ i₂ : Intrvl) : Intrvl :=
  { inf := max i₁.inf i₂.inf, sup := min i₁.sup i₂.sup }

  instance : Inter Intrvl := ⟨ intersect ⟩

   -- Adjusts the bounds of `i` to exclude a constant `iₐ`, if possible.
    --If `iₐ` is equal to the min or max of `i`, it adjusts the range accordingly.

  def const_bord (i iₐ : Intrvl) : Intrvl :=
    let a := iₐ.inf
    if i.inf == a then
      (if a == i.inf then sorry else { inf := a + 1, sup := i.sup })
    else if i.sup == a then
      { inf := i.inf, sup := a - 1 }
    else
      i

end Intrvl

def i1 : Intrvl := {inf := 2, sup := 5}
def i2 : Intrvl := {inf := 3, sup := 6}
#eval i1 + i2
#eval i1 * i2
#eval i1 ∪ i2
#eval i1 ∩ i2
--#eval i1 ⊆ i2
-/
