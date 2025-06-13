import Mathlib
import Projet.UInt64.Basic

/--
  A `Tnum` (tristate number) represents a value with potential uncertainty.
  It consists of a value (`v`) and a mask (`m`), where the mask indicates bits that may vary.
  This structure is useful for modeling computations where some bits may be unknown or variable.
-/


structure Tnum where
  v : UInt64
  m : UInt64
  wf : v &&& m = 0
  deriving Repr, BEq

instance : Inhabited Tnum := ⟨0 , 0 , refl 0⟩
instance : Membership UInt64 Tnum where
  mem t a := a &&& (~~~t.m) = t.v

instance (a : UInt64) (t : Tnum) : Decidable (a ∈ t) :=
  inferInstanceAs (Decidable (a &&& (~~~t.m) = t.v))

def t : Tnum := ⟨5, 2, by trivial⟩
#eval 5 ∈ t
namespace Tnum
/--
  Creates a constant `Tnum` with the given value `α` and a zero mask.
-/
def gval (t : Tnum) : UInt64 := t.v &&& t.m

def const (a : UInt64) : Tnum where
  v := a
  m := 0
  wf := by exact UInt64.and_zero

def lshift (t : Tnum) (k : Nat) : Tnum where
  v := t.v <<< k.toUInt64
  m := t.m <<< k.toUInt64
  wf : t.v <<< k.toUInt64 &&& t.m <<< k.toUInt64 = 0 := by apply UInt64.lshift_wf; exact t.wf

instance : HShiftLeft Tnum Nat Tnum := ⟨lshift⟩


def rshift (t : Tnum) (k : Nat) : Tnum where
  v := t.v >>> k.toUInt64
  m := t.m >>> k.toUInt64
  wf : t.v >>> k.toUInt64 &&& t.m >>> k.toUInt64 = 0 := by apply UInt64.rshift_wf; exact t.wf

instance : HShiftRight Tnum Nat Tnum := ⟨rshift⟩
/--
  Left shifts the `Tnum` by `k` bits, shifting both the value and mask.
-/

/-
  Right shifts the `Tnum` by `k` bits, shifting both the value and mask.
-/

/-
  Performs a bitwise AND operation between two `Tnum` values,
  correctly handling uncertainty propagation.
-/
def and (t₁ t₂ : Tnum) : Tnum :=
  let α := t₁.v ||| t₁.m
  let β := t₂.v ||| t₂.m
  let val := t₁.v &&& t₂.v
  { v := val, m := α &&& β &&& (~~~val),
    wf := by
      have : α &&& β &&& (~~~val) = (~~~val) &&& α &&& β := by rw [UInt64.and_comm, UInt64.and_assoc]
      rw [this, ← UInt64.and_assoc,  ← UInt64.and_assoc]
      rw [UInt64.and_not_eq_zero, UInt64.zero_and, UInt64.zero_and]
  }

instance : AndOp Tnum := ⟨ and ⟩
/--
  Performs a bitwise OR operation between two `Tnum` values.
-/
def or (t₁ t₂ : Tnum) : Tnum :=
  let val := t₁.v ||| t₂.v
  let μ := t₁.m ||| t₂.m
  { v := val, m := μ &&& (~~~val),
    wf := by
      have : val &&& (μ &&& ~~~val) = ~~~val &&& val &&& μ:= by rw [← UInt64.and_assoc, UInt64.and_comm, ← UInt64.and_assoc]
      have h : ~~~val &&& val = 0 := by rw [UInt64.and_comm, UInt64.and_not_eq_zero]
      rw [this, h, UInt64.zero_and]
  }

instance : OrOp Tnum := ⟨ or ⟩
/--
  Performs a bitwise XOR operation between two `Tnum` values.
-/

def xor (t₁ t₂ : Tnum) : Tnum :=
  let val := t₁.v ^^^ t₂.v
  let μ := t₁.m ||| t₂.m
  { v := val &&& (~~~μ), m := μ,
    wf := by
      rw [UInt64.and_assoc]
      have : ~~~μ &&& μ = 0 := by rw [UInt64.and_comm, UInt64.and_not_eq_zero]
      rw [this, UInt64.and_zero]
  }

instance : Xor Tnum := ⟨ xor ⟩
/--
  Adds two `Tnum` values while correctly handling uncertainty propagation.
-/
def add (t₁ t₂ : Tnum) : Tnum :=
  let sᵥ := t₁.v + t₂.v
  let sₘ := t₁.m + t₂.m
  let S := sᵥ + sₘ
  let q := S ^^^ sᵥ
  let h := q ||| t₁.m ||| t₂.m
  { v := sᵥ &&& (~~~h), m := h,
    wf := by
      rw [UInt64.and_assoc]
      have : ~~~h &&& h = 0 := by rw [UInt64.and_comm, UInt64.and_not_eq_zero]
      rw [this, UInt64.and_zero]
  }

instance : Add Tnum := ⟨ add ⟩
/--
  Multiplies two `Tnum` values, ensuring uncertainty is properly accounted for.
--/
def mul (t₁ t₂ : Tnum) : Tnum :=
  let val := t₁.v * t₂.v
  let mask := { v := 0, m := 0 ,wf := by admit}
  let rec loop (t₁ t₂ mask : Tnum) : Tnum :=
    if t₁.v = 0 ∧ t₁.m = 0 then mask
    else
      let mask :=
        if t₁.v &&& 1 = 1 then mask + { v := 0, m := t₂.m , wf := by rw [UInt64.zero_and]}
        else if t₁.m &&& 1 = 1 then mask + { v := 0, m := t₂.v ||| t₂.m, wf := by rw [UInt64.zero_and]}
        else mask
      loop (rshift t₁ 1) (lshift t₂ 1) mask
  termination_by (t₁.v ||| t₁.m)
  decreasing_by
    all_goals simp_wf
    · dsimp [rshift, UInt64.toNat]
      admit

  { v := val, m := 0 , wf := by rw [UInt64.and_zero]} + (loop t₁ t₂ mask)

instance : Mul Tnum := ⟨ mul ⟩
/--
  Computes the union of two `Tnum` values, merging value and mask appropriately.
-/
def union (t₁ t₂ : Tnum) : Tnum :=
  { v := t₁.v &&& t₂.v, m := t₁.m ||| t₂.m ||| (t₁.v ^^^ t₂.v), wf := by admit}

instance : Union Tnum := ⟨ union ⟩
/--
  Checks if `t₂` is within the possible values of `t₁`.
-/
def is_in (t₁ t₂ : Tnum) : Bool :=
  (union t₁ t₂ == t₁)

instance : HasSubset Tnum where
  Subset t₁ t₂ := is_in t₁ t₂ = true
/--
  Computes the intersection of two `Tnum` values, ensuring consistency.
-/
def intersect (t₁ t₂ : Tnum) : Tnum :=
  if ((t₁.v &&& t₂.m) ||| t₂.v) == ((t₂.v &&& t₁.m) ||| t₁.v) then
    { v := t₁.v ||| t₂.v, m := t₁.m &&& t₂.m , wf := by admit}
  else
    sorry

instance : Inter Tnum := ⟨intersect⟩
/--
  Checks if a `Tnum` is a constant (i.e., has no uncertain bits).
-/
def is_const (t : Tnum) : Bool :=
  (t.m == 0)

def const_is_in (t : Tnum) (α : UInt64) : Bool :=
  (α ^^^ (~~~t.m)) = t.v

instance : Membership UInt64 Tnum where
  mem t a := const_is_in t a = true


def sup (t : Tnum) : UInt64 := (t.v ||| t.m)

def inf (t : Tnum) : UInt64 := t.v
/--
  Adjusts `t` to match the constant bounds defined by `tₐ`.
  `tₐ` is assumed to be a constant `Tnum`.
-/
def const_bord (t tₐ : Tnum) : Tnum :=
  if (t.v ||| t.m) == (tₐ.v ||| t.m) then
    { v := t.v ||| (t.m &&& (~~~tₐ.v)), m := 0 , wf := by admit}
  else
    t


#eval const (5 : UInt64) /- Correct -/
#check lshift (const (5 : UInt64)) 1 /- Correct -/
#check rshift (const (5 : UInt64)) 1 /- Correct -/
def t₁ : Tnum := {v := 1 , m := 6 , wf := by admit}
def t₂ : Tnum := {v := 5 , m := 2 , wf := by admit}
#check add t₁ t₂ /- Correct -/
#check and t₁ t₂ /- Correct -/
#check or t₁ t₂ /- Correct -/
#check xor t₁ t₂ /- Correct -/
#eval! mul t₁ t₂ /- Correct -/
#check const_bord ({v := 25 , m:= 36 , wf := by admit}) (const 57) /- Correct-/
#check is_in ({v := 3 , m := 4 , wf := by admit}) ({v:= 1 , m:= 6 , wf := by admit}) /- Correct -/

end Tnum
