import Mathlib
variable {a b c d : UInt64}

namespace UInt64

  instance : Preorder UInt64 where
  le_refl := by intros a; exact UInt64.le_refl a
  le_trans := by intros a b c hab hbc; exact UInt64.le_trans hab hbc
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le := by intros a b; rfl

  instance : PartialOrder UInt64 where
  le_antisymm := by intro a b hab; exact UInt64.le_antisymm hab

  theorem min_toNat_eq : (min a b).toNat = min a.toNat b.toNat := by
    change (if a ≤ b then a else b).toNat = if a.toNat ≤ b.toNat then a.toNat else b.toNat
    split <;> split <;> trivial

  theorem max_toNat_eq : (max a b).toNat = max a.toNat b.toNat := by
    change (if a ≤ b then b else a).toNat = if a.toNat ≤ b.toNat then b.toNat else a.toNat
    split <;> split <;> trivial

  theorem toNat_add_le_umax (h : a.toNat + b.toNat ≤ UInt64.size-1) : a.toNat + b.toNat = (a + b).toNat := by admit
  theorem toNat_ge_add : (a + b).toNat ≤ a.toNat + b.toNat := by admit

  theorem add_le_add (p : a ≤ b) (q : c ≤ d) (h : b.toNat + d.toNat ≤ UInt64.size-1) : a + c ≤ b + d := by
    apply toNat_add_le_umax at h
    rw [UInt64.le_iff_toNat_le] at p q ⊢
    have h1 := Nat.add_le_add p q
    have h2 :(a + c).toNat ≤ a.toNat + c.toNat := by exact toNat_ge_add
    trans
    · exact h2
    · rw [h] at h1 ; exact h1
  theorem min_le_left : min a b ≤ a := by
    change (min a b).toNat ≤ a.toNat
    rw [UInt64.min_toNat_eq]
    apply Nat.min_le_left

  theorem le_max_left : a ≤ max a b := by
    change  a.toNat ≤ (max a b).toNat
    rw [UInt64.max_toNat_eq]
    apply Nat.le_max_left

  theorem and_zero : a &&& 0 = 0 := by
    simp only [HAnd.hAnd, AndOp.and, land]
    unfold toBitVec
    simp

  theorem zero_and : 0 &&& a = 0 := by
    simp only [HAnd.hAnd, AndOp.and, land]
    unfold toBitVec
    simp

  theorem mod_two_eq_zero_or_one : a % 2 = 0 ∨ a % 2 = 1 := by
    have h : (a % 2).toNat = a.toNat % 2 := UInt64.toNat_mod a 2
    have h' : a.toNat % 2 = 0 ∨ a.toNat % 2 = 1 := Nat.mod_two_eq_zero_or_one (a.toNat)
    rw [← h] at h'
    cases h' with
    | inl hl => exact Or.inl (UInt64.toNat_inj.mp hl)
    | inr hr => exact Or.inr (UInt64.toNat_inj.mp hr)

  theorem and_not_eq_zero (x : UInt64) : x &&& (~~~ x) = 0 := by
    simp only [HAnd.hAnd, AndOp.and, land, Complement.complement, UInt64.complement]
    have : x.toBitVec.and x.toBitVec.not = 0 := by bv_decide
    rw [this]
    trivial

  theorem div_rec_lemma {x y : UInt64} : 0 < y ∧ y ≤ x → x - y < x := by
    rintro ⟨ypos, ylex⟩
    rw [UInt64.sub_def, UInt64.lt_def, UInt64.le_def] at *
    bv_decide

  theorem and_comm {x y : UInt64} : x &&& y = y &&& x := by
    simp only [HAnd.hAnd, AndOp.and, land]
    have :  x.toBitVec.and y.toBitVec =  y.toBitVec.and x.toBitVec := by bv_decide
    rw [this]

  theorem and_assoc {x y z : UInt64} : x &&& y &&& z = x &&& (y &&& z) := by
    simp only [HAnd.hAnd, AndOp.and, land]
    have : (x.toBitVec.and y.toBitVec).and z.toBitVec = x.toBitVec.and (y.toBitVec.and z.toBitVec) := by bv_decide
    rw [this]

  protected def Lshift (x : UInt64) (s : Nat) : UInt64 := UInt64.ofNat (x.toNat <<< s)
  instance : HShiftLeft (UInt64) Nat (UInt64) := ⟨.Lshift⟩

  theorem zero_lshift {k : Nat} : (0 : UInt64) <<< k = 0 := by admit
  theorem lshift_and_comm {k : Nat} : (a <<< k) &&& (b <<< k) = (a &&& b) <<< k := by admit
  theorem lshift_wf (h : a &&& b = 0) : (a <<< k) &&& (b <<< k) = 0 := by
    have : (a <<< k) &&& (b <<< k) = (a &&& b) <<< k := by exact lshift_and_comm
    rw [h] at this
    rw [this]
    exact zero_lshift


  protected def Rshift (x : UInt64) (s : Nat) : UInt64 := UInt64.ofNat (x.toNat >>> s)
  instance : HShiftRight (UInt64) Nat (UInt64) := ⟨.Rshift⟩

  theorem zero_rshift {k : Nat} : (0 : UInt64) >>> k = 0 := by admit
  theorem rshift_and_comm {k : Nat} : (a >>> k) &&& (b >>> k) = (a &&& b) >>> k := by admit

  theorem rshift_wf (h : a &&& b = 0) : (a >>> k) &&& (b >>> k) = 0 := by
    have : (a >>> k) &&& (b >>> k) = (a &&& b) >>> k := by admit
    rw [h] at this
    rw [this]
    exact sorry

/-
  theorem div_eq (x y : UInt64) : x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 := by
  show UInt64.div x y = _
  rw [UInt64.div, BitVec.udiv]
  split
  unfold toBitVec
  sorry


  theorem div_le_self (n k : Nat) : n / k ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [div_eq]
    -- Note: manual split to avoid Classical.em which is not yet defined
    cases (inferInstance : Decidable (0 < k ∧ k ≤ n)) with
    | isFalse h => simp [h]
    | isTrue h =>
      suffices (n - k) / k + 1 ≤ n by simp [h, this]
      have ⟨hK, hKN⟩ := h
      have hSub : n - k < n := sub_lt (Nat.lt_of_lt_of_le hK hKN) hK
      have : (n - k) / k ≤ n - k := ih (n - k) hSub
      exact succ_le_of_lt (Nat.lt_of_le_of_lt this hSub)

theorem div_lt_self {n k : Nat} (hLtN : 0 < n) (hLtK : 1 < k) : n / k < n := by
  rw [div_eq]
  cases (inferInstance : Decidable (0 < k ∧ k ≤ n)) with
  | isFalse h => simp [hLtN, h]
  | isTrue h =>
    suffices (n - k) / k + 1 < n by simp [h, this]
    have ⟨_, hKN⟩ := h
    have : (n - k) / k ≤ n - k := div_le_self (n - k) k
    have := Nat.add_le_of_le_sub hKN this
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hLtK _) this

  theorem bitwise_rec_lemma {n : UInt64} (hNe : n ≠ 0) : n / 2 < n :=
  Nat.div_lt_self (Nat.zero_lt_of_ne_zero hNe) (Nat.lt_succ_self _)

/--
A helper for implementing bitwise operators on `Nat`.

Each bit of the resulting `Nat` is the result of applying `f` to the corresponding bits of the input
`Nat`s, up to the position of the highest set bit in either input.
-/
def bitwise (f : Bool → Bool → Bool) (n m : UInt64) : UInt64 :=
  if n = 0 then
    if f false true then m else 0
  else if m = 0 then
    if f true false then n else 0
  else
    let n' := n / 2
    let m' := m / 2
    let b₁ := n % 2 = 1
    let b₂ := m % 2 = 1
    let r  := bitwise f n' m'
    if f b₁ b₂ then
      r+r+1
    else
      r+r
decreasing_by apply bitwise_rec_lemma; assumption

  theorem and_one_is_mod (x : UInt64) : x &&& 1 = x % 2 := by
  if xz : x = 0 then
    simp [xz, zero_and]
  else
    have andz := (x/2).and_zero
    simp only [HAnd.hAnd, AndOp.and, land] at andz
    simp only [HAnd.hAnd, AndOp.and, land]
    unfold bitwise
    cases mod_two_eq_zero_or_one x with | _ p =>
      simp [xz, p, andz, one_div_two, mod_eq_of_lt]

  theorem b : x &&& 1 = x % 2 := by exact Nat.and_one_is_mod
-/
end UInt64
