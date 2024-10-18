def hello := "world"
/- Define some constants. -/

variable (p q r : Prop)

-- commutativity of ∧
example : (p ∧ q ↔ q ∧ p) :=
Iff.intro
  (fun h : p ∧ q => show q ∧ p from And.intro (And.right h) (And.left h))
  (fun h : q ∧ p => show p ∧ q from And.intro (And.right h) (And.left h))

example : p ∧ q ↔ q ∧ p := --simplified version
Iff.intro
  (fun h => And.intro (h.right) (h.left))
  (fun h => And.intro (h.right) (h.left))

-- commutativity of ∨
example : p ∨ q ↔ q ∨ p :=
Iff.intro
  (fun h : p ∨ q =>
  show q ∨ p from Or.elim h
    (fun h₁:p => show q ∨ p from Or.intro_right q h₁)
    (fun h₂:q => show q ∨ p from Or.intro_left p h₂))
  (fun h : q ∨ p =>
  show p ∨ q from Or.elim h
    (fun h₁: q => show p ∨ q from Or.intro_right p h₁)
    (fun h₂: p => show p ∨ q from Or.intro_left q h₂))

example : p ∨ q ↔ q ∨ p := --simplified version
Iff.intro
  (fun h => Or.elim h (fun h₁ => Or.intro_right q h₁) (fun h₂ => Or.intro_left p h₂))
  (fun h => Or.elim h (fun h₁ => Or.intro_right p h₁) (fun h₂ => Or.intro_left q h₂))

-- associativity of ∧
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
Iff.intro
  (fun h : (p ∧ q) ∧ r => show p ∧ (q ∧ r) from And.intro
    (And.left (And.left h))
    (And.intro (And.right (And.left h)) (And.right h)))
  (fun h : p ∧ (q ∧ r) => show (p ∧ q) ∧ r from And.intro
    (And.intro (And.left h) (And.left (And.right h)))
    (And.right (And.right h)))

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := --simplified version
Iff.intro
  (fun h => ⟨ h.left.left , ⟨ h.left.right , h.right ⟩ ⟩)
  (fun h => ⟨ ⟨ h.left, h.right.left ⟩ , h.right.right ⟩)


-- associativity of ∨
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
Iff.intro
  (fun h : (p ∨ q) ∨ r => show p ∨ (q ∨ r) from Or.elim h
    (fun h₁ : p ∨ q => show p ∨ (q ∨ r) from Or.elim h₁
      (fun hp : p => show p ∨ (q ∨ r) from Or.intro_left (q ∨ r) hp)
      (fun hq : q => show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_left r hq))
      )
    (fun h₂ : r => show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_right q h₂))
    )
  (fun h : p ∨ (q ∨ r) => show (p ∨ q) ∨ r from Or.elim h
    (fun h₁ : p => show (p ∨ q) ∨ r from Or.intro_left r (Or.intro_left q h₁))
    (fun h₂ : q ∨ r => show (p ∨ q) ∨ r from Or.elim h₂
      (fun hq : q => show (p ∨ q) ∨ r from Or.intro_left r (Or.intro_right p hq))
      (fun hr : r => show (p ∨ q) ∨ r from Or.intro_right (p ∨ q) hr )
    )
   )

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := --simplified version
Iff.intro
  (fun h => h.elim
    (fun h₁ => h₁.elim
      (fun hp => Or.inl hp)
      (fun hq => Or.inr (Or.inl hq))
      )
    (fun h₂ => Or.inr (Or.inr h₂))
    )
  (fun h => h.elim
    (fun h₁ => Or.inl (Or.inl h₁))
    (fun h₂ => h₂.elim
      (fun hq  => Or.inl (Or.inr hq))
      (fun hr  => Or.inr hr)
    )
   )
-- distributivity
open Classical

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
Iff.intro
(fun h : p ∧ (q ∨ r) => show (p ∧ q) ∨ (p ∧ r) from
  Or.elim (em q)
  (fun hq₁ : q => show (p ∧ q) ∨ (p ∧ r) from Or.intro_left (p ∧ r) (And.intro (And.left h) hq₁))
  (fun hnq : ¬q => show (p ∧ q) ∨ (p ∧ r) from Or.elim (And.right h)
    (fun hq₂ : q => show (p ∧ q) ∨ (p ∧ r) from Or.intro_right (p ∧ q) (absurd hq₂ hnq))
    (fun hr : r => show (p ∧ q) ∨ (p ∧ r) from Or.intro_right (p ∧ q) (And.intro (And.left h) hr))
  )
)
(fun h : (p ∧ q) ∨ (p ∧ r) => show p ∧ (q ∨ r) from
  And.intro
  (show p from (Or.elim h
    (fun h : (p ∧ q) => show p from (And.left h))
    (fun h : (p ∧ r) => show p from (And.left h))
    )
  )
  (show (q ∨ r) from (Or.elim h
    (fun h : (p ∧ q) => show (q ∨ r) from Or.intro_left r (And.right h))
    (fun h : (p ∧ r) => show (q ∨ r) from Or.intro_right q (And.right h))
    )
  )
)

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := --simplified version
Iff.intro
(fun h => (em q).elim
  (fun hq₁ => Or.inl ⟨h.left , hq₁⟩)
  (fun hnq => h.right.elim
    (fun hq₂ => Or.inr (absurd hq₂ hnq))
    (fun hr => Or.inr ⟨h.left , hr⟩)
  )
)
(fun h =>
  ⟨h.elim (fun h => h.left) (fun h => h.left),
  h.elim (fun h => Or.inl (h.right)) (fun h => Or.inr (h.right))⟩
)

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := --without Classical
Iff.intro
(fun h : p ∧ (q ∨ r) => show (p ∧ q) ∨ (p ∧ r) from Or.elim (And.right h)
 (fun hq : q => show (p ∧ q) ∨ (p ∧ r) from Or.intro_left (p ∧ r) (And.intro h.left hq))
 (fun hr : r => show (p ∧ q) ∨ (p ∧ r) from Or.intro_right (p ∧ q) (And.intro h.left hr))
)
(fun h : (p ∧ q) ∨ (p ∧ r) => show p ∧ (q ∨ r) from
  And.intro
  (show p from (Or.elim h
    (fun h : (p ∧ q) => show p from (And.left h))
    (fun h : (p ∧ r) => show p from (And.left h))
    )
  )
  (show (q ∨ r) from (Or.elim h
    (fun h : (p ∧ q) => show (q ∨ r) from Or.intro_left r (And.right h))
    (fun h : (p ∧ r) => show (q ∨ r) from Or.intro_right q (And.right h))
    )
  )
)

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := --without Classical simplfied version
Iff.intro
(fun h => h.right.elim
 (fun hq => Or.inl ⟨h.left , hq⟩)
 (fun hr => Or.inr ⟨h.left , hr⟩)
)
(fun h =>
  ⟨h.elim (fun h => h.left) (fun h => h.left),
  h.elim (fun h => Or.inl (h.right)) (fun h => Or.inr (h.right))⟩
)

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
Iff.intro
(fun h =>
  ⟨h.elim (fun hp => Or.inl hp) (fun hqr => Or.inr (hqr.left)),
   h.elim (fun hp => Or.inl hp) (fun hqr => Or.inr (hqr.right))⟩
)
(fun h => h.left.elim
  (fun hp => Or.inl hp)
  (fun hq => h.right.elim
    (fun hp => Or.inl hp)
    (fun hr => Or.inr ⟨hq , hr⟩)
  )
)

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
Iff.intro
  (fun h => (fun hpq => (h hpq.left) hpq.right))
  (fun h => fun hp => fun hq => h ⟨hp,hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
Iff.intro
  (fun h : ((p ∨ q) → r) => show (p → r) ∧ (q → r) from ⟨
    (fun hp => h (Or.inl hp)),
    (fun hq => h (Or.inr hq))
  ⟩)
  (fun h =>
    (fun hpq => hpq.elim (fun hp => h.left hp) (fun hq => h.right hq))
  )

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
Iff.intro
  (fun h => ⟨fun hp => h (Or.inl hp) , fun hq => h (Or.inr hq)⟩)
  (fun h =>
    (fun hpq => hpq.elim (fun hp => h.left hp) (fun hq => h.right hq))
  )

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
(fun h₁ : ¬p ∨ ¬q => (fun h₂ => h₁.elim
  (fun hnp => absurd h₂.left hnp)
  (fun hnq => absurd h₂.right hnq))
)

example : ¬(p ∧ ¬p) := (fun h => absurd h.left h.right)

example : p ∧ ¬q → ¬(p → q) :=
(fun h₁ => fun h₂ => absurd (h₂ h₁.left) h₁.right)

example : ¬p → (p → q) := (fun hnp => fun hp => absurd hp hnp)

example : (¬p ∨ q) → (p → q) :=
(fun h => fun hp => h.elim
  (fun hnp => absurd hp hnp)
  (fun hq => hq)
)

example : p ∨ False ↔ p :=
Iff.intro
  (fun h => h.elim
    (fun hp => hp)
    (fun hfalse => hfalse.elim)
  )
  (fun hp => Or.inl hp)

example : p ∧ False ↔ False :=
Iff.intro (fun h₁ => h₁.right) (fun h₂ => ⟨h₂.elim,h₂⟩)

example : (p → q) → (¬q → ¬p) :=
(fun h => fun hnq => fun hp => absurd (h hp) hnq)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
fun h => (em q).elim
  (fun hq => Or.inl (fun hp => hq))
  (fun hnq => Or.inr (fun hp => (h hp).elim
    (fun hq => absurd hq hnq)
    (fun hr => hr)))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  (fun h => (em p).elim
    (fun hp => Or.inr (fun hq => absurd ⟨hp , hq⟩ h ))
    (fun hnp => Or.inl hnp)
  )

example : (p → q) → (¬p ∨ q) :=
(fun hpq => byCases
  (fun hp => Or.inr (hpq hp))
  (fun hnp => Or.inl hnp))

example : (¬q → ¬p) → (p → q) :=
(fun h : (¬q → ¬p) => show (p → q) from byCases
  (fun hq => (fun hp => hq))
  (fun hnq => (fun hp => absurd hp (h hnq))))

example : p ∨ ¬p := byCases
(fun hp => Or.inl hp)
(fun hnp => Or.inr hnp)

/-
example : (((p → q) → p) → p) :=
(fun h : ((p → q) → p) => show p from byCases
  (fun hq => h (fun hp => hq))
  (fun hnq => sorry))

example : ¬(p → q) → p ∧ ¬q :=
  (fun h => ⟨
    show p from (em q).elim
      (fun hq => show p from absurd (fun hp => hq) h)
      (fun hnq => (em p).elim
        (fun hp => hp)
        (fun hnp => sorry)

      )
    ,
  sorry⟩)

-/
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
(fun h : (∃ x : α, r) => show r from h.elim (fun h => (fun hw : r => show r from hw)))

example (a : α) : r → (∃ x : α, r) := (fun r => ⟨a , r⟩)
/-
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
Iff.intro
(fun h₁ : (∃ x, p x ∧ r) =>
And.intro
  (show (∃ x, p x) from (sorry))
  (sorry)
)
(fun h₂ : (∃ x, p x) ∧ r => sorry)


example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
-/

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

theorem test2 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁

example : 3 = 3 := by
  generalize 3 = x
  -- goal is x : Nat ⊢ x = x
  revert x
  -- goal is ⊢ ∀ (x : Nat), x = x
  intro y
  -- goal is y : Nat ⊢ y = y
  rfl
