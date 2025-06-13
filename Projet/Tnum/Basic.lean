import Projet.Tnum.Def

open Tnum
  section const
    def const_only (t : Tnum) (α : UInt64): is_const t → (const_is_in t α → α = t.v)  := by
    sorry

    #print const_only
  end const

  section shift

    theorem rshift_leq (t : Tnum) :  t.gval > (t >>> 1).gval := by
      sorry

    theorem lshift_geq (t : Tnum) : (t >>> 1).gval > t.gval ∨ (t >>> 1).gval = 0 := by
      sorry
  end shift

  section and
    theorem and_symm (t₁ t₂ : Tnum) : and t₁ t₂ = and t₂ t₁ := by
      unfold Tnum.and
      sorry

    theorem and_leq (t₁ t₂ : Tnum) : (t₁ &&& t₂).gval < t₁.gval := by
      sorry
  end and

  section or
    theorem or_symm (t₁ t₂ : Tnum) : t₁ ||| t₂ = t₂ ||| t₁ := by
      sorry

    theorem or_geq (t₁ t₂ : Tnum) : (t₁ ||| t₂).gval > t₁.gval := by
      sorry
  end or
