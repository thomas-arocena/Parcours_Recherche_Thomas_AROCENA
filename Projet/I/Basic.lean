import Projet.I.Def
import Projet.UInt64.Basic

variable {a b c d : UInt64}
variable {i i₁ i₂ : Intrvl}

namespace I

  theorem empty (i : I): i.is_empty → a ∉ i := by
    intro hp hq
    unfold is_empty at hp -- unfold la def
    dsimp [Membership.mem] at hq -- simplification des eq def
    split at hp  -- split into two cases
    repeat contradiction


  theorem cst_is_const (a : UInt64) : is_const (cst a) := by
    unfold cst is_const
    split
    contradiction
    rw [decide_eq_true_eq]
    admit

end I

/-
namespace Intrvl
  def is_empty ( i : Intrvl) : Bool := i.inf > i.sup
  theorem empty : i.is_empty → a ∉ i := by
    intro hp hq
    unfold is_empty at hp -- unfold la def
    dsimp [instMembershipUInt64, Membership.mem] at hq -- simplification des eq def
    unfold const_is_in at hq
    rw [decide_eq_true_eq] at hp hq -- réécriture
    have := UInt64.le_trans hq.left hq.right
    rw [← UInt64.not_lt] at this
    contradiction

  section Intersect

    theorem intersect_empty (h1 : ¬ i₁.is_empty) (h2 : ¬ i₂.is_empty) (h3 : i₁.sup < i₂.inf) : is_empty (i₁ ∩ i₂) := by
      unfold is_empty
      rw [decide_eq_true_eq]
      dsimp [Inter.inter, intersect]
      have i₂_inf_eq : max i₁.inf i₂.inf = i₂.inf := by
        have i₂_inf_le : i₂.inf ≤ max i₁.inf i₂.inf := by
          --exact le_max_left
          sorry
        sorry
      have i₁_sup_eq : min i₁.sup i₂.sup = i₁.sup := by
        sorry
      rw [i₂_inf_eq, i₁_sup_eq]
      exact h3

    theorem intersect_is_in : (const_is_in i₁ α ∧ const_is_in i₂ α) →  const_is_in (intersect i₁ i₂) α :=
      sorry

    theorem intersect_symm (i₁ i₂ : Intrvl) : intersect i₁ i₂ = intersect i₂ i₁ := by
      --let a := (intersect i₁ i₂).min
    sorry
  end Intersect

  #print intersect_empty

end Intrvl
-/
