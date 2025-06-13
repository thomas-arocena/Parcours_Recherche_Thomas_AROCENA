import Projet.Syntaxe_eBPF

abbrev StSet := Set AbsState

structure pStSet where
  n : Nat
  p : StSet
  np : StSet
  wf : ∀ s ∈ (p ∪ np), s.pc = n

instance : EmptyCollection pStSet :=
  ⟨0, ∅ , ∅ , (by intro h; rw [Set.empty_union] ; exact (Set.not_mem_empty h).elim)⟩


structure StTable (p : Program) where
  stTable : List pStSet
  wf : stTable.length = p.length


def empty_StTable (n : Nat) : List pStSet := List.replicate n ∅

def init_StTable (p : Program) (sᵢ : pStSet) : StTable p :=
  if p.length ≥ 1 then
    let l : List pStSet := empty_StTable (p.length - 1)
    ⟨sᵢ :: l , by admit⟩
    else ⟨ [sᵢ], by admit ⟩

abbrev Pindex (p : Program) := Fin p.length
abbrev Lpindex (p : Program) := List (Pindex p)

structure Table (p : Program) where
  stTable : StTable p
  pcTable : Lpindex p

def new_Table (p : Program) (t : Table p) : Table p :=
  match t.pcTable with
    | [] => t
    | u₁ :: rpc =>
      have : u₁ < p.length := by sorry
      let I₁ : Statement := p[u₁]
      sorry
