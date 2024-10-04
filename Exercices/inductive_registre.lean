/-
def reg_change (scr_number : Nat)(new_data : List Nat) reg :=
reg.Change scr_number new_data-/
structure Register where
  number : Nat
  N_bits : Nat
  data : List Nat
  /-(get_reg : Nat -> List Nat)
  (Register_unicity : ∀ (a b : Nat), (get_reg a = get_reg b) → a = b)-/
def register1 : Register := {number := 1,N_bits:= 32, data :=[00110010,00110010,00110010,00110010]}
def register2 := Register.mk 2 32 [00110010,00110010,00110010,00110010]

#check register2
#check register2.number
#check register2.N_bits
#eval register2.data

#print Register
def add_data(L1 L2 : List Nat) : List Nat := L1 -- POUR LE MOMENT, PAS CORRECT
def sub_data(L1 L2 : List Nat) : List Nat := L1 -- PAREIL

def add_register(src_reg dst_reg : Register) : Register :=
    Register.mk dst_reg.number dst_reg.N_bits (add_data dst_reg.data src_reg.data)

def sub_register(src_reg dst_reg : Register) : Register :=
    Register.mk dst_reg.number dst_reg.N_bits (sub_data dst_reg.data src_reg.data)
