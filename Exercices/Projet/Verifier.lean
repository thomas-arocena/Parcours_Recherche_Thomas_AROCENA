import Projet.Syntaxe_eBPF

/-- Verifier is the Type of function from Program to Bool-/
abbrev Verifier : Type := Program -> Bool

/-- For each verifier, ValidProgram return the subType of Program that pass the verifier-/
def ValidProgram (v : Verifier) : Type := {val : Program // v val}

/-- interVerifier is a function from (Verifier x Verifier) to Verifier that takes two Verifier v1 and v2 and return the Verifier v1*v2 : p -> (v1(p) and v2(p)) -/
def interVerifier(v1 v2 : Verifier) : Verifier := fun p : Program => (v1 p) ∧ (v2 p)

/-- v_trivial is the Verifier always equal to true-/
def v_trivial : Verifier := (fun p : Program => true)


#eval v_trivial [Statement.exit]
#check [Statement.exit]
#check ValidProgram v_trivial
#eval [Statement.exit].length

/- The idea is to decompose eBPF verifier into small Verifier vk and then use interVerifier to built the complete verifier V and then use ValidProgram V to have the type of valid programm in eBPF-/

/-- vExit is the Verifier that check if the last Statement is exit-/
def vExit : Verifier := (fun p : Program => ((p[p.length]!) == Statement.exit))

def vR0 : Verifier := (fun p : Program => ((p[p.length]!) == Statement.exit))
