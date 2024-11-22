import Projet.Syntaxe_eBPF
import Projet.Semantic_eBPF

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

/-- vR0 is the Verifier that check if Register.reg0 has been initialize-/
def vR0 : Verifier := (fun p : Program => ((p[p.length]!) == Statement.exit))

/-def vStateZero : Verifier :=
    (fun p : Program => (∀ s0 : State , ∃ s1 : State, Semantics p s0 s1))
-/

def vAdd02 : Verifier := (fun p : Program => ((p[1]!) != Statement.add (Argument.reg Register.reg0) Register.reg2))
def vAdd03 : Verifier := (fun p : Program => ((p[1]!) != Statement.add (Argument.reg Register.reg0) Register.reg3))
def vAdd04 : Verifier := (fun p : Program => ((p[1]!) != Statement.add (Argument.reg Register.reg0) Register.reg4))
def vAdd05 : Verifier := (fun p : Program => ((p[1]!) != Statement.add (Argument.reg Register.reg0) Register.reg5))
def vAdd20 : Verifier := (fun p : Program => ((p[1]!) != Statement.add (Argument.reg Register.reg2) Register.reg0))
def vAdd23 : Verifier := (fun p : Program => ((p[1]!) != Statement.add (Argument.reg Register.reg2) Register.reg3))
def vAdd24 : Verifier := (fun p : Program => ((p[1]!) != Statement.add (Argument.reg Register.reg2) Register.reg4))
def vAdd25 : Verifier := (fun p : Program => ((p[1]!) != Statement.add (Argument.reg Register.reg2) Register.reg5))

/-ValidStatement-/

