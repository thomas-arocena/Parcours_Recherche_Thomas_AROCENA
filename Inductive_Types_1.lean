namespace Hidden
inductive Bool where
| false : Bool
| true : Bool
deriving Repr


namespace Bool
def and (a b : Bool) : Bool :=
  match a with
  |true => b
  |false => false

def or (a b : Bool) : Bool :=
  match a with
  |true => true
  |false => b

def not (a : Bool) : Bool :=
  match a with
  |true => false
  |false => true

#check Bool.false
#check Bool.true
#eval and false true
#eval and false false
#eval and true true
#eval and true false
#eval or false true
#eval or false false
#eval or true true
#eval or true false
