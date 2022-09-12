def hello := "world"

axiom A : Type
axiom Blue : A -> Prop
def claim: Prop := ∀ (x: A), Blue x
#check claim

def ja (_s : String) : Prop :=
  True

#check ja

def claim2 := ja "hello"
