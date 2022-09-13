def hello := "world"

axiom A : Prop
def claim: Prop := ∀ (x: A), A
#check claim

def ja (_s : String) : Prop :=
  claim

#check ja

def claim2 := ja "hello"

theorem test : ja "あああ" := by
  intro a; exact a
