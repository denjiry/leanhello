def hello := "world"

axiom A : Prop
def claim: Prop := ∀ (x: A), A

def ja (_s : String) : Prop :=
  claim

theorem test : ja "あああ" := by
  intro a; exact a

unsafe
def lbUnsafe (japanese: String) : Prop :=
  True

@[implementedBy lbUnsafe]
def lb (japanese : String) : Prop :=
  claim

theorem t2 : lb "あああああ" := by
  intro a;
