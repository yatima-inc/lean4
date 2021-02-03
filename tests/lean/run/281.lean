inductive V (α : Bool → Type) : Bool → Type
  | mk₁ {b} : α true → V α b
  | mk₂ : V α false → V α false

def V.map {α β} (f : (b : Bool) → α b → β b) : {b : Bool} → V α b → V β b
  | mk₁ x => mk₁ (f true x)
  | mk₂ e => mk₂ (e.map f)
