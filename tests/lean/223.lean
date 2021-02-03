universes u v

inductive Imf {α : Type u} {β : Type v} (f : α → β) : β → Type (max u v)
| mk : (a : α) → Imf f (f a)

def h {α β} {f : α → β} : {b : β} → Imf f b → α
| Imf.mk a => a

#print h

theorem ex : {α β : Sort u} → (h : α = β) → (a : α) → cast h a ≅ a
  | rfl, a => HEq.refl a

#print ex
