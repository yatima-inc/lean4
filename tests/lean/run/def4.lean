inductive Foo : Bool → Type
| Z  : Foo false
| O  : Foo false → Foo true
| E  : Foo true → Foo false

open Foo

def toNat : {b : Bool} → Foo b → Nat
| Z   => 0
| O n => toNat n + 1
| E n => toNat n + 1

example : toNat (E (O Z)) = 2 :=
rfl

example : toNat Z = 0 :=
rfl

example (a : Foo false) : toNat (O a) = toNat a + 1 :=
rfl

example (a : Foo true) : toNat (E a) = toNat a + 1 :=
rfl
