inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)

def Nat.add' : Nat → Nat → Nat
  | 0,      b => b
  | succ a, b => succ (add' a b)

def Vec.map (f : α → β) : {n : Nat} → Vec α n → Vec β n
  | nil       => nil
  | cons a as => cons (f a) (map f as)

def Vec.append : {n : Nat} → Vec α n → {m : Nat} → Vec α m → Vec α (Nat.add' n m)
  | nil,       bs => bs
  | cons a as, bs => cons a (append as bs)

def Vec.map2 (f : α → β) (as : Vec α n) : Vec β n :=
  loop as
where
  loop : {n : Nat} → Vec α n → Vec β n
    | nil       => nil
    | cons a as => cons (f a) (loop as)

def Vec.head (as : Vec α (n+1)) : α :=
  let aux : {n : Nat} → Vec α (n+1) → α
    | cons a _ => a
  aux as
