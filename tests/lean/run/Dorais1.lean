inductive Tree (α : Type _) : Type _
| leaf : α → Tree α
| branch : Tree α → Tree α → Tree α

inductive Path {α : Type _} : Tree α → Type _
| term (x : α) : Path (Tree.leaf x)
| left (tl tr : Tree α) : Path tl → Path (Tree.branch tl tr)
| right (tl tr : Tree α) : Path tr → Path (Tree.branch  tl tr)

section map
variable {α : Type _} {β : Type _} (f : α → β)

protected def Tree.map : Tree α → Tree β
  | Tree.leaf x => Tree.leaf (f x)
  | Tree.branch tl tr => Tree.branch (Tree.map tl) (Tree.map tr)

protected def Path.map : {t : Tree α} → Path t → Path (t.map f)
  | Path.term x        => Path.term (f x)
  | Path.left tl tr p  => Path.left (tl.map f) (tr.map f) (Path.map p)
  | Path.right tl tr p => Path.right (tl.map f) (tr.map f) (Path.map p)

protected def Path.unmap {t : Tree α} (p : Path (t.map f)) : Path t :=
  match t, p with
  | Tree.leaf x,   Path.term _          => Path.term x
  | Tree.branch tl tr, Path.left _ _ p  => Path.left tl tr (Path.unmap p)
  | Tree.branch tl tr, Path.right _ _ p => Path.right tl tr (Path.unmap p)

#print Path.unmap

end map
