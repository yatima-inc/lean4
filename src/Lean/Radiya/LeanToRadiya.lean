import Lean.Radiya.Expr
import Lean.Expr

namespace List

def getIdxEx {A : Type u} [BEq A] (as : List A) (a : A) : Nat :=
  let rec aux (as : List A) (a : A) (i : Nat) : Nat :=
    match as with
    | a' :: as' => if a == a' then i else aux as' a' (i+1)
    | [] => panic! "List does not contain value"
  aux as a 0

end List

namespace Lean.Radiya

abbrev ConstMap := Nat

def nameToCid (nam : Name) : Cid := panic! "TODO"

def findConstInfo (nam : Name) (constMap : ConstMap) : Const :=
  Const.theoremC (TheoremC.mk 0 (panic! "TODO") (panic! "TODO"))

def leanLevelToRadiya (levelParams : List Name) (lvl : Lean.Level) : Univ :=
  match lvl with
  | Lean.Level.zero _ => Univ.zero
  | Lean.Level.succ n _ => Univ.succ (leanLevelToRadiya levelParams n)
  | Lean.Level.max a b _ => Univ.max (leanLevelToRadiya levelParams a) (leanLevelToRadiya levelParams b)
  | Lean.Level.imax a b _ => Univ.imax (leanLevelToRadiya levelParams a) (leanLevelToRadiya levelParams b)
  | Lean.Level.param nam _ => Univ.param (List.getIdxEx levelParams nam)
  | Lean.Level.mvar _ _ => panic! "Unfilled level metavariable"

def leanExprToRadiya (lean : Lean.Expr) (constMap : ConstMap) (levelParams : List Name) : Expr :=
  match lean with
  | Lean.Expr.bvar idx _ => Expr.var idx
  | Lean.Expr.sort lvl _ => Expr.sort (leanLevelToRadiya levelParams lvl)
  | Lean.Expr.const nam lvls _ => Expr.const (findConstInfo nam constMap) (List.map (leanLevelToRadiya levelParams) lvls)
  | Lean.Expr.app fnc arg _ => Expr.app (leanExprToRadiya fnc constMap) (leanExprToRadiya arg constMap)
  | Lean.Expr.lam _ bnd bod _ => Expr.lam (leanExprToRadiya bnd constMap) (leanExprToRadiya bod constMap)
  | Lean.Expr.forallE _ dom img _ => Expr.pi (leanExprToRadiya dom constMap) (leanExprToRadiya img constMap)
  | Lean.Expr.letE _ typ exp bod _ =>
    Expr.letE (leanExprToRadiya typ constMap) (leanExprToRadiya exp constMap) (leanExprToRadiya bod constMap)
  | Lean.Expr.lit lit _ => Expr.lit lit
  | Lean.Expr.mdata _ e _ => leanExprToRadiya e constMap
  | Lean.Expr.proj .. => panic! "Projections TODO"
  | Lean.Expr.fvar .. => panic! "Unbound variable"
  | Lean.Expr.mvar .. => panic! "Unfilled metavariable"

end Lean.Radiya
