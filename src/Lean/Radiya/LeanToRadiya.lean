import Lean.Radiya.Expr
import Lean.Expr

namespace Lean.Radiya

abbrev ConstMap := Nat

def nameToCid (nam : Name) : Cid := panic! "TODO"

def findConstInfo (nam : Name) (constMap : ConstMap) : Const :=
  Const.theoremC (TheoremC.mk 0 (panic! "TODO") (panic! "TODO"))

def leanLevelToRadiya (lvl : Lean.Level) : Univ :=
  match lvl with
  | Lean.Level.zero .. => panic! "TODO"
  | Lean.Level.succ .. => panic! "TODO"
  | Lean.Level.max .. => panic! "TODO"
  | Lean.Level.imax .. => panic! "TODO"
  | Lean.Level.param .. => panic! "TODO"
  | Lean.Level.mvar .. => panic! "Expressions should not have meta variables"

def leanExprToRadiya (lean : Lean.Expr) (constMap : ConstMap) : Expr :=
  match lean with
  | Lean.Expr.bvar idx _ => Expr.var idx
  | Lean.Expr.sort lvl _ => Expr.sort (leanLevelToRadiya lvl)
  | Lean.Expr.const nam lvls _ => Expr.const (findConstInfo nam constMap) (List.map leanLevelToRadiya lvls)
  | Lean.Expr.app fnc arg _ => Expr.app (leanExprToRadiya fnc constMap) (leanExprToRadiya arg constMap)
  | Lean.Expr.lam _ bnd bod _ => Expr.lam (leanExprToRadiya bnd constMap) (leanExprToRadiya bod constMap)
  | Lean.Expr.forallE _ dom img _ => Expr.pi (leanExprToRadiya dom constMap) (leanExprToRadiya img constMap)
  | Lean.Expr.letE _ typ exp bod _ =>
    Expr.letE (leanExprToRadiya typ constMap) (leanExprToRadiya exp constMap) (leanExprToRadiya bod constMap)
  | Lean.Expr.lit lit _ => Expr.lit lit
  | Lean.Expr.mdata _ e _ => leanExprToRadiya e constMap
  | Lean.Expr.proj .. => panic! "Projections TODO"
  | Lean.Expr.fvar .. => panic! "Expressions should not have free variables"
  | Lean.Expr.mvar .. => panic! "Expressions should not have meta variables"

end Lean.Radiya
