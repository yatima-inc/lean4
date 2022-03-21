import Lean.Radiya.Expr
import Lean.Expr
import Lean.Environment

namespace List

def getIdxEx {A : Type u} [BEq A] (as : List A) (a : A) : Nat :=
  let rec aux (as : List A) (a : A) (i : Nat) : Nat :=
    match as with
    | a' :: as' => if a == a' then i else aux as' a' (i+1)
    | [] => panic! "List does not contain value"
  aux as a 0

end List

namespace Lean.Radiya

def nameToCid (nam : Name) : Cid := panic! "TODO"
def exprToCid (e : Lean.Expr) : Cid := panic! "TODO"
def combineCid (a : Cid) (b : Cid) : Cid := panic! "TODO"

def leanLevelToRadiya (levelParams : List Name) (lvl : Lean.Level) : Univ :=
  match lvl with
  | Lean.Level.zero _ => Univ.zero
  | Lean.Level.succ n _ => Univ.succ (leanLevelToRadiya levelParams n)
  | Lean.Level.max a b _ => Univ.max (leanLevelToRadiya levelParams a) (leanLevelToRadiya levelParams b)
  | Lean.Level.imax a b _ => Univ.imax (leanLevelToRadiya levelParams a) (leanLevelToRadiya levelParams b)
  | Lean.Level.param nam _ => Univ.param (List.getIdxEx levelParams nam)
  | Lean.Level.mvar _ _ => panic! "Unfilled level metavariable"

mutual
partial def findConstInfo (nam : Name) (constMap : Lean.ConstMap) : Const :=
  match constMap.find?' nam with
  | some (ConstantInfo.axiomInfo struct) =>
    let cid := combineCid (nameToCid struct.name) (exprToCid struct.type)
    let level := struct.levelParams.length
    let type := leanExprToRadiya struct.type constMap struct.levelParams
    Const.axiomC { cid, level, type }
  | some (ConstantInfo.thmInfo struct) =>
    let level := struct.levelParams.length
    let expr := leanExprToRadiya struct.value constMap struct.levelParams
    let type := leanExprToRadiya struct.type constMap struct.levelParams
    Const.theoremC { level, expr, type }
  | some (ConstantInfo.opaqueInfo struct) =>
    let cid := combineCid (nameToCid struct.name) (exprToCid struct.type)
    let level := struct.levelParams.length
    let expr := leanExprToRadiya struct.value constMap struct.levelParams
    let type := leanExprToRadiya struct.type constMap struct.levelParams
    let is_unsafe := default
    Const.opaque { cid, level, expr, type, is_unsafe }
  | some (ConstantInfo.defnInfo struct) =>
    let cid := combineCid (nameToCid struct.name) (exprToCid struct.type)
    let level := struct.levelParams.length
    let expr := leanExprToRadiya struct.value constMap struct.levelParams
    let type := leanExprToRadiya struct.type constMap struct.levelParams
    let safety := struct.safety
    Const.defn { cid, level, expr, type, safety }
  | some (ConstantInfo.ctorInfo struct) =>
    let cid := default
    let level := struct.levelParams.length
    let type := leanExprToRadiya struct.type constMap struct.levelParams
    let ctor_idx := default
    let num_params := default
    let num_fields := default
    let is_unsafe := default
    Const.ctor { cid, level, type, ctor_idx, num_params, num_fields, is_unsafe }
  | some (ConstantInfo.inductInfo struct) =>
    let cid := default
    let level := struct.levelParams.length
    let type := leanExprToRadiya struct.type constMap struct.levelParams
    let num_params := default
    let num_indices := default
    let ctors := default
    let is_rec := default
    let is_unsafe := default
    let is_reflexive := default
    let is_nested := default
    Const.induct { cid, level, type, num_params, num_indices, ctors, is_rec, is_unsafe, is_reflexive, is_nested }
  | some (ConstantInfo.recInfo struct) =>
    let cid := default
    let level := struct.levelParams.length
    let type := leanExprToRadiya struct.type constMap struct.levelParams
    let num_params := default
    let num_indices := default
    let num_motives := default
    let num_minors := default
    let rules := default
    let k := default
    let is_unsafe := default
    Const.recursor { cid, level, type, num_params, num_indices, num_motives, num_minors, rules, k, is_unsafe }
  | some (ConstantInfo.quotInfo struct) =>
    let level := struct.levelParams.length
    let type := leanExprToRadiya struct.type constMap struct.levelParams
    let kind := default
    Const.quotient { level, type, kind }
  | none => panic! "Unknown constant"

partial def leanExprToRadiya (lean : Lean.Expr) (constMap : Lean.ConstMap) (levelParams : List Name) : Expr :=
  match lean with
  | Lean.Expr.bvar idx _ => Expr.var idx
  | Lean.Expr.sort lvl _ => Expr.sort (leanLevelToRadiya levelParams lvl)
  | Lean.Expr.const nam lvls _ => Expr.const (findConstInfo nam constMap) (List.map (leanLevelToRadiya levelParams) lvls)
  | Lean.Expr.app fnc arg _ => Expr.app (leanExprToRadiya fnc constMap levelParams) (leanExprToRadiya arg constMap levelParams)
  | Lean.Expr.lam _ bnd bod _ => Expr.lam (leanExprToRadiya bnd constMap levelParams) (leanExprToRadiya bod constMap levelParams)
  | Lean.Expr.forallE _ dom img _ => Expr.pi (leanExprToRadiya dom constMap levelParams) (leanExprToRadiya img constMap levelParams)
  | Lean.Expr.letE _ typ exp bod _ =>
    Expr.letE
     (leanExprToRadiya typ constMap levelParams)
     (leanExprToRadiya exp constMap levelParams)
     (leanExprToRadiya bod constMap levelParams)
  | Lean.Expr.lit lit _ => Expr.lit lit
  | Lean.Expr.mdata _ e _ => leanExprToRadiya e constMap levelParams
  | Lean.Expr.proj .. => panic! "Projections TODO"
  | Lean.Expr.fvar .. => panic! "Unbound variable"
  | Lean.Expr.mvar .. => panic! "Unfilled metavariable"
end

end Lean.Radiya
