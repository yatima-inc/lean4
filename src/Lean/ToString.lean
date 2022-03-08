import Lean.Expr
import Lean.Environment

namespace Lean

def toStringConstKind (nam : Name) (env : Environment) : String :=
  match env.find? nam with
  | some (info@(ConstantInfo.axiomInfo _)) => "A"
  | some (info@(ConstantInfo.defnInfo _)) => "D"
  | some (info@(ConstantInfo.thmInfo _)) => "T"
  | some (info@(ConstantInfo.opaqueInfo _)) => "O"
  | some (info@(ConstantInfo.quotInfo _)) => "Q"
  | some (info@(ConstantInfo.inductInfo _)) => "I"
  | some (info@(ConstantInfo.ctorInfo _)) => "C"
  | some (info@(ConstantInfo.recInfo _)) => "R"
  | none => "!"

def toStringLvls (ls : List Level) : String :=
  match ls with
  | l::ls' => "[" ++ toString l ++ (List.foldr (fun lvl str => ", " ++ toString lvl ++ str) "]" ls')
  | [] => ""

def toStringLit (lit : Literal) : String :=
  match lit with
  | Literal.natVal val => toString val
  | Literal.strVal val => "\"" ++ val ++ "\""

def getPrefix (name : Name) : String :=
  match name with
  | Name.anonymous => "_"
  | Name.str Name.anonymous s _ => s ++ "_"
  | Name.str p _ _ => getPrefix p
  | Name.num p _ _  => getPrefix p

def toStringName (name : Name) : String :=
  match name with
  | Name.anonymous => "_"
  | Name.str _ s _ => s
  | Name.num p s _ => getPrefix p ++ toString s

def parens? (expr : Expr) (str : String) : String :=
  match expr with
  | Expr.bvar _ _ => str
  | Expr.fvar _ _ => str
  | Expr.mvar _ _ => str
  | Expr.sort _ _ => str
  | Expr.const _ _ _ => str
  | Expr.lit _ _ => str
  | _ => "(" ++ str ++ ")"

mutual
  partial def toStringExprAux
   (toStringDom? : Bool)
   (expr : Expr)
   (names : List Name)
   (env : Environment) : String :=
    match expr with
    | Expr.bvar n _ => "^" ++ toStringName (names.get! n)
    | Expr.fvar n _ => "#" ++ toStringName n.name
    | Expr.mvar n _ => "?" ++ toStringName n.name
    | Expr.sort l _ => "Sort " ++ toString l
    | Expr.const n ls _ => toStringConstKind n env ++ "$" ++ toString n ++ toStringLvls ls
    | Expr.app f a _ => toStringApp toStringDom? f names [a] env
    | Expr.lam n d b _ => toStringLam toStringDom? b names [(n, d)] env
    | Expr.forallE n d b _ => toStringAll toStringDom? b names [(n, d)] env
    | Expr.letE n t e b _ =>
      "let (" ++ toStringName n ++ " : " ++ toStringExprAux toStringDom? t names env ++ ") := " ++
      toStringExprAux toStringDom? e names env ++ " in " ++ toStringExprAux toStringDom? b (n :: names) env
    | Expr.lit l _ => toStringLit l
    | Expr.mdata m e _ => "MData. " ++ toStringExprAux toStringDom? e names env
    | Expr.proj n i e _ => "Proj " ++ toString n ++ " " ++ toString i ++ ". " ++ toStringExprAux toStringDom? e names env

  partial def toStringBind (toStringDom? : Bool) (env : Environment) : (List Name → String) → (Name × Expr) → List Name → String :=
    if toStringDom?
    then fun str (nam, expr) names => "(" ++ toStringName nam ++ " : " ++ toStringExprAux toStringDom? expr names env ++ ") " ++ str (nam :: names)
    else fun str (nam, _) names => toStringName nam ++ " " ++ str (nam :: names)

  partial def toStringLam
   (toStringDom? : Bool)
   (expr : Expr)
   (names : List Name)
   (binds : List (Name × Expr))
   (env : Environment) : String :=
    match expr with
    | Expr.lam n d b _ => toStringLam toStringDom? b names ((n, d) :: binds) env
    | _ =>
      let fold : String := List.foldl (toStringBind toStringDom? env) (λ _ => "=> ") binds names
      let names : List Name := List.append (List.map (fun (nam, _) => nam) binds) names
      "λ " ++ fold ++ toStringExprAux toStringDom? expr names env

  partial def toStringAll
   (toStringDom? : Bool)
   (expr : Expr)
   (names : List Name)
   (binds : List (Name × Expr))
   (env : Environment) : String :=
    match expr with
    | Expr.forallE n d b _ => toStringAll toStringDom? b names ((n, d) :: binds) env
    | _ =>
      let fold : String := List.foldl (toStringBind true env) (λ _ => "-> ") binds names
      let names : List Name := List.append (List.map (fun (nam, _) => nam) binds) names
      "∀ " ++ fold ++ toStringExprAux toStringDom? expr names env

  partial def toStringApp (toStringDom? : Bool)
   (expr : Expr)
   (names : List Name)
   (args : List Expr)
   (env : Environment) : String :=
    match expr with
    | Expr.app f a _ => toStringApp toStringDom? f names (a :: args) env
    | _ => parens? expr (toStringExprAux toStringDom? expr names env) ++ (List.foldr (fun arg str => " " ++ parens? arg (toStringExprAux toStringDom? arg names env) ++ str) "" args)
end

def toStringExpr (toStringDom? : Bool) (expr : Expr) (env : Environment) : String := toStringExprAux toStringDom? expr [] env

end Lean
