import Lean.Radiya.Expr
import Lean.Radiya.Ipld.Keccak
import Lean.Radiya.Ipld.Cid
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

abbrev ConstMap := SMap Name Const

structure Context where
  env : Lean.Environment
  constMap : Lean.ConstMap := {}

abbrev ConvM := ReaderT Context <| StateT ConstMap Id
instance : Monad ConvM := let i := inferInstanceAs (Monad ConvM); { pure := i.pure, bind := i.bind }

-- As it stands, it is using Keccak256. Should be parametrized on hash functions later
def nameToCid (nam : Name) : Cid :=
  -- Should we use `Name.hash` or our own encoding of names?
  let namHash := Name.hash nam
  let digest := Keccak.keccak256 $ ByteArray.pushUInt64LE ByteArray.empty namHash
  -- TODO: Correct the following 4 values
  let size := 0
  let code := 0
  let version := 0
  let codec := 0
  let multihash := Multihash.mk size code digest
  Cid.mk version codec multihash

def leanExprToCid (e : Lean.Expr) : Cid := panic! "TODO"
def inductiveToCid (induct : Lean.InductiveVal) : Cid := panic! "TODO"
def combineCid (a : Cid) (b : Cid) : Cid := panic! "TODO"

def inductiveIsUnitLike (ctors : List Name) : ConvM Bool :=
  match ctors with
  | [ctor] => do
    match Lean.Environment.find? (← read).env ctor with
    | some info =>
      match info with
      | ConstantInfo.ctorInfo cval => pure (cval.numFields != 0)
      | _ => pure false
    | none => pure false
  | _ => pure false

def leanLevelToRadiya (levelParams : List Name) (lvl : Lean.Level) : Univ :=
  match lvl with
  | Lean.Level.zero _ => Univ.zero
  | Lean.Level.succ n _ => Univ.succ (leanLevelToRadiya levelParams n)
  | Lean.Level.max a b _ => Univ.max (leanLevelToRadiya levelParams a) (leanLevelToRadiya levelParams b)
  | Lean.Level.imax a b _ => Univ.imax (leanLevelToRadiya levelParams a) (leanLevelToRadiya levelParams b)
  | Lean.Level.param nam _ => Univ.param (List.getIdxEx levelParams nam)
  | Lean.Level.mvar _ _ => panic! "Unfilled level metavariable"

mutual
partial def leanRuleToRadiya (rules : Lean.RecursorRule) : ConvM (RecursorRule Expr) := do
  let cid := default -- TODO
  let rhs ← leanExprToRadiya rules.rhs []
  pure $ RecursorRule.mk cid rules.nfields rhs

partial def toRadiyaConstMap (nam : Name) : ConvM ConstMap := do
  let insertConst := fun nam const => do
      let _ ← addConstInfo nam const
      pure default
  SMap.forM (← read).constMap insertConst
  get

partial def addConstInfo (nam : Name) (constInfo : ConstantInfo)  : ConvM Const := do
  let radiyaMap ← get
  match radiyaMap.find?' nam with
  | some const => pure const
  | none => do
    let const ← match constInfo with
    | ConstantInfo.axiomInfo struct => do
      let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
      let level := struct.levelParams.length
      let type ← leanExprToRadiya struct.type struct.levelParams
      pure $ Const.axiomC { cid, level, type }
    | ConstantInfo.thmInfo struct => do
      let level := struct.levelParams.length
      let expr ← leanExprToRadiya struct.value struct.levelParams
      let type ← leanExprToRadiya struct.type struct.levelParams
      pure $ Const.theoremC { level, expr, type }
    | ConstantInfo.opaqueInfo struct => do
      let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
      let level := struct.levelParams.length
      let expr ← leanExprToRadiya struct.value struct.levelParams
      let type ← leanExprToRadiya struct.type struct.levelParams
      let is_unsafe := struct.isUnsafe
      Const.opaque { cid, level, expr, type, is_unsafe }
    | ConstantInfo.defnInfo struct => do
      let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
      let level := struct.levelParams.length
      let expr ← leanExprToRadiya struct.value struct.levelParams
      let type ← leanExprToRadiya struct.type struct.levelParams
      let safety := struct.safety
      pure $ Const.defn { cid, level, expr, type, safety }
    | ConstantInfo.ctorInfo struct => do
      let cid := default -- TODO
      let level := struct.levelParams.length
      let type ← leanExprToRadiya struct.type struct.levelParams
      let ctor_idx := struct.cidx
      let num_params := struct.numParams
      let num_fields := struct.numFields
      let is_unsafe := struct.isUnsafe
      pure $ Const.ctor { cid, level, type, ctor_idx, num_params, num_fields, is_unsafe }
    | ConstantInfo.inductInfo struct => do
      let cid := inductiveToCid struct
      let level := struct.levelParams.length
      let type ← leanExprToRadiya struct.type struct.levelParams
      let num_params := struct.numParams
      let num_indices := struct.numIndices
      let is_unit ← inductiveIsUnitLike struct.ctors
      let is_rec := struct.isRec
      let is_unsafe := struct.isUnsafe
      let is_reflexive := struct.isReflexive
      let is_nested := struct.isNested
      pure $ Const.induct { cid, level, type, num_params, num_indices, is_unit, is_rec, is_unsafe, is_reflexive, is_nested }
    | ConstantInfo.recInfo struct => do
      let cid := default -- TODO
      let level := struct.levelParams.length
      let type ← leanExprToRadiya struct.type struct.levelParams
      let num_params := struct.numParams
      let num_indices := struct.numIndices
      let num_motives := struct.numMotives
      let num_minors := struct.numMinors
      let rules ← List.mapM leanRuleToRadiya struct.rules
      let k := struct.k
      let is_unsafe := struct.isUnsafe
      pure $ Const.recursor { cid, level, type, num_params, num_indices, num_motives, num_minors, rules, k, is_unsafe }
    | ConstantInfo.quotInfo struct => do
      let level := struct.levelParams.length
      let type ← leanExprToRadiya struct.type struct.levelParams
      let kind := struct.kind
      pure $ Const.quotient { level, type, kind }
    modifyGet (fun radiyaMap => (const, SMap.insert' radiyaMap nam const))

partial def leanExprToRadiya (lean : Lean.Expr) (levelParams : List Name) : ConvM Expr :=
  match lean with
  | Lean.Expr.bvar idx _ => pure $ Expr.var idx
  | Lean.Expr.sort lvl _ => pure $ Expr.sort (leanLevelToRadiya levelParams lvl)
  | Lean.Expr.const nam lvls _ => do
    match (← read).constMap.find?' nam with
    | some const =>
      let const ← addConstInfo nam const
      pure $ Expr.const const (List.map (leanLevelToRadiya levelParams) lvls)
    | none => panic! "Unknown constant"
  | Lean.Expr.app fnc arg _ => do
    let fnc ← leanExprToRadiya fnc levelParams
    let arg ← leanExprToRadiya arg levelParams
    pure $ Expr.app fnc arg
  | Lean.Expr.lam _ bnd bod _ => do
    let bnd ← leanExprToRadiya bnd levelParams
    let bod ← leanExprToRadiya bod levelParams
    pure $ Expr.lam bnd bod
  | Lean.Expr.forallE _ dom img _ => do
    let dom ← leanExprToRadiya dom levelParams
    let img ← leanExprToRadiya img levelParams
    pure $ Expr.pi dom img
  | Lean.Expr.letE _ typ exp bod _ => do
    let typ ← leanExprToRadiya typ levelParams
    let exp ← leanExprToRadiya exp levelParams
    let bod ← leanExprToRadiya bod levelParams
    pure $ Expr.letE typ exp bod
  | Lean.Expr.lit lit _ => pure $ Expr.lit lit
  | Lean.Expr.mdata _ e _ => leanExprToRadiya e levelParams
  | Lean.Expr.proj .. => panic! "Projections TODO"
  | Lean.Expr.fvar .. => panic! "Unbound variable"
  | Lean.Expr.mvar .. => panic! "Unfilled metavariable"
end

end Lean.Radiya
