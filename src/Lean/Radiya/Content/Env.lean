import Lean.Radiya.Ipld.Ipld
import Lean.Radiya.Ipld.Cid
import Lean.Radiya.Ipld.Multihash
import Lean.Radiya.Ipld.DagCbor
import Lean.Radiya.ToIpld
import Lean.Radiya.Content.Cid
import Lean.Radiya.Content.Name
import Lean.Radiya.Content.Univ
import Lean.Radiya.Content.Expr

import Lean
import Lean.Expr

import Std.Data.RBTree

open Lean (Literal)

open Std (RBNode)

namespace Lean.Radiya.Content

structure Env where
  lit : RBNode LitCid (fun _ => Literal)
  name : RBNode NameCid (fun _ => Name)
  univ : RBNode UnivCid (fun _ => Univ)
  univMeta : RBNode UnivMetaCid (fun _ => UnivMeta)
  expr : RBNode ExprCid (fun _ => Expr)
  exprMeta : RBNode ExprMetaCid (fun _ => ExprMeta)
  const : RBNode ExprCid (fun _ => Expr)
  constMeta : RBNode ExprMetaCid (fun _ => ExprMeta)

end Lean.Radiya.Content
