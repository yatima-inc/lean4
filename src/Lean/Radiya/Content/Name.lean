import Lean.Radiya.Ipld.Ipld
import Lean.Radiya.Ipld.Cid
import Lean.Radiya.Content.Cid
import Lean.Radiya.Ipld.Multihash
import Lean.Radiya.Ipld.DagCbor
import Lean.Radiya.ToIpld

namespace Lean.Radiya.Content

inductive Name where
| anon
| str : NameCid → String → Name
| num : NameCid → Nat → Name

namespace Name

open ToIpld
open Ipld

instance : ToIpld Name where
  toIpld
  | Name.anon    => array #[number NAME, number 0]
  | Name.str p s => array #[number NAME, number 1, toIpld p, toIpld s]
  | Name.num p n => array #[number NAME, number 2, toIpld p, toIpld n]

  fromIpld
  | array #[number NAME, number 0] => return Name.anon
  | array #[number NAME, number 1, p, s] => Name.str <$> fromIpld p <*> fromIpld s
  | array #[number NAME, number 2, p, n] => Name.num <$> fromIpld p <*> fromIpld n
  | _ => throw (IpldError.Expected "Name")

end Name



end Lean.Radiya.Content
