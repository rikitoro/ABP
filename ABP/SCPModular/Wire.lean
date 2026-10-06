import Std

namespace SCPModular

structure Packet (α : Type) where
  payload : α
  bit : Bool
  deriving Repr, DecidableEq

end SCPModular
