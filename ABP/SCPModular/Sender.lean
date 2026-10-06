import ABP.SCPModular.Wire

namespace SCPModular.Sender

variable {α : Type}

structure State (α : Type) where
  pending : List  α
  bit : Bool
  deriving Repr, DecidableEq

def initial (input : List α) : State α := ⟨input, false⟩






end SCPModular.Sender
