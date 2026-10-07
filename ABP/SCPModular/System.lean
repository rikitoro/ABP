import ABP.SCPModular.Sender
import ABP.SCPModular.Receiver

namespace SCPModular.System

variable {α : Type}

structure Network (α : Type) where
  dataCell : Option (Packet α)
  ackCell : Option Bool
  deriving Repr, DecidableEq

/-- 大域的状態 -/
structure State (α : Type) where
  sender : Sender.State α
  receiver : Receiver.State α
  network : Network α
  deriving Repr, DecidableEq

def initial (input : List α) : State α :=
  ⟨Sender.initial input, Receiver.initial, ⟨none, none⟩⟩

def sendData (s : State α) (p : Packet α) : State α :=
  { s with network := { s.network with dataCell := some p } }

def recvData (s : State α) (p : Packet α) : State α :=
  { s with
    receiver := Receiver.onData s.receiver p
    network := { s.network with dataCell :=none } }

def sendAck (s : State α) : State α :=
  { s with network := { s.network with ackCell := some (Receiver.emitAck s.receiver) } }

def recvAck (s : State α) (b : Bool) : State α :=
  { s with
    sender := Sender.onAck s.sender b
    network := { s.network with ackCell := none } }

def dropData (s : State α) : State α :=
  { s with network := { s.network with dataCell := none } }

def dropAck (s : State α) : State α :=
  { s with network := { s.network with ackCell := none } }

end SCPModular.System
