import ABP.SCPModular.System
import ABP.SCP

/-! 局所実装と SCP 仕様の接続 -/

namespace SCPModular.System

variable {α : Type}

@[simp, grind]
def abstractPacket (p : Packet α) : SCP.Packet α := ⟨p.payload, p.bit⟩

@[simp, grind]
def flatten (s : State α) : SCP.State α where
  pending := s.sender.pending
  sendBit := s.sender.bit
  expectBit := s.receiver.expected
  output := s.receiver.output
  dataCell := s.network.dataCell.map abstractPacket
  ackCell := s.network.ackCell

@[simp, grind =]
theorem flatten_initial (input : List α) : flatten (initial input) = SCP.initial input :=
  rfl

@[simp, grind =]
theorem flatten_recvData (s : State α) (p : Packet α) :
  flatten (recvData s p) = SCP.receiveData (flatten s) (abstractPacket p) := by
  grind

@[simp, grind =]
theorem flatten_sendAck (s : State α) :
  flatten (sendAck s) = SCP.transmitAck (flatten s) :=
  rfl

@[simp, grind =]
theorem flatten_recvAck (s : State α) (b : Bool) :
  flatten (recvAck s b) = SCP.receiveAck (flatten s) b := by
  grind


end SCPModular.System
